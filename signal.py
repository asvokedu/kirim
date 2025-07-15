import os
import requests
import time
import logging
import threading
import json
import sys
import queue
import pyodbc
import hmac
import hashlib
import urllib.parse
import select
import ssl
import socket
from collections import deque
from datetime import datetime, timedelta
from websocket import create_connection, WebSocketConnectionClosedException
from typing import List, Dict, Any, Set, Optional, Deque, Tuple
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Setup logging - HANYA KE FILE
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s",
    handlers=[
        logging.FileHandler("futures_signal_detector.log", mode='w'),
    ]
)
logger = logging.getLogger()

class SignalDetector:
    # --- Konfigurasi ---
    SYMBOL_LIST_FILE = "listsymbol.txt"
    INTERVAL = "15m"
    MAX_CONCURRENT_REQUESTS = 20
    MAX_SYMBOLS = 150
    ORDERBOOK_DEPTH_LEVEL = 100
    LIQ_HISTORY_WINDOW = 15  # Menit untuk perhitungan rata-rata likuidasi
    
    # --- URL Endpoint ---
    LIQUIDATION_WS_URL = "wss://fstream.binance.com/ws/!forceOrder@arr"
    BASE_WS_URL = "wss://fstream.binance.com/stream?streams="
    EXCHANGE_INFO_URL = "https://fapi.binance.com/fapi/v1/exchangeInfo"
    PREMIUM_INDEX_URL = "https://fapi.binance.com/fapi/v1/premiumIndex"
    OPEN_INTEREST_URL = "https://fapi.binance.com/fapi/v1/openInterest"
    DEPTH_URL = "https://fapi.binance.com/fapi/v1/depth"
    MARK_PRICE_WS_URL = "wss://fstream.binance.com/ws/!markPrice@arr"
    KLINE_URL = "https://fapi.binance.com/fapi/v1/klines"
    
    # Konfigurasi Database
    SQL_SERVER = os.getenv("SQL_SERVER")
    SQL_DATABASE = os.getenv("SQL_DATABASE")
    SQL_USERNAME = os.getenv("SQL_USERNAME")
    SQL_PASSWORD = os.getenv("SQL_PASSWORD")
    SQL_DRIVER = os.getenv("SQL_DRIVER", "{ODBC Driver 17 for SQL Server}")

    def __init__(self):
        self.symbols: List[str] = []
        self.valid_symbols: Set[str] = set()
        self.shutdown_event = threading.Event()
        self.SIGNAL_DETECTION_INTERVAL = 3  # Dalam detik
        self.data_lock = threading.Lock()
        self.symbol_info_cache: Dict[str, Dict] = {}  # Cache untuk info simbol
        
        self.liquidation_accumulator: Dict[str, Dict[str, float]] = {}
        self.volume_accumulator: Dict[str, Dict[str, float]] = {}
        self.order_books: Dict[str, Dict[str, Any]] = {}
        self.display_data: Dict[str, Dict[str, Any]] = {}
        
        # Struktur data untuk harga
        self.last_prices: Dict[str, float] = {}
        self.mark_prices: Dict[str, float] = {}
        
        # Menyimpan OI sebelumnya untuk perhitungan perubahan
        self.previous_oi: Dict[str, float] = {}
        
        # Menyimpan history likuidasi untuk perhitungan rata-rata
        self.liquidation_history: Dict[str, Deque[Tuple[datetime, float, float]]] = {}
        
        # === STRUKTUR DATA BARU UNTUK PENINGKATAN SINYAL ===
        self.price_history: Dict[str, Deque[Tuple[datetime, float]]] = {}
        self.funding_history: Dict[str, Deque[float]] = {}
        self.atr_values: Dict[str, float] = {}  # Menyimpan nilai ATR14 terkini
        
        # Data kline
        self.current_candle: Dict[str, Dict] = {}  # Data candle saat ini
        self.previous_candle: Dict[str, Dict] = {}  # Data candle sebelumnya
        
        self.liquidation_queue = queue.Queue()
        self.trade_queue = queue.Queue()
        self.depth_queue = queue.Queue()  # Queue untuk depth updates
        
        # Menyimpan sinyal dan skor terakhir
        self.last_signals: Dict[str, str] = {}  # {symbol: 'LONG'/'SHORT'/'HOLD'}
        self.current_scores: Dict[str, int] = {}  # {symbol: skor_terakhir}
        self.signal_lock = threading.Lock()
        
        self.request_semaphore = threading.Semaphore(self.MAX_CONCURRENT_REQUESTS)
        self.session = self._create_session()
        
        # Untuk menyimpan candle timestamp terakhir per simbol
        self.last_candle_timestamps: Dict[str, datetime] = {}
        
        # Untuk menyimpan burst threshold
        self.burst_thresholds: Dict[str, Dict[str, float]] = {}

    def _get_db_connection(self) -> Optional[pyodbc.Connection]:
        """Membuat koneksi baru ke database SQL Server"""
        if not all([self.SQL_SERVER, self.SQL_DATABASE, self.SQL_USERNAME, self.SQL_PASSWORD]):
            logger.error("Variabel lingkungan database tidak lengkap!")
            return None
            
        connection_string = (
            f"DRIVER={self.SQL_DRIVER};"
            f"SERVER={self.SQL_SERVER};"
            f"DATABASE={self.SQL_DATABASE};"
            f"UID={self.SQL_USERNAME};"
            f"PWD={self.SQL_PASSWORD}"
        )
        try:
            conn = pyodbc.connect(connection_string)
            return conn
        except Exception as e:
            logger.error(f"Gagal konek ke database: {e}")
            return None

    def _update_aset_table(self, symbol: str, position: str, score: int, 
                          liquidation_buy: float, liquidation_sell: float):
        """Update tabel T_Aset dengan posisi, signal, dan akumulasi likuidasi terbaru"""
        conn = self._get_db_connection()
        if not conn:
            return False
            
        try:
            cursor = conn.cursor()
            # Cek apakah simbol sudah ada di tabel
            cursor.execute("SELECT COUNT(*) FROM T_Aset WHERE symbol = ?", (symbol,))
            row = cursor.fetchone()
            
            if row and row[0] > 0:
                # Update existing record
                cursor.execute("""
                    UPDATE T_Aset 
                    SET posisi = ?, 
                        signal = ?, 
                        last_updated = ?,
                        liquidation_buy = ?,
                        liquidation_sell = ?
                    WHERE symbol = ?
                """, (position, score, datetime.utcnow(), liquidation_buy, liquidation_sell, symbol))
            else:
                # Insert new record
                cursor.execute("""
                    INSERT INTO T_Aset (
                        symbol, posisi, signal, last_updated, 
                        liquidation_buy, liquidation_sell
                    ) VALUES (?, ?, ?, ?, ?, ?)
                """, (symbol, position, score, datetime.utcnow(), liquidation_buy, liquidation_sell))
                
            conn.commit()
            logger.info(f"Updated T_Aset for {symbol}: {position} ({score}) | LiqBuy: {liquidation_buy:.2f} | LiqSell: {liquidation_sell:.2f}")
            return True
        except Exception as e:
            logger.error(f"Gagal update T_Aset untuk {symbol}: {e}")
            return False
        finally:
            conn.close()

    def _get_burst_thresholds(self, symbol: str) -> Dict[str, float]:
        """Mengambil burst threshold dari database menggunakan stored procedure"""
        conn = self._get_db_connection()
        if not conn:
            return {'burst_buy_threshold': 50000, 'burst_sell_threshold': 50000}  # Default values
            
        try:
            cursor = conn.cursor()
            cursor.execute("EXEC sp_burst_liquidation_threshold @symbol=?, @days_back=3, @sensitivity=2.5", symbol)
            row = cursor.fetchone()
            
            if row:
                return {
                    'burst_buy_threshold': float(row.burst_buy_threshold) if hasattr(row, 'burst_buy_threshold') else 50000,
                    'burst_sell_threshold': float(row.burst_sell_threshold) if hasattr(row, 'burst_sell_threshold') else 50000
                }
            return {'burst_buy_threshold': 50000, 'burst_sell_threshold': 50000}
        except Exception as e:
            logger.error(f"Gagal mengambil burst threshold untuk {symbol}: {e}")
            return {'burst_buy_threshold': 50000, 'burst_sell_threshold': 50000}
        finally:
            conn.close()

    def _get_atr14(self, symbol: str) -> float:
        """Mengambil nilai ATR14 dari database menggunakan stored procedure"""
        conn = self._get_db_connection()
        if not conn:
            return 0.0
            
        try:
            cursor = conn.cursor()
            cursor.execute("EXEC sp_calculate_atr14 @symbol=?, @interval=?, @limit=14", 
                          (symbol, self.INTERVAL))
            row = cursor.fetchone()
            
            if row and hasattr(row, 'atr_14'):
                return float(row.atr_14)
            return 0.0
        except Exception as e:
            logger.error(f"Gagal mengambil ATR14 untuk {symbol}: {e}")
            return 0.0
        finally:
            conn.close()

    def _save_signal(self, symbol: str, mark_price: float, position: str, score: int, candle_timestamp: datetime) -> bool:
        """
        Simpan sinyal ke database dengan status=2 (pending) jika:
        1. Tidak ada posisi aktif (status=1) untuk simbol tersebut
        2. Tidak ada sinyal pending (status=2) di candle yang sama
        3. Periode candle berbeda dengan sinyal sebelumnya
        """
        conn = self._get_db_connection()
        if not conn:
            return False
            
        try:
            cursor = conn.cursor()
            
            # 1. Cek apakah ada posisi aktif (status=1) untuk simbol ini
            cursor.execute("""
                SELECT COUNT(*) 
                FROM tran_TF 
                WHERE symbol = ? AND status = 1
            """, (symbol,))
            row = cursor.fetchone()
            if row and row[0] > 0:
                logger.info(f"Ada posisi aktif untuk {symbol}, skip penyimpanan sinyal")
                return False
                
            # 2. Cek apakah sudah ada sinyal di candle yang sama
            cursor.execute("""
                SELECT COUNT(*) 
                FROM tran_TF 
                WHERE symbol = ? 
                AND status = 2 
                AND binance_order_id = 'PENDING'
                AND timestamp >= ?
            """, (symbol, candle_timestamp))
            row = cursor.fetchone()
            if row and row[0] > 0:
                logger.info(f"Sudah ada sinyal pending untuk {symbol} di candle ini, skip")
                return False
                
            # 3. Cek periode candle berbeda dengan sinyal terakhir
            last_candle = self.last_candle_timestamps.get(symbol)
            if last_candle and last_candle == candle_timestamp:
                logger.info(f"Periode candle sama untuk {symbol}, skip penyimpanan sinyal")
                return False
                
            # Simpan candle timestamp terbaru
            self.last_candle_timestamps[symbol] = candle_timestamp
                
            # Jika semua kondisi terpenuhi, simpan sinyal
            query = """
                INSERT INTO tran_TF (
                    symbol, price_open, status, posisi, 
                    stop_lose, take_profit, feebinance, timestamp, 
                    qty, leverage, binance_order_id, signal_score
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """
            # Set nilai default untuk kolom yang tidak digunakan
            stop_loss = 0.0
            take_profit = 0.0
            fee = 0.0
            qty = 0.0
            leverage = 0
            
            params = (
                symbol, 
                mark_price, 
                2,  # Status: Pending
                position, 
                stop_loss, 
                take_profit, 
                fee, 
                datetime.utcnow(),
                qty,
                leverage,
                "PENDING",  # Menandai sebagai sinyal
                score
            )
            cursor.execute(query, params)
            conn.commit()
            logger.info(f"Sinyal {position} disimpan untuk {symbol} dengan skor {score} @ {mark_price:.5f}")
            
            
            return True
        except Exception as e:
            logger.error(f"Gagal menyimpan sinyal: {e}")
            return False
        finally:
            conn.close()

    def _create_session(self) -> requests.Session:
        session = requests.Session()
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=200, pool_maxsize=200,
            max_retries=requests.adapters.Retry(
                total=5, backoff_factor=1,
                status_forcelist=[429, 500, 502, 503, 504]
            )
        )
        session.mount("https://", adapter)
        session.mount("http://", adapter)
        return session

    def _fetch_valid_futures_symbols(self) -> Set[str]:
        try:
            response = self.session.get(self.EXCHANGE_INFO_URL, timeout=10)
            response.raise_for_status()
            return {s['symbol'] for s in response.json()['symbols'] if s['status'] == 'TRADING'}
        except Exception as e:
            logger.error(f"Gagal mengambil simbol valid: {e}")
            return set()

    def _load_symbol_list(self):
        if not os.path.exists(self.SYMBOL_LIST_FILE):
            sys.exit(f"Error: File '{self.SYMBOL_LIST_FILE}' tidak ditemukan.")

        self.valid_symbols = self._fetch_valid_futures_symbols()
        if not self.valid_symbols:
            logger.warning("Gagal validasi simbol, menggunakan semua dari file.")

        with open(self.SYMBOL_LIST_FILE, 'r') as f:
            symbols_from_file = {line.strip().upper() for line in f if line.strip()}

        validated_symbols = [
            symbol for symbol in sorted(list(symbols_from_file))
            if not self.valid_symbols or symbol in self.valid_symbols
        ]

        self.symbols = validated_symbols[:self.MAX_SYMBOLS]
        if not self.symbols:
            sys.exit("Error: Tidak ada simbol valid di dalam file list.")
        logger.info(f"Akan melacak {len(self.symbols)} simbol.")
        
    def _fetch_api_data(self, url: str, params: Dict) -> Optional[Dict]:
        with self.request_semaphore:
            if self.shutdown_event.is_set(): return None
            try:
                response = self.session.get(url, params=params, timeout=5)
                response.raise_for_status()
                return response.json()
            except Exception as e:
                logger.error(f"Error API di {url} dengan params {params}: {e}")
            return None
    
    def _fetch_order_book_snapshot(self, symbol: str) -> Optional[Dict]:
        data = self._fetch_api_data(self.DEPTH_URL, {"symbol": symbol, "limit": self.ORDERBOOK_DEPTH_LEVEL})
        return {'bids': data.get('bids', []), 'asks': data.get('asks', []), 'timestamp': datetime.utcnow()} if data else None

    def _fetch_current_kline(self, symbol: str) -> Optional[Dict]:
        """Mengambil data kline saat ini untuk simbol"""
        params = {
            'symbol': symbol,
            'interval': self.INTERVAL,
            'limit': 1
        }
        data = self._fetch_api_data(self.KLINE_URL, params)
        if data and isinstance(data, list) and len(data) > 0:
            kline = data[0]
            return {
                'open_time': datetime.utcfromtimestamp(kline[0]/1000),
                'open': float(kline[1]),
                'high': float(kline[2]),
                'low': float(kline[3]),
                'close': float(kline[4]),
                'volume': float(kline[5]),
                'close_time': datetime.utcfromtimestamp(kline[6]/1000),
                'is_closed': kline[6] < (time.time() * 1000) - 60000  # Cek jika candle sudah ditutup
            }
        return None

    def _initialize_data_structures(self):
        with self.data_lock:
            for symbol in self.symbols:
                self.liquidation_accumulator[symbol] = {'buy': 0.0, 'sell': 0.0}
                self.volume_accumulator[symbol] = {'market_buy': 0.0, 'market_sell': 0.0}
                self.order_books[symbol] = {'bids': [], 'asks': [], 'timestamp': None}
                self.display_data[symbol] = {
                    'funding_rate': 0, 
                    'open_interest': 0,
                    'oi_usd': 0,
                    'prev_oi_usd': 0,  # Simpan OI USD periode sebelumnya
                    'last_update': datetime.utcnow(),
                }
                self.last_prices[symbol] = 0.0
                self.mark_prices[symbol] = 0.0
                self.previous_oi[symbol] = 0.0
                self.liquidation_history[symbol] = deque(maxlen=1000)
                
                # Inisialisasi struktur data baru
                self.price_history[symbol] = deque(maxlen=3)
                self.funding_history[symbol] = deque(maxlen=48)
                self.atr_values[symbol] = 0.0
                
                # Inisialisasi data candle
                self.current_candle[symbol] = {
                    'high': 0.0,
                    'low': float('inf'),
                    'volume': 0.0
                }
                self.previous_candle[symbol] = {
                    'high': 0.0,
                    'low': float('inf'),
                    'volume': 0.0
                }
                
                self.last_candle_timestamps[symbol] = datetime.utcnow().replace(
                    minute=0, second=0, microsecond=0
                )
                
                # Inisialisasi burst thresholds dengan nilai default
                self.burst_thresholds[symbol] = {'burst_buy_threshold': 50000, 'burst_sell_threshold': 50000}
        logger.info("Inisialisasi struktur data selesai.")

    def _initialize_order_books(self):
        logger.info("Memulai inisialisasi order book awal...")
        threads = []
        def fetch_and_store(symbol):
            snapshot = self._fetch_order_book_snapshot(symbol)
            if snapshot:
                with self.data_lock:
                    self.order_books[symbol] = snapshot
                    if self.last_prices[symbol] == 0.0:
                        if snapshot['bids'] and snapshot['asks']:
                            bid = float(snapshot['bids'][0][0])
                            ask = float(snapshot['asks'][0][0])
                            self.last_prices[symbol] = (bid + ask) / 2
        
        for symbol in self.symbols:
            thread = threading.Thread(target=fetch_and_store, args=(symbol,), daemon=True)
            threads.append(thread)
            thread.start()
        
        for thread in threads:
            thread.join(timeout=10)
        logger.info("Inisialisasi order book awal selesai.")

    def _process_closed_bar(self, symbol: str):
        # Ambil data ATR14 dari database
        atr14 = self._get_atr14(symbol)
        
        # Ambil data kline saat ini untuk simbol
        kline_data = self._fetch_current_kline(symbol)
        
        oi_data = self._fetch_api_data(self.OPEN_INTEREST_URL, {"symbol": symbol})
        funding_data = self._fetch_api_data(self.PREMIUM_INDEX_URL, {"symbol": symbol})

        with self.data_lock:
            # Update nilai ATR14
            self.atr_values[symbol] = atr14
            
            # Update data candle
            if kline_data:
                self.previous_candle[symbol] = {
                    'high': kline_data['high'],
                    'low': kline_data['low'],
                    'volume': kline_data['volume']
                }
                # Reset candle saat ini
                self.current_candle[symbol] = {
                    'high': 0.0,
                    'low': float('inf'),
                    'volume': 0.0
                }
            
            # Simpan OI USD saat ini sebagai OI periode berikutnya
            current_oi_usd = self.display_data[symbol].get('oi_usd', 0)
            self.display_data[symbol]['prev_oi_usd'] = current_oi_usd
            
            if funding_data: 
                rate = float(funding_data.get("lastFundingRate", 0))
                self.display_data[symbol]['funding_rate'] = rate
                self.funding_history[symbol].append(rate)
                
            if oi_data: 
                oi_value = float(oi_data.get("openInterest", 0))
                self.display_data[symbol]['open_interest'] = oi_value
                self.display_data[symbol]['oi_usd'] = oi_value * self.mark_prices.get(symbol, 0)
            
            self.liquidation_accumulator[symbol] = {'buy': 0.0, 'sell': 0.0}
            self.volume_accumulator[symbol] = {'market_buy': 0.0, 'market_sell': 0.0}
            self.display_data[symbol]['last_update'] = datetime.utcnow()
            
            # Update burst thresholds setiap kali candle ditutup
            self.burst_thresholds[symbol] = self._get_burst_thresholds(symbol)
        logger.info(f"Reset akumulator dan update OI untuk {symbol}. ATR14: {atr14:.4f}")

    def _periodic_data_updater(self):
        while not self.shutdown_event.wait(60):
            logger.info("Memulai pembaruan data periodik...")
            for symbol in self.symbols:
                if self.shutdown_event.is_set(): break
                funding_data = self._fetch_api_data(self.PREMIUM_INDEX_URL, {"symbol": symbol})
                oi_data = self._fetch_api_data(self.OPEN_INTEREST_URL, {"symbol": symbol})
                with self.data_lock:
                    if symbol not in self.display_data: continue
                    
                    if funding_data: 
                        rate = float(funding_data.get("lastFundingRate", 0))
                        self.display_data[symbol]['funding_rate'] = rate
                        self.funding_history[symbol].append(rate)
                        
                    if oi_data: 
                        oi_value = float(oi_data.get("openInterest", 0))
                        self.display_data[symbol]['open_interest'] = oi_value
                        self.display_data[symbol]['oi_usd'] = oi_value * self.mark_prices.get(symbol, 0)
                    
                    self.display_data[symbol]['last_update'] = datetime.utcnow()
            logger.info("Pembaruan data periodik selesai.")
    
    def _websocket_connector(self, url: str, stream_name: str, handler_func):
        """Konektor WebSocket yang lebih tangguh dengan backoff eksponensial"""
        backoff = 1  # Backoff awal 1 detik
        while not self.shutdown_event.is_set():
            try:
                logger.info(f"Membuka koneksi WebSocket untuk {stream_name}...")
                # Tambahkan timeout dan SSL context untuk koneksi lebih stabil
                ws = create_connection(
                    url, 
                    timeout=10,
                    sslopt={"cert_reqs": ssl.CERT_NONE}  # Nonaktifkan verifikasi sertifikat
                )
                logger.info(f"Koneksi WebSocket {stream_name} berhasil.")
                backoff = 1  # Reset backoff setelah koneksi berhasil
                
                while not self.shutdown_event.is_set():
                    try:
                        # Gunakan select untuk timeout operasi recv
                        r, _, _ = select.select([ws.sock], [], [], 30)  # Timeout 30 detik
                        if r:
                            msg = ws.recv()
                            if msg: 
                                handler_func(json.loads(msg))
                        # Else: timeout, lanjutkan loop
                    except socket.timeout:  # Tangkap error timeout khusus
                        logger.warning(f"Timeout sementara di {stream_name}, melanjutkan...")
                        continue
                    except (WebSocketConnectionClosedException, ConnectionResetError) as e:
                        logger.warning(f"Koneksi WebSocket {stream_name} ditutup: {e}")
                        break
                    except Exception as e:
                        logger.error(f"Error dalam loop WebSocket {stream_name}: {e}")
                        time.sleep(1)
            except Exception as e:
                logger.error(f"Error WebSocket {stream_name}: {e}")
                # Backoff eksponensial
                sleep_time = min(backoff, 60)  # Maksimum backoff 60 detik
                logger.info(f"Menunggu {sleep_time} detik sebelum mencoba kembali koneksi {stream_name}")
                time.sleep(sleep_time)
                backoff *= 2  # Double backoff time
            finally:
                try:
                    if 'ws' in locals() and ws.connected:
                        ws.close()
                except:
                    pass

    def _handle_kline_stream(self, data):
        stream_data = data.get('data', {})
        if stream_data.get('e') == 'kline' and stream_data.get('k', {}).get('x'):
            symbol = stream_data['k']['s'].upper()
            threading.Thread(target=self._process_closed_bar, args=(symbol,), name=f"BarProc-{symbol}").start()

    def _handle_liquidation_stream(self, data):
        if isinstance(data, dict) and data.get('e') == 'forceOrder':
            self.liquidation_queue.put(data.get('o', {}))

    def _handle_trade_stream(self, data):
        if 'aggTrade' in data.get('stream', ''):
            self.trade_queue.put(data.get('data', {}))

    def _handle_depth_stream(self, data):
        # Skip pemrosesan jika antrian sudah penuh
        if self.depth_queue.qsize() > 100:  
            return   
        self.depth_queue.put(data)  # Masukkan ke antrian baru

    # Thread processor khusus:
    def _depth_processor(self):
        while not self.shutdown_event.is_set():
            try:
                data = self.depth_queue.get(timeout=1)
                stream_data = data.get('data', {})
                if 'depth' in data.get('stream', ''):
                    symbol = stream_data.get('s', '').upper()
                    if symbol in self.symbols:
                        with self.data_lock:
                            self.order_books[symbol]['bids'] = stream_data.get('b', [])
                            self.order_books[symbol]['asks'] = stream_data.get('a', [])
                            self.order_books[symbol]['timestamp'] = datetime.utcnow()
                            if self.order_books[symbol]['bids'] and self.order_books[symbol]['asks']:
                                bid = float(self.order_books[symbol]['bids'][0][0])
                                ask = float(self.order_books[symbol]['asks'][0][0])
                                self.last_prices[symbol] = (bid + ask) / 2
            except queue.Empty:
                continue

    def _handle_mark_price_stream(self, data):
        if isinstance(data, list):
            for update in data:
                symbol = update.get('s', '').upper()
                if symbol in self.symbols:
                    mark_price = float(update.get('p', 0.0))
                    with self.data_lock:
                        self.mark_prices[symbol] = mark_price
                        if symbol in self.display_data:
                            oi_value = self.display_data[symbol].get('open_interest', 0)
                            self.display_data[symbol]['oi_usd'] = oi_value * mark_price

    def _liquidation_processor(self):
        while not self.shutdown_event.is_set():
            try:
                event = self.liquidation_queue.get(timeout=1)
                symbol, qty, side = event.get('s', '').upper(), float(event.get('q', 0)), event.get('S', '').upper()
                if symbol in self.symbols:
                    with self.data_lock:
                        if side == 'BUY': 
                            self.liquidation_accumulator[symbol]['buy'] += qty
                            self.liquidation_history[symbol].append((datetime.utcnow(), qty, 0))
                        elif side == 'SELL': 
                            self.liquidation_accumulator[symbol]['sell'] += qty
                            self.liquidation_history[symbol].append((datetime.utcnow(), 0, qty))
            except queue.Empty: continue
            except Exception as e: logger.error(f"Error prosesor likuidasi: {e}")
            
    def _trade_processor(self):
        while not self.shutdown_event.is_set():
            try:
                event = self.trade_queue.get(timeout=1)
                symbol = event.get('s', '').upper()
                if symbol not in self.symbols: continue

                price = float(event.get('p', 0))
                quantity = float(event.get('q', 0))
                is_buyer_maker = event.get('m', False)
                current_time = datetime.utcnow()

                with self.data_lock:
                    self.last_prices[symbol] = price
                    volume_type = 'market_sell' if is_buyer_maker else 'market_buy'
                    self.volume_accumulator[symbol][volume_type] += quantity
                    
                    # Update candle saat ini
                    if symbol in self.current_candle:
                        # Update high dan low
                        self.current_candle[symbol]['high'] = max(
                            self.current_candle[symbol].get('high', 0), 
                            price
                        )
                        self.current_candle[symbol]['low'] = min(
                            self.current_candle[symbol].get('low', float('inf')), 
                            price
                        )
                        self.current_candle[symbol]['volume'] += quantity

                    # Simpan harga terakhir
                    self.price_history[symbol].append((current_time, price))

            except queue.Empty:
                continue
            except Exception as e:
                logger.error(f"Error prosesor perdagangan: {e}")
     
    def _calculate_adaptive_threshold(self, symbol: str, now: datetime) -> Tuple[float, float]:
        """Hitung rata-rata likuidasi untuk menentukan threshold adaptif"""
        with self.data_lock:
            history = list(self.liquidation_history.get(symbol, deque()))
        
        cutoff_time = now - timedelta(minutes=self.LIQ_HISTORY_WINDOW)
        total_buy = 0.0
        total_sell = 0.0
        count = 0
        
        for timestamp, buy_qty, sell_qty in history:
            if timestamp >= cutoff_time:
                total_buy += buy_qty
                total_sell += sell_qty
                count += 1
        
        avg_buy = total_buy / count if count > 0 else 0
        avg_sell = total_sell / count if count > 0 else 0
        
        buy_threshold = avg_buy * 1.5
        sell_threshold = avg_sell * 1.5
        
        return buy_threshold, sell_threshold

    def _signal_detector(self):
        """Thread untuk mendeteksi sinyal kuat dan menyimpannya ke database"""
        while not self.shutdown_event.is_set():
            try:
                time.sleep(self.SIGNAL_DETECTION_INTERVAL)  # Cek setiap 10 detik
                now = datetime.utcnow()
                current_candle = now.replace(second=0, microsecond=0)
                
                # Untuk candle 15m, bulatkan menit ke kelipatan 15
                current_candle = current_candle.replace(
                    minute=(current_candle.minute // 15) * 15
                )
                
                for symbol in self.symbols:
                    if self.shutdown_event.is_set():
                        break
                    
                    try:
                        with self.data_lock:
                            last_price = self.last_prices.get(symbol, 0.0)
                            mark_price = self.mark_prices.get(symbol, 0.0)
                            d = self.display_data.get(symbol, {})
                            current_oi = d.get('open_interest', 0)
                            # PERBAIKAN: TAAHKAN TANDA SAMA DENGAN (=) DI SINI
                            previous_oi_val = self.previous_oi.get(symbol, 0)
                            funding_rate = d.get('funding_rate', 0)
                            liq = self.liquidation_accumulator.get(symbol, {})
                            vol = self.volume_accumulator.get(symbol, {})
                            order_book = self.order_books.get(symbol, {})
                            burst_threshold = self.burst_thresholds.get(symbol, {'burst_buy_threshold': 50000, 'burst_sell_threshold': 50000})
                            current_candle_data = self.current_candle.get(symbol, {})
                            previous_candle_data = self.previous_candle.get(symbol, {})
                            atr14 = self.atr_values.get(symbol, 0.0)

                        # Skip jika data tidak lengkap
                        if last_price == 0.0 or mark_price == 0.0:
                            continue

                        # Hitung rasio volume
                        buy_vol_candle = vol.get('market_buy', 0)
                        sell_vol_candle = vol.get('market_sell', 0)  # PERBAIKAN: TAMBAHKAN = DAN PERBAIKI VARIABEL
                        total_vol_candle = buy_vol_candle + sell_vol_candle
                        
                        if total_vol_candle > 0:
                            buy_ratio = (buy_vol_candle / total_vol_candle) * 100
                            sell_ratio = (sell_vol_candle / total_vol_candle) * 100
                        else:
                            buy_ratio = 0.0
                            sell_ratio = 0.0

                        # Hitung threshold adaptif
                        buy_threshold, sell_threshold = self._calculate_adaptive_threshold(symbol, now)
                        
                        # === DETEKSI BURST LIQ TERBARU (2 MENIT) ===
                        cutoff_burst = now - timedelta(minutes=2)
                        burst_buy = 0.0
                        burst_sell = 0.0
                        for t, buy, sell in self.liquidation_history.get(symbol, []):
                            if t >= cutoff_burst:
                                burst_buy += buy
                                burst_sell += sell
                        
                        # ===== SISTEM SKORING TRADING =====
                        score = 0
                        
                        # 1. Perubahan Open Interest
                        if previous_oi_val > 0:
                            oi_change_percent = ((current_oi - previous_oi_val) / previous_oi_val) * 100
                        else:
                            oi_change_percent = 0.0
                        
                        if oi_change_percent > 2:
                            score += 2
                        elif oi_change_percent < -2:
                            score -= 2
                        
                        # 2. Dominasi Volume
                        if buy_ratio > 60:
                            score += 2
                        elif sell_ratio > 60:
                            score -= 2
                        
                        # 3. Funding Rate (versi adaptif)
                        fund_hist = list(self.funding_history.get(symbol, []))
                        if len(fund_hist) >= 10:
                            avg_fund = sum(fund_hist) / len(fund_hist)
                            deviation = funding_rate - avg_fund
                            if deviation < -0.0003:
                                score += 1
                            elif deviation > 0.0003:
                                score -= 1
                        else:
                            # Fallback ke logika lama jika belum cukup data
                            if funding_rate < 0:
                                score += 1
                            elif funding_rate > 0.0005:
                                score -= 1
                        
                        # 4. Likuidasi Squeeze (rata-rata jangka menengah)
                        liq_sell_usd = liq.get('sell', 0) * mark_price
                        liq_buy_usd = liq.get('buy', 0) * mark_price
                        
                        if liq_sell_usd > sell_threshold:  
                            score -= 3
                        elif liq_buy_usd > buy_threshold: 
                            score += 3
                        
                        # === PENINGKATAN: VOLUME BREAKOUT ===
                        prev_volume = previous_candle_data.get('volume', 0)
                        current_volume = current_candle_data.get('volume', 0)
                        volume_breakout = False
                        
                        if prev_volume > 0 and current_volume > prev_volume * 1.5:
                            volume_breakout = True
                            score += 1  # Bonus untuk volume tinggi
                        
                        # === PENINGKATAN: HIGH/LOW BREAKOUT ===
                        prev_high = previous_candle_data.get('high', 0)
                        prev_low = previous_candle_data.get('low', float('inf'))
                        current_high = current_candle_data.get('high', 0)
                        current_low = current_candle_data.get('low', float('inf'))
                        
                        if current_high > prev_high:
                            score += 1
                        if current_low < prev_low:
                            score -= 1
                        
                        # === PENINGKATAN: DETEKSI ANOMALI BURST VOLUME + LIKUIDASI SIMULTAN ===
                        burst_sell_threshold = burst_threshold.get('burst_sell_threshold', 50000)
                        burst_buy_threshold = burst_threshold.get('burst_buy_threshold', 50000)
                        
                        burst_sell_usd = burst_sell * mark_price
                        burst_buy_usd = burst_buy * mark_price
                        
                        if volume_breakout and burst_sell_usd > burst_sell_threshold:
                            # Anomali: Volume tinggi + likuidasi sell besar
                            score += 3
                            logger.warning(f"ANOMALI {symbol}: Burst volume + likuidasi SELL besar: {burst_sell_usd:.2f} USD")
                            
                        if volume_breakout and burst_buy_usd > burst_buy_threshold:
                            # Anomali: Volume tinggi + likuidasi buy besar
                            score -= 3
                            logger.warning(f"ANOMALI {symbol}: Burst volume + likuidasi BUY besar: {burst_buy_usd:.2f} USD")
                        
                        # 5. Interpretasi Skor (Hanya simpan sinyal kuat)
                        if score >= 6:  # Threshold dinaikkan karena penambahan faktor
                            signal = "LONG"
                        elif score <= -6:
                            signal = "SHORT"
                        else:
                            signal = "HOLD"
                        # ===== END SISTEM SKORING =====
                        # === UPDATE TABEL T_Aset ===
                        # Update hanya jika sinyal atau skor berubah
                        last_signal = self.last_signals.get(symbol)
                        last_score = self.current_scores.get(symbol)

                        if last_signal != signal or last_score != score:
                            # Perbarui dengan data likuidasi terkini
                            self._update_aset_table(
                                symbol, 
                                signal, 
                                score,
                                liquidation_buy,
                                liquidation_sell
                            )
                            self.last_signals[symbol] = signal
                            self.current_scores[symbol] = score

                        

                        # Validasi kondisi pasar
                        valid_signal = True
                        
                        # Validasi 1: Cek ketersediaan data order book
                        if not order_book.get('bids') or not order_book.get('asks'):
                            valid_signal = False
                        else:
                            # Validasi 2: Hitung spread
                            bid_price = float(order_book['bids'][0][0])
                            ask_price = float(order_book['asks'][0][0])
                            spread = ask_price - bid_price
                            
                            # Validasi 3: Cek kedalaman order book
                            depth_threshold = mark_price * 0.001  # 0.1% dari harga
                            valid_depth = True
                            
                            # Cek 5 level teratas di bids
                            for level in order_book['bids'][:5]:
                                price, qty = float(level[0]), float(level[1])
                                if price * qty < depth_threshold:
                                    valid_depth = False
                                    break
                            
                            # Cek 5 level teratas di asks
                            if valid_depth:
                                for level in order_book['asks'][:5]:
                                    price, qty = float(level[0]), float(level[1])
                                    if price * qty < depth_threshold:
                                        valid_depth = False
                                        break

                            # === PENINGKATAN: VALIDASI SPREAD DENGAN ATR ===
                            valid_spread = spread < atr14 * 0.5 if atr14 > 0 else spread < mark_price * 0.002

                            # Skip jika tidak memenuhi syarat
                            if not valid_spread or not valid_depth:
                                valid_signal = False
                        
                        if valid_signal and signal in ["LONG", "SHORT"]:  # Hanya simpan sinyal LONG/SHORT yang valid
                            # Simpan sinyal ke database dengan validasi periode
                            self._save_signal(symbol, mark_price, signal, score, current_candle)
                            
                    except Exception as e:
                        logger.error(f"Error deteksi sinyal untuk {symbol}: {e}")
                
            except Exception as e:
                logger.error(f"Error pada signal detector: {e}")

    def run(self):
        os.system('cls' if os.name == 'nt' else 'clear')
        print("Memuat daftar simbol...")
        self._load_symbol_list()
        self._initialize_data_structures()
        self._initialize_order_books()

        print("Memulai thread-thread pekerja...")
        # Pisahkan koneksi WebSocket untuk setiap stream
        stream_configs = [
            ('Liquidation', self.LIQUIDATION_WS_URL, self._handle_liquidation_stream),
            ('MarkPrice', self.MARK_PRICE_WS_URL, self._handle_mark_price_stream),
            ('Kline', self.BASE_WS_URL + "/".join([f"{s.lower()}@kline_{self.INTERVAL}" for s in self.symbols]), self._handle_kline_stream),
            ('Trade', self.BASE_WS_URL + "/".join([f"{s.lower()}@aggTrade" for s in self.symbols]), self._handle_trade_stream),
            ('Depth', self.BASE_WS_URL + "/".join([f"{s.lower()}@depth{self.ORDERBOOK_DEPTH_LEVEL}@500ms" for s in self.symbols]), self._handle_depth_stream),
        ]

        threads = [
            threading.Thread(target=self._liquidation_processor, name="LiqProcessor", daemon=True),
            threading.Thread(target=self._trade_processor, name="TradeProcessor", daemon=True),
            threading.Thread(target=self._depth_processor, name="DepthProcessor", daemon=True),
            threading.Thread(target=self._periodic_data_updater, name="PeriodicUpdater", daemon=True),
            threading.Thread(target=self._signal_detector, name="SignalDetector", daemon=True),
        ]

        # Tambahkan thread untuk setiap stream config
        for name, url, handler in stream_configs:
            threads.append(threading.Thread(
                target=self._websocket_connector, 
                args=(url, name, handler), 
                name=f"WS-{name}", 
                daemon=True
            ))

        for t in threads: 
            t.start()

        print("Signal detector berjalan. Tekan Ctrl+Ck berhenti.")
        try:
            while not self.shutdown_event.is_set():
                time.sleep(1)
        except KeyboardInterrupt:
            self.shutdown_event.set()
            print("\nMenghentikan semua thread...")
            for t in threads:
                if t.is_alive():
                    t.join(timeout=5)
            print("Program dihentikan.")

if __name__ == "__main__":
    try:
        app = SignalDetector()
        app.run()
    except Exception as e:
        logger.critical(f"Terjadi error fatal: {e}", exc_info=True)
        print(f"\nTerjadi error fatal. Periksa file 'futures_signal_detector.log' untuk detail.")
