import os
import requests
import time
import logging
import threading
import json
import sys
import queue
import curses
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
from decimal import Decimal

# Load environment variables
load_dotenv()

# Setup logging - HANYA KE FILE
logging.basicConfig(
    level=logging.DEBUG,  # Ubah ke DEBUG untuk troubleshooting
    format="%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s",
    handlers=[
        logging.FileHandler("futures_live.log", mode='a'),  # Mode append untuk melihat history
    ]
)
logger = logging.getLogger()

class FuturesTracker:
    # --- Konfigurasi ---
    SYMBOL_LIST_FILE = "listsymbol.txt"
    INTERVAL = "15m"
    MAX_CONCURRENT_REQUESTS = 20
    MAX_SYMBOLS = 150
    ORDERBOOK_DEPTH_LEVEL = 100
    LIQ_HISTORY_WINDOW = 15  # Menit untuk perhitungan rata-rata likuidasi
    BALANCE_PER_SYMBOL = 40.0  # Saldo $40 untuk setiap koin
    PROFIT_TARGET = 3.0  # Target profit $3
    LEVERAGE = 40  # Leverage 40x
    SLIPPAGE_TOLERANCE = 0.002  # 0.2% default
    MAX_SLIPPAGE_ALERT = 0.005  # 0.5% untuk warning
    MARGIN_MODE = "CROSSED"  # ISOLATED atau CROSSED
    SAFETY_MARGIN = 0.95  # Faktor keamanan 95% untuk margin
    ORDER_RETRY_DELAY = 5  # Detik antara percobaan ulang order
    WS_RECONNECT_BACKOFF_MAX = 60  # Maksimum backoff 60 detik
    DB_RELOAD_INTERVAL = 4  # Detik untuk reload data dari database
    
    # --- URL Endpoint ---
    LIQUIDATION_WS_URL = "wss://fstream.binance.com/ws/!forceOrder@arr"
    BASE_WS_URL = "wss://fstream.binance.com/stream?streams="
    EXCHANGE_INFO_URL = "https://fapi.binance.com/fapi/v1/exchangeInfo"
    PREMIUM_INDEX_URL = "https://fapi.binance.com/fapi/v1/premiumIndex"
    OPEN_INTEREST_URL = "https://fapi.binance.com/fapi/v1/openInterest"
    DEPTH_URL = "https://fapi.binance.com/fapi/v1/depth"
    MARK_PRICE_WS_URL = "wss://fstream.binance.com/ws/!markPrice@arr"
    ACCOUNT_BALANCE_URL = "https://fapi.binance.com/fapi/v2/balance"
    POSITION_RISK_URL = "https://fapi.binance.com/fapi/v2/positionRisk"
    
    # Konfigurasi Database
    SQL_SERVER = os.getenv("SQL_SERVER")
    SQL_DATABASE = os.getenv("SQL_DATABASE")
    SQL_USERNAME = os.getenv("SQL_USERNAME")
    SQL_PASSWORD = os.getenv("SQL_PASSWORD")
    SQL_DRIVER = os.getenv("SQL_DRIVER", "{ODBC Driver 17 for SQL Server}")

    # Binance API
    BINANCE_API_KEY = os.getenv("BINANCE_API_KEY")
    BINANCE_API_SECRET = os.getenv("BINANCE_API_SECRET")

    def __init__(self):
        self.symbols: List[str] = []
        self.valid_symbols: Set[str] = set()
        self.shutdown_event = threading.Event()
        self.data_lock = threading.Lock()
        self.symbol_info_cache: Dict[str, Dict] = {}  # Cache untuk info simbol
        self.leverage_set: Set[str] = set()  # Simpan simbol yang sudah diatur leverage
        self.total_balance = 0.0  # Total saldo akun
        self.used_margin = 0.0   # Margin yang sedang digunakan
        
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
        
        # Menyimpan data dari stored procedure
        self.symbol_info_db: Dict[str, Dict] = {}  # {symbol: {id, price_open, posisi, posisi_ch, signal_score, signal_ch}}
        
        # Cache untuk volatility dan spread_threshold
        self.volatility_cache: Dict[str, float] = {}
        self.spread_threshold_cache: Dict[str, float] = {}
        self.threshold_last_updated: Dict[str, float] = {}
        
        # Cache untuk burst liquidation threshold
        self.burst_threshold_cache: Dict[str, Dict[str, float]] = {}  # {symbol: {'buy': float, 'sell': float}}
        self.burst_threshold_last_updated: Dict[str, float] = {}
        
        # Cache untuk data database terakhir per simbol
        self.last_db_data: Dict[str, Dict] = {}  # Format: {symbol: {'id': ..., 'posisi': ..., 'price_open': ..., 'posisi_ch': ..., 'signal_ch': ...}}
        
        self.liquidation_queue = queue.Queue()
        self.trade_queue = queue.Queue()
        self.trading_queue = queue.Queue()  # Queue untuk eksekusi trading
        self.depth_queue = queue.Queue()  # Queue untuk depth updates
        
        # Menyimpan posisi terbuka {symbol: (position, price_open, qty, leverage, order_id, unrealized_pnl, db_id, db_posisi, db_signal_ch)}
        self.open_positions: Dict[str, Tuple] = {}  
        self.position_lock = threading.Lock()
        
        # Untuk mencegah race condition
        self.processing_symbols = set()
        self.processing_lock = threading.Lock()
        
        # Queue untuk retry leverage setting
        self.leverage_retry_queue = queue.Queue()
        
        # Untuk menandai order yang sedang diproses
        self.pending_orders = set()
        self.request_semaphore = threading.Semaphore(self.MAX_CONCURRENT_REQUESTS)
        # Flag untuk reload simbol
        self.symbols_reload_needed = False
        self.symbols_reload_time = time.time()
        self.reload_lock = threading.Lock()
        
        # Cache untuk realized PnL
        self.pnl_real_cache: Dict[int, float] = {}
        
        # Untuk penanda status trading
        self.trading_active = True

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

    def _save_trade_to_db(self, symbol: str, price_open: float, position: str, 
                         qty: float, leverage: int, binance_order_id: str, 
                         status: int = 1, signal_score: int = 0) -> Optional[int]:
        """Menyimpan eksekusi trading ke database dengan order ID, mengembalikan ID baris yang dibuat"""
        conn = self._get_db_connection()
        if not conn:
            return None
            
        # Validasi data sebelum disimpan
        if price_open <= 0 or qty <= 0 or leverage <= 0:
            logger.error(f"Data tidak valid untuk disimpan: price_open={price_open}, qty={qty}, leverage={leverage}")
            return None
            
        # Hitung SL/TP berdasarkan arah posisi
        if position == "LONG":
            stop_loss = price_open * 0.99  # -1%
            take_profit = price_open * 1.03  # +3%
        else:  # SHORT
            stop_loss = price_open * 1.01  # +1%
            take_profit = price_open * 0.97  # -3%
        
        fee = price_open * qty * 0.0004  # Fee 0.04%
        
        try:
            cursor = conn.cursor()
            # Periksa apakah sudah ada posisi aktif untuk simbol ini
            cursor.execute("SELECT COUNT(*) FROM tran_TF WHERE symbol = ? AND status IN (1, 2)", (symbol,))
            row = cursor.fetchone()
            if row and row[0] > 0:
                logger.error(f"Posisi aktif atau pending untuk {symbol} sudah ada di database, tidak disimpan lagi.")
                return None
                
            query = """
                INSERT INTO tran_TF (
                    symbol, price_open, price_close, status, posisi, 
                    stop_lose, take_profit, feebinance, timestamp, qty, leverage, binance_order_id, signal_score
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);
                SELECT SCOPE_IDENTITY();
            """
            params = (
                symbol, price_open, 0.0, status, position, 
                stop_loss, take_profit, fee, datetime.utcnow(), qty, leverage, binance_order_id, signal_score
            )
            cursor.execute(query, params)
            # Dapatkan ID baris yang baru dibuat
            row_id = cursor.fetchone()[0]
            conn.commit()
            logger.info(
                f"Trade disimpan: {symbol} {position} @ {price_open:.5f}, "
                f"SL={stop_loss:.5f}, TP={take_profit:.5f}, order_id={binance_order_id}, status={status}, id={row_id}"
            )
            return row_id
        except Exception as e:
            logger.error(f"Gagal menyimpan trade: {e}")
            return None
        finally:
            conn.close()

    def _update_trade_in_db(self, trade_id: int, price_close: float, binance_close_id: str) -> bool:
        """Update posisi saat closing dengan ID baris dan hitung realized PnL"""
        conn = self._get_db_connection()
        if not conn:
            return False
            
        try:
            cursor = conn.cursor()
            # Ambil data entry dari database
            cursor.execute("SELECT price_open, qty, posisi FROM tran_TF WHERE id = ?", (trade_id,))
            row = cursor.fetchone()
            if not row:
                logger.warning(f"Data tidak ditemukan untuk ID {trade_id}")
                return False

            entry_price = float(row.price_open)
            qty_val = float(row.qty)
            posisi = row.posisi
            fee_rate = 0.0004  # Fee 0.04%

            # Hitung total fee 2 arah
            total_fee = (entry_price + price_close) * qty_val * fee_rate
            
            # Hitung PnL berdasarkan arah posisi
            if posisi == "LONG":
                realized_pnl = (price_close - entry_price) * qty_val
            else:  # SHORT
                realized_pnl = (entry_price - price_close) * qty_val
                
            net_pnl = realized_pnl - total_fee

            query = """
                UPDATE tran_TF 
                SET price_close = ?, 
                    status = 0, 
                    timestamp = ?,
                    binance_close_id = ?,
                    pnl_real = ?
                WHERE id = ?
            """
            params = (price_close, datetime.utcnow(), binance_close_id, net_pnl, trade_id)
            cursor.execute(query, params)
            
            if cursor.rowcount == 0:
                logger.warning(f"Tidak ada posisi terbuka dengan ID {trade_id} atau sudah ditutup")
                return False
                
            conn.commit()
            logger.info(f"Posisi ditutup: ID={trade_id} @ {price_close:.5f}, close_id={binance_close_id}, Realized PnL: ${net_pnl:.2f}")
            return True
        except Exception as e:
            logger.error(f"Gagal update trade: {e}")
            return False
        finally:
            conn.close()

    def _load_open_positions(self):
        """Memuat posisi terbuka (status=1) dari database"""
        conn = self._get_db_connection()
        if not conn:
            return
            
        try:
            cursor = conn.cursor()
            cursor.execute("""
                SELECT id, symbol, posisi, price_open, qty, leverage, binance_order_id 
                FROM tran_TF 
                WHERE status = 1
            """)
            for row in cursor.fetchall():
                trade_id = row.id
                symbol = row.symbol
                position = row.posisi
                
                # Konversi Decimal ke float
                price_open = float(row.price_open)
                qty = float(row.qty)
                
                leverage = row.leverage
                order_id = row.binance_order_id or "N/A"
                
                # Inisialisasi unrealized PnL dengan 0
                unrealized_pnl = 0.0
                
                # Hitung initial PnL jika harga tersedia
                if symbol in self.mark_prices and price_open > 0:
                    if position == "LONG":
                        unrealized_pnl = qty * (self.mark_prices[symbol] - price_open)
                    else:  # SHORT
                        unrealized_pnl = qty * (price_open - self.mark_prices[symbol])
                
                # Simpan posisi
                self.open_positions[symbol] = (position, price_open, qty, leverage, order_id, unrealized_pnl, trade_id, "", "")
                
                logger.info(f"Memuat posisi terbuka: {symbol} {position} @ {price_open}, qty={qty}, leverage={leverage}, order_id={order_id}")
                
            logger.info(f"Memuat {len(self.open_positions)} posisi terbuka dari database")
        except Exception as e:
            logger.error(f"Gagal memuat posisi terbuka: {e}")
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

    def _fetch_symbols_from_db(self) -> List[Dict[str, Any]]:
        """Ambil daftar simbol dan kolom lain dari stored procedure sp_tranTF_last"""
        conn = self._get_db_connection()
        if not conn:
            logger.error("Tidak dapat terhubung ke database untuk mengambil simbol")
            return []
            
        try:
            cursor = conn.cursor()
            cursor.execute("exec sp_tranTF_last")
            columns = [column[0] for column in cursor.description]
            results = []
            for row in cursor.fetchall():
                row_dict = dict(zip(columns, row))
                # Pastikan konversi tipe data
                if 'price_open' in row_dict and row_dict['price_open'] is not None:
                    row_dict['price_open'] = float(row_dict['price_open'])
                # Tambahkan kolom baru
                results.append(row_dict)
            logger.info(f"Memuat {len(results)} simbol dari database")
            return results
        except Exception as e:
            logger.error(f"Gagal mengambil simbol dari database: {e}")
            return []
        finally:
            conn.close()

    def _get_account_balance(self):
        """Dapatkan saldo total akun dari Binance"""
        if not self.BINANCE_API_KEY or not self.BINANCE_API_SECRET:
            logger.error("API Key/Secret Binance tidak ditemukan")
            return 0.0
            
        try:
            timestamp = int(time.time() * 1000)
            payload = {"timestamp": timestamp}
            
            # Generate signature
            query_string = urllib.parse.urlencode(payload)
            signature = hmac.new(
                self.BINANCE_API_SECRET.encode('utf-8'),
                query_string.encode('utf-8'),
                hashlib.sha256
            ).hexdigest()
            payload["signature"] = signature

            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            
            response = self.session.get(
                self.ACCOUNT_BALANCE_URL,
                headers=headers,
                params=payload,
                timeout=5
            )
            response.raise_for_status()
            
            # Cari aset USDT
            for asset in response.json():
                if asset['asset'] == 'USDT':
                    self.total_balance = float(asset['balance'])
                    logger.info(f"Saldo akun: {self.total_balance:.2f} USDT")
                    return
                    
            logger.warning("Aset USDT tidak ditemukan di saldo akun")
            self.total_balance = 0.0
        except Exception as e:
            logger.error(f"Gagal mendapatkan saldo akun: {str(e)}")
            self.total_balance = 0.0

    def _get_position_risk(self):
        """Dapatkan risiko posisi untuk menghitung margin yang digunakan"""
        if not self.BINANCE_API_KEY or not self.BINANCE_API_SECRET:
            logger.error("API Key/Secret Binance tidak ditemukan")
            return
            
        try:
            timestamp = int(time.time() * 1000)
            payload = {"timestamp": timestamp}
            
            # Generate signature
            query_string = urllib.parse.urlencode(payload)
            signature = hmac.new(
                self.BINANCE_API_SECRET.encode('utf-8'),
                query_string.encode('utf-8'),
                hashlib.sha256
            ).hexdigest()
            payload["signature"] = signature

            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            
            response = self.session.get(
                self.POSITION_RISK_URL,
                headers=headers,
                params=payload,
                timeout=5
            )
            response.raise_for_status()
            
            # Hitung total margin yang digunakan
            total_used_margin = 0.0
            for position in response.json():
                if position['symbol'] in self.open_positions:
                    total_used_margin += float(position['initialMargin'])
            
            self.used_margin = total_used_margin
            logger.info(f"Margin digunakan: {self.used_margin:.2f} USDT")
        except Exception as e:
            logger.error(f"Gagal mendapatkan risiko posisi: {str(e)}")
            self.used_margin = 0.0

    def _load_symbol_list(self):
        # Ambil simbol dan data dari database menggunakan stored procedure
        symbols_data = self._fetch_symbols_from_db()
        if not symbols_data:
            sys.exit("Error: Tidak ada simbol dari database.")
            
        self.valid_symbols = self._fetch_valid_futures_symbols()
        if not self.valid_symbols:
            logger.warning("Gagal validasi simbol, menggunakan semua dari database.")

        validated_symbols = []
        self.symbol_info_db = {}  # Reset data
        self.last_db_data = {}    # Reset cache
        
        for data in symbols_data:
            symbol = data.get('symbol')
            if not symbol:
                continue
                
            if not self.valid_symbols or symbol in self.valid_symbols:
                validated_symbols.append(symbol)
                # Simpan semua data ke symbol_info_db dan last_db_data
                self.symbol_info_db[symbol] = data
                self.last_db_data[symbol] = data
                if len(validated_symbols) >= self.MAX_SYMBOLS:
                    break

        self.symbols = validated_symbols
        if not self.symbols:
            sys.exit("Error: Tidak ada simbol valid di dalam database.")
        logger.info(f"Akan melacak {len(self.symbols)} simbol dengan data dari database.")
        
    def _periodic_symbol_reloader(self):
        """Reload daftar simbol setiap kelipatan interval (15 menit)"""
        # Konversi interval ke detik
        interval_seconds = self._interval_to_seconds(self.INTERVAL)
        if interval_seconds <= 0:
            logger.error(f"Interval {self.INTERVAL} tidak valid")
            return

        while not self.shutdown_event.is_set():
            now = datetime.utcnow()
            # Hitung detik menuju kelipatan interval berikutnya
            next_time = now + timedelta(seconds=interval_seconds)
            # Bulatkan ke interval berikutnya (dengan menit:0, detik:0)
            next_time = next_time.replace(minute=(next_time.minute // (interval_seconds//60)) * (interval_seconds//60), second=0, microsecond=0)
            wait_seconds = (next_time - now).total_seconds()
            
            if wait_seconds <= 0:
                wait_seconds = interval_seconds

            logger.info(f"Menunggu {wait_seconds} detik hingga reload simbol berikutnya pada {next_time}")
            # Tunggu hingga waktu berikutnya, atau shutdown event
            self.shutdown_event.wait(wait_seconds)
            if self.shutdown_event.is_set():
                break

            # Lakukan reload
            logger.info("Memulai reload daftar simbol...")
            new_symbols_data = self._fetch_symbols_from_db()
            if not new_symbols_data:
                logger.warning("Gagal reload simbol dari database")
                continue

            # Validasi simbol baru
            validated_new_symbols = []
            new_symbol_info = {}
            
            for data in new_symbols_data:
                symbol = data.get('symbol')
                if not symbol:
                    continue
                    
                if not self.valid_symbols or symbol in self.valid_symbols:
                    validated_new_symbols.append(symbol)
                    new_symbol_info[symbol] = data
                    if len(validated_new_symbols) >= self.MAX_SYMBOLS:
                        break

            # Bandingkan dengan simbol saat ini
            with self.reload_lock:
                if set(validated_new_symbols) != set(self.symbols) or any(
                    self.symbol_info_db.get(s) != new_symbol_info.get(s) for s in validated_new_symbols
                ):
                    logger.info("Perubahan daftar simbol atau data terdeteksi, melakukan reload...")
                    self.symbols = validated_new_symbols
                    self.symbol_info_db = new_symbol_info
                    # Set flag untuk reload di dashboard
                    self.symbols_reload_needed = True
                    logger.info(f"Reload simbol selesai. Sekarang melacak {len(self.symbols)} simbol.")
                else:
                    logger.info("Tidak ada perubahan pada daftar simbol.")

    def _periodic_db_reloader(self):
        """Reload data dari stored procedure setiap 12 detik"""
        while not self.shutdown_event.is_set():
            # Tunggu 12 detik
            time.sleep(self.DB_RELOAD_INTERVAL)
            if self.shutdown_event.is_set():
                break
                
            logger.info("Memulai reload data dari stored procedure...")
            new_data = self._fetch_symbols_from_db()
            if not new_data:
                logger.warning("Gagal reload data dari database")
                continue
                
            # Buat mapping: symbol -> data
            new_data_map = {item['symbol']: item for item in new_data}
            
            with self.reload_lock:
                # Update hanya untuk simbol yang sedang dilacak
                for symbol in self.symbols:
                    if symbol in new_data_map:
                        new_info = new_data_map[symbol]
                        old_info = self.last_db_data.get(symbol, {})
                        
                        # Simpan price_open lama sebelum pembaruan
                        old_price_open = old_info.get('price_open', 0.0)
                        
                        # Periksa perubahan pada field kunci
                        fields_to_check = ['id', 'posisi', 'price_open', 'posisi_ch', 'signal_ch']
                        changed = False
                        changes_log = []
                        for field in fields_to_check:
                            old_val = old_info.get(field)
                            new_val = new_info.get(field)
                            if old_val != new_val:
                                changed = True
                                changes_log.append(f"{field}: {old_val} -> {new_val}")
                        
                        # Jika price_open baru kosong atau 0, gunakan yang lama
                        if new_info.get('price_open') in (None, 0.0) and old_price_open > 0:
                            new_info['price_open'] = old_price_open
                            if 'price_open' in changes_log:
                                changes_log.remove(f"price_open: {old_price_open} -> {new_val}")
                                if not changes_log:
                                    changed = False
                            logger.warning(f"Perbaikan price_open untuk {symbol}: menggunakan nilai lama {old_price_open}")
                        
                        # Skip update jika price_open masih 0
                        if new_info.get('price_open') == 0.0:
                            logger.warning(f"Ignore update {symbol}: price_open=0")
                            continue
                            
                        if changed:
                            logger.info(f"Perubahan data untuk {symbol}: {', '.join(changes_log)}")
                            # Update cache terakhir
                            self.last_db_data[symbol] = new_info
                            # Update data yang digunakan di aplikasi
                            self.symbol_info_db[symbol] = new_info
                        # Jika belum ada cache (pertama kali), isi cache
                        elif symbol not in self.last_db_data:
                            self.last_db_data[symbol] = new_info
                            self.symbol_info_db[symbol] = new_info
            logger.info("Reload data selesai.")

    def _interval_to_seconds(self, interval: str) -> int:
        """Convert interval string to seconds"""
        unit = interval[-1]
        if unit == 'm':
            return int(interval[:-1]) * 60
        elif unit == 'h':
            return int(interval[:-1]) * 3600
        elif unit == 'd':
            return int(interval[:-1]) * 86400
        else:
            logger.error(f"Unit interval tidak dikenali: {unit}")
            return 0

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
                # Inisialisasi cache threshold
                self.volatility_cache[symbol] = 0.0
                self.spread_threshold_cache[symbol] = 0.002  # Default value
                self.threshold_last_updated[symbol] = 0.0
                # Inisialisasi cache burst threshold
                self.burst_threshold_cache[symbol] = {'buy': 0.0, 'sell': 0.0}
                self.burst_threshold_last_updated[symbol] = 0.0
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
        oi_data = self._fetch_api_data(self.OPEN_INTEREST_URL, {"symbol": symbol})
        funding_data = self._fetch_api_data(self.PREMIUM_INDEX_URL, {"symbol": symbol})

        with self.data_lock:
            # Simpan OI USD saat ini sebagai OI periode berikutnya
            current_oi_usd = self.display_data[symbol].get('oi_usd', 0)
            self.display_data[symbol]['prev_oi_usd'] = current_oi_usd
            
            if funding_data: 
                self.display_data[symbol]['funding_rate'] = float(funding_data.get("lastFundingRate", 0))
            if oi_data: 
                oi_value = float(oi_data.get("openInterest", 0))
                self.display_data[symbol]['open_interest'] = oi_value
                self.display_data[symbol]['oi_usd'] = oi_value * self.mark_prices.get(symbol, 0)
            
            self.liquidation_accumulator[symbol] = {'buy': 0.0, 'sell': 0.0}
            self.volume_accumulator[symbol] = {'market_buy': 0.0, 'market_sell': 0.0}
            self.display_data[symbol]['last_update'] = datetime.utcnow()
        logger.info(f"Reset akumulator dan update OI untuk {symbol}")

    def _periodic_data_updater(self):
        while not self.shutdown_event.is_set():
            time.sleep(60)  # Cek setiap 60 detik
            logger.info("Memulai pembaruan data periodik...")
            for symbol in self.symbols:
                if self.shutdown_event.is_set(): break
                funding_data = self._fetch_api_data(self.PREMIUM_INDEX_URL, {"symbol": symbol})
                oi_data = self._fetch_api_data(self.OPEN_INTEREST_URL, {"symbol": symbol})
                with self.data_lock:
                    if symbol not in self.display_data: continue
                    
                    if funding_data: 
                        self.display_data[symbol]['funding_rate'] = float(funding_data.get("lastFundingRate", 0))
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
                sleep_time = min(backoff, self.WS_RECONNECT_BACKOFF_MAX)
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
                    
                    # Perbarui unrealized PnL untuk posisi terbuka
                    with self.position_lock:
                        if symbol in self.open_positions:
                            position, entry_price, qty, leverage, order_id, _, db_id, db_posisi, db_signal_ch = self.open_positions[symbol]
                            
                            # Hitung nilai posisi dalam USDT
                            position_value = qty * entry_price
                            
                            # Hitung unrealized PnL berdasarkan mark price
                            if position == "LONG":
                                unrealized_pnl = qty * (mark_price - entry_price)
                            else:  # SHORT
                                unrealized_pnl = qty * (entry_price - mark_price)
                            
                            # Simpan PnL baru
                            self.open_positions[symbol] = (position, entry_price, qty, leverage, order_id, unrealized_pnl, db_id, db_posisi, db_signal_ch)

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

            except queue.Empty:
                continue
            except Exception as e:
                logger.error(f"Error prosesor perdagangan: {e}")
    
    def _get_volatility_and_threshold(self, symbol: str) -> Tuple[float, float]:
        """Dapatkan volatility dan spread threshold dari database"""
        current_time = time.time()
        # Cek cache terlebih dahulu (cache berlaku 5 menit)
        if current_time - self.threshold_last_updated.get(symbol, 0) < 300:
            return self.volatility_cache.get(symbol, 0.0), self.spread_threshold_cache.get(symbol, 0.002)
        
        conn = self._get_db_connection()
        if not conn:
            return self.volatility_cache.get(symbol, 0.0), self.spread_threshold_cache.get(symbol, 0.002)
            
        try:
            cursor = conn.cursor()
            # Eksekusi stored procedure
            cursor.execute("EXEC sp_calculate_spread_threshold @symbol=?, @rows=?, @multiplier=?", 
                           (symbol, 20, 2.5))
            row = cursor.fetchone()
            if row:
                volatility = float(row.volatility)
                spread_threshold = float(row.spread_threshold)
                # Update cache
                with self.data_lock:
                    self.volatility_cache[symbol] = volatility
                    self.spread_threshold_cache[symbol] = spread_threshold
                    self.threshold_last_updated[symbol] = current_time
                logger.info(f"Volatilitas untuk {symbol}: {volatility:.6f}, Spread threshold: {spread_threshold:.6f}")
                return volatility, spread_threshold
            else:
                logger.warning(f"Tidak ada data threshold untuk {symbol} dari stored procedure")
                return self.volatility_cache.get(symbol, 0.0), self.spread_threshold_cache.get(symbol, 0.002)
        except Exception as e:
            logger.error(f"Gagal panggil stored procedure untuk {symbol}: {e}")
            return self.volatility_cache.get(symbol, 0.0), self.spread_threshold_cache.get(symbol, 0.002)
        finally:
            conn.close()

    def _get_burst_threshold(self, symbol: str) -> Tuple[float, float]:
        """Dapatkan burst threshold dari stored procedure sp_burst_liquidation_threshold"""
        current_time = time.time()
        # Cek cache terlebih dahulu (cache berlaku 5 menit)
        if current_time - self.burst_threshold_last_updated.get(symbol, 0) < 300:
            cache = self.burst_threshold_cache.get(symbol, {})
            return cache.get('buy', 0.0), cache.get('sell', 0.0)
        
        conn = self._get_db_connection()
        if not conn:
            return self.burst_threshold_cache.get(symbol, {}).get('buy', 0.0), self.burst_threshold_cache.get(symbol, {}).get('sell', 0.0)
            
        try:
            cursor = conn.cursor()
            # Eksekusi stored procedure
            cursor.execute("EXEC sp_burst_liquidation_threshold @symbol=?, @days_back=3, @sensitivity=2.5", (symbol,))
            row = cursor.fetchone()
            if row:
                buy_threshold = float(row.burst_buy_threshold)
                sell_threshold = float(row.burst_sell_threshold)
                # Update cache
                with self.data_lock:
                    self.burst_threshold_cache[symbol] = {
                        'buy': buy_threshold,
                        'sell': sell_threshold
                    }
                    self.burst_threshold_last_updated[symbol] = current_time
                logger.info(f"Burst threshold untuk {symbol}: Buy={buy_threshold:.2f}, Sell={sell_threshold:.2f}")
                return buy_threshold, sell_threshold
            else:
                logger.warning(f"Tidak ada data burst threshold untuk {symbol} dari stored procedure")
                return self.burst_threshold_cache.get(symbol, {}).get('buy', 0.0), self.burst_threshold_cache.get(symbol, {}).get('sell', 0.0)
        except Exception as e:
            logger.error(f"Gagal panggil stored procedure burst threshold untuk {symbol}: {e}")
            return self.burst_threshold_cache.get(symbol, {}).get('buy', 0.0), self.burst_threshold_cache.get(symbol, {}).get('sell', 0.0)
        finally:
            conn.close()

    def _get_symbol_info(self, symbol: str) -> Optional[Dict]:
        """Dapatkan info simbol untuk validasi harga dan quantity"""
        if symbol in self.symbol_info_cache:
            return self.symbol_info_cache[symbol]
            
        try:
            response = self.session.get(self.EXCHANGE_INFO_URL, timeout=10)
            response.raise_for_status()
            data = response.json()
            for s in data['symbols']:
                if s['symbol'] == symbol:
                    self.symbol_info_cache[symbol] = s
                    return s
            return None
        except Exception as e:
            logger.error(f"Gagal dapatkan info simbol {symbol}: {e}")
            return None

    def _set_margin_mode(self, symbol: str) -> bool:
        """Atur margin mode (ISOLATED/CROSSED) untuk simbol"""
        try:
            timestamp = int(time.time() * 1000)
            payload = {
                "symbol": symbol,
                "marginType": self.MARGIN_MODE,
                "timestamp": timestamp
            }
            
            # Generate signature menggunakan query string
            query_string = urllib.parse.urlencode(payload)
            signature = hmac.new(
                self.BINANCE_API_SECRET.encode('utf-8'),
                query_string.encode('utf-8'),
                hashlib.sha256
            ).hexdigest()
            payload["signature"] = signature

            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            
            # Kirim sebagai query parameter (bukan form data)
            response = self.session.post(
                "https://fapi.binance.com/fapi/v1/marginType",
                headers=headers,
                params=payload,
                timeout=5
            )
            
            # Tangani response khusus
            if response.status_code == 400:
                error_data = response.json()
                if error_data.get('code') == -4046:  # Margin type sudah sesuai
                    logger.info(f"Margin mode sudah {self.MARGIN_MODE} untuk {symbol}")
                    return True
                if error_data.get('code') == -4047:  # Ada posisi terbuka
                    logger.warning(f"Tidak bisa ubah margin type untuk {symbol} karena ada posisi terbuka")
                    return False
            
            response.raise_for_status()
            logger.info(f"Margin mode {self.MARGIN_MODE} berhasil diatur untuk {symbol}")
            return True
        except Exception as e:
            logger.error(f"Gagal atur margin mode untuk {symbol}: {str(e)}")
            return False

    def _set_leverage(self, symbol: str) -> bool:
        """Atur leverage untuk simbol tertentu di Binance"""
        try:
            timestamp = int(time.time() * 1000)
            payload = {
                "symbol": symbol,
                "leverage": self.LEVERAGE,
                "timestamp": timestamp
            }
            
            # Generate signature
            query_string = urllib.parse.urlencode(payload)
            signature = hmac.new(
                self.BINANCE_API_SECRET.encode('utf-8'),
                query_string.encode('utf-8'),
                hashlib.sha256
            ).hexdigest()
            payload["signature"] = signature

            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            
            # Kirim sebagai query parameter
            response = self.session.post(
                "https://fapi.binance.com/fapi/v1/leverage",
                headers=headers,
                params=payload,
                timeout=5
            )
            
            # Tangani error khusus
            if response.status_code == 400:
                error_data = response.json()
                if error_data.get('code') == -4046:  # Leverage sudah sesuai
                    logger.info(f"Leverage sudah {self.LEVERAGE}x untuk {symbol}")
                    return True
            
            response.raise_for_status()
            logger.info(f"Leverage {self.LEVERAGE}x berhasil diatur untuk {symbol}")
            return True
        except Exception as e:
            logger.error(f"Gagal atur leverage {self.LEVERAGE}x untuk {symbol}: {str(e)}")
            return False

    def _execute_trade(self, symbol: str, side: str, qty: float) -> Optional[Dict]:
        """Eksekusi order market di Binance Futures"""
        if not self.BINANCE_API_KEY or not self.BINANCE_API_SECRET:
            logger.error("API Key/Secret Binance tidak ditemukan")
            return None

        try:
            # Validasi quantity menggunakan LOT_SIZE filter
            symbol_info = self._get_symbol_info(symbol)
            if symbol_info:
                lot_size_filter = next((f for f in symbol_info['filters'] if f['filterType'] == 'LOT_SIZE'), None)
                if lot_size_filter:
                    min_qty = float(lot_size_filter['minQty'])
                    step_size = float(lot_size_filter['stepSize'])
                    
                    # Validasi minimum quantity
                    if qty < min_qty:
                        logger.warning(f"Qty {qty:.6f} < minimum {min_qty} untuk {symbol}")
                        return None
                    
                    # Adjust quantity to step size
                    valid_qty = round(round(qty / step_size) * step_size, 8)
                    if valid_qty < min_qty:
                        logger.warning(f"Qty adjusted {valid_qty:.6f} < minimum {min_qty}")
                        return None
                        
                    qty = valid_qty
            else:
                logger.warning(f"Info simbol {symbol} tidak ditemukan, menggunakan qty asli")
                
            # Hitung timestamp
            timestamp = int(time.time() * 1000)
            
            # Persiapkan payload
            payload = {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": round(qty, 5),  # Bulatkan ke 5 desimal
                "timestamp": timestamp
            }

            # Generate signature
            query_string = urllib.parse.urlencode(payload)
            signature = hmac.new(
                self.BINANCE_API_SECRET.encode('utf-8'),
                query_string.encode('utf-8'),
                hashlib.sha256
            ).hexdigest()
            payload["signature"] = signature

            # Kirim request
            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            response = self.session.post(
                "https://fapi.binance.com/fapi/v1/order",
                headers=headers,
                params=payload,
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            # Tambahkan log untuk melihat pesan error dari Binance
            if hasattr(e, 'response') and e.response is not None:
                try:
                    error_data = e.response.json()
                    logger.error(f"Error response: {error_data}")
                except:
                    logger.error(f"Error response text: {e.response.text}")
            logger.error(f"Gagal eksekusi order: {e}")
            return None

    def _trading_executor(self):
        """Thread untuk eksekusi trading berdasarkan sinyal"""
        while not self.shutdown_event.is_set():
            try:
                # Tunggu sinyal trading dari queue
                symbol, action, mark_price = self.trading_queue.get(timeout=1)
                logger.info(f"Memulai proses trading untuk {symbol} {action} @ {mark_price}")
                
                # Cek apakah trading aktif
                if not self.trading_active:
                    logger.info("Trading dinonaktifkan, lewati eksekusi")
                    continue
                
                # Cegah eksekusi ganda
                with self.processing_lock:
                    if symbol in self.processing_symbols:
                        logger.info(f"Ignore {symbol}: Sedang diproses")
                        continue
                    self.processing_symbols.add(symbol)
                
                # Periksa apakah sudah ada posisi terbuka
                with self.position_lock:
                    if symbol in self.open_positions:
                        logger.info(f"Ignore {symbol}: Sudah ada posisi {self.open_positions[symbol][0]}")
                        with self.processing_lock:
                            self.processing_symbols.discard(symbol)
                        continue
                
                # Periksa apakah ada pending order untuk simbol ini
                if self._has_pending_order(symbol):
                    logger.info(f"Ignore {symbol}: Ada pending order")
                    with self.processing_lock:
                        self.processing_symbols.discard(symbol)
                    continue
                
                # Perbarui saldo dan margin
                self._get_account_balance()
                self._get_position_risk()
                
                # Hitung margin yang tersedia
                available_margin = max(0, self.total_balance - self.used_margin)
                
                # Jika margin yang tersedia tidak mencukupi
                if available_margin < self.BALANCE_PER_SYMBOL * self.SAFETY_MARGIN:
                    logger.warning(
                        f"Margin tidak cukup untuk {symbol}. "
                        f"Tersedia: {available_margin:.2f}, "
                        f"Diperlukan: {self.BALANCE_PER_SYMBOL * self.SAFETY_MARGIN:.2f} USDT"
                    )
                    with self.processing_lock:
                        self.processing_symbols.discard(symbol)
                    continue
                
                # 0. Atur margin mode dan leverage dengan retry
                if symbol not in self.leverage_set:
                    MAX_RETRIES = 3
                    success = False
                    
                    for attempt in range(MAX_RETRIES):
                        if self._set_margin_mode(symbol) and self._set_leverage(symbol):
                            success = True
                            break
                        time.sleep(2)  # Tunggu sebelum retry
                    
                    if success:
                        self.leverage_set.add(symbol)
                        time.sleep(0.5)  # Beri waktu untuk Binance memproses
                    else:
                        logger.error(f"Gagal atur leverage setelah {MAX_RETRIES} percobaan, skip {symbol}")
                        with self.processing_lock:
                            self.processing_symbols.discard(symbol)
                        continue
                
                # Pastikan price_open valid (tidak 0)
                price_open = self.symbol_info_db.get(symbol, {}).get('price_open', 0.0)
                if price_open <= 0:
                    logger.error(f"Harga open tidak valid untuk {symbol}: {price_open}. Skip trading.")
                    with self.processing_lock:
                        self.processing_symbols.discard(symbol)
                    continue
                
                # 1. Hitung harga estimasi dengan mempertimbangkan slippage terburuk
                # Untuk menjamin margin cukup, gunakan worst-case scenario
                if action == "LONG":
                    # Untuk LONG: harga terburuk adalah harga lebih tinggi (slippage positif)
                    worst_case_price = mark_price * (1 + self.SLIPPAGE_TOLERANCE)
                else:  # SHORT
                    # Untuk SHORT: harga terburuk adalah harga lebih rendah (slippage negatif)
                    worst_case_price = mark_price * (1 - self.SLIPPAGE_TOLERANCE)
                
                # 2. Hitung kuantitas berdasarkan worst-case scenario dengan safety margin
                allocated_balance = min(
                    self.BALANCE_PER_SYMBOL * self.SAFETY_MARGIN,
                    available_margin
                )
                qty = (allocated_balance * self.LEVERAGE) / worst_case_price
                
                # 3. Tentukan sisi order
                order_side = "BUY" if action == "LONG" else "SELL"
                
                # 4. Eksekusi order di Binance
                logger.info(f"Eksekusi {action} untuk {symbol} @ {mark_price:.5f}, qty={qty:.5f} (worst-case: {worst_case_price:.5f})")
                order_result = self._execute_trade(symbol, order_side, qty)
                
                if order_result and order_result.get("orderId"):
                    order_id = str(order_result["orderId"])
                    execution_price = float(order_result["avgPrice"])
                    
                    # Pastikan harga eksekusi valid
                    if execution_price <= 0:
                        logger.error(f"Execution price tidak valid: {execution_price}")
                        with self.processing_lock:
                            self.processing_symbols.discard(symbol)
                        continue
                    
                    # 5. Hitung dan log slippage aktual
                    if action == "LONG":
                        slippage = (execution_price - mark_price) / mark_price
                    else:
                        slippage = (mark_price - execution_price) / mark_price
                    
                    slippage_percent = slippage * 100
                    slippage_msg = f"Slippage: {slippage_percent:.2f}%"
                    
                    if abs(slippage) > self.MAX_SLIPPAGE_ALERT:
                        logger.warning(f"SLIPPAGE TINGGI! {slippage_msg} pada {symbol}")
                    else:
                        logger.info(slippage_msg)
                    
                    # 6. Hitung ulang quantity jika perlu (dengan harga real)
                    real_qty = min(qty, (allocated_balance * self.LEVERAGE) / execution_price)
                    
                    # 7. Dapatkan data terbaru dari DB untuk disimpan di open_positions
                    db_info = self.symbol_info_db.get(symbol, {})
                    db_id = db_info.get('id', 0)
                    db_posisi = db_info.get('posisi', '')
                    db_signal_ch = db_info.get('signal_ch', '')
                    
                    # 8. Simpan ke database
                    success_id = self._save_trade_to_db(
                        symbol, execution_price, action, real_qty, self.LEVERAGE, order_id,
                        signal_score=db_info.get('signal_score', 0)
                    )
                    
                    if success_id:
                        with self.position_lock, self.processing_lock:
                            self.open_positions[symbol] = (
                                action, 
                                execution_price, 
                                real_qty, 
                                self.LEVERAGE, 
                                order_id, 
                                0.0,   # unrealized_pnl
                                success_id,   # ID baris di database
                                db_posisi,
                                db_signal_ch
                            )
                            self.processing_symbols.discard(symbol)
                            logger.info(f"Posisi {action} dibuka untuk {symbol} dengan order ID {order_id} dan database ID {success_id}")
                    else:
                        logger.error(f"Gagal menyimpan trade untuk {symbol} ke database")
                else:
                    logger.error(f"Gagal eksekusi order untuk {symbol}")
                    with self.processing_lock:
                        self.processing_symbols.discard(symbol)
            
            except queue.Empty:
                continue
            except Exception as e:
                logger.error(f"Error eksekutor trading: {e}")
                with self.processing_lock:
                    self.processing_symbols.discard(symbol)

    def _position_monitor(self):
        """Thread untuk memantau dan menutup posisi berdasarkan perubahan sinyal"""
        while not self.shutdown_event.is_set():
            time.sleep(5)  # Cek setiap 5 detik
            
            # Buat salinan posisi terbuka untuk menghindari deadlock
            positions_to_check = []
            with self.position_lock:
                positions_to_check = list(self.open_positions.items())
            
            if not positions_to_check:
                continue
                
            for symbol, position_data in positions_to_check:
                try:
                    # Unpack data
                    (position, entry_price, qty, leverage, order_id, unrealized_pnl, 
                     open_db_id, open_db_posisi, open_db_signal_ch) = position_data
                    
                    # Dapatkan data terbaru dari symbol_info_db
                    current_info = self.symbol_info_db.get(symbol, {})
                    if not current_info:
                        continue
                    
                    current_posisi = current_info.get('posisi', '')
                    current_signal_ch = current_info.get('signal_ch', '')
                    current_db_id = current_info.get('id', 0)
                    
                    # Tutup posisi jika terjadi perubahan pada posisi_ch atau signal_ch
                    close_position = False
                    close_reason = ""
                    
                    # Perubahan terjadi jika:
                    # 1. Ada perubahan pada posisi (LONG -> SHORT atau sebaliknya)
                    # 2. Ada perubahan pada signal_ch (misal BUY -> SELL)
                    # 3. ID baris database berubah (artinya ada update baru)
                    if (current_posisi != open_db_posisi or 
                        current_signal_ch != open_db_signal_ch or
                        current_db_id != open_db_id):
                        close_position = True
                        close_reason = (
                            f"Perubahan sinyal: "
                            f"Posisi[{open_db_posisi}->{current_posisi}], "
                            f"Signal[{open_db_signal_ch}->{current_signal_ch}], "
                            f"ID[{open_db_id}->{current_db_id}]"
                        )
                    
                    if close_position:
                        # Tentukan sisi order untuk close (kebalikan dari open)
                        close_side = "SELL" if position == "LONG" else "BUY"
                        
                        # Eksekusi close di Binance
                        close_result = self._execute_trade(symbol, close_side, qty)
                        
                        if close_result and close_result.get("orderId"):
                            close_id = str(close_result["orderId"])
                            close_price = float(close_result["avgPrice"])
                            
                            # Update database menggunakan ID baris
                            success = self._update_trade_in_db(open_db_id, close_price, close_id)
                            if success:
                                with self.position_lock:
                                    if symbol in self.open_positions:
                                        del self.open_positions[symbol]
                                logger.info(f"Closing {symbol} ({close_reason}): close_id={close_id}")
                        else:
                            logger.error(f"Gagal menutup posisi untuk {symbol}")
                except Exception as e:
                    logger.error(f"Error pada monitor posisi {symbol}: {e}")

    def _leverage_retry_manager(self):
        """Thread khusus untuk retry setting leverage"""
        while not self.shutdown_event.is_set():
            try:
                symbol = self.leverage_retry_queue.get(timeout=60)
                logger.info(f"Retrying leverage setup for {symbol}")
                
                if self._set_margin_mode(symbol) and self._set_leverage(symbol):
                    self.leverage_set.add(symbol)
                    logger.info(f"Leverage setup berhasil untuk {symbol} setelah retry")
                else:
                    # Masukkan kembali ke antrian untuk coba lagi nanti
                    self.leverage_retry_queue.put(symbol)
                    logger.info(f"Leverage setup gagal untuk {symbol}, dimasukkan kembali ke antrian")
                    
            except queue.Empty:
                pass

    def _get_pending_orders(self) -> List[Dict]:
        """Ambil semua pending order dari database (status=2)"""
        conn = self._get_db_connection()
        if not conn:
            return []
            
        try:
            cursor = conn.cursor()
            cursor.execute("""
                SELECT id, symbol, price_open, posisi, signal_score 
                FROM tran_TF 
                WHERE status = 2 AND binance_order_id = 'PENDING'
            """)
            columns = [col[0] for col in cursor.description]
            return [dict(zip(columns, row)) for row in cursor.fetchall()]
        except Exception as e:
            logger.error(f"Gagal mengambil pending orders: {e}")
            return []
        finally:
            conn.close()

    def _update_pending_order(self, order_id_db: int, execution_price: float, qty: float, binance_order_id: str) -> bool:
        """Update pending order setelah dieksekusi dengan lengkap"""
        if execution_price <= 0 or qty <= 0:
            logger.error(f"[ABORT] execution_price tidak valid (={execution_price}) atau qty tidak valid (={qty}) saat update pending order ID={order_id_db}")
            return False

        conn = self._get_db_connection()
        if not conn:
            return False
            
        try:
            cursor = conn.cursor()
            # Dapatkan posisi untuk perhitungan SL/TP
            cursor.execute("SELECT posisi FROM tran_TF WHERE id = ?", (order_id_db,))
            row = cursor.fetchone()
            if not row:
                logger.error(f"Pending order dengan ID {order_id_db} tidak ditemukan")
                return False
                
            position = row[0]
            
            # Hitung ulang SL/TP berdasarkan harga eksekusi
            if position == "LONG":
                stop_loss = execution_price * 0.99  # -1%
                take_profit = execution_price * 1.03  # +3%
            else:  # SHORT
                stop_loss = execution_price * 1.01  # +1%
                take_profit = execution_price * 0.97  # -3%
                
            fee = execution_price * qty * 0.0004  # Fee 0.04%

            # Gunakan leverage yang sebenarnya dari class
            leverage = self.LEVERAGE

            logger.info(
                f"[UPDATE] ID={order_id_db} | price_open={execution_price:.5f} | qty={qty:.6f} | "
                f"leverage={leverage} | order_id={binance_order_id} | "
                f"stop_loss={stop_loss:.5f} | take_profit={take_profit:.5f} | fee={fee:.5f}"
            )
            
            query = """
                UPDATE tran_TF 
                SET price_open = ?,
                    qty = ?,
                    leverage = ?,
                    binance_order_id = ?,
                    stop_lose = ?,
                    take_profit = ?,
                    feebinance = ?,
                    status = 1
                WHERE id = ?
            """
            params = (
                execution_price, qty, leverage, binance_order_id,
                stop_loss, take_profit, fee, order_id_db
            )
            cursor.execute(query, params)
            conn.commit()
            logger.info(
                f"Pending order diupdate: id={order_id_db}, price={execution_price:.5f}, qty={qty:.6f}, "
                f"leverage={leverage}, SL={stop_loss:.5f}, TP={take_profit:.5f}, fee={fee:.5f}, "
                f"binance_order_id={binance_order_id}"
            )
            return True
        except Exception as e:
            logger.error(f"Gagal update pending order: {e}", exc_info=True)
            return False
        finally:
            conn.close()

    def _execute_pending_order(self, symbol: str, position: str, target_price: float, order_id_db: int):
        # Dapatkan harga mark saat ini
        with self.data_lock:
            mark_price = self.mark_prices.get(symbol, 0.0)
        
        # Hitung kuantitas berdasarkan harga target
        allocated_balance = self.BALANCE_PER_SYMBOL * self.SAFETY_MARGIN
        qty = (allocated_balance * self.LEVERAGE) / target_price
        
        # Tentukan sisi order
        order_side = "BUY" if position == "LONG" else "SELL"
        
        # Eksekusi order di Binance dengan retry
        max_retries = 3
        for attempt in range(max_retries):
            logger.info(
                f"Eksekusi pending order: {position} {symbol} @ {target_price:.5f} (target), "
                f"qty={qty:.6f}, attempt {attempt+1}/{max_retries}"
            )
            order_result = self._execute_trade(symbol, order_side, qty)
            
            if order_result and order_result.get("orderId"):
                order_id = str(order_result["orderId"])
                execution_price = float(order_result["avgPrice"])
                executed_qty = float(order_result["executedQty"])
                
                # Gunakan executed_qty untuk update database
                success = self._update_pending_order(order_id_db, execution_price, executed_qty, order_id)
                
                if success:
                    # Dapatkan data terbaru untuk disimpan di open_positions
                    db_info = self.symbol_info_db.get(symbol, {})
                    db_id = db_info.get('id', 0)
                    db_posisi = db_info.get('posisi', '')
                    db_signal_ch = db_info.get('signal_ch', '')
                    
                    with self.position_lock:
                        self.open_positions[symbol] = (
                            position, 
                            execution_price, 
                            executed_qty,  # Gunakan qty yang dieksekusi
                            self.LEVERAGE, 
                            order_id, 
                            0.0,   # unrealized_pnl
                            order_id_db,  # Simpan ID baris database
                            db_posisi,
                            db_signal_ch
                        )
                    
                    logger.info(
                        f"Pending order dieksekusi: {symbol} {position} @ {execution_price:.5f} "
                        f"(qty={executed_qty:.6f}, order_id={order_id})"
                    )
                    return
            else:
                logger.error(f"Gagal eksekusi pending order untuk {symbol} pada attempt {attempt+1}")
                time.sleep(self.ORDER_RETRY_DELAY)
        
        # Jika semua percobaan gagal
        logger.error(f"Gagal eksekusi pending order untuk {symbol} setelah {max_retries} percobaan")
        self.pending_orders.discard(order_id_db)

    def _pending_order_executor(self):
        """Thread untuk eksekusi pending order (status=2)"""
        while not self.shutdown_event.is_set():
            try:
                # Ambil semua pending order dari database
                pending_orders = self._get_pending_orders()
                current_time = datetime.utcnow()
                
                for order in pending_orders:
                    order_id_db = order['id']
                    symbol = order['symbol']
                    target_price = float(order['price_open'])
                    position = order['posisi']
                    score = order['signal_score']  # Tidak digunakan di sini, hanya untuk informasi
                    
                    # Hindari memproses order yang sama berulang kali dalam satu iterasi
                    if order_id_db in self.pending_orders:
                        continue
                        
                    self.pending_orders.add(order_id_db)
                    
                    # Dapatkan harga mark saat ini
                    with self.data_lock:
                        current_price = self.mark_prices.get(symbol, 0.0)
                    
                    # Jika harga saat ini nol, lewati
                    if current_price == 0.0:
                        continue
                    
                    # Cek apakah harga saat ini sudah mencapai target (dalam toleransi 0.1%)
                    price_diff = abs(current_price - target_price)
                    tolerance = target_price * 0.001  # 0.1%
                    
                    if price_diff <= tolerance:
                        logger.info(f"Pending order untuk {symbol} mencapai harga target. Target: {target_price}, Current: {current_price}, Diff: {price_diff:.5f}")
                        # Eksekusi order
                        self._execute_pending_order(symbol, position, target_price, order_id_db)
                    else:
                        # Hapus dari set pending_orders agar bisa dicoba lagi di iterasi berikutnya
                        self.pending_orders.discard(order_id_db)
                
                # Tunggu sebentar sebelum cek lagi
                time.sleep(1)
            except Exception as e:
                logger.error(f"Error pada pending executor: {e}")
                time.sleep(5)

    def _has_pending_order(self, symbol: str) -> bool:
        """Cek apakah ada pending order untuk simbol ini (status=2)"""
        conn = self._get_db_connection()
        if not conn:
            return False
            
        try:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM tran_TF WHERE symbol = ? AND status = 2", (symbol,))
            count = cursor.fetchone()[0]
            return count > 0
        except Exception as e:
            logger.error(f"Gagal cek pending order untuk {symbol}: {e}")
            return False
        finally:
            conn.close()

    def _validate_market_conditions(self, symbol: str) -> bool:
        """Validasi kondisi pasar sebelum eksekusi trading"""
        with self.data_lock:
            order_book = self.order_books.get(symbol, {})
            mark_price = self.mark_prices.get(symbol, 0.0)
            
        # Cek ketersediaan data order book
        if not order_book.get('bids') or not order_book.get('asks'):
            logger.info(f"Validasi pasar {symbol} gagal: data order book tidak lengkap")
            return False
            
        # Hitung spread
        bid_price = float(order_book['bids'][0][0])
        ask_price = float(order_book['asks'][0][0])
        spread = ask_price - bid_price
        mid_price = (bid_price + ask_price) / 2
        spread_percent = spread / mid_price
        
        # Dapatkan spread threshold dari cache
        spread_threshold = self.spread_threshold_cache.get(symbol, 0.002)
        
        if spread_percent > spread_threshold:
            logger.info(f"Validasi pasar {symbol} gagal: spread {spread_percent:.4%} > threshold {spread_threshold:.4%}")
            return False
            
        # Validasi depth
        depth_threshold_value = mark_price * 0.001  # 0.1% dari harga
        valid_depth = True
        
        # Cek 5 level teratas di bids
        for level in order_book['bids'][:5]:
            price, qty = float(level[0]), float(level[1])
            if price * qty < depth_threshold_value:
                valid_depth = False
                break
                
        # Cek 5 level teratas di asks
        if valid_depth:
            for level in order_book['asks'][:5]:
                price, qty = float(level[0]), float(level[1])
                if price * qty < depth_threshold_value:
                    valid_depth = False
                    break
                    
        if not valid_depth:
            logger.info(f"Validasi pasar {symbol} gagal: depth tidak memadai")
            return False
            
        return True

    def _trading_signal_monitor(self):
        """Thread untuk memantau sinyal trading dan memasukkan ke antrian trading"""
        while not self.shutdown_event.is_set():
            time.sleep(1)  # Cek lebih sering
            
            # Buat salinan simbol untuk menghindari perubahan selama iterasi
            with self.reload_lock:
                symbols = self.symbols.copy()
                
            for symbol in symbols:
                try:
                    # Dapatkan data terbaru dari database
                    with self.reload_lock:
                        db_info = self.symbol_info_db.get(symbol, {})
                        price_open = db_info.get('price_open', 0.0)
                        posisi = db_info.get('posisi', '')
                        signal_score = db_info.get('signal_score', 0)
                    
                    # Jika tidak ada sinyal atau price_open tidak valid, lewati
                    if signal_score == 0 or price_open <= 0:
                        continue
                        
                    # Dapatkan harga mark terbaru
                    with self.data_lock:
                        mark_price = self.mark_prices.get(symbol, 0.0)
                    
                    # Jika mark_price tidak valid, lewati
                    if mark_price <= 0:
                        continue
                    
                    # Periksa apakah sudah ada posisi terbuka
                    with self.position_lock:
                        if symbol in self.open_positions:
                            continue
                    
                    # Periksa apakah ada pending order
                    if self._has_pending_order(symbol):
                        continue
                    
                    # Tentukan arah trading
                    trigger = False
                    if posisi == "LONG" and mark_price <= price_open:
                        trigger = True
                        action = "LONG"
                    elif posisi == "SHORT" and mark_price >= price_open:
                        trigger = True
                        action = "SHORT"
                    
                    if trigger:
                        logger.info(f"SignalMonitor: Trigger {action} untuk {symbol}: MarkPrice={mark_price:.5f} vs PriceOpen={price_open:.5f}")
                        # Masukkan ke trading queue untuk eksekusi
                        self.trading_queue.put((symbol, action, mark_price))
                        
                except Exception as e:
                    logger.error(f"Error pada trading signal monitor untuk {symbol}: {e}")

    def _display_dashboard(self, stdscr):
        curses.curs_set(0)
        stdscr.nodelay(True)
        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_GREEN, -1)    # Hijau
        curses.init_pair(2, curses.COLOR_YELLOW, -1)   # Kuning
        curses.init_pair(3, curses.COLOR_RED, -1)      # Merah
        curses.init_pair(4, curses.COLOR_CYAN, -1)     # Cyan
        curses.init_pair(5, curses.COLOR_MAGENTA, -1)  # Magenta
        curses.init_pair(6, curses.COLOR_WHITE, -1)    # Putih
        # Header dengan kolom tambahan untuk Entry Price
        headers = ["Symbol", "LastP", "MarkP", "PriceOpen", "REC.SIGN", "Real.SIGN", "EntryP", "Leverage", "UnrealPnL", "RealPnL", "OrderID"]
        min_col_widths = [8, 11, 11, 11, 12, 10, 11, 8, 12, 12, 15]
        col_padding = 1

        last_update_time = time.time()

        while not self.shutdown_event.is_set():
            try:
                # Handle keyboard input
                c = stdscr.getch()
                if c == ord('q'):
                    self.shutdown_event.set()
                    break
                elif c == ord('t'):
                    self.trading_active = not self.trading_active
                    status = "AKTIF" if self.trading_active else "NONAKTIF"
                    logger.info(f"Trading diubah menjadi {status}")

                current_time = time.time()
                if current_time - last_update_time < 0.5:
                    time.sleep(0.01)
                    continue
                last_update_time = current_time

                height, width = stdscr.getmaxyx()
                win = curses.newwin(height, width, 0, 0)
                win.nodelay(True)
                win.erase()
                
                # Hitung lebar kolom dinamis
                total_min_width = sum(min_col_widths) + (len(min_col_widths) - 1) * col_padding
                col_widths = min_col_widths.copy()
                
                if width > total_min_width:
                    extra_width = width - total_min_width
                    extra_per_col = extra_width // len(col_widths)
                    remainder = extra_width % len(col_widths)
                    
                    for i in range(len(col_widths)):
                        col_widths[i] += extra_per_col
                    
                    for i in range(remainder):
                        col_widths[i] += 1

                now = datetime.utcnow()
                title = f"Binance Futures Realtime - {now.strftime('%Y-%m-%d %H:%M:%S')} UTC | Mode: {self.MARGIN_MODE} | Leverage: {self.LEVERAGE}x | Balance: {self.total_balance:.2f} USDT | Used Margin: {self.used_margin:.2f} USDT | Trading: {'AKTIF' if self.trading_active else 'NONAKTIF'}"
                title_x = max(0, (width - len(title)) // 2)
                win.addstr(0, title_x, title, curses.A_BOLD | curses.color_pair(4))
                
                # Tampilkan header
                col_start = 1
                for i, h in enumerate(headers):
                    if col_start >= width - 1:
                        break
                    
                    padded_header = f" {h} ".ljust(col_widths[i] + col_padding)
                    win.addstr(2, col_start, padded_header[:col_widths[i] + col_padding], 
                              curses.A_UNDERLINE | curses.color_pair(4))
                    col_start += col_widths[i] + col_padding

                # Kumpulkan semua simbol dengan signal_score bukan 0
                non_zero_signals = []
                for symbol in self.symbols:
                    signal_score = self.symbol_info_db.get(symbol, {}).get('signal_score', 0)
                    if signal_score != 0:
                        non_zero_signals.append(symbol)
                
                # Kumpulkan simbol dengan posisi terbuka
                open_symbols = []
                with self.position_lock:
                    open_symbols = [s for s in self.symbols if s in self.open_positions]
                
                # Tentukan simbol yang akan ditampilkan
                if non_zero_signals:
                    # Tampilkan simbol dengan signal_score bukan 0 + semua posisi terbuka
                    display_symbols = list(set(non_zero_signals + open_symbols))
                else:
                    # Tampilkan semua simbol
                    display_symbols = self.symbols.copy()
                
                # Urutkan: posisi terbuka di atas, kemudian simbol lainnya
                display_symbols.sort(key=lambda s: (s not in open_symbols, s))
                
                # Tampilkan data untuk setiap simbol
                row = 3
                for symbol in display_symbols:
                    if row >= height - 2:
                        break
                    
                    with self.data_lock:
                        last_price = self.last_prices.get(symbol, 0.0)
                        mark_price = self.mark_prices.get(symbol, 0.0)
                        d = self.display_data.get(symbol, {})
                        current_oi = d.get('open_interest', 0)
                        previous_oi_val = self.previous_oi.get(symbol, 0)
                        funding_rate = d.get('funding_rate', 0)
                        liq = self.liquidation_accumulator.get(symbol, {})
                        vol = self.volume_accumulator.get(symbol, {})
                    
                    # Dapatkan data dari database
                    db_info = self.symbol_info_db.get(symbol, {})
                    price_open = db_info.get('price_open', 0.0)
                    posisi = db_info.get('posisi', '')
                    posisi_ch = db_info.get('posisi_ch', '')
                    signal_score = db_info.get('signal_score', 0)
                    signal_ch = db_info.get('signal_ch', '')
                    signal_realtime = f"{posisi_ch} {signal_ch}"
                    # Format sinyal untuk ditampilkan
                    signal_str = f"{posisi}({signal_score})"
                    
                    # Tentukan warna berdasarkan posisi
                    if posisi == "LONG":
                        signal_color = 1  # Hijau
                    elif posisi == "SHORT":
                        signal_color = 3  # Merah
                    else:
                        signal_color = 6  # Putih
                    
                    # Dapatkan posisi saat ini
                    position_display = ""
                    entry_price_display = ""
                    leverage_display = ""
                    unrealized_pnl_display = ""
                    realized_pnl_display = ""
                    order_id_display = ""
                    unrealized_pnl = 0.0
                    realized_pnl = 0.0
                    
                    with self.position_lock:
                        if symbol in self.open_positions:
                            position, entry_price, qty, leverage, order_id, upnl, trade_id, _, _ = self.open_positions[symbol]
                            position_display = position
                            entry_price_display = f"{entry_price:.5f}"
                            leverage_display = f"{leverage}x"
                            unrealized_pnl = upnl
                            unrealized_pnl_display = f"${upnl:.2f}"
                            order_id_display = order_id[:12]  # Tampilkan 12 karakter pertama
                            
                            # Dapatkan realized PnL dari cache atau database
                            if trade_id in self.pnl_real_cache:
                                realized_pnl = self.pnl_real_cache[trade_id]
                            else:
                                conn = self._get_db_connection()
                                if conn:
                                    try:
                                        cursor = conn.cursor()
                                        cursor.execute("SELECT pnl_real FROM tran_TF WHERE id = ?", (trade_id,))
                                        row = cursor.fetchone()
                                        if row:
                                            realized_pnl = float(row[0] or 0.0)
                                            self.pnl_real_cache[trade_id] = realized_pnl
                                    except Exception as e:
                                        logger.error(f"Gagal mengambil realized PnL untuk {symbol}: {e}")
                                    finally:
                                        conn.close()
                            
                            realized_pnl_display = f"${realized_pnl:.2f}"

                    # Format data untuk ditampilkan
                    data_to_display = [
                        symbol,
                        f"{last_price:.5f}",
                        f"{mark_price:.5f}",
                        f"{price_open:.5f}",
                        signal_str,
                        signal_realtime,  # Gunakan data dari database
                        entry_price_display,
                        leverage_display,
                        unrealized_pnl_display,
                        realized_pnl_display,
                        order_id_display
                    ]
                    
                    # Tampilkan baris data
                    col_start = 1
                    for i, val in enumerate(data_to_display):
                        if col_start >= width - 1:
                            break
                        
                        padded_val = f" {val} "
                        display_val = padded_val[:col_widths[i] + col_padding].ljust(col_widths[i] + col_padding)
                        
                        # Warna khusus untuk kolom tertentu
                        if i == 4:  # Kolom REC.SIGN
                            win.addstr(row, col_start, display_val, curses.color_pair(signal_color))
                        elif i == 8:  # Kolom UnrealPnL
                            if unrealized_pnl >= self.PROFIT_TARGET:
                                win.addstr(row, col_start, display_val, curses.color_pair(1))
                            elif unrealized_pnl > 0:
                                win.addstr(row, col_start, display_val, curses.color_pair(2))
                            elif unrealized_pnl < 0:
                                win.addstr(row, col_start, display_val, curses.color_pair(3))
                            else:
                                win.addstr(row, col_start, display_val, curses.color_pair(6))
                        elif i == 9:  # Kolom RealPnL
                            if realized_pnl > 0:
                                win.addstr(row, col_start, display_val, curses.color_pair(1))
                            elif realized_pnl < 0:
                                win.addstr(row, col_start, display_val, curses.color_pair(3))
                            else:
                                win.addstr(row, col_start, display_val, curses.color_pair(6))
                        else:
                            win.addstr(row, col_start, display_val, curses.color_pair(6))
                            
                        col_start += col_widths[i] + col_padding
                    row += 1

                # Tampilkan footer sederhana
                footer = f"Menampilkan {min(len(display_symbols), row-3)} dari {len(display_symbols)} simbol | Open: {len(open_symbols)} | Tekan 'q' untuk keluar | 't' untuk toggle trading"
                footer_x = max(0, (width - len(footer)) // 2)
                if height > 1:
                    win.addstr(height - 1, footer_x, footer, curses.A_DIM)
                
                win.noutrefresh()
                curses.doupdate()

            except curses.error: 
                pass
            except Exception as e: 
                logger.error(f"Error pada loop display: {e}")


    def run(self):
        os.system('cls' if os.name == 'nt' else 'clear')
        print("Memuat daftar simbol...")
        self.session = self._create_session()
        self._load_symbol_list()
        self._initialize_data_structures()
        self._initialize_order_books()
        self._get_account_balance()  # Dapatkan saldo akun
        self._get_position_risk()    # Dapatkan margin yang digunakan
        self._load_open_positions()  # Muat posisi terbuka dari database

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
            threading.Thread(target=self._trading_executor, name="TradingExecutor", daemon=True),
            threading.Thread(target=self._position_monitor, name="PositionMonitor", daemon=True),
            threading.Thread(target=self._leverage_retry_manager, name="LeverageRetry", daemon=True),
            threading.Thread(target=self._pending_order_executor, name="PendingOrderExecutor", daemon=True),
            threading.Thread(target=self._periodic_symbol_reloader, name="SymbolReloader", daemon=True),
            threading.Thread(target=self._periodic_db_reloader, name="DBReloader", daemon=True),
            threading.Thread(target=self._trading_signal_monitor, name="TradingSignalMonitor", daemon=True),
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

        print("Memulai tampilan realtime...")
        curses.wrapper(self._display_dashboard)
        print("\nMenunggu thread untuk berhenti... Selesai.")

if __name__ == "__main__":
    try:
        app = FuturesTracker()
        app.run()
    except (KeyboardInterrupt, SystemExit) as e:
        print(f"\nProgram dihentikan: {e}")
    except Exception as e:
        logger.critical(f"Terjadi error fatal: {e}", exc_info=True)
        print(f"\nTerjadi error fatal. Periksa file 'futures_live.log' untuk detail.")
