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
import signal
import zlib
import decimal
import uuid
import math
from enum import Enum
from collections import deque
from datetime import datetime, timedelta
from websocket import create_connection, WebSocketConnectionClosedException
from typing import List, Dict, Any, Set, Optional, Deque, Tuple
from flask import Flask, render_template, redirect, jsonify, request, session, url_for
from functools import wraps
from dotenv import load_dotenv

# Load environment variable
load_dotenv()
# Setup logging - HANYA KE FILE
root_logger = logging.getLogger()
root_logger.setLevel(logging.INFO)
# Hapus semua handler yang ada
for handler in root_logger.handlers[:]:
    root_logger.removeHandler(handler)

# Handler untuk menulis log ke file
file_handler = logging.FileHandler("futures_signal_detector.log", mode='w')
formatter = logging.Formatter("%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s")
file_handler.setFormatter(formatter)
root_logger.addHandler(file_handler)

logger = logging.getLogger(__name__)

# Import Flask dan SocketIO tanpa monkey patching
from flask import Flask, render_template, redirect, jsonify, request
from flask_socketio import SocketIO, emit
import traceback

class OrderType(Enum):
    LIMIT = "LIMIT"
    MARKET = "MARKET"

class OrderSide(Enum):
    BUY = "BUY"
    SELL = "SELL"

class DecimalEncoder(json.JSONEncoder):
    """Custom JSON encoder untuk menangani objek Decimal"""
    def default(self, o):
        if isinstance(o, decimal.Decimal):
            return float(o)
        return super(DecimalEncoder, self).default(o)

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'logged_in' not in session:
            return redirect(url_for('login_page'))
        return f(*args, **kwargs)
    return decorated_function


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
    ACCOUNT_BALANCE_URL = "https://fapi.binance.com/fapi/v2/balance"
    SYMBOL_INFO_URL = "https://fapi.binance.com/fapi/v1/exchangeInfo"

    # Konfigurasi Database
    SQL_SERVER = os.getenv("SQL_SERVER")
    SQL_DATABASE = os.getenv("SQL_DATABASE")
    SQL_USERNAME = os.getenv("SQL_USERNAME")
    SQL_PASSWORD = os.getenv("SQL_PASSWORD")
    SQL_DRIVER = os.getenv("SQL_DRIVER", "{ODBC Driver 17 for SQL Server}")

    # Binance API Configuration
    BINANCE_API_KEY = os.getenv("BINANCE_API_KEY")
    BINANCE_API_SECRET = os.getenv("BINANCE_API_SECRET")

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

        # Inisialisasi Flask dan Socket.IO dengan buffer yang lebih besar
        self.flask_app = Flask(__name__)
        self.flask_app.config['CORS_HEADERS'] = 'Content-Type'
        self.socketio = SocketIO(
            self.flask_app,
            async_mode='threading',  # PERBAIKAN: Ganti ke threading
            cors_allowed_origins="*",
            logger=False,  # Nonaktifkan logger Socket.IO
            engineio_logger=False,  # Nonaktifkan engineio logger
            max_http_buffer_size=50 * 1024 * 1024,  # 50MB (ditingkatkan)
            ping_interval=60,  # Ditingkatkan
            ping_timeout=120,   # Ditingkatkan
            compression_threshold=1024,  # Kompresi untuk payload besar
            json=json  # Gunakan JSON encoder kustom
        )

        # Setup route
        self.flask_app.add_url_rule('/', 'dashboard', self.dashboard)
        self.flask_app.add_url_rule('/index.html', 'index_redirect', self.index_redirect)
        self.flask_app.add_url_rule('/reload', 'manual_reload', self.manual_reload, methods=['POST'])
        self.flask_app.add_url_rule('/health', 'health_check', self.health_check)
        self.flask_app.add_url_rule('/symbol_info', 'symbol_info', self.symbol_info)
        self.flask_app.add_url_rule('/account_balance', 'account_balance', self.account_balance)
        self.flask_app.add_url_rule('/api/submit_order', 'submit_order', self.submit_order, methods=['POST'])
        # Tambahkan route untuk halaman open orders
        self.flask_app.add_url_rule('/open_orders.html', 'open_orders', self.open_orders_page)
        self.flask_app.add_url_rule('/api/open_orders', 'api_open_orders', self.get_open_orders)

        # Setup Socket.IO event
        self.socketio.on_event('connect', self.handle_connect, namespace='/')
        self.socketio.on_event('request_data', self.handle_request_data, namespace='/')
        self.socketio.on_event('disconnect', self.handle_disconnect, namespace='/')
        self.socketio.on_event('error', self.handle_error, namespace='/')

        # Data untuk dikirim ke klien
        self.client_data = {}
        self.last_update_time = datetime.utcnow()
        self.last_db_reload = time.time()
        self.last_emit_time = time.time()
        self.pending_price_updates = {}
        self.cached_formatted_data = None  # Cache untuk data yang diformat

        # Cache untuk data sinyal dari database
        self.signal_data_cache: Dict[str, Dict] = {}
        self.signal_cache_lock = threading.Lock()

        # Error counter
        self.error_counter = 0
        self.last_error_time = 0

        # Database connection semaphore and retry settings
        self.db_semaphore = threading.Semaphore(5)  # Batasi koneksi database simultan
        self.db_retry_attempts = 3
        self.db_retry_delay = 1  # detik

        # Cache untuk burst thresholds
        self.burst_threshold_cache: Dict[str, Tuple[Dict, float]] = {}
        self.burst_cache_lock = threading.Lock()

        # Cache untuk ATR values
        self.atr_cache: Dict[str, Tuple[float, float]] = {}
        self.atr_cache_lock = threading.Lock()
        self.atr_cache_timeout = 300  # 5 menit

        # Cache untuk informasi simbol (minQty, minNotional)
        self.symbol_info_map: Dict[str, Dict] = {}
        self.symbol_info_cache_time = 0
        self.symbol_info_refresh_interval = 3600  # 1 jam

        # Cache untuk saldo akun
        self.account_balance_cache: Dict[str, float] = {}
        self.balance_cache_time = 0
        self.balance_refresh_interval = 60  # 1 menit

        self.open_orders_cache = None  # Cache untuk data open orders
        self.open_orders_last_updated = 0  # Timestamp terakhir update
        self.open_orders_lock = threading.Lock()  # Lock untuk akses cache
        self.flask_app.add_url_rule('/api/close_order', 'close_order', self.close_order, methods=['POST'])
        # Konfigurasi Auto Close berdasarkan PnL
        self.flask_app.add_url_rule('/api/cancel_order', 'cancel_order', self.cancel_order, methods=['POST'])
        self.AUTO_CLOSE_THRESHOLD_LOSS = -0.8  # USD
        self.AUTO_CLOSE_THRESHOLD_PROFIT = 0.6  # USD
        self.auto_close_lock = threading.Lock()
        self.orders_in_process = set()  # Untuk melacak order yang sedang diproses

        self.flask_app.add_url_rule('/login', 'login_page', self.login_page, methods=['GET'])
        self.flask_app.add_url_rule('/login', 'login', self.login, methods=['POST'])
        self.flask_app.add_url_rule('/logout', 'logout', self.logout)
        self.flask_app.secret_key = os.getenv("FLASK_SECRET_KEY", "default_secret_key")
        self.flask_app.add_url_rule('/check_auth', 'check_auth', self.check_auth)

        #autobot
        self.autobot_enabled = False
        self.flask_app.add_url_rule('/api/autobot_status', 'autobot_status', self.get_autobot_status)
        self.flask_app.add_url_rule('/api/toggle_autobot', 'toggle_autobot', self.toggle_autobot, methods=['POST'])
        
        # Cache untuk melacak candle terakhir di mana autobot telah membuka posisi
        self.autobot_last_open: Dict[str, datetime] = {}

    @login_required
    def get_autobot_status(self):
        return jsonify({
            'status': 'success',
            'autobot_enabled': self.autobot_enabled
        })

    @login_required
    def toggle_autobot(self):
        try:
            self.autobot_enabled = not self.autobot_enabled
            # Broadcast new status to all clients
            self.socketio.emit('autobot_status', 
                              {'enabled': self.autobot_enabled}, 
                              namespace='/')
            return jsonify({
                'success': True,
                'enabled': self.autobot_enabled
            })
        except Exception as e:
            logger.error(f"Error toggling autobot: {e}")
            return jsonify({'success': False, 'error': str(e)}), 500

    def _autobot_open_position(self, symbol: str, position: str, mark_price: float, current_candle: datetime):
        if not self.autobot_enabled:
            return False
            
        # Cek apakah sudah ada posisi di candle ini
        if self.autobot_last_open.get(symbol) == current_candle:
            logger.info(f"Autobot: Already opened position for {symbol} in current candle. Skipping.")
            return False
            
        # Cek volume total
        with self.data_lock:
            vol = self.volume_accumulator.get(symbol, {})
            buy_vol_candle = vol.get('market_buy', 0) * mark_price
            sell_vol_candle = vol.get('market_sell', 0) * mark_price
            total_vol_candle = buy_vol_candle + sell_vol_candle
            
        if total_vol_candle < 1000000:  # 1 juta USD
            logger.info(f"Autobot: Volume too low for {symbol} ({total_vol_candle:.2f} USD). Skipping.")
            return False
            
        # Tentukan side
        if position == 'LONG':
            side = OrderSide.BUY
            posisi_db = 'LONG'
        elif position == 'SHORT':
            side = OrderSide.SELL
            posisi_db = 'SHORT'
        else:
            return False
            
        # Hitung quantity
        notional = 100.0   # 100 USDT
        quantity = notional / mark_price
        
        # Dapatkan info simbol
        symbol_info = self.symbol_info_map.get(symbol)
        if not symbol_info:
            logger.error(f"Autobot: Symbol info not found for {symbol}")
            return False
            
        min_qty = symbol_info.get('minQty', 0)
        step_size = symbol_info.get('stepSize', 0.001)
        min_notional = symbol_info.get('minNotional', 0)
        
        # PERBAIKAN 1: Validasi min notional
        if notional < min_notional:
            # Hitung ulang quantity berdasarkan minNotional
            required_qty = min_notional / mark_price
            if step_size > 0:
                precision = self._get_step_precision(step_size)
                required_qty = round(required_qty, precision)
            if required_qty < min_qty:
                required_qty = min_qty
            quantity = required_qty
            notional = quantity * mark_price
            logger.info(f"Autobot: Adjusted quantity to {quantity} to meet minNotional")
        
        # PERBAIKAN UTAMA: Penanganan step size yang lebih akurat
        if step_size > 0:
            # Hitung jumlah step yang valid dengan floor division
            steps = quantity / step_size
            # Gunakan floor untuk memastikan tidak melebihi saldo
            steps = math.floor(steps)
            quantity = steps * step_size
            
            # Perbaiki presisi floating point
            precision = self._get_step_precision(step_size)
            quantity = round(quantity, precision)
        else:
            quantity = round(quantity, 8)
                
        # PERBAIKAN 3: Pastikan quantity tidak kurang dari min_qty
        if quantity < min_qty:
            logger.warning(f"Autobot: Quantity {quantity} < minQty {min_qty} for {symbol}. Using minQty.")
            quantity = min_qty
        
        # PERBAIKAN: Validasi akhir notional
        final_notional = quantity * mark_price
        if final_notional < min_notional:
            logger.warning(f"Autobot: Final notional {final_notional:.4f} < min notional {min_notional} for {symbol}. Skipping.")
            return False
            
        # Set leverage to 50x
        leverage = 50
        set_leverage_url = "https://fapi.binance.com/fapi/v1/leverage"
        leverage_params = {
            'symbol': symbol,
            'leverage': leverage,
            'timestamp': int(time.time() * 1000)
        }
        leverage_params['signature'] = self._generate_signature(leverage_params)
        
        try:
            leverage_response = requests.post(
                set_leverage_url,
                params=leverage_params,
                headers={"X-MBX-APIKEY": self.BINANCE_API_KEY},
                timeout=5
            )
            leverage_response.raise_for_status()
        except Exception as e:
            logger.error(f"Autobot: Failed to set leverage: {e}")
            return False
            
        # Place the order
        logger.info(f"Autobot: Placing {position} order for {symbol}, qty: {quantity}, at mark price: {mark_price}")
        order_result = self._place_binance_order(
            symbol=symbol,
            side=side,
            order_type=OrderType.MARKET,
            quantity=quantity
        )
        
        if not order_result['success']:
            # PERBAIKAN 5: Log error lebih detail
            error_msg = order_result.get('msg', 'Unknown error')
            logger.error(f"Autobot: Order failed for {symbol}: {error_msg}")
            return False
            
        binance_order_id = order_result['data'].get('orderId')
        if not binance_order_id:
            logger.error("Autobot: No order ID in response")
            return False
            
        # PERBAIKAN UTAMA: Simpan ke database menggunakan fungsi yang benar
        db_success = self._submit_order_to_database(
            symbol=symbol,
            side=posisi_db,  # Gunakan 'LONG' atau 'SHORT'
            order_type=OrderType.MARKET.value,
            quantity=quantity,
            price=mark_price,  # Gunakan mark_price sebagai perkiraan
            leverage=leverage,
            stop_loss=None,
            take_profit=None,
            binance_order_id=str(binance_order_id),
            initial=True
        )
        
        if db_success:
            logger.info(f"Autobot: Order for {symbol} saved to database. Order ID: {binance_order_id}")
            # Tandai candle ini sudah dibuka
            self.autobot_last_open[symbol] = current_candle
            
            # PERBAIKAN: Panggil sinkronisasi harga untuk update lebih akurat
            threading.Thread(
                target=self._sync_order_price,
                args=(str(binance_order_id), symbol),
                daemon=True
            ).start()
            
            return True
        else:
            logger.error(f"Autobot: Failed to save order for {symbol} to database")
            return False

    def _sync_order_price(self, binance_order_id: str, symbol: str):
        """Sinkronisasi harga order dengan Binance"""
        attempts = 0
        max_attempts = 10
        order_filled = False
        
        while attempts < max_attempts and not self.shutdown_event.is_set():
            attempts += 1
            time.sleep(3)  # Tunggu 3 detik antar percobaan
            
            try:
                order_detail = self._fetch_binance_order_detail(
                    int(binance_order_id),
                    symbol
                )
                
                if not order_detail:
                    continue
                    
                status = order_detail.get('status')
                
                # Handle filled orders
                if status in ['PARTIALLY_FILLED', 'FILLED']:
                    executed_qty = float(order_detail.get('executedQty', 0))
                    if executed_qty > 0:
                        executed_price = float(order_detail.get('avgPrice', 0))
                        
                        # Update database dengan harga sebenarnya
                        update_success = self._submit_order_to_database(
                            symbol=symbol,
                            side=None,  # Tidak perlu update side
                            order_type=None,  # Tidak perlu update order type
                            quantity=None,  # Tidak perlu update quantity
                            price=executed_price,
                            leverage=None,  # Tidak perlu update leverage
                            stop_loss=None,
                            take_profit=None,
                            binance_order_id=binance_order_id,
                            initial=False  # Update existing order
                        )
                        
                        if update_success:
                            logger.info(f"Autobot: Successfully synced price for order {binance_order_id} @ {executed_price}")
                        else:
                            logger.warning(f"Autobot: Failed to update price for order {binance_order_id}")
                        
                        order_filled = True
                        break
                elif status in ['CANCELED', 'EXPIRED']:
                    logger.warning(f"Autobot: Order {binance_order_id} canceled/expired")
                    break
                    
            except Exception as e:
                logger.error(f"Autobot: Error syncing order price: {e}")
        
        if not order_filled:
            logger.warning(f"Autobot: Order {binance_order_id} not filled after {max_attempts} attempts")

    def _get_step_precision(self, step_size: float) -> int:
        """Hitung jumlah digit desimal yang dibutuhkan untuk step size"""
        if step_size <= 0:
            return 8
            
        # Handle integer step sizes (e.g., 1.0)
        if step_size.is_integer():
            return 0  # No decimal places needed
            
        # Hitung jumlah digit desimal
        decimal_str = str(step_size).rstrip('0').rstrip('.')
        if '.' in decimal_str:
            return len(decimal_str.split('.')[1])
        return 0

    @login_required
    def open_orders_page(self):
        """Render halaman open_orders.html"""
        return render_template('open_orders.html')

    def login(self):
        """Proses login"""
        username = request.form.get('username')
        password = request.form.get('password')

        # Validasi sederhana
        if username == "UBayeboy" and password == "MEmek_89*":
            session['logged_in'] = True
            return redirect(url_for('dashboard'))
        return self.login_page(error="Invalid credentials")  # Diperbaiki

    def login_page(self, error=None):
        """Render halaman login"""
        return render_template('login.html', error=error)

    def logout(self):
        """Logout user"""
        session.pop('logged_in', None)
        return redirect(url_for('login_page'))

    def check_auth(self):
        return jsonify({
            'authenticated': 'logged_in' in session
        })


    def _fetch_open_orders_data(self):
        """Mengambil data open orders dan format untuk response"""
        try:
            with self.db_semaphore:
                conn = self._get_db_connection()
                if not conn:
                    return {"status": "error", "message": "Database connection failed"}

                cursor = conn.cursor()
                cursor.execute("EXEC sp_openorder")
                columns = [column[0] for column in cursor.description]
                rows = cursor.fetchall()

                # Ambil snapshot mark_prices
                with self.data_lock:
                    mark_prices_snapshot = self.mark_prices.copy()

                orders = []
                for row in rows:
                    order_data = {}
                    for idx, col_name in enumerate(columns):
                        value = row[idx]

                        # Konversi Decimal ke float
                        if isinstance(value, decimal.Decimal):
                            order_data[col_name] = float(value)
                        # Konversi datetime ke string
                        elif isinstance(value, datetime):
                            order_data[col_name] = value.isoformat()
                        else:
                            order_data[col_name] = value

                    symbol = order_data.get('symbol')
                    order_data['mark_price'] = float(mark_prices_snapshot.get(symbol, 0.0))

                    # Dapatkan status order dari Binance jika ada order_id
                    binance_order_id = order_data.get('binance_order_id')
                    if binance_order_id and binance_order_id != 'PENDING':
                        order_detail = self._fetch_binance_order_detail(binance_order_id, symbol)
                        if order_detail:
                            order_data['binance_status'] = order_detail.get('status', 'UNKNOWN')
                        else:
                            order_data['binance_status'] = 'UNKNOWN'
                    else:
                        order_data['binance_status'] = 'PENDING'

                    orders.append(order_data)

                return {
                    "status": "success",
                    "data": orders,
                    "timestamp": datetime.utcnow().isoformat(),
                    "last_update": datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S')
                }

        except Exception as e:
            logger.error(f"Error _fetch_open_orders_data: {str(e)}")
            return {"status": "error", "message": str(e)}
        finally:
            try:
                conn.close()
            except:
                pass

    def get_open_orders(self):
        """Endpoint untuk mendapatkan data open positions dari cache"""
        try:
            with self.open_orders_lock:
                if self.open_orders_cache:
                    # Gunakan custom encoder untuk memastikan serialisasi
                    return jsonify(self.open_orders_cache), 200, {'Content-Type': 'application/json'}

            # Jika cache kosong, ambil data langsung
            orders_data = self._fetch_open_orders_data()
            return jsonify(orders_data), 200, {'Content-Type': 'application/json'}

        except Exception as e:
            logger.error(f"Error get_open_orders: {str(e)}")
            return jsonify({"status": "error", "message": "Internal server error"}), 500

    def _generate_signature(self, params: Dict) -> str:
        """Generate signature HMAC SHA256 untuk Binance API"""
        query_string = urllib.parse.urlencode(params)
        return hmac.new(
            self.BINANCE_API_SECRET.encode('utf-8'),
            query_string.encode('utf-8'),
            hashlib.sha256
        ).hexdigest()

    def _fetch_binance_api(self, url: str, params: Optional[Dict] = None, signed: bool = False) -> Optional[Dict]:
        """Mengambil data dari API Binance dengan penanganan error"""
        try:
            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY} if signed else {}
            if signed:
                if params is None:
                    params = {}
                params['timestamp'] = int(time.time() * 1000)
                params['signature'] = self._generate_signature(params)

            response = self.session.get(url, params=params, headers=headers, timeout=10)
            response.raise_for_status()
            return response.json()
        except Exception as e:
            logger.error(f"Binance API error: {e}")
            return None

    def _fetch_binance_order_detail(self, order_id: int, symbol: str) -> Optional[Dict]:
        """Mengambil detail order dari Binance berdasarkan order ID"""
        for attempt in range(3):
            try:
                params = {
                    'symbol': symbol,
                    'orderId': order_id,
                    'timestamp': int(time.time() * 1000)
                }
                params['signature'] = self._generate_signature(params)

                headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
                response = requests.get(
                    "https://fapi.binance.com/fapi/v1/order",
                    params=params,
                    headers=headers,
                    timeout=10
                )
                response.raise_for_status()
                return response.json()
            except requests.exceptions.HTTPError as e:
                if e.response.status_code == 404:
                    logger.warning(f"Order {order_id} not found, attempt {attempt+1}")
                    time.sleep(0.5 * (attempt + 1))
                else:
                    raise
        return None

    def _fetch_symbol_info_map(self):
        """Mengambil dan meng-cache informasi simbol futures"""
        current_time = time.time()
        if current_time - self.symbol_info_cache_time < self.symbol_info_refresh_interval:
            return  # Gunakan cache yang ada

        try:
            logger.info("Memperbarui informasi simbol futures...")
            data = self._fetch_api_data(self.SYMBOL_INFO_URL, {})
            if not data or 'symbols' not in data:
                logger.error("Gagal mendapatkan informasi simbol")
                return

            new_map = {}
            for symbol_info in data['symbols']:
                symbol = symbol_info['symbol']
                filters = {f['filterType']: f for f in symbol_info['filters']}

                min_qty = None
                min_notional = None

                # Cari filter LOT_SIZE untuk minQty
                if 'LOT_SIZE' in filters:
                    min_qty = float(filters['LOT_SIZE']['minQty'])

                # Cari filter MIN_NOTIONAL untuk minNotional
                if 'MIN_NOTIONAL' in filters:
                    min_notional = float(filters['MIN_NOTIONAL']['notional'])

                new_map[symbol] = {
                    'minQty': min_qty,
                    'minNotional': min_notional
                }

            with self.data_lock:
                self.symbol_info_map = new_map
                self.symbol_info_cache_time = current_time

            logger.info(f"Informasi simbol diperbarui untuk {len(new_map)} simbol")
        except Exception as e:
            logger.error(f"Error mengambil informasi simbol: {e}")

    def _fetch_account_balance(self):
        """Mengambil dan meng-cache saldo akun Binance Futures"""
        if not self.BINANCE_API_KEY or not self.BINANCE_API_SECRET:
            logger.warning("Binance API key/secret tidak tersedia untuk saldo akun")
            return

        current_time = time.time()
        if current_time - self.balance_cache_time < self.balance_refresh_interval:
            return  # Gunakan cache yang ada

        try:
            logger.info("Memperbarui saldo akun Binance...")
            data = self._fetch_binance_api(self.ACCOUNT_BALANCE_URL, signed=True)
            if not data:
                logger.error("Gagal mendapatkan saldo akun")
                return

            new_balance = {}
            for asset in data:
                if float(asset['balance']) > 0:
                    new_balance[asset['asset']] = float(asset['balance'])

            with self.data_lock:
                self.account_balance_cache = new_balance
                self.balance_cache_time = current_time

            logger.info(f"Saldo akun diperbarui: {new_balance}")
        except Exception as e:
            logger.error(f"Error mengambil saldo akun: {e}")

    def _get_db_connection(self) -> Optional[pyodbc.Connection]:
        """Membuat koneksi baru ke database SQL Server dengan retry"""
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

        for attempt in range(self.db_retry_attempts):
            try:
                conn = pyodbc.connect(connection_string)
                return conn
            except Exception as e:
                logger.warning(f"Attempt {attempt+1}/{self.db_retry_attempts} gagal konek ke database: {e}")
                if attempt < self.db_retry_attempts - 1:
                    time.sleep(self.db_retry_delay)
                    self.db_retry_delay *= 2  # Exponential backoff
                else:
                    logger.error(f"Gagal konek ke database setelah {self.db_retry_attempts} percobaan")
        return None

    def _get_burst_thresholds(self, symbol: str) -> Dict[str, float]:
        """Mengambil burst threshold dari database menggunakan stored procedure"""
        current_time = time.time()

        # Cek cache terlebih dahulu
        with self.burst_cache_lock:
            cached = self.burst_threshold_cache.get(symbol)
            if cached:
                thresholds, timestamp = cached
                if current_time - timestamp < 3600:  # Cache 1 jam
                    return thresholds

        # Jika tidak ada cache atau kadaluarsa, ambil dari database
        thresholds = {'burst_buy_threshold': 50000, 'burst_sell_threshold': 50000}  # Default values

        with self.db_semaphore:
            conn = self._get_db_connection()
            if not conn:
                return thresholds

            try:
                cursor = conn.cursor()
                cursor.execute("EXEC sp_burst_liquidation_threshold @symbol=?, @days_back=3, @sensitivity=2.5", symbol)
                row = cursor.fetchone()

                if row:
                    thresholds = {
                        'burst_buy_threshold': float(row.burst_buy_threshold) if hasattr(row, 'burst_buy_threshold') else 50000,
                        'burst_sell_threshold': float(row.burst_sell_threshold) if hasattr(row, 'burst_sell_threshold') else 50000
                    }
            except Exception as e:
                logger.error(f"Gagal mengambil burst threshold untuk {symbol}: {e}")
            finally:
                conn.close()

        # Update cache
        with self.burst_cache_lock:
            self.burst_threshold_cache[symbol] = (thresholds, current_time)

        return thresholds

    def _get_atr14(self, symbol: str) -> float:
        """Mengambil nilai ATR14 dari database menggunakan stored procedure"""
        current_time = time.time()

        # Cek cache terlebih dahulu
        with self.atr_cache_lock:
            cached = self.atr_cache.get(symbol)
            if cached:
                atr_value, timestamp = cached
                if current_time - timestamp < self.atr_cache_timeout:
                    return atr_value

        atr_value = 0.0

        with self.db_semaphore:
            conn = self._get_db_connection()
            if not conn:
                return atr_value

            try:
                cursor = conn.cursor()
                cursor.execute("EXEC sp_calculate_atr14 @symbol=?, @interval=?, @limit=14",
                            (symbol, self.INTERVAL))
                row = cursor.fetchone()

                if row and hasattr(row, 'atr_14'):
                    atr_value = float(row.atr_14)
            except Exception as e:
                logger.error(f"Gagal mengambil ATR14 untuk {symbol}: {e}")
            finally:
                conn.close()

        # Update cache
        with self.atr_cache_lock:
            self.atr_cache[symbol] = (atr_value, current_time)

        return atr_value

    def _save_signal(self, symbol: str, mark_price: float, position: str, score: int, candle_timestamp: datetime) -> bool:
        """
        Simpan sinyal ke database dengan status=2 (pending) jika:
        1. Tidak ada posisi aktif (status=1) untuk simbol tersebut
        2. Tidak ada sinyal pending (status=2) di candle yang sama
        3. Periode candle berbeda dengan sinyal sebelumnya
        """
        with self.db_semaphore:
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

                # Refresh data sinyal setelah penyimpanan berhasil
                self._refresh_signal_data()

                return True
            except Exception as e:
                logger.error(f"Gagal menyimpan sinyal: {e}")
                return False
            finally:
                conn.close()

    def _refresh_signal_data(self):
        """Mengambil data sinyal terbaru dari database menggunakan stored procedure"""
        with self.db_semaphore:
            conn = self._get_db_connection()
            if not conn:
                return

            try:
                cursor = conn.cursor()
                cursor.execute("EXEC sp_tranTF_last")
                rows = cursor.fetchall()

                # Buat struktur data baru
                new_cache = {}
                for row in rows:
                    symbol = row.symbol
                    new_cache[symbol] = {
                        'id': row.id,
                        'price_open': float(row.price_open) if row.price_open is not None else 0.0,
                        'posisi': row.posisi,
                        'signal_score': float(row.signal_score) if row.signal_score is not None else 0
                    }

                # Update cache dengan lock
                with self.signal_cache_lock:
                    self.signal_data_cache = new_cache

                logger.info("Data sinyal berhasil diperbarui dari database")
            except Exception as e:
                logger.error(f"Gagal memperbarui data sinyal: {e}")
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

                # Inisialisasi data sinyal
                self.last_signals[symbol] = 'HOLD'
                self.current_scores[symbol] = 0
        logger.info("Inisialisasi struktur data selesai.")
        self._refresh_signal_data()  # Muat data sinyal awal

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
            # LOG VOLUME SEBELUM RESET
            vol_before = self.volume_accumulator.get(symbol, {'market_buy':0, 'market_sell':0})
            logger.info(f"Closing bar for {symbol}. Volume: Buy={vol_before['market_buy']:.2f}, Sell={vol_before['market_sell']:.2f}")

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
                    'low': float('inf'),  # PERBAIKAN: Reset low ke nilai tinggi
                    'volume': 0.0
                }

            # Simpan OI USD saat ini sebagai OI periode berikutnya
            current_oi_usd = self.display_data[symbol].get('oi_usd', 0)
            self.display_data[symbol]['prev_oi_usd'] = current_oi_usd

            if funding_data:
                rate = float(funding_data.get("lastFundingRate", 0))
                self.display_data[symbol]['funding_rate'] = rate
                self.funding_history[symbol].append(rate)  # PERBAIKAN: Append ke funding history

            if oi_data:
                oi_value = float(oi_data.get("openInterest", 0))
                self.display_data[symbol]['open_interest'] = oi_value
                self.display_data[symbol]['oi_usd'] = oi_value * self.mark_prices.get(symbol, 0)
                # PERBAIKAN: Simpan OI saat ini untuk perhitungan berikutnya
                self.previous_oi[symbol] = oi_value

            # PERBAIKAN: Reset akumulator likuidasi dan volume
            self.liquidation_accumulator[symbol] = {'buy': 0.0, 'sell': 0.0}
            self.volume_accumulator[symbol] = {'market_buy': 0.0, 'market_sell': 0.0}
            self.display_data[symbol]['last_update'] = datetime.utcnow()

            # Update burst thresholds setiap kali candle ditutup
            self.burst_thresholds[symbol] = self._get_burst_thresholds(symbol)

        # PERBAIKAN: Refresh data sinyal setelah menutup candle
        self._refresh_signal_data()
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
                        # PERBAIKAN: Append ke funding history
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
            trade_data = data.get('data', {})
            self.trade_queue.put(trade_data)
            # Proses update harga terakhir
            symbol = trade_data.get('s', '').upper()
            if symbol and symbol in self.symbols:
                price = float(trade_data.get('p', 0))
                self._process_trade_data(symbol, price)

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
                    self._process_mark_price(symbol, mark_price)

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
        """Proses data trade dengan lock yang lebih ketat untuk akurasi volume"""
        last_log_time = time.time()
        trade_count = 0
        volume_by_symbol = {}  # Dictionary untuk menghitung volume per simbol dalam 10 detik

        while not self.shutdown_event.is_set():
            try:
                event = self.trade_queue.get(timeout=1)
                trade_count += 1
                symbol = event.get('s', '').upper()
                if symbol not in self.symbols:
                    continue

                price = float(event.get('p', 0))
                quantity = float(event.get('q', 0))
                is_buyer_maker = event.get('m', False)
                current_time_dt = datetime.utcnow()

                # Gunakan lock hanya untuk update data penting
                with self.data_lock:
                    # PERBAIKAN: Update harga terakhir secara eksplisit
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
                    self.price_history[symbol].append((current_time_dt, price))

                # Update volume_by_symbol untuk log
                if symbol not in volume_by_symbol:
                    volume_by_symbol[symbol] = 0.0
                volume_by_symbol[symbol] += quantity

                current_time = time.time()
                if current_time - last_log_time >= 10:  # Log setiap 10 detik
                    logger.info(f"Trade processor: processed {trade_count} trades in last 10 seconds")
                    # Log volume untuk 5 simbol teratas
                    if volume_by_symbol:
                        top_symbols = sorted(volume_by_symbol.items(), key=lambda x: x[1], reverse=True)[:5]
                        log_msg = "Volume in last 10s: " + ", ".join([f"{sym}: {vol:.2f}" for sym, vol in top_symbols])
                        logger.info(log_msg)
                    trade_count = 0
                    volume_by_symbol = {}
                    last_log_time = current_time

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
                            previous_oi_val = self.previous_oi.get(symbol, 0)  # PERBAIKAN: Ambil dari previous_oi
                            funding_rate = d.get('funding_rate', 0)
                            liq = self.liquidation_accumulator.get(symbol, {'buy': 0.0, 'sell': 0.0})
                            liquidation_buy = liq.get('buy', 0.0)
                            liquidation_sell = liq.get('sell', 0.0)
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
                        buy_vol_candle = vol.get('market_buy', 0) * mark_price
                        sell_vol_candle = vol.get('market_sell', 0) * mark_price
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
                        prev_volume = previous_candle_data.get('volume', 0) * mark_price
                        current_volume = current_candle_data.get('volume', 0) * mark_price
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
                            score -= 1
                        if current_low < prev_low:
                            score += 1

                        # === PENINGKATAN: DETEKSI ANOMALI BURST VOLUME + LIKUIDASI SIMULTAN ===
                        burst_sell_threshold = burst_threshold.get('burst_sell_threshold', 50000)
                        burst_buy_threshold = burst_threshold.get('burst_buy_threshold', 50000)

                        burst_sell_usd = burst_sell * mark_price
                        burst_buy_usd = burst_buy * mark_price

                        if volume_breakout and burst_sell_usd > burst_sell_threshold:
                            # Anomali: Volume tinggi + likuidasi sell besar
                            score -= 3
                            logger.warning(f"ANOMALI {symbol}: Burst volume + likuidasi SELL besar: {burst_sell_usd:.2f} USD")

                        if volume_breakout and burst_buy_usd > burst_buy_threshold:
                            # Anomali: Volume tinggi + likuidasi buy besar
                            score += 3
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
                            saved = self._save_signal(symbol, mark_price, signal, score, current_candle)
                            
                            # Jika autobot aktif dan sinyal berhasil disimpan, coba buka posisi
                            if saved and self.autobot_enabled:
                                self._autobot_open_position(symbol, signal, mark_price, current_candle)

                        # Simpan sinyal terakhir untuk ditampilkan di frontend
                        with self.signal_lock:
                            self.last_signals[symbol] = signal
                            self.current_scores[symbol] = score

                    except Exception as e:
                        logger.error(f"Error deteksi sinyal untuk {symbol}: {e}")

            except Exception as e:
                logger.error(f"Error pada signal detector: {e}")

    def _process_trade_data(self, symbol: str, price: float):
        """Proses data perdagangan dan kirim update"""
        with self.data_lock:
            self.last_prices[symbol] = price
            self.last_update_time = datetime.utcnow()
            self.pending_price_updates[symbol] = price

    def _process_mark_price(self, symbol: str, price: float):
        """Proses harga mark dan kirim update"""
        with self.data_lock:
            self.mark_prices[symbol] = price
            self.last_update_time = datetime.utcnow()

    # ===== FUNGSI ORDER BARU =====
    def _place_binance_order(self, symbol: str, side: OrderSide, order_type: OrderType,
                         quantity: float, price: Optional[float] = None) -> Dict[str, Any]:
        """Membuat order di Binance Futures"""
        if not self.BINANCE_API_KEY or not self.BINANCE_API_SECRET:
            logger.error("API key/secret Binance tidak tersedia")
            return {'success': False, 'msg': 'Binance credentials not configured'}

        # Validasi quantity
        symbol_info = self.symbol_info_map.get(symbol)
        if not symbol_info:
            logger.error(f"Informasi simbol {symbol} tidak ditemukan")
            return {'success': False, 'msg': 'Symbol info not found'}

        min_qty = symbol_info.get('minQty', 0)
        min_notional = symbol_info.get('minNotional', 0)

        if quantity < min_qty:
            return {'success': False, 'msg': f'Quantity below minimum ({min_qty})'}

        # Hitung notional (quantity * price)
        if order_type == OrderType.LIMIT and price:
            notional = quantity * price
        else:
            # Untuk market order, gunakan mark price terakhir
            notional = quantity * self.mark_prices.get(symbol, 0)

        if notional < min_notional:
            return {'success': False, 'msg': f'Notional value below minimum ({min_notional} USD)'}

        # Siapkan parameter order
        params = {
            'symbol': symbol,
            'side': side.value,
            'type': order_type.value,
            'quantity': quantity,
            'timestamp': int(time.time() * 1000),
            'newOrderRespType': 'FULL'  # Dapatkan respons lengkap
        }

        if order_type == OrderType.LIMIT:
            if not price:
                return {'success': False, 'msg': 'Price required for limit order'}
            params['price'] = price
            params['timeInForce'] = 'GTC'  # Good Till Cancel

        # Generate signature
        params['signature'] = self._generate_signature(params)

        try:
            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            params = {
                'symbol': symbol,
                'side': side.value,
                'type': order_type.value,
                'quantity': quantity,
                'timestamp': int(time.time() * 1000),
                'newOrderRespType': 'FULL'
            }

            if order_type == OrderType.LIMIT and price:
                params['price'] = price
                params['timeInForce'] = 'GTC'

            # Generate signature
            params['signature'] = self._generate_signature(params)

            response = requests.post(
                "https://fapi.binance.com/fapi/v1/order",
                params=params,
                headers=headers,
                timeout=10
            )
            response.raise_for_status()
            order_data = response.json()

            logger.info(f"Order berhasil dibuat: {order_data}")
            return {'success': True, 'data': order_data}
        except Exception as e:
            logger.error(f"Error membuat order di Binance: {e}")
            return {'success': False, 'msg': str(e)}

    def _submit_order_to_database(self, symbol: str, side: str, order_type: str,
                             quantity: float, price: float, leverage: int,
                             stop_loss: Optional[float], take_profit: Optional[float],
                             binance_order_id: str, initial: bool = True) -> bool:
        """Simpan/perbarui order ke database"""
        valid_sides = ["LONG", "SHORT"]
        if side.upper() not in valid_sides:
            logger.error(f"Invalid position side: {side}")
            return False

        with self.db_semaphore:
            conn = self._get_db_connection()
            if not conn:
                return False

            try:
                cursor = conn.cursor()

                if initial:
                    # Insert new order
                    query = """
                        INSERT INTO tran_order (
                            symbol, price_open, status, posisi,
                            stop_lose, take_profit, timestamp,
                            qty, leverage, binance_order_id
                        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """
                    params = (
                        symbol,
                        price,
                        1,  # Status: Active
                        side.upper(),
                        stop_loss,
                        take_profit,
                        datetime.utcnow(),
                        quantity,
                        leverage,
                        binance_order_id
                    )
                else:
                    # Update existing order
                    query = """
                        UPDATE tran_order
                        SET price_open = ?, timestamp = ?
                        WHERE binance_order_id = ?
                    """
                    params = (
                        price,
                        datetime.utcnow(),
                        binance_order_id
                    )

                cursor.execute(query, params)
                conn.commit()

                if initial:
                    logger.info(f"Order disimpan: {symbol} {side} {quantity} @ {price}")
                else:
                    logger.info(f"Order diperbarui: ID {binance_order_id} harga {price}")

                return True
            except Exception as e:
                logger.error(f"Gagal menyimpan order: {e}")
                return False
            finally:
                conn.close()

    def submit_order(self):
        """Endpoint untuk menerima order dari frontend"""
        try:
            data = request.get_json()
            logger.info(f"Received order request: {data}")

            # Validasi data
            required_fields = ['symbol', 'side', 'order_type', 'qty', 'leverage']
            for field in required_fields:
                if field not in data:
                    return jsonify({'success': False, 'msg': f'Missing field: {field}'}), 400

            symbol = data['symbol']
            side = OrderSide.BUY if data['side'].lower() == 'long' else OrderSide.SELL
            order_type = OrderType[data['order_type'].upper()]
            quantity = float(data['qty'])
            leverage = int(data['leverage'])

            # Harga opsional untuk limit order
            price = float(data.get('price', 0)) if data.get('price') else None

            # SL/TP opsional
            stop_loss = float(data['stop_loss']) if 'stop_loss' in data and data['stop_loss'] else None
            take_profit = float(data['take_profit']) if 'take_profit' in data and data['take_profit'] else None

            # 1. Set leverage terlebih dahulu
            set_leverage_url = "https://fapi.binance.com/fapi/v1/leverage"
            leverage_params = {
                'symbol': symbol,
                'leverage': leverage,
                'timestamp': int(time.time() * 1000)
            }
            leverage_params['signature'] = self._generate_signature(leverage_params)

            leverage_response = requests.post(
                set_leverage_url,
                params=leverage_params,
                headers={"X-MBX-APIKEY": self.BINANCE_API_KEY},
                timeout=5
            )

            if not leverage_response.ok:
                logger.error(f"Gagal mengatur leverage: {leverage_response.text}")
                return jsonify({
                    'success': False,
                    'msg': f'Leverage setting failed: {leverage_response.json().get("msg", "")}'
                }), 400

            # 2. Buat order di Binance
            order_result = self._place_binance_order(
                symbol=symbol,
                side=side,
                order_type=order_type,
                quantity=quantity,
                price=price
            )

            if not order_result['success']:
                return jsonify(order_result), 400

            # 3. Simpan order awal ke database (sementara dengan harga 0)
            order_data = order_result['data']
            binance_order_id_actual = str(order_data['orderId'])

            db_success = self._submit_order_to_database(
                symbol=symbol,
                side="LONG" if side == OrderSide.BUY else "SHORT",  # Konversi ke LONG/SHORT
                order_type=order_type.value,
                quantity=quantity,
                price=0,
                leverage=leverage,
                stop_loss=stop_loss,
                take_profit=take_profit,
                binance_order_id=binance_order_id_actual,
                initial=True
            )

            # 4. Sinkronisasi harga dengan Binance - MODIFIKASI UTAMA DI SINI
            def sync_order_price():
                attempts = 0
                max_attempts = 18000
                order_filled = False
                order_canceled = False  # Track if order was canceled

                while attempts < max_attempts and not self.shutdown_event.is_set():
                    attempts += 1
                    time.sleep(3)

                    try:
                        order_detail = self._fetch_binance_order_detail(
                            int(binance_order_id_actual),
                            symbol
                        )

                        if not order_detail:
                            continue

                        status = order_detail.get('status')

                        # Handle filled orders
                        if status in ['PARTIALLY_FILLED', 'FILLED']:
                            executed_qty = float(order_detail.get('executedQty', 0))
                            if executed_qty > 0:
                                executed_price = float(order_detail.get('avgPrice', 0))
                                update_success = self._submit_order_to_database(
                                    symbol=symbol,
                                    side="LONG" if side == OrderSide.BUY else "SHORT",
                                    order_type=order_type.value,
                                    quantity=quantity,
                                    price=executed_price,
                                    leverage=leverage,
                                    stop_loss=stop_loss,
                                    take_profit=take_profit,
                                    binance_order_id=binance_order_id_actual,
                                    initial=False
                                )
                                if update_success:
                                    logger.info(f"Sukses sinkronisasi harga (status {status}) untuk order {binance_order_id_actual} @ {executed_price}")
                                    order_filled = True
                                    break
                            else:
                                logger.info(f"Order {binance_order_id_actual} status {status} but no quantity executed yet")

                        elif status in ['CANCELED', 'EXPIRED']:
                            logger.warning(f"Order {binance_order_id_actual} canceled/expired on Binance")

                            update_success = self._update_order_status(
                                order_id=binance_order_id_actual,
                                status=3,  # Status 3: Canceled
                                close_price=0
                            )
                            if update_success:
                                logger.info(f"Marked order {binance_order_id_actual} as canceled in database")
                            else:
                                logger.error(f"Failed to mark order {binance_order_id_actual} as canceled")

                            order_canceled = True
                            break

                    except Exception as e:
                        logger.error(f"Error checking order status: {e}")

                if not order_filled and not order_canceled:
                    logger.warning(f"Order {binance_order_id_actual} not filled after {max_attempts} attempts")
                    try:
                        order_detail = self._fetch_binance_order_detail(
                            int(binance_order_id_actual),
                            symbol
                        )
                        if order_detail and order_detail.get('status') in ['CANCELED', 'EXPIRED']:
                            self._update_order_status(
                                order_id=binance_order_id_actual,
                                status=3,
                                close_price=0
                            )
                    except Exception as e:
                        logger.error(f"Final status check failed: {e}")


            # Jalankan sinkronisasi di thread terpisah
            threading.Thread(target=sync_order_price, daemon=True).start()

            # 5. Refresh data sinyal
            self._refresh_signal_data()

            return jsonify({
                'success': True,
                'order_id': order_data['orderId'],
                'client_order_id': order_data['clientOrderId']
            })

        except Exception as e:
            logger.error(f"Error processing order: {str(e)}", exc_info=True)
            return jsonify({'success': False, 'msg': str(e)}), 500

    def _cancel_binance_order(self, symbol: str, order_id: int) -> Tuple[bool, str]:
        """Batalkan order di Binance Futures dan kembalikan (success, message)"""
        try:
            params = {
                'symbol': symbol,
                'orderId': order_id,
                'timestamp': int(time.time() * 1000)
            }
            params['signature'] = self._generate_signature(params)

            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}
            response = requests.delete(
                "https://fapi.binance.com/fapi/v1/order",
                params=params,
                headers=headers,
                timeout=5
            )
            response.raise_for_status()
            return True, "Order canceled successfully"
        except requests.exceptions.HTTPError as e:
            try:
                error_data = e.response.json()
                error_msg = error_data.get('msg', e.response.text)
                return False, f"Binance API error: {error_msg}"
            except:
                return False, f"HTTP error: {e.response.status_code}"
        except Exception as e:
            return False, f"Error canceling order: {str(e)}"

    def close_order(self):
        """Endpoint untuk menutup posisi di Binance"""
        try:
            data = request.get_json()
            if not data:
                return jsonify({'success': False, 'msg': 'Invalid JSON data'}), 400

            logger.info(f"Received close order request: {data}")

            # Validasi data dengan lebih ketat
            required_fields = ['order_id', 'symbol']
            missing = [field for field in required_fields if field not in data]
            if missing:
                return jsonify({
                    'success': False,
                    'msg': f'Missing required fields: {", ".join(missing)}'
                }), 400

            symbol = data['symbol'].strip().upper()
            order_id = str(data['order_id']).strip()

            # Validasi format order ID
            if not order_id or order_id.lower() == 'pending':
                return jsonify({'success': False, 'msg': 'Invalid order ID'}), 400

            logger.info(f"Processing close order for {symbol} - ID: {order_id}")

            # Dapatkan informasi posisi dari database
            position_info = self._get_position_info(order_id)
            if not position_info:
                return jsonify({
                    'success': False,
                    'msg': 'Active position not found or already closed'
                }), 404

            # Tutup posisi di Binance
            close_result = self._close_binance_position(
                symbol=symbol,
                position_side=position_info['position_side'],
                quantity=position_info['quantity']
            )

            if not close_result['success']:
                error_msg = close_result.get('msg', 'Unknown error from Binance')
                logger.error(f"Binance close failed: {error_msg}")
                return jsonify({'success': False, 'msg': error_msg}), 400

            # Perbarui status di database
            update_success = self._update_order_status(
                order_id=order_id,
                status=0,  # Status: Closed
                close_price=close_result['price']
            )

            if update_success:
                # Refresh cache open orders
                self._refresh_open_orders_cache()
                return jsonify({
                    'success': True,
                    'message': f"Position closed @ {close_result['price']}",
                    'price': close_result['price']
                })
            else:
                # Berhasil di Binance tapi gagal update database
                logger.error("Database update failed after successful Binance close")
                return jsonify({
                    'success': False,
                    'msg': 'Position closed on Binance but failed to update database',
                    'binance_price': close_result['price']
                }), 500

        except Exception as e:
            logger.error(f"Critical error in close_order: {str(e)}", exc_info=True)
            return jsonify({
                'success': False,
                'msg': 'Internal server error'
            }), 500

    def _get_position_info(self, binance_order_id: str) -> Optional[Dict]:
        """Dapatkan informasi posisi dengan konversi yang aman"""
        with self.db_semaphore:
            conn = self._get_db_connection()
            if not conn:
                return None

            try:
                cursor = conn.cursor()
                cursor.execute("""
                    SELECT symbol, posisi, qty, binance_order_id
                    FROM tran_order
                    WHERE binance_order_id = ? AND status = 1
                """, (binance_order_id,))
                row = cursor.fetchone()

                if not row:
                    return None

                # Konversi quantity dengan penanganan error
                try:
                    quantity = float(row.qty)
                except (TypeError, ValueError) as e:
                    logger.error(f"Invalid quantity format: {row.qty} - {str(e)}")
                    return None

                if quantity <= 0:
                    logger.error(f"Invalid quantity: {quantity}")
                    return None

                return {
                    'symbol': row.symbol,
                    'position_side': row.posisi.strip().upper(),
                    'quantity': quantity,
                    'binance_order_id': row.binance_order_id
                }
            except Exception as e:
                logger.error(f"Error in _get_position_info: {e}")
                return None
            finally:
                try:
                    conn.close()
                except:
                    pass

    def _close_binance_position(self, symbol: str, position_side: str, quantity: float) -> Dict:
        """Tutup posisi di Binance Futures"""
        if not self.BINANCE_API_KEY or not self.BINANCE_API_SECRET:
            return {'success': False, 'msg': 'Binance credentials not configured'}

        if position_side.upper() == "LONG":
            side = "SELL"
        elif position_side.upper() == "SHORT":
            side = "BUY"
        else:
            return {'success': False, 'msg': 'Invalid position side'}

        try:
            params = {
                'symbol': symbol.upper(),
                'side': side,
                'type': 'MARKET',
                'quantity': quantity,
                'reduceOnly': True,
                'recvWindow': 5000,
                'timestamp': int(time.time() * 1000)
            }

            # Signature
            params['signature'] = self._generate_signature(params)
            headers = {"X-MBX-APIKEY": self.BINANCE_API_KEY}

            response = requests.post(
                "https://fapi.binance.com/fapi/v1/order",
                params=params,
                headers=headers,
                timeout=10
            )
            response.raise_for_status()
            order_data = response.json()

            # Ambil harga dari field `avgFillPrice` atau gunakan `price`
            executed_price = float(order_data.get('avgFillPrice') or order_data.get('price') or 0.0)

            logger.info(f"Position closed successfully: {order_data}")
            return {
                'success': True,
                'price': executed_price,
                'data': order_data
            }

        except requests.exceptions.RequestException as e:
            try:
                error_data = e.response.json()
                error_msg = error_data.get('msg', str(e))
            except:
                error_msg = str(e)
            logger.error(f"Binance API error: {error_msg}")
            return {'success': False, 'msg': error_msg}

        except Exception as e:
            logger.error(f"Unexpected error: {str(e)}")
            return {'success': False, 'msg': str(e)}


    def _update_order_status(self, order_id: str, status: int, close_price: float) -> bool:
        """Update order status with support for canceled orders"""
        with self.db_semaphore:
            conn = self._get_db_connection()
            if not conn:
                return False

            try:
                cursor = conn.cursor()

                # Handle canceled orders differently (no close price)
                if status == 3:  # Canceled status
                    cursor.execute("""
                        UPDATE tran_order
                        SET status = ?, close_time = ?
                        WHERE binance_order_id = ? AND status = 1
                    """, (status, datetime.utcnow(), order_id))
                else:
                    cursor.execute("""
                        UPDATE tran_order
                        SET status = ?, price_close = ?, close_time = ?
                        WHERE binance_order_id = ? AND status = 1
                    """, (status, close_price, datetime.utcnow(), order_id))

                conn.commit()
                return cursor.rowcount > 0
            except Exception as e:
                logger.error(f"Error updating order status: {e}")
                return False
            finally:
                try:
                    conn.close()
                except:
                    pass

    def _refresh_open_orders_cache(self):
        """Refresh open orders cache setelah perubahan"""
        with self.open_orders_lock:
            self.open_orders_cache = self._fetch_open_orders_data()
            self.open_orders_last_updated = time.time()

        # Kirim update ke klien
        self.socketio.emit('open_orders_update', self.open_orders_cache, namespace='/')

    def _pnl_monitor(self):
        while not self.shutdown_event.is_set():
            try:
                time.sleep(3)

                # Dapatkan snapshot harga
                with self.data_lock:
                    mark_prices = self.mark_prices.copy()

                # Dapatkan open orders
                orders_data = self._fetch_open_orders_data()
                if orders_data['status'] != 'success':
                    continue

                for order in orders_data['data']:
                    if order['status'] != 1:  # Skip non-active orders
                        continue

                    symbol = order['symbol']
                    order_id = order['binance_order_id']

                    # Skip jika harga buka belum terisi (masih 0)
                    if order['price_open'] <= 0:
                        continue

                    # Dapatkan harga mark terbaru
                    current_price = mark_prices.get(symbol)
                    if not current_price:
                        continue

                    # Hitung PnL
                    pnl = self._calculate_pnl(order, current_price)

                    # Cek threshold dengan lock
                    with self.auto_close_lock:
                        if order_id in self.orders_in_process:
                            continue

                        if pnl <= self.AUTO_CLOSE_THRESHOLD_LOSS or pnl >= self.AUTO_CLOSE_THRESHOLD_PROFIT:
                            self.orders_in_process.add(order_id)
                            threading.Thread(
                                target=self._close_position,
                                args=(order_id, current_price),
                                daemon=True
                            ).start()
            except Exception as e:
                logger.error(f"PnL monitor error: {e}")

    def _calculate_pnl(self, order: Dict, current_price: float) -> float:
        """Hitung unrealized PnL dalam USD termasuk fee"""
        # Pastikan harga buka valid
        if order['price_open'] <= 0:
            return 0.0

        if order['posisi'] == 'LONG':
            pnl = (current_price - order['price_open']) * order['qty']
        else:  # SHORT
            pnl = (order['price_open'] - current_price) * order['qty']

        # Kurangi fee (contoh: 0.04% per trade)
        fee = order['price_open'] * order['qty'] * 0.0008
        return pnl - fee

    def _close_position(self, order_id: str, current_price: float):
        try:
            # Dapatkan info posisi
            position_info = self._get_position_info(order_id)
            if not position_info:
                return

            # Tutup di Binance
            close_result = self._close_binance_position(
                symbol=position_info['symbol'],
                position_side=position_info['position_side'],
                quantity=position_info['quantity']
            )

            if close_result['success']:
                # Update database
                self._update_order_status(
                    order_id=order_id,
                    status=0,
                    close_price=close_result['price']
                )
                logger.info(f"Auto-closed order {order_id} @ {close_result['price']}")
        except Exception as e:
            logger.error(f"Auto close failed: {e}")
        finally:
            with self.auto_close_lock:
                self.orders_in_process.discard(order_id)

    def cancel_order(self):
        """Endpoint untuk membatalkan order yang belum terisi"""
        try:
            data = request.get_json()
            logger.info(f"Received cancel order request: {data}")

            # Validasi data
            required_fields = ['order_id', 'symbol']
            for field in required_fields:
                if field not in data:
                    return jsonify({'success': False, 'msg': f'Missing field: {field}'}), 400

            symbol = data['symbol']
            order_id = data['order_id']

            # 1. Batalkan order di Binance
            cancel_success, cancel_msg = self._cancel_binance_order(symbol, int(order_id))
            if not cancel_success:
                return jsonify({'success': False, 'msg': cancel_msg}), 400

            # 2. Perbarui status di database
            update_success = self._update_order_status(
                order_id=order_id,
                status=0,  # Status: Closed (atau status khusus untuk dibatalkan)
                close_price=0
            )

            if not update_success:
                logger.warning("Order Binance berhasil dibatalkan tetapi gagal memperbarui database")

            # Refresh data setelah perubahan
            self._refresh_open_orders_cache()

            return jsonify({
                'success': True,
                'message': f"Order {order_id} canceled successfully"
            })

        except Exception as e:
            logger.error(f"Error canceling order: {str(e)}")
            return jsonify({'success': False, 'msg': str(e)}), 500

    # ===== ENDPOINT BARU =====
    def symbol_info(self):
        """Endpoint untuk mendapatkan informasi simbol futures (minQty dan minNotional)"""
        try:
            # Perbarui cache jika perlu
            self._fetch_symbol_info_map()

            with self.data_lock:
                # Buat salinan untuk thread safety
                symbol_info = self.symbol_info_map.copy()

            return jsonify({
                "status": "success",
                "data": symbol_info,
                "timestamp": datetime.utcnow().isoformat()
            })
        except Exception as e:
            logger.error(f"Error endpoint symbol_info: {e}")
            return jsonify({
                "status": "error",
                "message": str(e)
            }), 500

    def account_balance(self):
        """Endpoint untuk mendapatkan saldo akun Binance Futures"""
        try:
            # Perbarui cache jika perlu
            self._fetch_account_balance()

            with self.data_lock:
                # Buat salinan untuk thread safety
                balance = self.account_balance_cache.copy()

            return jsonify({
                "status": "success",
                "data": balance,
                "timestamp": datetime.utcnow().isoformat()
            })
        except Exception as e:
            logger.error(f"Error endpoint account_balance: {e}")
            return jsonify({
                "status": "error",
                "message": str(e)
            }), 500


    # ===== PERBAIKAN WEB SERVER HANDLERS =====
    def handle_connect(self):
        """Handler untuk koneksi Socket.IO - PERBAIKAN: tidak ada argumen tambahan"""
        logger.info('Client connected')
        # Kirim data segera setelah koneksi
        self.emit_data_update()

    def handle_disconnect(self):
        logger.info('Client disconnected')

    def handle_error(self, e):
        logger.error(f'Socket.IO error: {e}')
        self.error_counter += 1
        self.last_error_time = time.time()

    def handle_request_data(self):
        """Handler untuk request data - PERBAIKAN: tidak ada argumen tambahan"""
        logger.info('Client requested data')
        self.emit_data_update()

    def compress_data(self, data):
        """Kompresi data menggunakan zlib"""
        json_str = json.dumps(data, cls=DecimalEncoder)  # Gunakan custom encoder
        return zlib.compress(json_str.encode())

    def emit_data_update(self):
        try:
            # Gunakan cache jika tersedia dan belum kadaluarsa
            current_time = time.time()
            if self.cached_formatted_data and current_time - self.last_emit_time < 4:
                data = self.cached_formatted_data
            else:
                data = self.get_formatted_data()
                self.cached_formatted_data = data  # Cache data
                self.last_emit_time = current_time

            # Kompresi data jika besar
            json_str = json.dumps(data, cls=DecimalEncoder)
            if len(json_str) > 1024 * 1024:  # >1MB
                compressed = self.compress_data(data)
                self.socketio.emit('compressed_data', compressed, namespace='/')
            else:
                # PERBAIKAN: Kirim data langsung tanpa argumen 'json'
                self.socketio.emit('data_update', data, namespace='/')
        except Exception as e:
            logger.error(f"Error in emit_data_update: {e}")

    def _periodic_price_emitter(self):
        """Thread untuk mengirim update harga secara periodik"""
        while not self.shutdown_event.is_set():
            try:
                time.sleep(2)  # Kirim setiap 1 detik (dikurangi dari 0.5s)

                # Kirim update harga jika ada perubahan
                if self.pending_price_updates:
                    with self.data_lock:
                        if self.pending_price_updates:
                            # Buat salinan data untuk dikirim
                            price_data = self.pending_price_updates.copy()
                            self.pending_price_updates = {}

                    # Pastikan semua nilai float
                    clean_price_data = {symbol: float(price) for symbol, price in price_data.items()}

                    # Kirim dalam satu paket
                    self.socketio.emit('price_update', {
                        'updates': clean_price_data,
                        'timestamp': datetime.utcnow().isoformat()
                    }, namespace='/')

                # Kirim data lengkap setiap 5 detik
                current_time = time.time()
                if current_time - self.last_emit_time >= 5:
                    self.emit_data_update()
                    self.last_emit_time = current_time

                # Buat snapshot data harga
                with self.data_lock:
                    mark_prices_snapshot = self.mark_prices.copy()

                # Kirim ke semua klien
                if mark_prices_snapshot:
                    self.socketio.emit(
                        'price_update',
                        {'mark_prices': mark_prices_snapshot},
                        namespace='/'
                    )

            except Exception as e:
                logger.error(f"Error dalam periodic emitter: {e}")

    @login_required
    def dashboard(self):
        return render_template('dashboard.html')

    def index_redirect(self):
        return redirect('/')

    @login_required
    def manual_reload(self):
        # Refresh data dari database
        self._refresh_signal_data()
        self.emit_data_update()
        return jsonify({"status": "success", "message": "Data reloaded"})

    def health_check(self):
        return jsonify({
            "status": "ok",
            "time": datetime.utcnow().isoformat(),
            "symbol_count": len(self.symbols),
            "last_update": self.last_update_time.isoformat(),
            "error_count": self.error_counter,
            "last_error": datetime.utcfromtimestamp(self.last_error_time).isoformat() if self.last_error_time else "never"
        })

    def get_formatted_data(self):
        """Format data untuk dikirim ke frontend"""
        assets = []
        server_info = f"{self.SQL_SERVER} | {self.SQL_DATABASE}"

        # Ambil data sinyal dari cache
        with self.signal_cache_lock:
            signal_cache = self.signal_data_cache.copy()

        with self.data_lock:
            for symbol in self.symbols:
                # Ambil data dari struktur internal
                d = self.display_data.get(symbol, {})
                last_price = float(self.last_prices.get(symbol, 0.0))  # Pastikan float
                mark_price = float(self.mark_prices.get(symbol, 0.0))  # Pastikan float
                liq = self.liquidation_accumulator.get(symbol, {'buy': 0.0, 'sell': 0.0})
                vol = self.volume_accumulator.get(symbol, {'market_buy': 0.0, 'market_sell': 0.0})

                # Ambil data sinyal dari cache database
                signal_info = signal_cache.get(symbol, {})

                # Ambil data realtime dengan lock
                with self.signal_lock:
                    realtime_signal = self.last_signals.get(symbol, 'HOLD')
                    realtime_score = self.current_scores.get(symbol, 0)

                # Format data untuk baris tabel
                asset = {
                    'id': signal_info.get('id', 0),
                    'symbol': symbol,
                    'price_open': float(signal_info.get('price_open', 0.0)),  # Konversi ke float
                    # Posisi Sch: menggunakan data realtime
                    'posisi_sch': f"{realtime_signal} / {realtime_score}",
                    # Posisi Sign: menggunakan data dari database (posisi + signal_score)
                    # PERBAIKAN: Format menjadi 'POSISI / SKOR' dan bulatkan skor
                    'posisi_sign': f"{signal_info.get('posisi', 'HOLD')} / {int(round(float(signal_info.get('signal_score', 0))))}",
                    'last_price': last_price,
                    'mark_price': mark_price,
                    'liquidation_buy': float(liq.get('buy', 0)) * mark_price if mark_price else 0,
                    'liquidation_sell': float(liq.get('sell', 0)) * mark_price if mark_price else 0,
                    'volume_buy': float(vol.get('market_buy', 0)) * mark_price if mark_price else 0,
                    'volume_sell': float(vol.get('market_sell', 0)) * mark_price if mark_price else 0,
                    'updated': True
                }
                assets.append(asset)

        # PERBAIKAN: Urutkan aset dengan price_open != 0 di atas
        active_signals = [a for a in assets if a['price_open'] != 0]
        inactive_signals = [a for a in assets if a['price_open'] == 0]

        # Gabungkan kembali dengan active_signals di atas
        sorted_assets = active_signals + inactive_signals

        return {
            'assets': sorted_assets,
            'last_update': self.last_update_time.strftime('%Y-%m-%d %H:%M:%S'),
            'last_db_reload': datetime.utcfromtimestamp(self.last_db_reload).strftime('%Y-%m-%d %H:%M:%S'),
            'server_info': server_info
        }

    def run_web_server(self):
        logger.info("Starting web server on port 5000")
        self.socketio.run(
            self.flask_app,
            host='0.0.0.0',
            port=5000,
            debug=False,
            use_reloader=False,
            log_output=False,  # Nonaktifkan output log
            allow_unsafe_werkzeug=True
        )

    def run(self):
        logger.info("Memuat daftar simbol...")
        self._load_symbol_list()
        self._initialize_data_structures()
        self._initialize_order_books()

        # Muat informasi simbol awal
        self._fetch_symbol_info_map()

        # Muat saldo akun awal jika kredensial tersedia
        if self.BINANCE_API_KEY and self.BINANCE_API_SECRET:
            self._fetch_account_balance()

        logger.info("Memulai thread-thread pekerja...")
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
            threading.Thread(target=self._periodic_price_emitter, name="PriceEmitter", daemon=True),
            threading.Thread(target=self._periodic_symbol_info_updater, name="SymbolInfoUpdater", daemon=True),
            threading.Thread(target=self._periodic_balance_updater, name="BalanceUpdater", daemon=True),
            threading.Thread(target=self._periodic_open_orders_updater, name="OpenOrdersUpdater", daemon=True),
            threading.Thread(target=self._periodic_mark_price_updater, name="MarkPriceUpdater", daemon=True),
            threading.Thread(target=self._pnl_monitor, name="PnLMonitor", daemon=True)
        ]

        # Tambahkan thread untuk setiap stream config
        for name, url, handler in stream_configs:
            threads.append(threading.Thread(
                target=self._websocket_connector,
                args=(url, name, handler),
                name=f"WS-{name}",
                daemon=True
            ))

        # Start web server in a separate thread
        web_thread = threading.Thread(target=self.run_web_server, daemon=True, name="WebServer")
        threads.append(web_thread)

        for t in threads:
            t.start()

        logger.info("Signal detector berjalan. Tekan Ctrl+C berhenti.")
        try:
            while not self.shutdown_event.is_set():
                time.sleep(1)
        except KeyboardInterrupt:
            self.shutdown_event.set()
            logger.info("\nMenghentikan semua thread...")
            for t in threads:
                if t.is_alive():
                    t.join(timeout=5)
            logger.info("Program dihentikan.")

    def _periodic_symbol_info_updater(self):
        """Thread untuk memperbarui informasi simbol secara periodik"""
        while not self.shutdown_event.wait(self.symbol_info_refresh_interval):
            self._fetch_symbol_info_map()

    def _periodic_balance_updater(self):
        """Thread untuk memperbarui saldo akun secara periodik"""
        while not self.shutdown_event.wait(self.balance_refresh_interval):
            if self.BINANCE_API_KEY and self.BINANCE_API_SECRET:
                self._fetch_account_balance()

    def _periodic_open_orders_updater(self):
        """Thread untuk memperbarui data open orders setiap 10 detik"""
        while not self.shutdown_event.wait(15):
            try:
                logger.info("Memperbarui data open orders...")

                # Ambil data dari database
                orders_data = self._fetch_open_orders_data()

                # Simpan di cache
                with self.open_orders_lock:
                    self.open_orders_cache = orders_data
                    self.open_orders_last_updated = time.time()

                # Kirim ke frontend
                self.socketio.emit('open_orders_update', orders_data, namespace='/')
            except Exception as e:
                logger.error(f"Error pembaruan open orders: {e}")

    def _periodic_mark_price_updater(self):
        """Thread untuk mengirim update mark price setiap 1 detik"""
        while not self.shutdown_event.wait(3):
            try:
                # Ambil snapshot mark prices
                with self.data_lock:
                    mark_prices = self.mark_prices.copy()

                # Kirim ke frontend
                self.socketio.emit('mark_price_update', mark_prices, namespace='/')
            except Exception as e:
                logger.error(f"Error pembaruan mark price: {e}")

if __name__ == "__main__":
    try:
        detector = SignalDetector()
        detector.run()
    except Exception as e:
        logger.critical(f"Terjadi error fatal: {e}", exc_info=True)
