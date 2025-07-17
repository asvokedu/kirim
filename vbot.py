import ccxt
import pyodbc
import time
import threading
from datetime import datetime, timedelta
from decimal import Decimal
import os
from dotenv import load_dotenv
import logging
import json

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('trading_bot.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class BinanceFuturesBot:
    def __init__(self):
        # Load environment variables
        load_dotenv()
        
        # Trading configuration
        self.BALANCE_PER_SYMBOL = Decimal(os.getenv('BALANCE_PER_SYMBOL', '1000'))
        self.SAFETY_MARGIN = Decimal(os.getenv('SAFETY_MARGIN', '0.9'))
        self.SLIPPAGE_TOLERANCE = Decimal(os.getenv('SLIPPAGE_TOLERANCE', '0.005'))
        self.MIN_REOPEN_DELAY = int(os.getenv('MIN_REOPEN_DELAY', '60'))
        
        # Inisialisasi koneksi Binance
        self.exchange = ccxt.binance({
            'apiKey': os.getenv('BINANCE_API_KEY'),
            'secret': os.getenv('BINANCE_API_SECRET'),
            'enableRateLimit': True,
            'options': {
                'defaultType': 'future',
            }
        })
        
        # Inisialisasi koneksi database
        self.db_conn = self.create_db_connection()
        self.db_cursor = self.db_conn.cursor()
        
        # Data trading
        self.last_prices = {}
        self.mark_prices = {}
        self.last_closed_time = {}
        self.total_balance = Decimal('0')
        self.used_margin = Decimal('0')
        self.positions = {}
        
        # Flag untuk menghentikan thread
        self.running = True
        
        # Mapping status
        self.status_mapping = {
            'PENDING': 0,
            'OPEN': 1,
            'CLOSED': 2,
            'CANCELED': 3,
            'FAILED': 4
        }
        
        # Load balance awal
        self.update_balance()
        
    def create_db_connection(self):
        """Membuat koneksi ke database SQL Server"""
        try:
            conn_str = (
                f"DRIVER={os.getenv('SQL_DRIVER')};"
                f"SERVER={os.getenv('SQL_SERVER')};"
                f"DATABASE={os.getenv('SQL_DATABASE')};"
                f"UID={os.getenv('SQL_USERNAME')};"
                f"PWD={os.getenv('SQL_PASSWORD')};"
            )
            return pyodbc.connect(conn_str)
        except Exception as e:
            logger.error(f"Gagal terhubung ke database: {e}")
            raise

    def start(self):
        """Memulai bot trading"""
        logger.info("Memulai Binance Futures Trading Bot...")
        logger.info(f"Konfigurasi: Balance per Symbol={self.BALANCE_PER_SYMBOL}, Safety Margin={self.SAFETY_MARGIN}")
        logger.info(f"Slippage Tolerance={self.SLIPPAGE_TOLERANCE}, Min Reopen Delay={self.MIN_REOPEN_DELAY}s")
        
        try:
            # Mulai thread untuk memantau harga dan balance
            price_thread = threading.Thread(target=self.monitor_prices_and_balance, daemon=True)
            price_thread.start()
            
            # Mulai thread untuk memproses signal
            signal_thread = threading.Thread(target=self.process_signals, daemon=True)
            signal_thread.start()
            
            # Mulai thread untuk memantau posisi terbuka
            position_thread = threading.Thread(target=self.monitor_positions, daemon=True)
            position_thread.start()
            
            while self.running:
                time.sleep(1)
                
        except KeyboardInterrupt:
            logger.info("Menghentikan bot...")
            self.running = False
        except Exception as e:
            logger.error(f"Error utama: {e}")
            self.running = False
            
    def monitor_prices_and_balance(self):
        """Memantau harga dan balance secara realtime"""
        logger.info("Memulai pemantauan harga dan balance...")
        
        while self.running:
            try:
                # Ambil data ticker untuk semua symbol
                tickers = self.exchange.fetch_tickers()
                
                for symbol, ticker in tickers.items():
                    if symbol.endswith('/USDT'):  # Hanya untuk pair USDT
                        self.last_prices[symbol] = Decimal(str(ticker['last']))
                        self.mark_prices[symbol] = Decimal(str(ticker['info']['markPrice']))
                
                # Update balance dan margin
                self.update_balance()
                
                # Log harga untuk monitoring
                price_info = "\n".join(
                    f"{symbol}: Last={self.last_prices[symbol]}, Mark={self.mark_prices[symbol]}" 
                    for symbol in list(self.last_prices.keys())[:5]
                )
                logger.info(f"\nHarga Terakhir - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                logger.info(f"Total Balance: {self.total_balance}, Used Margin: {self.used_margin}")
                logger.info(f"Available Margin: {self.total_balance - self.used_margin}")
                logger.info(f"Price Info:\n{price_info}")
                
                time.sleep(5)  # Update setiap 5 detik
                
            except Exception as e:
                logger.error(f"Error dalam pemantauan harga: {e}")
                time.sleep(10)
    
    def update_balance(self):
        """Update total balance dan used margin dari exchange"""
        try:
            balance = self.exchange.fetch_balance()
            self.total_balance = Decimal(str(balance['USDT']['total']))
            self.used_margin = Decimal(str(balance['USDT']['used']))
            
            # Update posisi terbuka
            self.positions = {}
            for position in balance['info']['positions']:
                if Decimal(position['positionAmt']) != 0:
                    symbol = position['symbol'].replace('USDT', '') + '/USDT'
                    self.positions[symbol] = {
                        'side': 'LONG' if Decimal(position['positionAmt']) > 0 else 'SHORT',
                        'amount': abs(Decimal(position['positionAmt'])),
                        'entryPrice': Decimal(position['entryPrice'])
                    }
        except Exception as e:
            logger.error(f"Error update balance: {e}")
    
    def process_signals(self):
        """Memproses signal trading dari database"""
        logger.info("Memulai pemrosesan signal...")
        
        while self.running:
            try:
                # Eksekusi stored procedure untuk mendapatkan signal
                self.db_cursor.execute("EXEC sp_tranTF_last")
                signals = self.db_cursor.fetchall()
                
                if signals:
                    logger.info(f"Ditemukan {len(signals)} signal untuk diproses")
                    
                    for signal in signals:
                        try:
                            signal_id = signal.id
                            symbol = signal.symbol
                            posisi = signal.posisi.upper()  # LONG/SHORT
                            price_open = Decimal(str(signal.price_open))
                            leverage = signal.leverage
                            stop_lose = Decimal(str(signal.stop_lose))
                            take_profit = Decimal(str(signal.take_profit))
                            signal_ch = signal.signal_score  # Unique signal identifier
                            
                            # Format symbol untuk Binance
                            binance_symbol = f"{symbol}/USDT"
                            
                            # Dapatkan harga mark saat ini
                            mark_price = self.mark_prices.get(binance_symbol, Decimal('0'))
                            
                            if mark_price == 0:
                                continue
                            
                            # 1. Trigger Eksekusi Open Posisi
                            trigger_condition_met = False
                            if posisi == "LONG" and mark_price <= price_open:
                                trigger_condition_met = True
                            elif posisi == "SHORT" and mark_price >= price_open:
                                trigger_condition_met = True
                            
                            if not trigger_condition_met:
                                logger.info(f"Signal {signal_id} belum memenuhi kondisi trigger (Posisi: {posisi}, Mark: {mark_price}, Open: {price_open})")
                                continue
                            
                            # 2. Validasi Margin
                            available_margin = (self.total_balance - self.used_margin) * self.SAFETY_MARGIN
                            if available_margin < self.BALANCE_PER_SYMBOL:
                                logger.warning(f"Margin tidak cukup untuk {symbol}. Available: {available_margin}, Required: {self.BALANCE_PER_SYMBOL}")
                                continue
                            
                            # 3. Slippage Aware Quantity Calculation
                            if posisi == "LONG":
                                worst_case_price = mark_price * (1 + self.SLIPPAGE_TOLERANCE)
                            else:  # SHORT
                                worst_case_price = mark_price * (1 - self.SLIPPAGE_TOLERANCE)
                            
                            qty = (self.BALANCE_PER_SYMBOL * leverage) / worst_case_price
                            qty = self.adjust_quantity_precision(symbol, qty)
                            
                            logger.info(f"Memproses signal {signal_id}: {symbol} {posisi} {qty} @ ~{mark_price} (leverage {leverage}x)")
                            
                            # 5. Cegah Duplikasi Sinyal Close-Open
                            last_closed = self.last_closed_time.get(binance_symbol)
                            if last_closed and (datetime.now() - last_closed).total_seconds() < self.MIN_REOPEN_DELAY:
                                logger.info(f"Menunggu {self.MIN_REOPEN_DELAY}s sebelum open baru untuk {symbol}")
                                continue
                            
                            # Set leverage terlebih dahulu
                            self.set_leverage(symbol, leverage)
                            
                            # Eksekusi order
                            order_result = self.execute_order(symbol, posisi, qty)
                            
                            if order_result:
                                # Dapatkan harga eksekusi aktual
                                execution_price = Decimal(str(order_result['price'])) if order_result['price'] else mark_price
                                
                                # Update status di database jika order berhasil
                                self.update_signal_status(
                                    signal_id=signal_id,
                                    status='OPEN',
                                    binance_order_id=order_result['id'],
                                    price_open=execution_price,
                                    leverage=leverage,
                                    stop_lose=stop_lose,
                                    take_profit=take_profit,
                                    signal_ch=signal_ch
                                )
                                logger.info(f"Order berhasil dieksekusi: {order_result['id']}")
                            else:
                                self.update_signal_status(signal_id, 'FAILED')
                                logger.error("Gagal mengeksekusi order")
                                
                        except Exception as e:
                            logger.error(f"Error memproses signal {signal.id if hasattr(signal, 'id') else 'unknown'}: {e}")
                            continue
                
                time.sleep(10)  # Cek signal setiap 10 detik
                
            except Exception as e:
                logger.error(f"Error dalam pemrosesan signal: {e}")
                time.sleep(30)
    
    def adjust_quantity_precision(self, symbol, qty):
        """Menyesuaikan quantity dengan precision yang didukung oleh exchange"""
        try:
            market = self.exchange.market(f"{symbol}/USDT")
            precision = market['precision']['amount']
            adjusted_qty = Decimal(str(round(float(qty), precision)))
            return adjusted_qty
        except Exception as e:
            logger.error(f"Error adjust quantity precision: {e}")
            return qty
    
    def monitor_positions(self):
        """Memantau posisi terbuka dan eksekusi TP/SL"""
        logger.info("Memulai pemantauan posisi terbuka...")
        
        while self.running:
            try:
                # Ambil semua posisi terbuka dari database
                self.db_cursor.execute("""
                    SELECT id, symbol, binance_order_id, posisi, qty, price_open, 
                           stop_lose, take_profit, leverage, signal_score
                    FROM tran_TF 
                    WHERE status = 1""")  # Status 1 = OPEN
                open_positions_db = self.db_cursor.fetchall()
                
                if open_positions_db:
                    logger.info(f"Memantau {len(open_positions_db)} posisi terbuka...")
                    
                    for db_position in open_positions_db:
                        try:
                            position_id = db_position.id
                            symbol = db_position.symbol
                            binance_order_id = db_position.binance_order_id
                            db_posisi = db_position.posisi.upper()  # LONG/SHORT
                            db_qty = Decimal(str(db_position.qty))
                            price_open = Decimal(str(db_position.price_open))
                            stop_lose = Decimal(str(db_position.stop_lose))
                            take_profit = Decimal(str(db_position.take_profit))
                            leverage = db_position.leverage
                            db_signal_ch = db_position.signal_score
                            
                            # Format symbol untuk Binance
                            binance_symbol = f"{symbol}/USDT"
                            
                            # Dapatkan posisi aktual dari exchange
                            current_position = self.positions.get(binance_symbol)
                            
                            # 4. CLOSE POSISI - Cross-check dengan posisi aktual
                            should_close = False
                            close_reason = ""
                            
                            # Cek jika posisi sudah tidak ada di exchange
                            if not current_position:
                                should_close = True
                                close_reason = "Position Not Found"
                            # Cek jika posisi berbeda (LONG vs SHORT)
                            elif current_position['side'] != db_posisi:
                                should_close = True
                                close_reason = f"Position Mismatch (DB:{db_posisi}, Exchange:{current_position['side']})"
                            # Cek jika signal_ch berbeda (signal baru)
                            # (Implementasi ini memerlukan field signal_ch di database)
                            
                            # Jika tidak ada masalah cross-check, cek TP/SL
                            if not should_close:
                                # Dapatkan harga saat ini
                                current_price = self.mark_prices.get(binance_symbol, Decimal('0'))
                                
                                if current_price == 0:
                                    continue
                                    
                                # 6. Cross-check PnL (unrealized)
                                unrealized_pnl = self.calculate_pnl(
                                    db_posisi, 
                                    db_qty, 
                                    price_open, 
                                    current_price, 
                                    leverage
                                )
                                logger.info(f"Posisi {position_id}: Unrealized PnL = {unrealized_pnl}")
                                
                                # Cek apakah TP/SL terpicu
                                if db_posisi == 'LONG':
                                    if current_price <= stop_lose:
                                        should_close = True
                                        close_reason = "Stop Loss"
                                    elif current_price >= take_profit:
                                        should_close = True
                                        close_reason = "Take Profit"
                                elif db_posisi == 'SHORT':
                                    if current_price >= stop_lose:
                                        should_close = True
                                        close_reason = "Stop Loss"
                                    elif current_price <= take_profit:
                                        should_close = True
                                        close_reason = "Take Profit"
                            
                            if should_close:
                                logger.info(f"{close_reason} terpicu untuk posisi {position_id}")
                                self.close_position(
                                    position_id=position_id,
                                    symbol=symbol,
                                    posisi=db_posisi,
                                    qty=db_qty,
                                    price_open=price_open,
                                    current_price=self.mark_prices.get(binance_symbol, Decimal('0')),
                                    leverage=leverage,
                                    close_reason=close_reason
                                )
                                
                        except Exception as e:
                            logger.error(f"Error memantau posisi {db_position.id if hasattr(db_position, 'id') else 'unknown'}: {e}")
                            continue
                
                time.sleep(15)  # Cek posisi setiap 15 detik
                
            except Exception as e:
                logger.error(f"Error dalam pemantauan posisi: {e}")
                time.sleep(30)
    
    def set_leverage(self, symbol, leverage):
        """Mengatur leverage untuk symbol tertentu"""
        try:
            # Format symbol untuk Binance
            binance_symbol = f"{symbol}/USDT"
            
            # Set leverage
            self.exchange.set_leverage(leverage, binance_symbol)
            logger.info(f"Leverage untuk {symbol} diatur ke {leverage}x")
        except Exception as e:
            logger.error(f"Gagal mengatur leverage untuk {symbol}: {e}")
    
    def execute_order(self, symbol, posisi, qty):
        """Mengeksekusi order di Binance"""
        try:
            # Format symbol untuk Binance
            binance_symbol = f"{symbol}/USDT"
            
            # Konversi posisi LONG/SHORT ke side buy/sell
            side = 'buy' if posisi == 'LONG' else 'sell'
            
            # Buat order market
            order = self.exchange.create_order(
                symbol=binance_symbol,
                type='MARKET',
                side=side,
                amount=float(qty),
                params={'positionSide': 'BOTH'}  # Untuk futures
            )
            
            # Dapatkan detail order
            order_details = self.exchange.fetch_order(order['id'], binance_symbol)
            return order_details
            
        except Exception as e:
            logger.error(f"Error dalam eksekusi order: {e}")
            return None
    
    def close_position(self, position_id, symbol, posisi, qty, price_open, current_price, leverage, close_reason):
        """Menutup posisi terbuka"""
        try:
            # Format symbol untuk Binance
            binance_symbol = f"{symbol}/USDT"
            
            # 5. Cegah Duplikasi Sinyal Close
            if binance_symbol in self.last_closed_time:
                last_close = self.last_closed_time[binance_symbol]
                if (datetime.now() - last_close).total_seconds() < self.MIN_REOPEN_DELAY:
                    logger.info(f"Menunggu {self.MIN_REOPEN_DELAY}s sebelum close baru untuk {symbol}")
                    return False
            
            # Tentukan side untuk penutupan posisi
            close_side = 'sell' if posisi == 'LONG' else 'buy'
            
            # Eksekusi order penutupan
            close_order = self.execute_order(symbol, close_side.upper(), qty)
            
            if close_order:
                # Hitung PnL
                pnl = self.calculate_pnl(posisi, qty, price_open, current_price, leverage)
                
                # Update status di database
                self.update_signal_status(
                    signal_id=position_id,
                    status='CLOSED',
                    binance_close_id=close_order['id'],
                    price_close=current_price,
                    pnl_real=pnl,
                    close_reason=close_reason
                )
                
                # Update last closed time
                self.last_closed_time[binance_symbol] = datetime.now()
                
                logger.info(f"Posisi {position_id} berhasil ditutup. PnL: {pnl}")
                return True
            else:
                logger.error(f"Gagal menutup posisi {position_id}")
                return False
                
        except Exception as e:
            logger.error(f"Error dalam penutupan posisi: {e}")
            return False
    
    def calculate_pnl(self, posisi, qty, entry_price, exit_price, leverage):
        """Menghitung PnL real"""
        qty = Decimal(str(qty))
        entry_price = Decimal(str(entry_price))
        exit_price = Decimal(str(exit_price))
        leverage = Decimal(str(leverage))
        
        if posisi == 'LONG':
            pnl = qty * (exit_price - entry_price) / entry_price * leverage
        else:  # SHORT
            pnl = qty * (entry_price - exit_price) / entry_price * leverage
            
        return pnl
    
    def update_signal_status(self, signal_id, status, **kwargs):
        """Update status signal di database"""
        try:
            status_code = self.status_mapping.get(status, 0)
            
            if status == 'OPEN':
                self.db_cursor.execute("""
                    UPDATE tran_TF 
                    SET binance_order_id = ?, price_open = ?, leverage = ?, 
                        stop_lose = ?, take_profit = ?, status = ?, signal_score = ?, timestamp = GETDATE()
                    WHERE id = ?""",
                    kwargs.get('binance_order_id'), 
                    float(kwargs.get('price_open')), 
                    kwargs.get('leverage'),
                    float(kwargs.get('stop_lose')),
                    float(kwargs.get('take_profit')),
                    status_code,
                    kwargs.get('signal_ch'),
                    signal_id
                )
            elif status == 'CLOSED':
                self.db_cursor.execute("""
                    UPDATE tran_TF 
                    SET binance_close_id = ?, price_close = ?, status = ?, 
                        pnl_real = ?, feebinance = ?, close_reason = ?, timestamp = GETDATE()
                    WHERE id = ?""",
                    kwargs.get('binance_close_id'), 
                    float(kwargs.get('price_close')),
                    status_code,
                    float(kwargs.get('pnl_real')),
                    float(kwargs.get('feebinance', 0)),
                    kwargs.get('close_reason', ''),
                    signal_id
                )
            else:
                self.db_cursor.execute("""
                    UPDATE tran_TF 
                    SET status = ?, timestamp = GETDATE()
                    WHERE id = ?""",
                    status_code,
                    signal_id
                )
                
            self.db_conn.commit()
        except Exception as e:
            logger.error(f"Error dalam update status signal: {e}")
    
    def __del__(self):
        """Cleanup saat bot dihentikan"""
        try:
            if hasattr(self, 'db_cursor'):
                self.db_cursor.close()
            if hasattr(self, 'db_conn'):
                self.db_conn.close()
            if hasattr(self, 'exchange'):
                self.exchange.close()
        except Exception as e:
            logger.error(f"Error saat cleanup: {e}")

if __name__ == "__main__":
    # Install package yang diperlukan jika belum ada
    try:
        import ccxt
        import pyodbc
        from dotenv import load_dotenv
    except ImportError as e:
        print(f"Package yang diperlukan belum terinstall: {e}")
        print("Silakan install dengan perintah: pip install ccxt pyodbc python-dotenv")
        exit(1)
    
    try:
        bot = BinanceFuturesBot()
        bot.start()
    except Exception as e:
        logging.error(f"Error utama: {e}")
