import sys
import os
import codecs
import struct
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout,
                             QHBoxLayout, QPushButton, QTableWidget, QTableWidgetItem,
                             QFileDialog, QMessageBox, QLabel, QHeaderView, QLineEdit,
                             QToolBar, QStatusBar, QMenu, QMenuBar, QProgressDialog,
                             QInputDialog)
from PySide6.QtCore import Qt, QSize, QThread, Signal, QThreadPool, QRunnable, QObject, Slot
from PySide6.QtGui import QFont, QIcon, QColor, QAction
from googletrans import Translator
import urllib.request
import urllib.parse
import re
import html.parser

@dataclass
class DBPFHeader:
    version: int
    index_major_version: int
    index_count: int
    index_offset: int
    index_size: int

@dataclass
class DBPFEntry:
    type_id: int
    group_id: int
    instance_id: int
    offset: int
    size: int
    
class DBPFFile:
    STBL_TYPE = 0x220557DA  # String table type ID
    
    def __init__(self):
        self.header: Optional[DBPFHeader] = None
        self.entries: List[DBPFEntry] = []
        self.string_tables: Dict[int, StringTableFile] = {}  # instance_id -> StringTableFile
        
    def load_from_binary(self, data: bytes) -> bool:
        try:
            if len(data) < 96:  # Minimum header size
                print("Data too small for DBPF")
                return False
                
            if not data.startswith(b'DBPF'):
                print("Not a DBPF file")
                return False
                
            pos = 4  # Skip DBPF magic
            
            # Read file version (must be 2,1)
            file_version = (int.from_bytes(data[pos:pos+4], 'little'),
                          int.from_bytes(data[pos+4:pos+8], 'little'))
            if file_version != (2, 1):
                print(f"Unsupported DBPF version: {file_version}")
                return False
            pos += 8
            
            # Read user version (must be 0,0)
            user_version = (int.from_bytes(data[pos:pos+4], 'little'),
                          int.from_bytes(data[pos+4:pos+8], 'little'))
            if user_version != (0, 0):
                print(f"Unsupported user version: {user_version}")
                return False
            pos += 8
            
            # Skip unused
            pos += 4
            
            # Read timestamps
            creation_time = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            updated_time = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Skip unused
            pos += 4
            
            # Read index info
            index_count = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            index_offset_low = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            index_size = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Skip to high offset
            pos += 16
            index_offset_high = int.from_bytes(data[pos:pos+4], 'little')
            
            # Use high offset if available
            index_offset = index_offset_high if index_offset_high != 0 else index_offset_low
            
            print(f"DBPF Version: {file_version}")
            print(f"User Version: {user_version}")
            print(f"Creation Time: {creation_time}, Updated Time: {updated_time}")
            print(f"Index Count: {index_count}, Offset: {index_offset}, Size: {index_size}")
            
            if index_offset == 0:
                if index_count != 0:
                    print("Warning: Package contains entries but no index")
                return False
            
            # Store header info
            self.header = DBPFHeader(
                version=file_version[0],
                index_major_version=user_version[0],
                index_count=index_count,
                index_offset=index_offset,
                index_size=index_size
            )
            
            # Read index entries
            pos = index_offset
            flags = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Handle constant values based on flags
            const_type = bool(flags & 1)
            const_group = bool(flags & 2)
            const_instance_ex = bool(flags & 4)
            
            if const_type:
                entry_type = int.from_bytes(data[pos:pos+4], 'little')
                pos += 4
            if const_group:
                entry_group = int.from_bytes(data[pos:pos+4], 'little')
                pos += 4
            if const_instance_ex:
                entry_inst_ex = int.from_bytes(data[pos:pos+4], 'little')
                pos += 4
            
            for i in range(index_count):
                try:
                    # Read type ID if not constant
                    if not const_type:
                        entry_type = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    
                    # Read group ID if not constant
                    if not const_group:
                        entry_group = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    
                    # Read instance high bits if not constant
                    if not const_instance_ex:
                        entry_inst_ex = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    
                    # Read instance low bits
                    entry_inst = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Read resource offset and size
                    resource_offset = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    file_size = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Read decompressed size
                    decompressed_size = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Handle compression
                    if file_size & 0x80000000:
                        compression = (int.from_bytes(data[pos:pos+2], 'little'),
                                    int.from_bytes(data[pos+2:pos+4], 'little'))
                        pos += 4
                    else:
                        compression = (0, 1)
                    
                    # Clear high bit from size
                    file_size &= 0x7FFFFFFF
                    
                    print(f"Entry {i}: Type={hex(entry_type)}, Group={hex(entry_group)}, Instance={hex(entry_inst_ex << 32 | entry_inst)}")
                    print(f"  Offset={resource_offset}, Size={file_size}, Compression={compression}")
                    
                    # Skip deleted entries
                    if compression[0] == 0xFFE0:
                        continue
                    
                    entry = DBPFEntry(
                        type_id=entry_type,
                        group_id=entry_group,
                        instance_id=entry_inst_ex << 32 | entry_inst,
                        offset=resource_offset,
                        size=file_size
                    )
                    
                    self.entries.append(entry)
                    
                    # If this is a string table, try to load it
                    if entry_type == self.STBL_TYPE:
                        try:
                            # Get the raw data for this entry
                            stbl_data = data[resource_offset:resource_offset+file_size]
                            
                            # Handle compression
                            if compression[0] == 0:  # No compression
                                pass
                            elif compression[0] == 0x5A42:  # zlib
                                import zlib
                                stbl_data = zlib.decompress(stbl_data, 15, decompressed_size)
                            elif compression[0] == 0xFFFE:  # RefPack
                                # TODO: Implement RefPack decompression
                                print(f"Warning: RefPack compression not supported yet")
                                continue
                            elif compression[0] == 0xFFFF:  # RefPack
                                # TODO: Implement RefPack decompression
                                print(f"Warning: RefPack compression not supported yet")
                                continue
                            else:
                                print(f"Warning: Unknown compression type {compression}")
                                continue
                            
                            stbl = StringTableFile()
                            if stbl.load_from_binary(stbl_data):
                                self.string_tables[entry.instance_id] = stbl
                                print(f"Successfully loaded STBL with {len(stbl.strings)} strings")
                            else:
                                print(f"Failed to load STBL at offset {resource_offset}")
                                
                        except Exception as e:
                            print(f"Error loading STBL at offset {resource_offset}: {e}")
                            continue
                            
                except Exception as e:
                    print(f"Error reading index entry {i}: {e}")
                    continue
            
            if not self.string_tables:
                print("No string tables found in package")
            else:
                print(f"Successfully loaded {len(self.string_tables)} string tables")
                
            return len(self.string_tables) > 0
            
        except Exception as e:
            print(f"Error loading DBPF: {e}")
            import traceback
            traceback.print_exc()
            return False
            
    def save_to_binary(self, original_data: bytes) -> bytes:
        try:
            # Start with the original data
            data = bytearray(original_data)
            
            # Find the end of the original data
            end_offset = len(data)
            
            # Track which entries we need to update in the index
            updated_entries = {}
            
            # First pass: Save all modified STBL entries to the end of the file
            for entry in self.entries:
                if entry.type_id == self.STBL_TYPE and entry.instance_id in self.string_tables:
                    stbl = self.string_tables[entry.instance_id]
                    stbl_data = stbl.save_to_binary()
                    
                    # Store the new offset and size
                    updated_entries[entry.instance_id] = (end_offset, len(stbl_data))
                    
                    # Append the STBL data to the end
                    data.extend(stbl_data)
                    end_offset += len(stbl_data)
            
            # Second pass: Update the index entries
            if updated_entries:
                index_pos = self.header.index_offset
                flags = int.from_bytes(data[index_pos:index_pos+4], 'little')
                pos = index_pos + 4
                
                # Handle constant values based on flags
                const_type = bool(flags & 1)
                const_group = bool(flags & 2)
                const_instance_ex = bool(flags & 4)
                
                if const_type:
                    pos += 4
                if const_group:
                    pos += 4
                if const_instance_ex:
                    pos += 4
                
                # Update each index entry
                for i in range(self.header.index_count):
                    # Skip type if not constant
                    if not const_type:
                        pos += 4
                    
                    # Skip group if not constant
                    if not const_group:
                        pos += 4
                    
                    # Read instance ID
                    if not const_instance_ex:
                        inst_ex = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    else:
                        inst_ex = int.from_bytes(data[index_pos+4:index_pos+8], 'little')
                    
                    inst = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    instance_id = inst_ex << 32 | inst
                    
                    # If this entry was updated, update its offset and size
                    if instance_id in updated_entries:
                        new_offset, new_size = updated_entries[instance_id]
                        # Update offset
                        data[pos:pos+4] = new_offset.to_bytes(4, 'little')
                        # Update size (no compression flag)
                        data[pos+4:pos+8] = new_size.to_bytes(4, 'little')
                        # Update decompressed size
                        data[pos+8:pos+12] = new_size.to_bytes(4, 'little')
                    
                    # Skip to next entry
                    pos += 12  # Skip offset, size, and decompressed size
                    
                    # Skip compression data if present
                    if int.from_bytes(data[pos-8:pos-4], 'little') & 0x80000000:
                        pos += 4
            
            return bytes(data)
            
        except Exception as e:
            print(f"Error saving DBPF: {e}")
            import traceback
            traceback.print_exc()
            return b''

@dataclass
class StringTableEntry:
    key: int
    value: str
    flags: int = 0

class StringTableFile:
    def __init__(self):
        self.strings: Dict[int, StringTableEntry] = {}
        self.version: int = 5
        self.language: int = 0
        
    def load_from_binary(self, data: bytes) -> bool:
        try:
            # Check for minimum size
            if len(data) < 20:  # Basic header size
                print("Data too small for STBL")
                return False
                
            # Check magic number
            if not data.startswith(b'STBL'):
                print("Invalid STBL magic number")
                return False
                
            pos = 4  # Skip STBL magic
            
            # Read header
            self.version = int.from_bytes(data[pos:pos+2], 'little')
            print(f"STBL version: {self.version}")
            pos += 2
            
            compression = data[pos]
            print(f"Compression: {compression}")
            pos += 1
            
            num_entries = int.from_bytes(data[pos:pos+8], 'little')
            print(f"Number of entries: {num_entries}")
            pos += 8
            
            pos += 2  # Skip reserved bytes
            
            strings_length = int.from_bytes(data[pos:pos+4], 'little')
            print(f"Strings length: {strings_length}")
            pos += 4
            
            # Read string entries
            for i in range(num_entries):
                try:
                    if pos + 7 > len(data):  # Minimum entry size (key + flags + min length)
                        print(f"Data truncated at entry {i}")
                        break
                        
                    key = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    flags = data[pos]
                    pos += 1
                    
                    length = int.from_bytes(data[pos:pos+2], 'little')
                    pos += 2
                    
                    if pos + length > len(data):
                        print(f"String data truncated at entry {i}")
                        break
                        
                    try:
                        value = data[pos:pos+length].decode('utf-8')
                        pos += length
                        
                        self.strings[key] = StringTableEntry(key=key, value=value, flags=flags)
                    except UnicodeDecodeError:
                        print(f"Unicode decode error at entry {i}")
                        pos += length
                        continue
                        
                except Exception as e:
                    print(f"Error reading entry {i}: {e}")
                    continue
            
            print(f"Successfully loaded {len(self.strings)} strings")
            return len(self.strings) > 0
            
        except Exception as e:
            print(f"Error loading STBL: {e}")
            import traceback
            traceback.print_exc()
            return False
            
    def save_to_binary(self) -> bytes:
        try:
            # Calculate total strings length
            strings_length = len(self.strings)
            for entry in self.strings.values():
                strings_length += len(entry.value.encode('utf-8'))
            
            # Build header
            data = bytearray()
            data.extend(b'STBL')
            data.extend(self.version.to_bytes(2, 'little'))
            data.append(0)  # compression
            data.extend(len(self.strings).to_bytes(8, 'little'))
            data.extend(b'\x00\x00')  # reserved
            data.extend(strings_length.to_bytes(4, 'little'))
            
            # Add string entries
            for entry in self.strings.values():
                data.extend(entry.key.to_bytes(4, 'little'))
                data.append(entry.flags)
                value_bytes = entry.value.encode('utf-8')
                data.extend(len(value_bytes).to_bytes(2, 'little'))
                data.extend(value_bytes)
            
            return bytes(data)
        except Exception as e:
            print(f"Error saving STBL: {e}")
            return b''

class WorkerSignals(QObject):
    progress = Signal(int, str)
    finished = Signal()
    error = Signal(str)

class TranslateWorker(QRunnable):
    def __init__(self, texts, start_index):
        super().__init__()
        self.texts = texts
        self.start_index = start_index
        self.signals = WorkerSignals()
        
    def run(self):
        try:
            # Google Translate URL
            url = 'http://translate.google.com/m?sl=en&tl=tr&q=%s'
            ua = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36'
            
            # Combine texts with special character handling
            text_strings = []
            for text in self.texts:
                if text.strip():
                    text = text.replace("\n", r"\x0a").replace("\r", r"\x0d")
                    text_strings.append(text)
            
            # Join texts with newline
            combined_text = '\n'.join(text_strings)
            
            # Translate combined text
            link = url % urllib.parse.quote(combined_text)
            request = urllib.request.Request(link, headers={'User-Agent': ua})
            data = urllib.request.urlopen(request).read().decode('utf-8')
            expr = r'(?s)class="(?:t0|result-container)">(.*?)<'
            translated_text = html.unescape(re.findall(expr, data)[0])
            
            # Split translations
            translations = translated_text.split('\n')
            
            # Send results back
            for i, translation in enumerate(translations):
                if i < len(self.texts):
                    translation = translation.replace(r"\x0a", "\n").replace(r"\x0d", "\r")
                    self.signals.progress.emit(self.start_index + i, translation)
            
            self.signals.finished.emit()
                    
        except Exception as e:
            self.signals.error.emit(str(e))

class ModTranslator(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("The Sims 4 Mod Translator for TR | Discord: merxdo")
        self.setMinimumSize(1000, 700)
        
        # Initialize package file
        self.package_file = DBPFFile()
        self.current_file_data = None
        
        # Initialize thread pool
        self.thread_pool = QThreadPool()
        self.active_workers = 0
        
        # Setup UI
        self.setup_ui()
        
    def setup_ui(self):
        # Create central widget and main layout
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        
        # Create menu bar
        self.create_menu_bar()
        
        # Create toolbar
        self.create_toolbar()
        
        # Create search bar
        search_layout = QHBoxLayout()
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Kelime Ara")
        self.search_input.textChanged.connect(self.filter_table)
        search_layout.addWidget(self.search_input)
        
        # Add auto-translate button
        translate_btn = QPushButton("Hepsini Otomatik Çevir")
        translate_btn.setStyleSheet("""
            QPushButton {
                background-color: #FF9800;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                font-weight: bold;
            }
            QPushButton:hover {
                background-color: #F57C00;
            }
        """)
        translate_btn.clicked.connect(self.auto_translate_all)
        search_layout.addWidget(translate_btn)
        
        main_layout.addLayout(search_layout)
        
        # Create table
        self.table = QTableWidget()
        self.table.setColumnCount(3)
        self.table.setHorizontalHeaderLabels(["Anahtar", "Orijinal Dize", "Düzenlenebilir Dize"])
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(2, QHeaderView.Stretch)
        main_layout.addWidget(self.table)
        
        # Create status bar
        self.status_bar = QStatusBar()
        self.setStatusBar(self.status_bar)
        
        # Apply styling
        self.apply_styling()
        
    def auto_translate_all(self):
        try:
            # Create progress dialog
            self.progress = QProgressDialog("Dizeler çevriliyor...", "İptal", 0, self.table.rowCount(), self)
            self.progress.setWindowModality(Qt.WindowModal)
            self.progress.setWindowTitle("Otomatik Çeviri İlerlemesi")
            
            # Collect all texts to translate
            texts_to_translate = []
            self.row_indices = []
            
            for row in range(self.table.rowCount()):
                original_text = self.table.item(row, 1).text()
                if original_text.strip():
                    texts_to_translate.append(original_text)
                    self.row_indices.append(row)
            
            if not texts_to_translate:
                return
                
            # Split texts into chunks of 10 for batch processing
            chunk_size = 10
            chunks = [texts_to_translate[i:i + chunk_size] for i in range(0, len(texts_to_translate), chunk_size)]
            
            self.active_workers = len(chunks)
            
            # Process each chunk in parallel
            for i, chunk in enumerate(chunks):
                if self.progress.wasCanceled():
                    break
                    
                worker = TranslateWorker(chunk, i * chunk_size)
                worker.signals.progress.connect(self.update_translation)
                worker.signals.finished.connect(self.worker_finished)
                worker.signals.error.connect(self.worker_error)
                self.thread_pool.start(worker)
            
        except Exception as e:
            QMessageBox.critical(
                self,
                "Hata",
                f"Otomatik çeviri sırasında hata oluştu: {str(e)}"
            )
    
    @Slot(int, str)
    def update_translation(self, index, translation):
        if index < len(self.row_indices):
            row = self.row_indices[index]
            self.table.item(row, 2).setText(translation)
            self.progress.setValue(index + 1)
    
    @Slot()
    def worker_finished(self):
        self.active_workers -= 1
        if self.active_workers == 0:
            self.progress.setValue(self.table.rowCount())
            self.status_bar.showMessage("Auto-translation completed")
    
    @Slot(str)
    def worker_error(self, error_msg):
        QMessageBox.critical(
            self,
            "Hata",
            f"Çeviri hatası: {error_msg}"
        )
            
    def create_menu_bar(self):
        menubar = self.menuBar()
        
        # File menu
        file_menu = menubar.addMenu("Dosya")
        
        open_action = QAction("Aç", self)
        open_action.setShortcut("Ctrl+O")
        open_action.triggered.connect(self.open_file)
        file_menu.addAction(open_action)
        
        save_action = QAction("Kaydet", self)
        save_action.setShortcut("Ctrl+S")
        save_action.triggered.connect(self.save_file)
        file_menu.addAction(save_action)
        
        file_menu.addSeparator()
        
        exit_action = QAction("Çıkış", self)
        exit_action.setShortcut("Ctrl+Q")
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)
        
        # Edit menu
        edit_menu = menubar.addMenu("Düzenle")
        
        find_action = QAction("Bul", self)
        find_action.setShortcut("Ctrl+F")
        find_action.triggered.connect(lambda: self.search_input.setFocus())
        edit_menu.addAction(find_action)
        
        translate_action = QAction("Hepsini Otomatik Çevir", self)
        translate_action.setShortcut("Ctrl+T")
        translate_action.triggered.connect(self.auto_translate_all)
        edit_menu.addAction(translate_action)
        
    def create_toolbar(self):
        toolbar = QToolBar()
        toolbar.setIconSize(QSize(24, 24))
        self.addToolBar(toolbar)
        
        # Open button
        open_btn = QPushButton("Dosya Aç")
        open_btn.setStyleSheet("""
            QPushButton {
                background-color: #4CAF50;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                font-weight: bold;
            }
            QPushButton:hover {
                background-color: #45a049;
            }
        """)
        open_btn.clicked.connect(self.open_file)
        toolbar.addWidget(open_btn)
        
        # Save button
        save_btn = QPushButton("Kaydet")
        save_btn.setStyleSheet("""
            QPushButton {
                background-color: #008CBA;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                font-weight: bold;
            }
            QPushButton:hover {
                background-color: #007399;
            }
        """)
        save_btn.clicked.connect(self.save_file)
        toolbar.addWidget(save_btn)
        
    def apply_styling(self):
        self.setStyleSheet("""
            QMainWindow {
                background-color: #f5f5f5;
            }
            QTableWidget {
                background-color: white;
                border: 1px solid #ddd;
                border-radius: 4px;
                color: #333333;
                gridline-color: #e0e0e0;
            }
            QHeaderView::section {
                background-color: #2196F3;
                color: white;
                padding: 8px;
                border: none;
                font-weight: bold;
            }
            QTableWidget::item {
                color: #333333;
                padding: 8px;
            }
            QTableWidget::item:selected {
                background-color: #e3f2fd;
                color: #1976D2;
            }
            QLineEdit {
                padding: 8px;
                border: 1px solid #ddd;
                border-radius: 4px;
                background-color: white;
                color: #333333;
            }
            QLineEdit:focus {
                border-color: #2196F3;
            }
            QStatusBar {
                background-color: #f5f5f5;
                color: #666666;
            }
            QMenuBar {
                background-color: #000000;
                border-bottom: 1px solid #ddd;
            }
            QMenuBar::item:selected {
                background-color: #e3f2fd;
                color: #1976D2;
            }
            QMenu {
                background-color: black;
                border: 1px solid #ddd;
            }
            QMenu::item:selected {
                background-color: #e3f2fd;
                color: #1976D2;
            }
        """)
        
    def open_file(self):
        file_name, _ = QFileDialog.getOpenFileName(
            self,
            "Dosyayı Aç",
            "",
            "Package Dosyaları (*.package);;STBL Dosyaları (*.stbl);;Tüm dosyalar (*.*)"
        )
        
        if not file_name:
            return
            
        try:
            with open(file_name, 'rb') as file:
                data = file.read()
                self.current_file_data = data
                
            if file_name.lower().endswith('.package'):
                # Load package file
                if self.package_file.load_from_binary(data):
                    # Get the first string table for now (we can add table selection later)
                    if self.package_file.string_tables:
                        first_stbl = next(iter(self.package_file.string_tables.values()))
                        self.string_table = first_stbl
                        self.populate_table()
                        self.status_bar.showMessage(
                            f"Loaded {len(self.string_table.strings)} strings from {os.path.basename(file_name)}"
                        )
                    else:
                        QMessageBox.warning(self, "Uyarı", "Paket dosyasında dize tablosu bulunamadı")
                else:
                    QMessageBox.critical(self, "Hata", "Geçersiz paket dosya biçimi")
            else:
                # Load STBL file directly
                if self.string_table.load_from_binary(data):
                    self.populate_table()
                    self.status_bar.showMessage(
                        f"Loaded {len(self.string_table.strings)} strings from {os.path.basename(file_name)}"
                    )
                else:
                    QMessageBox.critical(self, "Hata", "Geçersiz STBL dosya biçimi")
                    
        except Exception as e:
            QMessageBox.critical(self, "Hata", f"Dosya açılırken hata oluştu: {str(e)}")
                
    def save_file(self):
        file_name, _ = QFileDialog.getSaveFileName(
            self,
            "Dosyayı Kaydet",
            "",
            "Package Dosyaları (*.package);;STBL Dosyaları (*.stbl);;Tüm Dosyalar (*.*)"
        )
        
        if not file_name:
            return
            
        try:
            # Update string table from UI
            for row in range(self.table.rowCount()):
                key = int(self.table.item(row, 0).text())
                translation = self.table.item(row, 2).text()
                if key in self.string_table.strings:
                    self.string_table.strings[key].value = translation
            
            # Save file
            if file_name.lower().endswith('.package') and self.current_file_data:
                # Update the string table in package_file before saving
                for instance_id, stbl in self.package_file.string_tables.items():
                    if stbl is self.string_table:  # Find the currently edited string table
                        self.package_file.string_tables[instance_id] = self.string_table
                        break
                
                # Save as package file
                data = self.package_file.save_to_binary(self.current_file_data)
                if data:
                    with open(file_name, 'wb') as file:
                        file.write(data)
                    self.status_bar.showMessage(f"Paket dosyası kaydedildi {os.path.basename(file_name)}")
                else:
                    QMessageBox.critical(self, "Hata", "Paket dosyası oluşturulurken hata oluştu")
            else:
                # Save as STBL file
                data = self.string_table.save_to_binary()
                if data:
                    with open(file_name, 'wb') as file:
                        file.write(data)
                    self.status_bar.showMessage(f"{len(self.string_table.strings)} dizesi {os.path.basename(file_name)} dizinine kaydedildi")
                else:
                    QMessageBox.critical(self, "Hata", "STBL dosyası oluşturulurken hata oluştu")
                    
        except Exception as e:
            QMessageBox.critical(self, "Hata", f"Dosya kaydedilirken hata oluştu: {str(e)}")
                
    def populate_table(self):
        self.table.setRowCount(0)
        
        for entry in self.string_table.strings.values():
            row = self.table.rowCount()
            self.table.insertRow(row)
            
            # Key
            key_item = QTableWidgetItem(str(entry.key))
            key_item.setFlags(key_item.flags() & ~Qt.ItemIsEditable)
            self.table.setItem(row, 0, key_item)
            
            # Original string
            original_item = QTableWidgetItem(entry.value)
            original_item.setFlags(original_item.flags() & ~Qt.ItemIsEditable)
            self.table.setItem(row, 1, original_item)
            
            # Translation
            translation_item = QTableWidgetItem(entry.value)
            self.table.setItem(row, 2, translation_item)
            
    def filter_table(self, text):
        for row in range(self.table.rowCount()):
            show_row = False
            for col in range(1, 3):  # Search in Original String and Translation columns
                item = self.table.item(row, col)
                if item and text.lower() in item.text().lower():
                    show_row = True
                    break
            self.table.setRowHidden(row, not show_row)

if __name__ == '__main__':
    app = QApplication(sys.argv)
    
    # Set application style
    app.setStyle('Fusion')
    
    # Set default font
    font = QFont("Segoe UI", 9)
    app.setFont(font)
    
    # Create and show window
    window = ModTranslator()
    window.show()
    
    sys.exit(app.exec()) 
