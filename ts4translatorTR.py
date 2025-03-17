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
                             QInputDialog, QFrame, QSplitter, QDialog, QGroupBox, QTextEdit,
                             QRadioButton, QProgressBar)
from PySide6.QtCore import Qt, QSize, QThread, Signal, QThreadPool, QRunnable, QObject, Slot, QSettings
from PySide6.QtGui import QFont, QIcon, QColor, QAction, QPalette, QFontDatabase, QIntValidator
import urllib.request
import urllib.parse
import re
import html.parser

# DeepL modülünü koşullu olarak import et
try:
    import deepl
    DEEPL_AVAILABLE = True
except ImportError:
    DEEPL_AVAILABLE = False

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
    
def decode_ref_pack(ibuf):
    if ibuf[1] != 0xFB:
        raise Exception('Invalid compressed data')

    iptr = 2
    optr = 0
    flags = ibuf[0]
    osize = 0

    for _ in range(4 if flags & 0x80 else 3):
        osize = (osize << 8) | ibuf[iptr]
        iptr += 1

    obuf = bytearray(osize)
    while iptr < len(ibuf):
        copy_offset = 0
        cc0 = ibuf[iptr]
        iptr += 1
        if cc0 <= 0x7F:
            cc1 = ibuf[iptr]
            iptr += 1
            _cc = (cc0, cc1)
            num_plaintext = cc0 & 0x03
            num_to_copy = ((cc0 & 0x1C) >> 2) + 3
            copy_offset = ((cc0 & 0x60) << 3) + cc1
        elif cc0 <= 0xBF:
            cc1 = ibuf[iptr]
            iptr += 1
            cc2 = ibuf[iptr]
            iptr += 2
            _cc = (cc0, cc1, cc2)
            num_plaintext = (cc1 & 0xC0) >> 6
            num_to_copy = (cc0 & 0x3F) + 4
            copy_offset = ((cc1 & 0x3F) << 8) + cc2
        elif cc0 <= 0xDF:
            cc1 = ibuf[iptr]
            iptr += 1
            cc2 = ibuf[iptr]
            iptr += 1
            cc3 = ibuf[iptr]
            iptr += 1
            _cc = (cc0, cc1, cc2, cc3)
            num_plaintext = cc0 & 0x03
            num_to_copy = ((cc0 & 0x0C) << 6) + cc3 + 5
            copy_offset = ((cc0 & 0x10) << 12) + (cc1 << 8) + cc2
        elif cc0 <= 0xFB:
            _cc = (cc0,)
            num_plaintext = ((cc0 & 0x1F) << 2) + 4
            num_to_copy = 0
        else:
            _cc = (cc0,)
            num_plaintext = cc0 & 3
            num_to_copy = 0

        obuf[optr:optr + num_plaintext] = ibuf[iptr:iptr + num_plaintext]
        iptr += num_plaintext
        optr += num_plaintext

        for _ in range(num_to_copy):
            obuf[optr] = obuf[optr - 1 - copy_offset]
            optr += 1

    return bytes(obuf)

class DBPFFile:
    STBL_TYPE = 0x220557DA  # Dize tablo türü kimliği
    
    def __init__(self):
        self.header: Optional[DBPFHeader] = None
        self.entries: List[DBPFEntry] = []
        self.string_tables: Dict[int, StringTableFile] = {}  # instance_id -> StringTableFile
        
    def load_from_binary(self, data: bytes) -> bool:
        try:
            if len(data) < 96:  # Minimum başlık boyutu
                print("Data too small for DBPF")
                return False
                
            if not data.startswith(b'DBPF'):
                print("Not a DBPF file")
                return False
                
            pos = 4  # DBPF büyüsünü atla
            
            # Dosya sürümünü oku (2,1 olmalı)
            file_version = (int.from_bytes(data[pos:pos+4], 'little'),
                          int.from_bytes(data[pos+4:pos+8], 'little'))
            if file_version != (2, 1):
                print(f"Unsupported DBPF version: {file_version}")
                return False
            pos += 8
            
            # Kullanıcı sürümünü oku (0,0 olmalı)
            user_version = (int.from_bytes(data[pos:pos+4], 'little'),
                          int.from_bytes(data[pos+4:pos+8], 'little'))
            if user_version != (0, 0):
                print(f"Unsupported user version: {user_version}")
                return False
            pos += 8
            
            # Kullanılmayanları atla
            pos += 4
            
            # Zaman damgalarını oku
            creation_time = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            updated_time = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Kullanılmayanları atla
            pos += 4
            
            # Dizin bilgilerini oku
            index_count = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            index_offset_low = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            index_size = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Yüksek ofsete geç
            pos += 16
            index_offset_high = int.from_bytes(data[pos:pos+4], 'little')
            
            # Mümkünse yüksek ofset kullan
            index_offset = index_offset_high if index_offset_high != 0 else index_offset_low
            
            print(f"DBPF Version: {file_version}")
            print(f"User Version: {user_version}")
            print(f"Creation Time: {creation_time}, Updated Time: {updated_time}")
            print(f"Index Count: {index_count}, Offset: {index_offset}, Size: {index_size}")
            
            if index_offset == 0:
                if index_count != 0:
                    print("Warning: Package contains entries but no index")
                return False
            
            # Başlık bilgisi
            self.header = DBPFHeader(
                version=file_version[0],
                index_major_version=user_version[0],
                index_count=index_count,
                index_offset=index_offset,
                index_size=index_size
            )
            
            # Dizin girişlerini oku
            pos = index_offset
            flags = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Bayraklara dayalı sabit değerleri işle
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
                    # Sabit değilse tür kimliğini oku
                    if not const_type:
                        entry_type = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    
                    # Sabit değilse grup kimliğini oku
                    if not const_group:
                        entry_group = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    
                    # Sabit değilse örnek yüksek bitleri oku
                    if not const_instance_ex:
                        entry_inst_ex = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    else:
                        entry_inst_ex = int.from_bytes(data[index_pos+4:index_pos+8], 'little')
                    
                    # Düşük bitleri oku
                    entry_inst = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Kaynak ofsetini ve boyutunu oku
                    resource_offset = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    file_size = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Sıkıştırılmış boyutu oku
                    decompressed_size = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Sıkıştırmayı ele al
                    if file_size & 0x80000000:
                        compression = (int.from_bytes(data[pos:pos+2], 'little'),
                                    int.from_bytes(data[pos+2:pos+4], 'little'))
                        pos += 4
                    else:
                        compression = (0, 1)
                    
                    # Boyuttan yüksek biti temizle
                    file_size &= 0x7FFFFFFF
                    
                    print(f"Entry {i}: Type={hex(entry_type)}, Group={hex(entry_group)}, Instance={hex(entry_inst_ex << 32 | entry_inst)}")
                    print(f"  Offset={resource_offset}, Size={file_size}, Compression={compression}")
                    
                    # Silinen girdileri atla
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
                    
                    # Eğer bu bir dize tablosuysa yüklemeyi dene
                    if entry_type == self.STBL_TYPE:
                        try:
                            # Bu giriş için verileri al
                            stbl_data = data[resource_offset:resource_offset+file_size]
                            
                            # Sıkıştırmayı ele al
                            if compression[0] == 0:  # Sıkıştırma yok
                                pass
                            elif compression[0] == 0x5A42:  # zlib
                                import zlib
                                stbl_data = zlib.decompress(stbl_data, 15, decompressed_size)
                            elif compression[0] == 0xFFFE:  # RefPack
                                stbl_data = decode_ref_pack(stbl_data)
                            elif compression[0] == 0xFFFF:  # RefPack
                                stbl_data = decode_ref_pack(stbl_data)
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
            # Orijinal veriyi kopyala
            data = bytearray(original_data)
            
            # Güncellenecek girişleri takip et
            updated_entries = {}
            
            # İlk geçiş: Tüm değiştirilmiş STBL girişlerini kaydet
            for entry in self.entries:
                if entry.type_id == self.STBL_TYPE and entry.instance_id in self.string_tables:
                    stbl = self.string_tables[entry.instance_id]
                    stbl_data = stbl.save_to_binary()
                    
                    # zlib sıkıştırması uygula
                    import zlib
                    compressed_data = zlib.compress(stbl_data)
                    
                    # Yeni veriyi dosyanın sonuna ekle
                    new_offset = len(data)
                    data.extend(compressed_data)
                    
                    # Sıkıştırma bayrağını ayarla ve boyutları kaydet
                    new_size = len(compressed_data)
                    decompressed_size = len(stbl_data)
                    
                    # Güncellenecek girişi kaydet
                    updated_entries[entry.instance_id] = (new_offset, new_size, decompressed_size)
            
            # İkinci geçiş: İndeks girişlerini güncelle
            if updated_entries:
                index_pos = self.header.index_offset
                flags = int.from_bytes(data[index_pos:index_pos+4], 'little')
                pos = index_pos + 4
                
                # Sabit değerleri kontrol et
                const_type = bool(flags & 1)
                const_group = bool(flags & 2)
                const_instance_ex = bool(flags & 4)
                
                if const_type:
                    pos += 4
                if const_group:
                    pos += 4
                if const_instance_ex:
                    pos += 4
                
                # Her indeks girişini güncelle
                for i in range(self.header.index_count):
                    # Sabit olmayan tip ve grup alanlarını atla
                    if not const_type:
                        pos += 4
                    if not const_group:
                        pos += 4
                    
                    # Instance ID'yi oku
                    if not const_instance_ex:
                        inst_ex = int.from_bytes(data[pos:pos+4], 'little')
                        pos += 4
                    else:
                        inst_ex = int.from_bytes(data[index_pos+4:index_pos+8], 'little')
                    
                    inst = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    instance_id = inst_ex << 32 | inst
                    
                    # Eğer bu giriş güncellendiyse, offset ve boyut bilgilerini güncelle
                    if instance_id in updated_entries:
                        new_offset, new_size, decompressed_size = updated_entries[instance_id]
                        
                        # Offset'i güncelle
                        data[pos:pos+4] = new_offset.to_bytes(4, 'little')
                        
                        # Boyutu güncelle (sıkıştırma bayrağı ile)
                        data[pos+4:pos+8] = (new_size | 0x80000000).to_bytes(4, 'little')
                        
                        # Sıkıştırılmamış boyutu güncelle
                        data[pos+8:pos+12] = decompressed_size.to_bytes(4, 'little')
                        
                        # Sıkıştırma tipini ayarla (zlib)
                        data[pos+12:pos+14] = (0x5A42).to_bytes(2, 'little')  # zlib
                        data[pos+14:pos+16] = (1).to_bytes(2, 'little')  # alt tip
                        
                        pos += 16  # Sonraki girişe geç
                    else:
                        # Değiştirilmemiş girişleri atla
                        pos += 12  # offset, size, decompressed_size
                        # Sıkıştırma bilgisi varsa atla
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

    def get_formatted_value(self) -> str:
        # Referans projedeki gibi basit ve etkili string formatlama
        if self.value:
            # Sadece \r ve \n karakterlerini düzelt, diğer tüm karakterleri olduğu gibi bırak
            return self.value.replace("\r", "").replace("\n", "\\n")
        return ""

class StringTableFile:
    def __init__(self):
        self.strings: Dict[int, StringTableEntry] = {}
        self.version: int = 5
        self.language: int = 0
        
    def load_from_binary(self, data: bytes) -> bool:
        try:
            if len(data) < 20:
                print("Data too small for STBL")
                return False
                
            if not data.startswith(b'STBL'):
                print("Invalid STBL magic number")
                return False
                
            pos = 4
            
            # Sürümü oku (5 olmalı)
            version = int.from_bytes(data[pos:pos+2], 'little')
            if version != 5:
                print(f"Unsupported STBL version: {version}")
                return False
            pos += 2
            
            # Sıkıştırma bayrağını oku
            compressed = data[pos]
            pos += 1
            
            # Girişlerin okunma sayısı
            num_entries = int.from_bytes(data[pos:pos+8], 'little')
            pos += 8
            
            # Ayrılmış baytları atla
            pos += 2
            
            # Dizelerin uzunluğunu oku
            strings_length = int.from_bytes(data[pos:pos+4], 'little')
            pos += 4
            
            # Tüm dize girişlerini oku
            for _ in range(num_entries):
                try:
                    # Anahtarı oku
                    key = int.from_bytes(data[pos:pos+4], 'little')
                    pos += 4
                    
                    # Bayrakları oku
                    flags = data[pos]
                    pos += 1
                    
                    # Dize uzunluğunu oku
                    length = int.from_bytes(data[pos:pos+2], 'little')
                    pos += 2
                    
                    # Dize değerini oku ve UTF-8 olarak kodla
                    try:
                        # String'i direkt olarak UTF-8 ile decode et
                        value = data[pos:pos+length].decode('utf-8', errors='replace')
                        pos += length
                        
                        # Dizeyi sakla
                        self.strings[key] = StringTableEntry(key=key, value=value, flags=flags)
                    except UnicodeError as e:
                        print(f"Error decoding string at position {pos}: {e}")
                        pos += length
                        continue
                    
                except Exception as e:
                    print(f"Error reading string entry: {e}")
                    continue
                    
            return True
            
        except Exception as e:
            print(f"Error loading STBL: {e}")
            return False
            
    def save_to_binary(self) -> bytes:
        try:
            # Toplam string sayısı
            num_entries = len(self.strings)
            
            # Çıktı buffer'ını oluştur
            data = bytearray()
            
            # STBL başlığını yaz
            data.extend(b'STBL')
            data.extend((5).to_bytes(2, 'little'))  # Versiyon
            data.append(0)  # Sıkıştırma bayrağı
            data.extend(num_entries.to_bytes(8, 'little'))  # Giriş sayısı
            data.extend((0).to_bytes(2, 'little'))  # Rezerve
            
            # String uzunluklarını hesapla
            strings_length = 0
            for entry in self.strings.values():
                formatted_value = entry.get_formatted_value()
                if formatted_value:  # Boş string kontrolü
                    strings_length += len(formatted_value.encode('utf-8')) + 7  # 4 (key) + 1 (flag) + 2 (length)
                else:
                    strings_length += 7  # 4 (key) + 1 (flag) + 2 (length)
            
            # Toplam string uzunluğunu yaz
            data.extend(strings_length.to_bytes(4, 'little'))
            
            # Stringleri sıralı şekilde yaz
            for key in sorted(self.strings.keys()):
                entry = self.strings[key]
                
                # Anahtarı yaz
                data.extend(key.to_bytes(4, 'little'))
                
                # Flag'i yaz
                data.append(entry.flags)
                
                # Diziyi formatla ve yaz
                formatted_value = entry.get_formatted_value()
                if formatted_value:
                    string_bytes = formatted_value.encode('utf-8')
                    # String uzunluğunu yaz
                    data.extend(len(string_bytes).to_bytes(2, 'little'))
                    # Dizinin kendisini yaz
                    data.extend(string_bytes)
                else:
                    # Boş string için 0 uzunluk
                    data.extend((0).to_bytes(2, 'little'))
            
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
        self.translation_speed = 500  # Varsayılan hız (ms)
        
    def preprocess_text(self, text):
        """Çeviri öncesi metni hazırla"""
        # Oyun değerlerini koru
        game_values = []
        def save_game_value(match):
            game_values.append(match.group(0))
            return f"GAMEVALUE{len(game_values)-1}"
        
        # Oyun değerlerini geçici olarak kaldır
        text = re.sub(r'{[^{}]*}(?:\'s)?', save_game_value, text)
        
        # İngilizce kalıpları daha iyi çevrilebilir formata dönüştür
        replacements = {
            r'^Seems like\b': "It seems that",
            r'\bMaybe\b': "Perhaps",
            r'\bshould try\b': "needs to try",
            r'\bis not\b': "does not",
            r'\bcan\'t\b': "cannot",
            r'\bdon\'t\b': "do not",
            r'\bwon\'t\b': "will not",
            r'\bdidn\'t\b': "did not",
            r'\bhasn\'t\b': "has not",
            r'\bhaven\'t\b': "have not",
            r'\bwasn\'t\b': "was not",
            r'\baren\'t\b': "are not",
            r'\bweren\'t\b': "were not",
            r'\bisn\'t\b': "is not",
            r'\bgoing to\b': "will",
            r'\bwanna\b': "want to",
            r'\bgonna\b': "going to",
            r'\bgotta\b': "got to",
            r'\bkinda\b': "kind of",
            r'\bsorta\b': "sort of",
            r'\bcause\b': "because",
            r'\btil\b': "until",
            r'\btill\b': "until",
            r'\by\'all\b': "you all",
            r'\bain\'t\b': "is not"
        }
        
        for pattern, replacement in replacements.items():
            text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
        
        # Oyun değerlerini geri koy
        for i, value in enumerate(game_values):
            text = text.replace(f"GAMEVALUE{i}", value)
            
        return text
        
    def postprocess_translation(self, text):
        """Çeviri sonrası metni düzelt"""
        # Gereksiz boşlukları temizle
        text = re.sub(r'\s+', ' ', text).strip()
        
        # Noktalama işaretlerinden önceki boşlukları kaldır
        text = re.sub(r'\s+([.,!?])', r'\1', text)
        
        # Yaygın çeviri hatalarını düzelt
        replacements = {
            r'\bgibi görünüyor\b': "görünüyor",
            r'\byapmak gerekiyor\b': "gerekiyor",
            r'\byapmam gerek\b': "gerekiyor",
            r'\byapmak gerek\b': "gerekiyor",
            r'\byapmak lazım\b': "gerekiyor",
            r'\byapmak gerekir\b': "gerekiyor",
            r'\byapmak zorunda\b': "gerekiyor",
            r'\byapmak durumunda\b': "gerekiyor",
            r'\byapmak mecburiyetinde\b': "gerekiyor",
            r'\byapmak şart\b': "gerekiyor",
            r'\byapmak icap eder\b': "gerekiyor",
            r'\byapmak icap ediyor\b': "gerekiyor",
            r'\byapmak gerekli\b': "gerekiyor",
            r'\byapmak zorunlu\b': "gerekiyor",
            r'\byapmak şarttır\b': "gerekiyor",
            r'\byapmak gereklidir\b': "gerekiyor",
            r'\byapmak zorunludur\b': "gerekiyor",
            r'\byapmak mecburidir\b': "gerekiyor",
            r'\byapmak lazımdır\b': "gerekiyor",
            r'\byapmak icap eder\b': "gerekiyor",
            r'\byapmak icap etmektedir\b': "gerekiyor",
            r'\byapmak durumundadır\b': "gerekiyor",
            r'\byapmak zorundadır\b': "gerekiyor",
            r'\byapmak mecburiyetindedir\b': "gerekiyor",
            r'\byapmak şarttır\b': "gerekiyor",
            r'\byapmak gerekir\b': "gerekiyor"
        }
        
        for pattern, replacement in replacements.items():
            text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
        
        # Cümle başlarını büyük harf yap
        text = '. '.join(s[0].upper() + s[1:] if s else '' for s in text.split('. '))
        
        return text
        
    def run(self):
        try:
            settings = QSettings("TS4ModTranslator", "Settings")
            service = settings.value("translation_service", "google")

            if service == "deepl" and DEEPL_AVAILABLE:
                api_key = settings.value("deepl_api_key", "")
                if not api_key:
                    self.signals.error.emit("DeepL API Key bulunamadı. Lütfen ayarlardan API Key'inizi girin.")
                    return

                try:
                    translator = deepl.Translator(api_key)
                    # Her metni ayrı ayrı işle
                    for i, text in enumerate(self.texts):
                        if text.strip():
                            # Oyun değerlerini bul
                            segments = []
                            last_end = 0
                            
                            # Sadece oyun değerlerini bul
                            for match in re.finditer(r'{[^{}]*}(?:\'s)?', text):
                                start, end = match.span()
                                
                                # Önceki normal metni ekle (eğer varsa)
                                if start > last_end:
                                    prev_text = text[last_end:start]
                                    # Metni ön işle
                                    prev_text = self.preprocess_text(prev_text)
                                    segments.append(('text', prev_text))
                                
                                matched_text = match.group()
                                if matched_text.endswith("'s"):  # Oyun değeri + 's
                                    game_value = matched_text[:-2]  # 's kısmını çıkar
                                    segments.append(('game', game_value))
                                    segments.append(('apostrophe', "'nin"))  # Türkçe iyelik eki
                                else:  # Sadece oyun değeri
                                    segments.append(('game', matched_text))
                                
                                last_end = end
                            
                            # Son normal metni ekle (eğer varsa)
                            if last_end < len(text):
                                final_text = text[last_end:]
                                # Metni ön işle
                                final_text = self.preprocess_text(final_text)
                                segments.append(('text', final_text))
                            
                            # Segmentleri çevir ve birleştir
                            translated_segments = []
                            for type, segment in segments:
                                if type == 'text' and segment.strip():
                                    # Boşlukları koru
                                    leading_spaces = len(segment) - len(segment.lstrip())
                                    trailing_spaces = len(segment) - len(segment.rstrip())
                                    
                                    # Çevrilecek metni hazırla
                                    to_translate = segment.strip()
                                    
                                    # Metni çevir
                                    result = translator.translate_text(to_translate, target_lang="TR")
                                    translated = result.text
                                    
                                    # Çeviri son işle
                                    translated = self.postprocess_translation(translated)
                                    
                                    # Boşlukları geri ekle
                                    translated = ' ' * leading_spaces + translated + ' ' * trailing_spaces
                                    translated_segments.append(translated)
                                elif type == 'game':
                                    # Oyun değerlerini olduğu gibi koru
                                    translated_segments.append(segment)
                                elif type == 'apostrophe':
                                    # Kesme işaretli ekleri olduğu gibi koru
                                    translated_segments.append(segment)
                            
                            # Tüm segmentleri birleştir
                            translated = ''.join(translated_segments)
                            # Son bir kez tüm metni son işle
                            translated = self.postprocess_translation(translated)
                            self.signals.progress.emit(self.start_index + i, translated)
                            
                            # Çeviri hızına bağlı olarak çeviriler arasında gecikme ekle
                            if i < len(self.texts) - 1:  # Son maddeden sonra gecikme
                                QThread.msleep(self.translation_speed)
                except Exception as e:
                    self.signals.error.emit(f"DeepL çeviri hatası: {str(e)}")
                    return
            else:
                # DeepL seçili ama kullanılamıyorsa uyarı ver
                if service == "deepl" and not DEEPL_AVAILABLE:
                    self.signals.error.emit("DeepL modülü yüklü değil. Google Translate kullanılıyor.")
                
                # Google Translate kullan
                url = 'http://translate.google.com/m?sl=auto&tl=tr&q=%s'
                ua = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36'
                
                # Her metni ayrı ayrı işle
                for i, text in enumerate(self.texts):
                    if text.strip():
                        # Oyun değerlerini bul
                        segments = []
                        last_end = 0
                        
                        # Sadece oyun değerlerini bul
                        for match in re.finditer(r'{[^{}]*}(?:\'s)?', text):
                            start, end = match.span()
                            
                            # Önceki normal metni ekle (eğer varsa)
                            if start > last_end:
                                prev_text = text[last_end:start]
                                # Metni ön işleme
                                prev_text = self.preprocess_text(prev_text)
                                segments.append(('text', prev_text))
                            
                            matched_text = match.group()
                            if matched_text.endswith("'s"):  # Oyun değeri + 's
                                game_value = matched_text[:-2]  # 's kısmını çıkar
                                segments.append(('game', game_value))
                                segments.append(('apostrophe', "'nin"))  # Türkçe iyelik eki
                            else:  # Sadece oyun değeri
                                segments.append(('game', matched_text))
                            
                            last_end = end
                        
                        # Son normal metni ekle (eğer varsa)
                        if last_end < len(text):
                            final_text = text[last_end:]
                            # Metni ön işle
                            final_text = self.preprocess_text(final_text)
                            segments.append(('text', final_text))
                        
                        # Segmentleri çevir ve birleştir
                        translated_segments = []
                        for type, segment in segments:
                            if type == 'text' and segment.strip():
                                # Boşlukları koru
                                leading_spaces = len(segment) - len(segment.lstrip())
                                trailing_spaces = len(segment) - len(segment.rstrip())
                                
                                # Çevrilecek metni hazırla
                                to_translate = segment.strip()
                                
                                # Satır sonlarını koru
                                to_translate = to_translate.replace("\n", r"\x0a").replace("\r", r"\x0d")
                                
                                # Metni çevir
                                link = url % urllib.parse.quote(to_translate)
                                request = urllib.request.Request(link, headers={'User-Agent': ua})
                                data = urllib.request.urlopen(request).read().decode('utf-8')
                                expr = r'(?s)class="(?:t0|result-container)">(.*?)<'
                                translated = html.unescape(re.findall(expr, data)[0])
                                
                                # Satır sonlarını geri getir
                                translated = translated.replace(r"\x0a", "\n").replace(r"\x0d", "\r")
                                
                                # Çeviriyi son işle
                                translated = self.postprocess_translation(translated)
                                
                                # Boşlukları geri ekle
                                translated = ' ' * leading_spaces + translated + ' ' * trailing_spaces
                                translated_segments.append(translated)
                            elif type == 'game':
                                # Oyun değerlerini olduğu gibi koru
                                translated_segments.append(segment)
                            elif type == 'apostrophe':
                                # Kesme işaretli ekleri olduğu gibi koru
                                translated_segments.append(segment)
                        
                        # Tüm segmentleri birleştir
                        translated = ''.join(translated_segments)
                        # Son bir kez tüm metni son işle
                        translated = self.postprocess_translation(translated)
                        self.signals.progress.emit(self.start_index + i, translated)
                        
                        # Çeviri hızına bağlı olarak çeviriler arasında gecikme ekle
                        if i < len(self.texts) - 1:  # Son maddeden sonra gecikme
                            QThread.msleep(self.translation_speed)
            
            self.signals.finished.emit()
                    
        except Exception as e:
            self.signals.error.emit(str(e))

class EditDialog(QDialog):
    def __init__(self, original_text, editable_text, parent=None):
        super().__init__(parent)
        # Vurgulama için bayrak - en başta tanımlanmalı
        self.is_highlighting = False
        
        self.setWindowTitle("Dize Düzenle")
        self.setMinimumSize(800, 400)
        
        # Ana layout
        layout = QVBoxLayout(self)
        
        # Üst kısım - metin alanları
        texts_layout = QHBoxLayout()
        
        # Sol taraf - Orijinal metin
        original_group = QGroupBox("Orijinal Metin")
        original_layout = QVBoxLayout(original_group)
        self.original_text = QTextEdit()
        self.original_text.setPlainText(original_text)
        self.original_text.setReadOnly(True)
        self.highlight_game_values(self.original_text)
        self.original_text.setStyleSheet("""
            QTextEdit {
                background-color: #1E1E1E;
                color: #FFFFFF;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                padding: 8px;
                font-size: 13px;
            }
        """)
        original_layout.addWidget(self.original_text)
        texts_layout.addWidget(original_group)
        
        # Sağ taraf - Düzenlenebilir metin
        editable_group = QGroupBox("Düzenlenebilir Metin")
        editable_layout = QVBoxLayout(editable_group)
        self.editable_text = QTextEdit()
        self.editable_text.setPlainText(editable_text)
        self.highlight_game_values(self.editable_text)
        
        self.editable_text.cursorPositionChanged.connect(self.on_cursor_position_changed)
        
        self.editable_text.setStyleSheet("""
            QTextEdit {
                background-color: #1E1E1E;
                color: #FFFFFF;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                padding: 8px;
                font-size: 13px;
            }
            QTextEdit:focus {
                border: 1px solid #007ACC;
            }
        """)
        editable_layout.addWidget(self.editable_text)
        
        texts_layout.addWidget(editable_group)
        
        layout.addLayout(texts_layout)
        
        # Alt kısım - butonlar
        buttons_layout = QHBoxLayout()
        
        # Kaydet butonu
        save_btn = QPushButton("Kaydet")
        save_btn.setStyleSheet("""
            QPushButton {
                background-color: #007ACC;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                min-width: 80px;
                font-weight: bold;
            }
            QPushButton:hover {
                background-color: #005999;
            }
            QPushButton:pressed {
                background-color: #004C80;
            }
        """)
        save_btn.clicked.connect(self.accept)
        buttons_layout.addWidget(save_btn)
        
        # İptal butonu
        cancel_btn = QPushButton("İptal")
        cancel_btn.setStyleSheet("""
            QPushButton {
                background-color: #3D3D3D;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                min-width: 80px;
            }
            QPushButton:hover {
                background-color: #4D4D4D;
            }
            QPushButton:pressed {
                background-color: #5D5D5D;
            }
        """)
        cancel_btn.clicked.connect(self.reject)
        buttons_layout.addWidget(cancel_btn)
        
        layout.addLayout(buttons_layout)
        
        # Diyalog stili
        self.setStyleSheet("""
            QDialog {
                background-color: #2D2D2D;
            }
            QGroupBox {
                color: #FFFFFF;
                font-weight: bold;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                margin-top: 12px;
                padding-top: 24px;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                subcontrol-position: top left;
                padding: 0 4px;
                left: 8px;
            }
        """)
        
    def on_cursor_position_changed(self):
        if not self.is_highlighting:
            self.is_highlighting = True
            self.highlight_game_values(self.editable_text)
            self.is_highlighting = False

    def highlight_game_values(self, text_edit):
        if self.is_highlighting:
            return
            
        # Metni al
        text = text_edit.toPlainText()
        cursor = text_edit.textCursor()
        cursor_position = cursor.position()
        
        # Özel değerleri vurgula
        text_edit.blockSignals(True)  # Sinyalleri geçici olarak devre dışı bırak
        
        text_edit.clear()
        cursor = text_edit.textCursor()
        
        # Oyun değerlerini bul ve renklendir
        game_values = list(re.finditer(r'{[^{}]*}', text))  # Sadece süslü parantez içindeki değerleri al
        offset = 0
        
        for match in game_values:
            start, end = match.span()
            value = match.group()
            
            # Önceki metni normal formatta ekle
            normal_format = cursor.charFormat()
            normal_format.setForeground(QColor("#FFFFFF"))  # Beyaz renk
            normal_format.setFontWeight(QFont.Normal)
            cursor.insertText(text[offset:start], normal_format)
            
            # Oyun değerini renkli ve kalın ekle
            game_format = cursor.charFormat()
            game_format.setForeground(QColor("#FFA500"))  # Turuncu renk
            game_format.setFontWeight(QFont.Bold)
            cursor.insertText(value, game_format)
            
            offset = end
        
        # Kalan metni normal formatta ekle
        normal_format = cursor.charFormat()
        normal_format.setForeground(QColor("#FFFFFF"))  # Beyaz renk
        normal_format.setFontWeight(QFont.Normal)
        cursor.insertText(text[offset:], normal_format)
        
        # İmleci eski konumuna getir
        cursor.setPosition(cursor_position)
        text_edit.setTextCursor(cursor)
        
        text_edit.blockSignals(False)  # Sinyalleri tekrar etkinleştir

    def get_edited_text(self):
        return self.editable_text.toPlainText()

    def auto_translate_current(self):
        try:
            # Orijinal metni al
            text = self.original_text.toPlainText()
            if not text.strip():
                return

            # Çeviri servisini kontrol et
            settings = QSettings("TS4ModTranslator", "Settings")
            service = settings.value("translation_service", "google")

            if service == "deepl" and DEEPL_AVAILABLE:
                api_key = settings.value("deepl_api_key", "")
                if not api_key:
                    QMessageBox.warning(
                        self,
                        "Uyarı",
                        "DeepL API Key bulunamadı. Lütfen ayarlardan API Key'inizi girin."
                    )
                    return
                
                try:
                    translator = deepl.Translator(api_key)
                    result = translator.translate_text(text, target_lang="TR")
                    translated_text = result.text
                except Exception as e:
                    QMessageBox.critical(
                        self,
                        "DeepL Hatası",
                        f"Çeviri sırasında hata oluştu: {str(e)}"
                    )
                    return
            else:
                # DeepL seçili ama kullanılamıyorsa uyarı ver
                if service == "deepl" and not DEEPL_AVAILABLE:
                    QMessageBox.warning(
                        self,
                        "Uyarı",
                        "DeepL modülü yüklü değil. Google Translate kullanılıyor."
                    )
                
                # Google Translate kullan
                text = text.replace("\n", r"\x0a").replace("\r", r"\x0d")
                url = 'http://translate.google.com/m?sl=auto&tl=tr&q=%s'
                ua = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36'
                
                link = url % urllib.parse.quote(text)
                request = urllib.request.Request(link, headers={'User-Agent': ua})
                data = urllib.request.urlopen(request).read().decode('utf-8')
                expr = r'(?s)class="(?:t0|result-container)">(.*?)<'
                translated_text = html.unescape(re.findall(expr, data)[0])
                translated_text = translated_text.replace(r"\x0a", "\n").replace(r"\x0d", "\r")

            # Çeviriyi metin kutusuna yerleştir
            self.editable_text.setPlainText(translated_text)
            self.highlight_game_values(self.editable_text)

        except Exception as e:
            QMessageBox.critical(
                self,
                "Hata",
                f"Çeviri sırasında hata oluştu: {str(e)}"
            )

class SettingsDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Seçenekler")
        self.setMinimumWidth(400)
        
        # Ana layout
        layout = QVBoxLayout(self)
        
        # Çeviri servisi seçimi
        service_group = QGroupBox("Çeviri Servisi")
        service_layout = QVBoxLayout(service_group)
        
        self.google_radio = QRadioButton("Google Translate (Ücretsiz)")
        self.deepl_radio = QRadioButton("DeepL Translate (API Key Gerekli)")
        
        # Mevcut ayarı yükle
        settings = QSettings("TS4ModTranslator", "Settings")
        current_service = settings.value("translation_service", "google")
        if current_service == "google":
            self.google_radio.setChecked(True)
        else:
            self.deepl_radio.setChecked(True)
        
        service_layout.addWidget(self.google_radio)
        service_layout.addWidget(self.deepl_radio)
        
        # DeepL API Key girişi
        api_group = QGroupBox("DeepL API Key")
        api_layout = QVBoxLayout(api_group)
        
        self.api_key_input = QLineEdit()
        self.api_key_input.setPlaceholderText("DeepL API Key'inizi girin")
        self.api_key_input.setText(settings.value("deepl_api_key", ""))
        self.api_key_input.setEchoMode(QLineEdit.Password)
        api_layout.addWidget(self.api_key_input)
        
        # Çeviri hızı ayarı
        speed_group = QGroupBox("Çeviri Hızı")
        speed_layout = QVBoxLayout(speed_group)
        
        speed_label = QLabel("Çeviri istekleri arasındaki bekleme süresi (ms):")
        self.speed_input = QLineEdit()
        self.speed_input.setPlaceholderText("Örn: 500")
        self.speed_input.setText(settings.value("translation_speed", "500"))
        self.speed_input.setValidator(QIntValidator(0, 10000))
        
        speed_layout.addWidget(speed_label)
        speed_layout.addWidget(self.speed_input)
        
        # Butonlar
        buttons_layout = QHBoxLayout()
        
        save_btn = QPushButton("Kaydet")
        save_btn.clicked.connect(self.save_settings)
        cancel_btn = QPushButton("İptal")
        cancel_btn.clicked.connect(self.reject)
        
        buttons_layout.addWidget(save_btn)
        buttons_layout.addWidget(cancel_btn)
        
        # Stil
        self.setStyleSheet("""
            QDialog {
                background-color: #2D2D2D;
                color: #FFFFFF;
            }
            QGroupBox {
                color: #FFFFFF;
                font-weight: bold;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                margin-top: 12px;
                padding-top: 24px;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                subcontrol-position: top left;
                padding: 0 4px;
                left: 8px;
            }
            QRadioButton, QLabel {
                color: #FFFFFF;
                padding: 4px;
            }
            QRadioButton::indicator {
                width: 16px;
                height: 16px;
            }
            QLineEdit {
                background-color: #1E1E1E;
                color: #FFFFFF;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                padding: 8px;
            }
            QPushButton {
                background-color: #007ACC;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                min-width: 80px;
            }
            QPushButton:hover {
                background-color: #005999;
            }
            QPushButton[text="İptal"] {
                background-color: #3D3D3D;
            }
            QPushButton[text="İptal"]:hover {
                background-color: #4D4D4D;
            }
        """)
        
        # Layout'ları ana layout'a ekle
        layout.addWidget(service_group)
        layout.addWidget(api_group)
        layout.addWidget(speed_group)
        layout.addLayout(buttons_layout)
        
    def save_settings(self):
        # DeepL seçili ve API key boşsa kaydetmeyi engelle
        if self.deepl_radio.isChecked() and not self.api_key_input.text().strip():
            QMessageBox.warning(
                self,
                "Uyarı",
                "DeepL Translate seçiliyken API Key boş bırakılamaz.\nLütfen geçerli bir API Key girin veya Google Translate'i seçin."
            )
            return
            
        # API key'i test et
        if self.deepl_radio.isChecked() and DEEPL_AVAILABLE:
            try:
                translator = deepl.Translator(self.api_key_input.text().strip())
                # API key'in geçerli olup olmadığını kontrol et
                translator.get_usage()
            except Exception as e:
                QMessageBox.critical(
                    self,
                    "DeepL API Hatası",
                    f"Girilen API Key geçersiz veya hatalı.\nHata: {str(e)}"
                )
                return
        elif self.deepl_radio.isChecked() and not DEEPL_AVAILABLE:
            QMessageBox.warning(
                self,
                "Uyarı",
                "DeepL modülü yüklü değil. DeepL seçilse bile Google Translate kullanılacak."
            )
        
        # Çeviri hızını kontrol et
        try:
            speed = int(self.speed_input.text())
            if speed < 0:
                raise ValueError("Çeviri hızı negatif olamaz")
        except ValueError:
            QMessageBox.warning(
                self,
                "Uyarı",
                "Çeviri hızı geçerli bir sayı olmalıdır.\nVarsayılan değer (500 ms) kullanılacak."
            )
            self.speed_input.setText("500")
        
        # Ayarları kaydet
        settings = QSettings("TS4ModTranslator", "Settings")
        settings.setValue("translation_service", "google" if self.google_radio.isChecked() else "deepl")
        settings.setValue("deepl_api_key", self.api_key_input.text().strip())
        settings.setValue("translation_speed", self.speed_input.text().strip())
        self.accept()

class ModTranslator(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("The Sims 4 Mod Translator TR | Discord: merxdo")
        self.setMinimumSize(1200, 800)
        
        # Paket dosyasını başlat
        self.package_file = DBPFFile()
        self.current_file_data = None
        
        # İş parçacığı havuzunu başlat
        self.thread_pool = QThreadPool()
        self.active_workers = 0
        
        # Değişiklikleri takip et
        self.has_unsaved_changes = False
        
        # UI kurulumu
        self.setup_ui()
        
        # Koyu temayı uygula
        self.apply_dark_theme()
        
    def setup_ui(self):
        # Merkezi widget ve ana düzen oluştur
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setSpacing(10)
        main_layout.setContentsMargins(10, 10, 10, 10)
        
        # Menü çubuğu oluştur
        self.create_menu_bar()
        
        # Araç çubuğu oluştur
        self.create_toolbar()
        
        # Başlık bölümü
        header_frame = QFrame()
        header_frame.setFrameShape(QFrame.StyledPanel)
        header_frame.setStyleSheet("""
            QFrame {
                background-color: #2D2D2D;
                border-radius: 8px;
                padding: 10px;
            }
        """)
        header_layout = QVBoxLayout(header_frame)  # Dikey layout kullan
        header_layout.setSpacing(10)  # Öğeler arası boşluk
        
        # Üst kısım - Arama ve çeviri butonu
        top_section = QHBoxLayout()
        
        # Arama çubuğu
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Kelime ara...")
        self.search_input.textChanged.connect(self.filter_table)
        self.search_input.setStyleSheet("""
            QLineEdit {
                background-color: #3D3D3D;
                color: #FFFFFF;
                border: 1px solid #555555;
                border-radius: 4px;
                padding: 8px;
                font-size: 14px;
            }
            QLineEdit:focus {
                border: 1px solid #007ACC;
            }
        """)
        top_section.addWidget(self.search_input)
        
        # Otomatik çeviri butonu
        self.translate_btn = QPushButton("Hepsini Otomatik Çevir")
        self.translate_btn.setStyleSheet("""
            QPushButton {
                background-color: #007ACC;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                font-weight: bold;
                font-size: 14px;
            }
            QPushButton:hover {
                background-color: #005999;
            }
            QPushButton:pressed {
                background-color: #004C80;
            }
        """)
        self.translate_btn.clicked.connect(self.auto_translate_all)
        top_section.addWidget(self.translate_btn)
        
        header_layout.addLayout(top_section)
        
        # Alt kısım - İlerleme çubuğu ve yüzde
        progress_section = QHBoxLayout()
        
        # İlerleme çubuğu
        self.progress_bar = QProgressBar()
        self.progress_bar.setStyleSheet("""
            QProgressBar {
                background-color: #1E1E1E;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                padding: 1px;
                text-align: center;
                color: white;
            }
            QProgressBar::chunk {
                background-color: #007ACC;
                border-radius: 4px;
            }
        """)
        self.progress_bar.setFormat("Çeviri İlerlemesi: %p% (%v/%m)")
        progress_section.addWidget(self.progress_bar)
        
        header_layout.addLayout(progress_section)
        
        main_layout.addWidget(header_frame)
        
        # Tablo oluştur
        self.table = QTableWidget()
        self.table.setColumnCount(4)  # Seçim kutusu için bir sütun ekle
        self.table.setHorizontalHeaderLabels(["Seç", "Anahtar", "Orijinal Dize", "Düzenlenebilir Dize"])
        self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(2, QHeaderView.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(3, QHeaderView.Stretch)
        self.table.verticalHeader().setVisible(False)
        self.table.setAlternatingRowColors(True)
        self.table.setSelectionBehavior(QTableWidget.SelectRows)
        self.table.setSelectionMode(QTableWidget.SingleSelection)
        self.table.cellDoubleClicked.connect(self.show_edit_dialog)
        
        # Stil
        self.table.setStyleSheet("""
            QTableWidget {
                background-color: #1E1E1E;
                color: #FFFFFF;
                gridline-color: #3D3D3D;
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                selection-background-color: #264F78;
                selection-color: #FFFFFF;
                alternate-background-color: #2A2A2A;
            }
            QTableWidget::item {
                padding: 8px;
                border: none;
            }
            QHeaderView::section {
                background-color: #2D2D2D;
                color: #FFFFFF;
                padding: 8px;
                border: none;
                border-right: 1px solid #3D3D3D;
                border-bottom: 1px solid #3D3D3D;
                font-weight: bold;
            }
            QTableWidget::item:selected {
                background-color: #264F78;
            }
            QCheckBox {
                color: #FFFFFF;
            }
            QCheckBox::indicator {
                width: 16px;
                height: 16px;
            }
        """)
        
        main_layout.addWidget(self.table)
        
        # Durum çubuğu oluştur
        self.status_bar = QStatusBar()
        self.status_bar.setStyleSheet("""
            QStatusBar {
                background-color: #007ACC;
                color: white;
                padding: 4px;
                font-weight: bold;
            }
        """)
        self.setStatusBar(self.status_bar)
        
        # Başlangıç mesajı
        self.status_bar.showMessage("Hazır. Dosya > Aç menüsünden bir dosya seçin.")
        
        # Seçilen satırları takip et
        self.selected_rows = set()
        
        # Çeviri butonunun durumunu güncelle
        self.update_translate_button()
        
    def apply_dark_theme(self):
        # Uygulama yazı tipini ayarla
        font_id = QFontDatabase.addApplicationFont(":/fonts/Segoe UI")
        if font_id != -1:
            font_family = QFontDatabase.applicationFontFamilies(font_id)[0]
        else:
            font_family = "Segoe UI"
            
        self.setStyleSheet(f"""
            QMainWindow {{
                background-color: #1E1E1E;
                font-family: "{font_family}";
            }}
            QWidget {{
                color: #FFFFFF;
            }}
            QToolBar {{
                background-color: #2D2D2D;
                border: none;
                spacing: 5px;
                padding: 5px;
            }}
            QToolButton {{
                background-color: transparent;
                border: none;
                border-radius: 4px;
                padding: 5px;
            }}
            QToolButton:hover {{
                background-color: #3D3D3D;
            }}
            QToolButton:pressed {{
                background-color: #4D4D4D;
            }}
            QMenu {{
                background-color: #2D2D2D;
                border: 1px solid #3D3D3D;
            }}
            QMenu::item {{
                padding: 5px 20px;
            }}
            QMenu::item:selected {{
                background-color: #3D3D3D;
            }}
            QMenuBar {{
                background-color: #2D2D2D;
            }}
            QMenuBar::item {{
                padding: 5px 10px;
            }}
            QMenuBar::item:selected {{
                background-color: #3D3D3D;
            }}
            QProgressDialog {{
                background-color: #2D2D2D;
                color: #FFFFFF;
            }}
            QProgressDialog QProgressBar {{
                border: 1px solid #3D3D3D;
                border-radius: 4px;
                text-align: center;
            }}
            QProgressDialog QProgressBar::chunk {{
                background-color: #007ACC;
            }}
            QMessageBox {{
                background-color: #2D2D2D;
            }}
            QMessageBox QPushButton {{
                background-color: #007ACC;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
                min-width: 80px;
            }}
            QMessageBox QPushButton:hover {{
                background-color: #005999;
            }}
        """)
        
    def create_toolbar(self):
        toolbar = QToolBar()
        toolbar.setIconSize(QSize(24, 24))
        toolbar.setMovable(False)
        
        # Dosya açma eylemi
        open_action = QAction(QIcon(":/icons/open.png"), "Dosyayı Aç", self)
        open_action.setStatusTip("Bir mod dosyası açın")
        open_action.triggered.connect(self.open_file)
        toolbar.addAction(open_action)
        
        toolbar.addSeparator()
        
        # Dosya kaydetme eylemi
        save_action = QAction(QIcon(":/icons/save.png"), "Dosyayı Kaydet", self)
        save_action.setStatusTip("Değişiklikleri kaydet")
        save_action.triggered.connect(self.save_file)
        toolbar.addAction(save_action)
        
        toolbar.addSeparator()
        
        # Ayarlar eylemi
        settings_action = QAction(QIcon(":/icons/settings.png"), "Seçenekler", self)
        settings_action.setStatusTip("Çeviri ayarlarını yapılandır")
        settings_action.triggered.connect(self.show_settings)
        toolbar.addAction(settings_action)
        
        self.addToolBar(toolbar)
        
    def auto_translate_all(self):
        try:
            # Dosya yüklü olup olmadığını kontrol et
            if not hasattr(self, 'string_table') or not self.string_table.strings:
                QMessageBox.warning(
                    self,
                    "Uyarı",
                    "Lütfen önce bir dosya yükleyin.\nDosya > Aç menüsünden veya araç çubuğundaki Dosyayı Aç butonundan bir dosya seçin."
                )
                return

            # Çevrilecek tüm metinleri topla
            texts_to_translate = []
            self.row_indices = []
            
            # Satırları seçip seçmediğimizi kontrol et
            if self.selected_rows:
                # Yalnızca seçili satırları çevir
                for row in self.selected_rows:
                    original_text = self.table.item(row, 2).text()
                    if original_text.strip():
                        texts_to_translate.append(original_text)
                        self.row_indices.append(row)
            else:
                # Tüm satırları çevir
                for row in range(self.table.rowCount()):
                    original_text = self.table.item(row, 2).text()
                    if original_text.strip():
                        texts_to_translate.append(original_text)
                        self.row_indices.append(row)
            
            if not texts_to_translate:
                return

            # Toplam çevrilecek metin sayısı
            self.total_translations = len(texts_to_translate)
            self.completed_translations = 0
                
            # İlerleme çubuğunu sıfırla
            self.progress_bar.setValue(0)
            self.progress_bar.setFormat("Çeviri İlerlemesi: %p% (%v/%m)")
            self.progress_bar.setMaximum(self.total_translations)

            # İlerleme iletişim kutusu
            self.progress = QProgressDialog("Dizeler çevriliyor...", "İptal", 0, self.total_translations, self)
            self.progress.setWindowModality(Qt.WindowModal)
            self.progress.setWindowTitle("Otomatik Çeviri İlerlemesi")
            
            # Toplu işleme için metinleri 10'lu parçalara böl
            chunk_size = 10
            chunks = [texts_to_translate[i:i + chunk_size] for i in range(0, len(texts_to_translate), chunk_size)]
            
            self.active_workers = len(chunks)
            
            # Çeviri hızı ayarını, ayarlardan al
            settings = QSettings("TS4ModTranslator", "Settings")
            translation_speed = int(settings.value("translation_speed", "500"))
            
            # Her parçayı paralel olarak işle
            for i, chunk in enumerate(chunks):
                if self.progress.wasCanceled():
                    break
                    
                worker = TranslateWorker(chunk, i * chunk_size)
                worker.signals.progress.connect(self.update_translation)
                worker.signals.finished.connect(self.worker_finished)
                worker.signals.error.connect(self.worker_error)
                worker.translation_speed = translation_speed
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
            item = QTableWidgetItem(translation)
            item.setFlags(item.flags() & ~Qt.ItemIsEditable)  # Düzenlemeyi devre dışı bırak
            
            # Tamamlanmış çeviri için arka plan rengini ayarla
            if translation.strip():  # Çeviri boş değilse
                item.setBackground(QColor("#1E392A"))  # Koyu yeşil ton
                
                # Tüm satırı yeşil yap
                for col in range(4):  # Onay kutusu sütununu eklemek için güncelle
                    cell_item = self.table.item(row, col)
                    if cell_item:
                        cell_item.setBackground(QColor("#1E392A"))
            
            current_text = self.table.item(row, 2).text()  # Orijinal metin 2. stunda
            if translation != current_text:  # Eğer çeviri mevcut metinden farklıysa
                self.has_unsaved_changes = True  # Değişiklik yapıldığını işaretle
            
            self.table.setItem(row, 3, item)  # Çeviri 3. stunda
            
            # İlerleme sayacı
            self.completed_translations += 1
            
            # İlerleme çubuğunu ve dialog'u güncelle
            self.progress_bar.setValue(self.completed_translations)
            self.progress.setValue(self.completed_translations)
    
    @Slot()
    def worker_finished(self):
        self.active_workers -= 1
        if self.active_workers == 0:
            # Tüm işler tamamlandığında
            self.progress_bar.setValue(self.total_translations)
            self.progress.setValue(self.total_translations)
            self.status_bar.showMessage(f"Otomatik çeviri tamamlandı - {self.total_translations} dize çevrildi")
    
    @Slot(str)
    def worker_error(self, error_msg):
        QMessageBox.critical(
            self,
            "Hata",
            f"Çeviri hatası: {error_msg}"
        )
            
    def create_menu_bar(self):
        menubar = self.menuBar()
        
        # Dosya menüsü
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
        
        # Düzenleme menüsü
        edit_menu = menubar.addMenu("Düzenle")
        
        find_action = QAction("Bul", self)
        find_action.setShortcut("Ctrl+F")
        find_action.triggered.connect(lambda: self.search_input.setFocus())
        edit_menu.addAction(find_action)
        
        translate_action = QAction("Hepsini Otomatik Çevir", self)
        translate_action.setShortcut("Ctrl+T")
        translate_action.triggered.connect(self.auto_translate_all)
        edit_menu.addAction(translate_action)
        
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
                # Paket dosyasını yükle
                if self.package_file.load_from_binary(data):
                    # Tüm string tablolarını birleştir
                    self.string_table = StringTableFile()
                    total_strings = 0
                    
                    for instance_id, stbl in self.package_file.string_tables.items():
                        # Her bir string tablosundaki dizeleri ana tabloya ekle
                        for key, entry in stbl.strings.items():
                            if key not in self.string_table.strings:
                                self.string_table.strings[key] = entry
                                total_strings += 1
                    
                    if total_strings > 0:
                        self.populate_table()
                        self.status_bar.showMessage(
                            f"{os.path.basename(file_name)} dosyasından {total_strings} dize yüklendi"
                        )
                    else:
                        QMessageBox.warning(self, "Uyarı", "Paket dosyasında dize tablosu bulunamadı")
                else:
                    QMessageBox.critical(self, "Hata", "Geçersiz paket dosya biçimi")
            else:
                # STBL dosyasını doğrudan yükle
                self.string_table = StringTableFile()
                if self.string_table.load_from_binary(data):
                    self.populate_table()
                    self.status_bar.showMessage(
                        f"{os.path.basename(file_name)} dosyasından {len(self.string_table.strings)} dize yüklendi"
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
            # Kullanıcı arayüzünden dize tablosunu güncelle
            for row in range(self.table.rowCount()):
                key = int(self.table.item(row, 1).text())
                translation = self.table.item(row, 3).text()
                if key in self.string_table.strings:
                    self.string_table.strings[key].value = translation
            
            # Save file
            if file_name.lower().endswith('.package') and self.current_file_data:
                # Tüm string tablolarını güncelle
                for instance_id, stbl in self.package_file.string_tables.items():
                    # Her bir string tablosunu güncelle
                    for key in stbl.strings.keys():
                        if key in self.string_table.strings:
                            stbl.strings[key] = self.string_table.strings[key]
                
                # Paket dosyası olarak kaydet
                data = self.package_file.save_to_binary(self.current_file_data)
                if data:
                    with open(file_name, 'wb') as file:
                        file.write(data)
                    self.status_bar.showMessage(f"Paket dosyası kaydedildi {os.path.basename(file_name)}")
                    self.has_unsaved_changes = False  # Değişiklikleri kaydet
                else:
                    QMessageBox.critical(self, "Hata", "Paket dosyası oluşturulurken hata oluştu")
            else:
                # Save as STBL file
                data = self.string_table.save_to_binary()
                if data:
                    with open(file_name, 'wb') as file:
                        file.write(data)
                    self.status_bar.showMessage(f"{len(self.string_table.strings)} dizesi {os.path.basename(file_name)} dizinine kaydedildi")
                    self.has_unsaved_changes = False  # Değişiklikleri kaydet
                else:
                    QMessageBox.critical(self, "Hata", "STBL dosyası oluşturulurken hata oluştu")
                    
            # Dosya başarıyla kaydedildi, programı açık tut
            return True
                    
        except Exception as e:
            QMessageBox.critical(self, "Hata", f"Dosya kaydedilirken hata oluştu: {str(e)}")
            return False
                
    def populate_table(self):
        self.table.setRowCount(0)
        self.selected_rows.clear()
        
        # Anahtarları sıralı bir şekilde işle
        sorted_keys = sorted(self.string_table.strings.keys())
        
        for key in sorted_keys:
            entry = self.string_table.strings[key]
            row = self.table.rowCount()
            self.table.insertRow(row)
            
            # Seçim için onay kutusu
            checkbox_item = QTableWidgetItem()
            checkbox_item.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled)
            checkbox_item.setCheckState(Qt.Unchecked)
            self.table.setItem(row, 0, checkbox_item)
            
            # Anahtar
            key_item = QTableWidgetItem(str(entry.key))
            key_item.setFlags(key_item.flags() & ~Qt.ItemIsEditable)
            self.table.setItem(row, 1, key_item)
            
            # Orijinal dize
            original_item = QTableWidgetItem(entry.value)
            original_item.setFlags(original_item.flags() & ~Qt.ItemIsEditable)
            self.table.setItem(row, 2, original_item)
            
            # Çeviri
            translation_item = QTableWidgetItem(entry.value)
            translation_item.setFlags(translation_item.flags() & ~Qt.ItemIsEditable)  # Doğrudan düzenlemeyi devre dışı bırak
            
            # Eğer çeviri varsa ve orijinalden farklıysa yeşil yap
            if entry.value.strip() and translation_item.text() != original_item.text():
                for col in range(4):
                    cell_item = self.table.item(row, col)
                    if cell_item:
                        cell_item.setBackground(QColor("#1E392A"))
            
            self.table.setItem(row, 3, translation_item)
            
        # Tüm sütunları düzenlenemez yap
        self.table.setEditTriggers(QTableWidget.NoEditTriggers)
        
        # Bağlantı onay kutusu değişim sinyali
        self.table.itemChanged.connect(self.on_checkbox_changed)
        
        # Çeviri düğmesi metnini güncelle
        self.update_translate_button()
        
    def on_checkbox_changed(self, item):
        # Yalnızca işlem onay kutusu sütunu
        if item.column() == 0:
            row = item.row()
            if item.checkState() == Qt.Checked:
                self.selected_rows.add(row)
            else:
                if row in self.selected_rows:
                    self.selected_rows.remove(row)
            
            # Çeviri düğmesi metnini güncelle
            self.update_translate_button()
            
    def update_translate_button(self):
        if hasattr(self, 'selected_rows') and self.selected_rows:
            self.translate_btn.setText(f"Seçilen Dizeleri Çevir ({len(self.selected_rows)})")
        else:
            self.translate_btn.setText("Hepsini Otomatik Çevir")

    def filter_table(self, text):
        for row in range(self.table.rowCount()):
            show_row = False
            for col in range(1, 4):  # Anahtar, Orijinal Dize ve Düzenlenebilir Dize sütunlarında arama yapın
                item = self.table.item(row, col)
                if item and text.lower() in item.text().lower():
                    show_row = True
                    break
            self.table.setRowHidden(row, not show_row)
            
    def show_edit_dialog(self, row, column):
        # Yalnızca düzenlenebilir sütun için iletişim kutusunu göster (sütun 3)
        if column == 3:
            original_text = self.table.item(row, 2).text()
            editable_text = self.table.item(row, 3).text()
            
            dialog = EditDialog(original_text, editable_text, self)
            if dialog.exec():
                edited_text = dialog.get_edited_text()
                
                # Tabloyu güncelle
                item = QTableWidgetItem(edited_text)
                item.setFlags(item.flags() & ~Qt.ItemIsEditable)  # Doğrudan düzenlemeyi devre dışı bırak
                
                # Düzenlenen metin için arka plan rengini ayarlayın
                if edited_text.strip() and edited_text != original_text:
                    item.setBackground(QColor("#1E392A"))  # Koyu yeşil ton
                    
                    # Tüm satırı yeşil yap (işe yaramadı, kalsın daha sonra kontrol et.)
                    for col in range(4):
                        cell_item = self.table.item(row, col)
                        if cell_item:
                            cell_item.setBackground(QColor("#1E392A"))
                
                self.table.setItem(row, 3, item)
                
                # Dize tablosunu güncelle
                key = int(self.table.item(row, 1).text())
                self.string_table.strings[key].value = edited_text
                
                # Kaydedilmemiş değişiklikler olarak işaretle
                self.has_unsaved_changes = True

    def show_settings(self):
        dialog = SettingsDialog(self)
        dialog.exec()

    def closeEvent(self, event):
        if self.has_unsaved_changes:
            msg_box = QMessageBox(self)
            msg_box.setWindowTitle("Kaydedilmemiş Değişiklikler")
            msg_box.setText("Kaydedilmemiş değişiklikleriniz var.\nDeğişiklikleri kaydetmeden çıkmak istediğinize emin misiniz?")
            msg_box.setIcon(QMessageBox.Question)
            
            # Özel butonları ekle
            kaydet_btn = msg_box.addButton("Kaydet", QMessageBox.AcceptRole)
            kaydetme_btn = msg_box.addButton("Kaydetme", QMessageBox.DestructiveRole)
            iptal_btn = msg_box.addButton("İptal", QMessageBox.RejectRole)
            
            msg_box.setDefaultButton(kaydet_btn)  # Varsayılan buton
            
            # Stil
            msg_box.setStyleSheet("""
                QPushButton {
                    background-color: #007ACC;
                    color: white;
                    border: none;
                    padding: 8px 16px;
                    border-radius: 4px;
                    min-width: 80px;
                }
                QPushButton:hover {
                    background-color: #005999;
                }
                QPushButton[text="Kaydetme"] {
                    background-color: #CC4B37;
                }
                QPushButton[text="Kaydetme"]:hover {
                    background-color: #A63A2A;
                }
                QPushButton[text="İptal"] {
                    background-color: #3D3D3D;
                }
                QPushButton[text="İptal"]:hover {
                    background-color: #4D4D4D;
                }
            """)
            
            msg_box.exec()
            clicked_button = msg_box.clickedButton()
            
            if clicked_button == kaydet_btn:
                saved = self.save_file()
                if not saved:  # Eğer kaydetme başarısız olduysa
                    event.ignore()
                    return
                # Kaydetme başarılı olsa bile, kullanıcı çıkmak istemiyor olabilir
                # Bu nedenle event.ignore() ile çıkışı engelle
                event.ignore()
                return
            elif clicked_button == kaydetme_btn:
                # Kullanıcı kaydetmeden çık
                event.accept()
            else:  # İptal butonu
                event.ignore()
        else:
            # Değişiklik yoksa normal çıkış
            event.accept()

if __name__ == '__main__':
    app = QApplication(sys.argv)
    
    # Uygulama stilini ayarla
    app.setStyle('Fusion')
    
    # Varsayılan yazı tipini ayarla
    font = QFont("Segoe UI", 9)
    app.setFont(font)
    
    # Pencere oluştur ve göster
    window = ModTranslator()
    window.show()
    
    sys.exit(app.exec()) 
