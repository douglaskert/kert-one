import hashlib
import json
import time
import threading
import sqlite3
import os
from uuid import uuid4
from flask import Flask, jsonify, request, send_file, render_template
import requests
from urllib.parse import urlparse
import socket
import ipaddress
import sys
from ecdsa import SigningKey, VerifyingKey, SECP256k1, BadSignatureError
import qrcode
from io import BytesIO
from datetime import datetime
import re
import shutil
from flask_cors import CORS
from PyQt5.QtCore import pyqtSlot, pyqtSignal, QTimer, Qt, QObject, QMetaObject, Q_ARG, QMutex, QMutexLocker
from PyQt5.QtWidgets import (QApplication, QMainWindow, QPushButton, QTextEdit, 
                             QVBoxLayout, QWidget, QLabel, QLineEdit, QFormLayout, 
                             QGroupBox, QMessageBox, QHBoxLayout, QTabWidget, 
                             QStatusBar, QDialog, QDialogButtonBox, QPlainTextEdit, 
                             QInputDialog, QRadioButton)
from PyQt5.QtGui import QFont, QColor, QPalette, QTextCursor, QDoubleValidator, QValidator 
import multiprocessing

# --- INJEÇÃO DE MINERAÇÃO REAL (GPU/CPU) ---
try:
    import pyopencl as cl
    import numpy as np
    HAS_GPU = True
    platforms = cl.get_platforms()
    if not platforms:
        raise Exception("Nenhuma plataforma OpenCL encontrada")
    print(f"[SISTEMA] OpenCL Detectado: {platforms[0].name}")
except Exception as e:
    HAS_GPU = False
    print(f"[SISTEMA] Modo GPU Indisponível ({e}). Usando CPU.")

# --- Configurações ---
DIFFICULTY = 4 
MINING_REWARD = 50 
DATABASE = 'chain.db'
COIN_NAME = "Kert-One"
COIN_SYMBOL = "KERT"
PEERS_FILE = 'peers.json'
WALLET_FILE = "client_wallet.json"
NGROK_AUTH_FILE = "ngrok_auth.txt" 

# --- CHECKPOINT DE SEGURANÇA (Evita rejeição de blocos antigos) ---
LEGACY_CUTOFF_INDEX = 3330 

# --- NÓS SEMENTES (SEED NODES) ---
SEED_NODES = [
    "https://seend.kert-one.com",
    "http://seend3.kert-one.com:8001"
]

OPENCL_KERNEL = """
#define ROR(x, y) ((x >> y) | (x << (32 - y)))
#define Ch(x, y, z) (z ^ (x & (y ^ z)))
#define Maj(x, y, z) ((x & y) | (z & (x | y)))
#define S0(x) (ROR(x, 2) ^ ROR(x, 13) ^ ROR(x, 22))
#define S1(x) (ROR(x, 6) ^ ROR(x, 11) ^ ROR(x, 25))
#define s0(x) (ROR(x, 7) ^ ROR(x, 18) ^ (x >> 3)) 
#define s1(x) (ROR(x, 17) ^ ROR(x, 19) ^ (x >> 10))

__constant unsigned int K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

void sha256_transform(unsigned int *state, const unsigned int *data) {
    unsigned int a, b, c, d, e, f, g, h, t1, t2;
    unsigned int W[64];
    for (int i = 0; i < 16; ++i) W[i] = data[i];
    for (int i = 16; i < 64; ++i) W[i] = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
    a = state[0]; b = state[1]; c = state[2]; d = state[3];
    e = state[4]; f = state[5]; g = state[6]; h = state[7];
    for (int i = 0; i < 64; ++i) {
        t1 = h + S1(e) + Ch(e, f, g) + K[i] + W[i];
        t2 = S0(a) + Maj(a, b, c);
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

__kernel void search_block(__global unsigned int *result, __global int *found, const unsigned int difficulty, const unsigned int start_nonce) {
    unsigned int gid = get_global_id(0);
    unsigned int loop_count = 2000;
    for(unsigned int i=0; i < loop_count; i++) {
        if(*found != 0) return;
        unsigned int nonce = start_nonce + (gid * loop_count) + i;
        unsigned int state[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
        unsigned int data[16] = {0}; 
        data[0] = nonce;
        sha256_transform(state, data);
        
        if (state[0] <= (0xFFFFFFFF >> (difficulty * 4))) {
            *result = nonce;
            *found = 1;
            return;
        }
    }
}
"""

app = Flask(__name__)
node_id = str(uuid4()).replace('-', '')
CORS(app)

# --- Variáveis Globais ---
known_nodes = set()
miner_lock = threading.Lock()
blockchain = None
miner_address = None
miner_address_global = None 
meu_url = None
meu_ip = None
port = None
mining_active = False
mining_stop_flag = multiprocessing.Event()
mining_result = multiprocessing.Value('i', -1)
current_hashrate_global = 0.0

# --- Persistência ---
def salvar_peers(peers):
    with open(PEERS_FILE, 'w') as f: json.dump(list(peers), f)

def carregar_peers():
    if not os.path.exists(PEERS_FILE): return []
    with open(PEERS_FILE, 'r') as f:
        try: return json.load(f)
        except: return []

known_nodes = set(carregar_peers())

# --- Classe Blockchain ---
class Blockchain:
    ADJUST_INTERVAL = 10
    TARGET_TIME = 30

    def _calculate_difficulty_for_index(self, target_block_index):
        if target_block_index % self.ADJUST_INTERVAL != 0:
            return self.chain[-1].get('difficulty', 4)
        if len(self.chain) < self.ADJUST_INTERVAL: return 4 
        last_block = self.chain[-1]
        first_block = self.chain[-self.ADJUST_INTERVAL]
        actual_time = last_block['timestamp'] - first_block['timestamp']
        expected_time = self.ADJUST_INTERVAL * self.TARGET_TIME
        old_diff = last_block.get('difficulty', 4)
        new_diff = int(old_diff * (expected_time / max(1, actual_time)))
        return max(1, min(20, new_diff))
        
    def __init__(self, conn, node_id):
        self.conn = conn
        self.node_id = node_id
        self._init_db()
        self.chain = self._load_chain()
        self.current_transactions = []
        if not self.chain:
            print("[BOOT] 📡 Inserindo Gênese Base 500.0...")
            genesis_block = {'index': 1, 'previous_hash': '1', 'proof': 100, 'timestamp': 1700000000.0, 'miner': 'genesis', 'transactions': [], 'difficulty': 1, 'protocol_value': 500.0}
            self.chain.append(genesis_block)
            self._save_block(genesis_block)
        self.difficulty = self._calculate_difficulty_for_index(len(self.chain))
        print(f"[BOOT] Dificuldade inicial: {self.difficulty}")

    @staticmethod
    def hash(block):
        block_core = {"index": block["index"], "previous_hash": block["previous_hash"], "proof": block["proof"], "timestamp": block["timestamp"], "miner": block["miner"], "difficulty": block.get("difficulty", 1), "protocol_value": block.get("protocol_value", 0), "transactions": block["transactions"]}
        block_string = json.dumps(block_core, sort_keys=True, separators=(',', ':')).encode()
        return hashlib.sha256(block_string).hexdigest()

    def is_duplicate_transaction(self, new_tx):
        for tx in self.current_transactions:
            if tx.get('id') == new_tx.get('id'): return True
        return False

    @staticmethod
    def custom_asic_resistant_hash(data_bytes, nonce):
        raw = data_bytes + str(nonce).encode()
        return hashlib.sha256(hashlib.sha256(raw).digest()).hexdigest()

    def _init_db(self):
        c = self.conn.cursor()
        c.execute('CREATE TABLE IF NOT EXISTS blocks(index_ INTEGER PRIMARY KEY, previous_hash TEXT, proof INTEGER, timestamp REAL, miner TEXT, difficulty INTEGER, protocol_value REAL)')
        c.execute('CREATE TABLE IF NOT EXISTS txs(id TEXT PRIMARY KEY, sender TEXT, recipient TEXT, amount TEXT, fee TEXT, signature TEXT, block_index INTEGER, public_key TEXT)')
        self.conn.commit()

    def _load_chain(self):
        c = self.conn.cursor()
        c.execute("SELECT index_, previous_hash, proof, timestamp, miner, difficulty, protocol_value FROM blocks ORDER BY index_")
        chain = []
        for idx, prev, proof, ts, miner, difficulty, p_val in c.fetchall():
            c.execute("SELECT id, sender, recipient, amount, fee, signature, public_key FROM txs WHERE block_index=?", (idx,))
            txs = []
            for r in c.fetchall():
                txs.append(dict(id=r[0], sender=r[1], recipient=r[2], amount=r[3], fee=r[4], signature=r[5], public_key=r[6]))
            chain.append({'index': idx, 'previous_hash': prev, 'proof': proof, 'timestamp': ts, 'miner': miner, 'transactions': txs, 'difficulty': difficulty, 'protocol_value': p_val})
        return chain

    def new_block(self, proof, previous_hash, miner, initial_difficulty=None):
        block_index = len(self.chain) + 1
        reward = self._get_mining_reward(block_index)
        difficulty = self._calculate_difficulty_for_index(block_index) if initial_difficulty is None else initial_difficulty
        mining_reward_tx = {'id': str(uuid4()), 'sender': '0', 'recipient': miner, 'amount': f"{reward:.8f}", 'fee': f"{0.0:.8f}", 'signature': '', 'public_key': ''}
        if not (proof == 100 and previous_hash == '1'): self.current_transactions.insert(0, mining_reward_tx)
        block = {'index': block_index, 'previous_hash': previous_hash, 'proof': proof, 'timestamp': time.time(), 'miner': miner, 'transactions': self.current_transactions, 'difficulty': difficulty}
        self.current_transactions = []
        self.chain.append(block)
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM blocks WHERE index_=?", (block['index'],))
        if not c.fetchone(): self._save_block(block)
        return block

    def _save_block(self, block):
        c = self.conn.cursor()
        c.execute("INSERT INTO blocks VALUES (?, ?, ?, ?, ?, ?, ?)", (block['index'], block['previous_hash'], block['proof'], block['timestamp'], block['miner'], block['difficulty'], block.get('protocol_value', 500.0)))
        for t in block['transactions']:
            c.execute("INSERT INTO txs VALUES (?, ?, ?, ?, ?, ?, ?, ?)", (t['id'], t['sender'], t['recipient'], t['amount'], t['fee'], t['signature'], block['index'], t.get('public_key', '')))
        self.conn.commit()

    def _get_mining_reward(self, block_index):
        if block_index <= 1200: return 50.0
        elif block_index <= 2200: return 25.0
        elif block_index <= 4000: return 12.5
        elif block_index <= 5500: return 6.5
        elif block_index <= 6200: return 3.25
        elif block_index <= 20000: return 1.25
        elif block_index <= 1000000: return 0.03
        else:
            halvings = (block_index - 1000000) // 2100000
            return max(0.03 / (2 ** halvings), 0.0)

    def last_block(self): return self.chain[-1] if self.chain else None

    def proof_of_work(self, last_proof):
        difficulty = self._calculate_difficulty_for_index(len(self.chain) + 1)
        proof = 0
        print(f"⛏️  [MINER] Iniciando CPU. Dif: {difficulty}")
        while not self.valid_proof(last_proof, proof, difficulty):
            global mining_active
            if not mining_active: return -1
            if proof % 1000 == 0: time.sleep(0.001) 
            if self.last_block()['proof'] != last_proof: return -1
            proof += 1
        return proof

    @staticmethod
    def valid_proof(last_proof, proof, difficulty):
        guess = f"{last_proof}{proof}".encode()
        guess_hash = Blockchain.custom_asic_resistant_hash(guess, proof)
        return guess_hash[:difficulty] == "0" * difficulty
        
    @staticmethod
    def _mine_gpu(last_proof, difficulty, stop_event, result_value):
        global current_hashrate_global
        try:
            import pyopencl as cl
            import numpy as np
            import time
        except ImportError: return -1

        try:
            platforms = cl.get_platforms()
            if not platforms: return -1
            target_platform = next((p for p in platforms if "nvidia" in p.name.lower()), platforms[0])
            device = target_platform.get_devices(device_type=cl.device_type.GPU)[0]
            
            ctx = cl.Context(devices=[device])
            queue = cl.CommandQueue(ctx)
            prg = cl.Program(ctx, OPENCL_KERNEL).build()
            kernel = cl.Kernel(prg, "search_block")

            result_nonce = np.zeros(1, dtype=np.uint32)
            found = np.zeros(1, dtype=np.int32)
            res_buf = cl.Buffer(ctx, cl.mem_flags.WRITE_ONLY, result_nonce.nbytes)
            found_buf = cl.Buffer(ctx, cl.mem_flags.READ_WRITE | cl.mem_flags.COPY_HOST_PTR, hostbuf=found)

            batch_size = 500000 
            loop_intern0 = 2000   
            current_nonce = 0
            start_time = time.time()
            total_hashes = 0

            print(f"🔥 [GPU] ENGINE KERT-ONE ATIVA: {device.name}")

            while not stop_event.is_set():
                iter_start = time.time()
                kernel(queue, (batch_size,), None, res_buf, found_buf, np.uint32(difficulty), np.uint32(current_nonce))
                queue.finish() 
                
                if (time.time() - iter_start) < 0.001:
                    print("[GPU WATCHDOG] ⚠️ Driver parou de responder. Reiniciando minerador...")
                    current_hashrate_global = 0.0
                    return -1

                cl.enqueue_copy(queue, found, found_buf)
                total_hashes += (batch_size * loop_intern0)
                
                now = time.time()
                if now - start_time >= 3.0:
                    current_hashrate_global = (total_hashes / (now - start_time)) / 1e6
                    print(f"⚡ [GPU] Speed: {current_hashrate_global:.2f} MH/s")
                    start_time = now
                    total_hashes = 0
                
                if found[0] == 1:
                    cl.enqueue_copy(queue, result_nonce, res_buf)
                    nonce = int(result_nonce[0])
                    if Blockchain.valid_proof(last_proof, nonce, difficulty):
                        print(f"💎 [GPU] BLOCO ENCONTRADO: {nonce}")
                        result_value.value = nonce
                        stop_event.set()
                        return nonce
                    found[0] = 0
                    cl.enqueue_copy(queue, found_buf, found)

                current_nonce += (batch_size * loop_intern0)
                if current_nonce > 4000000000: current_nonce = 0
                
        except Exception as e:
            print(f"[GPU ERROR] {e}")
            current_hashrate_global = 0.0
            return -1
        return -1

    def tx_already_mined(self, tx_id):
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM txs WHERE id=?", (tx_id,))
        return c.fetchone() is not None

    def valid_chain(self, chain, check_strict=True):
        if not chain: return False
        if chain[0]['index'] != 1 or chain[0]['previous_hash'] != '1': return False
        for idx in range(1, len(chain)):
            prev = chain[idx - 1]
            curr = chain[idx]
            
            if check_strict:
                if curr['previous_hash'] != self.hash(prev): return False
                if curr['index'] >= LEGACY_CUTOFF_INDEX:
                    if not self.valid_proof(prev['proof'], curr['proof'], curr.get('difficulty', DIFFICULTY)): return False
            else:
                if curr['index'] != prev['index'] + 1: return False
        return True

    def get_total_difficulty(self, chain_to_check):
        return sum([block.get('difficulty', DIFFICULTY) for block in chain_to_check])

    def resolve_conflicts(self):
        neighbors = list(known_nodes)
        new_chain = None
        max_difficulty = self.get_total_difficulty(self.chain)
        
        is_fresh_install = (len(self.chain) <= 1)
        if is_fresh_install:
            print("[BOOT] 🐇 MODO CÓPIA CEGA ATIVADO (Windows): Baixando chain do Seed...")

        print(f"[CONSENSO] A verificar {len(neighbors)} vizinhos...")
        for node_url in neighbors:
            if node_url == meu_url: continue
            try:
                response = requests.get(f"{node_url}/chain", timeout=60)
                if response.status_code == 200:
                    data = response.json()
                    peer_chain = data.get("chain")
                    if not peer_chain: continue
                    
                    peer_difficulty = self.get_total_difficulty(peer_chain)
                    
                    if peer_difficulty > max_difficulty:
                        if self.valid_chain(peer_chain, check_strict=not is_fresh_install):
                            max_difficulty = peer_difficulty
                            new_chain = peer_chain
                            print(f"[CONSENSO] 📥 Nova chain encontrada em: {node_url}")
                        else:
                            print(f"[CONSENSO] Chain de {node_url} rejeitada (Inválida).")
            except: pass
            
        if new_chain:
            self.chain = new_chain
            self._rebuild_db_from_chain()
            print(f"[CONSENSO] ✅ Sincronizado. Blocos: {len(self.chain)}")
            return True
        return False

    def _rebuild_db_from_chain(self):
        try:
            c = self.conn.cursor()
            c.execute("DELETE FROM txs"); c.execute("DELETE FROM blocks")
            for block in self.chain:
                c.execute("INSERT INTO blocks VALUES (?, ?, ?, ?, ?, ?, ?)", (block['index'], block['previous_hash'], block['proof'], block['timestamp'], block['miner'], block.get('difficulty', 1), block.get('protocol_value', 0.0)))
                for tx in block['transactions']:
                    c.execute("INSERT INTO txs VALUES (?, ?, ?, ?, ?, ?, ?, ?)", (tx['id'], tx['sender'], tx['recipient'], tx['amount'], tx['fee'], tx['signature'], block['index'], tx.get('public_key', '')))
            self.conn.commit()
        except Exception as e: print(f"[REBUILD ERRO] {e}")

    def balance(self, address):
        bal = 0.0
        for block in self.chain:
            for t in block['transactions']:
                if t['sender'] == address: bal -= (float(t['amount']) + float(t['fee']))
                if t['recipient'] == address: bal += float(t['amount'])
        for t in self.current_transactions:
            if t['sender'] == address: bal -= (float(t['amount']) + float(t['fee']))
            if t['recipient'] == address: bal += float(t['amount'])
        return bal

# --- Funções de Carteira ---
def gerar_endereco(public_key_hex):
    try:
        if public_key_hex.startswith("04"): public_key_hex = public_key_hex[2:]
        return hashlib.sha256(bytes.fromhex(public_key_hex)).hexdigest()[:40]
    except: return None

def sign_transaction(private_key_hex, tx_data):
    sk = SigningKey.from_string(bytes.fromhex(private_key_hex), curve=SECP256k1)
    message_json = json.dumps({'amount': tx_data['amount'], 'fee': tx_data['fee'], 'recipient': tx_data['recipient'], 'sender': tx_data['sender']}, sort_keys=True, separators=(',',':')).encode('utf-8')
    return sk.sign_digest(hashlib.sha256(message_json).digest()).hex()

def create_wallet():
    pk = SigningKey.generate(curve=SECP256k1)
    pub = "04" + pk.get_verifying_key().to_string().hex()
    return {'private_key': pk.to_string().hex(), 'public_key': pub, 'address': gerar_endereco(pub)}

def load_wallet_file(filepath):
    if os.path.exists(filepath):
        try:
            with open(filepath, 'r') as f: return json.load(f)
        except: return None
    return None

def save_wallet_file(wallet_data, filepath):
    with open(filepath, 'w') as f: json.dump(wallet_data, f, indent=4)

# --- Funções de Token Visual ---
def load_ngrok_token():
    if os.path.exists(NGROK_AUTH_FILE):
        try:
            with open(NGROK_AUTH_FILE, 'r') as f: return f.read().strip()
        except: return None
    return None

def save_ngrok_token(token):
    try:
        with open(NGROK_AUTH_FILE, 'w') as f: f.write(token.strip())
    except: pass

# --- Flask Endpoints ---
@app.route('/chain', methods=['GET'])
def chain_api():
    return jsonify({'chain': blockchain.chain, 'length': len(blockchain.chain), 'pending_transactions': blockchain.current_transactions, 'node_id': node_id}), 200

@app.route('/nodes/register', methods=['POST'])
def register_nodes_api():
    data = request.get_json(silent=True) or {}
    new_node_url = data.get("url")
    if not new_node_url and data.get("ip"): new_node_url = f"http://{data['ip']}:{data.get('port')}"
    if not new_node_url: return jsonify({"message": "Invalido"}), 400
    new_node_url = new_node_url.strip().rstrip("/")
    if not new_node_url.startswith("http"): new_node_url = "http://" + new_node_url
    if new_node_url == meu_url: return jsonify({"message": "Self ignored"}), 200
    if new_node_url not in known_nodes:
        known_nodes.add(new_node_url); salvar_peers(known_nodes)
        try: requests.post(f"{new_node_url}/nodes/register", json={"url": meu_url}, timeout=5)
        except: pass
    return jsonify({"message": "Registrado", "known_peers": list(known_nodes)}), 200

@app.route('/nodes', methods=['GET'])
def get_nodes_api(): return jsonify({'nodes': list(known_nodes)}), 200

@app.route('/nodes/resolve', methods=['GET'])
def resolve_api():
    replaced = blockchain.resolve_conflicts()
    return jsonify({'message': 'Cadeia substituida' if replaced else 'Cadeia mantida'}), 200

@app.route('/balance/<addr>', methods=['GET'])
def balance_api(addr):
    return jsonify({'address': addr, 'balance': blockchain.balance(addr), 'symbol': COIN_SYMBOL}), 200

@app.route('/tx/new', methods=['POST'])
def new_transaction_api():
    values = request.get_json(silent=True)
    required = ['id', 'sender', 'recipient', 'amount', 'fee', 'public_key', 'signature']
    if not values or not all(k in values for k in required): return jsonify({'message': 'Dados incompletos'}), 400
    try:
        tx = {'id': values['id'], 'sender': values['sender'], 'recipient': values['recipient'], 'amount': f"{float(values['amount']):.8f}", 'fee': f"{float(values['fee']):.8f}", 'public_key': values['public_key'], 'signature': values['signature'], 'timestamp': values.get('timestamp', time.time())}
        if blockchain.is_duplicate_transaction(tx): return jsonify({'message': 'Duplicada'}), 200
        
        vk = VerifyingKey.from_string(bytes.fromhex(values['public_key']), curve=SECP256k1)
        msg = json.dumps({'amount': tx['amount'], 'fee': tx['fee'], 'recipient': tx['recipient'], 'sender': tx['sender']}, sort_keys=True, separators=(',', ':')).encode('utf-8')
        vk.verify_digest(bytes.fromhex(tx['signature']), hashlib.sha256(msg).digest())
        
        if blockchain.balance(tx['sender']) < (float(tx['amount']) + float(tx['fee'])): return jsonify({'message': 'Saldo insuficiente'}), 400
        blockchain.current_transactions.append(tx)
        broadcast_tx_to_peers(tx)
        return jsonify({'message': 'TX Adicionada'}), 201
    except Exception as e: return jsonify({'message': f'Erro: {e}'}), 400

def broadcast_tx_to_peers(tx):
    for peer in known_nodes.copy():
        if peer == meu_url: continue
        try: requests.post(f"{peer}/tx/receive", json=tx, timeout=3)
        except: pass

@app.route('/tx/receive', methods=['POST'])
def receive_transaction_api():
    tx = request.get_json()
    if not tx: return jsonify({"message": "No data"}), 400
    blockchain.current_transactions.append(tx)
    return jsonify({"message": "OK"}), 200

@app.route('/blocks/receive', methods=['POST'])
def receive_block_api():
    block = request.get_json()
    last = blockchain.last_block()
    if block['index'] > last['index'] + 1:
        threading.Thread(target=blockchain.resolve_conflicts, daemon=True).start()
        return jsonify({'message': 'Sync started'}), 202
    if blockchain.valid_proof(last['proof'], block['proof'], block['difficulty']):
        blockchain.chain.append(block); blockchain._save_block(block)
        blockchain.current_transactions = [t for t in blockchain.current_transactions if t['id'] not in {x['id'] for x in block['transactions']}]
        return jsonify({'message': 'Bloco aceito'}), 200
    return jsonify({'message': 'Invalido'}), 400

@app.route('/sync/check', methods=['GET'])
def check_sync_api():
    last = blockchain.last_block()
    return jsonify({'index': last['index'], 'hash': blockchain.hash(last)})

@app.route('/miner/set_address', methods=['POST'])
def set_miner_address_api():
    global miner_address_global
    data = request.get_json() or {}
    addr = data.get("address")
    if addr: miner_address_global = addr; return jsonify({"message": "OK"}), 200
    return jsonify({"message": "Error"}), 400

@app.route('/miner/set_mode', methods=['POST'])
def set_miner_mode_api():
    data = request.get_json()
    if data.get('mode') == 'GPU' and HAS_GPU: blockchain.use_gpu = True
    else: blockchain.use_gpu = False
    return jsonify({"message": "OK"}), 200

@app.route('/miner/stop', methods=['POST'])
def stop_mining_api():
    global mining_active, mining_stop_flag
    if mining_active:
        mining_stop_flag.set()
        with miner_lock: mining_active = False
    return jsonify({"message": "Parado"}), 200

@app.route('/mine', methods=['GET'])
def mine_api():
    global mining_active, miner_address_global, mining_stop_flag, mining_result
    if not miner_address_global: return jsonify({"message": "Sem endereço"}), 400
    with miner_lock:
        if mining_active: return jsonify({"message": "Ocupado"}), 409
        mining_active = True
    
    try:
        last_block = blockchain.last_block()
        proof = -1
        mining_stop_flag.clear(); mining_result.value = -1
        
        if getattr(blockchain, 'use_gpu', False) and HAS_GPU:
            proof = Blockchain._mine_gpu(last_block['proof'], blockchain._calculate_difficulty_for_index(len(blockchain.chain)+1), mining_stop_flag, mining_result)
        else:
            proof = blockchain.proof_of_work(last_block['proof'])
            
        if proof != -1:
            new_block = blockchain.new_block(proof, blockchain.hash(last_block), miner_address_global)
            broadcast_block(new_block)
            return jsonify({"message": "Minerado!", "index": new_block['index']}), 200
        return jsonify({"message": "Parado"}), 200
    finally:
        with miner_lock: mining_active = False

def broadcast_block(block):
    for peer in known_nodes | set(SEED_NODES):
        if peer == meu_url: continue
        try: requests.post(f"{peer}/blocks/receive", json=block, timeout=5)
        except: pass

# --- ROTAS SOLICITADAS ---
@app.route('/dashboard')
def dashboard_visual():
    return render_template('dashboard.html')

@app.route('/miner')
def miner_web():
    return render_template('miner.html')

@app.route('/api/stats', methods=['GET'])
def get_stats():
    last_block = blockchain.last_block()
    return jsonify({
        "hashrate": f"{current_hashrate_global:.2f}",
        "index": last_block['index'],
        "difficulty": last_block.get('difficulty', 1),
        "status": "Mining" if mining_active else "Idle",
        "gpu": "GTX 1060 100% Cuda" if HAS_GPU else "CPU Mode"
    }), 200

def get_my_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); s.connect(("8.8.8.8", 80)); ip = s.getsockname()[0]; s.close(); return ip
    except: return "127.0.0.1"

def load_or_create_node_id():
    if os.path.exists("node_id.txt"): return open("node_id.txt").read().strip()
    node_id = str(uuid4()).replace("-", "")[:16]
    with open("node_id.txt", "w") as f: f.write(node_id)
    return node_id

def auto_sync_checker(blockchain_instance):
    while True:
        try: blockchain_instance.resolve_conflicts()
        except: pass
        time.sleep(60)

# --- APIClient para a GUI ---
class APIClient:
    def __init__(self, base_url): self.base_url = base_url
    def set_base_url(self, new_url): self.base_url = new_url

# --- Cliente Kert-One Core GUI (Versão Final Sem Timer) ---
class KertOneCoreClient(QMainWindow):
    start_mining_signal = pyqtSignal() 
    log_signal = pyqtSignal(str, str)
    chain_viewer_signal = pyqtSignal(str)

    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"Kert-One Core Client ({COIN_NAME})")
        self.setGeometry(100, 100, 1000, 700)
        self.mining_active = False
        self.miner_address = None
        self.wallet_data = None
        self.is_mining_busy = False 
        self.apply_dark_theme()
        self.api_client = APIClient(f"http://127.0.0.1:5001") 
        self.setup_ui()
        self.load_wallet()
        self.chain_viewer_signal.connect(self.chain_viewer.setPlainText)
        self.log_signal.connect(self.update_log_viewer)
        self.start_mining_signal.connect(self.mine_block_via_api)
        self._on_flask_url_ready("http://127.0.0.1:5001")

    def start_continuous_mining(self):
        if self.mining_active: return
        addr = self.get_miner_address()
        if not addr: return
        self.miner_address = addr
        self.mining_active = True
        self.is_mining_busy = False 
        self.mine_single_btn.setEnabled(False)
        self.start_mining_btn.setEnabled(False)
        self.stop_mining_btn.setEnabled(True)
        self.radio_cpu.setEnabled(False)
        self.radio_gpu.setEnabled(False)
        self.status_bar.showMessage(f"Mineração ativa: {self.miner_address}", 0)
        self.log_signal.emit("🚀 Mineração Sequencial Iniciada.", "success")
        self.mine_block_via_api()

    def stop_continuous_mining(self):
        self.mining_active = False
        try: requests.post(f"{meu_url}/miner/stop", timeout=2)
        except: pass
        self.mine_single_btn.setEnabled(True)
        self.start_mining_btn.setEnabled(True)
        self.stop_mining_btn.setEnabled(False)
        self.radio_cpu.setEnabled(True)
        if HAS_GPU: self.radio_gpu.setEnabled(True)
        self.status_bar.showMessage("Parado.", 5000)
        self.log_signal.emit("Mineração interrompida.", "warning")

    def mine_block_via_api(self):
        if not self.mining_active: return
        if self.is_mining_busy: return 
        self.is_mining_busy = True 
        threading.Thread(target=self._mine_async, args=(self.miner_address,)).start()

    def _mine_async(self, miner_address):
        try:
            requests.post(f"{meu_url}/miner/set_address", json={"address": miner_address}, timeout=5)
            response = requests.get(f"{meu_url}/mine", timeout=None)
            if response.status_code == 200:
                data = response.json()
                if "Minerado" in data.get("message", ""):
                    self.log_signal.emit(f"💎 BLOCO ENCONTRADO!", "success")
                    self.check_wallet_balance()
            elif response.status_code == 409: pass 
        except Exception as e:
            self.log_signal.emit(f"Erro no ciclo: {e}", "info")
            time.sleep(1)
        finally:
            self.is_mining_busy = False 
            if self.mining_active:
                time.sleep(0.1) 
                self.start_mining_signal.emit()

    def update_log_viewer(self, message, message_type="info"):
        color_map = {"info": "#a0a0ff", "success": "#66ff66", "error": "#ff6666", "warning": "#ffff66", "default": "#f0f0f0"}
        color = color_map.get(message_type, color_map["default"])
        timestamp = datetime.now().strftime('%H:%M:%S')
        self.log_viewer.append(f'<font color="{color}">[{timestamp}] {message}</font>')

    def apply_dark_theme(self):
        dark_palette = QPalette()
        dark_palette.setColor(QPalette.ColorRole.Window, QColor(45, 45, 45))
        dark_palette.setColor(QPalette.ColorRole.WindowText, QColor(200, 200, 200))
        dark_palette.setColor(QPalette.ColorRole.Base, QColor(30, 30, 30))
        dark_palette.setColor(QPalette.ColorRole.Text, QColor(200, 200, 200))
        dark_palette.setColor(QPalette.ColorRole.Button, QColor(60, 60, 60))
        dark_palette.setColor(QPalette.ColorRole.ButtonText, QColor(200, 200, 200))
        dark_palette.setColor(QPalette.ColorRole.Highlight, QColor(42, 130, 218))
        QApplication.instance().setPalette(dark_palette)
        self.setStyleSheet("QWidget { background-color: rgb(45, 45, 45); color: rgb(200, 200, 200); } QPushButton { background-color: rgb(60, 60, 60); border: 1px solid rgb(80, 80, 80); padding: 8px; border-radius: 5px; } QPushButton:hover { background-color: rgb(80, 80, 80); } QPushButton:pressed { background-color: rgb(100, 100, 100); } QLineEdit, QTextEdit, QPlainTextEdit { background-color: rgb(30, 30, 30); border: 1px solid rgb(60, 60, 60); padding: 5px; border-radius: 3px; } QGroupBox { border: 1px solid rgb(80, 80, 80); margin-top: 10px; padding-top: 15px; } QGroupBox::title { subcontrol-origin: margin; subcontrol-position: top left; padding: 0 5px; color: rgb(150, 150, 255); } QTabWidget::pane { border: 1px solid rgb(60, 60, 60); } QTabBar::tab { background: rgb(55, 55, 55); border: 1px solid rgb(60, 60, 60); padding: 8px; border-bottom: none; } QTabBar::tab:selected { background: rgb(75, 75, 75); border-bottom: none; } #LogViewer { background-color: #202020; color: #f0f0f0; border: none; }")

    def setup_ui(self):
        self.central_widget = QWidget(); self.setCentralWidget(self.central_widget); self.main_layout = QVBoxLayout(self.central_widget)
        self.tabs = QTabWidget(); self.tab_wallet = QWidget(); self.tab_send = QWidget(); self.tab_mine = QWidget(); self.tab_network = QWidget()
        self.tabs.addTab(self.tab_wallet, "Carteira"); self.tabs.addTab(self.tab_send, "Enviar"); self.tabs.addTab(self.tab_mine, "Mineração"); self.tabs.addTab(self.tab_network, "Rede/Blockchain")
        self.main_layout.addWidget(self.tabs)
        self.log_viewer = QTextEdit(); self.log_viewer.setObjectName("LogViewer"); self.log_viewer.setReadOnly(True)
        self.main_layout.addWidget(QLabel("Log de Atividade:")); self.main_layout.addWidget(self.log_viewer, 3)
        self.status_bar = QStatusBar(self); self.setStatusBar(self.status_bar); self.status_bar.showMessage(f"Cliente Kert-One conectado ao nó: {meu_url}", 5000)
        self.setup_wallet_tab(); self.setup_send_tab(); self.setup_mine_tab(); self.setup_network_tab()
        node_info_group = QGroupBox("Informações do Nó"); node_info_layout = QFormLayout(node_info_group)
        self.node_id_label = QLabel(f"<span style='font-weight:bold;'>{node_id[:16]}...</span>"); self.node_url_label = QLabel(f"<span style='font-weight:bold;'>{meu_url}</span>") 
        node_info_layout.addRow("ID do Nó:", self.node_id_label); node_info_layout.addRow("URL do Nó:", self.node_url_label)
        self.main_layout.insertWidget(0, node_info_group)

    @pyqtSlot(str)
    def _on_flask_url_ready(self, url):
        global meu_url; meu_url = url; self.api_client.set_base_url(meu_url); self.update_log_viewer(f"Servidor Flask pronto em: {meu_url}", "success"); self.node_url_label.setText(f"<span style='font-weight:bold;'>{meu_url}</span>"); self.status_bar.showMessage(f"Cliente Kert-One conectado ao nó: {meu_url}", 5000)

    def setup_wallet_tab(self):
        layout = QVBoxLayout(self.tab_wallet); wallet_group = QGroupBox("Carteira Atual"); wallet_layout = QFormLayout(wallet_group)
        self.balance_label = QLabel(f"0.0 {COIN_SYMBOL}"); self.balance_label.setFont(QFont("Arial", 28, QFont.Weight.Bold))
        self.address_label = QLineEdit("N/A"); self.address_label.setReadOnly(True)
        self.public_key_label = QTextEdit("N/A"); self.public_key_label.setReadOnly(True); self.public_key_label.setFixedHeight(80)
        wallet_layout.addRow("Saldo Atual:", self.balance_label); wallet_layout.addRow("Endereço:", self.address_label); wallet_layout.addRow("Chave Pública:", self.public_key_label)
        layout.addWidget(wallet_group); button_layout = QHBoxLayout()
        new_wallet_btn = QPushButton("Criar Nova Carteira"); new_wallet_btn.clicked.connect(self.create_new_wallet)
        load_wallet_btn = QPushButton("Carregar Carteira (client_wallet.json)"); load_wallet_btn.clicked.connect(self.load_wallet)
        check_balance_btn = QPushButton("Atualizar Saldo"); check_balance_btn.clicked.connect(self.check_wallet_balance)
        button_layout.addWidget(new_wallet_btn); button_layout.addWidget(load_wallet_btn); button_layout.addWidget(check_balance_btn); layout.addLayout(button_layout); layout.addStretch(1)

    def create_new_wallet(self):
        wallet_data = create_wallet()
        if wallet_data:
            save_wallet_file(wallet_data, WALLET_FILE); self.wallet_data = wallet_data; self.update_wallet_status(); self.log_signal.emit(f"Nova carteira criada e salva em {WALLET_FILE}.", "success"); QMessageBox.information(self, "Carteira Criada", f"Nova carteira salva com sucesso. Endereço: {wallet_data['address']}"); self.check_wallet_balance()
        else: self.log_signal.emit("Falha ao criar nova carteira.", "error")

    def load_wallet(self):
        self.wallet_data = load_wallet_file(WALLET_FILE)
        if self.wallet_data: self.update_wallet_status(); self.log_signal.emit(f"Carteira carregada com sucesso.", "info"); self.check_wallet_balance()
        else: self.update_wallet_status(); self.log_signal.emit("Arquivo de carteira não encontrado ou corrompido.", "warning")

    def update_wallet_status(self):
        if self.wallet_data:
            self.address_label.setText(self.wallet_data.get('address', 'N/A')); self.public_key_label.setText(self.wallet_data.get('public_key', 'N/A')); self.status_bar.showMessage(f"Carteira carregada: {self.wallet_data['address']}", 5000)
        else:
            self.address_label.setText("N/A"); self.public_key_label.setText("N/A"); self.balance_label.setText("0.0 KRT"); self.status_bar.showMessage("Nenhuma carteira carregada.", 5000)

    def check_wallet_balance(self):
        if not self.wallet_data: self.log_signal.emit("Nenhuma carteira carregada.", "warning"); return
        address = self.wallet_data['address']; threading.Thread(target=self._fetch_balance_async, args=(address,)).start()

    def _fetch_balance_async(self, address):
        try:
            response = requests.get(f"{meu_url}/balance/{address}", timeout=5); response.raise_for_status(); balance_data = response.json(); balance = balance_data.get('balance', 0)
            self.balance_label.setText(f"{balance} {COIN_SYMBOL}"); self.log_signal.emit(f"Saldo atualizado: {balance} {COIN_SYMBOL}", "info")
        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Erro ao conectar ao nó ({meu_url}) ou buscar saldo: {e}", "error"); self.balance_label.setText("Erro de Conexão")

    def setup_send_tab(self):
        layout = QVBoxLayout(self.tab_send); transaction_group = QGroupBox("Nova Transação"); form_layout = QFormLayout(transaction_group)
        self.recipient_input = QLineEdit(); self.amount_input = QLineEdit(); self.fee_input = QLineEdit()
        validator = QDoubleValidator(0.0, 100000000.0, 8, self); validator.setNotation(QDoubleValidator.StandardNotation)
        self.amount_input.setValidator(validator); self.fee_input.setValidator(validator)
        form_layout.addRow("Destinatário (Endereço):", self.recipient_input); form_layout.addRow(f"Valor ({COIN_SYMBOL}):", self.amount_input); form_layout.addRow("Taxa (Fee):", self.fee_input)
        send_btn = QPushButton("Assinar e Enviar Transação"); send_btn.clicked.connect(self.enviar_transacao)
        layout.addWidget(transaction_group); layout.addWidget(send_btn); layout.addStretch(1)

    def enviar_transacao(self):
        if not self.wallet_data: QMessageBox.warning(self, "Aviso", "Nenhuma carteira carregada."); return
        recipient_addr = self.recipient_input.text().strip(); amount_str = self.amount_input.text().strip().replace(',', '.'); fee_str = self.fee_input.text().strip().replace(',', '.')
        if not recipient_addr or not amount_str or not fee_str: QMessageBox.warning(self, "Erro", "Todos os campos são obrigatórios."); return
        try:
            amount = float(amount_str); fee = float(fee_str)
            if amount <= 0 or fee < 0: raise ValueError("Valor ou taxa inválidos.")
            transaction_id = str(uuid4()); amount_fmt = f"{amount:.8f}"; fee_fmt = f"{fee:.8f}"
            tx_data_for_signing = {'sender': self.wallet_data['address'], 'recipient': recipient_addr, 'amount': amount_fmt, 'fee': fee_fmt}
            signature = sign_transaction(self.wallet_data['private_key'], tx_data_for_signing)
            if signature is None: raise Exception("Falha ao assinar a transação.")
            tx_full_data = {'id': transaction_id, 'sender': self.wallet_data['address'], 'recipient': recipient_addr, 'amount': amount_fmt, 'fee': fee_fmt, 'signature': signature, 'public_key': self.wallet_data['public_key'], 'timestamp': time.time()}
            self.log_signal.emit("Enviando transação para o nó...", "info")
            threading.Thread(target=self._send_transaction_async, args=(tx_full_data,), daemon=True).start()
        except ValueError as e: QMessageBox.critical(self, "Erro de Entrada", f"Valor inválido: {e}")
        except Exception as e: self.log_signal.emit(f"Ocorreu um erro inesperado: {e}", "error")

    def _send_transaction_async(self, tx_full_data):
        try:
            response = requests.post(f"{meu_url}/tx/new", json=tx_full_data, timeout=10); response.raise_for_status()
            if response.status_code in [200, 201]: self.log_signal.emit(f"Transação enviada com sucesso: {response.json().get('message')}", "success"); self._clear_transaction_fields(); self.check_wallet_balance() 
            else: self.log_signal.emit(f"Erro ao enviar transação: {response.json().get('error', response.text)}", "error")
        except requests.exceptions.RequestException as e: self.log_signal.emit(f"Taxa é obrigatória ou erro de conexão com o nó ({meu_url}) ao enviar transação: {e}", "error")

    def _clear_transaction_fields(self):
        self.recipient_input.clear(); self.amount_input.clear(); self.fee_input.clear()

    def setup_mine_tab(self):
        layout = QVBoxLayout(self.tab_mine); mine_addr_group = QGroupBox("Carteira de Recompensa"); mine_addr_layout = QHBoxLayout(mine_addr_group)
        self.miner_addr_input = QLineEdit(); self.miner_addr_input.setPlaceholderText("Endereço para receber KERT minerados"); mine_addr_layout.addWidget(self.miner_addr_input); layout.addWidget(mine_addr_group)
        hw_group = QGroupBox("Modo de Mineração (Hardware)"); hw_layout = QHBoxLayout(hw_group)
        self.radio_cpu = QRadioButton("CPU (Multicore)"); self.radio_gpu = QRadioButton("GPU (OpenCL Real)")
        self.radio_cpu.toggled.connect(lambda: self.update_mining_mode("CPU")); self.radio_gpu.toggled.connect(lambda: self.update_mining_mode("GPU"))
        if HAS_GPU: self.radio_gpu.setEnabled(True); self.radio_gpu.setText("GPU (OpenCL Real - DETECTADA)"); self.radio_gpu.setChecked(True) 
        else: self.radio_cpu.setChecked(True); self.radio_gpu.setEnabled(False); self.radio_gpu.setText("GPU (Drivers não encontrados)")
        hw_layout.addWidget(self.radio_cpu); hw_layout.addWidget(self.radio_gpu); layout.addWidget(hw_group)
        mining_control_group = QGroupBox("Controle"); mining_control_layout = QHBoxLayout(mining_control_group)
        self.mine_single_btn = QPushButton("Minerar 1 Bloco"); self.start_mining_btn = QPushButton("Iniciar Mineração Contínua"); self.stop_mining_btn = QPushButton("Parar"); self.stop_mining_btn.setEnabled(False)
        self.mine_single_btn.clicked.connect(self.mine_single_block); self.start_mining_btn.clicked.connect(self.start_continuous_mining); self.stop_mining_btn.clicked.connect(self.stop_continuous_mining)
        mining_control_layout.addWidget(self.mine_single_btn); mining_control_layout.addWidget(self.start_mining_btn); mining_control_layout.addWidget(self.stop_mining_btn); layout.addWidget(mining_control_group); layout.addStretch(1)

    def update_mining_mode(self, mode):
        sender = self.sender()
        if sender.isChecked():
            try: requests.post(f"{meu_url}/miner/set_mode", json={'mode': mode}); self.log_signal.emit(f"Modo de mineração alterado para: {mode}", "info")
            except: self.log_signal.emit("Erro ao alterar modo de mineração.", "error")

    def get_miner_address(self):
        addr = self.miner_addr_input.text().strip()
        if addr: return addr
        if self.wallet_data and 'address' in self.wallet_data: return self.wallet_data['address']
        QMessageBox.warning(self, "Aviso", "Nenhum endereço de mineração fornecido e nenhuma carteira carregada."); return None

    def mine_single_block(self):
        miner_addr = self.get_miner_address()
        if miner_addr: self.log_signal.emit("Iniciando mineração de bloco único...", "info"); threading.Thread(target=self._mine_async, args=(miner_addr,)).start()

    def setup_network_tab(self):
        layout = QVBoxLayout(self.tab_network); chain_group = QGroupBox("Blockchain View"); chain_layout = QVBoxLayout(chain_group)
        self.chain_viewer = QPlainTextEdit(); self.chain_viewer.setReadOnly(True); self.chain_viewer.setPlaceholderText("Clique em 'Ver Blockchain Completa' para carregar os dados do nó.")
        self.view_chain_btn = QPushButton("Ver Blockchain Completa"); self.sync_chain_btn = QPushButton("Sincronizar Blockchain (Consenso)")
        chain_layout.addWidget(self.chain_viewer); chain_layout.addWidget(self.view_chain_btn); chain_layout.addWidget(self.sync_chain_btn)
        self.view_chain_btn.clicked.connect(self.view_blockchain); self.sync_chain_btn.clicked.connect(self.sync_blockchain)
        layout.addWidget(chain_group); network_options_group = QGroupBox("Opções de Rede"); network_options_layout = QHBoxLayout(network_options_group)
        self.register_peer_btn = QPushButton("Registrar Novo Peer"); self.consult_contract_btn = QPushButton("Consultar Contrato Inteligente")
        self.change_token_btn = QPushButton("Ativar Nó Público (Ngrok)") # Botão Atualizado
        self.register_peer_btn.clicked.connect(self.register_peer_dialog); self.consult_contract_btn.clicked.connect(self.consult_contract_dialog); self.change_token_btn.clicked.connect(self.change_ngrok_token)
        network_options_layout.addWidget(self.register_peer_btn); network_options_layout.addWidget(self.consult_contract_btn); network_options_layout.addWidget(self.change_token_btn); layout.addWidget(network_options_group)
        self.open_urls_button = QPushButton("Abrir Portais"); self.open_urls_button.clicked.connect(self.abrir_portais); layout.addWidget(self.open_urls_button); layout.addStretch(1)

    def abrir_portais(self):
        import webbrowser; webbrowser.open(f"http://{meu_ip}:{port}/"); webbrowser.open(f"http://{meu_ip}:{port}/miner"); webbrowser.open("https://kert-one.com/"); self.log_signal.emit("Abrindo portais do Kert-One...", "info")

    def view_blockchain(self):
        self.log_signal.emit("Buscando blockchain completa...", "info"); threading.Thread(target=self._fetch_blockchain_async).start()

    def _fetch_blockchain_async(self):
        try:
            response = requests.get(f"{meu_url}/chain", timeout=10); response.raise_for_status(); chain_data = response.json()
            formatted_chain = json.dumps(chain_data, indent=2); self.chain_viewer_signal.emit(formatted_chain); self.log_signal.emit(f"Blockchain carregada. Comprimento: {len(chain_data['chain'])} blocos.", "success")
        except requests.exceptions.RequestException as e: self.log_signal.emit(f"Erro ao buscar blockchain: {e}", "error"); self.chain_viewer_signal.emit("Erro ao carregar a blockchain.")

    def sync_blockchain(self):
        threading.Thread(target=self._sync_blockchain_async, daemon=True).start()
        
    def _sync_blockchain_async(self):
        while True:
            try:
                self.log_signal.emit("Iniciando sincronização (consenso)...", "info"); response = requests.get(f"{meu_url}/nodes/resolve", timeout=30); response.raise_for_status(); data = response.json()
                if data.get("message") == "Nossa cadeia foi substituída.": self.log_signal.emit("Blockchain sincronizada com sucesso. Cadeia atualizada para a mais longa.", "success"); self.view_blockchain()
                else: self.log_signal.emit("Blockchain já sincronizada ou não houve alteração.", "info")
            except requests.exceptions.RequestException as e: self.log_signal.emit(f"Erro ao sincronizar com o nó: {e}", "error")
            time.sleep(10)

    def register_peer_dialog(self):
        text, ok = QInputDialog.getText(self, 'Registrar Peer', 'Digite a URL completa do novo peer (ex: http://IP:PORTA):')
        if ok and text: self.log_signal.emit(f"Tentando registrar peer: {text}", "info"); threading.Thread(target=self._register_peer_async, args=(text,)).start()
    
    def _register_peer_async(self, node_url):
        try:
            parsed_url = urlparse(node_url); peer_ip = parsed_url.hostname; peer_port = parsed_url.port or 5000 
            if not peer_ip: self.log_signal.emit(f"URL do peer inválida: {node_url}", "error"); return
            payload = {'ip': peer_ip, 'port': peer_port}; response = requests.post(f"{meu_url}/nodes/register", json=payload, timeout=10); response.raise_for_status()
            self.log_signal.emit(f"Peer '{node_url}' registrado com sucesso! Resposta: {response.json()}", "success")
        except requests.exceptions.RequestException as e: self.log_signal.emit(f"Erro ao registrar peer: {e}", "error")

    def consult_contract_dialog(self):
        text, ok = QInputDialog.getText(self, 'Consultar Contrato', 'Digite o endereço do contrato inteligente:')
        if ok and text: self.log_signal.emit(f"Consultando contrato: {text}", "info"); threading.Thread(target=self._consult_contract_async, args=(text,)).start()

    def _consult_contract_async(self, contract_address):
        try:
            response = requests.get(f"{meu_url}/contract/{contract_address}/transactions", timeout=10); response.raise_for_status(); contract_data = response.json(); formatted_data = json.dumps(contract_data, indent=2); self.log_signal.emit(f"Detalhes do Contrato ({contract_address}):\n{formatted_data}", "info")
        except requests.exceptions.HTTPError as e:
            if e.response.status_code == 404: self.log_signal.emit("Contrato não encontrado na blockchain.", "warning")
            else: self.log_signal.emit(f"Erro HTTP ao consultar contrato: {e}", "error")
        except requests.exceptions.RequestException as e: self.log_signal.emit(f"Erro de conexão ao consultar contrato: {e}", "error")

    def change_ngrok_token(self):
        """Abre o diálogo para mudar o token."""
        text, ok = QInputDialog.getText(self, "Configurar Ngrok", "Insira seu novo Ngrok Authtoken:\n(Reinicie o programa após salvar)", QLineEdit.Normal, load_ngrok_token() or "")
        if ok and text:
            save_ngrok_token(text)
            self.log_signal.emit("Token Ngrok salvo! Reinicie o programa para aplicar.", "warning")
            QMessageBox.information(self, "Token Salvo", "O novo token foi salvo. Por favor, feche e abra o programa novamente para conectar.")

# --- Execução Principal ---
def run_server():
    app.run(host='0.0.0.0', port=5001, threaded=True)

if __name__ == "__main__":
    multiprocessing.freeze_support()
    
    # 1. Carrega token se existir (NÃO PEDE MAIS)
    token = load_ngrok_token()

    port = int(os.environ.get('PORT', 5001))

    # 2. Inicia Ngrok (se tiver token salvo)
    try:
        from pyngrok import ngrok, conf
        if token:
            conf.get_default().auth_token = token
            public_url = ngrok.connect(port).public_url
            meu_url = public_url
            print(f"[REDE] 🌍 Seu nó está público em: {meu_url}")
        else:
            raise Exception("Sem token")
    except Exception as e:
        print(f"[NGROK] Modo Local Ativo (Sem Túnel Público). Motivo: {e}")
        meu_ip = get_my_ip()
        meu_url = f"http://{meu_ip}:{port}"
        print(f"[REDE] 🏠 Rodando localmente em: {meu_url}")

    conn = sqlite3.connect(DATABASE, check_same_thread=False)
    node_id_val = load_or_create_node_id()
    blockchain = Blockchain(conn, node_id_val)

    server_thread = threading.Thread(target=run_server, daemon=True)
    server_thread.start()
    time.sleep(2) 

    print("\n[BOOT] 📡 Conectando aos Seeds...")
    for seed in SEED_NODES: known_nodes.add(seed)
    salvar_peers(known_nodes) 
    
    if blockchain.resolve_conflicts(): 
        print("[BOOT] ✅ Sincronizado com sucesso (Modo Checkpoint)!")
    else: 
        print("[BOOT] ⚠️ Sync falhou ou chain local é a maior.")

    threading.Thread(target=auto_sync_checker, args=(blockchain,), daemon=True).start()

    print("[GUI] 🚀 Iniciando Interface...")
    qt_app = QApplication(sys.argv)
    window = KertOneCoreClient()
    window._on_flask_url_ready(f"http://127.0.0.1:{port}")
    window.show()
    sys.exit(qt_app.exec_())
