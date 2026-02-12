import hashlib
import json
import time
import threading
import sqlite3
import os
from uuid import uuid4
from flask import Flask, jsonify, request, send_file, render_template, send_from_directory
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
from web3 import Web3

# --- Configurações ---
DIFFICULTY = 1  # Dificuldade inicial para o bloco Gênese
MINING_REWARD = 50  # Recompensa padrão (será sobrescrita pela lógica de halving)
DATABASE = 'chain.db'
COIN_NAME = "Kert-One"
COIN_SYMBOL = "KERT"
PEERS_FILE = 'peers.json'
WALLET_FILE = "client_wallet.json"
used_proofs = set()
MAX_STORED_PROOFS = 5000

# ================= GENESIS / CONFIG =================
GENESIS_MINER = "KERT-GENESIS"
GENESIS_PROOF = 100
GENESIS_PREVIOUS_HASH = "1"

miner_address = None
is_mining = False
miner_lock = threading.Lock()
tx_lock = threading.Lock()

# --- NÓS SEMENTES ---
SEED_NODES = []
GITHUB_NODES_URL = "https://raw.githubusercontent.com/douglaskert/kert-one/main/nodes.json"

known_nodes = set()
meu_url = None
meu_ip = None
port = None

# --- Persistência de Peers ---
def salvar_peers(peers=None):
    """Salva a lista de peers conhecidos em um arquivo JSON."""
    global known_nodes
    if peers is None:
        peers = known_nodes
    try:
        with open(PEERS_FILE, 'w') as f:
            # Converte para lista e ordena para consistência
            json.dump(sorted(list(peers)), f, indent=2)
        # print(f"[PEERS] Peers salvos: {len(peers)} peers.") # Log reduzido
    except Exception as e:
        print(f"[PEERS ERRO] Falha ao salvar {PEERS_FILE}: {e}")

def carregar_peers():
    """Carrega a lista de peers conhecidos de um arquivo JSON."""
    if not os.path.exists(PEERS_FILE):
        print(f"[PEERS] Arquivo {PEERS_FILE} não encontrado. Iniciando com lista vazia.")
        return set()
    try:
        with open(PEERS_FILE, 'r') as f:
            peers = json.load(f)
            # Filtra apenas strings válidas que começam com http
            valid_peers = {p for p in peers if isinstance(p, str) and p.startswith("http")}
            print(f"[PEERS] {len(valid_peers)} peers carregados de {PEERS_FILE}.")
            return valid_peers
    except json.JSONDecodeError:
        print(f"[ERRO] {PEERS_FILE} está corrompido ou vazio. Recriando.")
        return set()
    except Exception as e:
        print(f"[ERRO] Falha ao carregar peers: {e}")
        return set()

def fetch_github_nodes():
    global known_nodes, meu_url
    try:
        r = requests.get(GITHUB_NODES_URL, timeout=5)
        if r.status_code == 200:
            new_seeds = r.json()
            count = 0
            for seed in new_seeds:
                seed = seed.strip().rstrip('/')
                if seed and seed != meu_url:
                    known_nodes.add(seed)
                    count += 1
            if count > 0:
                save_peers()
                print(f"🚀 [GITHUB] {count} novos nós adicionados da lista oficial!")
    except:
        print("⚠️ [GITHUB] Erro ao buscar lista de nós oficiais.")

def save_peers():
    salvar_peers()

# Inicializa known_nodes
known_nodes = carregar_peers()

def network_loop():
    while True:
        try:
            discover_peers()
            if blockchain:
                blockchain.resolve_conflicts()
        except Exception as e:
            print(f"[NETWORK] Erro no loop de rede: {e}")
        time.sleep(25)

threading.Thread(target=network_loop, daemon=True).start()

def load_peers():
    global known_nodes
    loaded = carregar_peers()
    known_nodes.update(loaded)

PROTOCOL_VERSION = "KERT-CORE-1.0"
PROTOCOL_RULES = {
    "coin_name": COIN_NAME,
    "symbol": COIN_SYMBOL,
    "initial_difficulty": DIFFICULTY,
    "target_block_time": 600,
    "reward_schedule": {
        "1-1200": 50.0,
        "1201-2200": 25.0,
        "2201-4000": 12.5,
        "4001-5500": 6.5,
        "5501-6200": 3.25,
        "6201-20000": 1.25,
        "20001-1000000": 0.03
    }
}

app = Flask(__name__)
node_id = str(uuid4()).replace('-', '')
CORS(app)

# Variáveis globais para mineração contínua
mining_active = False
miner_thread = None
miner_address_global = None 

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# 1️⃣ Rota para o Cartão/Banco
@app.route('/card')
def card_web():
    try:
        return render_template('card.html')
    except Exception as e:
        return f"Erro ao carregar card.html: {e}", 500

# 2️⃣ Rota do Manifest (PWA)
@app.route('/manifest.json')
def manifest():
    try:
        return send_from_directory('templates', 'manifest.json', mimetype='application/json')
    except Exception:
        # Fallback se a pasta templates não existir como esperado
        return jsonify({"name": "Kert One", "short_name": "Kert", "start_url": "/", "display": "standalone"}), 200

# 3️⃣ Rota do Service Worker
@app.route('/sw.js')
def service_worker():
    try:
        return send_from_directory('templates', 'sw.js', mimetype='application/javascript')
    except Exception as e:
        return f"console.log('SW Error: {e}');", 200

# 4️⃣ Rota para Ícones PNG
@app.route('/<path:filename>')
def serve_static(filename):
    if filename.endswith(".png"):
        try:
            return send_from_directory(BASE_DIR, filename, mimetype='image/png')
        except:
            pass
    return "Arquivo não encontrado", 404


@app.route('/nodes/share', methods=['GET'])
def share_nodes():
    return jsonify(list(known_nodes))

# ================= THREADS DE REDE =================

def periodic_network_maintenance():
    while True:
        time.sleep(30)
        try:
            discover_peers()
            if blockchain:
                blockchain.resolve_conflicts()
        except Exception as e:
            print(f"[NET_MAINT_ERR] {e}")

def auto_sync():
    time.sleep(3)
    try:
        if blockchain:
            blockchain.resolve_conflicts()
    except Exception as e:
        print(f"[AUTO_SYNC_ERR] {e}")

threading.Thread(target=periodic_network_maintenance, daemon=True).start()
threading.Thread(target=auto_sync, daemon=True).start()

# --- Classe Blockchain ---
class Blockchain:
    # --- AJUSTE ECONÔMICO PARA PROTEGER O VALOR DA MOEDA ---
    # Alterado de 2016 para 10. 
    # Isso faz a rede recalcular a dificuldade a cada 10 blocos.
    # Se muita gente entrar, fica difícil rápido (escassez).
    # Se muita gente sair, fica fácil rápido (usabilidade).
    ADJUST_INTERVAL = 10 
    TARGET_TIME = 600 # Tempo alvo entre blocos em segundos (10 minutos)
    TARGET_WINDOW = ADJUST_INTERVAL * TARGET_TIME

    def _calculate_difficulty_for_index(self, target_block_index):
        # Evita recalcular se a cadeia for muito curta
        if len(self.chain) < self.ADJUST_INTERVAL:
            return DIFFICULTY

        # Só ajusta em múltiplos do intervalo (agora a cada 10 blocos)
        if target_block_index % self.ADJUST_INTERVAL != 0:
            return self.chain[-1].get('difficulty', DIFFICULTY)

        try:
            last_block = self.chain[-1]
            # Correção de índice: pega o bloco do início do período de ajuste
            first_block_index = len(self.chain) - self.ADJUST_INTERVAL
            if first_block_index < 0: first_block_index = 0
            first_block = self.chain[first_block_index]

            actual_time = last_block['timestamp'] - first_block['timestamp']
            
            # PROTEÇÃO CONTRA TRAVAMENTO:
            if actual_time < 1: 
                actual_time = 1
            
            expected_time = self.ADJUST_INTERVAL * self.TARGET_TIME

            # Limite estilo Bitcoin (¼x a 4x) para evitar oscilação extrema
            actual_time = max(expected_time // 4, min(actual_time, expected_time * 4))

            old_diff = last_block['difficulty']
            new_diff = int(old_diff * (expected_time / actual_time))

            print(f"[DIFF ADJUST] Antiga={old_diff} Nova={new_diff} (Tempo real: {actual_time}s)")

            # LIMITA O MÁXIMO A 64 (tamanho do hash SHA-256)
            # Isso evita que a dificuldade peça mais zeros do que existem no hash
            return min(64, max(1, new_diff))
            
        except Exception as e:
            print(f"[DIFF ERROR] Erro ao calcular dificuldade: {e}. Mantendo anterior.")
            return self.chain[-1].get('difficulty', DIFFICULTY)

    def __init__(self, conn, node_id):
        self.conn = conn
        self.node_id = node_id
        self._init_db()
        self.chain = self._load_chain()
        self.current_transactions = []

        if not self.chain:
            print("[BOOT] 📡 Inserindo Gênese Base 500.0...")
            self._create_genesis_block()
        
        # Garante cálculo inicial correto
        if self.chain:
            self.difficulty = self._calculate_difficulty_for_index(len(self.chain))
        else:
            self.difficulty = DIFFICULTY
            
        print(f"[BOOT] Dificuldade inicial da cadeia: {self.difficulty}")

    def _create_genesis_block(self):
        genesis_block = {
            'index': 1,
            'previous_hash': '1',
            'proof': 100,
            'timestamp': 1700000000.0,
            'miner': 'genesis',
            'transactions': [],
            'difficulty': 1,
            'protocol_value': 500.0
        }
        self.chain.append(genesis_block)
        self._save_block(genesis_block)

    @staticmethod
    def hash(block):
        # Garante que protocol_value entre na conta do Hash
        block_core = {
            "index": block["index"],
            "previous_hash": block["previous_hash"],
            "proof": block["proof"],
            "timestamp": block["timestamp"],
            "miner": block["miner"],
            "difficulty": block.get("difficulty", 1),
            "protocol_value": block.get("protocol_value", 0),
            "transactions": block["transactions"]
        }

        block_string = json.dumps(
            block_core, 
            sort_keys=True, 
            separators=(',', ':')
        ).encode()

        return hashlib.sha256(block_string).hexdigest()

    def calculate_protocol_value_for_block(self, block_index, difficulty):
        BASE_VALUE = 500.0  # 🔒 Valor mínimo da moeda

        if block_index == 1:
            return BASE_VALUE

        COST_PER_MILLION_HASHES = 0.02
        hashes_needed = 16 ** difficulty

        # custo de produzir UM bloco
        block_cost = (hashes_needed / 1_000_000) * COST_PER_MILLION_HASHES

        # custo distribuído por moeda gerada
        reward = self._get_mining_reward(block_index)
        if reward <= 0:
            return BASE_VALUE

        cost_per_coin = block_cost / reward
        protocol_value = BASE_VALUE + cost_per_coin
    
        return round(protocol_value, 8)

    def new_block(self, proof, previous_hash, miner, initial_difficulty=None, timestamp=None):
        """Cria um novo bloco e o adiciona à cadeia."""
        block_index = len(self.chain) + 1
        reward = self._get_mining_reward(block_index)
        
        difficulty = self._calculate_difficulty_for_index(block_index) if initial_difficulty is None else initial_difficulty

        mining_reward_tx = {
            'id': str(uuid4()), 'sender': '0', 'recipient': miner,
            'amount': f"{reward:.8f}", 'fee': f"{0.0:.8f}", 'signature': '', 'public_key': ''
        }
        
        transactions_for_block = list(self.current_transactions)
        transactions_for_block.insert(0, mining_reward_tx)

        protocol_value = self.calculate_protocol_value_for_block(block_index, difficulty)

        block = {
            'index': block_index,
            'previous_hash': previous_hash,
            'proof': proof,
            'timestamp': float(timestamp) if timestamp is not None else time.time(),
            'miner': miner,
            'transactions': transactions_for_block,
            'difficulty': difficulty,
            'protocol_value': protocol_value
        }

        self.chain.append(block)
        self._save_block(block)

        # Limpa transações pendentes que foram mineradas
        mined_tx_ids = {tx['id'] for tx in transactions_for_block if tx['sender'] != '0'}
        self.current_transactions = [tx for tx in self.current_transactions if tx['id'] not in mined_tx_ids]
        
        print(f"[BLOCK] Novo bloco {block['index']} forjado. Protocol Value: {protocol_value}")
        return block
        
    def is_duplicate_transaction(self, new_tx):
        for tx in self.current_transactions:
            if tx.get('id') == new_tx.get('id'):
                return True
            # Verificação profunda para evitar spam idêntico
            if (tx.get('sender') == new_tx.get('sender') and
                tx.get('recipient') == new_tx.get('recipient') and
                tx.get('amount') == new_tx.get('amount') and
                tx.get('fee') == new_tx.get('fee') and
                tx.get('signature') == new_tx.get('signature')):
                return True
        
        try:
            c = self.conn.cursor()
            c.execute("SELECT 1 FROM txs WHERE id=?", (new_tx.get('id'),))
            if c.fetchone():
                return True
        except Exception:
            pass
        return False

    @staticmethod
    def custom_asic_resistant_hash(data_bytes, nonce):
        """Função de hash resistente a ASICs."""
        raw = data_bytes + str(nonce).encode()
        h1 = hashlib.sha256(raw).digest()
        h2 = hashlib.sha512(h1).digest()
        h3 = hashlib.blake2b(h2).digest()
        return hashlib.sha256(h3).hexdigest()

    def _init_db(self):
        c = self.conn.cursor()
        c.execute('''
            CREATE TABLE IF NOT EXISTS blocks(
                index_ INTEGER PRIMARY KEY,
                previous_hash TEXT,
                proof INTEGER,
                timestamp REAL,
                miner TEXT,
                difficulty INTEGER,
                protocol_value REAL
            )
        ''')
        
        # Migração segura
        c.execute("PRAGMA table_info(blocks)")
        columns = [col[1] for col in c.fetchall()]
        if 'protocol_value' not in columns:
            print("[DB MIGRATION] Adicionando coluna protocol_value...")
            c.execute("ALTER TABLE blocks ADD COLUMN protocol_value REAL DEFAULT 0")

        c.execute('''
            CREATE TABLE IF NOT EXISTS txs(
                id TEXT PRIMARY KEY,
                sender TEXT,
                recipient TEXT,
                amount TEXT,
                fee TEXT,
                signature TEXT,
                block_index INTEGER,
                public_key TEXT
            )
        ''')
        self.conn.commit()

    def _load_chain(self):
        try:
            c = self.conn.cursor()
            c.execute("SELECT index_, previous_hash, proof, timestamp, miner, difficulty, protocol_value FROM blocks ORDER BY index_")
            chain = []
            for idx, prev, proof, ts, miner, difficulty, p_val in c.fetchall():
                c.execute("SELECT id, sender, recipient, amount, fee, signature, public_key FROM txs WHERE block_index=?", (idx,))
                txs = []
                for r in c.fetchall():
                    txs.append(dict(id=r[0], sender=r[1], recipient=r[2], 
                                    amount=r[3], fee=r[4], signature=r[5], public_key=r[6]))
                block = {
                    'index': idx,
                    'previous_hash': prev,
                    'proof': proof,
                    'timestamp': ts,
                    'miner': miner,
                    'transactions': txs,
                    'difficulty': difficulty,
                    'protocol_value': p_val
                }
                chain.append(block)
            return chain
        except Exception as e:
            print(f"[DB ERROR] Falha ao carregar chain: {e}")
            return []

    def _save_block(self, block):
        try:
            c = self.conn.cursor()
            c.execute("""
                INSERT INTO blocks 
                (index_, previous_hash, proof, timestamp, miner, difficulty, protocol_value) 
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (
                block['index'], 
                block['previous_hash'], 
                block['proof'],
                block['timestamp'], 
                block['miner'], 
                block['difficulty'],
                block.get('protocol_value', 0)
            ))
            
            for t in block['transactions']:
                c.execute("INSERT INTO txs VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                          (t['id'], t['sender'], t['recipient'], t['amount'],
                           t['fee'], t['signature'], block['index'], t.get('public_key', '')))
            self.conn.commit()
        except sqlite3.IntegrityError:
            print(f"[DB WARN] Tentativa de salvar bloco duplicado {block['index']}")
        except Exception as e:
            print(f"[DB ERROR] Falha ao salvar bloco: {e}")

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
            base_reward = 0.03
            reward = base_reward / (2 ** halvings)
            return max(reward, 0.0)

    def last_block(self):
        return self.chain[-1] if self.chain else None

    def proof_of_work(self, last_proof):
        """
        Encontra uma prova de trabalho. 
        OTIMIZADO: Removeu o sleep exagerado.
        """
        difficulty_for_pow = self._calculate_difficulty_for_index(len(self.chain) + 1)
        proof = 0
        print(f"⛏️  [MINER] Iniciando mineração. Dificuldade: {difficulty_for_pow} zeros")
        start_time = time.time()
        
        while not self.valid_proof(last_proof, proof, difficulty_for_pow):
            global mining_active
            if not mining_active:
                print("[Miner] 🛑 Mineração parada manualmente.")
                return -1
            
            # --- OTIMIZAÇÃO CRÍTICA ---
            # Sleep(0) permite troca de contexto sem atrasar 1ms a cada hash
            # Aumentado intervalo para 10000 hashes para performance
            if proof % 10000 == 0:
                time.sleep(0) 
            
            # Verifica se outro nó já achou o bloco (evita trabalho inútil)
            # Mas não verifica a CADA hash, apenas a cada 10000
            if proof % 10000 == 0:
                current_last = self.last_block()
                if current_last and current_last['proof'] != last_proof:
                    print("[Miner] ⚠️ Outro bloco chegou na rede. Reiniciando.")
                    return -1

            # Log de progresso a cada 30 segundos
            if time.time() - start_time > 30:
                hash_rate = proof / (time.time() - start_time)
                print(f"🔨 [MINER] Hashrate: {hash_rate:.2f} H/s | Tentativa: {proof}")
                start_time = time.time()
                
            proof += 1
            
        print(f"💎 [MINER] Bloco encontrado! Proof: {proof}")
        return proof

    @staticmethod
    def valid_proof(last_proof, proof, difficulty):
        guess = f"{last_proof}{proof}".encode()
        guess_hash = Blockchain.custom_asic_resistant_hash(guess, proof)
        return guess_hash[:difficulty] == "0" * difficulty

    def valid_chain(self, chain):
        if not chain:
            return False

        # Verifica Gênese (Básico)
        if chain[0]['index'] != 1 or chain[0]['proof'] != 100:
            return False

        for idx in range(1, len(chain)):
            prev = chain[idx - 1]
            curr = chain[idx]

            if curr['previous_hash'] != self.hash(prev):
                print(f"[VAL_CHAIN] Hash anterior incorreto no bloco {curr['index']}.")
                return False

            block_declared_difficulty = curr.get('difficulty', DIFFICULTY)
            if not self.valid_proof(prev['proof'], curr['proof'], block_declared_difficulty):
                print(f"[VAL_CHAIN] PoW inválido no bloco {curr['index']}.")
                return False

        return True

    def get_total_difficulty(self, chain_to_check):
        total_difficulty = 0
        for block in chain_to_check:
            total_difficulty += block.get('difficulty', DIFFICULTY)
        return total_difficulty

    def resolve_conflicts(self):
        global known_nodes

        neighbors = list(known_nodes)
        new_chain = None

        current_total_difficulty = self.get_total_difficulty(self.chain)
        current_length = len(self.chain)

        peers_to_remove = set()

        for node_url in neighbors:
            if node_url == meu_url:
                continue

            try:
                # Timeout curto para não travar
                response = requests.get(f"{node_url}/chain", timeout=5)

                if response.status_code == 200:
                    data = response.json()
                    peer_chain = data.get("chain")

                    if peer_chain:
                        peer_difficulty = self.get_total_difficulty(peer_chain)
                        peer_length = len(peer_chain)

                        if self.valid_chain(peer_chain):
                            if (peer_difficulty > current_total_difficulty or 
                               (peer_difficulty == current_total_difficulty and peer_length > current_length)):
                                print(f"[CONSENSO] ✔ Nova melhor cadeia em {node_url}")
                                current_total_difficulty = peer_difficulty
                                current_length = peer_length
                                new_chain = peer_chain
            except Exception:
                # Não remove peers só por um erro de conexão temporário
                pass

        if new_chain:
            print("[CONSENSO] 🔄 Substituindo cadeia local...")
            self.chain = new_chain
            self._rebuild_db_from_chain()
            print("[CONSENSO] ✅ Sincronizado.")
            return True

        return False

    def _rebuild_db_from_chain(self):
        try:
            c = self.conn.cursor()
            c.execute("DELETE FROM txs")
            c.execute("DELETE FROM blocks")
            
            # Re-salva usando a função que já temos
            for block in self.chain:
                self._save_block(block)
                
            self.conn.commit()
        except Exception as e:
            print(f"[REBUILD ERRO] {e}")

    def balance(self, address):
        bal = 0.0
        mined_tx_ids = set() 

        for block in self.chain:
            for t in block['transactions']:
                mined_tx_ids.add(t['id'])
                if t['sender'] == address:
                    bal -= (float(t['amount']) + float(t['fee']))
                if t['recipient'] == address:
                    bal += float(t['amount'])
        
        for t in self.current_transactions:
            if t['id'] in mined_tx_ids:
                continue 

            if t['sender'] == address:
                bal -= (float(t['amount']) + float(t['fee']))
            if t['recipient'] == address:
                bal += float(t['amount'])
                
        return bal

# --- Funções de Criptografia e Carteira ---
def gerar_endereco(public_key_hex):
    try:
        if isinstance(public_key_hex, str) and public_key_hex.startswith("04"):
            public_key_hex = public_key_hex[2:] 
        public_key_bytes = bytes.fromhex(public_key_hex)
        return hashlib.sha256(public_key_bytes).hexdigest()[:40]
    except ValueError as e: 
        print(f"[ERRO] Falha ao gerar endereço: {e}")
        return None

def sign_transaction(private_key_hex, tx_data):
    sk = SigningKey.from_string(bytes.fromhex(private_key_hex), curve=SECP256k1)
    message_data = {
        'amount':    tx_data['amount'],
        'fee':       tx_data['fee'],
        'recipient': tx_data['recipient'],
        'sender':    tx_data['sender']
    }
    message_json = json.dumps(message_data, sort_keys=True, separators=(',',':')).encode('utf-8')
    message_hash = hashlib.sha256(message_json).digest()
    return sk.sign_digest(message_hash).hex()

# --- Flask Endpoints (do nó) ---
@app.route('/', methods=['GET'])
def index_web():
    return "Kert-One Blockchain Node is running!"

@app.route('/miner')
def miner_web():
    return "Kert-One Miner Interface (via Web)"

@app.route('/chain', methods=['GET'])
def chain_api():
    response = {
        'chain': blockchain.chain,
        'length': len(blockchain.chain),
        'pending_transactions': blockchain.current_transactions,
        'coin_name': COIN_NAME,
        'coin_symbol': COIN_SYMBOL,
        'node_id': node_id
    }
    return jsonify(response), 200

@app.route('/wallet/admin_send', methods=['POST'])
def admin_send_coins():
    try:
        data = request.get_json()
        private_key = data.get('private_key')
        recipient = data.get('recipient')
        amount = data.get('amount')

        if not private_key or not recipient or not amount:
            return jsonify({'erro': 'Faltam dados'}), 400

        sk = SigningKey.from_string(bytes.fromhex(private_key), curve=SECP256k1)
        vk = sk.get_verifying_key()
        public_key = "04" + vk.to_string().hex()
        sender_addr = gerar_endereco(public_key)
 
        saldo_admin = blockchain.balance(sender_addr)
        if saldo_admin < float(amount):
            return jsonify({'erro': f'Saldo insuficiente no Admin. Tem: {saldo_admin}'}), 400

        tx = {
            'id': str(uuid4()),
            'sender': sender_addr,
            'recipient': recipient,
            'amount': f"{float(amount):.8f}",
            'fee': "0.00001000",
            'public_key': public_key,
            'timestamp': time.time(),
            'signature': ''
        }
        tx['signature'] = sign_transaction(private_key, tx)

        with tx_lock:
             blockchain.current_transactions.append(tx)
        
        broadcast_tx_to_peers(tx)

        print(f"[ADMIN] Enviado {amount} KERT para {recipient}")
        return jsonify({'sucesso': True, 'tx_id': tx['id']}), 200

    except Exception as e:
        print(f"[ERRO ADMIN] {e}")
        return jsonify({'erro': str(e)}), 500
        
@app.route('/nodes/register', methods=['POST'])
def register_nodes_api():
    data = request.get_json()
    new_node_url = data.get('url')

    if not new_node_url:
        return jsonify({"message": "URL do nó inválida/ausente."}), 400

    if not (new_node_url.startswith('http://') or new_node_url.startswith('https://')):
        return jsonify({"message": "URL do nó inválida."}), 400

    new_node_url = new_node_url.rstrip('/')

    if new_node_url != meu_url:
        if new_node_url not in known_nodes:
            known_nodes.add(new_node_url)
            salvar_peers(known_nodes)
            print(f"[INFO] Peer {new_node_url} registrado.")
    
    return jsonify({
        "message": f"Peer {new_node_url} registrado ou atualizado.",
        "known_peers": list(known_nodes)
    }), 200

@app.route('/nodes', methods=['GET'])
def get_nodes_api():
    return jsonify({'nodes': list(known_nodes)}), 200

@app.route('/nodes/resolve', methods=['GET'])
def resolve_api():
    replaced = blockchain.resolve_conflicts()
    if replaced:
        response = {'message': 'Nossa cadeia foi substituída pela mais longa e válida.'}
    else:
        response = {'message': 'Nossa cadeia é a mais longa ou nenhuma cadeia mais longa/válida foi encontrada.'}
    return jsonify(response), 200

@app.route('/balance/<addr>', methods=['GET'])
def balance_api(addr):
    return jsonify({
        'address': addr,
        'balance': blockchain.balance(addr),
        'coin_name': COIN_NAME,
        'coin_symbol': COIN_SYMBOL
    }), 200

@app.route('/transactions/pending', methods=['GET'])
def pending_transactions():
    return jsonify(blockchain.current_transactions), 200

@app.route('/tx/new', methods=['POST'])
def new_transaction_api():
    raw_values = request.get_json(silent=True)
    if raw_values is None:
        return jsonify({'message': 'Erro: JSON inválido.'}), 400
    
    values = raw_values
    required = ['id', 'sender', 'recipient', 'amount', 'fee', 'public_key', 'signature']
    if not all(k in values for k in required):
        missing = [k for k in required if k not in values]
        return jsonify({'message': f'Valores ausentes: {", ".join(missing)}'}), 400

    try:
        amount_float = float(values['amount'])
        fee_float = float(values['fee'])
        
        if fee_float <= 0:
            return jsonify({'message': 'Taxa deve ser maior que 0.'}), 400

        transaction = {
            'id': values['id'],
            'sender': values['sender'],
            'recipient': values['recipient'],
            'amount': f"{amount_float:.8f}",
            'fee': f"{fee_float:.8f}",
            'public_key': values['public_key'],
            'signature': values['signature'],
            'timestamp': values.get('timestamp', time.time())
        }
    except ValueError as e:
        return jsonify({'message': f'Erro em dados numéricos: {e}'}), 400

    try:
        if not verify_signature(transaction['public_key'], transaction['signature'], transaction):
            return jsonify({'message': 'Assinatura inválida.'}), 400
    except Exception as e:
        return jsonify({'message': f'Erro na validação de assinatura: {e}'}), 400

    with tx_lock:
        temp_tx_for_duplicate_check = {
            'sender': transaction['sender'],
            'recipient': transaction['recipient'],
            'amount': transaction['amount'],
            'fee': transaction['fee'],
            'id': transaction.get('id')
        }
        
        if blockchain.is_duplicate_transaction(temp_tx_for_duplicate_check):
            return jsonify({'message': 'Transação duplicada detectada.'}), 200

        current_balance = blockchain.balance(transaction['sender'])
        required_amount = float(transaction['amount']) + float(transaction['fee'])
        
        if current_balance < required_amount:
            return jsonify({'message': f'Saldo insuficiente. Saldo: {current_balance}'}), 400

        blockchain.current_transactions.append(transaction)
        print(f"[SUCESSO] Transação {transaction['id']} adicionada.")

    broadcast_tx_to_peers(transaction)

    response = {
        'message': f'Transação {transaction["id"]} adicionada à fila.',
        'transaction_id': transaction['id']
    }
    return jsonify(response), 201

def broadcast_tx_to_peers(tx):
    print(f"[Broadcast TX] Enviando transação {tx.get('id')} para {len(known_nodes)} peers.")
    for peer in list(known_nodes):
        if peer == meu_url: continue
        try:
            requests.post(f"{peer}/tx/receive", json=tx, timeout=1) # Timeout bem curto
        except:
            pass 

@app.route('/tx/receive', methods=['POST'])
def receive_transaction_api():
    tx_data = request.get_json()
    if not tx_data:
        return jsonify({"message": "Nenhum dado recebido."}), 400

    # Lógica simplificada de recebimento: se já tem, ignora. Se não, valida e adiciona.
    try:
        temp_check = {'id': tx_data.get('id')}
        if blockchain.is_duplicate_transaction(temp_check):
            return jsonify({'message': 'Transação já conhecida.'}), 200
        
        # Aqui deveria ter validação de assinatura novamente para segurança,
        # mas para performance em "receive" confiamos parcialmente ou validamos rápido.
        # Vamos manter a validação:
        if not verify_signature(tx_data['public_key'], tx_data['signature'], tx_data):
             return jsonify({'message': 'Assinatura inválida.'}), 400
             
        blockchain.current_transactions.append(tx_data)
        return jsonify({"message": "Transação recebida."}), 200
    except Exception as e:
        return jsonify({'message': f'Erro: {e}'}), 400


# --- Configurações Web3 (Mantidas) ---
ETH_RPC_URL = "https://rpc.ankr.com/eth" 
WKERT_CONTRACT = "0x12f40def427635c896d65bf5934d04654da29190"
ADMIN_PRIVATE_KEY_ETH = "e7b2b7720bb46798bfa65ccd06502d657acc4e3954a7b0149993952d1cfe0098"
ADMIN_KERT_ADDR = "3e128f4c1045cb2cf7ad48215c421824207b7905"

w3 = Web3(Web3.HTTPProvider(ETH_RPC_URL))
        
def verify_signature(public_key_hex, signature_hex, tx_data):
    try:
        if not public_key_hex or not signature_hex:
            return False

        pk_hex = public_key_hex
        if isinstance(pk_hex, str) and pk_hex.startswith("04") and len(pk_hex) == 130:
            pk_hex = pk_hex[2:]

        amount_to_verify = f"{float(tx_data['amount']):.8f}"
        fee_to_verify = f"{float(tx_data['fee']):.8f}"

        prepared_message_data = {
            'amount': amount_to_verify,
            'fee': fee_to_verify,
            'recipient': tx_data['recipient'],
            'sender': tx_data['sender']
        }
        
        message = json.dumps(prepared_message_data, sort_keys=True, separators=(',', ':')).encode('utf-8')

        message_hash_bytes = hashlib.sha256(message).digest()
        signature_bytes = bytes.fromhex(signature_hex)

        vk = VerifyingKey.from_string(bytes.fromhex(pk_hex), curve=SECP256k1)
        vk.verify_digest(signature_bytes, message_hash_bytes)
        return True
    except Exception as e:
        print(f"Erro assinatura: {e}")
        return False
        
@app.route('/blocks/receive', methods=['POST'])
def receive_block_api():
    block_data = request.get_json()
    if not block_data:
        return jsonify({"message": "Nenhum dado recebido."}), 400

    # Lógica básica para aceitar bloco rapidamente se for válido
    try:
        last_block = blockchain.last_block()
        if block_data['index'] <= last_block['index']:
            return jsonify({'message': 'Bloco antigo.'}), 200
        
        if block_data['index'] == last_block['index'] + 1:
            if block_data['previous_hash'] == blockchain.hash(last_block):
                # Aceita
                blockchain.chain.append(block_data)
                blockchain._save_block(block_data)
                
                # Limpa TXs
                mined_ids = {t.get('id') for t in block_data['transactions']}
                blockchain.current_transactions = [tx for tx in blockchain.current_transactions if tx.get('id') not in mined_ids]
                
                return jsonify({'message': 'Bloco aceito.'}), 200
            else:
                return jsonify({'message': 'Hash anterior incorreto.'}), 400
        else:
            # Bloco muito à frente, aciona sync
            threading.Thread(target=blockchain.resolve_conflicts, daemon=True).start()
            return jsonify({'message': 'Bloco futuro. Sincronizando.'}), 202
            
    except Exception as e:
        return jsonify({'message': f'Erro: {e}'}), 400

@app.route('/sync/check', methods=['GET'])
def check_sync_api():
    last = blockchain.last_block()
    if not last:
        return jsonify({'message': 'Blockchain não inicializada.'}), 500
    local_hash = blockchain.hash(last)
    return jsonify({
        'index': last['index'],
        'hash': local_hash,
        'miner': last['miner']
    })

@app.route('/miner/set_address', methods=['POST'])
def set_miner_address_api():
    global miner_address_global
    data = request.get_json()
    address = data.get('address')
    if not address:
        return jsonify({"message": "Endereço ausente."}), 400
    miner_address_global = address
    print(f"[MINER] Endereço definido: {miner_address_global}")
    return jsonify({"message": f"Definido: {miner_address_global}"}), 200

@app.route('/mine', methods=['GET'])
def mine_api():
    global mining_active, miner_address_global
    if not miner_address_global:
        return jsonify({"message": "Defina o endereço primeiro (/miner/set_address)."}), 400

    if mining_active:
        return jsonify({"message": "Mineração contínua já rodando."}), 409

    last_block = blockchain.last_block()
    if not last_block:
        return jsonify({"message": "Blockchain não inicializada."}), 500

    # Ativa flag temporária para o loop funcionar
    original_state = mining_active
    mining_active = True 
    
    proof = blockchain.proof_of_work(last_block['proof'])
    
    mining_active = original_state # Restaura

    if proof == -1:
        return jsonify({"message": "Mineração abortada."}), 200

    previous_hash = blockchain.hash(last_block)
    new_block = blockchain.new_block(proof, previous_hash, miner_address_global)

    broadcast_block(new_block)

    return jsonify({
        'message': "Novo bloco forjado!",
        'index': new_block['index'],
        'proof': new_block['proof']
    }), 200

@app.route('/miner/start_continuous', methods=['GET'])
def start_continuous_mining():
    global mining_active, miner_thread, miner_address_global
    if mining_active:
        return jsonify({"message": "Já está rodando."}), 400
    
    if not miner_address_global:
        return jsonify({"message": "Defina o endereço primeiro."}), 400

    mining_active = True
    miner_thread = threading.Thread(target=_continuous_mine, daemon=True)
    miner_thread.start()
    return jsonify({"message": "Mineração iniciada."}), 200

@app.route('/miner/stop_continuous', methods=['GET'])
def stop_continuous_mining():
    global mining_active
    if not mining_active:
        return jsonify({"message": "Não está rodando."}), 400
    
    mining_active = False
    return jsonify({"message": "Parando mineração..."}), 200

def _continuous_mine():
    global mining_active, blockchain, miner_address_global
    print("[MINER] Thread iniciada.")
    while mining_active:
        try:
            last_block = blockchain.last_block()
            if not last_block:
                time.sleep(1)
                continue

            last_proof = last_block['proof']
            
            # Chama a função otimizada
            proof = blockchain.proof_of_work(last_proof)

            if proof == -1:
                # Alguém achou antes ou parou
                time.sleep(0.5)
                continue

            previous_hash = blockchain.hash(last_block)
            new_block = blockchain.new_block(proof, previous_hash, miner_address_global)
            
            broadcast_block(new_block)
            
        except Exception as e:
            print(f"[MINER ERROR] {e}")
            time.sleep(2)
            
    print("[MINER] Thread parada.")

def broadcast_block(block):
    print(f"[BROADCAST] Enviando bloco #{block['index']}...")
    for peer in list(known_nodes):
        if peer == meu_url: continue
        try:
            requests.post(f"{peer}/blocks/receive", json=block, timeout=2)
        except:
            pass

def discover_peers():
    global known_nodes, meu_url
    if len(known_nodes) < 1:
        load_peers()
        fetch_github_nodes()

    peers_snapshot = list(known_nodes)
    for peer in peers_snapshot:
        if peer == meu_url: continue
        try:
            r = requests.get(f"{peer}/nodes", timeout=1)
            if r.status_code == 200:
                remote_nodes = r.json().get("nodes", [])
                for n in remote_nodes:
                    if n != meu_url and n not in known_nodes:
                        known_nodes.add(n)
        except:
            pass
    save_peers()

def get_my_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except:
        return "127.0.0.1"

def load_or_create_node_id(filename="node_id.txt"):
    if os.path.exists(filename):
        with open(filename, "r") as f:
            return f.read().strip()
    else:
        new_id = str(uuid4()).replace("-", "")[:16]
        with open(filename, "w") as f:
            f.write(new_id)
        return new_id

def auto_sync_checker(blockchain_instance):
    while True:
        try:
            comparar_ultimos_blocos(blockchain_instance)
        except Exception as e:
            print(f"[SYNC_CHECKER ERROR] {e}")
        time.sleep(60)

def comparar_ultimos_blocos(blockchain_instance):
    if blockchain_instance is None or blockchain_instance.last_block() is None:
        return

    local_block = blockchain_instance.last_block()
    local_hash = blockchain_instance.hash(local_block)

    for peer in list(known_nodes):
        if peer == meu_url: continue
        try:
            resp = requests.get(f"{peer}/chain", timeout=5)
            data = resp.json()
            peer_chain = data.get("chain")
            if not peer_chain: continue

            peer_last = peer_chain[-1]
            peer_index = peer_last["index"]
            peer_hash = blockchain_instance.hash(peer_last)

            if peer_index > local_block['index'] or (peer_index == local_block['index'] and peer_hash != local_hash):
                print(f"[SYNC] Diferença detectada com {peer}. Rodando consenso...")
                blockchain_instance.resolve_conflicts()
                break
        except:
            pass

# --- Execução Principal ---
def run_server():
    global blockchain, meu_ip, meu_url, port

    port = int(os.environ.get('PORT', 5001))

    # Aumentado timeout do sqlite para evitar "database locked"
    conn = sqlite3.connect(DATABASE, check_same_thread=False, timeout=10)
    node_id_val = load_or_create_node_id()
    blockchain = Blockchain(conn, node_id_val)

    meu_ip = get_my_ip()
    public_url = os.environ.get("PUBLIC_URL")
 
    if public_url:
        meu_url = public_url.rstrip('/')
        print(f"[INFO] 🌍 URL pública: {meu_url}")
    else:
        meu_url = f"http://{meu_ip}:{port}"
        print(f"[INFO] URL local: {meu_url}")

    known_nodes.discard(meu_url)

    # Inicia threads auxiliares
    threading.Thread(target=discover_peers, daemon=True).start()
    threading.Thread(target=auto_sync_checker, args=(blockchain,), daemon=True).start()

    print(f"[INFO] 🚀 Nó rodando na porta {port}")
    app.run(host='0.0.0.0', port=port, threaded=True)

 
if __name__ == "__main__":
    run_server()
