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

# --- Configurações ---  
DIFFICULTY = 1 # Dificuldade inicial para o bloco Gênese
MINING_REWARD = 50 # Recompensa padrão (será sobrescrita pela lógica de halving)
DATABASE = 'chain.db'
COIN_NAME = "Kert-One"
COIN_SYMBOL = "KERT"
PEERS_FILE = 'peers.json'
WALLET_FILE = "client_wallet.json" # Caminho para o arquivo da carteira do cliente - mantido para compatibilidade, mas não usado pela GUI
used_proofs = set()
MAX_STORED_PROOFS = 5000
# ================= GENESIS / CONFIG =================
GENESIS_MINER = "KERT-GENESIS"          # miner fixo para o bloco 1
GENESIS_PROOF = 100
GENESIS_PREVIOUS_HASH = "1"

miner_address = None
is_mining = False
miner_lock = threading.Lock()
tx_lock = threading.Lock() # <--- ADICIONE ISTO

# --- NÓS SEMENTES (Mantenha a variável mesmo que use o GitHub) ---
SEED_NODES = [] 
GITHUB_NODES_URL = "https://raw.githubusercontent.com/douglaskert/kert-one/main/nodes.json"

def fetch_github_nodes():
    global known_nodes
    try:
        r = requests.get(GITHUB_NODES_URL, timeout=5)
        if r.status_code == 200:
            new_seeds = r.json()
            for seed in new_seeds:
                seed = seed.strip()
                if seed and seed != meu_url:
                    known_nodes.add(seed)
            
            # ADICIONE ESTA LINHA AQUI EMBAIXO:
            save_peers() 
            print("🚀 [GITHUB] Lista salva em peers.json!")
    except:
        print("⚠️ [GITHUB] Erro ao buscar/salvar.")

def save_peers():
    global known_nodes
    try:
        with open(PEERS_FILE, 'w') as f:
            json.dump(sorted(list(known_nodes)), f, indent=2)
        print(f"[PEERS] {len(known_nodes)} peers salvos em {PEERS_FILE}.")
    except Exception as e:
        print(f"[PEERS ERRO] Falha ao salvar {PEERS_FILE}: {e}")


def network_loop():
    while True:
        try:
            discover_peers()
            blockchain.resolve_conflicts()
        except Exception as e:
            print(f"[NETWORK] Erro: {e}")
        time.sleep(25)

threading.Thread(target=network_loop, daemon=True).start()


def load_peers():
    """Carrega peers SEM sobrescrever os atuais"""
    if not os.path.exists(PEERS_FILE):
        return
    try:
        with open(PEERS_FILE, 'r') as f:
            peers = json.load(f)
            for p in peers:
                if isinstance(p, str) and p.startswith("http"):
                    known_nodes.add(p)
        print(f"[PEERS] {len(known_nodes)} peers ativos.")
    except Exception as e:
        print(f"[PEERS] erro ao carregar: {e}")


# --- Na função discover_peers ou no início do programa ---
# Chame fetch_external_seeds() logo após carregar o peers.json
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
miner_address_global = None # Endereço para onde as recompensas de mineração serão enviadas

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
    except Exception as e:
        return f"Erro ao carregar manifest.json: {e}", 500


# 3️⃣ Rota do Service Worker
@app.route('/sw.js')
def service_worker():
    try:
        return send_from_directory('templates', 'sw.js', mimetype='application/javascript')
    except Exception as e:
        return f"Erro ao carregar sw.js: {e}", 500


# 4️⃣ Rota para Ícones PNG
@app.route('/<path:filename>')
def serve_static(filename):
    if filename.endswith(".png"):
        return send_from_directory(BASE_DIR, filename, mimetype='image/png')
    return "Arquivo não encontrado", 404

# --- Funções de Persistência de Peers ---
def salvar_peers(peers):
    """Salva a lista de peers conhecidos em um arquivo JSON."""
    with open(PEERS_FILE, 'w') as f:
        json.dump(list(peers), f)
    print(f"[PEERS] Peers salvos: {len(peers)} peers.")

def carregar_peers():
    """Carrega a lista de peers conhecidos de um arquivo JSON."""
    if not os.path.exists(PEERS_FILE):
        print(f"[PEERS] Arquivo {PEERS_FILE} não encontrado. Iniciando com lista vazia.")
        return []
    with open(PEERS_FILE, 'r') as f:
        try:
            peers = json.load(f)
            print(f"[PEERS] {len(peers)} peers carregados de {PEERS_FILE}.")
            return peers
        except json.JSONDecodeError:
            print(f"[ERRO] {PEERS_FILE} está corrompido ou vazio. Recriando.")
            return []

known_nodes = set(carregar_peers())

blockchain = None
meu_url = None # Definido no main
meu_ip = None # Definido no main
port = None # Definido no main

@app.route('/nodes/share', methods=['GET'])
def share_nodes():
    return jsonify(list(known_nodes))

def _create_official_genesis(self):
        """Cria o bloco Gênese hardcoded para ser IDÊNTICO ao do servidor oficial."""
        genesis_block = {
            'index': 1,
            'previous_hash': '1',
            'proof': 100,
            'timestamp': 1700000000.0, # <--- DATA EXATA DO SEEND (Não mude!)
            'miner': 'genesis',
            'transactions': [],
            'difficulty': 1,
            'protocol_value': 500.0  # <--- CORRIGIDO: DE 0 PARA 500.0
        }
        
        # Salva sem passar pela validação (pois é o Gênese)
        self.chain.append(genesis_block)
        self._save_block(genesis_block)
        print("[BOOT] Gênese oficial criado (Valor Base 500.0).")
# ================= THREADS DE REDE =================

def periodic_network_maintenance():
    while True:
        time.sleep(30)
        try:
            discover_peers()              # função global correta
            blockchain.resolve_conflicts()
        except Exception as e:
            print(f"[NET_MAINT_ERR] {e}")

def auto_sync():
    time.sleep(3)
    try:
        blockchain.resolve_conflicts()
    except Exception as e:
        print(f"[AUTO_SYNC_ERR] {e}")

threading.Thread(target=periodic_network_maintenance, daemon=True).start()
threading.Thread(target=auto_sync, daemon=True).start()

# CÓDIGO PARA O SERVIDOR SEEND (Sugestão de melhoria)
@app.route('/chain/chunk', methods=['GET'])
def chain_chunk_api():
    try:
        start = int(request.args.get('start', 0))
        end = int(request.args.get('end', len(blockchain.chain)))
        # Limita para não travar o servidor (ex: máx 1000 blocos por vez)
        if end - start > 1000: end = start + 1000
        
        chunk = blockchain.chain[start:end]
        return jsonify({'chain': chunk, 'start': start, 'end': end, 'total': len(blockchain.chain)}), 200
    except:
        return jsonify({'error': 'Invalid params'}), 400

# --- Classe Blockchain ---
class Blockchain:
    ADJUST_INTERVAL = 10
    TARGET_TIME = 600 # Tempo alvo entre blocos em segundos (10 minutos)
    TARGET_WINDOW = ADJUST_INTERVAL * TARGET_TIME

    def _calculate_difficulty_for_index(self, target_block_index):

        # Só ajusta em múltiplos de 2016
        if target_block_index % self.ADJUST_INTERVAL != 0:
            return self.chain[-1].get('difficulty', DIFFICULTY)

        if len(self.chain) < self.ADJUST_INTERVAL:
            return DIFFICULTY
    
        last_block = self.chain[-1]
        first_block = self.chain[-self.ADJUST_INTERVAL]

        actual_time = last_block['timestamp'] - first_block['timestamp']
        expected_time = self.ADJUST_INTERVAL * self.TARGET_TIME

        # Limite estilo Bitcoin (¼x a 4x)
        actual_time = max(expected_time // 4, min(actual_time, expected_time * 4))

        old_diff = last_block['difficulty']
        new_diff = int(old_diff * (expected_time / actual_time))

        print(f"[DIFF BITCOIN] antiga={old_diff} nova={new_diff}")

        return max(1, new_diff)

    def __init__(self, conn, node_id):
        self.conn = conn
        self.node_id = node_id
        self._init_db()
        self.chain = self._load_chain()
        self.current_transactions = []

        if not self.chain:
            print("[BOOT] 📡 Inserindo Gênese Base 500.0...")
            genesis_block = {
                'index': 1,
                'previous_hash': '1',
                'proof': 100,
                'timestamp': 1700000000.0,
                'miner': 'genesis',
                'transactions': [],
                'difficulty': 1,
                'protocol_value': 500.0 # <--- ERA 0, AGORA É 500 (IGUAL AO SERVER)
            }
            self.chain.append(genesis_block)
            self._save_block(genesis_block)
            
        self.difficulty = self._calculate_difficulty_for_index(len(self.chain))
        print(f"[BOOT] Dificuldade inicial da cadeia: {self.difficulty}")

    @staticmethod
    def hash(block):
        # Garante que protocol_value entre na conta do Hash
        block_core = {
            "index": block["index"],
            "previous_hash": block["previous_hash"],
            "proof": block["proof"],
            "timestamp": block["timestamp"],
            "miner": block["miner"],
            "difficulty": block.get("difficulty", 1), # Garante campo
            "protocol_value": block.get("protocol_value", 0), # <--- CRÍTICO
            "transactions": block["transactions"]
        }

        # Ordena as chaves para garantir que o hash seja sempre o mesmo
        block_string = json.dumps(
            block_core, 
            sort_keys=True, 
            separators=(',', ':')
        ).encode()

        return hashlib.sha256(block_string).hexdigest()

    def get_protocol_price(self):
        """
        Retorna o preço atual baseado no custo de computação.
        NOTA: Calcula o valor REAL para exibição, mesmo que a blockchain esteja gravando 0.
        """
        # Pega a dificuldade atual
        difficulty = self._calculate_difficulty_for_index(len(self.chain) + 1)
        
        # Fórmula do custo
        hashes_needed = 16 ** difficulty
        COST_PER_MILLION_HASHES = 0.02  # Custo de energia/hardware estimado
        
        block_cost = (hashes_needed / 1_000_000) * COST_PER_MILLION_HASHES
        
        reward = self._get_mining_reward(len(self.chain) + 1)
        
        if reward == 0:
            return 0.0
            
        # Preço por moeda = Custo do Bloco / Quantidade de Moedas ganhas
        price_per_coin = block_cost / reward
        
        # Retorna com alta precisão (6 casas decimais)
        return round(price_per_coin, 8)


    def calculate_protocol_value_for_block(self, block_index, difficulty):

        BASE_VALUE = 500.0  # 🔒 Valor mínimo da moeda

        # Bloco gênese já nasce com o valor base
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

        # 💰 VALOR FINAL = BASE + CUSTO
        protocol_value = BASE_VALUE + cost_per_coin
    
        return round(protocol_value, 8)

    
    def new_block(self, proof, previous_hash, miner, initial_difficulty=None, timestamp=None):
        """Cria um novo bloco e o adiciona à cadeia."""
        block_index = len(self.chain) + 1
        reward = self._get_mining_reward(block_index)
        
        difficulty = self._calculate_difficulty_for_index(block_index) if initial_difficulty is None else initial_difficulty

        # Adiciona a transação de recompensa (coinbase) ao início das transações do bloco
        mining_reward_tx = {
            'id': str(uuid4()), 'sender': '0', 'recipient': miner,
            'amount': f"{reward:.8f}", 'fee': f"{0.0:.8f}", 'signature': '', 'public_key': ''
        }
        
        # Cria uma cópia das transações pendentes para o novo bloco
        transactions_for_block = list(self.current_transactions)
        transactions_for_block.insert(0, mining_reward_tx) # Insere a recompensa

        protocol_value = self.calculate_protocol_value_for_block(block_index, difficulty)

        # REMOVIDA DUPLICIDADE 'miner' (apenas uma ocorrência)
        block = {
            'index': block_index,
            'previous_hash': previous_hash,
            'proof': proof,
            'timestamp': float(timestamp) if timestamp is not None else time.time(),
            'miner': miner,
            'transactions': transactions_for_block,
            'difficulty': difficulty,
            'protocol_value': protocol_value   # 🔒 AGORA É CONSENSO
        }

        self.chain.append(block)

        self._save_block(block) # Salva o novo bloco no DB

        # Remove as transações que foram incluídas no bloco da lista de transações pendentes
        mined_tx_ids = {tx['id'] for tx in transactions_for_block if tx['sender'] != '0'}
        self.current_transactions = [tx for tx in self.current_transactions if tx['id'] not in mined_tx_ids]
        print(f"[BLOCK] Novo bloco {block['index']} forjado com {len(transactions_for_block)} transações.")
        
        return block
        
    def is_duplicate_transaction(self, new_tx):
        """Verifica se uma transação já está na fila de transações pendentes ou em um bloco minerado."""
        # Verificar transações pendentes
        for tx in self.current_transactions:
            if tx.get('id') == new_tx.get('id'):
                print(f"[DUPLICIDADE] Transação {new_tx.get('id')} já pendente.")
                return True
            # Verificação mais robusta para transações sem ID (embora todas devam ter)
            if (tx.get('sender') == new_tx.get('sender') and
                tx.get('recipient') == new_tx.get('recipient') and
                tx.get('amount') == new_tx.get('amount') and
                tx.get('fee') == new_tx.get('fee') and
                tx.get('signature') == new_tx.get('signature')):
                print(f"[DUPLICIDADE] Detectada transação pendente quase idêntica (sender={new_tx.get('sender')}, amount={new_tx.get('amount')}).")
                return True
        
        # Verificar transações já mineradas
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM txs WHERE id=?", (new_tx.get('id'),))
        if c.fetchone():
            print(f"[DUPLICIDADE] Transação {new_tx.get('id')} já minerada.")
            return True
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
        """Inicializa o esquema do banco de dados SQLite com suporte a protocol_value."""
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
        
        # 🔥 MIGRAÇÃO AUTOMÁTICA (Adiciona a coluna se não existir)
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
        """Carrega a cadeia de blocos do banco de dados."""
        c = self.conn.cursor()
        # Agora selecionamos também o protocol_value
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
                'protocol_value': p_val # Carrega o valor
            }
            chain.append(block)
        return chain


    def new_block(self, proof, previous_hash, miner, initial_difficulty=None, timestamp=None):
        """Cria um novo bloco e o adiciona à cadeia."""
        block_index = len(self.chain) + 1
        reward = self._get_mining_reward(block_index)
        
        difficulty = self._calculate_difficulty_for_index(block_index) if initial_difficulty is None else initial_difficulty

        # Adiciona a transação de recompensa (coinbase) ao início das transações do bloco
        mining_reward_tx = {
            'id': str(uuid4()), 'sender': '0', 'recipient': miner,
            'amount': f"{reward:.8f}", 'fee': f"{0.0:.8f}", 'signature': '', 'public_key': ''
        }
        
        # Cria uma cópia das transações pendentes para o novo bloco
        transactions_for_block = list(self.current_transactions)
        transactions_for_block.insert(0, mining_reward_tx) # Insere a recompensa

        protocol_value = self.calculate_protocol_value_for_block(block_index, difficulty)

        # REMOVIDA DUPLICIDADE 'miner' (apenas uma ocorrência)
        block = {
            'index': block_index,
            'previous_hash': previous_hash,
            'proof': proof,
            'timestamp': float(timestamp) if timestamp is not None else time.time(),
            'miner': miner,
            'transactions': transactions_for_block,
            'difficulty': difficulty,
            'protocol_value': protocol_value   # 🔒 AGORA É CONSENSO
        }

        self.chain.append(block)

        self._save_block(block) # Salva o novo bloco no DB

        # Remove as transações que foram incluídas no bloco da lista de transações pendentes
        mined_tx_ids = {tx['id'] for tx in transactions_for_block if tx['sender'] != '0'}
        self.current_transactions = [tx for tx in self.current_transactions if tx['id'] not in mined_tx_ids]
        print(f"[BLOCK] Novo bloco {block['index']} forjado com {len(transactions_for_block)} transações.")
        
        return block

    def _save_block(self, block):
        """Salva um bloco e suas transações no banco de dados."""
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
            block.get('protocol_value', 0) # Salva o valor do protocolo
        ))
        
        for t in block['transactions']:
            c.execute("INSERT INTO txs VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                      (t['id'], t['sender'], t['recipient'], t['amount'],
                       t['fee'], t['signature'], block['index'], t.get('public_key', '')))
        self.conn.commit()

    def new_tx(self, sender, recipient, amount_str, fee_str, signature, public_key):
        """Adiciona uma nova transação à lista de transações pendentes.
           amount_str e fee_str já devem ser strings formatadas."""
        tx = {
            'id': str(uuid4()), 'sender': sender, 'recipient': recipient,
            'amount': amount_str, 'fee': fee_str, 'signature': signature, 'public_key': public_key
        }
        if self.is_duplicate_transaction(tx):
            print(f"[TX] Transação {tx.get('id', '')} já pendente ou minerada. Ignorando.")
            return -1
        
        self.current_transactions.append(tx)
        print(f"[TX] Nova transação adicionada: {tx['id']}")
        return self.last_block()['index'] + 1 if self.chain else 1

    def _get_mining_reward(self, block_index):
        """Calcula a recompensa de mineração com base no índice do bloco (halving)."""
        if block_index <= 1200:
            return 50.0
        elif block_index <= 2200:
            return 25.0
        elif block_index <= 4000:
            return 12.5
        elif block_index <= 5500:
            return 6.5
        elif block_index <= 6200:
            return 3.25
        elif block_index <= 20000:
            return 1.25
        elif block_index <= 1000000:
            return 0.03
        else:
            halvings = (block_index - 1000000) // 2100000
            base_reward = 0.03
            reward = base_reward / (2 ** halvings)
            return max(reward, 0.0)

    def last_block(self):
        """Retorna o último bloco da cadeia."""
        return self.chain[-1] if self.chain else None

    def proof_of_work(self, last_proof):
        """
        Encontra uma prova de trabalho. 
        OTIMIZADO: Libera a CPU periodicamente para não travar o Flask.
        """
        difficulty_for_pow = self._calculate_difficulty_for_index(len(self.chain) + 1)
        proof = 0
        print(f"⛏️  [MINER] Iniciando mineração. Dificuldade: {difficulty_for_pow}")
        start_time = time.time()
        
        while not self.valid_proof(last_proof, proof, difficulty_for_pow):
            global mining_active
            if not mining_active:
                print("[Miner] 🛑 Mineração parada manualmente.")
                return -1
            
            # --- CORREÇÃO CRÍTICA AQUI ---
            # A cada 1000 hashes, dorme 1ms para o Flask processar requisições de rede
            if proof % 1000 == 0:
                time.sleep(0.001) 
            
            # Verifica se outro nó já achou o bloco (evita trabalho inútil)
            if self.last_block()['proof'] != last_proof:
                print("[Miner] ⚠️ Outro bloco chegou na rede. Reiniciando mineração.")
                return -1

            # Log de progresso a cada 10 segundos
            if time.time() - start_time > 10:
                hash_rate = proof / (time.time() - start_time)
                print(f"🔨 [MINER] Hashrate: {hash_rate:.2f} H/s | Tentativa: {proof}")
                start_time = time.time() # Reseta timer do log para não floodar
                
            proof += 1
            
        print(f"💎 [MINER] Bloco encontrado! Proof: {proof}")
        return proof

    @staticmethod
    def valid_proof(last_proof, proof, difficulty):
        """
        Valida se um dado hash de prova satisfaz os requisitos de dificuldade.
        """
        guess = f"{last_proof}{proof}".encode()
        guess_hash = Blockchain.custom_asic_resistant_hash(guess, proof)
        return guess_hash[:difficulty] == "0" * difficulty

    def tx_already_mined(self, tx_id):
        """Verifica se uma transação com o dado ID já foi minerada em algum bloco."""
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM txs WHERE id=?", (tx_id,))
        return c.fetchone() is not None

    def valid_chain(self, chain):
        """
        Determina se uma dada cadeia de blocos é válida.
        Verifica hashes, provas de trabalho, transações, dificuldade
        E VALIDA O PROTOCOL VALUE COM TOLERÂNCIA (CONSENSO ECONÔMICO).
        """
        if not chain:
            print("[VAL_CHAIN_ERRO] Cadeia vazia.")
            return False

        # Bloco Gênese
        if chain[0]['index'] != 1 or chain[0]['previous_hash'] != '1' or chain[0]['proof'] != 100:
            print("[VAL_CHAIN_ERRO] Bloco Gênese inválido.")
            return False

        for idx in range(1, len(chain)):
            prev = chain[idx - 1]
            curr = chain[idx]

            # Hash anterior
            if curr['previous_hash'] != self.hash(prev):
                print(f"[VAL_CHAIN_ERRO] Hash anterior incorreto no bloco {curr['index']}.")
                return False

            # PoW
            block_declared_difficulty = curr.get('difficulty', DIFFICULTY)
            if not self.valid_proof(prev['proof'], curr['proof'], block_declared_difficulty):
                print(f"[VAL_CHAIN_ERRO] Proof of Work inválido no bloco {curr['index']}.")
                return False

            # 🔥 PROTOCOL VALUE COM TOLERÂNCIA
            expected_protocol_value = float(self.calculate_protocol_value_for_block(
                curr['index'],
                block_declared_difficulty
            ))

            try:
                peer_protocol_value = float(curr.get('protocol_value', 0.0))
            except:
                peer_protocol_value = 0.0

            if abs(peer_protocol_value - expected_protocol_value) > 1e-6:
                print(f"[VAL_CHAIN_ERRO] Protocol Value inválido no bloco {curr['index']}. "
                      f"Esperado: {expected_protocol_value}, Obtido: {peer_protocol_value}")
                return False

            # Validação das transações
            for tx in curr.get('transactions', []):
                if tx['sender'] == '0':
                    if tx['recipient'] != curr['miner']:
                        print(f"[VAL_CHAIN_ERRO] TX de recompensa inválida no bloco {curr['index']}.")
                        return False

                    expected_reward = self._get_mining_reward(curr['index'])
                    if abs(float(tx['amount']) - expected_reward) > 1e-6:
                        print(f"[VAL_CHAIN_ERRO] Valor de recompensa incorreto no bloco {curr['index']}.")
                        return False
                    continue

                try:
                    pk = tx.get('public_key', '')
                    if not pk:
                        print(f"[VAL_CHAIN_ERRO] TX sem public_key no bloco {curr['index']}.")
                        return False

                    if isinstance(pk, str) and pk.startswith('04') and len(pk) == 130:
                        pk = pk[2:]

                    derived_address = hashlib.sha256(bytes.fromhex(pk)).hexdigest()[:40]
                    if derived_address != tx['sender']:
                        print(f"[VAL_CHAIN_ERRO] Endereço inválido na TX {tx.get('id', '<no-id>')}.")
                        return False

                    amount_to_verify = f"{float(tx['amount']):.8f}"
                    fee_to_verify = f"{float(tx['fee']):.8f}"

                    tx_copy_for_signature = {
                        'amount': amount_to_verify,
                        'fee': fee_to_verify,
                        'recipient': tx['recipient'],
                        'sender': tx['sender']
                    }

                    message = json.dumps(tx_copy_for_signature, sort_keys=True, separators=(",", ":")).encode()
                    vk = VerifyingKey.from_string(bytes.fromhex(pk), curve=SECP256k1)
                    vk.verify_digest(bytes.fromhex(tx['signature']), hashlib.sha256(message).digest())

                except BadSignatureError:
                    print(f"[VAL_CHAIN_ERRO] Assinatura inválida na TX {tx.get('id', '<no-id>')}.")
                    return False
                except Exception as e:
                    print(f"[VAL_CHAIN_ERRO] Erro na TX {tx.get('id', '<no-id>')}: {e}")
                    return False

        return True

    def get_total_difficulty(self, chain_to_check):
        """Calcula a dificuldade acumulada de uma cadeia."""
        total_difficulty = 0
        for block in chain_to_check:
            total_difficulty += block.get('difficulty', DIFFICULTY)
        return total_difficulty

    def resolve_conflicts(self):
        neighbors = list(known_nodes)
        new_chain = None

        my_total_difficulty = self.get_total_difficulty(self.chain)

        print(f"[CONSENSO] Verificando {len(neighbors)} vizinhos...")
        print(f"[CONSENSO] Minha dificuldade acumulada: {my_total_difficulty}")

        for node_url in neighbors:
            if node_url == meu_url:
                continue

            try:
                response = requests.get(f"{node_url}/chain", timeout=20)

                if response.status_code != 200:
                    continue

                data = response.json()
                peer_chain = data.get("chain")

                if not peer_chain:
                    continue
    
                if not self.valid_chain(peer_chain):
                    print(f"[CONSENSO] Cadeia inválida de {node_url}")
                    continue

                peer_total_difficulty = self.get_total_difficulty(peer_chain)

                print(f"[CONSENSO] {node_url} dificuldade acumulada: {peer_total_difficulty}")

                # 🔥 REGRA REAL DE CONSENSO (Bitcoin-like)
                if peer_total_difficulty > my_total_difficulty:
                    print(f"[CONSENSO] Nova cadeia mais forte encontrada em {node_url}")
                    new_chain = peer_chain
                    my_total_difficulty = peer_total_difficulty

            except Exception as e:
                continue

        if new_chain:
            print("[CONSENSO] 🔄 Atualizando cadeia local...")
            self.chain = new_chain
            self._rebuild_db_from_chain()
            print(f"[CONSENSO] ✅ Sincronizado no bloco {len(self.chain)}")
            return True

        print("[CONSENSO] 🔒 Nenhuma cadeia superior encontrada.")
        return False

    def _rebuild_db_from_chain(self):
        print("[REBUILD] Reconstruindo dados locais...")
        try:
            c = self.conn.cursor()
            c.execute("DELETE FROM txs")
            c.execute("DELETE FROM blocks")

            for block in self.chain:
                c.execute("""
                    INSERT INTO blocks
                    (index_, previous_hash, proof, timestamp, miner, difficulty, protocol_value)
                   VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (
                    block['index'], block['previous_hash'], block['proof'],
                    block['timestamp'], block['miner'], block.get('difficulty', 1),
                    block.get('protocol_value', 0.0)
                ))

                for tx in block['transactions']:
                    # MUDANÇA AQUI: Adicionado "OR IGNORE" para evitar o erro de ID duplicado
                    c.execute("""
                        INSERT OR IGNORE INTO txs
                        (id, sender, recipient, amount, fee, signature, block_index, public_key)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                        tx['id'], tx['sender'], tx['recipient'], tx['amount'],
                        tx['fee'], tx['signature'], block['index'], tx.get('public_key', '')
                    ))

            self.conn.commit()
            print("[REBUILD] OK")
        except Exception as e:
            print(f"[REBUILD ERRO] {e}")

    def balance(self, address):
        """Calcula o saldo ignorando transações pendentes que já foram mineradas."""
        bal = 0.0
        mined_tx_ids = set() # Guarda os IDs que já estão na blockchain

        # 1. Soma tudo que já está gravado nos Blocos (Confirmado)
        for block in self.chain:
            for t in block['transactions']:
                mined_tx_ids.add(t['id']) # Marca esse ID como processado
                
                if t['sender'] == address:
                    bal -= (float(t['amount']) + float(t['fee']))
                if t['recipient'] == address:
                    bal += float(t['amount'])
        
        # 2. Soma o que está Pendente (MAS verifica se já não foi processado antes)
        for t in self.current_transactions:
            # --- AQUI ESTÁ A CORREÇÃO ---
            if t['id'] in mined_tx_ids:
                continue # Se já está no bloco, ignora aqui para não contar duas vezes!
            # -----------------------------

            if t['sender'] == address:
                bal -= (float(t['amount']) + float(t['fee']))
            if t['recipient'] == address:
                bal += float(t['amount'])
                
        return bal

# --- Funções de Criptografia e Carteira ---
def gerar_endereco(public_key_hex):
    """Gera um endereço de carteira a partir de uma chave pública hexadecimal."""
    try:
        if isinstance(public_key_hex, str) and public_key_hex.startswith("04"):
            public_key_hex = public_key_hex[2:] 
        public_key_bytes = bytes.fromhex(public_key_hex)
        return hashlib.sha256(public_key_bytes).hexdigest()[:40]
    except ValueError as e: 
        print(f"[ERRO] Falha ao gerar endereço: {e}")
        return None

def get_block_reward(height):
    initial_reward = 10
    halving_interval = 1000

    halvings = height // halving_interval
    reward = initial_reward / (2 ** halvings)

    return max(reward, 0.1)


@app.route('/coin/value', methods=['GET'])
def coin_value_api():
    # Pega o valor real matemático do último bloco
    if not blockchain.chain:
        price = 500.0
    else:
        last_block = blockchain.last_block()
        price = float(last_block.get('protocol_value', 0.0))

    # Lógica de Exibição: 
    # Se o valor matemático for menor que o piso (500), somamos para visualização
    # Isso garante que a moeda nunca pareça valer "0"
    if price < 500.0:
        display_price = 500.0 + price
    else:
        display_price = price

    return jsonify({
        "coin": COIN_SYMBOL,
        "protocol_value": price,             # Valor real do banco de dados
        "protocol_value_display": f"{display_price:.2f}", # Valor para exibir na tela
        "unit": "USD"
    }), 200


def sign_transaction(private_key_hex, tx_data):
    """
    Assina uma transação com a chave privada ECDSA (SECP256k1).
    tx_data deve ter: 'sender', 'recipient', 'amount' (string), 'fee' (string).
    Retorna a assinatura em hex.
    """
    sk = SigningKey.from_string(bytes.fromhex(private_key_hex), curve=SECP256k1)

    message_data = {
        'amount':    tx_data['amount'],
        'fee':       tx_data['fee'],
        'recipient': tx_data['recipient'],
        'sender':    tx_data['sender']
    }

    message_json = json.dumps(
        message_data,
        sort_keys=True,
        separators=(',',':')
    ).encode('utf-8')

    message_hash = hashlib.sha256(message_json).digest()
    return sk.sign_digest(message_hash).hex()

def create_wallet():
    """Cria e retorna dados de uma nova carteira."""
    private_key_obj = SigningKey.generate(curve=SECP256k1)
    public_key_obj = private_key_obj.get_verifying_key()
    private_key_hex = private_key_obj.to_string().hex()
    public_key_hex = "04" + public_key_obj.to_string().hex()
    address = gerar_endereco(public_key_hex)

    if address is None:
        print("[ERRO] Falha ao criar carteira: Endereço não pôde ser gerado.")
        return None

    return {
        'private_key': private_key_hex,
        'public_key': public_key_hex,
        'address': address
    }

def load_wallet_file(filepath):
    """Carrega dados da carteira de um arquivo JSON."""
    if os.path.exists(filepath):
        try:
            with open(filepath, 'r') as f:
                wallet_data = json.load(f)
                if 'public_key' in wallet_data:
                    derived_addr_check = gerar_endereco(wallet_data['public_key'])
                    if derived_addr_check and derived_addr_check != wallet_data.get('address'):
                        print(f"[WALLET] Endereço na carteira desatualizado. Atualizando de {wallet_data.get('address')} para {derived_addr_check}")
                        wallet_data['address'] = derived_addr_check
                        with open(filepath, "w") as fw:
                            json.dump(wallet_data, fw, indent=4)
                return wallet_data
        except (json.JSONDecodeError, FileNotFoundError) as e:
            print(f"[ERRO] Falha ao carregar carteira de {filepath}: {e}")
            return None
    return None

def save_wallet_file(wallet_data, filepath):
    """Salva dados da carteira em um arquivo JSON."""
    try:
        with open(filepath, 'w') as f:
            json.dump(wallet_data, f, indent=4)
        print(f"[WALLET] Carteira salva em {filepath}.")
    except Exception as e:
        print(f"[ERRO] Falha ao salvar carteira em {filepath}: {e}")

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

# --- ADICIONE ISTO NO FINAL DO SEU KERT.PY (Antes do if __name__) ---

@app.route('/wallet/admin_send', methods=['POST'])
def admin_send_coins():
    """Endpoint exclusivo para o PHP mandar moedas usando a chave privada"""
    try:
        data = request.get_json()
        private_key = data.get('private_key') # Chave mestra que vem do PHP
        recipient = data.get('recipient')
        amount = data.get('amount')

        if not private_key or not recipient or not amount:
            return jsonify({'erro': 'Faltam dados'}), 400

        # 1. Recupera a carteira a partir da chave privada
        sk = SigningKey.from_string(bytes.fromhex(private_key), curve=SECP256k1)
        vk = sk.get_verifying_key()
        public_key = "04" + vk.to_string().hex()
        sender_addr = gerar_endereco(public_key)
 
        # 2. Verifica Saldo do Admin
        saldo_admin = blockchain.balance(sender_addr)
        if saldo_admin < float(amount):
            return jsonify({'erro': f'Saldo insuficiente no Admin. Tem: {saldo_admin}'}), 400

        # 3. Cria a Transação
        tx = {
            'id': str(uuid4()),
            'sender': sender_addr,
            'recipient': recipient,
            'amount': f"{float(amount):.8f}",
            'fee': "0.00001000", # Taxa baixa para o sistema
            'public_key': public_key,
            'timestamp': time.time(),
            'signature': ''
        }

        # 4. Assina
        tx['signature'] = sign_transaction(private_key, tx)

        # 5. Adiciona na Blockchain e Espalha
        blockchain.current_transactions.append(tx)
        broadcast_tx_to_peers(tx)

        print(f"[ADMIN] Enviado {amount} KERT para {recipient}")
        return jsonify({'sucesso': True, 'tx_id': tx['id']}), 200

    except Exception as e:
        print(f"[ERRO ADMIN] {e}")
        return jsonify({'erro': str(e)}), 500
        
@app.route('/nodes/register', methods=['POST'])
def register_nodes_api():
    """
    Registra um novo nó na lista de peers conhecidos.
    Espera a URL completa do nó no payload.
    """
    data = request.get_json()
    new_node_url = data.get('url') # Agora espera a URL completa

    if not new_node_url:
        print(f"[ERRO 400] URL do nó ausente na requisição de registro.")
        return jsonify({"message": "URL do nó inválida/ausente."}), 400

    # Validação básica da URL
    if not (new_node_url.startswith('http://') or new_node_url.startswith('https://')):
        print(f"[ERRO 400] URL do nó inválida: {new_node_url}. Deve começar com http:// ou https://")
        return jsonify({"message": "URL do nó inválida. Deve começar com http:// ou https://."}), 400

    if new_node_url != meu_url:
        if new_node_url not in known_nodes:
            known_nodes.add(new_node_url)
            salvar_peers(known_nodes)
            print(f"[INFO] Peer {new_node_url} registrado.")
        else:
            print(f"[INFO] Peer {new_node_url} já estava registrado.")
    else:
        print(f"[INFO] Recebi meu próprio registro: {new_node_url}. Ignorando.")

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
    """Retorna a lista de transações pendentes."""
    return jsonify(blockchain.current_transactions), 200

@app.route('/tx/new', methods=['POST'])
def new_transaction_api():
    """Recebe uma nova transação do cliente e a adiciona à fila pendente."""
    
    # --- 1. Parsing e Validação Básica ---
    raw_values = None
    try:
        raw_values = request.get_json(silent=True)
    except Exception as e:
        print(f"DEBUG_SERVER: ERRO - Exceção durante o parsing JSON: {e}")
    
    if raw_values is None:
        print(f"DEBUG_SERVER: ERRO - request.get_json() retornou None.")
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

        # Formatação padronizada
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
    except Exception as e:
        return jsonify({'message': f'Erro ao processar dados: {e}'}), 400

    # --- 2. Validação Criptográfica (Pesada - Fica FORA do Lock) ---
    try:
        pk_for_address_derivation = transaction['public_key']
        if isinstance(pk_for_address_derivation, str) and pk_for_address_derivation.startswith('04') and len(pk_for_address_derivation) == 130:
            pk_for_address_derivation = pk_for_address_derivation[2:]
        
        derived_address = hashlib.sha256(bytes.fromhex(pk_for_address_derivation)).hexdigest()[:40] 
        if derived_address != transaction['sender']:
            return jsonify({'message': 'Assinatura inválida: Endereço não corresponde à chave pública'}), 400

        if not verify_signature(transaction['public_key'], transaction['signature'], transaction):
            return jsonify({'message': 'Assinatura inválida.'}), 400
            
    except Exception as e:
        print(f"[ERRO 400] Erro na validação de assinatura: {e}")
        return jsonify({'message': f'Erro na validação de assinatura: {e}'}), 400

    # --- 3. SEÇÃO CRÍTICA (Protegida contra Envio Duplo) ---
    # Aqui usamos o tx_lock para impedir que duas threads insiram a mesma TX ao mesmo tempo
    
    with tx_lock:
        # A. Verifica Duplicidade (Dentro do Lock)
        temp_tx_for_duplicate_check = {
            'sender': transaction['sender'],
            'recipient': transaction['recipient'],
            'amount': transaction['amount'],
            'fee': transaction['fee'],
            'id': transaction.get('id')
        }
        
        if blockchain.is_duplicate_transaction(temp_tx_for_duplicate_check):
            print(f"[AVISO] Transação duplicada bloquada pelo Lock: {transaction['id']}")
            return jsonify({'message': 'Transação duplicada detectada.'}), 200

        # B. Verifica Saldo (Dentro do Lock)
        current_balance = blockchain.balance(transaction['sender'])
        required_amount = float(transaction['amount']) + float(transaction['fee'])
        
        if current_balance < required_amount:
            print(f"[ERRO] Saldo insuficiente. Tem: {current_balance}, Precisa: {required_amount}")
            return jsonify({'message': f'Saldo insuficiente. Saldo: {current_balance}'}), 400

        # C. Adiciona à Lista (Sucesso)
        blockchain.current_transactions.append(transaction)
        print(f"[SUCESSO] Transação {transaction['id']} adicionada.")

    # --- 4. Broadcast (Fora do Lock para não travar o servidor) ---
    broadcast_tx_to_peers(transaction)

    response = {
        'message': f'Transação {transaction["id"]} adicionada à fila.',
        'coin_name': COIN_NAME,
        'coin_symbol': COIN_SYMBOL,
        'transaction_id': transaction['id']
    }
    return jsonify(response), 201

def broadcast_tx_to_peers(tx):
    """Envia uma transação para todos os peers conhecidos."""
    print(f"[Broadcast TX] Enviando transação {tx.get('id')} para {len(known_nodes)} peers.")
    peers_to_remove = set()
    for peer in known_nodes.copy():
        if peer == meu_url: continue
        try:
            requests.post(f"{peer}/tx/receive", json=tx, timeout=3)
        except requests.exceptions.RequestException as e:
            print(f"[Broadcast TX] Erro ao enviar TX para {peer}: {e}. Marcando peer para remoção (se não for seed).")
            if peer not in SEED_NODES:
                peers_to_remove.add(peer)
        except Exception as e:
            print(f"[Broadcast TX] Erro inesperado ao enviar TX para {peer}: {e}. Marcando peer para remoção (se não for seed).")
            if peer not in SEED_NODES:
                peers_to_remove.add(peer)
    
    if peers_to_remove:
        known_nodes.difference_update(peers_to_remove)
        salvar_peers(known_nodes)
        print(f"[Broadcast TX] Removidos {len(peers_to_remove)} peers problemáticos.")

@app.route('/tx/receive', methods=['POST'])
def receive_transaction_api():
    """Recebe uma transação de outro nó e a adiciona à fila pendente após validação."""
    tx_data = request.get_json()
    if not tx_data:
        print("[RECEIVE_TX ERROR] Nenhum dado de transação recebido.")
        return jsonify({"message": "Nenhum dado de transação recebido."}), 400

    required = ['id', 'sender', 'recipient', 'amount', 'fee', 'public_key', 'signature']
    if not all(k in tx_data for k in required):
        print(f"[RECEIVE_TX ERROR] Dados de transação incompletos: {tx_data}")
        return jsonify({'message': 'Dados de transação incompletos.'}), 400

    try:
        amount_float = float(tx_data['amount'])
        fee_float = float(tx_data['fee'])
        amount_str_formatted = f"{amount_float:.8f}"
        fee_str_formatted = f"{fee_float:.8f}"

        if fee_float <= 0:
            print(f"[RECEIVE TX ERROR] Taxa de transação inválida: {fee_float}. A taxa deve ser maior que 0.")
            return jsonify({'message': 'Transação inválida: A taxa deve ser maior que 0.'}), 400

        temp_tx_for_duplicate_check = {
            'sender': tx_data['sender'],
            'recipient': tx_data['recipient'],
            'amount': amount_str_formatted,
            'fee': fee_str_formatted,
            'id': tx_data.get('id')
        }
        if blockchain.is_duplicate_transaction(temp_tx_for_duplicate_check):
            print(f"[RECEIVE TX] Transação {tx_data.get('id')} já existe na fila pendente ou minerada. Ignorando.")
            return jsonify({'message': 'Transação já conhecida.'}), 200

        tx_for_verification = {
            'id': tx_data['id'],
            'sender': tx_data['sender'],
            'recipient': tx_data['recipient'],
            'amount': amount_str_formatted,
            'fee': fee_str_formatted,
            'public_key': tx_data['public_key'],
            'signature': tx_data['signature'],
            'timestamp': tx_data.get('timestamp', time.time())
        }

        if not verify_signature(tx_for_verification['public_key'], tx_for_verification['signature'], tx_for_verification):
            print(f"[RECEIVE TX ERROR] TX {tx_data.get('id')}: Assinatura inválida ou chave pública malformada.")
            return jsonify({'message': 'Transação inválida: Assinatura inválida ou chave pública malformada.'}), 400

        current_balance = blockchain.balance(tx_data['sender'])
        required_amount = float(tx_data['amount']) + float(tx_data['fee'])
        if current_balance < required_amount:
            print(f"[RECEIVE TX ERROR] TX {tx_data.get('id')}: Saldo insuficiente para {tx_data['sender']}. Necessário: {required_amount}, Disponível: {current_balance}")
            return jsonify({'message': 'Transação inválida: Saldo insuficiente.'}), 400

        blockchain.current_transactions.append(tx_for_verification)
        print(f"[RECEIVE TX] Transação {tx_data.get('id')} recebida e adicionada à fila pendente.")
        return jsonify({"message": "Transação recebida e adicionada com sucesso."}), 200

    except ValueError as e:
        print(f"[RECEIVE TX ERROR] Erro de conversão de tipo ao processar TX {tx_data.get('id')}: {e}")
        return jsonify({'message': f'Erro ao processar dados numéricos da transação: {e}'}), 400
    except Exception as e:
        print(f"[RECEIVE TX ERROR] Erro inesperado ao processar TX {tx_data.get('id')}: {e}")
        return jsonify({'message': f'Erro interno ao processar transação: {e}'}), 500


        
def verify_signature(public_key_hex, signature_hex, tx_data):
    """
    Verifica a assinatura de uma transação.
    tx_data deve conter 'sender', 'recipient', 'amount', 'fee'.
    'amount' e 'fee' devem ser strings formatadas com 8 casas decimais.
    """
    try:
        if not public_key_hex or not signature_hex:
            return False

        # Normaliza chave pública (remove prefixo '04' se presente)
        pk_hex = public_key_hex
        if isinstance(pk_hex, str) and pk_hex.startswith("04") and len(pk_hex) == 130:
            pk_hex = pk_hex[2:]

        # Garantir que amount e fee são strings formatadas para a verificação
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
    except BadSignatureError:
        print("Falha na verificação da assinatura: BadSignatureError!")
        return False
    except ValueError as ve:
        print(f"Falha na verificação da assinatura: ValueError (e.g., bad hex string or malformed key): {ve}")
        return False
    except Exception as e:
        print(f"Erro durante a verificação da assinatura: {e}")
        return False
        
@app.route('/blocks/receive', methods=['POST'])
def receive_block_api():
    block_data = request.get_json()
    if not block_data:
        return jsonify({"message": "Nenhum dado de bloco recebido."}), 400

    required = ['index','previous_hash','proof','timestamp','miner','transactions','difficulty','protocol_value']
    if not all(k in block_data for k in required):
        return jsonify({"message": "Dados de bloco incompletos."}), 400

    try:
        block_data['index'] = int(block_data['index'])
        block_data['difficulty'] = int(block_data['difficulty'])
        block_data['proof'] = int(block_data['proof'])
        block_data['timestamp'] = float(block_data['timestamp'])
    except:
        return jsonify({'message': 'Tipos inválidos'}), 400

    if not blockchain.chain:
        threading.Thread(target=blockchain.resolve_conflicts, daemon=True).start()
        return jsonify({'message': 'Sincronizando cadeia inicial.'}), 202

    last_block = blockchain.last_block()

    if block_data['index'] <= last_block['index']:
        return jsonify({'message': 'Bloco antigo/duplicado.'}), 200

    if block_data['index'] > last_block['index'] + 1:
        threading.Thread(target=blockchain.resolve_conflicts, daemon=True).start()
        return jsonify({'message': 'Bloco à frente. Sincronizando.'}), 202

    if block_data['previous_hash'] != blockchain.hash(last_block):
        threading.Thread(target=blockchain.resolve_conflicts, daemon=True).start()
        return jsonify({'message': 'Hash anterior inválido'}), 400

    if not blockchain.valid_proof(last_block['proof'], block_data['proof'], block_data['difficulty']):
        return jsonify({'message': 'Proof of Work inválido'}), 400

    if block_data['timestamp'] > time.time() + 120:
        return jsonify({'message': 'Timestamp no futuro'}), 400

    # 🔥 AQUI ESTÁ A CORREÇÃO
    # Não rejeitamos bloco por diferença de protocol_value
    try:
        peer_value = float(block_data.get('protocol_value', 0))
        if peer_value <= 0:
            return jsonify({'message': 'Protocol Value estruturalmente inválido'}), 400
    except:
        return jsonify({'message': 'Protocol Value inválido'}), 400

    # Validação de transações
    for tx in block_data['transactions']:
        if tx['sender'] == '0':
            continue
        try:
            tx_for_verification = {
                'amount': f"{float(tx['amount']):.8f}",
                'fee': f"{float(tx['fee']):.8f}",
                'recipient': tx['recipient'],
                'sender': tx['sender']
            }
            pub = tx.get('public_key','')
            if isinstance(pub,str) and pub.startswith("04") and len(pub)==130:
                pub = pub[2:]
            if not verify_signature(pub, tx['signature'], tx_for_verification):
                raise ValueError
        except:
            return jsonify({'message': 'Transação inválida'}), 400

    temp_chain = blockchain.chain + [block_data]
    if not blockchain.valid_chain(temp_chain):
        return jsonify({'message': 'Bloco quebra regras da cadeia'}), 400

    blockchain.chain.append(block_data)
    blockchain._save_block(block_data)

    mined_ids = {t.get('id') for t in block_data['transactions']}
    blockchain.current_transactions = [tx for tx in blockchain.current_transactions if tx.get('id') not in mined_ids]

    return jsonify({'message': 'Bloco aceito'}), 200


@app.route('/sync/check', methods=['GET'])
def check_sync_api():
    last = blockchain.last_block()
    if not last:
        return jsonify({'message': 'Blockchain não inicializada localmente.'}), 500
    local_hash = blockchain.hash(last)
    return jsonify({
        'index': last['index'],
        'hash': local_hash,
        'timestamp': last['timestamp'],
        'miner': last['miner'],
        'num_txs': len(last['transactions'])
    })

@app.route('/miner/set_address', methods=['POST'])
def set_miner_address_api():
    """Define o endereço de mineração para o nó."""
    global miner_address_global # Usar a variável global consistente
    data = request.get_json()
    address = data.get('address')
    if not address:
        return jsonify({"message": "Endereço do minerador ausente."}), 400
    miner_address_global = address
    print(f"[MINER] Endereço do minerador definido para {miner_address_global}")
    return jsonify({"message": f"Endereço do minerador definido para {miner_address_global}"}), 200

@app.route('/mine', methods=['GET'])
def mine_api():
    """Inicia o processo de mineração de um novo bloco (manual)."""
    global mining_active, miner_address_global
    if not miner_address_global:
        return jsonify({"message": "Endereço do minerador não definido. Por favor, defina um endereço primeiro usando /miner/set_address."}), 400

    # Se a mineração contínua estiver ativa, não permitir mineração manual separada
    if mining_active:
        return jsonify({"message": "Mineração contínua já está em andamento. Pare-a para minerar manualmente."}), 409

    last_block = blockchain.last_block()
    if not last_block:
        return jsonify({"message": "Blockchain não inicializada. Não é possível minerar."}), 500

    last_proof = last_block['proof']
    
    # Temporariamente ativar mining_active para que proof_of_work funcione
    # e possa ser interrompido se necessário (embora esta rota não tenha um 'stop')
    original_mining_active_state = mining_active
    mining_active = True 
    proof = blockchain.proof_of_work(last_proof)
    mining_active = original_mining_active_state # Restaurar estado

    if proof == -1: # Mineração foi abortada (por chegada de bloco ou outro motivo)
        return jsonify({"message": "Mineração abortada ou interrompida (provavelmente um bloco foi encontrado por outro nó)."}), 200

    previous_hash = blockchain.hash(last_block)
    new_block = blockchain.new_block(proof, previous_hash, miner_address_global)

    broadcast_block(new_block)

    response = {
        'message': "Novo bloco forjado!",
        'index': new_block['index'],
        'transactions': new_block['transactions'],
        'proof': new_block['proof'],
        'previous_hash': new_block['previous_hash'],
        'difficulty': new_block['difficulty']
    }
    return jsonify(response), 200

@app.route('/miner/start_continuous', methods=['GET'])
def start_continuous_mining():
    """Endpoint para iniciar a mineração contínua em um thread separado."""
    global mining_active, miner_thread, miner_address_global
    if mining_active:
        return jsonify({"message": "Mineração contínua já está em execução."}), 400
    
    if not miner_address_global:
        return jsonify({"message": "Endereço do minerador não definido. Defina um endereço primeiro usando /miner/set_address."}), 400

    mining_active = True
    miner_thread = threading.Thread(target=_continuous_mine, daemon=True)
    miner_thread.start()
    print("[MINER] Mineração contínua iniciada.")
    return jsonify({"message": "Mineração contínua iniciada."}), 200

@app.route('/miner/stop_continuous', methods=['GET'])
def stop_continuous_mining():
    """Endpoint para parar a mineração contínua."""
    global mining_active, miner_thread
    if not mining_active:
        return jsonify({"message": "Mineração contínua não está em execução."}), 400
    
    mining_active = False
    # O thread irá parar por si só na próxima iteração do loop ou quando proof_of_work verificar `mining_active`
    print("[MINER] Sinal para parar mineração contínua enviado.")
    return jsonify({"message": "Sinal para parar mineração contínua enviado. Pode levar alguns segundos para parar o bloco atual."}), 200

def _continuous_mine():
    """Função que executa a mineração continuamente em um thread."""
    global mining_active, blockchain, miner_address_global
    print("[MINER] Thread de mineração contínua iniciada.")
    while mining_active:
        try:
            last_block = blockchain.last_block()
            if not last_block:
                print("[MINER ERROR] Blockchain não inicializada para mineração contínua. Tentando novamente em 5s.")
                time.sleep(5) # Espera antes de tentar novamente
                continue

            last_proof = last_block['proof']
            
            proof = blockchain.proof_of_work(last_proof)

            if proof == -1: # Mineração foi abortada (novo bloco encontrado ou sinal para parar)
                print("[MINER] Mineração de bloco abortada. Verificando novamente o estado.")
                time.sleep(1) # Pequena pausa antes de tentar o próximo bloco
                continue

            previous_hash = blockchain.hash(last_block)
            new_block = blockchain.new_block(proof, previous_hash, miner_address_global)
            print(f"[MINER] Bloco minerado continuamente: {new_block['index']}")

            broadcast_block(new_block)
            time.sleep(1) # Pequena pausa para evitar loops muito rápidos

        except Exception as e:
            print(f"[MINER ERROR] Erro na mineração contínua: {e}. Parando mineração.")
            mining_active = False # Parar a mineração em caso de erro grave
            break
    print("[MINER] Thread de mineração contínua parada.")


# --- Funções de Peer-to-Peer (do nó) ---
def broadcast_block(block):
    """Envia um bloco recém-minerado para todos os peers conhecidos."""
    print(f"[BROADCAST] Enviando bloco #{block['index']} para {len(known_nodes)} peers...")
    peers_to_remove = set()
    for peer in known_nodes.copy():
        if peer == meu_url: continue
        try:
            requests.post(f"{peer}/blocks/receive", json=block, timeout=5)
        except requests.exceptions.RequestException as e:
            print(f"[BROADCAST] Erro ao enviar bloco para {peer}: {e}. Marcando peer para remoção (se não for seed).")
            if peer not in SEED_NODES:
                peers_to_remove.add(peer)
        except Exception as e:
            print(f"[BROADCAST] Erro inesperado ao enviar bloco para {peer}: {e}. Marcando peer para remoção (se não for seed).")
            if peer not in SEED_NODES:
                peers_to_remove.add(peer)
    
    if peers_to_remove:
        known_nodes.difference_update(peers_to_remove)
        salvar_peers(known_nodes)
        print(f"[BROADCAST] Removidos {len(peers_to_remove)} peers problemáticos.")

def discover_peers():
    global known_nodes, meu_url
    # print("[DISCOVERY] Varrendo peers...") # Comentado para poluir menos o log

    # Carrega seeds se necessário
    if len(known_nodes) < 1:
        load_peers()
        fetch_github_nodes()

    peers_snapshot = list(known_nodes)
    peers_to_remove = set() # Lista para remover nós mortos

    for peer in peers_snapshot:
        if peer == meu_url:
            continue
        try:
            # TIMEOUT REDUZIDO PARA 2 SEGUNDOS
            # Se o peer não responder rápido, ignoramos para não travar a mineração
            r = requests.get(f"{peer}/nodes", timeout=2)
            
            if r.status_code == 200:
                remote_nodes = r.json().get("nodes", [])
                for n in remote_nodes:
                    if n != meu_url and n not in known_nodes:
                        known_nodes.add(n)
        except:
            # Se der erro, apenas ignora, não remove imediatamente para não perder seeds temporariamente offline
            pass

    save_peers()

def get_my_ip():
    """Tenta obter o IP local do nó e avisa se for privado."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80)) # Conecta a um IP público para obter o IP de saída
        ip = s.getsockname()[0]
        s.close()
        try:
            if ipaddress.ip_address(ip).is_private:
                print(f"[AVISO IP] Seu IP ({ip}) é privado. Para comunicação completa com peers públicos, configure o redirecionamento de portas (port forwarding) para a porta {port} no seu roteador e use um IP público ou serviço DDNS.")
        except ValueError:
            pass # Não é um IP válido para verificar se é privado
        return ip
    except Exception:
        print("[AVISO IP] Não foi possível determinar o IP local. Usando 127.0.0.1 como fallback. A comunicação com peers externos pode ser limitada.")
        return "127.0.0.1"

def load_or_create_node_id(filename="node_id.txt"):
    """Carrega ou cria um ID de nó único."""
    if os.path.exists(filename):
        with open(filename, "r") as f:
            node_id_loaded = f.read().strip()
            print(f"[BOOT] ID do nó carregado: {node_id_loaded}")
            return node_id_loaded
    else:
        new_id = str(uuid4()).replace("-", "")[:16]
        with open(filename, "w") as f:
            f.write(new_id)
        print(f"[BOOT] Novo ID do nó criado: {new_id}")
        return new_id

# Funções auxiliares para auto_sync_checker
def auto_sync_checker(blockchain_instance):
    """Verifica periodicamente a sincronização com os peers e inicia a resolução de conflitos se necessário."""
    while True:
        try:
            comparar_ultimos_blocos(blockchain_instance)
        except Exception as e:
            print(f"[SYNC_CHECKER ERROR] Erro no verificador de sincronização: {e}")
        time.sleep(60) # Verifica a cada 60 segundos

def safe_json_response(resp, peer):
    try:
        if resp.status_code != 200:
            print(f"[NET] {peer} retornou status {resp.status_code}")
            return None
        if 'application/json' not in resp.headers.get('Content-Type', ''):
            print(f"[NET] {peer} não retornou JSON")
            return None
        return resp.json()
    except Exception as e:
        print(f"[NET] JSON inválido de {peer}: {e}")
        return None

def comparar_ultimos_blocos(blockchain_instance):
    if blockchain_instance is None or blockchain_instance.last_block() is None:
        return

    local_block = blockchain_instance.last_block()
    local_hash = blockchain_instance.hash(local_block)

    for peer in known_nodes.copy():
        if peer == meu_url:
            continue
        try:
            resp = requests.get(f"{peer}/chain", timeout=5)
            data = resp.json()
            peer_chain = data.get("chain")
            if not peer_chain:
                continue

            peer_last = peer_chain[-1]
            peer_index = peer_last["index"]
            peer_hash = blockchain_instance.hash(peer_last)

            if peer_index != local_block['index'] or peer_hash != local_hash:
                print(f"[SYNC] Diferença detectada com {peer}. Rodando consenso...")
                blockchain_instance.resolve_conflicts()
                break  # evita múltiplas execuções simultâneas

        except:
            print(f"[SYNC] {peer} não respondeu (pode estar offline).")

def broadcast_new_block(block):
    for node in known_nodes:
        try:
            requests.post(f"{node}/blocks/receive", json=block, timeout=2)
        except: 
            print(f"Node {node} offline, não recebeu o bloco.")
            
# --- Execução Principal ---
def run_server():
    global blockchain, meu_ip, meu_url, port

    port = int(os.environ.get('PORT', 5001))

    conn = sqlite3.connect(DATABASE, check_same_thread=False)
    node_id_val = load_or_create_node_id()
    blockchain = Blockchain(conn, node_id_val)

    # 🔹 IP interno (somente para o Flask escutar)
    meu_ip = get_my_ip()

    # 🔹 URL pública real (evita nó isolado)
    public_url = os.environ.get("PUBLIC_URL")
 
    if public_url:
        meu_url = public_url.rstrip('/')
        print(f"[INFO] 🌍 URL pública do nó: {meu_url}") 
    else:
        meu_url = f"http://{meu_ip}:{port}"
        print(f"[WARN] ⚠ PUBLIC_URL não definida — nó pode ficar isolado.")
        print(f"[INFO] URL local: {meu_url}")

    # 🔹 Garante que o próprio nó não está na lista de peers
    known_nodes.discard(meu_url)

    # 🔹 Inicia descoberta de peers
    threading.Thread(target=discover_peers, daemon=True).start()

    # 🔹 Espera real por peers antes de sincronizar (anti-fork)
    print("[BOOT] Aguardando peers iniciais...") 
    for _ in range(12):  # até ~24s
        if known_nodes:
            break
        time.sleep(2)

    if known_nodes:
        print(f"[BOOT] {len(known_nodes)} peers encontrados. Sincronizando cadeia...")
        blockchain.resolve_conflicts()
    else:
        print("[BOOT] Nenhum peer ainda. Operando temporariamente isolado.")

    # 🔹 Segunda tentativa de sync após a rede estabilizar
    def delayed_second_sync():
        time.sleep(30)
        if known_nodes:
            print("[BOOT] Segunda verificação de consenso após estabilização da rede...")
            blockchain.resolve_conflicts()

    threading.Thread(target=delayed_second_sync, daemon=True).start()

    # 🔹 Inicia verificador automático de sincronização contínua
    threading.Thread(target=auto_sync_checker, args=(blockchain,), daemon=True).start()

    print(f"[INFO] 🚀 Nó rodando na porta {port}")
    app.run(host='0.0.0.0', port=port, threaded=True)

 
if __name__ == "__main__":
    run_server()
