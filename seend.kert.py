import hashlib
import json
import time
import threading
import sqlite3
import os
from uuid import uuid4
from flask import Flask, jsonify, request, render_template, send_from_directory
import requests
from urllib.parse import urlparse
import socket
import ipaddress
import sys
from ecdsa import SigningKey, VerifyingKey, SECP256k1, BadSignatureError
import multiprocessing
import urllib3

# Desativa avisos de SSL
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# --- DEFINIÇÃO DE DIRETÓRIO BASE ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# --- INJEÇÃO DE MINERAÇÃO REAL (GPU/CPU) ---
try:
    import pyopencl as cl
    import numpy as np
    HAS_GPU = True
except ImportError:
    HAS_GPU = False
    print("[SISTEMA] PyOpenCL ou Numpy não instalados. Mineração GPU desativada (Usando CPU).")

# --- Configurações ---
DIFFICULTY = 4 
MINING_REWARD = 50 
DATABASE = 'chain.db'
COIN_NAME = "Kert-One"
COIN_SYMBOL = "KERT"
PEERS_FILE = 'peers.json'
WALLET_FILE = "server_wallet.json"

# --- NÓS SEMENTES (SEED NODES) ---
SEED_NODES = [
    "https://seend.kert-one.com",
    "http://seend3.kert-one.com:8001"
]

# --- KERNEL TURBO ALINHADO ---
OPENCL_KERNEL = """
typedef unsigned int uint;
#define ROR(x, y) ((x >> y) | (x << (32 - y)))
#define Ch(x, y, z) (z ^ (x & (y ^ z)))
#define Maj(x, y, z) ((x & y) | (z & (x | y)))
#define S0(x) (ROR(x, 2) ^ ROR(x, 13) ^ ROR(x, 22))
#define S1(x) (ROR(x, 6) ^ ROR(x, 11) ^ ROR(x, 25))
#define s0(x) (ROR(x, 7) ^ ROR(x, 18) ^ (x >> 3))
#define s1(x) (ROR(x, 17) ^ ROR(x, 19) ^ (x >> 10))

__constant uint K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

void sha256_transform(uint *state, const uint *data) {
    uint a, b, c, d, e, f, g, h, t1, t2;
    uint W[64];
    for (int i = 0; i < 16; ++i) W[i] = data[i];
    for (int i = 16; i < 64; ++i) W[i] = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
    a = state[0]; b = state[1]; c = state[2]; d = state[3]; e = state[4]; f = state[5]; g = state[6]; h = state[7];
    for (int i = 0; i < 64; ++i) {
        t1 = h + S1(e) + Ch(e, f, g) + K[i] + W[i]; t2 = S0(a) + Maj(a, b, c);
        h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d; state[4] += e; state[5] += f; state[6] += g; state[7] += h;
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

# --- Funções de Persistência de Peers ---
def salvar_peers(peers):
    try:
        with open(PEERS_FILE, 'w') as f:
            json.dump(list(peers), f)
        print(f"[P2P] Arquivo {PEERS_FILE} salvo.")
    except Exception as e:
        print(f"[ERRO] Falha ao salvar peers: {e}")

def carregar_peers():
    if not os.path.exists(PEERS_FILE):
        return []
    with open(PEERS_FILE, 'r') as f:
        try:
            return json.load(f)
        except json.JSONDecodeError:
            return []

known_nodes = set(carregar_peers())
miner_lock = threading.Lock()

blockchain = None
miner_address = None
miner_address_global = None 
meu_url = None
port = None

# Global variable for mining control
mining_active = False
mining_stop_flag = multiprocessing.Event()
mining_result = multiprocessing.Value('i', -1)

@app.route('/coin/value', methods=['GET'])
def coin_value_api():
    if not blockchain.chain:
        price = 500.0
    else:
        last_block = blockchain.last_block()
        price = float(last_block.get('protocol_value', 0.0))

    if price < 500.0:
        display_price = 500.0 + price
    else:
        display_price = price

    return jsonify({
        "coin": COIN_SYMBOL,
        "protocol_value": price,
        "protocol_value_display": f"{display_price:.2f}",
        "unit": "USD"
    }), 200
    
# --- Classe Blockchain ---
class Blockchain:
    ADJUST_INTERVAL = 10 
    TARGET_TIME = 30

    def _calculate_difficulty_for_index(self, target_block_index):
        if target_block_index % self.ADJUST_INTERVAL != 0:
            return self.chain[-1].get('difficulty', 4)

        if len(self.chain) < self.ADJUST_INTERVAL:
            return 4
    
        last_block = self.chain[-1]
        first_block = self.chain[-self.ADJUST_INTERVAL]
        actual_time = last_block['timestamp'] - first_block['timestamp']
        
        expected_time = self.ADJUST_INTERVAL * self.TARGET_TIME
        old_diff = last_block['difficulty']
        
        if actual_time <= 0: actual_time = 1
        new_diff = int(old_diff * (expected_time / actual_time))
        return max(1, min(20, new_diff))
        
    def __init__(self, conn, node_id):
        self.conn = conn
        self.node_id = node_id
        self._init_db()
        self.chain = self._load_chain()
        self.current_transactions = []
        if not self.chain:
            print("[BOOT] 📡 Inserindo Gênese Base...")
            genesis_block = {
                'index': 1, 'previous_hash': '1', 'proof': 100,
                'timestamp': 1700000000.0, 'miner': 'genesis',
                'transactions': [], 'difficulty': 1, 'protocol_value': 500.0
            }
            self.chain.append(genesis_block)
            self._save_block(genesis_block)
        self.difficulty = self._calculate_difficulty_for_index(len(self.chain))
        print(f"[BOOT] Dificuldade inicial: {self.difficulty}")

    @staticmethod
    def hash(block):
        block_core = {
            "index": block["index"], "previous_hash": block["previous_hash"],
            "proof": block["proof"], "timestamp": block["timestamp"],
            "miner": block["miner"], "difficulty": block.get("difficulty", 1),
            "protocol_value": block.get("protocol_value", 0),
            "transactions": block["transactions"]
        }
        # Garante ordenação consistente
        block_string = json.dumps(block_core, sort_keys=True, separators=(',', ':')).encode()
        return hashlib.sha256(block_string).hexdigest()

    def is_duplicate_transaction(self, new_tx):
        for tx in self.current_transactions:
            if tx.get('id') == new_tx.get('id'):
                return True
        return False

    @staticmethod
    def custom_asic_resistant_hash(data_bytes, nonce):
        raw = data_bytes + str(nonce).encode()
        return hashlib.sha256(hashlib.sha256(raw).digest()).hexdigest()

    def _init_db(self):
        c = self.conn.cursor()
        c.execute('''CREATE TABLE IF NOT EXISTS blocks(index_ INTEGER PRIMARY KEY, previous_hash TEXT, proof INTEGER, timestamp REAL, miner TEXT, difficulty INTEGER, protocol_value REAL)''')
        c.execute('''CREATE TABLE IF NOT EXISTS txs(id TEXT PRIMARY KEY, sender TEXT, recipient TEXT, amount TEXT, fee TEXT, signature TEXT, block_index INTEGER, public_key TEXT)''')
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
            block = {
                'index': idx, 'previous_hash': prev, 'proof': proof,
                'timestamp': ts, 'miner': miner, 'transactions': txs,
                'difficulty': difficulty, 'protocol_value': p_val
            }
            chain.append(block)
        return chain

    def new_block(self, proof, previous_hash, miner, initial_difficulty=None):
        block_index = len(self.chain) + 1
        reward = self._get_mining_reward(block_index)
        difficulty = self._calculate_difficulty_for_index(block_index) if initial_difficulty is None else initial_difficulty
        mining_reward_tx = {
            'id': str(uuid4()), 'sender': '0', 'recipient': miner,
            'amount': f"{reward:.8f}", 'fee': f"{0.0:.8f}", 'signature': '', 'public_key': ''
        }
        if not (proof == 100 and previous_hash == '1'):
             self.current_transactions.insert(0, mining_reward_tx)
        block = {
            'index': block_index, 'previous_hash': previous_hash, 'proof': proof,
            'timestamp': time.time(), 'miner': miner,
            'transactions': self.current_transactions, 'difficulty': difficulty
        }
        self.current_transactions = []
        self.chain.append(block)
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM blocks WHERE index_=?", (block['index'],))
        if not c.fetchone():
            self._save_block(block)
        return block

    def _save_block(self, block):
        c = self.conn.cursor()
        c.execute("INSERT INTO blocks VALUES (?, ?, ?, ?, ?, ?, ?)",
                  (block['index'], block['previous_hash'], block['proof'],
                   block['timestamp'], block['miner'], block['difficulty'],
                   block.get('protocol_value', 500.0)))
        for t in block['transactions']:
            c.execute("INSERT INTO txs VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                      (t['id'], t['sender'], t['recipient'], t['amount'],
                       t['fee'], t['signature'], block['index'], t.get('public_key', '')))
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

    def last_block(self):
        return self.chain[-1] if self.chain else None

    def proof_of_work(self, last_proof):
        difficulty_for_pow = self._calculate_difficulty_for_index(len(self.chain) + 1)
        proof = 0
        print(f"⛏️  [MINER] CPU Mining. Dif: {difficulty_for_pow}")
        while not self.valid_proof(last_proof, proof, difficulty_for_pow):
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
        try:
            import pyopencl as cl
            import numpy as np
            import time
        except ImportError: return -1

        try:
            platforms = cl.get_platforms()
            if not platforms: return -1
            target_device = platforms[0].get_devices(device_type=cl.device_type.GPU)[0]
            
            ctx = cl.Context(devices=[target_device])
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
            
            print(f"🔥 [GPU] SEED ATIVO: {target_device.name}")

            while not stop_event.is_set():
                iter_start = time.time()
                kernel(queue, (batch_size,), None, res_buf, found_buf, np.uint32(difficulty), np.uint32(current_nonce))
                queue.finish() 
                
                if (time.time() - iter_start) < 0.001:
                    print("[GPU] Erro de driver detectado. Reiniciando worker.")
                    return -1

                cl.enqueue_copy(queue, found, found_buf)
                
                if found[0] == 1:
                    cl.enqueue_copy(queue, result_nonce, res_buf)
                    nonce = int(result_nonce[0])
                    if Blockchain.valid_proof(last_proof, nonce, difficulty):
                        print(f"💎 [GPU-SEED] BLOCO ENCONTRADO: {nonce}")
                        result_value.value = nonce
                        stop_event.set()
                        return nonce
                    found[0] = 0
                    cl.enqueue_copy(queue, found_buf, found)

                current_nonce += (batch_size * loop_intern0)
                if current_nonce > 4000000000: current_nonce = 0
                
        except Exception as e:
            print(f"[GPU ERROR] {e}")
            return -1
        return -1

    def tx_already_mined(self, tx_id):
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM txs WHERE id=?", (tx_id,))
        return c.fetchone() is not None

    # --- CORREÇÃO CRÍTICA PARA ACEITAR BLOCOS ANTIGOS (MODO BLIND SYNC) ---
    def valid_chain(self, chain, check_strict=True):
        if not chain: return False
        if chain[0]['index'] != 1 or chain[0]['previous_hash'] != '1': return False
        for idx in range(1, len(chain)):
            prev = chain[idx - 1]
            curr = chain[idx]
            
            # Se for checagem estrita (padrão), valida hash e PoW
            if check_strict:
                if curr['previous_hash'] != self.hash(prev):
                    print(f"[SYNC ERROR] Hash inválido no bloco {curr['index']}.")
                    return False
                if not self.valid_proof(prev['proof'], curr['proof'], curr.get('difficulty', DIFFICULTY)):
                    print(f"[SYNC ERROR] Prova inválida no bloco {curr['index']}.")
                    return False
            else:
                # Se for MODO CÓPIA (check_strict=False), confia e só verifica a sequência
                if curr['index'] != prev['index'] + 1:
                    return False
                    
        return True

    def get_total_difficulty(self, chain_to_check):
        return sum([block.get('difficulty', DIFFICULTY) for block in chain_to_check])

    def resolve_conflicts(self):
        # GARANTE que estamos lendo os peers do arquivo + memória
        current_peers = known_nodes.union(set(carregar_peers()))
        neighbors = list(current_peers)
        new_chain = None
        max_difficulty = self.get_total_difficulty(self.chain)
        
        # --- DETECÇÃO DE BOOTSTRAP (Se eu sou novo, ativo o modo 'Confia no Pai') ---
        # Se eu só tenho o Genesis, eu NÃO valido hashes antigos, eu só baixo.
        is_fresh_install = (len(self.chain) <= 1)
        if is_fresh_install:
            print("[BOOT] 🐇 MODO CÓPIA CEGA ATIVADO: Baixando chain sem validar hashes antigos...")

        print(f"[SYNC] Verificando {len(neighbors)} peers...")
        
        for node_url in neighbors:
            if node_url == meu_url: continue
            try:
                print(f"   -> Conectando a {node_url}...")
                response = requests.get(f"{node_url}/chain", timeout=60, verify=False)
                if response.status_code == 200:
                    data = response.json()
                    peer_chain = data.get("chain")
                    if not peer_chain: continue
                    
                    peer_difficulty = self.get_total_difficulty(peer_chain)
                    print(f"      [INFO] Peer Dif: {peer_difficulty} | Local Dif: {max_difficulty}")
                    
                    if peer_difficulty > max_difficulty:
                        # O PULO DO GATO: Se for instalação nova, passa check_strict=False
                        if self.valid_chain(peer_chain, check_strict=not is_fresh_install):
                            max_difficulty = peer_difficulty
                            new_chain = peer_chain
                            print("      [UPGRADE] Nova chain aceita e baixada!")
                        else:
                            print("      [REJECT] Chain rejeitada (Inválida).")
            except Exception as e:
                print(f"      [OFFLINE] {node_url}: {e}")
                
        if new_chain:
            self.chain = new_chain
            self._rebuild_db_from_chain()
            print(f"[CONSENSO] ✅ Sincronizado com sucesso! Total Blocos: {len(self.chain)}")
            return True
        print("[CONSENSO] Mantendo cadeia local.")
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
        except Exception as e: print(f"[DB] Erro rebuild: {e}")

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

# --- Endpoints Flask ---
@app.route('/', methods=['GET'])
def index_web(): return "Kert-One Seed Node Running (Linux/Ubuntu)"

@app.route('/chain', methods=['GET'])
def chain_api():
    response = {'chain': blockchain.chain, 'length': len(blockchain.chain), 'pending_transactions': blockchain.current_transactions, 'node_id': node_id}
    return jsonify(response), 200

@app.route('/nodes/register', methods=['POST'])
def register_nodes_api():
    data = request.get_json(silent=True) or {}
    new_node_url = data.get("url")
    if not new_node_url:
        new_node_ip = data.get("ip"); new_node_port = data.get("port")
        if new_node_ip and new_node_port: new_node_url = f"http://{new_node_ip}:{new_node_port}"
    if not new_node_url: return jsonify({"message": "Invalido"}), 400
    
    new_node_url = new_node_url.strip().rstrip("/")
    if not new_node_url.startswith("http"): new_node_url = "http://" + new_node_url
    if new_node_url == meu_url: return jsonify({"message": "Self ignored"}), 200
    
    if new_node_url not in known_nodes:
        known_nodes.add(new_node_url)
        salvar_peers(known_nodes) 
        print(f"[P2P] Novo peer registrado: {new_node_url}")
        try: requests.post(f"{new_node_url}/nodes/register", json={"url": meu_url}, timeout=5, verify=False)
        except: pass
    return jsonify({"message": "Registrado", "known_peers": list(known_nodes)}), 200

@app.route('/nodes', methods=['GET'])
def get_nodes_api(): return jsonify({'nodes': list(known_nodes)}), 200

@app.route('/nodes/resolve', methods=['GET'])
def resolve_api():
    replaced = blockchain.resolve_conflicts()
    return jsonify({'message': 'Cadeia substituida' if replaced else 'Cadeia autoritativa'}), 200

@app.route('/balance/<addr>', methods=['GET'])
def balance_api(addr):
    return jsonify({'address': addr, 'balance': blockchain.balance(addr), 'symbol': COIN_SYMBOL}), 200

@app.route('/tx/new', methods=['POST'])
def new_transaction_api():
    values = request.get_json(silent=True)
    required = ['id', 'sender', 'recipient', 'amount', 'fee', 'public_key', 'signature']
    if not values or not all(k in values for k in required): return jsonify({'message': 'Faltando dados'}), 400
    
    try:
        amount_fmt = f"{float(values['amount']):.8f}"
        fee_fmt = f"{float(values['fee']):.8f}"
        transaction = {
            'id': values['id'], 'sender': values['sender'], 'recipient': values['recipient'],
            'amount': amount_fmt, 'fee': fee_fmt,
            'public_key': values['public_key'], 'signature': values['signature'],
            'timestamp': values.get('timestamp', time.time())
        }
        
        vk = VerifyingKey.from_string(bytes.fromhex(values['public_key']), curve=SECP256k1)
        msg_data = {'amount': amount_fmt, 'fee': fee_fmt, 'recipient': values['recipient'], 'sender': values['sender']}
        message = json.dumps(msg_data, sort_keys=True, separators=(',', ':')).encode('utf-8')
        vk.verify_digest(bytes.fromhex(values['signature']), hashlib.sha256(message).digest())

        if blockchain.balance(values['sender']) < (float(amount_fmt) + float(fee_fmt)):
             return jsonify({'message': 'Saldo insuficiente'}), 400

        blockchain.current_transactions.append(transaction)
        broadcast_tx_to_peers(transaction)
        return jsonify({'message': 'TX Adicionada'}), 201
    except Exception as e:
        return jsonify({'message': f'Erro: {e}'}), 400

def broadcast_tx_to_peers(tx):
    for peer in known_nodes.copy():
        if peer == meu_url: continue
        try: requests.post(f"{peer}/tx/receive", json=tx, timeout=3, verify=False)
        except: pass

@app.route('/tx/receive', methods=['POST'])
def receive_transaction_api():
    tx_data = request.get_json()
    if not tx_data: return jsonify({'message': 'No data'}), 400
    blockchain.current_transactions.append(tx_data)
    return jsonify({'message': 'TX Recebida'}), 200

@app.route('/blocks/receive', methods=['POST'])
def receive_block_api():
    block_data = request.get_json()
    last_block = blockchain.last_block()
    if block_data['index'] > last_block['index'] + 1:
        threading.Thread(target=blockchain.resolve_conflicts, daemon=True).start()
        return jsonify({'message': 'Sync started'}), 202
    if blockchain.valid_proof(last_block['proof'], block_data['proof'], block_data['difficulty']):
         blockchain.chain.append(block_data)
         blockchain._save_block(block_data)
         mined_ids = {t['id'] for t in block_data['transactions']}
         blockchain.current_transactions = [tx for tx in blockchain.current_transactions if tx['id'] not in mined_ids]
         return jsonify({'message': 'Bloco aceito'}), 200
    return jsonify({'message': 'Bloco invalido'}), 400

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
    return jsonify({"message": "Missing address"}), 400

@app.route('/mine', methods=['GET'])
def mine_api():
    global mining_active, miner_address_global, mining_stop_flag, mining_result
    if not miner_address_global: return jsonify({"message": "Endereço minerador nao definido"}), 400
    with miner_lock:
        if mining_active: return jsonify({"message": "Ja minerando"}), 409
        mining_active = True
    try:
        last_block = blockchain.last_block()
        proof = -1
        mining_stop_flag.clear(); mining_result.value = -1
        
        if HAS_GPU:
             proof = Blockchain._mine_gpu(last_block['proof'], blockchain._calculate_difficulty_for_index(len(blockchain.chain)+1), mining_stop_flag, mining_result)
        if proof == -1: 
             proof = blockchain.proof_of_work(last_block['proof'])
             
        if proof != -1:
            new_block = blockchain.new_block(proof, blockchain.hash(last_block), miner_address_global)
            broadcast_block(new_block)
            return jsonify({"message": "Bloco Minerado!", "index": new_block['index']}), 200
        return jsonify({"message": "Parado"}), 200
    finally:
        with miner_lock: mining_active = False

def broadcast_block(block):
    for peer in known_nodes | set(SEED_NODES):
        if peer == meu_url: continue
        try: requests.post(f"{peer}/blocks/receive", json=block, timeout=5, verify=False)
        except: pass

# --- ROTAS PWA E FRONTEND ---
@app.route('/card')
def card_web():
    try: return render_template('card.html')
    except Exception as e: return f"Erro: {e}", 500

@app.route('/manifest.json')
def manifest():
    try: return send_from_directory(os.path.join(BASE_DIR, 'static'), 'manifest.json', mimetype='application/json')
    except Exception as e: return f"Erro: {e}", 500

@app.route('/sw.js')
def service_worker():
    try: return send_from_directory(os.path.join(BASE_DIR, 'static'), 'sw.js', mimetype='application/javascript')
    except Exception as e: return f"Erro: {e}", 500

@app.route('/static/<path:filename>')
def serve_static_files(filename):
    return send_from_directory(os.path.join(BASE_DIR, 'static'), filename)

def get_my_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]; s.close()
        return ip
    except: return "127.0.0.1"

def auto_sync_checker(blockchain_instance):
    while True:
        try:
            blockchain_instance.resolve_conflicts()
        except Exception as e: print(f"[SYNC] Erro: {e}")
        time.sleep(60)

# --- EXECUÇÃO PRINCIPAL ---
if __name__ == "__main__":
    conn = sqlite3.connect(DATABASE, check_same_thread=False)
    node_id_val = str(uuid4()).replace("-", "")[:16]
    blockchain = Blockchain(conn, node_id_val)

    port = int(os.environ.get('PORT',5001))
    meu_ip = get_my_ip()
    meu_url = f"http://{meu_ip}:{port}"
    print(f"[LINUX SEED] 🐧 Rodando em: {meu_url}")

    # --- INICIALIZAÇÃO AGRESSIVA ---
    print("[BOOT] 📡 Carregando Seeds e Peers...")
    for seed in SEED_NODES: 
        known_nodes.add(seed)
    
    salvar_peers(known_nodes) 
    print(f"[SISTEMA] Arquivo peers.json criado/atualizado com {len(known_nodes)} nós.")

    print("[BOOT] ⏳ Iniciando Sync Inicial...")
    if blockchain.resolve_conflicts():
        print("[BOOT] ✅ Sync Concluído!")
    else:
        print("[BOOT] ⚠️ Sync terminou sem mudanças (ou chain local é a maior).")

    threading.Thread(target=auto_sync_checker, args=(blockchain,), daemon=True).start()
    
    kwargs = {'host': '0.0.0.0', 'port': 5001, 'threaded': True, 'use_reloader': False}
    flask_thread = threading.Thread(target=app.run, kwargs=kwargs, daemon=True)
    flask_thread.start()

    print("[SISTEMA] 🚀 Servidor ONLINE.")

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("Desligando nó...")
