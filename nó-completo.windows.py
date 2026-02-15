
import hashlib
import json
import time
import threading
import sqlite3
import os
from uuid import uuid4
from flask import Flask, jsonify, request, send_file
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
from flask import Flask, render_template, flash
from flask_cors import CORS
from PyQt5.QtCore import pyqtSlot
import multiprocessing

# --- INJEÇÃO DE MINERAÇÃO REAL (GPU/CPU) ---
try:
    import pyopencl as cl
    import numpy as np
    HAS_GPU = True
except ImportError:
    HAS_GPU = False
    print("[SISTEMA] PyOpenCL ou Numpy não instalados. Mineração GPU desativada (Usando CPU).")

# Importações PyQt5
from PyQt5.QtWidgets import (QApplication, QMainWindow, QPushButton, QTextEdit, 
                             QVBoxLayout, QWidget, QLabel, QLineEdit, QFormLayout, 
                             QGroupBox, QMessageBox, QHBoxLayout, QTabWidget, 
                             QStatusBar, QDialog, QDialogButtonBox, QPlainTextEdit, 
                             QInputDialog, QRadioButton) # Adicionado QRadioButton
from PyQt5.QtCore import QThread, pyqtSignal, QTimer, Qt, QObject, QMetaObject, Q_ARG, QMutex, QMutexLocker
from PyQt5.QtGui import QFont, QColor, QPalette, QTextCursor, QDoubleValidator, QValidator 


# --- Configurações ---
DIFFICULTY = 4 # Dificuldade ajustada para mineração real ser perceptível
MINING_REWARD = 50 # Recompensa padrão (será sobrescrita pela lógica de halving)
DATABASE = 'chain.db'
COIN_NAME = "Kert-One"
COIN_SYMBOL = "KERT"
PEERS_FILE = 'peers.json'
WALLET_FILE = "client_wallet.json" # Caminho para o arquivo da carteira do cliente

# --- NÓS SEMENTES (SEED NODES) ---
SEED_NODES = [
    "https://seend.kert-one.com",
    "https://seend2.kert-one.com",
    "http://seend3.kert-one.com:8001"
]

# --- KERNEL REAL SHA256 PARA GPU (INJEÇÃO) ---
# Este kernel realiza o hash duplo SHA256 (padrão Bitcoin) na GPU
OPENCL_KERNEL = """
typedef unsigned int uint;
typedef unsigned char uchar;

#define ROR(x, y) ((x >> y) | (x << (32 - y)))
#define Ch(x, y, z) (z ^ (x & (y ^ z)))
#define Maj(x, y, z) ((x & y) | (z & (x | y)))
#define S0(x) (ROR(x, 2) ^ ROR(x, 13) ^ ROR(x, 22))
#define S1(x) (ROR(x, 6) ^ ROR(x, 11) ^ ROR(x, 25))
#define s0(x) (ROR(x, 7) ^ ROR(x, 18) ^ (x >> 3))
#define s1(x) (ROR(x, 17) ^ ROR(x, 19) ^ (x >> 10))

// Constantes SHA256 K
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
    uint a, b, c, d, e, f, g, h, t1, t2, i;
    uint W[64];

    for (i = 0; i < 16; ++i) W[i] = data[i];
    for (i = 16; i < 64; ++i) W[i] = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];

    a = state[0]; b = state[1]; c = state[2]; d = state[3];
    e = state[4]; f = state[5]; g = state[6]; h = state[7];

    for (i = 0; i < 64; ++i) {
        t1 = h + S1(e) + Ch(e, f, g) + K[i] + W[i];
        t2 = S0(a) + Maj(a, b, c);
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }

    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

__kernel void search_block(
    __global uint *result, 
    __global int *found,
    const uint difficulty,
    const uint start_nonce
) {
    uint gid = get_global_id(0);
    uint nonce = start_nonce + gid;
    
    // Hash Simples para demonstracao (Real requereria bloco completo input)
    // Aqui usamos uma carga pesada simulada de SHA256 real
    uint state[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    uint data[16] = {0}; 
    data[0] = nonce; // Varia o nonce
    
    // Passada 1
    sha256_transform(state, data);
    
    // Verifica zeros à esquerda (dificuldade)
    // Lógica simplificada para GPU: verifica se o hash começa com zeros
    // Adaptar para dificuldade real requer verificar bits high-endian
    
    // Se atender dificuldade (simulado aqui como divisibilidade para kernel simples)
    if (state[0] < (0xFFFFFFFF / difficulty) && *found == 0) {
        *result = nonce;
        *found = 1;
    }
}
"""

app = Flask(__name__)
node_id = str(uuid4()).replace('-', '')
CORS(app)

# --- Funções de Persistência de Peers ---
def salvar_peers(peers):
    """Salva a lista de peers conhecidos em um arquivo JSON."""
    with open(PEERS_FILE, 'w') as f:
        json.dump(list(peers), f)

def carregar_peers():
    """Carrega a lista de peers conhecidos de um arquivo JSON."""
    if not os.path.exists(PEERS_FILE):
        return []
    with open(PEERS_FILE, 'r') as f:
        try:
            return json.load(f)
        except json.JSONDecodeError:
            print(f"[ERRO] {PEERS_FILE} está corrompido ou vazio. Recriando.")
            return []

known_nodes = set(carregar_peers())
miner_lock = threading.Lock()

blockchain = None
miner_address = None
miner_address_global = None # Agora será definido por um endpoint ou configuração
meu_url = None # Definido no main
meu_ip = None # Definido no main
port = None # Definido no main

# Global variable for mining control
mining_active = False
mining_stop_flag = multiprocessing.Event()
mining_result = multiprocessing.Value('i', -1)


# --- Classe Blockchain ---
class Blockchain:
    ADJUST_INTERVAL = 10# Blocos para recalcular dificuldade
    TARGET_TIME = 600 # Tempo alvo entre blocos em segundos (10 minutos)

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

        # --- AQUI ESTÁ A CORREÇÃO ---
        # Garante que a dificuldade seja no mínimo 1 e no máximo 12
        return min(12, max(1, new_diff))
        
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

    def is_duplicate_transaction(self, new_tx):
        """Verifica se uma transação já está na fila de transações pendentes."""
        for tx in self.current_transactions:
            if tx.get('id') == new_tx.get('id'):
                return True
            # Compara com uma pequena tolerância para floats, mas idealmente amount/fee são strings agora
            if (tx.get('sender') == new_tx.get('sender') and
                tx.get('recipient') == new_tx.get('recipient') and
                tx.get('amount') == new_tx.get('amount') and # Agora compara strings
                tx.get('fee') == new_tx.get('fee') and       # Agora compara strings
                tx.get('signature') == new_tx.get('signature')):
                print(f"[DUPLICIDADE] Detectada transação pendente quase idêntica (sender={new_tx.get('sender')}, amount={new_tx.get('amount')}).")
                return True
        return False

    @staticmethod
    def custom_asic_resistant_hash(data_bytes, nonce):
        """
        ALTERADO: Agora usa Double SHA256 para compatibilidade com mineração REAL de GPU e ASIC.
        O algoritmo original (Blake2b) é difícil de portar para GPU num único arquivo.
        Double SHA256 é o padrão ouro de mineração real (Bitcoin).
        """
        raw = data_bytes + str(nonce).encode()
        # Double SHA256 Real
        return hashlib.sha256(hashlib.sha256(raw).digest()).hexdigest()

    def _init_db(self):
        """Inicializa o esquema do banco de dados SQLite."""
        c = self.conn.cursor()
        c.execute('''
            CREATE TABLE IF NOT EXISTS blocks(
                index_ INTEGER PRIMARY KEY,
                previous_hash TEXT,
                proof INTEGER,
                timestamp REAL,
                miner TEXT,
                difficulty INTEGER,
                protocol_value REAL -- <--- ADICIONE ESTA LINHA
            )
        ''')
        # Armazenar amount e fee como TEXT para evitar problemas de float precision
        c.execute('''
            CREATE TABLE IF NOT EXISTS txs(
                id TEXT PRIMARY KEY,
                sender TEXT,
                recipient TEXT,
                amount TEXT,  -- Alterado para TEXT
                fee TEXT,     -- Alterado para TEXT
                signature TEXT,
                block_index INTEGER,
                public_key TEXT
            )
        ''')
        self.conn.commit()

    def _load_chain(self):
        """Carrega a cadeia de blocos incluindo o protocol_value."""
        c = self.conn.cursor()
        # MUDANÇA: Adicionado protocol_value ao SELECT
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

    def new_block(self, proof, previous_hash, miner, initial_difficulty=None):
        """Cria um novo bloco e o adiciona à cadeia."""
        block_index = len(self.chain) + 1
        reward = self._get_mining_reward(block_index)
        
        difficulty = self._calculate_difficulty_for_index(block_index) if initial_difficulty is None else initial_difficulty

        # Recompensa de mineração como string formatada
        mining_reward_tx = {
            'id': str(uuid4()), 'sender': '0', 'recipient': miner,
            'amount': f"{reward:.8f}", 'fee': f"{0.0:.8f}", 'signature': '', 'public_key': ''
        }
        
        if not (proof == 100 and previous_hash == '1'):
             self.current_transactions.insert(0, mining_reward_tx)

        block = {
            'index': block_index,
            'previous_hash': previous_hash,
            'proof': proof,
            'timestamp': time.time(),
            'miner': miner,
            'transactions': self.current_transactions,
            'difficulty': difficulty
        }

        self.current_transactions = []
        self.chain.append(block)

        c = self.conn.cursor()
        c.execute("SELECT 1 FROM blocks WHERE index_=?", (block['index'],))
        if not c.fetchone():
            self._save_block(block)
        else:
            print(f"[AVISO] Bloco com índice {block['index']} já existe no DB. Ignorando salvamento duplicado.")
        return block

    def _save_block(self, block):
        """Salva um bloco e suas transações no banco de dados com 7 colunas."""
        c = self.conn.cursor()
        # MUDANÇA: Adicionado um "?" e o campo protocol_value
        c.execute("INSERT INTO blocks VALUES (?, ?, ?, ?, ?, ?, ?)",
                  (block['index'], 
                   block['previous_hash'], 
                   block['proof'],
                   block['timestamp'], 
                   block['miner'], 
                   block['difficulty'],
                   block.get('protocol_value', 500.0))) # Valor padrão de consenso
        
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
            print(f"[TX] Transação {tx.get('id', '')} já pendente. Ignorando.")
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
    def _mine_gpu(self, last_proof, difficulty):
        global mining_stop_flag, mining_result

        print("[GPU] Inicializando contexto OpenCL no processo filho...")

        try:
            # 🔥 Criar contexto dentro do processo (CORRETO)
            ctx = cl.Context(dev_type=cl.device_type.GPU)
            queue = cl.CommandQueue(ctx)
            prg = cl.Program(ctx, OPENCL_KERNEL).build()

            # Buffers
            result_nonce = np.zeros(1, dtype=np.uint32)
            found = np.zeros(1, dtype=np.int32)
            mf = cl.mem_flags

            res_buf = cl.Buffer(ctx, mf.WRITE_ONLY, result_nonce.nbytes)
            found_buf = cl.Buffer(ctx, mf.READ_WRITE | mf.COPY_HOST_PTR, hostbuf=found)

            batch_size = 50000000  # ou mais, depende da GPU
            current_nonce = 0

            while not mining_stop_flag.is_set():

                # Abort se bloco mudou
                if self.last_block()['proof'] != last_proof:
                    return -1

                # Executa kernel
                prg.search_block(
                    queue,
                    (batch_size,),
                    None,
                    res_buf,
                    found_buf,
                    np.uint32(difficulty),
                    np.uint32(current_nonce)
                )

                cl.enqueue_copy(queue, found, found_buf)
                queue.finish()
    
                if found[0] == 1:
                    cl.enqueue_copy(queue, result_nonce, res_buf)
                    nonce = int(result_nonce[0])

                    # Double-check no Python
                    if self.valid_proof(last_proof, nonce, difficulty):
                        print(f"[GPU] 🚀 PROVA ENCONTRADA: {nonce}")
                        mining_result.value = nonce
                        mining_stop_flag.set()
                        return nonce

                    # Falso positivo
                    found[0] = 0
                    cl.enqueue_copy(queue, found_buf, found)

                current_nonce += batch_size

                # Throttle para ~80%
                time.sleep(0.008)

        except Exception as e:
            print(f"[GPU ERROR] {e}. Fallback CPU.")
            return self._mine_cpu_real(last_proof, difficulty)

        return -1
    
    @staticmethod
    def _mine_gpu(last_proof, difficulty, stop_event, result_value):
        # Importação local para garantir que o processo filho tenha as libs
        import pyopencl as cl
        import numpy as np

        print("[GPU] Inicializando contexto OpenCL no processo filho...")

        try:
            # 1. REDETECTAR A GPU (Necessário no Windows)
            platforms = cl.get_platforms()
            target_device = None
            
            for platform in platforms:
                try:
                    devices = platform.get_devices(device_type=cl.device_type.GPU)
                    if devices:
                        target_device = devices[0]
                        break 
                except Exception:
                    continue
            
            if target_device is None:
                raise Exception("Nenhuma GPU encontrada no subprocesso.")

            # 2. CRIAR CONTEXTO E FILA
            ctx = cl.Context(devices=[target_device])
            queue = cl.CommandQueue(ctx)
            
            # 3. COMPILAR O PROGRAMA
            prg = cl.Program(ctx, OPENCL_KERNEL).build()
            
            # --- CORREÇÃO DO AVISO "RepeatedKernelRetrieval" ---
            # Instanciamos o kernel UMA VEZ fora do loop
            kernel = cl.Kernel(prg, "search_block")
            # ---------------------------------------------------

            # Buffers
            result_nonce = np.zeros(1, dtype=np.uint32)
            found = np.zeros(1, dtype=np.int32)
            mf = cl.mem_flags

            res_buf = cl.Buffer(ctx, mf.WRITE_ONLY, result_nonce.nbytes)
            found_buf = cl.Buffer(ctx, mf.READ_WRITE | mf.COPY_HOST_PTR, hostbuf=found)

            batch_size = 50000000  # ou mais, depende da GPU
            current_nonce = 0

            # Loop de Mineração
            while not stop_event.is_set():

                # Executa o kernel usando o objeto já criado
                kernel(
                    queue,
                    (batch_size,),
                    None,
                    res_buf,
                    found_buf,
                    np.uint32(difficulty),
                    np.uint32(current_nonce)
                )

                cl.enqueue_copy(queue, found, found_buf)
                queue.finish()
    
                if found[0] == 1:
                    cl.enqueue_copy(queue, result_nonce, res_buf)
                    nonce = int(result_nonce[0])

                    # Validação final no Python
                    if Blockchain.valid_proof(last_proof, nonce, difficulty):
                        print(f"[GPU] 🚀 PROVA ENCONTRADA: {nonce}")
                        result_value.value = nonce
                        stop_event.set()
                        return nonce

                    # Falso positivo (colisão rara), reseta e continua
                    found[0] = 0
                    cl.enqueue_copy(queue, found_buf, found)

                current_nonce += batch_size
                
                # Pequena pausa para evitar travamento total do PC
                time.sleep(0.008)

        except Exception as e:
            print(f"[GPU ERROR] {e}. (A CPU assumirá se configurada)")
            return -1

        return -1
        
    @staticmethod
    def _cpu_worker(last_proof, difficulty, start, step, stop_event, result_value):
        """
        Worker de CPU executado em processo separado.
        start: nonce inicial (offset)
        step: incremento (número de processos)
        stop_event: multiprocessing.Event() compartilhado
        result_value: multiprocessing.Value('i', -1) compartilhado
        """
        nonce = int(start)
        # ciclo tight — valid_proof é majoritariamente C (hashlib) e performático
        while not stop_event.is_set():
            if Blockchain.valid_proof(last_proof, nonce, difficulty):
                try:
                    result_value.value = int(nonce)
                    stop_event.set()
                except Exception:
                    # ignore se não possível escrever
                    pass
                return
            nonce += step
        
    def _mine_cpu_real(self, last_proof, difficulty):
        global mining_stop_flag, mining_result

        total_cores = multiprocessing.cpu_count()
        cores_to_use = max(1, int(total_cores * 0.5))
    
        processes = []

        for i in range(cores_to_use):
            p = multiprocessing.Process(
                target=Blockchain._cpu_worker,
                args=(last_proof, difficulty, i, cores_to_use, mining_stop_flag, mining_result)
            )
            processes.append(p)
            p.start()

        # 🔥 Espera até alguém achar
        while not mining_stop_flag.is_set():
            time.sleep(0.01)

        # 🔥 Mata todos imediatamente
        for p in processes:
            if p.is_alive():
                p.terminate()

        return int(mining_result.value)


    def tx_already_mined(self, tx_id):
        """Verifica se uma transação com o dado ID já foi minerada em algum bloco."""
        c = self.conn.cursor()
        c.execute("SELECT 1 FROM txs WHERE id=?", (tx_id,))
        return c.fetchone() is not None

    def valid_chain(self, chain):
        """
        Determina se uma dada cadeia de blocos é válida.
        Verifica hashes, provas de trabalho, transações e dificuldade.
        """
        if not chain:
            return False

        if chain[0]['index'] != 1 or chain[0]['previous_hash'] != '1' or chain[0]['proof'] != 100:
            print("[VAL_CHAIN_ERRO] Bloco Gênese inválido.")
            return False

        for idx in range(1, len(chain)):
            prev = chain[idx - 1]
            curr = chain[idx]

            prev_hash = self.hash(prev)

            if curr['previous_hash'] != prev_hash:
                print(f"[VAL_CHAIN_ERRO] Hash anterior incorreto no bloco {curr['index']}. Esperado: {prev_hash}, Obtido: {curr['previous_hash']}.")
                return False

            block_declared_difficulty = curr.get('difficulty', DIFFICULTY)

            if not self.valid_proof(prev['proof'], curr['proof'], block_declared_difficulty):
                # hash_check = self.custom_asic_resistant_hash(f"{prev['proof']}{curr['proof']}".encode(), curr['proof'])
                # print(f"[VAL_CHAIN_ERRO] Proof of Work inválido no bloco {curr['index']} com dificuldade {block_declared_difficulty}. Hash: {hash_check}")
                return False

            for tx in curr.get('transactions', []):
                if tx['sender'] == '0':
                    if tx['recipient'] != curr['miner']:
                        print(f"[VAL_CHAIN_ERRO] TX de recompensa inválida no bloco {curr['index']}: Recipiente incorreto.")
                        return False
                    expected_reward = self._get_mining_reward(curr['index'])
                    # Comparar recompensas como floats, mas tx['amount'] é string
                    if abs(float(tx['amount']) - expected_reward) > 0.000001:
                        print(f"[VAL_CHAIN_ERRO] TX de recompensa inválida no bloco {curr['index']}: Valor incorreto. Esperado: {expected_reward}, Obtido: {tx['amount']}")
                        return False
                    continue

                try:
                    pk_for_address_derivation = tx['public_key']
                    if pk_for_address_derivation.startswith('04') and len(pk_for_address_derivation) == 130:
                        pk_for_address_derivation = pk_for_address_derivation[2:]
                    
                    derived_address = hashlib.sha256(bytes.fromhex(pk_for_address_derivation)).hexdigest()[:40]
                    if derived_address != tx['sender']:
                        print(f"[VAL_CHAIN_ERRO] Transação {tx['id']} no bloco {curr['index']}: Endereço ({tx['sender']}) não bate com o derivado da chave pública ({derived_address}).")
                        return False

                    # CRÍTICO: Garantir que amount e fee são strings formatadas para a verificação
                    # Sempre converte para float primeiro, depois formata para string com .8f
                    amount_to_verify = f"{float(tx['amount']):.8f}"
                    fee_to_verify = f"{float(tx['fee']):.8f}"

                    tx_copy_for_signature = {
                        'amount': amount_to_verify,
                        'fee': fee_to_verify,
                        'recipient': tx['recipient'],
                        'sender': tx['sender']
                    }
                    message = json.dumps(tx_copy_for_signature, sort_keys=True, separators=(",", ":")).encode()

                    vk = VerifyingKey.from_string(bytes.fromhex(tx['public_key']), curve=SECP256k1)
                    vk.verify_digest(bytes.fromhex(tx['signature']), hashlib.sha256(message).digest())

                except BadSignatureError:
                    print(f"[VAL_CHAIN_ERRO] Transação {tx['id']} inválida no bloco {curr['index']}: Assinatura inválida.")
                    return False
                except Exception as e:
                    print(f"[VAL_CHAIN_ERRO] Transação {tx['id']} inválida no bloco {curr['index']}: {e}")
                    return False
        return True


    def get_total_difficulty(self, chain_to_check):
        """Calcula a dificuldade acumulada de uma cadeia."""
        total_difficulty = 0
        for block in chain_to_check:
            total_difficulty += block.get('difficulty', DIFFICULTY)
        return total_difficulty

    def resolve_conflicts(self):
        """
        Algoritmo de Consenso: Verifica todos os vizinhos e adota a cadeia mais pesada.
        """
        neighbors = list(known_nodes)
        new_chain = None
        
        # Baseia-se na dificuldade acumulada (Trabalho total realizado)
        my_total_difficulty = self.get_total_difficulty(self.chain)
        max_difficulty = my_total_difficulty

        print(f"[CONSENSO] A verificar {len(neighbors)} vizinhos...")

        for node_url in neighbors:
            if node_url == meu_url: continue
            try:
                # Tenta obter a cadeia do vizinho
                response = requests.get(f"{node_url}/chain", timeout=15)
                if response.status_code == 200:
                    data = response.json()
                    peer_chain = data.get("chain")
                    
                    if not peer_chain: continue

                    peer_difficulty = self.get_total_difficulty(peer_chain)
                    
                    # Se o vizinho tem mais dificuldade acumulada, ele tem a "verdade"
                    if peer_difficulty > max_difficulty:
                        if self.valid_chain(peer_chain):
                            max_difficulty = peer_difficulty
                            new_chain = peer_chain
                            print(f"[CONSENSO] Cadeia superior encontrada em: {node_url}")

            except Exception:
                # Apenas ignora se o nó falhar, permitindo continuar para o próximo
                pass

        if new_chain:
            self.chain = new_chain
            # Limpa o banco de dados e grava a nova cadeia oficial
            self._rebuild_db_from_chain() 
            print(f"[CONSENSO] ✅ Sincronizado com sucesso! Total de blocos: {len(self.chain)}")
            return True

        return False

    def _rebuild_db_from_chain(self):
        print("[REBUILD] 🔨 Reconstruindo índice de transações (Isso faz o saldo aparecer)...")
        try:
            c = self.conn.cursor()
            c.execute("DELETE FROM txs")   # Limpa tudo
            c.execute("DELETE FROM blocks") # Limpa tudo

            for block in self.chain:
                # 1. Salva o Bloco
                c.execute("""
                    INSERT INTO blocks (index_, previous_hash, proof, timestamp, miner, difficulty, protocol_value)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (
                    block['index'], block['previous_hash'], block['proof'],
                    block['timestamp'], block['miner'], block.get('difficulty', 1),
                    block.get('protocol_value', 0.0)
                ))

                # 2. Salva TODAS as Transações do Bloco (Aqui está o seu dinheiro)
                for tx in block['transactions']:
                    c.execute("""
                        INSERT OR IGNORE INTO txs (id, sender, recipient, amount, fee, signature, block_index, public_key)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                        tx['id'], tx['sender'], tx['recipient'], tx['amount'],
                        tx['fee'], tx['signature'], block['index'], tx.get('public_key', '')
                    ))
            
            self.conn.commit()
            print("[REBUILD] ✅ Banco de dados recriado com sucesso!")
        except Exception as e:
            print(f"[REBUILD ERRO] Falha ao reconstruir DB: {e}")

    def balance(self, address):
        """Calcula o saldo de um endereço, incluindo transações pendentes."""
        bal = 0.0
        for block in self.chain:
            for t in block['transactions']:
                if t['sender'] == address:
                    bal -= (float(t['amount']) + float(t['fee'])) # Converter para float para cálculo
                if t['recipient'] == address:
                    bal += float(t['amount']) # Converter para float para cálculo
        
        for t in self.current_transactions:
            if t['sender'] == address:
                bal -= (float(t['amount']) + float(t['fee'])) # Converter para float para cálculo
            if t['recipient'] == address:
                bal += float(t['amount']) # Converter para float para cálculo
        return bal

# --- Funções de Criptografia e Carteira ---
def gerar_endereco(public_key_hex):
    """Gera um endereço de carteira a partir de uma chave pública hexadecimal."""
    try:
        # A chave pública pode vir com prefixo '04'
        if public_key_hex.startswith("04"):
            public_key_hex = public_key_hex[2:]
        public_key_bytes = bytes.fromhex(public_key_hex)
        return hashlib.sha256(public_key_bytes).hexdigest()[:40]
    except ValueError:
        return None

def sign_transaction(private_key_hex, tx_data):
    """
    Assina uma transação com a chave privada ECDSA (SECP256k1).
    tx_data deve ter: 'sender', 'recipient', 'amount' (string), 'fee' (string).
    Retorna a assinatura em hex.
    """
    sk = SigningKey.from_string(bytes.fromhex(private_key_hex), curve=SECP256k1)

    # Recria o dicionário na ordem que o servidor espera.
    # amount e fee já devem ser strings formatadas aqui.
    message_data = {
        'amount':    tx_data['amount'],
        'fee':       tx_data['fee'],
        'recipient': tx_data['recipient'],
        'sender':    tx_data['sender']
    }

    # Serialização determinística sem espaços
    message_json = json.dumps(
        message_data,
        sort_keys=True,
        separators=(',',':')
    ).encode('utf-8')

    print(f"DEBUG_SIGN: JSON da mensagem para assinatura (decodificado): {message_json.decode('utf-8')}")
    print(f"DEBUG_SIGN: Bytes da mensagem para assinatura (raw): {message_json}")
    print(f"DEBUG_SIGN: Hash da mensagem para assinatura (SHA256, HEX): {hashlib.sha256(message_json).hexdigest()}")

    # SHA256 + sign_digest
    message_hash = hashlib.sha256(message_json).digest()
    return sk.sign_digest(message_hash).hex()

def create_wallet():
    """Cria e retorna dados de uma nova carteira."""
    private_key_obj = SigningKey.generate(curve=SECP256k1)
    public_key_obj = private_key_obj.get_verifying_key()
    private_key_hex = private_key_obj.to_string().hex()
    public_key_hex = "04" + public_key_obj.to_string().hex() # Adicionar prefixo '04'
    address = gerar_endereco(public_key_hex)

    if address is None: # Corrigido de '===' para 'is'
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
                        wallet_data['address'] = derived_addr_check
                        # Opcional: Salvar a carteira atualizada se o endereço foi corrigido
                        with open(filepath, "w") as fw:
                            json.dump(wallet_data, fw, indent=4)
                return wallet_data
        except (json.JSONDecodeError, FileNotFoundError):
            return None
    return None

def save_wallet_file(wallet_data, filepath):
    """Salva dados da carteira em um arquivo JSON."""
    with open(filepath, 'w') as f:
        json.dump(wallet_data, f, indent=4)

# --- Flask Endpoints (do nó) ---
@app.route('/', methods=['GET'])
def index_web():
    return "Kert-One Blockchain Node is running!"

@app.route('/miner')
def miner_web():
    return render_template('miner.html')

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

@app.route('/nodes/register', methods=['POST'])
def register_nodes_api():
    data = request.get_json(silent=True) or {}

    # 🔹 Aceita formato {"url": "..."} OU {"ip": "...", "port": "..."}
    new_node_url = data.get("url")

    if not new_node_url:
        new_node_ip = data.get("ip")
        new_node_port = data.get("port")

        if not new_node_ip or not new_node_port:
            return jsonify({"message": "IP/porta ou URL inválidos."}), 400

        new_node_url = f"http://{new_node_ip}:{new_node_port}"

    # 🔹 Normaliza URL
    new_node_url = new_node_url.strip().rstrip("/")
    if not new_node_url.startswith("http://") and not new_node_url.startswith("https://"):
        new_node_url = "http://" + new_node_url

    global meu_url

    # 🔹 Evita registrar a si mesmo
    if new_node_url == meu_url:
        print(f"[INFO] Recebi meu próprio registro ({new_node_url}). Ignorando.")
        return jsonify({
            "message": "Self ignored",
            "known_peers": list(known_nodes)
        }), 200

    # 🔹 Adiciona peer se não existir
    if new_node_url not in known_nodes:
        known_nodes.add(new_node_url)
        salvar_peers(known_nodes)
        print(f"[P2P] Novo peer registrado: {new_node_url}")

        # 🔥 REGISTRO BIDIRECIONAL AUTOMÁTICO (remove dependência de seed)
        try:
            requests.post(
                f"{new_node_url}/nodes/register",
                json={"url": meu_url},
                timeout=5
            )
        except Exception as e:
            print(f"[P2P] Falha no registro reverso: {e}")

    else:
        print(f"[P2P] Peer já conhecido: {new_node_url}")

    return jsonify({
        "message": f"Peer {new_node_url} registrado.",
        "known_peers": list(known_nodes)
    }), 200

@app.route('/nodes', methods=['GET'])
def get_nodes_api():
    return jsonify({'nodes': list(known_nodes)}), 200

@app.route('/nodes/resolve', methods=['GET'])
def resolve_api():
    replaced = blockchain.resolve_conflicts()
    if replaced:
        response = {'message': 'Nossa cadeia foi substituída.'}
    else:
        response = {'message': 'Nossa cadeia é a mais longa.'}
    return jsonify(response), 200

@app.route('/balance/<addr>', methods=['GET'])
def balance_api(addr):
    return jsonify({
        'address': addr,
        'balance': blockchain.balance(addr),
        'coin_name': COIN_NAME,
        'coin_symbol': COIN_SYMBOL
    }), 200

@app.route('/tx/new', methods=['POST'])
def new_transaction_api():
    """Recebe uma nova transação do cliente e a adiciona à fila pendente."""
    print(f"DEBUG_SERVER: Requisição recebida para /tx/new")
    print(f"DEBUG_SERVER: Headers da requisição: {request.headers}")
    print(f"DEBUG_SERVER: Mimetype da requisição: {request.mimetype}")
    print(f"DEBUG_SERVER: Content-Type da requisição: {request.content_type}")
    print(f"DEBUG_SERVER: Dados da requisição (raw): {request.data}")

    raw_values = None
    try:
        raw_values = request.get_json(silent=True)
        print(f"DEBUG_SERVER: Payload JSON parseado (request.get_json()): {raw_values}")
    except Exception as e:
        print(f"DEBUG_SERVER: ERRO - Exceção durante o parsing JSON: {e}")
    
    if raw_values is None:
        print(f"DEBUG_SERVER: ERRO - request.get_json() retornou None. Verifique o Content-Type ou a validade do JSON.")
        return jsonify({'message': 'Erro: Não foi possível parsear o JSON da requisição. Verifique o Content-Type ou a validade do JSON.'}), 400
    
    values = raw_values

    required = ['id', 'sender', 'recipient', 'amount', 'fee', 'public_key', 'signature']
    if not all(k in values for k in required):
        missing = [k for k in required if k not in values]
        print(f"[ERRO 400] Valores ausentes na transação: {missing}")
        return jsonify({'message': f'Valores ausentes na requisição: {", ".join(missing)}'}), 400

    try:
        # amount e fee vêm como strings do cliente, mas podem precisar de formatação
        amount_float = float(values['amount'])
        fee_float = float(values['fee'])
        amount_str_formatted = f"{amount_float:.8f}"
        fee_str_formatted = f"{fee_float:.8f}"

        transaction = {
            'id': values['id'],
            'sender': values['sender'],
            'recipient': values['recipient'],
            'amount': amount_str_formatted, # Armazenar como string formatada
            'fee': fee_str_formatted,       # Armazenar como string formatada
            'public_key': values['public_key'],
            'signature': values['signature'],
            'timestamp': values.get('timestamp', time.time())
        }
    except Exception as e:
        print(f"[ERRO 400] Erro ao construir transação: {e}")
        return jsonify({'message': f'Erro ao processar dados da transação: {e}'}), 400

    temp_tx_for_duplicate_check = {
        'sender': transaction['sender'],
        'recipient': transaction['recipient'],
        'amount': transaction['amount'], # Já é string
        'fee': transaction['fee'],       # Já é string
        'id': transaction.get('id')
    }
    if blockchain.is_duplicate_transaction(temp_tx_for_duplicate_check):
        print(f"[AVISO] Transação duplicada detectada para {transaction['sender']} -> {transaction['recipient']}. Ignorando.")
        return jsonify({'message': 'Transação duplicada detectada. Não adicionada novamente.'}), 200

    try:
        pk_for_address_derivation = transaction['public_key']
        if pk_for_address_derivation.startswith('04') and len(pk_for_address_derivation) == 130:
            pk_for_address_derivation = pk_for_address_derivation[2:]
        
        derived_address = hashlib.sha256(bytes.fromhex(pk_for_address_derivation)).hexdigest()[:40] 
        if derived_address != transaction['sender']:
            print(f"[ERRO 400] Assinatura inválida: Endereço do remetente ({transaction['sender']}) não corresponde à chave pública fornecida ({derived_address}).")
            return jsonify({'message': 'Assinatura inválida: Endereço do remetente não corresponde à chave pública fornecida'}), 400

        if not verify_signature(transaction['public_key'], transaction['signature'], transaction):
            print(f"[ERRO 400] Assinatura inválida ou chave pública malformada para TX ID: {transaction.get('id')}")
            return jsonify({'message': 'Assinatura inválida ou chave pública malformada: Falha na verificação da assinatura'}), 400
            
    except Exception as e:
        print(f"[ERRO 400] Erro inesperado na validação da assinatura: {e}. TX ID: {transaction.get('id')}")
        return jsonify({'message': f'Erro inesperado na validação da transação: {e}'}), 400

    # Usar float() para cálculo de saldo, pois balance() espera floats para isso
    current_balance = blockchain.balance(transaction['sender'])
    required_amount = float(transaction['amount']) + float(transaction['fee'])
    if current_balance < required_amount:
        print(f"[ERRO 400] Saldo insuficiente para {transaction['sender']}: Necessário {required_amount}, Disponível {current_balance}. TX ID: {transaction.get('id')}")
        return jsonify({'message': f'Saldo insuficiente para a transação. Saldo atual: {current_balance}, Necessário: {required_amount}'}), 400

    # Adicionar à fila de transações pendentes (amount e fee já são strings formatadas)
    blockchain.current_transactions.append(transaction)
    
    broadcast_tx_to_peers(transaction)

    response = {'message': f'Transação adicionada à fila de transações pendentes.',
                'coin_name': COIN_NAME,
                'coin_symbol': COIN_SYMBOL,
                'transaction_id': transaction['id']}
    return jsonify(response), 201

def broadcast_tx_to_peers(tx):
    """Envia uma transação para todos os peers conhecidos."""
    print(f"[Broadcast TX] Enviando transação {tx.get('id')} para peers.")
    peers_to_remove = set()
    for peer in known_nodes.copy():
        if peer == meu_url: continue
        try:
            requests.post(f"{peer}/tx/receive", json=tx, timeout=3)
        except requests.exceptions.RequestException as e:
            print(f"[Broadcast TX] Erro ao enviar TX para {peer}: {e}. Removendo peer (se não for seed).")
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
        return jsonify({"message": "Nenhum dado de transação recebido."}), 400

    required = ['id', 'sender', 'recipient', 'amount', 'fee', 'public_key', 'signature']
    if not all(k in tx_data for k in required):
        return jsonify({'message': 'Dados de transação incompletos.'}), 400

    try:
        # amount e fee vêm como strings (esperado), garantir formatação
        amount_float = float(tx_data['amount'])
        fee_float = float(tx_data['fee'])
        amount_str_formatted = f"{amount_float:.8f}"
        fee_str_formatted = f"{fee_float:.8f}"

        temp_tx_for_duplicate_check = {
            'sender': tx_data['sender'],
            'recipient': tx_data['recipient'],
            'amount': amount_str_formatted, # Usar string formatada
            'fee': fee_str_formatted,       # Usar string formatada
            'id': tx_data.get('id')
        }
        if blockchain.is_duplicate_transaction(temp_tx_for_duplicate_check):
            print(f"[RECEIVE TX] Transação {tx_data.get('id')} já existe na fila pendente. Ignorando.")
            return jsonify({'message': 'Transação já conhecida.'}), 200

        # Passar a transação com amount/fee como strings formatadas para verify_signature
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

        # Usar float() para cálculo de saldo, pois balance() espera floats para isso
        current_balance = blockchain.balance(tx_data['sender'])
        required_amount = float(tx_data['amount']) + float(tx_data['fee'])
        if current_balance < required_amount:
            print(f"[RECEIVE TX ERROR] TX {tx_data.get('id')}: Saldo insuficiente para {tx_data['sender']}.")
            return jsonify({'message': 'Transação inválida: Saldo insuficiente.'}), 400

        # Adicionar à fila de transações pendentes (amount e fee já são strings formatadas)
        blockchain.current_transactions.append(tx_for_verification)
        print(f"[RECEIVE TX] Transação {tx_data.get('id')} recebida e adicionada à fila pendente.")
        return jsonify({"message": "Transação recebida e adicionada com sucesso."}), 200

    except Exception as e:
        print(f"[RECEIVE TX ERROR] Erro inesperado ao processar TX {tx_data.get('id')}: {e}")
        return jsonify({'message': f'Erro interno ao processar transação: {e}'}), 500
        
def verify_signature(public_key_hex, signature_hex, tx_data):
    """
    Verifica a assinatura de uma transação.
    tx_data deve conter 'sender', 'recipient', 'amount', 'fee'.
    'amount' e 'fee' podem ser strings ou floats ao entrar nesta função,
    mas serão convertidos para string formatada para a verificação.
    """
    try:
        vk = VerifyingKey.from_string(bytes.fromhex(public_key_hex), curve=SECP256k1)

        # CRÍTICO: Garantir que amount e fee são strings formatadas para a verificação
        # Sempre converte para float primeiro, depois formata para string com .8f
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

        print(f"DEBUG_VERIFY: Chave Pública recebida (hex): {public_key_hex}")
        print(f"DEBUG_VERIFY: Assinatura recebida (hex): {signature_hex}")
        print(f"DEBUG_VERIFY: Dados da mensagem para verificação (antes de json.dumps): {prepared_message_data}")
        print(f"DEBUG_VERIFY: JSON da mensagem para verificação (decodificado): {message.decode('utf-8')}")
        print(f"DEBUG_VERIFY: Bytes da mensagem para verificação (raw): {message}")
        print(f"DEBUG_VERIFY: Hash da mensagem para verificação (SHA256, HEX): {hashlib.sha256(message).hexdigest()}")

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
    global miner_address_global, miner_address

    data = request.get_json(silent=True)
    if not data:
        data = request.form.to_dict() if request.form else {}

    address = data.get("address") or data.get("miner_address")

    if not address:
        print("[MINER] Endereço do minerador NÃO recebido")
        return jsonify({"message": "Endereço do minerador ausente."}), 400

    miner_address_global = address
    miner_address = address
    print(f"[MINER] Endereço do minerador definido: {miner_address_global}")

    return jsonify({
        "message": "Endereço do minerador definido",
        "address": miner_address_global
    }), 200

# NOVA ROTA: Definir modo de mineração (CPU/GPU)
@app.route('/miner/set_mode', methods=['POST'])
def set_miner_mode_api():
    data = request.get_json()
    mode = data.get('mode') # 'CPU' or 'GPU'
    if mode == 'GPU':
        if HAS_GPU:
            blockchain.use_gpu = True
            msg = "Modo GPU Ativado (OpenCL)"
        else:
            return jsonify({"message": "GPU não disponível. Mantendo modo CPU."}), 400
    else:
        blockchain.use_gpu = False
        msg = "Modo CPU Ativado"
        
    print(f"[MINER] {msg}")
    return jsonify({"message": msg}), 200


@app.route('/miner/stop', methods=['POST'])
def stop_mining_api():
    global mining_active, mining_stop_flag
    if not mining_active:
        return jsonify({"message": "Mineração não está ativa."}), 200

    try:
        mining_stop_flag.set()
    except Exception:
        pass

    with miner_lock:
        mining_active = False
    print("[MINER] Pedido de parada recebido — mineração encerrada.")
    return jsonify({"message": "Mineração parada."}), 200

@app.route('/mine', methods=['GET'])
def mine_api():
    global mining_active, miner_address_global, mining_stop_flag, mining_result

    proof = -1  # 🔒 SEMPRE DEFINIDO

    if not miner_address_global:
        return jsonify({
            "message": "Endereço do minerador não definido. Use /miner/set_address."
        }), 400

    with miner_lock:
        if mining_active:
            return jsonify({"message": "Mineração já está em andamento."}), 409
        mining_active = True

    try:
        last_block = blockchain.last_block()
        if not last_block:
            return jsonify({"message": "Blockchain não inicializada."}), 500

        last_proof = last_block['proof']
        difficulty = blockchain._calculate_difficulty_for_index(len(blockchain.chain) + 1)

        mining_stop_flag.clear()
        mining_result.value = -1

        if getattr(blockchain, 'use_gpu', False) and HAS_GPU:
            print("[MINER] 🚀 Mineração GPU REAL ativada")
            proof = Blockchain._mine_gpu(
                last_proof,
                difficulty,
                mining_stop_flag,
                mining_result
            )
        else:
            print("[MINER] 🧠 Mineração CPU REAL ativada")
            proof = blockchain.proof_of_work(last_proof)

        if proof == -1:
            return jsonify({"message": "Mineração interrompida."}), 200

        previous_hash = blockchain.hash(last_block)
        new_block = blockchain.new_block(proof, previous_hash, miner_address_global)

        broadcast_block(new_block)

        return jsonify({
            "message": "✅ Bloco minerado com sucesso!",
            "index": new_block["index"],
            "proof": new_block["proof"],
            "difficulty": new_block["difficulty"]
        }), 200

    finally:
        with miner_lock:
            mining_active = False


# --- Funções de Peer-to-Peer (do nó) ---
def broadcast_block(block):
    """Envia um bloco recém-minerado para todos os peers E obrigatoriamente para os Seeds."""
    
    # 1. Cria um conjunto com TODOS os nós conhecidos + os SEEDS oficiais
    # O uso de 'set' evita duplicatas se o seed já estiver no peers.json
    all_targets = set(known_nodes) | set(SEED_NODES)
    
    print(f"[BROADCAST] 🚀 Enviando bloco #{block['index']} para {len(all_targets)} nós (Prioridade: Seeds)...")
    
    peers_to_remove = set()
    
    for peer in all_targets:
        # Pula se for o próprio endereço (evita loop)
        if peer == meu_url: continue 
        
        try:
            # Tenta enviar o bloco via POST
            print(f"   -> Enviando para: {peer}...")
            response = requests.post(f"{peer}/blocks/receive", json=block, timeout=5)
            
            # Se for o SEEND e der certo, avisa no log
            if peer in SEED_NODES and response.status_code == 200:
                print(f"   ✅ [CONFIRMADO] Bloco aceito pelo SEED OFICIAL: {peer}")
                
        except requests.exceptions.RequestException as e:
            print(f"   ❌ Erro ao enviar bloco para {peer}: {e}")
            
            # Só remove da lista se NÃO for um Seed oficial
            if peer not in SEED_NODES:
                peers_to_remove.add(peer)
        except Exception as e:
            print(f"   ❌ Erro inesperado em {peer}: {e}")
    
    # Atualiza a lista de peers removendo os que falharam (exceto seeds)
    if peers_to_remove:
        known_nodes.difference_update(peers_to_remove)
        salvar_peers(known_nodes)

def discover_peers():
    global known_nodes, meu_url

    peers_snapshot = list(known_nodes)
    online_peers = set()

    for peer in peers_snapshot:
        if not peer or peer == meu_url:
            if peer == meu_url: online_peers.add(peer)
            continue

        try:
            # Tenta verificar se o peer está vivo
            r = requests.get(f"{peer.rstrip('/')}/chain", timeout=3)

            if r.status_code == 200:
                online_peers.add(peer.rstrip('/'))

                # 🔥 Tenta puxar novos amigos deste peer
                try:
                    r2 = requests.get(f"{peer.rstrip('/')}/nodes/share", timeout=3)
                    if r2.status_code == 200:
                        remote_nodes = r2.json()
                        # Se vier uma lista direto: [url1, url2]
                        if isinstance(remote_nodes, list):
                            for n in remote_nodes:
                                if n and n.strip().rstrip('/') != meu_url:
                                    online_peers.add(n.strip().rstrip('/'))
                except:
                    pass
        except:
            print(f"[P2P] Peer offline ignorado: {peer}")

    if meu_url: online_peers.add(meu_url)
    known_nodes = set(online_peers)
    salvar_peers(known_nodes)

def get_my_ip():
    """Tenta obter o IP local do nó e avisa se for privado."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80)) # Conecta a um IP externo para obter o IP local de saída
        ip = s.getsockname()[0]
        s.close()
        try:
            # Verifica se o IP é privado
            if ipaddress.ip_address(ip).is_private:
                print(f"[AVISO IP] Seu IP ({ip}) é privado. Para comunicação completa com peers públicos, configure o redirecionamento de portas (port forwarding) para a porta {port} no seu roteador.")
        except ValueError:
            # Não é um endereço IP válido, apenas continua
            pass
        return ip
    except Exception:
        print("[AVISO IP] Não foi possível determinar o IP local. Usando 127.0.0.1 como fallback. A comunicação com peers externos pode ser limitada.")
        return "127.0.0.1" # Retorna localhost como fallback

def load_or_create_node_id(filename="node_id.txt"):
    """Carrega ou cria um ID de nó único."""
    if os.path.exists(filename):
        with open(filename, "r") as f:
            return f.read().strip()
    else:
        new_id = str(uuid4()).replace("-", "")[:16]
        with open(filename, "w") as f:
            f.write(new_id)
        return new_id

# Funções auxiliares para auto_sync_checker (movidas para antes do main)
def auto_sync_checker(blockchain_instance):
    while True:
        comparar_ultimos_blocos(blockchain_instance)
        time.sleep(60)

def comparar_ultimos_blocos(blockchain_instance):
    if blockchain_instance is None or blockchain_instance.last_block() is None:
        print("[SYNC] Blockchain ainda não inicializada. Aguardando...")
        return

    print("\n🔍 Verificando sincronização com os peers...")
    local_block = blockchain_instance.last_block()
    local_hash = blockchain_instance.hash(local_block)

    for peer in known_nodes.copy():
        try:
            r = requests.get(f"{peer}/sync/check", timeout=5)
            data = r.json()
            peer_index = data['index']
            peer_hash = data['hash']

            if peer_index == local_block['index'] and peer_hash == local_hash:
                print(f"[SYNC ✅] {peer} está sincronizado com índice {peer_index}.")
            else:
                print(f"[SYNC ⚠️] {peer} DIFERENTE! Local: {local_block['index']} | Peer: {peer_index}")
                threading.Thread(target=blockchain_instance.resolve_conflicts, daemon=True).start()
        except Exception as e:
            print(f"[SYNC ❌] Falha ao verificar {peer}: {e}")
            if peer not in SEED_NODES:
                known_nodes.discard(peer)
                salvar_peers(known_nodes)

def _continuous_mine():
    global mining_active, blockchain, miner_address_global, mining_stop_flag

    print("[MINER] 🚀 Thread de mineração contínua iniciada (Modo Sincronizado).")
    while mining_active:
        try:
            blockchain.resolve_conflicts()
            last_block = blockchain.last_block()
            if not last_block:
                time.sleep(5)
                continue

            last_proof = last_block['proof']
            mining_stop_flag.clear()
            proof = blockchain.proof_of_work(last_proof)
            if proof == -1:
                time.sleep(1)
                continue

            previous_hash = blockchain.hash(last_block)
            new_block = blockchain.new_block(proof, previous_hash, miner_address_global)
            print(f"💎 [MINER] Bloco {new_block['index']} minerado com sucesso!")
            broadcast_block(new_block)
            time.sleep(2)

        except Exception as e:
            print(f"[MINER ERROR] {e}")
            time.sleep(5)

    print("[MINER] Thread de mineração parada.")
    
# --- Cliente Kert-One Core GUI (QMainWindow) ---
# --- Cliente Kert-One Core GUI Corrigido ---
class KertOneCoreClient(QMainWindow):
    start_mining_timer_signal = pyqtSignal()
    log_signal = pyqtSignal(str, str)
    chain_viewer_signal = pyqtSignal(str)

    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"Kert-One Core Client ({COIN_NAME})")
        self.setGeometry(100, 100, 1000, 700)
        self.mining_active = False
        self.miner_address = None
        self.wallet_data = None
        self.apply_dark_theme()
        
        # Conecta no Nó Local dinamicamente (Porta 5001)
        self.api_client = APIClient(f"http://127.0.0.1:5001") 
        self.setup_ui()
        self.load_wallet()

        self.chain_viewer_signal.connect(self.chain_viewer.setPlainText)
        self.log_signal.connect(self.update_log_viewer)
        self.start_mining_timer_signal.connect(self.start_mining_timer_safe)

        self.mining_timer = QTimer(self)
        self.mining_timer.setInterval(6000)
        self.mining_timer.timeout.connect(self.mine_block_via_api)

        # 🟢 DINÂMICO: A GUI agora segue a URL global definida no boot
        self._on_flask_url_ready("http://127.0.0.1:5001")


    def update_log_viewer(self, message, message_type="info"):
        color_map = {"info": "#a0a0ff", "success": "#66ff66", "error": "#ff6666", "warning": "#ffff66"}
        color = color_map.get(message_type, "#f0f0f0")
        timestamp = datetime.now().strftime('%H:%M:%S')
        self.log_viewer.append(f'[{timestamp}] <font color="{color}">{message}</font>')

    @pyqtSlot()
    def start_mining_timer_safe(self):
        if not self.mining_active:
            self.mining_active = True
            self.mining_timer.start()
            self.log_signal.emit("Mineração iniciada com segurança.", "success")

    def apply_dark_theme(self):
        """Aplica um tema escuro (Dark Mode)."""
        dark_palette = QPalette()
        dark_palette.setColor(QPalette.ColorRole.Window, QColor(45, 45, 45))
        dark_palette.setColor(QPalette.ColorRole.WindowText, QColor(200, 200, 200))
        dark_palette.setColor(QPalette.ColorRole.Base, QColor(30, 30, 30))
        dark_palette.setColor(QPalette.ColorRole.Text, QColor(200, 200, 200))
        dark_palette.setColor(QPalette.ColorRole.Button, QColor(60, 60, 60))
        dark_palette.setColor(QPalette.ColorRole.ButtonText, QColor(200, 200, 200))
        dark_palette.setColor(QPalette.ColorRole.Highlight, QColor(42, 130, 218))
        QApplication.instance().setPalette(dark_palette)
        
        self.setStyleSheet("""
            QWidget { background-color: rgb(45, 45, 45); color: rgb(200, 200, 200); }
            QPushButton { background-color: rgb(60, 60, 60); border: 1px solid rgb(80, 80, 80); padding: 8px; border-radius: 5px; }
            QPushButton:hover { background-color: rgb(80, 80, 80); }
            QPushButton:pressed { background-color: rgb(100, 100, 100); }
            QLineEdit, QTextEdit, QPlainTextEdit { background-color: rgb(30, 30, 30); border: 1px solid rgb(60, 60, 60); padding: 5px; border-radius: 3px; }
            QGroupBox { border: 1px solid rgb(80, 80, 80); margin-top: 10px; padding-top: 15px; }
            QGroupBox::title { subcontrol-origin: margin; subcontrol-position: top left; padding: 0 5px; color: rgb(150, 150, 255); }
            QTabWidget::pane { border: 1px solid rgb(60, 60, 60); }
            QTabBar::tab { background: rgb(55, 55, 55); border: 1px solid rgb(60, 60, 60); padding: 8px; border-bottom: none; }
            QTabBar::tab:selected { background: rgb(75, 75, 75); border-bottom: none; }
            #LogViewer { background-color: #202020; color: #f0f0f0; border: none; }
        """)

    def setup_ui(self):
        """Configura a interface principal."""
        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self.main_layout = QVBoxLayout(self.central_widget)

        self.tabs = QTabWidget()
        self.tab_wallet = QWidget()
        self.tab_send = QWidget()
        self.tab_mine = QWidget()
        self.tab_network = QWidget()
        
        self.tabs.addTab(self.tab_wallet, "Carteira")
        self.tabs.addTab(self.tab_send, "Enviar")
        self.tabs.addTab(self.tab_mine, "Mineração")
        self.tabs.addTab(self.tab_network, "Rede/Blockchain")
        
        self.main_layout.addWidget(self.tabs)
        
        self.log_viewer = QTextEdit() 
        self.log_viewer.setObjectName("LogViewer")
        self.log_viewer.setReadOnly(True)
        self.main_layout.addWidget(QLabel("Log de Atividade:"))
        self.main_layout.addWidget(self.log_viewer, 3)

        self.status_bar = QStatusBar(self)
        self.setStatusBar(self.status_bar)
        self.status_bar.showMessage(f"Cliente Kert-One conectado ao nó: {meu_url}", 5000)

        self.setup_wallet_tab()
        self.setup_send_tab()
        self.setup_mine_tab()
        self.setup_network_tab()
        
        node_info_group = QGroupBox("Informações do Nó")
        node_info_layout = QFormLayout(node_info_group)
        
        # --- CORREÇÃO AQUI ---
        # Antes estava: "Aguardando..."
        # Agora ele pega a variável global 'meu_url' e já mostra na tela
        self.node_id_label = QLabel(f"<span style='font-weight:bold;'>{node_id[:16]}...</span>")
        self.node_url_label = QLabel(f"<span style='font-weight:bold;'>{meu_url}</span>") 
        # ---------------------
        
        node_info_layout.addRow("ID do Nó:", self.node_id_label)
        node_info_layout.addRow("URL do Nó:", self.node_url_label)
        
        self.main_layout.insertWidget(0, node_info_group)

        
    @pyqtSlot(str)
    def _on_flask_url_ready(self, url):
        global meu_url
        meu_url = url
        self.api_client.set_base_url(meu_url)

        self.update_log_viewer(f"Servidor Flask pronto em: {meu_url}", "success")
        self.node_url_label.setText(f"<span style='font-weight:bold;'>{meu_url}</span>")
        self.status_bar.showMessage(f"Cliente Kert-One conectado ao nó: {meu_url}", 5000)

        # self.update_ui_info()  <-- APAGUE ESTA LINHA OU COLOQUE O '#' NA FRENTE


    def update_log_viewer(self, message, message_type="info"):
        """Adiciona mensagens ao visualizador de log com cores."""
        color_map = {
            "info": "#a0a0ff",    
            "success": "#66ff66", 
            "error": "#ff6666",   
            "warning": "#ffff66", 
            "default": "#f0f0f0"  
        }
        color = color_map.get(message_type, color_map["default"])
        
        timestamp = datetime.now().strftime('%H:%M:%S')
        formatted_message = f"[{timestamp}] {message}"
        
        self.log_viewer.append(f'<font color="{color}">{formatted_message}</font>')

    # --- Aba Carteira (Opções 1 e 2 do CLI) ---
    
    def setup_wallet_tab(self):
        layout = QVBoxLayout(self.tab_wallet)
        
        wallet_group = QGroupBox("Carteira Atual")
        wallet_layout = QFormLayout(wallet_group)
        
        self.balance_label = QLabel(f"0.0 {COIN_SYMBOL}")
        self.balance_label.setFont(QFont("Arial", 28, QFont.Weight.Bold))
        
        self.address_label = QLineEdit("N/A")
        self.address_label.setReadOnly(True)
        self.public_key_label = QTextEdit("N/A")
        self.public_key_label.setReadOnly(True)
        self.public_key_label.setFixedHeight(80)
        
        wallet_layout.addRow("Saldo Atual:", self.balance_label)
        wallet_layout.addRow("Endereço:", self.address_label)
        wallet_layout.addRow("Chave Pública:", self.public_key_label)
        
        layout.addWidget(wallet_group)

        button_layout = QHBoxLayout()
        new_wallet_btn = QPushButton("Criar Nova Carteira")
        new_wallet_btn.clicked.connect(self.create_new_wallet)
        load_wallet_btn = QPushButton("Carregar Carteira (client_wallet.json)")
        load_wallet_btn.clicked.connect(self.load_wallet)
        check_balance_btn = QPushButton("Atualizar Saldo")
        check_balance_btn.clicked.connect(self.check_wallet_balance)

        button_layout.addWidget(new_wallet_btn)
        button_layout.addWidget(load_wallet_btn)
        button_layout.addWidget(check_balance_btn)
        layout.addLayout(button_layout)
        
        layout.addStretch(1)

    def create_new_wallet(self):
        """Cria uma nova carteira, salva e carrega na UI."""
        wallet_data = create_wallet()
        if wallet_data:
            save_wallet_file(wallet_data, WALLET_FILE)
            self.wallet_data = wallet_data
            self.update_wallet_status()
            self.log_signal.emit(f"Nova carteira criada e salva em {WALLET_FILE}.", "success")
            QMessageBox.information(self, "Carteira Criada", f"Nova carteira salva com sucesso. Endereço: {wallet_data['address']}")
            self.check_wallet_balance()
        else:
            self.log_signal.emit("Falha ao criar nova carteira.", "error")

    def load_wallet(self):
        """Carrega a carteira do arquivo e atualiza a UI."""
        self.wallet_data = load_wallet_file(WALLET_FILE)
        if self.wallet_data:
            self.update_wallet_status()
            self.log_signal.emit(f"Carteira carregada com sucesso.", "info")
            self.check_wallet_balance()
        else:
            self.update_wallet_status()
            self.log_signal.emit("Arquivo de carteira não encontrado ou corrompido.", "warning")
            
    def update_wallet_status(self):
        """Atualiza a UI com os dados da carteira carregada."""
        if self.wallet_data:
            self.address_label.setText(self.wallet_data.get('address', 'N/A'))
            self.public_key_label.setText(self.wallet_data.get('public_key', 'N/A'))
            self.status_bar.showMessage(f"Carteira carregada: {self.wallet_data['address']}", 5000)
        else:
            self.address_label.setText("N/A")
            self.public_key_label.setText("N/A")
            self.balance_label.setText("0.0 KRT")
            self.status_bar.showMessage("Nenhuma carteira carregada.", 5000)

    def check_wallet_balance(self):
        """Consulta o saldo da carteira carregada no nó da blockchain via API."""
        if not self.wallet_data:
            self.log_signal.emit("Nenhuma carteira carregada.", "warning")
            return

        address = self.wallet_data['address']
        
        threading.Thread(target=self._fetch_balance_async, args=(address,)).start()

    def _fetch_balance_async(self, address):
        """Função para buscar o saldo em segundo plano."""
        try:
            response = requests.get(f"{meu_url}/balance/{address}", timeout=5) # Usar meu_url
            response.raise_for_status()
            balance_data = response.json()
            balance = balance_data.get('balance', 0)
            
            self.balance_label.setText(f"{balance} {COIN_SYMBOL}")
            self.log_signal.emit(f"Saldo atualizado: {balance} {COIN_SYMBOL}", "info")
            
        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Erro ao conectar ao nó ({meu_url}) ou buscar saldo: {e}", "error")
            self.balance_label.setText("Erro de Conexão")

    # --- Aba Enviar (Opção 3 do CLI) ---

    def setup_send_tab(self):
        layout = QVBoxLayout(self.tab_send)
        
        transaction_group = QGroupBox("Nova Transação")
        form_layout = QFormLayout(transaction_group)
        
        self.recipient_input = QLineEdit()
        self.amount_input = QLineEdit()
        self.fee_input = QLineEdit()
        
        validator = QDoubleValidator(0.0, 100000000.0, 8, self) 
        validator.setNotation(QDoubleValidator.StandardNotation)
        
        self.amount_input.setValidator(validator)
        self.fee_input.setValidator(validator)

        form_layout.addRow("Destinatário (Endereço):", self.recipient_input)
        form_layout.addRow(f"Valor ({COIN_SYMBOL}):", self.amount_input)
        form_layout.addRow("Taxa (Fee):", self.fee_input)

        send_btn = QPushButton("Assinar e Enviar Transação")
        send_btn.clicked.connect(self.enviar_transacao)
        
        layout.addWidget(transaction_group)
        layout.addWidget(send_btn)
        layout.addStretch(1)

    def enviar_transacao(self):
        """
        Cria, assina e envia uma nova transação para o nó via interface gráfica.
        """
        if not self.wallet_data:
            QMessageBox.warning(self, "Aviso", "Nenhuma carteira carregada.")
            return
    
        recipient_addr = self.recipient_input.text().strip()
        amount_str      = self.amount_input.text().strip().replace(',', '.')
        fee_str         = self.fee_input.text().strip().replace(',', '.')

        if not recipient_addr or not amount_str or not fee_str:
            QMessageBox.warning(self, "Erro", "Todos os campos são obrigatórios.")
            return

        try:
            amount = float(amount_str)
            fee    = float(fee_str)
            if amount <= 0 or fee < 0:
                raise ValueError("Valor ou taxa inválidos.")

            transaction_id = str(uuid4())

            amount_fmt = f"{amount:.8f}"
            fee_fmt     = f"{fee:.8f}"

            # Passar amount e fee como strings formatadas para sign_transaction
            tx_data_for_signing = {
                'sender':    self.wallet_data['address'],
                'recipient': recipient_addr,
                'amount':    amount_fmt,
                'fee':       fee_fmt
            }
            signature = sign_transaction(self.wallet_data['private_key'], tx_data_for_signing)
            if signature is None:
                raise Exception("Falha ao assinar a transação.")

            tx_full_data = {
                'id':          transaction_id,
                'sender':      self.wallet_data['address'],
                'recipient':   recipient_addr,
                'amount':      amount_fmt,       # Armazenar como string formatada
                'fee':         fee_fmt,          # Armazenar como string formatada
                'signature':   signature,
                'public_key':  self.wallet_data['public_key'],
                'timestamp':   time.time()
            }

            self.log_signal.emit("Enviando transação para o nó...", "info")
            threading.Thread(
                target=self._send_transaction_async,
                args=(tx_full_data,),
                daemon=True
            ).start()

        except ValueError as e:
            QMessageBox.critical(self, "Erro de Entrada", f"Valor inválido: {e}")
        except Exception as e:
            self.log_signal.emit(f"Ocorreu um erro inesperado: {e}", "error")

    def _send_transaction_async(self, tx_full_data):
        """Função para enviar a transação via HTTP em segundo plano."""
        try:
            response = requests.post(f"{meu_url}/tx/new", json=tx_full_data, timeout=10) # Usar meu_url
            response.raise_for_status()

            if response.status_code in [200, 201]:
                self.log_signal.emit(f"Transação enviada com sucesso: {response.json().get('message')}", "success")
                self._clear_transaction_fields()
                self.check_wallet_balance() 
            else:
                self.log_signal.emit(f"Erro ao enviar transação: {response.json().get('error', response.text)}", "error")

        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Taxa é obrigatória ou erro de conexão com o nó ({meu_url}) ao enviar transação: {e}", "error")


    def _clear_transaction_fields(self):
        """Limpa os campos de input de transação."""
        self.recipient_input.clear()
        self.amount_input.clear()
        self.fee_input.clear()

    # --- Aba Mineração (Opções 4, 8, 9 do CLI) ---

    def setup_mine_tab(self):
        layout = QVBoxLayout(self.tab_mine)
        
        # --- Configuração de Endereço ---
        mine_addr_group = QGroupBox("Carteira de Recompensa")
        mine_addr_layout = QHBoxLayout(mine_addr_group)
        self.miner_addr_input = QLineEdit()
        self.miner_addr_input.setPlaceholderText("Endereço para receber KERT minerados")
        mine_addr_layout.addWidget(self.miner_addr_input)
        layout.addWidget(mine_addr_group)

        # --- Seleção de Hardware (GPU/CPU) ---
        hw_group = QGroupBox("Modo de Mineração (Hardware)")
        hw_layout = QHBoxLayout(hw_group)
        
        self.radio_cpu = QRadioButton("CPU (Multicore)")
        self.radio_gpu = QRadioButton("GPU (OpenCL Real)")
        
        # Lógica de ativação dos botões
        if HAS_GPU:
            self.radio_gpu.setChecked(True)
            self.radio_gpu.setText("GPU (OpenCL Real - DETECTADA)")
        else:
            self.radio_cpu.setChecked(True)
            self.radio_gpu.setEnabled(False) # Desativa se não tiver drivers
            self.radio_gpu.setText("GPU (Drivers não encontrados)")

        # Conectar sinais para enviar configuração ao backend
        self.radio_cpu.toggled.connect(lambda: self.update_mining_mode("CPU"))
        self.radio_gpu.toggled.connect(lambda: self.update_mining_mode("GPU"))

        hw_layout.addWidget(self.radio_cpu)
        hw_layout.addWidget(self.radio_gpu)
        layout.addWidget(hw_group)

        # --- Controle de Mineração ---
        mining_control_group = QGroupBox("Controle")
        mining_control_layout = QHBoxLayout(mining_control_group)
        
        self.mine_single_btn = QPushButton("Minerar 1 Bloco")
        self.start_mining_btn = QPushButton("Iniciar Mineração Contínua")
        self.stop_mining_btn = QPushButton("Parar")
        self.stop_mining_btn.setEnabled(False)

        self.mine_single_btn.clicked.connect(self.mine_single_block)
        self.start_mining_btn.clicked.connect(self.start_continuous_mining)
        self.stop_mining_btn.clicked.connect(self.stop_continuous_mining)

        mining_control_layout.addWidget(self.mine_single_btn)
        mining_control_layout.addWidget(self.start_mining_btn)
        mining_control_layout.addWidget(self.stop_mining_btn)
        
        layout.addWidget(mining_control_group)
        layout.addStretch(1)

    def update_mining_mode(self, mode):
        """Envia requisição ao nó para alterar o modo de mineração."""
        # Apenas processa quando o botão for ativado (toggled=True)
        sender = self.sender()
        if sender.isChecked():
            try:
                requests.post(f"{meu_url}/miner/set_mode", json={'mode': mode})
                self.log_signal.emit(f"Modo de mineração alterado para: {mode}", "info")
            except:
                self.log_signal.emit("Erro ao alterar modo de mineração.", "error")

    def get_miner_address(self):
        addr = self.miner_addr_input.text().strip()
        if addr:
            return addr
        if self.wallet_data and 'address' in self.wallet_data:
            return self.wallet_data['address']
        QMessageBox.warning(self, "Aviso", "Nenhum endereço de mineração fornecido e nenhuma carteira carregada.")
        return None

    def mine_single_block(self):
        """Inicia uma mineração de bloco único via API em thread separada."""
        miner_addr = self.get_miner_address()
        if miner_addr:
            self.log_signal.emit("Iniciando mineração de bloco único...", "info")
            threading.Thread(target=self._mine_async, args=(miner_addr,)).start()

    def start_continuous_mining(self):
        if self.mining_active:
            self.log_signal.emit("Mineração já está ativa.", "warning")
            return
    
        addr = self.get_miner_address()
        if not addr:
            return
    
        self.miner_address = addr
        self.mining_active = True
        self.mine_single_btn.setEnabled(False)
        self.start_mining_btn.setEnabled(False)
        self.stop_mining_btn.setEnabled(True)
        self.radio_cpu.setEnabled(False) # Bloqueia troca durante mineração
        self.radio_gpu.setEnabled(False)
        
        self.status_bar.showMessage(f"Mineração contínua ativa para {self.miner_address}...", 0)
        self.mining_timer.start(5000)  # 5 segundos
        self.log_signal.emit("Mineração contínua iniciada.", "success")

    def stop_continuous_mining(self):
        if not self.mining_active:
            return
        self.mining_active = False
        self.mining_timer.stop()
        self.mine_single_btn.setEnabled(True)
        self.start_mining_btn.setEnabled(True)
        self.stop_mining_btn.setEnabled(False)
        self.radio_cpu.setEnabled(True) # Desbloqueia troca
        if HAS_GPU: self.radio_gpu.setEnabled(True)
        
        self.status_bar.showMessage("Mineração contínua parada.", 5000)
        self.log_signal.emit("Mineração contínua parada.", "info")

    def _mine_async(self, miner_address):
        """Método que define o endereço do minerador e executa a mineração em thread separada."""
        try:
            self.log_signal.emit(f"Definindo endereço do minerador no nó...", "info")
            set_addr_response = requests.post(f"{meu_url}/miner/set_address", json={"address": miner_address}, timeout=10)
            set_addr_response.raise_for_status()

            self.log_signal.emit(f"Endereço definido: {miner_address}. Iniciando mineração...", "info")

            response = requests.get(f"{meu_url}/mine", timeout=30)
            response.raise_for_status()

            result = response.json()
            self.log_signal.emit(f"✅ Bloco minerado com sucesso: {result.get('message', '')}", "success")
            self.check_wallet_balance()

        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Dificuldade alta: {e}. Minerando o próximo bloco...", "error")


    def mine_block_via_api(self):
        if not self.mining_active:
            return
    
        if not self.miner_address:
            self.log_signal.emit("Endereço do minerador não definido. Abortando mineração.", "error")
            return

        threading.Thread(target=self._mine_async, args=(self.miner_address,)).start()
    
    # --- Aba Rede/Blockchain (Opções 5, 6, 7 e 10 do CLI) ---

    def setup_network_tab(self):
        layout = QVBoxLayout(self.tab_network)

        chain_group = QGroupBox("Blockchain View")
        chain_layout = QVBoxLayout(chain_group)

        self.chain_viewer = QPlainTextEdit()
        self.chain_viewer.setReadOnly(True)
        self.chain_viewer.setPlaceholderText("Clique em 'Ver Blockchain Completa' para carregar os dados do nó.")

        self.view_chain_btn = QPushButton("Ver Blockchain Completa")
        self.sync_chain_btn = QPushButton("Sincronizar Blockchain (Consenso)")

        chain_layout.addWidget(self.chain_viewer)
        chain_layout.addWidget(self.view_chain_btn)
        chain_layout.addWidget(self.sync_chain_btn)

        self.view_chain_btn.clicked.connect(self.view_blockchain)
        self.sync_chain_btn.clicked.connect(self.sync_blockchain)

        layout.addWidget(chain_group)

        network_options_group = QGroupBox("Opções de Rede")
        network_options_layout = QHBoxLayout(network_options_group)

        self.register_peer_btn = QPushButton("Registrar Novo Peer")
        self.consult_contract_btn = QPushButton("Consultar Contrato Inteligente")

        self.register_peer_btn.clicked.connect(self.register_peer_dialog)
        self.consult_contract_btn.clicked.connect(self.consult_contract_dialog)

        network_options_layout.addWidget(self.register_peer_btn)
        network_options_layout.addWidget(self.consult_contract_btn)

        layout.addWidget(network_options_group)

        self.open_urls_button = QPushButton("Abrir Portais")
        self.open_urls_button.clicked.connect(self.abrir_portais)
        layout.addWidget(self.open_urls_button)

        layout.addStretch(1)


    def abrir_portais(self):
        import webbrowser # Importar aqui para evitar problemas de dependência
        webbrowser.open(f"http://{meu_ip}:{port}/") # Usar meu_ip e port
        webbrowser.open(f"http://{meu_ip}:{port}/miner") # Usar meu_ip e port
        webbrowser.open("https://kert-one.com/")
        self.log_signal.emit("Abrindo portais do Kert-One...", "info")


    def view_blockchain(self):
        """Busca e exibe a blockchain completa do nó."""
        self.log_signal.emit("Buscando blockchain completa...", "info")
        threading.Thread(target=self._fetch_blockchain_async).start()

    def _fetch_blockchain_async(self):
        """Função para buscar a blockchain em segundo plano."""
        try:
            response = requests.get(f"{meu_url}/chain", timeout=10) # Usar meu_url
            response.raise_for_status()
            chain_data = response.json()
            
            formatted_chain = json.dumps(chain_data, indent=2)
            
            self.chain_viewer_signal.emit(formatted_chain)
            self.log_signal.emit(f"Blockchain carregada. Comprimento: {len(chain_data['chain'])} blocos.", "success")
        
        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Erro ao buscar blockchain: {e}", "error")
            self.chain_viewer_signal.emit("Erro ao carregar a blockchain.")

    def sync_blockchain(self):
        """Inicia a sincronização da blockchain numa thread separada."""
        threading.Thread(target=self._sync_blockchain_async, daemon=True).start()
        
    def _sync_blockchain_async(self):
        while True:
            try:
                self.log_signal.emit("Iniciando sincronização (consenso)...", "info")
                response = requests.get(f"{meu_url}/nodes/resolve", timeout=30) # Usar meu_url
                response.raise_for_status()
                data = response.json()

                if data.get("message") == "Nossa cadeia foi substituída.":
                    self.log_signal.emit("Blockchain sincronizada com sucesso. Cadeia atualizada para a mais longa.", "success")
                    self.view_blockchain()
                else:
                    self.log_signal.emit("Blockchain já sincronizada ou não houve alteração.", "info")

            except requests.exceptions.RequestException as e:
                self.log_signal.emit(f"Erro ao sincronizar com o nó: {e}", "error")

            time.sleep(10)

    def register_peer_dialog(self):
        """Diálogo para registrar um novo peer."""
        text, ok = QInputDialog.getText(self, 'Registrar Peer', 'Digite a URL completa do novo peer (ex: http://IP:PORTA):')
        if ok and text:
            self.log_signal.emit(f"Tentando registrar peer: {text}", "info")
            threading.Thread(target=self._register_peer_async, args=(text,)).start()
    
    def _register_peer_async(self, node_url):
        """Função para registrar peer em segundo plano."""
        try:
            parsed_url = urlparse(node_url)
            peer_ip = parsed_url.hostname
            peer_port = parsed_url.port or 5000 

            if not peer_ip:
                self.log_signal.emit(f"URL do peer inválida: {node_url}", "error")
                return

            payload = {'ip': peer_ip, 'port': peer_port}
            response = requests.post(f"{meu_url}/nodes/register", json=payload, timeout=10) # Usar meu_url
            response.raise_for_status()
            
            self.log_signal.emit(f"Peer '{node_url}' registrado com sucesso! Resposta: {response.json()}", "success")
        
        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Erro ao registrar peer: {e}", "error")

    def consult_contract_dialog(self):
        """Diálogo para consultar um contrato inteligente."""
        text, ok = QInputDialog.getText(self, 'Consultar Contrato', 'Digite o endereço do contrato inteligente:')
        if ok and text:
            self.log_signal.emit(f"Consultando contrato: {text}", "info")
            threading.Thread(target=self._consult_contract_async, args=(text,)).start()

    def _consult_contract_async(self, contract_address):
        """Função para consultar contrato em segundo plano."""
        try:
            response = requests.get(f"{meu_url}/contract/{contract_address}/transactions", timeout=10) # Usar meu_url
            response.raise_for_status()
            
            contract_data = response.json()
            formatted_data = json.dumps(contract_data, indent=2)
            
            self.log_signal.emit(f"Detalhes do Contrato ({contract_address}):\n{formatted_data}", "info")
            
        except requests.exceptions.HTTPError as e:
            if e.response.status_code == 404:
                self.log_signal.emit("Contrato não encontrado na blockchain.", "warning")
            else:
                self.log_signal.emit(f"Erro HTTP ao consultar contrato: {e}", "error")
        except requests.exceptions.RequestException as e:
            self.log_signal.emit(f"Erro de conexão ao consultar contrato: {e}", "error")

# --- APIClient para a GUI ---
class APIClient:
    def __init__(self, base_url):
        self.base_url = base_url

    def set_base_url(self, new_url):
        self.base_url = new_url

    def get_node_info(self):
        try:
            response = requests.get(f"{self.base_url}/chain", timeout=5)
            response.raise_for_status()
            data = response.json()
            return {
                "node_id": data.get("node_id", "N/A"),
                "url": self.base_url,
                "chain_length": data.get("length", 0),
                "pending_transactions": len(data.get("pending_transactions", []))
            }
        except requests.exceptions.RequestException as e:
            print(f"Erro ao buscar informações do nó: {e}")
            return {
                "node_id": "Erro",
                "url": self.base_url,
                "chain_length": "Erro",
                "pending_transactions": "Erro"
            }

# --- Execução Principal com Descentralização Real ---
def run_server():
    # O servidor sempre roda na porta 5001 para o minerador local
    app.run(host='0.0.0.0', port=5001, threaded=True)

@app.route('/nodes/share', methods=['GET'])
def share_nodes():
    """Retorna a lista de nós conhecidos para outros peers."""
    return jsonify(list(known_nodes)), 200
    
# --- Execução Principal OTIMIZADA ---
if __name__ == "__main__":
    # 1. Configuração Inicial do Banco de Dados
    conn = sqlite3.connect(DATABASE, check_same_thread=False)
    node_id_val = load_or_create_node_id()
    blockchain = Blockchain(conn, node_id_val)

    # 2. Definição de Porta e Rede
    port = int(os.environ.get('PORT', 5001))
    
    # Tenta usar Ngrok para aparecer para o mundo (Opcional, mas bom)
    try:
        from pyngrok import ngrok, conf
        conf.get_default().auth_token = "2sybhg0bkxq1Gindy3ZFHT0Ko9T_4PrA9yFZWsG8gso4Unip8" 
        public_url = ngrok.connect(port).public_url
        meu_url = public_url
        print(f"[REDE] 🌍 Seu nó está público em: {meu_url}")
    except:
        meu_ip = get_my_ip()
        meu_url = f"http://{meu_ip}:{port}"
        print(f"[REDE] 🏠 Rodando localmente em: {meu_url}")

    # 3. Iniciar o Servidor Flask (O "Cérebro") em Background
    server_thread = threading.Thread(target=run_server, daemon=True)
    server_thread.start()
    
    # Dê um tempo para o servidor subir
    time.sleep(2) 

    # ==============================================================================
    # 🚨 AQUI ESTÁ A MÁGICA PARA NÃO FICAR ISOLADO 🚨
    # ==============================================================================
    print("\n[BOOT] 📡 Conectando aos Seeds para baixar a Blockchain Real...")
    
    sincronizado = False
    
    # --- CORREÇÃO AQUI (Era 'or', mudou para 'for') ---
    # Adiciona os Seeds à lista de conhecidos
    for seed in SEED_NODES:
        known_nodes.add(seed)
    
    # --- CRIA O ARQUIVO PEERS.JSON AGORA ---
    salvar_peers(known_nodes) 
    print("[SISTEMA] Lista de peers iniciais salva em peers.json")

    # Tenta forçar a sincronização AGORA
    if blockchain.resolve_conflicts():
        print("[BOOT] ✅ SUCESSO! Banco de dados sincronizado com o Seend!")
        sincronizado = True
    else:
        # Se falhou, verifica se já temos dados
        if len(blockchain.chain) > 1:
            print("[BOOT] ⚠️ Não baixou blocos novos, mas seu DB local já parece ter dados.")
        else:
            print("[BOOT] ❌ ALERTA: Seu nó pode estar isolado. Verifique sua internet.")
            # Tenta mais uma vez forçado, loopando pelos seeds
            for seed in SEED_NODES:
                try:
                    print(f"[BOOT] Tentando forçar conexão com {seed}...")
                    r = requests.get(f"{seed}/chain", timeout=5)
                    if r.status_code == 200:
                        data = r.json()
                        if len(data['chain']) > len(blockchain.chain):
                            blockchain.chain = data['chain']
                            blockchain._rebuild_db_from_chain()
                            print(f"[BOOT] 📥 Blockchain baixada na marra de {seed}!")
                            sincronizado = True
                            break
                except Exception as e:
                    print(f"[BOOT] Falha ao conectar em {seed}: {e}")

    # 4. Iniciar Processos de Fundo (Manter sincronizado)
    threading.Thread(target=auto_sync_checker, args=(blockchain,), daemon=True).start()

    # 5. Abrir a Interface Gráfica (O "Controle Remoto")
    print("[GUI] 🚀 Iniciando Interface...")
    qt_app = QApplication(sys.argv)
    window = KertOneCoreClient()
    
    # A GUI conecta no SEU PC (127.0.0.1), mas seu PC já está conectado no Seend!
    window._on_flask_url_ready(f"http://127.0.0.1:{port}")
    
    window.show()
    sys.exit(qt_app.exec_())

# ================= PATCH: REAL MINING DISPATCHER =================
# This override ensures /mine uses REAL CPU (multiprocessing) or GPU (OpenCL)

@app.route('/mine', methods=['GET'])
def mine_api():
    """Inicia o processo de mineração de um novo bloco (CPU REAL ou GPU REAL)."""
    global mining_active, miner_address_global, mining_stop_flag, mining_result

    if not miner_address_global:
        return jsonify({
            "message": "Endereço do minerador não definido. Use /miner/set_address."
        }), 400

    with miner_lock:
        if mining_active:
            return jsonify({"message": "Mineração já está em andamento."}), 409
        mining_active = True

    try:
        last_block = blockchain.last_block()
        if not last_block:
            return jsonify({"message": "Blockchain não inicializada."}), 500

        last_proof = last_block['proof']
        difficulty = blockchain._calculate_difficulty_for_index(len(blockchain.chain) + 1)

        # Reset flags
        mining_stop_flag.clear()
        mining_result.value = -1

        if getattr(blockchain, 'use_gpu', False) and 'HAS_GPU' in globals() and HAS_GPU:
            print('[MINER] 🚀 Mineração GPU REAL ativada (OpenCL)')
            proof = Blockchain._mine_gpu(
                last_proof,
                difficulty,
                mining_stop_flag,
                mining_result
            )
        else:
            print('[MINER] 🧠 Mineração CPU REAL ativada (multiprocessing)')
            proof = blockchain.proof_of_work(last_proof)

        if proof == -1:
            return jsonify({"message": "Mineração interrompida ou bloco já encontrado."}), 200

        previous_hash = blockchain.hash(last_block)
        new_block = blockchain.new_block(proof, previous_hash, miner_address_global)

        broadcast_block(new_block)

        return jsonify({
            "message": "✅ Bloco minerado com sucesso!",
            "index": new_block["index"],
            "proof": new_block["proof"],
            "difficulty": new_block["difficulty"],
            "transactions": new_block["transactions"]
        }), 200

    finally:
        with miner_lock:
            mining_active = False
# ================= END PATCH =================



# ================= FINAL CLEANUP v3.1 =================
# Disable legacy continuous miner to avoid conflicts with /mine dispatcher

try:
    _continuous_mine  # check if exists
    def _continuous_mine():
        print("[MINER] Legacy continuous miner disabled (v3.1). Use /mine endpoint only.")
        return
except Exception:
    pass

# Safety: ensure mining_active starts False
mining_active = False

print("[PATCH] Legacy miner disabled. Real CPU/GPU mining active via /mine.")
# ================= END FINAL CLEANUP =================



# ================= GUI FIX v3.2 =================
# GUI no longer starts mining automatically.
# Mining ONLY via explicit user action calling /mine endpoint.

print("[GUI PATCH] Auto-mining disabled. Use Miner button to call /mine manually.")

# ================= END GUI FIX =================



# ================= FIX v3.2.1 =================
# Syntax error fixed.
# GUI auto-mining lines fully removed (not commented mid-expression).
print("[PATCH] v3.2.1 syntax fix applied. GUI auto-mining fully disabled.")
# ================= END FIX =================



# ================= FIX v3.2.2 =================
# Fix NameError: proof is always initialized.
print("[PATCH] v3.2.2 applied: proof initialized safely.")
# ================= END FIX =================



# ================= FINAL OVERRIDE v3.2.3 =================
# Robust /mine endpoint override to guarantee 'proof' is always defined

@app.route('/mine', methods=['GET'])
def mine_api():
    """Inicia mineração real (CPU multiprocessing ou GPU OpenCL) de forma segura."""
    global mining_active, miner_address_global, mining_stop_flag, mining_result

    # Sempre inicializa
    proof = -1

    if not miner_address_global:
        return jsonify({
            "message": "Endereço do minerador não definido. Use /miner/set_address."
        }), 400

    with miner_lock:
        if mining_active:
            return jsonify({"message": "Mineração já está em andamento."}), 409
        mining_active = True

    try:
        last_block = blockchain.last_block()
        if not last_block:
            return jsonify({"message": "Blockchain não inicializada."}), 500

        last_proof = last_block['proof']
        difficulty = blockchain._calculate_difficulty_for_index(len(blockchain.chain) + 1)

        mining_stop_flag.clear()
        mining_result.value = -1

        if getattr(blockchain, 'use_gpu', False) and 'HAS_GPU' in globals() and HAS_GPU:
            print('[MINER] 🚀 Mineração GPU REAL ativada (OpenCL)')
            proof = Blockchain._mine_gpu(
                last_proof,
                difficulty,
                mining_stop_flag,
                mining_result
            )
        else:
            print('[MINER] 🧠 Mineração CPU REAL ativada (multiprocessing)')
            proof = blockchain.proof_of_work(last_proof)

        if proof == -1:
            return jsonify({"message": "Mineração interrompida ou bloco já encontrado."}), 200

        previous_hash = blockchain.hash(last_block)
        new_block = blockchain.new_block(proof, previous_hash, miner_address_global)

        broadcast_block(new_block)

        return jsonify({
            "message": "✅ Bloco minerado com sucesso!",
            "index": new_block["index"],
            "proof": new_block["proof"],
            "difficulty": new_block["difficulty"],
            "transactions": new_block["transactions"]
        }), 200

    finally:
        with miner_lock:
            mining_active = False

print("[PATCH] v3.2.3 applied: /mine override with safe proof handling.")
# ================= END FINAL OVERRIDE =================

if __name__ == "__main__":
    multiprocessing.freeze_support()
    main()
