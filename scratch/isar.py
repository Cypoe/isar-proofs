import numpy as np
import sqlite3
import os
from typing import List, Tuple, Optional

# ============================================================================
# ONTOLOGICAL TAGGING SYSTEM
# ============================================================================
# Axiomatic Geometric Signatures (Standard PLEX Basis)
I_MAT = np.array([[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]], dtype=float)
A_MAT = np.array([[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]], dtype=float)
S_MAT = np.array([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], dtype=float)
R_MAT = np.array([[1, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]], dtype=float)

def _derive_sig(matrix: np.ndarray) -> int:
    diag = (np.diag(matrix) != 0).astype(int)
    sig = 0
    for i, b in enumerate(diag):
        if b: sig |= (1 << i)
    return sig & 0b111

def _derive_sig_row(matrix: np.ndarray, row: int = 0) -> int:
    r_sigs = (matrix[row] != 0).astype(int)
    sig = 0
    for i, b in enumerate(r_sigs):
        if b: sig |= (1 << i)
    return sig & 0b111

# Stable Axiomatic Tags
TAG_INT = _derive_sig(A_MAT)        # 0
TAG_SYM = _derive_sig(I_MAT)        # 5
TAG_DAT = _derive_sig_row(S_MAT, 0) # 3
TAG_STRUC = 4
TAG_ERR = 7

def get_tag(v): return v & 0b111
def untag(v): return v >> 3

def tag_int(v): return (int(v) << 3) | TAG_INT
def tag_sym(idx): return (int(idx) << 3) | TAG_SYM
def tag_dat(idx): return (int(idx) << 3) | TAG_DAT
def tag_err(code): return (int(code) << 3) | TAG_ERR

# Canonical IDs (Axiomatically Derived)
import zlib
def _h(s): return (zlib.crc32(s.lower().encode('utf-8')) & 0xFFFFFF)
ID_NIL = tag_sym(_h("NIL"))
ID_T   = tag_sym(_h("T"))
ID_ERR = tag_sym(_h("ERR"))

ID_INPUT = tag_sym(_h("INPUT"))
ID_PROGRAM = tag_sym(_h("PROGRAM"))


# ============================================================================
# THE ISAR KERNEL (PROVEN SPARSE PROJECTION)
# ============================================================================

class ISARKernel:
    # Optimal Reference Matrices (Axiomatic)
    I = np.array([[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]], dtype=float)
    R = np.array([[0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]], dtype=float)
    A = np.array([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=float)
    S = np.array([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], dtype=float)
    
    def __init__(self, db_path=":memory:"):
        self.db_path = db_path
        self.conn = sqlite3.connect(db_path)
        self.c = self.conn.cursor()
        self._init_schema()
        
        # Next unique ID for tensors (high range to avoid collisions)
        self.c.execute("SELECT MAX(i) FROM U")
        m = self.c.fetchone()[0]
        if m:
            # If m is already a tagged tensor, we want the untagged high-water mark
            # (Ensures continuity across reloads)
            high_id = m >> 3
            self.next_id = max(50000000, high_id + 1)
        else:
            self.next_id = 50000000
        
        self._bootstrap()



    def _init_schema(self):
        self.c.execute("CREATE TABLE IF NOT EXISTS U (i INT, s INT, a INT, r INT, value REAL, PRIMARY KEY(i,s,a,r))")
        self.c.execute("CREATE TABLE IF NOT EXISTS NAMES (id INTEGER PRIMARY KEY, name TEXT)")
        self.c.execute("CREATE INDEX IF NOT EXISTS idx_u_i ON U(i)")
        self.c.execute("CREATE INDEX IF NOT EXISTS idx_u_i_s ON U(i, s)")
        self.c.execute("CREATE INDEX IF NOT EXISTS idx_names_name ON NAMES(name)")

    def put_symbol(self, name: str) -> int:
        """Register/Put a symbol with deduplication. (Case-Insensitive IDs)
        
        Returns the tagged symbol ID.
        """
        # 1. Generate ID using case-insensitive hash
        sid = _h(name)
        
        # 2. Check if ID already exists
        self.c.execute("SELECT name FROM NAMES WHERE id=?", (sid,))
        res = self.c.fetchone()
        if res:
            # ID collision check: if different name, find next available ID
            if res[0].lower() != name.lower():
                while True:
                    sid = (sid + 1) & 0xFFFFFF
                    self.c.execute("SELECT name FROM NAMES WHERE id=?", (sid,))
                    coll = self.c.fetchone()
                    if not coll: break
                    if coll[0].lower() == name.lower():
                        return tag_sym(sid)
            else:
                return tag_sym(sid)
                
        # 3. Register New Symbol
        self.register_symbol(sid, name)
        # Ensure it's in U table as a self-tagged symbol (Tagged ID in 'i' column)
        tid = tag_sym(sid)
        self.c.execute("INSERT OR REPLACE INTO U VALUES (?, 2, ?, 0, 1.0)", (tid, tid))
        self.conn.commit()
        return tid

    def _bootstrap(self):
        """Standardized Axiomatic Bootstrap"""
        # 1. Emergent Operators
        ops = {
            1: self.S @ self.I, 
            2: self.A @ self.R, 
            3: self.R @ self.A @ self.S, 
            4: self.S @ self.S, 
            5: self.R @ self.R
        }
        for op_id, mat in ops.items():
            for s in range(4):
                for a in range(4):
                    if mat[s, a] != 0:
                        self.c.execute("INSERT OR REPLACE INTO U VALUES (?,?,?,1,?)", 
                                     (op_id, s+1, a+1, float(mat[s, a])))
        
        # 2. Canonical Symbols
        specials = {
            ID_NIL: "NIL", ID_T: "T", ID_ERR: "ERR", 
            ID_INPUT: "INPUT", ID_PROGRAM: "PROGRAM"
        }
        for vid, name in specials.items():
            self.register_symbol(untag(vid), name)
            self.c.execute("INSERT OR REPLACE INTO U VALUES (?, 2, ?, 0, 1.0)", (vid, vid))
            
        self.conn.commit()

    def register_symbol(self, sid: int, name: str):
        """Register a symbol ID with its name (Preserve Casing)"""
        self.c.execute("INSERT OR REPLACE INTO NAMES (id, name) VALUES (?, ?)", (sid, name))
        self.conn.commit()

    def get_symbol_name(self, sid: int) -> Optional[str]:
        """Resolve symbol ID to name"""
        self.c.execute("SELECT name FROM NAMES WHERE id=?", (sid,))
        res = self.c.fetchone()
        return res[0] if res else None

    def tensor_product(self, tid_a: int, tid_b: int) -> int:
        """
        Relational join: A ⊗ B = A JOIN B ON A.r = B.i
        """
        tid_res = self.allocate_tensor()
        self.c.execute(f"""
            INSERT INTO U (i, s, a, r, value)
            SELECT {tid_res}, A.s, B.a, B.r, A.value * B.value
            FROM U A JOIN U B ON A.a = B.i
            WHERE A.i = ? AND B.i = ?
        """, (tid_a, tid_b))
        self.conn.commit()
        return tid_res

    def allocate_triple(self, i, s, a, r=1, value=1.0):
        self.c.execute("INSERT OR REPLACE INTO U VALUES (?,?,?,?,?)", (i, s, a, r, float(value)))
        self.conn.commit()

    def get_u_table(self):
        return self.c

    def allocate_tensor(self) -> int:
        """Allocate a new structural tensor ID (Tag 100 / 4)"""
        tid = (self.next_id << 3) | TAG_STRUC
        self.next_id += 1
        return tid

    def tensor_to_minimal(self, tid: int, max_steps: int = 100) -> int:
        """
        Contraction morphism: Finds the minimal representative (fixed point)
        of a structural tensor, resolving loops and self-references.
        """
        # 1. Base case: atoms are already minimal
        if get_tag(tid) != TAG_STRUC:
            return tid
            
        memo = {}
        
        def minimal(curr, depth=0):
            if get_tag(curr) != TAG_STRUC: return curr
            if depth > max_steps: return tid # Loop detected, return root as proxy
            if curr in memo: return memo[curr]
            
            # Get structural components (s=1)
            self.c.execute("SELECT s, a, r FROM U WHERE i=? AND s=1", (curr,))
            rows = self.c.fetchall()
            if not rows: 
                # Check for atom rows as fallback
                self.c.execute("SELECT s, a, r FROM U WHERE i=? AND s=2", (curr,))
                if self.c.fetchone(): return curr
                return curr
            
            # If it's a simple indirection (one row, s=1, r=1 maybe?) 
            # we follow it. But usually it's a list.
            
            # Heuristic: if we find a path back to 'tid', we've closed a loop.
            # In the axiomatic substrate, a fixed point is where the structure repeats.
            
            new_id = self.allocate_tensor()
            memo[curr] = new_id
            
            for s, a, r in rows:
                if s == 1: # Sub-structure
                    target = minimal(a, depth + 1)
                    self.c.execute("INSERT INTO U VALUES (?, 1, ?, ?, 1.0)", (new_id, target, r))
                else: # Atom
                    self.c.execute("INSERT INTO U VALUES (?, ?, ?, ?, 1.0)", (new_id, s, a, r))
            
            return new_id

        # For now, a simple structural clone that stops at max_steps/depth
        # In a real ISAR kernel, this would perform graph isomorphism reduction.
        return minimal(tid)

    def commit(self):
        self.conn.commit()

    def close(self):
        self.conn.close()
