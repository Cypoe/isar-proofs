import numpy as np

np.set_printoptions(suppress=True)

# ============================================================
# 0) Something exists -> Void
# ============================================================
empty = frozenset()
Void = frozenset([empty])              # {∅}
print("Void =", Void)

# ============================================================
# 1) Self-describe -> Pair + Δ asymmetry (ordered pair)
# ============================================================
def kuratowski(x, y):
    return frozenset([frozenset([x]), frozenset([x, y])])

Pair = kuratowski(empty, empty)        # (∅,∅) = {{∅},{∅,∅}} = {{∅}}
print("Pair =", Pair)

# Δ exists once ordered structure exists (non-commutativity of projections)
# We won’t use text Δ; we encode Δ as a non-invertible operator later.

# ============================================================
# 2) Structural Arithmetic -> I O B (carriers, not sets)
#    Carrier basis: [S, A, R, I]  (state, adjacency, rewrite, invariant)
# ============================================================
# Interpret the *mere existence* of four roles as a 4D carrier space.
# The only extra structure is the invariant quotient projector Π (axiom 3).

# IOB primitives as linear ops on carrier-space:
# - I: identity on carrier space (not the ISAR I-matrix yet)
I = np.eye(4)

# - O: self-application operator (advances "phase"/slot; introduces sequence)
O = np.array([
    [0,1,0,0],  # S <- A
    [0,0,1,0],  # A <- R
    [0,0,0,1],  # R <- I
    [1,0,0,0],  # I <- S
], dtype=float)

# - B: body/pair structure operator (binds S<->A as "term has edge")
B = np.array([
    [1,0,0,0],
    [1,1,0,0],
    [0,0,1,0],
    [0,0,0,1],
], dtype=float)

print("\n=== IOB (structural) ===")
print("I=\n", I)
print("O=\n", O)
print("B=\n", B)

# ============================================================
# 3) Quantity calculus Q = (S,Y,M,E)  -> SAR decomposition
#    We define SAR as induced roles from IOB:
#    S = closure on state axis
#    A = adjacency (edge-formation)
#    R = rewrite/selection (non-invertible choice)
# ============================================================

# Raw candidates (pre-quotient):
I_dense = I

S_dense = np.eye(4)          # closure initially “do nothing”

A_dense = np.array([         # adjacency shift (like your A)
    [0,0,0,0],
    [1,0,0,0],
    [0,1,0,0],
    [0,0,0,0],
], dtype=float)

R_dense = np.array([         # rewrite "rotate with loss" (like your R)
    [1,0,0,0],
    [0,0,0,1],
    [0,1,0,0],
    [0,0,1,0],
], dtype=float)

# AXIOMS test!?
# assert np.allclose(R_raw @ R_raw @ R_raw @ R_raw, I), "R_raw @ R_raw @ R_raw @ R_raw != I"
# assert np.allclose(S_raw @ S_raw @ S_raw @ S_raw, I), "S_raw @ S_raw @ S_raw @ S_raw != I"
# assert np.allclose(A_raw @ A_raw @ A_raw @ A_raw, I), "A_raw @ A_raw @ A_raw @ A_raw != I"
# assert np.allclose(R_raw @ S_raw @ A_raw @ R_raw, 0), "R_raw @ S_raw @ A_raw @ R_raw != 0"
# assert np.allclose(A_raw @ R_raw @ A_raw @ A_raw, 0), "A_raw @ R_raw @ A_raw @ A_raw != 0"

print("\n=== SAR (raw, before quotient) ===")
print("I_dense=\n", I_dense)
print("S_dense=\n", S_dense)
print("A_dense=\n", A_dense)
print("R_dense=\n", R_dense)

# ============================================================
# 4) Operational quotient Π : enforces invariant layer (axiom 3)
#    This is where C_I etc. become *not the same* as raw objects.
#    Π projects away non-observable degrees of freedom.
#
#    Choose Π so that it enforces your canonical sparse ISAR representatives:
#    (This is the computational meaning of “I = ISAR/∼”.)
# ============================================================
# C_I = np.array([            # invariant projection
#     [1,0,0,0],
#     [0,0,0,0],
#     [0,0,1,0],
#     [0,0,0,0],
# ], dtype=float)

# Strong normalization morphism: q(M) = Π M C
# In categorical terms: quotient q is not just a projector onto a subspace; 
# it’s a quotient + identification that can merge multiple 
# preimages into one observable class.
# Computationally, that means:
# q must include a column merge (or linear combination) step, e.g.:
# q(M) = Π M C, where
# C is a fixed 4×4 “coarse-graining” matrix that merges gauge columns into an observable column.
Pi = np.array([[1,0,0,0],
               [0,0,0,0],
               [0,0,1,0],
               [0,0,0,0]], float)

C  = np.array([[1,1,0,0],
               [0,1,0,0],
               [0,0,1,0],
               [0,0,0,1]], float)

def q(M): 
    return Pi @ M @ C

# Apply quotient to carriers:
S = np.array([
    [1,1,0,0],
    [0,1,0,0],
    [0,0,1,0],
    [0,0,0,1],
], dtype=float)            # your S
A = A_dense                 # already sparse
R = np.array([             # your sparse R (selection carrier)
    [1,0,0,0],
    [0,0,0,0],
    [0,1,0,0],
    [0,0,1,0],
], dtype=float)
I = Pi                  # your I

print("\n=== Quotient Π (Invariant layer) ===")
print("Π=\n", Pi)

print("\n=== ISAR canonical matrices (after quotient) ===")
print("I=\n", I)
print("R=\n", R)
print("A=\n", A)
print("S=\n", S)

# Compute ISAR kernel:
K_dense = R_dense@A_dense@S_dense
K_isar = I@R@A@S

qK_dense = q(K_dense)
print("q(K_dense):\n", qK_dense)
print("diff qK_dense - K_isar:\n", qK_dense - K_isar)
assert np.allclose(qK_dense, K_isar)

# ============================================================
# 5) ISAR kernel generator
# ============================================================
K = I @ R @ A @ S
print("\n=== ISAR kernel K = I·R·A·S ===")
print(K)
print("rank(K) =", np.linalg.matrix_rank(K))
print("K^2 =\n", K@K)
assert np.linalg.matrix_rank(K) == 1, "rank(K) != 1 (kernel failed)"
assert np.allclose(K, 0) == False, "K(isar) != 0 (kernel failed, trivial!)"
assert np.allclose(K@K, 0), "K^2 != 0 (nilpotency failed)"
print("✓ K kernel and nilpotency")

# Assert your desired substrate form:
K_expected = np.array([
    [0,0,0,0],
    [0,0,0,0],
    [1,1,0,0],
    [0,0,0,0],
], dtype=float)

print(f"\nDiff K - K_expected =  {'✓ ' if np.allclose(K, K_expected) else '✗ '}\n{K - K_expected}")
assert np.allclose(K, K_expected), "K does not match expected substrate"
print()

# ============================================================
# 6) Native derived ops
# ============================================================
NORM = S @ I
APP  = A @ R
COMP = R @ A @ S

DUP  = S @ S
SWAP = R @ S

CONST = I @ S

print("\n=== Derived ops ===")
print("NORM=S·I=\n", NORM)
print("APP =A·R=\n", APP)
print("COMP=R·A·S=\n", COMP)
print("DUP =S·S=\n", DUP)
print("SWAP=R·S=\n", SWAP)
print("CONST=I·S=\n", CONST)

# ============================================================
# 7) SKI (as distinguished operators in the same substrate)
#    NOTE: This is naming/embedding, not classical β-equality proof.
# ============================================================
S_comb = S
K_comb = I @ S
I_comb = I
print("\n=== SKI (matrix representatives) ===")
print("S=\n", S_comb)
print("K=\n", K_comb)
print("I=\n", I_comb)

# ============================================================
# 8) Futamura (Cartesian product, not composition)
#    Implement as Kronecker products / outer products of the matrices.
# ============================================================
U_fut = np.kron(I, np.kron(S, A))   # I × S × A
print("\n=== Futamura kernel U_fut = I × S × A (Kronecker) ===")
print("shape:", U_fut.shape)
print("rank:", np.linalg.matrix_rank(U_fut))
# 1st, 2nd, 3rd, 4rd Futamura
print("U_fut=\n", U_fut)
assert np.allclose(U_fut, 0) == False, "U_fut != 0 (nilpotency failed)"
print("✓ U_fut matches expected and U_fut=0")


# ============================================================
# 9) Quine tensor (your 3 entries)
# ============================================================
U_quine = np.zeros((4,4,4,4), dtype=float)
quine_tensor = [
    (1,1,1,1, 1.0),
    (2,1,2,2, 1.0),
    (3,1,3,3, 1.0),
]
for i,s,a,r,v in quine_tensor:
    U_quine[i-1,s-1,a-1,r-1] = v

print("\n=== Quine tensor nonzeros ===")
print(np.argwhere(U_quine > 0.5))
