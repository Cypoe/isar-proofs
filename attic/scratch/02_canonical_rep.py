import numpy as np, pandas as pd, os, json
os.makedirs('output', exist_ok=True)

def bmat(x):
    return np.array(x, dtype=np.uint8)

def bmul(A,B):
    return ((A @ B) > 0).astype(np.uint8)

def key(A):
    return ''.join(map(str, A.flatten().tolist()))

G = {
    'I': bmat([[1,0,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,0]]),
    'R': bmat([[1,0,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,1]]),
    'A': bmat([[0,0,0,0],[1,0,0,0],[0,1,0,0],[0,0,0,0]]),
    'S': bmat([[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]),
}
# closure
closure = {}
for n,M in G.items():
    closure[key(M)] = M
changed = True
while changed:
    changed = False
    mats = list(closure.values())
    for A in mats:
        for B in mats:
            C = bmul(A,B)
            k = key(C)
            if k not in closure:
                closure[k] = C
                changed = True
# shortest canonical words by BFS
from collections import deque
canon = {}  # key -> word
q = deque(sorted(G.keys()))
for g in sorted(G.keys()):
    canon[key(G[g])] = g
seen_words = set(sorted(G.keys()))
max_len = 8
while q:
    w = q.popleft()
    # eval word
    M = G[w[0]]
    for ch in w[1:]:
        M = bmul(M, G[ch])
    kw = key(M)
    # extend if beneficial
    if len(w) >= max_len:
        continue
    for g in sorted(G.keys()):
        nw = w + g
        if nw in seen_words:
            continue
        seen_words.add(nw)
        M2 = bmul(M, G[g])
        k2 = key(M2)
        if k2 not in canon or len(nw) < len(canon[k2]) or (len(nw)==len(canon[k2]) and nw < canon[k2]):
            canon[k2] = nw
        q.append(nw)

# ensure all closure elements got representatives
assert set(canon.keys()) == set(closure.keys()), (len(canon), len(closure))

# stable names by canonical words, generators first
items = sorted(canon.items(), key=lambda kv: (len(kv[1]), kv[1]))
name_of = {}
for k,w in items:
    if w in G:
        name_of[k] = w
for i,(k,w) in enumerate(items, start=1):
    if k not in name_of:
        name_of[k] = f'E{i}'

# transitions from canonical rep times generator
rows=[]
for k,w in sorted(canon.items(), key=lambda kv: (len(kv[1]), kv[1])):
    M = closure[k]
    src = name_of[k]
    for g in sorted(G.keys()):
        destM = bmul(M, G[g])
        kd = key(destM)
        dest = name_of[kd]
        rw = canon[kd]
        rows.append({'source':src,'canon_word':w,'append':g,'product_word':w+g,'reduces_to':rw,'dest':dest})
trans = pd.DataFrame(rows)
trans.to_csv('output/canonical_transitions.csv', index=False)

# length-reducing rules among short words: w -> canon(w) where shorter
rules=[]
# enumerate words up to length 6
from itertools import product
for L in range(2,7):
    for tup in product(sorted(G.keys()), repeat=L):
        w=''.join(tup)
        M = G[w[0]]
        for ch in w[1:]:
            M=bmul(M,G[ch])
        c=canon[key(M)]
        if len(c) < len(w) or (len(c)==len(w) and c < w):
            rules.append((w,c))
# keep only irreducible-by-subrule left-sides to get a compact basis
rules = sorted(set(rules), key=lambda x: (len(x[0])-len(x[1]), len(x[0]), x[0], x[1]))
compact=[]
lefts=[]
for w,c in rules:
    reducible=False
    for l,_ in compact:
        if l in w and l != w:
            reducible=True
            break
    if not reducible:
        compact.append((w,c))
compact_df = pd.DataFrame(compact, columns=['lhs','rhs'])
compact_df.to_csv('output/compact_rewrite_rules.csv', index=False)

# representatives table
rep_rows=[]
for k,w in sorted(canon.items(), key=lambda kv: (len(kv[1]), kv[1])):
    rep_rows.append({'name':name_of[k],'canonical_word':w,'length':len(w)})
pd.DataFrame(rep_rows).to_csv('output/canonical_representatives.csv', index=False)

# summary of compact rules
print(json.dumps({
    'closure_size': len(closure),
    'compact_rule_count': len(compact),
    'compact_rules': compact,
    'representatives': rep_rows[:15]
}, indent=2))
