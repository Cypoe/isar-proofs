import numpy as np, pandas as pd, os, json
os.makedirs('output', exist_ok=True)

def bmat(x):
    return np.array(x, dtype=np.uint8)

def bmul(A,B):
    return ((A @ B) > 0).astype(np.uint8)

def key(A):
    return ''.join(map(str, A.flatten().tolist()))

def pretty(A):
    return '[' + '; '.join(''.join(map(str,row.tolist())) for row in A) + ']'

G = {
    'I': bmat([[1,0,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,0]]),
    'R': bmat([[1,0,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,1]]),
    'A': bmat([[0,0,0,0],[1,0,0,0],[0,1,0,0],[0,0,0,0]]),
    'S': bmat([[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]),
}

closure = {}
name_of = {}
queue = []
for n,M in G.items():
    k = key(M)
    closure[k] = M
    name_of[k] = n
    queue.append(M)

added = True
while added:
    added = False
    mats = list(closure.values())
    for A1 in mats:
        for B1 in mats:
            C = bmul(A1,B1)
            k = key(C)
            if k not in closure:
                closure[k] = C
                queue.append(C)
                added = True

# stable naming: generators first, then others sorted by bitstring
others = sorted([k for k in closure if k not in [key(G[n]) for n in ['I','R','A','S']]])
for idx,k in enumerate(others, start=1):
    name_of[k] = f'B{idx}'

items = sorted(closure.items(), key=lambda kv: (0 if name_of[kv[0]] in ['I','R','A','S'] else 1, name_of[kv[0]]))
order = [name_of[k] for k,_ in items]
mat_of_name = {name_of[k]:M for k,M in items}

# elements csv
rows = []
for n in order:
    M = mat_of_name[n]
    rows.append({'name': n, 'matrix': pretty(M), 'ones': int(M.sum())})
pd.DataFrame(rows).to_csv('output/boolean_closure_elements.csv', index=False)

# cayley table csv
cayley = pd.DataFrame(index=order, columns=order)
for a in order:
    for b in order:
        c = bmul(mat_of_name[a], mat_of_name[b])
        cayley.loc[a,b] = name_of[key(c)]
cayley.to_csv('output/boolean_cayley_table.csv')

# property table
props = []
Z = np.zeros((4,4), dtype=np.uint8)
for n in order:
    M = mat_of_name[n]
    props.append({
        'name': n,
        'idempotent': np.array_equal(bmul(M,M), M),
        'nilpotent_index_le_4': any(np.array_equal(np.linalg.matrix_power(M.astype(int),p)>0, Z) for p in range(1,5)),
        'square': name_of[key(bmul(M,M))],
    })
pd.DataFrame(props).to_csv('output/boolean_properties.csv', index=False)

# stdout summary
print(json.dumps({
    'closure_size': len(order),
    'order': order,
    'elements': {n: pretty(mat_of_name[n]) for n in order},
    'selected_products': {
        'S2': name_of[key(bmul(mat_of_name['S'], mat_of_name['S']))],
        'A2': name_of[key(bmul(mat_of_name['A'], mat_of_name['A']))],
        'A3': name_of[key(bmul(bmul(mat_of_name['A'], mat_of_name['A']), mat_of_name['A']))],
        'IR': name_of[key(bmul(mat_of_name['I'], mat_of_name['R']))],
        'RI': name_of[key(bmul(mat_of_name['R'], mat_of_name['I']))],
        'SI': name_of[key(bmul(mat_of_name['S'], mat_of_name['I']))],
        'SR': name_of[key(bmul(mat_of_name['S'], mat_of_name['R']))],
        'AS': name_of[key(bmul(mat_of_name['A'], mat_of_name['S']))],
        'SA': name_of[key(bmul(mat_of_name['S'], mat_of_name['A']))],
    }
}, indent=2))
