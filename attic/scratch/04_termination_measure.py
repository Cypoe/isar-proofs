import pandas as pd, os, json
os.makedirs('output', exist_ok=True)

rules = [
    ("AR","AI"), ("RA","IA"), ("AIA","AAA"), ("IAI","AAA"), ("RSA","ISA"),
    ("II","I"), ("IR","I"), ("RI","I"), ("RR","R"), ("SI","I"), ("SR","R"), ("SS","S"),
    ("AAI","AA"), ("IAA","AA"), ("IAS","IA"), ("SAA","AA"), ("AAAA","AAA"), ("AAAS","AAA"),
    ("ASAI","ASA"), ("AASA","AA"), ("AISA","AI"), ("ASASA","ASA"),
]

order = {'S':0,'A':1,'I':2,'R':3}

def key(w):
    return (len(w), tuple(order[c] for c in w))

rows=[]
for lhs, rhs in rules:
    rows.append({
        'lhs': lhs,
        'rhs': rhs,
        'lhs_len': len(lhs),
        'rhs_len': len(rhs),
        'lhs_key': key(lhs),
        'rhs_key': key(rhs),
        'strictly_decreases_shortlex_SAIR': key(rhs) < key(lhs)
    })

df = pd.DataFrame(rows)
df.to_csv('output/termination_measure_shortlex.csv', index=False)

print(json.dumps({
    'all_rules_decrease_shortlex_SAIR': bool(df['strictly_decreases_shortlex_SAIR'].all()),
    'nondecreasing_rules': df[df['strictly_decreases_shortlex_SAIR']==False][['lhs','rhs']].to_dict(orient='records')
}, indent=2))
