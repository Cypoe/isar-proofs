import os, pandas as pd, json
os.makedirs('output', exist_ok=True)

rules = [
    ("AR","AI"),
    ("RA","IA"),
    ("AIA","AAA"),
    ("IAI","AAA"),
    ("RSA","ISA"),
    ("II","I"),
    ("IR","I"),
    ("RI","I"),
    ("RR","R"),
    ("SI","I"),
    ("SR","R"),
    ("SS","S"),
    ("AAI","AA"),
    ("IAA","AA"),
    ("IAS","IA"),
    ("SAA","AA"),
    ("AAAA","AAA"),
    ("AAAS","AAA"),
    ("ASAI","ASA"),
    ("AASA","AA"),
    ("AISA","AI"),
    ("ASASA","ASA"),
]

# one-step reductions anywhere
from collections import deque

def one_step_reducts(w):
    outs = []
    for lhs, rhs in rules:
        start = 0
        while True:
            i = w.find(lhs, start)
            if i == -1:
                break
            outs.append((lhs, rhs, i, w[:i] + rhs + w[i+len(lhs):]))
            start = i + 1
    return outs

def normal_forms(w):
    seen = {w}
    q = deque([w])
    irreducible = set()
    while q:
        x = q.popleft()
        reds = one_step_reducts(x)
        if not reds:
            irreducible.add(x)
            continue
        for _,_,_,y in reds:
            if y not in seen:
                seen.add(y)
                q.append(y)
    return irreducible

def nf_unique(w):
    nfs = normal_forms(w)
    return len(nfs) == 1, sorted(nfs)

# Critical overlaps and peak joinability
cp_rows = []
for i,(l1,r1) in enumerate(rules):
    for j,(l2,r2) in enumerate(rules):
        # suffix of l1 overlaps prefix of l2
        for k in range(1, min(len(l1), len(l2))):
            if l1[-k:] == l2[:k]:
                s = l1 + l2[k:]
                left = r1 + l2[k:]
                right = l1[:-k] + r2
                join_left = normal_forms(left)
                join_right = normal_forms(right)
                join = sorted(join_left & join_right)
                cp_rows.append({
                    'rule1': f'{l1}->{r1}', 'rule2': f'{l2}->{r2}', 'type':'suffix/prefix', 'overlap_len':k,
                    'source': s, 'left_peak': left, 'right_peak': right,
                    'left_nfs': ' | '.join(sorted(join_left)), 'right_nfs': ' | '.join(sorted(join_right)),
                    'joinable': len(join) > 0, 'common_nf': ' | '.join(join)
                })
        # containment of l2 inside l1
        start = 0
        while True:
            p = l1.find(l2, start)
            if p == -1:
                break
            if not (p == 0 and len(l2) == len(l1)):  # skip exact same handled via ordinary peak already
                s = l1
                left = r1
                right = l1[:p] + r2 + l1[p+len(l2):]
                join_left = normal_forms(left)
                join_right = normal_forms(right)
                join = sorted(join_left & join_right)
                cp_rows.append({
                    'rule1': f'{l1}->{r1}', 'rule2': f'{l2}->{r2}', 'type':'containment', 'overlap_len':len(l2),
                    'source': s, 'left_peak': left, 'right_peak': right,
                    'left_nfs': ' | '.join(sorted(join_left)), 'right_nfs': ' | '.join(sorted(join_right)),
                    'joinable': len(join) > 0, 'common_nf': ' | '.join(join)
                })
            start = p + 1

cp = pd.DataFrame(cp_rows).drop_duplicates()
cp.to_csv('output/critical_pairs.csv', index=False)

# Summary by source peak
unjoin = cp[cp['joinable'] == False].copy()
unjoin.to_csv('output/unjoinable_critical_pairs.csv', index=False)

# Exhaustive test all words up to length 8 for unique normal form
alphabet = 'AIRS'
rows=[]
for maxL in range(1,9):
    # incremental enumeration
    from itertools import product
    for L in [maxL]:
        for tup in product(alphabet, repeat=L):
            w = ''.join(tup)
            ok, nfs = nf_unique(w)
            rows.append({'word':w,'length':L,'unique_nf':ok,'normal_forms':' | '.join(nfs)})
exh = pd.DataFrame(rows)
exh.to_csv('output/exhaustive_unique_nf_len8.csv', index=False)

bad = exh[exh['unique_nf']==False].copy()
bad.to_csv('output/nonunique_nf_len8.csv', index=False)

# termination check by rule lengths
length_rows = [{'rule':f'{l}->{r}','lhs_len':len(l),'rhs_len':len(r),'strictly_decreasing':len(r)<len(l)} for l,r in rules]
pd.DataFrame(length_rows).to_csv('output/rule_lengths.csv', index=False)

print(json.dumps({
    'rule_count': len(rules),
    'all_rules_strictly_decrease_length': all(len(r)<len(l) for l,r in rules),
    'critical_pair_count': int(len(cp)),
    'unjoinable_critical_pair_count': int(len(unjoin)),
    'all_words_len_le_8_have_unique_nf': bool(len(bad)==0),
    'num_counterexamples_len_le_8': int(len(bad)),
    'sample_unjoinable': unjoin.head(10).to_dict(orient='records')
}, indent=2))
