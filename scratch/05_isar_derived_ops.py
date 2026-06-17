import numpy as np, pandas as pd, os, json
os.makedirs('output', exist_ok=True)
I = np.array([[1,0,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,0]], dtype=float)
R = np.array([[1,0,0,0],[0,0,0,0],[0,1,0,0],[0,0,1,0]], dtype=float)
A = np.array([[0,0,0,0],[1,0,0,0],[0,1,0,0],[0,0,0,0]], dtype=float)
S = np.array([[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]], dtype=float)
ops = {
    'U_K=IRAS': I@R@A@S,
    'NORM=SI': S@I,
    'APP=AR': A@R,
    'COMP=RAS': R@A@S,
    'DUP=SS': S@S,
    'SWAP=RS': R@S,
    'CONST=IS': I@S,
}
rows=[]
for name,M in ops.items():
    rows.append({'name':name,'matrix':M.tolist(),'rank':int(np.linalg.matrix_rank(M)),'trace':float(np.trace(M))})
pd.DataFrame(rows).to_csv('output/isar_derived_ops.csv', index=False)
print(json.dumps({k:v.tolist() for k,v in ops.items()}, indent=2))
