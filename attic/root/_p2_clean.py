import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

def kill_arg(seg, name):
    # remove ` name,` / `, name` / `name, ` occurrence inside a simp list
    for pat in (' ' + name + ',', ',\n          ' + name + ',', ' ' + name + ')', ', ' + name + ']'):
        if pat in seg:
            if pat.endswith(','):
                seg = seg.replace(pat, pat[:-1].rstrip(), 1) if False else seg.replace(pat, pat.replace(name, '').rstrip(', ') + ',' if False else '', 1)
    return seg

def remove_simp_arg(seg, name):
    # try patterns: "name, " , ", name" , ",\n  name"
    cands = [
        (name + ',\n          ', ''),
        (name + ', ', ''),
        (', ' + name, ''),
        (' ' + name + '\n          ', ''),
    ]
    for a, b in cands:
        if a in seg:
            seg = seg.replace(a, b, 1)
            return seg, True
    return seg, False

def remove_have(seg, name):
    # remove "  have NAME : ... := <one or two lines>"
    import re
    pat = re.compile(r'\n  have ' + name + r' :[^\n]*(:=\n    [^\n]*|:= [^\n]*)')
    seg2 = pat.sub('', seg, count=1)
    return seg2

def lemma_seg(txt, start_marker, end_marker):
    i = txt.index(start_marker)
    j = txt.index(end_marker, i)
    return i, j

# --- p2Step_open: drop p2ResvRawT, consRevL ---
i = txt.index('theorem p2Step_open'); j = txt.index('/-- the rec continuation', i)
seg = txt[i:j]
seg, _ = remove_simp_arg(seg, 'p2ResvRawT')
seg, _ = remove_simp_arg(seg, 'consRevL')
txt = txt[:i] + seg + txt[j:]

# --- p2RecCont_apply: drop c11 have+arg ---
i = txt.index('theorem p2RecCont_apply'); j = txt.index('/-- `of`/`ln` betas', i)
seg = txt[i:j]
seg, _ = remove_simp_arg(seg, 'c11')
seg = remove_have(seg, 'c11')
txt = txt[:i] + seg + txt[j:]

# --- p2OfLn_apply: drop c8 ---
i = txt.index('theorem p2OfLn_apply'); j = txt.index('/-- `dispS', i)
seg = txt[i:j]
seg, _ = remove_simp_arg(seg, 'c8')
seg = remove_have(seg, 'c8')
txt = txt[:i] + seg + txt[j:]

# --- p2Disp_open: drop cr, c8 ---
i = txt.index('theorem p2Disp_open'); j = txt.index('/-- `end4` beta', i)
seg = txt[i:j]
seg, _ = remove_simp_arg(seg, 'cr')
seg = remove_have(seg, 'cr')
seg, _ = remove_simp_arg(seg, 'c8')
seg = remove_have(seg, 'c8')
txt = txt[:i] + seg + txt[j:]

# --- p2E4_apply: drop c1, c8 ---
i = txt.index('theorem p2E4_apply'); j = txt.index('/-- `rsv` beta', i)
seg = txt[i:j]
seg, _ = remove_simp_arg(seg, 'c1')
seg = remove_have(seg, 'c1')
seg, _ = remove_simp_arg(seg, 'c8')
seg = remove_have(seg, 'c8')
txt = txt[:i] + seg + txt[j:]

# --- p2RsvCont_apply: drop c8 ---
i = txt.index('theorem p2RsvCont_apply'); j = txt.index('/-- `enc2` beta', i)
seg = txt[i:j]
seg, _ = remove_simp_arg(seg, 'c8')
seg = remove_have(seg, 'c8')
txt = txt[:i] + seg + txt[j:]

# --- p2Enc_apply: drop ce, ci, cr, c8 (cenc covers the composite) ---
i = txt.index('theorem p2Enc_apply'); j = txt.index('/-- `resv·nm`', i)
seg = txt[i:j]
for n in ('ce', 'ci', 'cr', 'c8'):
    seg, _ = remove_simp_arg(seg, n)
    seg = remove_have(seg, n)
txt = txt[:i] + seg + txt[j:]

io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('done')
