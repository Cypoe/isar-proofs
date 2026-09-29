import io, re
mod = io.open('src/ISAR/SpecVocabulary.lean', encoding='utf-8').read()
i = mod.index('def emitStepT')
s = mod[i:i+1600]
k = s.index('aps (.var 0) [') + len('aps (.var 0) [')
depth = 1; j = k
for p, ch in enumerate(s[k:], k):
    if ch == '[': depth += 1
    elif ch == ']':
        depth -= 1
        if depth == 0: j = p; break
cont = s[k:j]
cont = re.sub(r'\bencT\b', 'e', cont)
cont = re.sub(r'\bsymT\b', 's', cont)
cont = re.sub(r'\blcT\b', 'lc', cont)
cont = re.sub(r'\bbasT\b', 'b', cont)
cont = cont.replace('(.var 1)]), (.var 7), (aps', '(.var 1)]), accT, (aps')
cont = cont.replace('(.var 10)', 'accT')
assert cont.count('(.var 7)') == 1
assert not cont.endswith(']')

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()
i0 = txt.index('def p2RecContT')
i1 = txt.index('\n\n', i0)
txt = txt[:i0] + 'def p2RecContT (e s lc b accT : LTerm) : LTerm :=\n  ' + cont + txt[i1:]

# give every open the conssL + consRevL haves (subst descends the
# whole CONT/disp term into those leaves at depth 9-10)
for anchor in ['c9 : ∀ c, closed c foldlL = true := fun c =>',
               'c8 : ∀ c, closed c conssL = true := fun c =>']:
    pass  # already present in p2Step_open

# p2RecCont_apply, p2OfLn_apply, p2Disp_open, p2E4_apply,
# p2RsvCont_apply, p2Enc_apply: insert c8 conssL + c11 consRevL
# before c9 foldlL have, and extend simp sets
ins_haves = '''  have c8 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c9'''
for name in ['theorem p2RecCont_apply', 'theorem p2OfLn_apply',
             'theorem p2Disp_open', 'theorem p2E4_apply',
             'theorem p2RsvCont_apply', 'theorem p2Enc_apply']:
    i = txt.index(name)
    seg = txt[i:i+9000]
    if 'closed c conssL' not in seg.split('exact LRed_of_hsteps')[0]:
        seg2 = seg.replace('  have c9', ins_haves, 1)
        txt = txt[:i] + seg2 + txt[i+9000:]

# extend simp arg lists: add c8, c11 where missing
for pat, rep in [
  ('ce, cs, clc, cb, ca, ci, co, c1, c2, c3, c4, c5, c6, c7,\n          c9, c10',
   'ce, cs, clc, cb, ca, ci, co, c1, c2, c3, c4, c5, c6, c7,\n          c8, c9, c10, c11'),
  ('ce, cs, clc, cb, ca, ci, co, cn, c1, c2, c3, c4, c5, c6,\n          c7, c9, c10',
   'ce, cs, clc, cb, ca, ci, co, cn, c1, c2, c3, c4, c5, c6,\n          c7, c8, c9, c10, c11'),
  ('ce, cs, clc, cb, ca, ci, co, cn, ct, cr, c1, c2, c3, c4,\n          c5, c6, c7, c9',
   'ce, cs, clc, cb, ca, ci, co, cn, ct, cr, c1, c2, c3, c4,\n          c5, c6, c7, c8, c9, c10, c11'),
  ('ce, cs, clc, ca, ci, ce4, c1, c4, c5, c6, c9, c10, c11',
   'ce, cs, clc, ca, ci, ce4, c1, c4, c5, c6, c8, c9, c10, c11'),
  ('ce, ca, ci, cr, c9, c10, c11',
   'ce, ca, ci, cr, c8, c9, c10, c11'),
]:
    txt = txt.replace(pat, rep)

# also need a c10 klL have in p2Disp_open (it lacked c10)
seg = txt[txt.index('theorem p2Disp_open'):]
if 'closed c klL' not in seg.split('exact LRed_of_hsteps')[0][:4000]:
    seg2 = seg.replace('  have c9 : ∀ c, closed c foldlL = true := fun c =>',
      '''  have c8 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>''', 1)
    txt = txt[:txt.index('theorem p2Disp_open')] + seg2
# and c10 klL + c11 consRevL haves for p2Disp_open
for name in ['theorem p2Disp_open']:
    i = txt.index(name)
    seg = txt[i:i+9000]
    if 'closed c klL' not in seg.split('exact LRed_of_hsteps')[0]:
        seg2 = seg.replace('  exact LRed_of_hsteps',
          '''  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  exact LRed_of_hsteps''', 1)
        txt = txt[:i] + seg2 + txt[i+9000:]
# same for p2RecCont_apply / p2OfLn_apply (add c11 consRevL)
for name in ['theorem p2RecCont_apply', 'theorem p2OfLn_apply']:
    i = txt.index(name)
    seg = txt[i:i+9000]
    if 'closed c consRevL' not in seg.split('exact LRed_of_hsteps')[0]:
        seg2 = seg.replace('  exact LRed_of_hsteps',
          '''  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  exact LRed_of_hsteps''', 1)
        txt = txt[:i] + seg2 + txt[i+9000:]

io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('fixed')
