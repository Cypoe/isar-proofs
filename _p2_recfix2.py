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
        if depth == 0: j = p + 1; break
cont = s[k:j]
# param renames (word-boundary)
cont = re.sub(r'\bencT\b', 'e', cont)
cont = re.sub(r'\bsymT\b', 's', cont)
cont = re.sub(r'\blcT\b', 'lc', cont)
cont = re.sub(r'\bbasT\b', 'b', cont)
# acc splices: eqStr arg (.var 7) and foldl arg (.var 10)
assert '(.var 1)]), (.var 7), (aps' in cont
cont = cont.replace('(.var 1)]), (.var 7), (aps', '(.var 1)]), accT, (aps')
assert '(.var 10)' in cont
cont = cont.replace('(.var 10)', 'accT')
# remaining (.var 7) must be exactly the ENC it-slot
assert cont.count('(.var 7)') == 1, cont.count('(.var 7)')

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()
# replace the broken p2RecContT def (find its span)
i0 = txt.index('def p2RecContT')
i1 = txt.index('\n\n', i0)
newdef = 'def p2RecContT (e s lc b accT : LTerm) : LTerm :=\n  ' + cont
txt = txt[:i0] + newdef + txt[i1:]

# closedness: unfold consRevL? no — keep inline consRev raw.
old2 = '''  simp only [p2RecContT, p2ResvRawT, closed, aps, List.foldl,
             Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)'''
new2 = '''  simp only [p2RecContT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)'''
assert old2 in txt
txt = txt.replace(old2, new2)
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('p2RecContT replaced with verbatim CONT')
