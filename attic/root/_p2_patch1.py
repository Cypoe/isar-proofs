import io
txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()
old = """/-- semantic prep entry: the item, its position, its declared
    length bytes, and the bytes the encoder emits for it under
    this entry's instantiated resolver. -/
structure P2Item where
  it : AsmItem
  ofB : B4L
  lnB : B4L
  bs : B4L

/-- prep entry term `PAIR it (PAIR of4 ln4)`. -/
def p2EntryT (e : P2Item) : LTerm :=
  pairLit e.it.itT
    (pairLit (scottList (bm e.ofB)) (scottList (bm e.lnB)))

/-- per-item semantic pass-2 step: labels pass acc through,
    insn items prepend their emitted bytes REVERSED (the
    `FOLDL (\\o.\\c. CONS c o)` accumulation order). -/
def p2StepSem (e : P2Item) (acc : List LTerm) : List LTerm :=
  if decide (e.it.ns = lblNibs) then acc
  else (bm e.bs).reverse ++ acc"""
new = """/-- semantic prep entry `(it, ofB, lnB, bs)`: the item, its
    position, its declared length bytes, and the bytes the
    encoder emits for it under this entry's instantiated
    resolver. -/
abbrev P2Item := AsmItem × B4L × B4L × B4L

/-- prep entry term `PAIR it (PAIR of4 ln4)`. -/
def p2EntryT (e : P2Item) : LTerm :=
  pairLit e.1.itT
    (pairLit (scottList (bm e.2.1)) (scottList (bm e.2.2.1)))

/-- per-item semantic pass-2 step: labels pass acc through,
    insn items prepend their emitted bytes REVERSED (the
    `FOLDL (\\o.\\c. CONS c o)` accumulation order). -/
def p2StepSem (e : P2Item) (acc : List LTerm) : List LTerm :=
  if decide (e.1.ns = lblNibs) then acc
  else (bm e.2.2.2).reverse ++ acc"""
assert old in txt
txt = txt.replace(old, new)
txt = txt.replace(
  'simp only [p2E4ContT, closed, aps, List.foldl, Bool.and_eq_true]',
  'simp only [p2E4ContT, p2RsvContT, p2ResvRawT, closed, aps,\n             List.foldl, Bool.and_eq_true]')
txt = txt.replace(
  'simp only [p2DispT, closed, aps, List.foldl, Bool.and_eq_true]',
  'simp only [p2DispT, p2E4ContT, p2RsvContT, p2ResvRawT, closed, aps,\n             List.foldl, Bool.and_eq_true]')
txt = txt.replace(
  'simp only [p2DispS, closed, aps, List.foldl, Bool.and_eq_true]',
  'simp only [p2DispS, p2E4ContT, p2RsvContT, p2ResvRawT, closed, aps,\n             List.foldl, Bool.and_eq_true]')
txt = txt.replace(
  'simp only [p2OfLnContT, closed, aps, List.foldl, Bool.and_eq_true]',
  'simp only [p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT, p2ResvRawT,\n             closed, aps, List.foldl, Bool.and_eq_true]')
txt = txt.replace(
  'simp only [p2RecContT, closed, aps, List.foldl, Bool.and_eq_true]',
  'simp only [p2RecContT, p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT,\n             p2ResvRawT, closed, aps, List.foldl, Bool.and_eq_true]')
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
