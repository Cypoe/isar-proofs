import io

emit_txt = io.open('_prog_emit.txt', encoding='utf-8').read()
txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

block = '''
/-- programOf's per-routine segment model: the emitted spine read as
    `List OSeg` (items carry `rbbT`/`cbT`/`nbT` params; fuel-frag items
    keep `.var 1` for `fv`). -/
''' + emit_txt + '''

/-- the emitted body equals the segment fold — structural identity
    checked by the kernel (`osegChain`/`psegChain`/`conssChain`/
    `aps` unfold to the same tree). -/
theorem progBody_eq (fsT fuelT rbbT cbT nbT : LTerm) :
    progBodyOpen fsT fuelT rbbT cbT nbT =
      osegChain fsT fuelT (progSegs rbbT cbT nbT) nilL := rfl

/-- one emitted item's closedness idiom (smoke test for the generated
    `closed_progSegs` discharge). -/
example (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    closed 0 (aps conssL [(nibLit 6), aps conssL [(nibLit 12),
      rbbT]]) = true := by
  simp only [closed, aps, List.foldl, conssL, nilL, nibLit, absN,
    pairSrcL, Bool.and_eq_true, decide_eq_true_eq, hr, hc, hn]

/-- subst-normalization smoke test on a small emitted-shape spine. -/
example (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    subst rbbT 0 (aps conssL [(nibLit 6), .var 2]) =
      aps conssL [(nibLit 6), rbbT] := by
  simp only [subst, aps, List.foldl]
  rw [shift_of_closed0 hr]
'''

txt = txt.replace('\nend ISAR', block + '\nend ISAR')
io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('spliced', len(block), 'chars')
