import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# replace the two smoke examples with calibrated idioms
i0 = txt.index('/-- one emitted item')
i1 = txt.index('end ISAR')
block = '''/-- closed-0 idiom on a real emitted item (`rbbT`-leaf). -/
example (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    closed 0 (aps conssL [(aps conssL [(nibLit 6), aps conssL
        [(nibLit 12), klL]]),
      aps conssL [(aps pairSrcL [(nibLit 5), (nibLit 15)]),
        rbbT]]) = true := by
  simp only [closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first | exact hr | exact hc | exact hn | decide

/-- closed-2 idiom for fuelR items (`.var 1` = fv slot). -/
example (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    closed 2 (aps conssL [(nibLit 6), .var 1]) = true := by
  simp only [closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first | exact hr | exact hc | exact hn | decide

/-- subst clause for fuelR items: `subst v 1` keeps `.var 1`->v closed. -/
example (rbbT cbT nbT v : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) (hv : closed 0 v = true) :
    closed 0 (subst v 1 (aps conssL [(nibLit 6),
      aps conssL [.var 1, rbbT]])) = true := by
  simp only [subst, shift_of_closed0 hv, closed, aps, List.foldl,
    Bool.and_eq_true, hv]
  repeat' constructor
  all_goals first | exact hr | exact hc | exact hn | exact hv | decide
'''
txt = txt[:i0] + block + '\n' + txt[i1:]
io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok')
