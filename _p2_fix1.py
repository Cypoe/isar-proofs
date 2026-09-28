import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

# replace foldl_cellRev_scott with the foldr-bridge
txt = txt.replace('''/-- `FOLDL (λo.λc. CONS c o)` over cell-lists prepends the input in
    reverse onto the seed's cells. -/
theorem foldl_cellRev_scott (cs acc : List LTerm) :
    cs.foldl (fun a e => cellLit e a) (scottList acc)
      = scottList (cs.reverse ++ acc) := by
  show cs.foldl (fun a e => cellLit e a) (acc.foldr cellLit nilL)
    = (cs.reverse ++ acc).foldr cellLit nilL
  rw [List.foldr_append]
  show cs.foldl (fun a e => cellLit e a) (acc.foldr cellLit nilL)
    = cs.reverse.foldr cellLit (acc.foldr cellLit nilL)
  rw [← List.foldr_reverse]
''', '''/-- `foldr cellLit` onto a Scott-list seed is `scottList` of the
    concatenated cells. -/
theorem foldr_cellLit_scott (cs acc : List LTerm) :
    cs.foldr cellLit (scottList acc) = scottList (cs ++ acc) := by
  show cs.foldr cellLit (acc.foldr cellLit nilL)
    = (cs ++ acc).foldr cellLit nilL
  rw [List.foldr_append]
''')

# fix hread to consume fold_read's foldr result
txt = txt.replace('''    have hread : LRed (ggbA consRevL (scottList (bm e.2.2.2))
        (scottList acc))
        ((bm e.2.2.2).foldl (fun a c => cellLit c a)
          (scottList acc)) := by
      show LRed (ggbA stepConsL (scottList (bm e.2.2.2))
        (scottList acc)) _
      exact fold_read _ _ (fun _ hx => closed_bm hx)
        (closed_scottList haccc)
    rw [foldl_cellRev_scott] at hread''', '''    have hread : LRed (ggbA consRevL (scottList (bm e.2.2.2))
        (scottList acc))
        (scottList ((bm e.2.2.2).reverse ++ acc)) := by
      show LRed (ggbA stepConsL (scottList (bm e.2.2.2))
        (scottList acc)) _
      have h := fold_read _ _ (fun _ hx => closed_bm hx)
        (closed_scottList haccc)
      rw [foldr_cellLit_scott] at h
      exact h''')

# fix p2StepSem_wf simp args
txt = txt.replace('''    simp only [p2StepSem, decide_eq_false hns, if_false]''',
'''    simp only [p2StepSem, decide_eq_false hns]''')

io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('fixed')
