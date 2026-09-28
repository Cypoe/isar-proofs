import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()
txt = txt.replace('(List.mem_cons_self _ _)', 'List.mem_cons_self')

old1 = '''  rw [if_neg (by decide : ¬(0 < 0)), if_pos rfl]
  exact shift_of_closed0 hs 0 0'''
new1 = '''  show conssChain its (shift 0 0 s) = _
  congr 1
  exact shift_of_closed0 hs 0 0'''
assert old1 in txt; txt = txt.replace(old1, new1)
# drop the now-dead congr-context line for that block — check structure
old1b = '''  show conssChain its (subst s 0 (.var 0)) = _
  congr 1
  simp only [subst]
  show conssChain its (shift 0 0 s) = _
  congr 1
  exact shift_of_closed0 hs 0 0'''
new1b = '''  show conssChain its (subst s 0 (.var 0)) = _
  congr 1
  show shift 0 0 s = s
  exact shift_of_closed0 hs 0 0'''
assert old1b in txt; txt = txt.replace(old1b, new1b)

old2 = '''    have hs : subst t 0 (.var 0) = t := by
      simp only [subst]
      rw [if_neg (by decide : ¬(0 < 0)), if_pos rfl]
      exact shift_of_closed0 htcl 0 0'''
new2 = '''    have hs : subst t 0 (.var 0) = t := by
      show shift 0 0 t = t
      exact shift_of_closed0 htcl 0 0'''
assert old2 in txt; txt = txt.replace(old2, new2)

old3 = '''  congr 1
    simp only [subst]
    rw [if_pos (by decide : 0 < 1)]'''
new3 = '''    congr 1
    simp only [subst]
    rw [if_pos (by decide : 0 < 1)]'''

old4 = '''  have h := (LRed_app_left (LRed_app_left (LRed_app_left hfuel))).trans
    (LRed_app_left (justL_apply3 v fn fj hv hfn hj))
  show LRed (((fuelT.app fn).app fj).app rest) _
  exact h'''
new4 = '''  have h := (LRed_app_left (LRed_app_left (LRed_app_left hfuel))).trans
    (LRed_app_left (x := rest) (justL_apply3 v fn fj hv hfn hj))
  show LRed (((fuelT.app fn).app fj).app rest) _
  exact h'''
assert old4 in txt; txt = txt.replace(old4, new4)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
