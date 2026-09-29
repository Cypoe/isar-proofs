import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# add subst_var_self before subst_conssChain_var
old0 = '''/-- `subst s 0` of a `.var 0`-tailed chain with closed items
    splices `s` at the tail. -/
theorem subst_conssChain_var'''
new0 = '''/-- `subst s 0 (.var 0)` is `s` itself (shift of closed). -/
theorem subst_var_self (s : LTerm) (hs : closed 0 s = true) :
    subst s 0 (.var 0) = s := by
  show shift 0 0 s = s
  exact shift_of_closed0 hs 0 0

/-- `subst s 0` of a `.var 0`-tailed chain with closed items
    splices `s` at the tail. -/
theorem subst_conssChain_var'''
assert old0 in txt; txt = txt.replace(old0, new0)

old1 = '''  rw [subst_conssChain, map_subst_closed0 its s hits]
  show conssChain its (subst s 0 (.var 0)) = _
  congr 1
  show shift 0 0 s = s
  exact shift_of_closed0 hs 0 0'''
new1 = '''  rw [subst_conssChain, map_subst_closed0 its s hits,
      subst_var_self s hs]'''
assert old1 in txt; txt = txt.replace(old1, new1)

old2 = '''    have hs : subst t 0 (.var 0) = t := by
      show shift 0 0 t = t
      exact shift_of_closed0 htcl 0 0
    rwa [hs] at hh'''
new2 = '''    rwa [subst_var_self t htcl] at hh'''
assert old2 in txt; txt = txt.replace(old2, new2)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
