import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

old_macro = '''macro "litSubst" : tactic =>
  `(tactic| simp only [subst, shift_of_closed0 hv,
      subst_of_closed0 hr, subst_of_closed0 hc, subst_of_closed0 hn,'''
new_macro = '''macro "litSubst" v:term r:term c:term n:term : tactic =>
  `(tactic| simp only [subst, shift_of_closed0 $v,
      subst_of_closed0 $r, subst_of_closed0 $c, subst_of_closed0 $n,'''
assert old_macro in txt
txt = txt.replace(old_macro, new_macro)

txt = txt.replace('''      | (intro v hv; litSubst)''',
                  '''      | (intro v hv; litSubst hv hr hc hn)''')

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok')
