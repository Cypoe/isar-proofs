import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

old_c = '''macro "litClosed" : tactic =>
  `(tactic| simp only [closed, aps, List.foldl,
      Bool.and_eq_true, closed_conssL_any, closed_klL_any,
      closed_kilL_any, closed_nilL_any, closed_pairSrcL_any,
      closed_nibLit_any] <;>
    repeat' constructor <;>
    first | assumption | decide)'''
new_c = '''macro "litClosed" : tactic =>
  `(tactic| (try simp only [closed, aps, List.foldl,
      Bool.and_eq_true, closed_conssL_any, closed_klL_any,
      closed_kilL_any, closed_nilL_any, closed_pairSrcL_any,
      closed_nibLit_any]) <;>
    repeat' constructor <;>
    first | assumption | decide)'''
assert old_c in txt
txt = txt.replace(old_c, new_c)

old_s = '''macro "litSubst" v:term r:term c:term n:term : tactic =>
  `(tactic| simp only [subst, shift_of_closed0 $v,'''
new_s = '''macro "litSubst" v:term r:term c:term n:term : tactic =>
  `(tactic| (try simp only [subst, shift_of_closed0 $v,'''
assert old_s in txt
txt = txt.replace(old_s, new_s)

old_s2 = '''      closed_nilL_any, closed_pairSrcL_any, closed_nibLit_any] <;>
    repeat' constructor <;>
    first | assumption | decide)

set_option maxRecDepth 10000 in'''
new_s2 = '''      closed_nilL_any, closed_pairSrcL_any, closed_nibLit_any]) <;>
    repeat' constructor <;>
    first | assumption | decide)

set_option maxRecDepth 10000 in'''
assert old_s2 in txt
txt = txt.replace(old_s2, new_s2)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok')
