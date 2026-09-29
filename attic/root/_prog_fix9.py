import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

old = '''macro "litSubst" v:term r:term c:term n:term : tactic =>'''
new = '''macro "litSubst" v:term "," r:term "," c:term "," n:term : tactic =>'''
assert old in txt
txt = txt.replace(old, new)

txt = txt.replace('''    repeat' constructor
    all_goals first
      | (intro x hx; cases hx)
      | litClosed
      | (intro v hv; litSubst hv hr hc hn)''',
'''    and_intros
    all_goals first
      | (intro x hx; cases hx)
      | litClosed
      | (intro v hv; litSubst hv, hr, hc, hn)''')

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok, litSubst-sites:', txt.count('litSubst hv, hr, hc, hn'),
      'and_intros:', txt.count('and_intros'))
