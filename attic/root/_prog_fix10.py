import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# add litTree after litSubst macro definition
anchor = '''    repeat' constructor <;>
    first | assumption | decide)

set_option maxRecDepth 10000 in'''
litTree = '''    repeat' constructor <;>
    first | assumption | decide)

/-- recursively decompose `And`/`∀` shapes and close each leaf:
    `∀ x ∈ []` is vacuous; `closed d <lit>` by `litClosed`;
    `∀ v, closed 0 v → closed 0 (subst v 1 c)` by `litSubst`. -/
macro "litTree" : tactic =>
  `(tactic| first
    | (intro x hx; cases hx)
    | litClosed
    | (intro v hv; litSubst hv, hr, hc, hn)
    | (constructor <;> litTree)
    | (refine ⟨?_, ?_⟩ <;> litTree))

set_option maxRecDepth 10000 in'''
assert anchor in txt
txt = txt.replace(anchor, litTree)

txt = txt.replace('''    and_intros
    all_goals first
      | (intro x hx; cases hx)
      | litClosed
      | (intro v hv; litSubst hv, hr, hc, hn)''',
'''    all_goals litTree''')

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok, litTree sites:', txt.count('all_goals litTree'))
