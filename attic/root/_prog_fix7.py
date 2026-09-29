import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# var-closedness at symbolic depth: expose decide via `show`, then rw+omega
txt = txt.replace(
    '(by rw [decide_eq_true_eq]; omega)',
    '(by show decide (0 < d + 1) = true; rw [decide_eq_true_eq]; omega)')
# the d+2 ones (inside fuelR's λfv.λt and the .abs (.var 0) frags)
txt = txt.replace(
    '(by show decide (0 < d + 1) = true; rw [decide_eq_true_eq]; omega))\n      (by show decide (0 < d + 1)',
    'XXX')  # no-op guard
txt = txt.replace(
    '''    refine ⟨⟨⟨hfu, by rw [decide_eq_true_eq]; omega⟩, ?_⟩, htcl⟩
    exact closed_conssChain a (.var 0) (d + 2)
      (fun c hc => closed_mono ((hcs c hc).1 :
        closed 2 c = true) (by omega))
      (by show decide (0 < d + 1) = true; rw [decide_eq_true_eq]; omega)''',
    '''    refine ⟨⟨⟨hfu, by show decide (0 < d + 2) = true;
        rw [decide_eq_true_eq]; omega⟩, ?_⟩, htcl⟩
    exact closed_conssChain a (.var 0) (d + 2)
      (fun c hc => closed_mono ((hcs c hc).1 :
        closed 2 c = true) (by omega))
      (by show decide (0 < d + 2) = true; rw [decide_eq_true_eq]; omega)''')

# closed_osegApp stS/bDS: `.abs (.var 0)` frags and inner `.var 0` tails
txt = txt.replace(
    '''    refine ⟨⟨⟨hfs, ?_⟩, by simp only [closed]; omega⟩, htcl⟩''',
    '''    refine ⟨⟨⟨hfs, ?_⟩, by show decide (0 < d + 2) = true;
        rw [decide_eq_true_eq]; omega⟩, htcl⟩''')
txt = txt.replace(
    '''    refine ⟨⟨⟨hfs, ?_⟩, by simp⟩, htcl⟩''',
    '''    refine ⟨⟨⟨hfs, ?_⟩, by show decide (0 < d + 2) = true;
        rw [decide_eq_true_eq]; omega⟩, htcl⟩''')
txt = txt.replace(
    '''    refine ⟨⟨⟨hfs, by simp⟩, ?_⟩, htcl⟩''',
    '''    refine ⟨⟨⟨hfs, by show decide (0 < d + 2) = true;
        rw [decide_eq_true_eq]; omega⟩, ?_⟩, htcl⟩''')
txt = txt.replace(
    '''    refine ⟨⟨closed_mono closed_conssL (Nat.zero_le (d + 1)), ?_⟩,
      by simp⟩''',
    '''    refine ⟨⟨closed_mono closed_conssL (Nat.zero_le (d + 1)), ?_⟩,
      by show decide (0 < d + 1) = true; rw [decide_eq_true_eq]; omega⟩''')

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('done')
