import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# bump limits on the three giant defs
txt = txt.replace(
    'def progSegs (rbbT cbT nbT : LTerm) : List OSeg :=',
    'set_option maxRecDepth 10000 in\n'
    'set_option maxHeartbeats 16000000 in\n'
    'def progSegs (rbbT cbT nbT : LTerm) : List OSeg :=')
txt = txt.replace(
    'def progBodyOpen (fsT fuelT rbbT cbT nbT : LTerm) : LTerm :=',
    'set_option maxRecDepth 10000 in\n'
    'set_option maxHeartbeats 16000000 in\n'
    'def progBodyOpen (fsT fuelT rbbT cbT nbT : LTerm) : LTerm :=')
txt = txt.replace(
    'def programT : LTerm :=',
    'set_option maxRecDepth 10000 in\n'
    'set_option maxHeartbeats 16000000 in\n'
    'def programT : LTerm :=')

# fix the closedness smoke test: leaf lemmas + hyp rewrites
old_ex = '''example (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    closed 0 (aps conssL [(nibLit 6), aps conssL [(nibLit 12),
      rbbT]]) = true := by
  simp only [closed, aps, List.foldl, conssL, nilL, nibLit, absN,
    pairSrcL, Bool.and_eq_true, decide_eq_true_eq, hr, hc, hn]'''
new_ex = '''example (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    closed 0 (aps conssL [(nibLit 6), aps conssL [(nibLit 12),
      rbbT]]) = true := by
  simp only [closed, aps, List.foldl, Bool.and_eq_true,
    closed_nibLit, closed_conssL, closed_nilL, closed_pairSrcL,
    hr, hc, hn]'''
assert old_ex in txt; txt = txt.replace(old_ex, new_ex)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok')
