import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

# insert pairLit_sndKI before the asm_eval block's comment
old0 = '''/-- program-level pass-1 well-formedness: the fragment fold
    preserves loc/prep closedness and pos-length. -/
theorem p1ProgSem_wf'''
new0 = '''/-- `pairLit` second-projection under the `K·I`-application form
    (`KI` as `aps klL [idL]`, the selector asmLocV/asmPrepV emit). -/
theorem pairLit_sndKI (a b : LTerm) (ha : closed 0 a = true)
    (hb : closed 0 b = true) :
    LRed (.app (pairLit a b) (aps klL [idL])) b := by
  refine (pairLit_apply a b (aps klL [idL]) ha hb).trans ?_
  show LRed (aps (aps klL [idL]) [a, b]) b
  exact kiApp_apply2 a b

/-- program-level pass-1 well-formedness: the fragment fold
    preserves loc/prep closedness and pos-length. -/
theorem p1ProgSem_wf'''
assert old0 in txt; txt = txt.replace(old0, new0)

old1 = '''    refine (LRed_app_left (LRed_app_left hp1)).trans ?_
    unfold p1AccTV p1AccT
    exact (LRed_app_left (pairLit_snd _ _ hposcl hlp)).trans
      (pairLit_fst _ _ hlocc hprepc)'''
new1 = '''    refine (LRed_app_left (LRed_app_left hp1)).trans ?_
    unfold p1AccTV p1AccT
    exact (LRed_app_left (pairLit_sndKI _ _ hposcl hlp)).trans
      (pairLit_fst _ _ hlocc hprepc)'''
assert old1 in txt; txt = txt.replace(old1, new1)

old2 = '''      refine (LRed_app_left (LRed_app_left hp1)).trans ?_
      unfold p1AccTV p1AccT
      exact (LRed_app_left (pairLit_snd _ _ hposcl hlp)).trans
        (pairLit_snd _ _ hlocc hprepc)'''
new2 = '''      refine (LRed_app_left (LRed_app_left hp1)).trans ?_
      unfold p1AccTV p1AccT
      exact (LRed_app_left (pairLit_sndKI _ _ hposcl hlp)).trans
        (pairLit_sndKI _ _ hlocc hprepc)'''
assert old2 in txt; txt = txt.replace(old2, new2)

io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
