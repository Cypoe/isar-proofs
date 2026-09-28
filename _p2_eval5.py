import io, re

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

old1 = '''  have hp1Vc : closed 0 p1V = true :=
    closed_p1ValT 0 he hz hp hb
  have hKI : closed 0 (aps klL [idL]) = true :=
    closed_app closed_klL closed_idL
  have hloccl' : closed 0 (asmLocV p1V) = true := by
    simp only [asmLocV, aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_app (closed_app hp1Vc hKI) closed_klL⟩
  have hprepcl : closed 0 (asmPrepV p1V) = true := by
    simp only [asmPrepV, aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_revL, closed_app (closed_app hp1Vc hKI) hKI⟩'''
new1 = '''  have hp1Vc : closed 0 p1V = true :=
    closed_p1ValT 0 he hz hp hb
  have hKI : closed 0 (aps klL [idL]) = true :=
    closed_app closed_klL closed_idL
  have hinnercl : closed 0 (aps p1V [aps klL [idL],
      aps klL [idL]]) = true :=
    closed_app (closed_app hp1Vc hKI) hKI
  have hloccl' : closed 0 (asmLocV p1V) = true :=
    closed_app (closed_app hp1Vc hKI) closed_klL
  have hprepcl : closed 0 (asmPrepV p1V) = true :=
    closed_app closed_revL hinnercl'''
assert old1 in txt; txt = txt.replace(old1, new1)

old2 = '''  have hloc : LRed (asmLocV p1V) (scottList st.2.1) :=
    (LRed_app_left (LRed_app_left hp1)).trans
      ((LRed_app_left (pairLit_snd _ _ hposcl hlp)).trans
        (pairLit_fst _ _ hlocc hprepc))
  have hinnercl : closed 0 (aps p1V [aps klL [idL],
      aps klL [idL]]) = true :=
    closed_app (closed_app hp1Vc hKI) hKI
  have hprep : LRed (asmPrepV p1V) (scottList st.2.2.reverse) := by
    show LRed (aps revL [aps p1V [aps klL [idL], aps klL [idL]]]) _
    have h1 : LRed (aps p1V [aps klL [idL], aps klL [idL]])
        (scottList st.2.2) :=
      (LRed_app_left (LRed_app_left hp1)).trans
        ((LRed_app_left (pairLit_snd _ _ hposcl hlp)).trans
          (pairLit_snd _ _ hlocc hprepc))
    exact revL_eval _ _ hinnercl hwf2 h1'''
new2 = '''  have hloc : LRed (asmLocV p1V) (scottList st.2.1) := by
    refine (LRed_app_left (LRed_app_left hp1)).trans ?_
    unfold p1AccTV p1AccT
    exact (LRed_app_left (pairLit_snd _ _ hposcl hlp)).trans
      (pairLit_fst _ _ hlocc hprepc)
  have hprep : LRed (asmPrepV p1V) (scottList st.2.2.reverse) := by
    show LRed (aps revL [aps p1V [aps klL [idL], aps klL [idL]]]) _
    have h1 : LRed (aps p1V [aps klL [idL], aps klL [idL]])
        (scottList st.2.2) := by
      refine (LRed_app_left (LRed_app_left hp1)).trans ?_
      unfold p1AccTV p1AccT
      exact (LRed_app_left (pairLit_snd _ _ hposcl hlp)).trans
        (pairLit_snd _ _ hlocc hprepc)
    exact revL_eval _ _ hinnercl hwf2 h1'''
assert old2 in txt; txt = txt.replace(old2, new2)

old3 = '''  have houtcl : closed 0 (asmOutV encT symT basT p1V) = true := by
    simp only [asmOutV, aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_foldlL, hstepcl, hprepcl⟩'''
new3 = '''  have houtcl : closed 0 (asmOutV encT symT basT p1V) = true :=
    closed_app (closed_app (closed_app closed_foldlL hstepcl)
      hprepcl) closed_klL'''
assert old3 in txt; txt = txt.replace(old3, new3)

io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('fixed')
