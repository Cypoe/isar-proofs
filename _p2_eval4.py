import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

block = '''
/-- program-level pass-1 well-formedness: the fragment fold
    preserves loc/prep closedness and pos-length. -/
theorem p1ProgSem_wf (encT zrvT : LTerm) (basB : B4L) :
    ∀ (frs : List (List AsmItem)),
    (∀ it ∈ frs.flatten, AsmItem.V encT zrvT it) →
    (∀ it ∈ frs.flatten, it.ns = lblNibs →
        ∃ nm rest, it.rrCs = nm :: rest) →
    ∀ (st : P1St),
      (∀ c ∈ st.2.1, closed 0 c = true) →
      (∀ c ∈ st.2.2, closed 0 c = true) →
      st.1.length = 4 →
      (∀ c ∈ (p1ProgSem basB frs st).2.1, closed 0 c = true) ∧
      (∀ c ∈ (p1ProgSem basB frs st).2.2, closed 0 c = true) ∧
      (p1ProgSem basB frs st).1.length = 4 := by
  intro frs
  induction frs with
  | nil => intro _ _ st h1 h2 hl4; exact ⟨h1, h2, hl4⟩
  | cons its frs ih =>
    intro hV hrrn st h1 h2 hl4
    simp only [p1ProgSem, List.foldl_cons]
    have hVh : ∀ i ∈ its, AsmItem.V encT zrvT i := fun i hi =>
      hV i (List.mem_flatten.mpr ⟨its, List.mem_cons_self, hi⟩)
    have hrrh : ∀ i ∈ its, i.ns = lblNibs →
        ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
      hrrn i (List.mem_flatten.mpr ⟨its, List.mem_cons_self, hi⟩)
    have hVr : ∀ i ∈ frs.flatten, AsmItem.V encT zrvT i :=
      fun i hi => hV i (List.mem_flatten.mpr (by
        obtain ⟨l', hl', hmem⟩ := List.mem_flatten.mp hi
        exact ⟨l', List.mem_cons_of_mem _ hl', hmem⟩))
    have hrrr : ∀ i ∈ frs.flatten, i.ns = lblNibs →
        ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
      hrrn i (List.mem_flatten.mpr (by
        obtain ⟨l', hl', hmem⟩ := List.mem_flatten.mp hi
        exact ⟨l', List.mem_cons_of_mem _ hl', hmem⟩))
    exact ih hVr hrrr (its.foldl (fun s i => p1StepSem basB i s) st)
      (p1Fold_wf encT zrvT basB its hVh hrrh st h1 h2 hl4).1
      (p1Fold_wf encT zrvT basB its hVh hrrh st h1 h2 hl4).2.1
      (p1Fold_wf encT zrvT basB its hVh hrrh st h1 h2 hl4).2.2

/-- the pass-2 fold preserves accumulator-cell closedness. -/
theorem p2FoldSem_wf : ∀ (es : List P2Item) (acc : List LTerm),
    (∀ c ∈ acc, closed 0 c = true) →
    ∀ c ∈ es.foldl (fun a e => p2StepSem e a) acc,
      closed 0 c = true := by
  intro es; induction es with
  | nil => intro acc h c hc; exact h c hc
  | cons e es ih =>
    intro acc h c hc
    simp only [List.foldl_cons] at hc
    exact ih (p2StepSem e acc) (p2StepSem_wf e acc h) c hc

/-- **`asm_eval`**: the whole `assemble` stage reduces to
    `PAIR (REV (p2FoldSem prep)) loc` — emitted bytes in forward
    order paired with the pass-1 local table. -/
theorem asm_eval (encT zrvT progT symT basT : LTerm)
    (basB : B4L) (st : P1St) (es : List P2Item)
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hp : closed 0 progT = true) (hs : closed 0 symT = true)
    (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4)
    (hp1 : LRed (p1ValT encT zrvT progT basT) (p1AccTV st))
    (hwf1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (hwf2 : ∀ c ∈ st.2.2, closed 0 c = true)
    (h2 : List.Forall₂ p2EntryRel st.2.2.reverse es)
    (hV : ∀ e ∈ es, p2ItmV encT symT
        (asmLocV (p1ValT encT zrvT progT basT)) basT e)
    (hlen : ∀ e ∈ es, e.2.1.length = 4 ∧ e.2.2.1.length = 4) :
    LRed (aps asmL [encT, zrvT, progT, symT, basT])
      (pairLit (scottList (p2FoldSem es).reverse)
               (scottList st.2.1)) := by
  set p1V := p1ValT encT zrvT progT basT with hp1V
  have hp1Vc : closed 0 p1V = true :=
    closed_p1ValT 0 he hz hp hb
  have hKI : closed 0 (aps klL [idL]) = true :=
    closed_app closed_klL closed_idL
  have hloccl' : closed 0 (asmLocV p1V) = true := by
    simp only [asmLocV, aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_app (closed_app hp1Vc hKI) closed_klL⟩
  have hprepcl : closed 0 (asmPrepV p1V) = true := by
    simp only [asmPrepV, aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_revL, closed_app (closed_app hp1Vc hKI) hKI⟩
  -- p1V projections: loc = snd·fst, prep = REV (snd·snd)
  have hposcl : closed 0 (scottList (bm st.1)) = true :=
    closed_scott_bm _
  have hlocc : closed 0 (scottList st.2.1) = true :=
    closed_scottList hwf1
  have hprepc : closed 0 (scottList st.2.2) = true :=
    closed_scottList hwf2
  have hlp : closed 0 (pairLit (scottList st.2.1)
      (scottList st.2.2)) = true :=
    closed_pairLit (closed_mono hlocc (Nat.zero_le 1))
      (closed_mono hprepc (Nat.zero_le 1))
  have hloc : LRed (asmLocV p1V) (scottList st.2.1) :=
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
    exact revL_eval _ _ hinnercl hwf2 h1
  -- the emit fold
  have hstepcl : closed 0 (emitStepT encT symT (asmLocV p1V) basT) =
      true := closed_emitStepT 0 he hs hloccl' hb
  have htscl : ∀ c ∈ st.2.2.reverse, closed 0 c = true :=
    fun c hc => hwf2 c (List.mem_reverse.mp hc)
  have hrevsccl : closed 0 (scottList st.2.2.reverse) = true :=
    closed_scottList htscl
  have hout : LRed (asmOutV encT symT basT p1V)
      (scottList (p2FoldSem es)) := by
    show LRed (aps foldlL
        [emitStepT encT symT (asmLocV p1V) basT,
         asmPrepV p1V, klL]) (scottList (p2FoldSem es))
    have h0 : LRed (aps foldlL
          [emitStepT encT symT (asmLocV p1V) basT,
           asmPrepV p1V, klL])
        (ggbA (emitStepT encT symT (asmLocV p1V) basT)
          (scottList st.2.2.reverse) klL) :=
      (LRed_app_left (LRed_app_right hprep)).trans
        (foldl_to_ggb _ _ _ hstepcl hrevsccl closed_klL)
    have h1 := fold_run _ hstepcl st.2.2.reverse klL htscl closed_klL
    have h2' := p2Fold_eval encT symT (asmLocV p1V) basT basB
      he hs hloccl' hb hbas hb4 h2 hV hlen [] klL
      (fun c hc => nomatch hc) closed_klL
      Relation.ReflTransGen.refl
    have h := h0.trans (h1.trans h2')
    show LRed _ (scottList (p2FoldSem es))
    exact h
  -- REV out + PAIR
  have houtcl : closed 0 (asmOutV encT symT basT p1V) = true := by
    simp only [asmOutV, aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_foldlL, hstepcl, hprepcl⟩
  have hcells : ∀ c ∈ p2FoldSem es, closed 0 c = true :=
    p2FoldSem_wf es [] (fun c hc => nomatch hc)
  have hrev : LRed (aps revL [asmOutV encT symT basT p1V])
      (scottList (p2FoldSem es).reverse) :=
    revL_eval _ _ houtcl hcells hout
  have hrevcl : closed 0 (scottList (p2FoldSem es).reverse) = true :=
    closed_scottList (fun c hc => hcells c (List.mem_reverse.mp hc))
  have hopen := asm_open encT zrvT progT symT basT he hz hp hs hb
  have hfinal : LRed (aps pairSrcL
        [aps revL [asmOutV encT symT basT p1V], asmLocV p1V])
      (pairLit (scottList (p2FoldSem es).reverse)
               (scottList st.2.1)) :=
    pairSrcCell_nf hrev hloc hrevcl hlocc
  exact hopen.trans hfinal
'''

txt = txt.replace('\nend ISAR', '\n' + block + '\nend ISAR')
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('appended asm_eval')
