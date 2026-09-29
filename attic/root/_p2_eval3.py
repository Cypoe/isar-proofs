import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

block = '''
/-- `FOLDL (λo.λc. CONS c o)` over cell-lists prepends the input in
    reverse onto the seed's cells. -/
theorem foldl_cellRev_scott (cs acc : List LTerm) :
    cs.foldl (fun a e => cellLit e a) (scottList acc)
      = scottList (cs.reverse ++ acc) := by
  show cs.foldl (fun a e => cellLit e a) (acc.foldr cellLit nilL)
    = (cs.reverse ++ acc).foldr cellLit nilL
  rw [List.foldr_append]
  show cs.foldl (fun a e => cellLit e a) (acc.foldr cellLit nilL)
    = cs.reverse.foldr cellLit (acc.foldr cellLit nilL)
  rw [← List.foldr_reverse]

/-- per-item contract for pass-2 emission: the item satisfies the
    encoder contract under ITS OWN resolver (the `end4` built from
    this entry's `of`/`ln` bytes), and its byte output normalizes to
    the declared emitted bytes. -/
def p2ItmV (encT sT lcT basT : LTerm) (e : P2Item) : Prop :=
  AsmItem.V encT (p2ResvT sT lcT
    (aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
                 scottList (bm e.2.2.1)])) e.1 ∧
  LRed e.1.byT (scottList (bm e.2.2.2))

/-- **`p2_step_eval`**: one emitted pass-2 step —
    `emitstep·acc·rec` evaluates to the semantic `p2StepSem`:
    label entries pass the accumulator through, instruction entries
    prepend the encoder's emitted bytes in reverse-cell order. -/
theorem p2_step_eval (encT sT lcT basT accT recT : LTerm)
    (basB : B4L) (e : P2Item) (acc : List LTerm)
    (he : closed 0 encT = true) (hs : closed 0 sT = true)
    (hlc : closed 0 lcT = true) (hb : closed 0 basT = true)
    (ha : closed 0 accT = true) (hr : closed 0 recT = true)
    (hbas : LRed basT (scottList (bm basB)))
    (hrec : LRed recT (p2EntryT e))
    (hit : p2ItmV encT sT lcT basT e)
    (hacc : LRed accT (scottList acc))
    (haccc : ∀ c ∈ acc, closed 0 c = true)
    (hb4 : basB.length = 4) (hof4 : e.2.1.length = 4)
    (hln4 : e.2.2.1.length = 4) :
    LRed (aps (emitStepT encT sT lcT basT) [accT, recT])
         (scottList (p2StepSem e acc)) := by
  obtain ⟨hitV, hby⟩ := hit
  obtain ⟨⟨tgT, rrT, hitC, htag, _hrr2, htgcl, hrrcl⟩, hitcl, _hrrCs,
      hbycl, hlncl, henc, _hlnT⟩ := hitV
  -- closedness of the entry components
  have hof4cl : closed 0 (scottList (bm e.2.1)) = true :=
    closed_scott_bm _
  have hln4cl : closed 0 (scottList (bm e.2.2.1)) = true :=
    closed_scott_bm _
  have holcl : closed 0 (pairLit (scottList (bm e.2.1))
      (scottList (bm e.2.2.1))) = true :=
    closed_pairLit (closed_mono hof4cl (Nat.zero_le 1))
      (closed_mono hln4cl (Nat.zero_le 1))
  have he4cl : closed 0 (aps b4addL
      [aps b4addL [basT, scottList (bm e.2.1)],
       scottList (bm e.2.2.1)]) = true := by
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_b4addL
      | exact hb
      | exact hof4cl
      | exact hln4cl
  have hrsv : closed 0 (p2ResvT sT lcT (aps b4addL
      [aps b4addL [basT, scottList (bm e.2.1)],
       scottList (bm e.2.2.1)])) = true :=
    closed_p2ResvT 0 (closed_mono hs (Nat.zero_le 1))
      (closed_mono hlc (Nat.zero_le 1))
      (closed_mono he4cl (Nat.zero_le 1))
  -- prefix: open + destructure + dispatch
  have s1 := p2Step_open encT sT lcT basT accT recT he hs hlc hb ha hr
  have s2 : LRed (.app recT (p2RecContT encT sT lcT basT accT))
      (aps (p2RecContT encT sT lcT basT accT) [e.1.itT,
        pairLit (scottList (bm e.2.1)) (scottList (bm e.2.2.1))]) :=
    (LRed_app_left hrec).trans
      (pairLit_apply e.1.itT _ _ hitcl holcl)
  have s3 := p2RecCont_apply encT sT lcT basT accT e.1.itT
    (pairLit (scottList (bm e.2.1)) (scottList (bm e.2.2.1)))
    he hs hlc hb ha hitcl holcl
  have s4 : LRed (.app (pairLit (scottList (bm e.2.1))
        (scottList (bm e.2.2.1)))
        (p2OfLnContT encT sT lcT basT accT e.1.itT))
      (aps (p2OfLnContT encT sT lcT basT accT e.1.itT)
        [scottList (bm e.2.1), scottList (bm e.2.2.1)]) :=
    pairLit_apply _ _ _ hof4cl hln4cl
  have s5 := p2OfLn_apply encT sT lcT basT accT e.1.itT
    (scottList (bm e.2.1)) (scottList (bm e.2.2.1))
    he hs hlc hb ha hitcl hof4cl hln4cl
  have s6 : LRed (aps e.1.itT [klL,
        p2DispS encT sT lcT basT accT e.1.itT
          (scottList (bm e.2.1)) (scottList (bm e.2.2.1))])
      (aps (p2DispS encT sT lcT basT accT e.1.itT
          (scottList (bm e.2.1)) (scottList (bm e.2.2.1)))
        [tgT, rrT]) :=
    (LRed_app_left (LRed_app_left hitC)).trans
      (cellLit_apply2 tgT rrT klL _ htgcl hrrcl)
  have s7 := p2Disp_open encT sT lcT basT accT e.1.itT
    (scottList (bm e.2.1)) (scottList (bm e.2.2.1)) tgT rrT
    he hs hlc hb ha hitcl hof4cl hln4cl htgcl hrrcl
  -- eqStr prefix → boolLit
  have hnib : ∀ x ∈ e.1.ns.map nibLit, closed 0 x = true :=
    fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx; exact closed_nibLit _
  have hlen : LRed (aps lenL [tgT])
      (succChain kilL e.1.ns.length) := by
    have h1 := (LRed_app_right htag).trans
      (len_eval (e.1.ns.map nibLit) hnib)
    rw [List.length_map] at h1; exact h1
  have hlencl : closed 0 (aps lenL [tgT]) = true := by
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_lenL, htgcl⟩
  have heq3 := eqStr_eval e.1.ns lblNibs e.1.ns.length (Nat.le_refl _)
    tgT lblL (aps lenL [tgT]) htag lbl_nf hlen htgcl closed_lblL hlencl
  have hsel : LRed (aps eqStrL [tgT, lblL, aps lenL [tgT], accT,
        aps (p2E4ContT encT sT lcT accT e.1.itT)
          [aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
            scottList (bm e.2.2.1)]]])
      (aps (boolLit (decide (e.1.ns = lblNibs)))
        [accT, aps (p2E4ContT encT sT lcT accT e.1.itT)
          [aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
            scottList (bm e.2.2.1)]]]) :=
    LRed_app_left (LRed_app_left heq3)
  have hsel' := hsel.trans (boolLit_sel _ _ _)
  by_cases hns : e.1.ns = lblNibs
  · have hdec : decide (e.1.ns = lblNibs) = true := by
      rw [hns]; decide
    rw [hdec] at hsel'
    have hsem : p2StepSem e acc = acc := by simp [p2StepSem, hns]
    rw [hsem]
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans
      (s6.trans (s7.trans (hsel'.trans hacc)))))))
  · have hdec : decide (e.1.ns = lblNibs) = false :=
      decide_eq_false hns
    rw [hdec] at hsel'
    have hsem : p2StepSem e acc = (bm e.2.2.2).reverse ++ acc := by
      simp [p2StepSem, hns]
    rw [hsem]
    -- insn chain: end4 = B4ADD (B4ADD base of) ln
    have b1 : LRed (aps b4addL [basT, scottList (bm e.2.1)])
        (scottList (bm (resList basB e.2.1 0))) := by
      have h : LRed (aps b4addL [scottList (bm basB),
          scottList (bm e.2.1)])
          (scottList (bm (resList basB e.2.1 0))) :=
        b4add_eval_scott basB e.2.1 (hb4.trans hof4.symm)
      exact (LRed_app_left (LRed_app_right hbas)).trans h
    have b2 : LRed (aps b4addL
        [aps b4addL [basT, scottList (bm e.2.1)],
         scottList (bm e.2.2.1)])
        (scottList (bm (end4Sem basB e.2.1 e.2.2.1))) := by
      have h1 : LRed (aps b4addL
          [scottList (bm (resList basB e.2.1 0)),
           scottList (bm e.2.2.1)])
          (scottList (bm (resList (resList basB e.2.1 0)
            e.2.2.1 0))) :=
        b4add_eval_scott _ _ ((resList_len basB e.2.1 0
          (hb4.trans hof4.symm)).trans (hb4.trans hln4.symm))
      have h0 : LRed (aps b4addL
          [aps b4addL [basT, scottList (bm e.2.1)],
           scottList (bm e.2.2.1)])
          (aps b4addL [scottList (bm (resList basB e.2.1 0)),
            scottList (bm e.2.2.1)]) :=
        LRed_app_left (LRed_app_right b1)
      have h := h0.trans h1
      show LRed _ (scottList (bm (end4Sem basB e.2.1 e.2.2.1)))
      exact h
    have s8 := p2E4_apply encT sT lcT accT e.1.itT
      (aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
        scottList (bm e.2.2.1)])
      he hs hlc ha hitcl he4cl
    have s9 := p2RsvCont_apply encT accT e.1.itT
      (p2ResvT sT lcT (aps b4addL
        [aps b4addL [basT, scottList (bm e.2.1)],
         scottList (bm e.2.2.1)]))
      he ha hitcl hrsv
    have s10 := p2Enc_apply encT accT e.1.itT
      (p2ResvT sT lcT (aps b4addL
        [aps b4addL [basT, scottList (bm e.2.1)],
         scottList (bm e.2.2.1)]))
      he ha hitcl hrsv
    -- fst projection + byte-list fold
    have hbyt : LRed (.app (aps encT [e.1.itT,
          p2ResvT sT lcT (aps b4addL
            [aps b4addL [basT, scottList (bm e.2.1)],
             scottList (bm e.2.2.1)])]) klL)
        (scottList (bm e.2.2.2)) :=
      (LRed_app_left henc).trans
        ((pairLit_fst e.1.byT e.1.lnT hbycl hlncl).trans hby)
    have hfold : LRed (aps foldlL [consRevL,
          .app (aps encT [e.1.itT, p2ResvT sT lcT (aps b4addL
            [aps b4addL [basT, scottList (bm e.2.1)],
             scottList (bm e.2.2.1)])]) klL,
          accT])
        (ggbA consRevL (scottList (bm e.2.2.2)) (scottList acc)) := by
      have h0 : LRed (aps foldlL [consRevL,
          .app (aps encT [e.1.itT, p2ResvT sT lcT (aps b4addL
            [aps b4addL [basT, scottList (bm e.2.1)],
             scottList (bm e.2.2.1)])]) klL,
          accT])
          (aps foldlL [consRevL, scottList (bm e.2.2.2),
            scottList acc]) :=
        (LRed_app_left (LRed_app_right hbyt)).trans
          (LRed_app_right hacc)
      exact h0.trans (foldl_to_ggb _ _ _ closed_consRevL
        (closed_scott_bm _) (closed_scottList haccc))
    have hread : LRed (ggbA consRevL (scottList (bm e.2.2.2))
        (scottList acc))
        ((bm e.2.2.2).foldl (fun a c => cellLit c a)
          (scottList acc)) := by
      show LRed (ggbA stepConsL (scottList (bm e.2.2.2))
        (scottList acc)) _
      exact fold_read _ _ (fun _ hx => closed_bm hx)
        (closed_scottList haccc)
    rw [foldl_cellRev_scott] at hread
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans
      (s6.trans (s7.trans (hsel'.trans (s8.trans (s9.trans
        (s10.trans (hfold.trans hread)))))))))))

/-- `p2StepSem` preserves accumulator-cell closedness. -/
theorem p2StepSem_wf (e : P2Item) (acc : List LTerm)
    (h : ∀ c ∈ acc, closed 0 c = true) :
    ∀ c ∈ p2StepSem e acc, closed 0 c = true := by
  by_cases hns : e.1.ns = lblNibs
  · simp only [p2StepSem, decide_eq_true hns, if_true]
    exact h
  · simp only [p2StepSem, decide_eq_false hns, if_false]
    intro c hc
    simp only [List.mem_append, List.mem_reverse] at hc
    rcases hc with hc | hc
    · exact closed_bm hc
    · exact h c hc

/-- fold-start congruence over prep-entry terms. -/
theorem p2Fold_cong (st : LTerm) : ∀ (ts : List LTerm) (X a : LTerm),
    LRed X a →
    LRed (ts.foldl (fun acc t => aps st [acc, t]) X)
         (ts.foldl (fun acc t => aps st [acc, t]) a) := by
  intro ts; induction ts with
  | nil => intro X a h; exact h
  | cons t ts ih =>
    intro X a h
    exact ih _ _ (LRed_app_left (LRed_app_right h))

/-- entry-term ↔ item correspondence for the pass-2 fold. -/
def p2EntryRel (t : LTerm) (e : P2Item) : Prop :=
  LRed t (p2EntryT e) ∧ closed 0 t = true

/-- the emitted pass-2 fold over prep entries evaluates to the
    semantic `p2StepSem`-fold (accumulator threaded as a Scott-list
    of emitted cells). -/
theorem p2Fold_eval (encT sT lcT basT : LTerm) (basB : B4L)
    (he : closed 0 encT = true) (hs : closed 0 sT = true)
    (hlc : closed 0 lcT = true) (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4)
    {es : List P2Item} {ts : List LTerm}
    (h2 : List.Forall₂ p2EntryRel ts es) :
    (∀ e ∈ es, p2ItmV encT sT lcT basT e) →
    (∀ e ∈ es, e.2.1.length = 4 ∧ e.2.2.1.length = 4) →
    ∀ (acc : List LTerm) (accT : LTerm),
      (∀ c ∈ acc, closed 0 c = true) → closed 0 accT = true →
      LRed accT (scottList acc) →
      LRed (ts.foldl (fun a t =>
            aps (emitStepT encT sT lcT basT) [a, t]) accT)
           (scottList (es.foldl (fun a e => p2StepSem e a) acc)) := by
  induction h2 with
  | nil => intro _ _ acc accT _ _ hacc; exact hacc
  | cons hstep h2' ih =>
    rename_i t e ts' es'
    obtain ⟨he', htcl⟩ := hstep
    intro hV hlen acc accT haccc haccl hacc
    simp only [List.foldl_cons]
    have hVit := hV e List.mem_cons_self
    have hleni := hlen e List.mem_cons_self
    have hVtl : ∀ x ∈ es', p2ItmV encT sT lcT basT x := fun x hx =>
      hV x (List.mem_cons_of_mem _ hx)
    have hlenTl : ∀ x ∈ es', x.2.1.length = 4 ∧
        x.2.2.1.length = 4 := fun x hx =>
      hlen x (List.mem_cons_of_mem _ hx)
    have hstep' := p2_step_eval encT sT lcT basT accT t basB e acc
      he hs hlc hb haccl htcl hbas he' hVit hacc haccc hb4
      hleni.1 hleni.2
    have hwf := p2StepSem_wf e acc haccc
    have hcl' := closed_scottList hwf
    have hcong := p2Fold_cong (emitStepT encT sT lcT basT) ts'
      (aps (emitStepT encT sT lcT basT) [accT, t])
      (scottList (p2StepSem e acc)) hstep'
    exact hcong.trans (ih hVtl hlenTl (p2StepSem e acc)
      (scottList (p2StepSem e acc)) hwf hcl'
      Relation.ReflTransGen.refl)
'''

txt = txt.replace('\nend ISAR', '\n' + block + '\nend ISAR')
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('appended step+fold eval')
