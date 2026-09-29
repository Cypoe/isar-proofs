import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

# remove the broken block I just appended (alookFold_mem .. p2Resv_eval)
i = txt.index('/-- the last-match fold only returns rows present in the table')
txt = txt[:i].rstrip() + '\n\nend ISAR\n'

block = '''
/-- the last-match fold only returns rows present in the table
    (or the initial acc). -/
theorem alookFold_mem (key : List (Fin 16)) (kvs : List P2Row)
    (a : Option P2Row) (kv : P2Row)
    (h : kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv else acc) a = some kv) :
    kv ∈ kvs ∨ a = some kv := by
  induction kvs generalizing a with
  | nil =>
    simp only [List.foldl_nil] at h
    exact Or.inr h
  | cons kv' kvs ih =>
    simp only [List.foldl_cons, List.mem_cons] at h ⊢
    cases hd : decide (key = kv'.1) with
    | true =>
      have h' := ih (some kv') (by simpa [hd] using h)
      rcases h' with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inl (Or.inl (Option.some.inj h').symm)
    | false =>
      have h' := ih a (by simpa [hd] using h)
      rcases h' with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

/-- a row occurring in a `p2RowRel`-aligned table has a row-relation
    witness entry. -/
theorem p2RowRel_of_mem {es : List LTerm} {kvs : List P2Row}
    (h2 : List.Forall₂ p2RowRel es kvs) {kv : P2Row}
    (hk : kv ∈ kvs) : ∃ e ∈ es, p2RowRel e kv := by
  induction h2 with
  | nil => exact absurd hk List.not_mem_nil
  | cons hr _ ih =>
    rw [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨e, he, hr'⟩ := ih hk
      exact ⟨e, List.mem_cons_of_mem _ he, hr'⟩

/-- **`p2Resv_eval`**: the emitted resolver `λnm. (ALOOK sym nm)
    ((ALOOK loc nm) (B4SUB b4z e4) (λlv. B4SUB lv e4))
    (λsv. B4SUB sv e4)` — symbol hit shadows the local table, a hit
    subtracts `end4` (rel32), a miss falls back to zero bytes. -/
theorem p2Resv_eval (symRows locRows : List P2Row)
    (nm : List (Fin 16)) (e4B : B4L)
    (nmT e4T sT lcT : LTerm)
    (hnmT : LRed nmT (scottList (nm.map nibLit)))
    (hnmcl : closed 0 nmT = true)
    (he4T : LRed e4T (scottList (bm e4B))) (he4cl : closed 0 e4T = true)
    (he4len : e4B.length = 4)
    (symEs : List LTerm) (hsym2 : List.Forall₂ p2RowRel symEs symRows)
    (hsymes : ∀ e ∈ symEs, closed 0 e = true)
    (hsT : LRed sT (scottList symEs)) (hscl : closed 0 sT = true)
    (hsymlen : ∀ kv ∈ symRows, kv.2.1.length = 4)
    (locEs : List LTerm) (hloc2 : List.Forall₂ p2RowRel locEs locRows)
    (hloces : ∀ e ∈ locEs, closed 0 e = true)
    (hlcT : LRed lcT (scottList locEs)) (hlccl : closed 0 lcT = true)
    (hloclen : ∀ kv ∈ locRows, kv.2.1.length = 4) :
    LRed (aps (p2ResvT sT lcT e4T) [nmT])
      (scottList (bm (resvSem
        (symRows.map (fun kv => (kv.1, kv.2.1)))
        (locRows.map (fun kv => (kv.1, kv.2.1))) nm e4B))) := by
  have hJsv : closed 0 (.abs (aps b4subL [.var 0, e4T])) = true := by
    simp only [closed, aps, List.foldl, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_b4subL
      | exact closed_mono he4cl (Nat.zero_le _)
  have hZ : closed 0 (aps b4subL [b4zL, e4T]) = true := by
    simp only [closed, aps, List.foldl, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_b4subL
      | exact closed_b4zL
      | exact closed_mono he4cl (Nat.zero_le _)
  have hInner : closed 0 (aps alookL
      [lcT, nmT, aps b4subL [b4zL, e4T],
       .abs (aps b4subL [.var 0, e4T])]) = true := by
    simp only [closed, aps, List.foldl, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_alookL
      | exact hlccl
      | exact hnmcl
      | exact hZ
      | exact hJsv
  have h1 := p2Resv_apply sT lcT e4T nmT hscl hlccl he4cl hnmcl
  have h2 := alook_eval_lit nm nmT hnmT hnmcl symEs symRows hsym2
    hsymes sT hsT hscl
  have h3 : LRed (aps alookL
        [sT, nmT,
         aps alookL
           [lcT, nmT, aps b4subL [b4zL, e4T],
            .abs (aps b4subL [.var 0, e4T])],
         .abs (aps b4subL [.var 0, e4T])])
      (aps (optionLit (Option.map (·.2.2)
          (symRows.foldl (fun acc kv =>
            if decide (nm = kv.1) then some kv else acc) none)))
        [aps alookL
           [lcT, nmT, aps b4subL [b4zL, e4T],
            .abs (aps b4subL [.var 0, e4T])],
         .abs (aps b4subL [.var 0, e4T])]) :=
    LRed_app_left (LRed_app_left h2)
  have hopt : ∀ v, Option.map (·.2.2)
        (symRows.foldl (fun acc kv =>
          if decide (nm = kv.1) then some kv else acc) none)
        = some v → closed 0 v = true := by
    intro v hv
    cases hfo : symRows.foldl (fun acc kv =>
        if decide (nm = kv.1) then some kv else acc) none with
    | none =>
      rw [hfo] at hv
      simp at hv
    | some kv =>
      rw [hfo] at hv
      simp only [Option.map] at hv
      obtain rfl := Option.some.inj hv
      have hmem : kv ∈ symRows :=
        (alookFold_mem nm symRows none kv hfo).elim id
          (fun h => nomatch h)
      obtain ⟨_, _, _, _, _, _, _, _, hvcl⟩ :=
        p2RowRel_of_mem hsym2 hmem
      exact hvcl
  have h4 := optionLit_apply2
    (Option.map (·.2.2) (symRows.foldl (fun acc kv =>
      if decide (nm = kv.1) then some kv else acc) none))
    (aps alookL [lcT, nmT, aps b4subL [b4zL, e4T],
      .abs (aps b4subL [.var 0, e4T])])
    (.abs (aps b4subL [.var 0, e4T])) hopt hInner hJsv
  have hb4z : LRed b4zL (scottList (bm b4zeroBytes)) := by
    show LRed b4zL (scottList (List.replicate 4 (byteLit 0 0)))
    exact b4z_nf
  unfold resvSem
  simp only [← alookSem_proj nm symRows]
  cases hfo : symRows.foldl (fun acc kv =>
      if decide (nm = kv.1) then some kv else acc) none with
  | some kv =>
    rw [hfo] at h4
    simp only [Option.map] at h4
    show LRed _ (scottList (bm (subResList kv.2.1 e4B 1)))
    have hmem : kv ∈ symRows :=
      (alookFold_mem nm symRows none kv hfo).elim id
        (fun h => nomatch h)
    obtain ⟨_, _, _, _, _, hvT, _, _, hvcl⟩ :=
      p2RowRel_of_mem hsym2 hmem
    have hsub : LRed (aps b4subL [kv.2.2, e4T])
        (scottList (bm (subResList kv.2.1 e4B 1))) := by
      have hcong : LRed (aps b4subL [kv.2.2, e4T])
          (aps b4subL [scottList (bm kv.2.1),
                       scottList (bm e4B)]) :=
        LRed_app (LRed_app Relation.ReflTransGen.refl hvT) he4T
      exact hcong.trans (b4sub_eval_scott kv.2.1 e4B
        ((hsymlen kv hmem).trans he4len.symm))
    have hcont := p2SubCont_apply e4T kv.2.2 he4cl hvcl
    exact h1.trans (h3.trans (h4.trans (hcont.trans hsub)))
  | none =>
    rw [hfo] at h4
    simp only [Option.map] at h4
    have h5 := alook_eval_lit nm nmT hnmT hnmcl locEs locRows hloc2
      hloces lcT hlcT hlccl
    have h6 : LRed (aps alookL
          [lcT, nmT, aps b4subL [b4zL, e4T],
           .abs (aps b4subL [.var 0, e4T])])
        (aps (optionLit (Option.map (·.2.2)
            (locRows.foldl (fun acc kv =>
              if decide (nm = kv.1) then some kv else acc) none)))
          [aps b4subL [b4zL, e4T],
           .abs (aps b4subL [.var 0, e4T])]) :=
      LRed_app_left (LRed_app_left h5)
    have hoptL : ∀ v, Option.map (·.2.2)
          (locRows.foldl (fun acc kv =>
            if decide (nm = kv.1) then some kv else acc) none)
          = some v → closed 0 v = true := by
      intro v hv
      cases hfo2 : locRows.foldl (fun acc kv =>
          if decide (nm = kv.1) then some kv else acc) none with
      | none =>
        rw [hfo2] at hv
        simp at hv
      | some kv =>
        rw [hfo2] at hv
        simp only [Option.map] at hv
        obtain rfl := Option.some.inj hv
        have hmem : kv ∈ locRows :=
          (alookFold_mem nm locRows none kv hfo2).elim id
            (fun h => nomatch h)
        obtain ⟨_, _, _, _, _, _, _, _, hvcl⟩ :=
          p2RowRel_of_mem hloc2 hmem
        exact hvcl
    have h7 := optionLit_apply2
      (Option.map (·.2.2) (locRows.foldl (fun acc kv =>
        if decide (nm = kv.1) then some kv else acc) none))
      (aps b4subL [b4zL, e4T])
      (.abs (aps b4subL [.var 0, e4T])) hoptL hZ hJsv
    simp only [← alookSem_proj nm locRows]
    cases hfo2 : locRows.foldl (fun acc kv =>
        if decide (nm = kv.1) then some kv else acc) none with
    | some kv =>
      rw [hfo2] at h7
      simp only [Option.map] at h7
      show LRed _ (scottList (bm (subResList kv.2.1 e4B 1)))
      have hmem : kv ∈ locRows :=
        (alookFold_mem nm locRows none kv hfo2).elim id
          (fun h => nomatch h)
      obtain ⟨_, _, _, _, _, hvT, _, _, hvcl⟩ :=
        p2RowRel_of_mem hloc2 hmem
      have hsub : LRed (aps b4subL [kv.2.2, e4T])
          (scottList (bm (subResList kv.2.1 e4B 1))) := by
        have hcong : LRed (aps b4subL [kv.2.2, e4T])
            (aps b4subL [scottList (bm kv.2.1),
                         scottList (bm e4B)]) :=
          LRed_app (LRed_app Relation.ReflTransGen.refl hvT) he4T
        exact hcong.trans (b4sub_eval_scott kv.2.1 e4B
          ((hloclen kv hmem).trans he4len.symm))
      have hcont := p2SubCont_apply e4T kv.2.2 he4cl hvcl
      exact h1.trans (h3.trans (h4.trans (h6.trans (h7.trans
        (hcont.trans hsub)))))
    | none =>
      rw [hfo2] at h7
      simp only [Option.map] at h7
      show LRed _ (scottList (bm (subResList b4zeroBytes e4B 1)))
      have hcong : LRed (aps b4subL [b4zL, e4T])
          (aps b4subL [scottList (bm b4zeroBytes),
                       scottList (bm e4B)]) :=
        LRed_app (LRed_app Relation.ReflTransGen.refl hb4z) he4T
      have hsub := hcong.trans (b4sub_eval_scott b4zeroBytes e4B
        (by simp [b4zeroBytes, he4len]))
      exact h1.trans (h3.trans (h4.trans (h6.trans (h7.trans hsub))))
'''

txt = txt.replace('\nend ISAR', '\n' + block + '\nend ISAR')
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('rewrote')
