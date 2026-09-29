import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# 1. consAbs_apply: fix `items`->`its` typo (statement + h1) and use subst_consApp
old0 = '''/-- `(λt. CONS x t)·rest →* cellLit x' rest'` when `x →* x'`. -/
theorem consAbs_apply : ∀ (its : List LTerm) (t tn : LTerm),
    (∀ c ∈ its, closed 0 c = true) → closed 0 t = true →
    LRed t tn → closed 0 tn = true →
    LRed (.app (.abs (aps conssL [conssChain items nilL, .var 0])) t)
         (cellLit (scottList its) tn) := by
  intro its t tn hits htcl ht htn
  have hxc : closed 0 (conssChain its nilL) = true :=
    closed_conssChain its nilL 0 hits closed_nilL
  have h1 : LRed (.app (.abs (aps conssL
      [conssChain items nilL, .var 0])) t)
      (aps conssL [conssChain its nilL, t]) := by
    have hh := LRed_of_hsteps (k := 1)
      (t := .app (.abs (aps conssL [conssChain its nilL, .var 0])) t)
      (u := subst t 0 (aps conssL [conssChain its nilL, .var 0])) rfl
    have hs : subst t 0 (aps conssL
        [conssChain its nilL, .var 0]) =
        aps conssL [conssChain its nilL, t] := by
      show subst t 0 (.app (.app conssL (conssChain its nilL))
        (.var 0)) = (.app (.app conssL (conssChain its nilL)) t)
      simp only [subst,
        subst_of_closed (closed_mono closed_conssL (Nat.zero_le 0)),
        subst_of_closed0 hxc t 0, subst_var_self t htcl]
    rwa [hs] at hh'''
new0 = '''/-- `subst t 0` of `CONS x (.var 0)` conses `x` onto `t`. -/
theorem subst_consApp (x t : LTerm) (hx : closed 0 x = true)
    (ht : closed 0 t = true) :
    subst t 0 (aps conssL [x, .var 0]) = aps conssL [x, t] := by
  show subst t 0 (.app (.app conssL x) (.var 0)) =
    (.app (.app conssL x) t)
  rw [show subst t 0 (.app (.app conssL x) (.var 0)) =
       .app (subst t 0 (.app conssL x)) (subst t 0 (.var 0)) from rfl]
  rw [show subst t 0 (.app conssL x) =
       .app (subst t 0 conssL) (subst t 0 x) from rfl]
  rw [subst_of_closed (closed_mono closed_conssL (Nat.zero_le 0)),
      subst_of_closed0 hx t 0, subst_var_self t ht]

/-- `(λt. CONS x t)·rest →* cellLit x' rest'` when `x →* x'`. -/
theorem consAbs_apply : ∀ (its : List LTerm) (t tn : LTerm),
    (∀ c ∈ its, closed 0 c = true) → closed 0 t = true →
    LRed t tn → closed 0 tn = true →
    LRed (.app (.abs (aps conssL [conssChain its nilL, .var 0])) t)
         (cellLit (scottList its) tn) := by
  intro its t tn hits htcl ht htn
  have hxc : closed 0 (conssChain its nilL) = true :=
    closed_conssChain its nilL 0 hits closed_nilL
  have h1 : LRed (.app (.abs (aps conssL
      [conssChain its nilL, .var 0])) t)
      (aps conssL [conssChain its nilL, t]) := by
    have hh := LRed_of_hsteps (k := 1)
      (t := .app (.abs (aps conssL [conssChain its nilL, .var 0])) t)
      (u := subst t 0 (aps conssL [conssChain its nilL, .var 0])) rfl
    rwa [subst_consApp (conssChain its nilL) t hxc htcl] at hh'''
assert old0 in txt, "old0"
txt = txt.replace(old0, new0)

# 2. closed_psegApp fuse: fix assoc nesting
old1 = '''    refine ⟨⟨hfs, ?_, ?_⟩, htcl⟩'''
assert old1 in txt, "old1"
txt = txt.replace(old1, '''    refine ⟨⟨⟨hfs, ?_⟩, ?_⟩, htcl⟩''')

# 3. closed_psegApp fuelR: fix assoc nesting
old2 = '''    refine ⟨⟨hfu, by decide, ?_⟩, htcl⟩'''
assert old2 in txt, "old2"
txt = txt.replace(old2, '''    refine ⟨⟨⟨hfu, by decide⟩, ?_⟩, htcl⟩''')

# 4. closed_psegSem: fix `show ... at hci` misuse
old3 = '''  cases s with
  | cell it =>
    show c ∈ [it] at hci
    simp only [List.mem_singleton] at hci
    rw [hci]; exact hsc
  | fuse a b =>
    obtain ⟨hac, hbc⟩ := hsc
    cases fuse
    · exact hbc c (by
        show c ∈ (psegItems false fuel (.fuse a b)) at hci
        exact hci)
    · exact hac c (by
        show c ∈ (psegItems true fuel (.fuse a b)) at hci
        exact hci)
  | fuelR a =>
    cases fuel with
    | none => nomatch hci
    | some v =>
      exact (closed_map_subst1 a v hsc (hfv v rfl)) c (by
        show c ∈ (psegItems fuse (some v) (.fuelR a)) at hci
        exact hci)'''
new3 = '''  cases s with
  | cell it =>
    have hci' : c ∈ [it] := hci
    simp only [List.mem_singleton] at hci'
    rw [hci']; exact hsc
  | fuse a b =>
    obtain ⟨hac, hbc⟩ := hsc
    cases fuse
    · exact hbc c (show c ∈ b from hci)
    · exact hac c (show c ∈ a from hci)
  | fuelR a =>
    cases fuel with
    | none => nomatch hci
    | some v =>
      exact (closed_map_subst1 a v hsc (hfv v rfl)) c
        (show c ∈ a.map (subst v 1) from hci)'''
assert old3 in txt, "old3"
txt = txt.replace(old3, new3)

# 5. closed_osegApp stS/bDS: fix assoc nesting
old4 = '''    refine ⟨⟨hfs, ?_, by simp only [closed]; omega⟩, htcl⟩
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨closed_mono closed_conssL (Nat.zero_le (d + 1)), ?_,
      by simp only [closed]; omega⟩
    exact closed_conssChain items nilL (d + 1)
      (fun c hc => closed_mono (hcs c hc :
        closed 0 c = true) (Nat.zero_le (d + 1)))
      (closed_mono closed_nilL (Nat.zero_le (d + 1)))
  | bDS items =>'''
new4 = '''    refine ⟨⟨⟨hfs, ?_⟩, by simp only [closed]; omega⟩, htcl⟩
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨⟨closed_mono closed_conssL (Nat.zero_le (d + 1)), ?_⟩,
      by simp only [closed]; omega⟩
    exact closed_conssChain items nilL (d + 1)
      (fun c hc => closed_mono (hcs c hc :
        closed 0 c = true) (Nat.zero_le (d + 1)))
      (closed_mono closed_nilL (Nat.zero_le (d + 1)))
  | bDS items =>'''
assert old4 in txt, "old4"
txt = txt.replace(old4, new4)

old5 = '''    refine ⟨⟨hfs, by simp only [closed]; omega, ?_⟩, htcl⟩
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨closed_mono closed_conssL (Nat.zero_le (d + 1)), ?_,
      by simp only [closed]; omega⟩
    exact closed_conssChain items nilL (d + 1)
      (fun c hc => closed_mono (hcs c hc :
        closed 0 c = true) (Nat.zero_le (d + 1)))
      (closed_mono closed_nilL (Nat.zero_le (d + 1)))

/-- the folded outer chain stays closed. -/'''
new5 = '''    refine ⟨⟨⟨hfs, by simp only [closed]; omega⟩, ?_⟩, htcl⟩
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨⟨closed_mono closed_conssL (Nat.zero_le (d + 1)), ?_⟩,
      by simp only [closed]; omega⟩
    exact closed_conssChain items nilL (d + 1)
      (fun c hc => closed_mono (hcs c hc :
        closed 0 c = true) (Nat.zero_le (d + 1)))
      (closed_mono closed_nilL (Nat.zero_le (d + 1)))

/-- the folded outer chain stays closed. -/'''
assert old5 in txt, "old5"
txt = txt.replace(old5, new5)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
