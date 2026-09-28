import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# add closed_conssChain after subst_conssChain_var block (before fragAbs_apply)
old0 = '''/-- `(λt. CONS-chain its t)·rest →* its.foldr cellLit tn`. -/
theorem fragAbs_apply'''
new0 = '''/-- depth-d closedness of a cons-chain. -/
theorem closed_conssChain : ∀ (its : List LTerm) (t : LTerm)
    (d : Nat),
    (∀ c ∈ its, closed d c = true) → closed d t = true →
    closed d (conssChain its t) = true := by
  intro its; induction its with
  | nil => intro t d _ h; exact h
  | cons i is ih =>
    intro t d h ht
    show closed d (aps conssL [i, conssChain is t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨⟨closed_mono closed_conssL (Nat.zero_le d),
            h i (List.mem_cons_self _ _)⟩,
           ih t d (fun c hc => h c (List.mem_cons_of_mem _ hc)) ht⟩

/-- `(λt. CONS-chain its t)·rest →* its.foldr cellLit tn`. -/
theorem fragAbs_apply'''
assert old0 in txt; txt = txt.replace(old0, new0)

# fix psegApp_eval's select steps: h1 already yields the .app form,
# no extra LRed_app_left needed; and fill the some-v case.
old1 = '''    have h1 := boolSel3_eval fuse hfs
    cases fuse
    · show LRed _ ((psegItems false fuel (.fuse a b)).foldr cellLit tn)
      show LRed _ (b.foldr cellLit tn)
      exact (LRed_app_left h1).trans
        (fragAbs_apply b t tn hbc htcl ht htn)
    · show LRed _ (a.foldr cellLit tn)
      exact (LRed_app_left h1).trans
        (fragAbs_apply a t tn hac htcl ht htn)'''
new1 = '''    have h1 := boolSel3_eval fuse hfs
    cases fuse
    · show LRed _ ((psegItems false fuel (.fuse a b)).foldr cellLit tn)
      show LRed _ (b.foldr cellLit tn)
      exact h1.trans (fragAbs_apply b t tn hbc htcl ht htn)
    · show LRed _ (a.foldr cellLit tn)
      exact h1.trans (fragAbs_apply a t tn hac htcl ht htn)'''
assert old1 in txt; txt = txt.replace(old1, new1)

old2 = '''    cases fuel with
    | none =>
      show LRed _ ((psegItems fuse none (.fuelR a)).foldr cellLit tn)
      show LRed _ tn
      have hfuel' : LRed fuelT klL := hfuel
      exact (maybeSelNone_eval hfuel').trans
        (idAbs_apply t tn htcl ht)
    | some v =>
      show LRed _ ((psegItems fuse (some v) (.fuelR a)).foldr
        cellLit tn)
      show LRed _ ((a.map (subst v 1)).foldr cellLit tn)
      have hv : closed 0 v = true := hfjcl v rfl
      have hfuel' : LRed fuelT (.app justL v) := hfuel
      have hfn : closed 0 (.abs (.var 0)) = true := by decide
      have hj : closed 0 (.abs (.abs (conssChain a (.var 0)))) =
          true := by
        simp only [closed]
        exact closed_conssChain?? -- placeholder
      sorry'''
new2 = '''    cases fuel with
    | none =>
      show LRed _ ((psegItems fuse none (.fuelR a)).foldr cellLit tn)
      show LRed _ tn
      have hfuel' : LRed fuelT klL := hfuel
      exact (maybeSelNone_eval hfuel').trans
        (idAbs_apply t tn htcl ht)
    | some v =>
      show LRed _ ((psegItems fuse (some v) (.fuelR a)).foldr
        cellLit tn)
      show LRed _ ((a.map (subst v 1)).foldr cellLit tn)
      have hv : closed 0 v = true := hfjcl v rfl
      have hfuel' : LRed fuelT (.app justL v) := hfuel
      have hfn : closed 0 (.abs (.var 0)) = true := by decide
      have hj : closed 0 (.abs (.abs (conssChain a (.var 0)))) =
          true :=
        closed_conssChain a (.var 0) 2 hcs (by decide)
      exact (maybeSelJust_eval v hv hfn hj hfuel').trans
        ((LRed_app_left (fuelFj_apply a v hv)).trans
          (fragAbs_apply (a.map (subst v 1)) t tn
            (closed_map_subst1 a v hcs hv) htcl ht htn))'''
assert old2 in txt; txt = txt.replace(old2, new2)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
