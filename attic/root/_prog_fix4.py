import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# psegClosed: fuelR items carry closed-2 AND closed-0-after-subst
old0 = '''/-- per-seg closedness side-condition. -/
def psegClosed (s : PSeg) : Prop :=
  match s with
  | .cell it => closed 0 it = true
  | .fuse a b => (∀ c ∈ a, closed 0 c = true) ∧
      (∀ c ∈ b, closed 0 c = true)
  | .fuelR a => ∀ c ∈ a, closed 2 c = true'''
new0 = '''/-- per-seg closedness side-condition: fuelR items are `.var 1`-open
    (the `fv` slot) — closed at depth 2, and `subst v 1` makes them
    closed-0 for closed `v`. -/
def psegClosed (s : PSeg) : Prop :=
  match s with
  | .cell it => closed 0 it = true
  | .fuse a b => (∀ c ∈ a, closed 0 c = true) ∧
      (∀ c ∈ b, closed 0 c = true)
  | .fuelR a => ∀ c ∈ a, closed 2 c = true ∧
      (∀ v : LTerm, closed 0 v = true →
        closed 0 (subst v 1 c) = true)'''
assert old0 in txt; txt = txt.replace(old0, new0)

old1 = '''/-- fuel-just items with `.var 1` splice-slots are closed at depth 2
    and become closed-0 after the `subst v 1`. -/
theorem closed_map_subst1 : ∀ (a : List LTerm) (v : LTerm),
    (∀ c ∈ a, closed 2 c = true) → closed 0 v = true →
    ∀ c ∈ a.map (subst v 1), closed 0 c = true := by
  intro a v ha hv c hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  exact closed_subst x v 1 (ha x hx) hv'''
new1 = '''/-- fuel-just items become closed-0 after `subst v 1`. -/
theorem closed_map_subst1 : ∀ (a : List LTerm) (v : LTerm),
    (∀ c ∈ a, closed 2 c = true ∧
      (∀ v : LTerm, closed 0 v = true →
        closed 0 (subst v 1 c) = true)) →
    closed 0 v = true →
    ∀ c ∈ a.map (subst v 1), closed 0 c = true := by
  intro a v ha hv c hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  exact (ha x hx).2 v hv'''
assert old1 in txt; txt = txt.replace(old1, new1)

# fuelFj_apply: annotate .abs in the show
old2 = '''  have hs : subst v 0 (.abs (conssChain a (.var 0))) =
      .abs (conssChain (a.map (subst v 1)) (.var 0)) := by
    show .abs (subst v 1 (conssChain a (.var 0))) = _
    rw [subst_conssChain]
    congr 1
    simp only [subst]
    rw [if_pos (by decide : 0 < 1)]'''
new2 = '''  have hs : subst v 0 (.abs (conssChain a (.var 0))) =
      .abs (conssChain (a.map (subst v 1)) (.var 0)) := by
    show (.abs (subst v 1 (conssChain a (.var 0))) : LTerm) = _
    rw [subst_conssChain]
    congr 1
    simp only [subst]
    rw [if_pos (by decide : 0 < 1)]'''
assert old2 in txt; txt = txt.replace(old2, new2)

# boolSel3_eval: pin implicits via typed have
old3 = '''    have h1 := boolSel3_eval fuse hfs
    cases fuse
    · show LRed _ ((psegItems false fuel (.fuse a b)).foldr cellLit tn)
      show LRed _ (b.foldr cellLit tn)
      exact h1.trans (fragAbs_apply b t tn hbc htcl ht htn)
    · show LRed _ (a.foldr cellLit tn)
      exact h1.trans (fragAbs_apply a t tn hac htcl ht htn)'''
new3 = '''    have h1 : LRed (aps fsT
        [.abs (conssChain a (.var 0)),
         .abs (conssChain b (.var 0)), t])
        (.app (if fuse then .abs (conssChain a (.var 0))
          else .abs (conssChain b (.var 0))) t) :=
      boolSel3_eval fuse hfs
    cases fuse
    · show LRed _ ((psegItems false fuel (.fuse a b)).foldr cellLit tn)
      show LRed _ (b.foldr cellLit tn)
      exact h1.trans (fragAbs_apply b t tn hbc htcl ht htn)
    · show LRed _ (a.foldr cellLit tn)
      exact h1.trans (fragAbs_apply a t tn hac htcl ht htn)'''
assert old3 in txt; txt = txt.replace(old3, new3)

# fuelR: unpack hcs pair; hj via .1; closed_map via .2
old4 = '''      have hv : closed 0 v = true := hfjcl v rfl
      have hfuel' : LRed fuelT (.app justL v) := hfuel
      have hfn : closed 0 (.abs (.var 0)) = true := by decide
      have hj : closed 0 (.abs (.abs (conssChain a (.var 0)))) =
          true :=
        closed_conssChain a (.var 0) 2 hcs (by decide)
      exact (maybeSelJust_eval v hv hfn hj hfuel').trans
        ((LRed_app_left (fuelFj_apply a v hv)).trans
          (fragAbs_apply (a.map (subst v 1)) t tn
            (closed_map_subst1 a v hcs hv) htcl ht htn))'''
new4 = '''      have hv : closed 0 v = true := hfjcl v rfl
      have hfuel' : LRed fuelT (.app justL v) := hfuel
      have hfn : closed 0 (.abs (.var 0)) = true := by decide
      have hj : closed 0 (.abs (.abs (conssChain a (.var 0)))) =
          true :=
        closed_conssChain a (.var 0) 2
          (fun c hc => (hcs c hc).1) (by decide)
      have hsel : LRed (aps fuelT
          [.abs (.var 0),
           .abs (.abs (conssChain a (.var 0))), t])
          (.app (.app (.abs (.abs (conssChain a (.var 0)))) v) t) :=
        maybeSelJust_eval v hv hfn hj hfuel'
      exact hsel.trans
        ((LRed_app_left (fuelFj_apply a v hv)).trans
          (fragAbs_apply (a.map (subst v 1)) t tn
            (closed_map_subst1 a v hcs hv) htcl ht htn))'''
assert old4 in txt; txt = txt.replace(old4, new4)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
