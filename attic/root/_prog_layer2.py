import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

block = '''
/-- `psegChain` closedness: the folded term is closed when the
    segments and tail are. -/
theorem closed_psegApp (fsT fuelT : LTerm) (d : Nat)
    (hfs : closed d fsT = true) (hfu : closed d fuelT = true) :
    ∀ (s : PSeg) (t : LTerm),
      psegClosed s → closed d t = true →
      closed d (psegApp fsT fuelT s t) = true := by
  intro s t hcs htcl
  cases s with
  | cell it =>
    show closed d (aps conssL [it, t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨⟨closed_mono closed_conssL (Nat.zero_le d),
            closed_mono hcs (Nat.zero_le d)⟩, htcl⟩
  | fuse a b =>
    obtain ⟨hac, hbc⟩ := hcs
    show closed d (aps fsT
        [.abs (conssChain a (.var 0)),
         .abs (conssChain b (.var 0)), t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨⟨⟨hfs, ?_, ?_⟩, htcl⟩⟩ <;> exact closed_conssChain _
      (.var 0) (d + 1)
      (fun c hc => closed_mono
        ((by first | exact hac c hc | exact hbc c hc) :
          closed 0 c = true) (Nat.zero_le (d + 1)))
      (by decide)
  | fuelR a =>
    show closed d (aps fuelT
        [.abs (.var 0),
         .abs (.abs (conssChain a (.var 0))), t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨⟨⟨hfu, by decide, ?_⟩, htcl⟩⟩
    exact closed_conssChain a (.var 0) (d + 2)
      (fun c hc => closed_mono ((hcs c hc).1 :
        closed 2 c = true) (by omega)) (by decide)

/-- the folded chain stays closed. -/
theorem closed_psegChain (fsT fuelT : LTerm)
    (hfs : closed 0 fsT = true) (hfu : closed 0 fuelT = true) :
    ∀ (segs : List PSeg) (t : LTerm),
      (∀ s ∈ segs, psegClosed s) → closed 0 t = true →
      closed 0 (psegChain fsT fuelT segs t) = true := by
  intro segs; induction segs with
  | nil => intro t _ h; exact h
  | cons s ss ih =>
    intro t hcs htcl
    show closed 0 (psegApp fsT fuelT s (psegChain fsT fuelT ss t)) =
        true
    exact closed_psegApp fsT fuelT 0 hfs hfu s _
      (hcs s List.mem_cons_self)
      (ih t (fun s' hs' => hcs s' (List.mem_cons_of_mem _ hs')) htcl)

/-- semantic frag items are closed under `psegClosed` + closed fuel
    payload. -/
theorem closed_psegSem : ∀ (segs : List PSeg)
    (fuse : Bool) (fuel : Option LTerm),
    (∀ s ∈ segs, psegClosed s) →
    (∀ v ∈ fuel, closed 0 v = true) →
    ∀ c ∈ psegSem fuse fuel segs, closed 0 c = true := by
  intro segs fuse fuel hcs hfv c hc
  obtain ⟨s, hs, hci⟩ := List.mem_flatMap.mp hc
  have hsc := hcs s hs
  cases s with
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
        exact hci)

/-- fragment-chain eval: `psegChain segs rest` folds the fragment's
    emitted items onto `rest`'s normal form. -/
theorem psegChain_eval (fsT fuelT : LTerm)
    (fuse : Bool) (fuel : Option LTerm)
    (hfs : LRed fsT (boolLit fuse))
    (hfuel : LRed fuelT (optionLit fuel))
    (hfjcl : ∀ v ∈ fuel, closed 0 v = true)
    (hfscl : closed 0 fsT = true) (hfucl : closed 0 fuelT = true) :
    ∀ (segs : List PSeg) (t tn : LTerm),
      (∀ s ∈ segs, psegClosed s) → closed 0 t = true →
      LRed t tn → closed 0 tn = true →
      LRed (psegChain fsT fuelT segs t)
           ((psegSem fuse fuel segs).foldr cellLit tn) := by
  intro segs; induction segs with
  | nil => intro t tn _ _ ht _; exact ht
  | cons s ss ih =>
    intro t tn hcs htcl ht htn
    show LRed (psegApp fsT fuelT s (psegChain fsT fuelT ss t)) _
    have hss := fun s' hs' => hcs s' (List.mem_cons_of_mem _ hs')
    have hinner := ih t tn hss htcl ht htn
    have hich : closed 0 ((psegSem fuse fuel ss).foldr cellLit tn) =
        true :=
      closed_foldr_cellLit _ tn (closed_psegSem ss fuse fuel hss hfjcl)
        htn
    have htcl' : closed 0 (psegChain fsT fuelT ss t) = true :=
      closed_psegChain fsT fuelT hfscl hfucl ss t hss htcl
    have hstep := psegApp_eval fsT fuelT fuse fuel hfs hfuel hfjcl
      s (psegChain fsT fuelT ss t)
      ((psegSem fuse fuel ss).foldr cellLit tn)
      (hcs s List.mem_cons_self) htcl' hinner hich
    show LRed _ ((psegSem fuse fuel (s :: ss)).foldr cellLit tn)
    show LRed _ (((psegItems fuse fuel s) ++
      (psegSem fuse fuel ss)).foldr cellLit tn)
    rw [List.foldr_append]
    exact hstep

/-- outer spine segment: a whole routine fragment (one outer cell),
    or a fuse_s-conditional whole fragment. -/
inductive OSeg where
  | frag : List PSeg → OSeg
  | stS : List LTerm → OSeg
  | bDS : List LTerm → OSeg

/-- outer segment applied to a tail term. -/
def osegApp (fsT fuelT : LTerm) (s : OSeg) (t : LTerm) : LTerm :=
  match s with
  | .frag segs => aps conssL
      [psegChain fsT fuelT segs nilL, t]
  | .stS items => aps fsT
      [.abs (aps conssL [conssChain items nilL, .var 0]),
       .abs (.var 0), t]
  | .bDS items => aps fsT
      [.abs (.var 0),
       .abs (aps conssL [conssChain items nilL, .var 0]), t]

/-- per-oseg semantic cells: the fragment-list cells the segment
    contributes to the outer list. -/
def osegCells (fuse : Bool) (fuel : Option LTerm) (s : OSeg) :
    List LTerm :=
  match s with
  | .frag segs => [scottList (psegSem fuse fuel segs)]
  | .stS items => if fuse then [scottList items] else []
  | .bDS items => if fuse then [] else [scottList items]

/-- per-oseg closedness. -/
def osegClosed (s : OSeg) : Prop :=
  match s with
  | .frag segs => ∀ s ∈ segs, psegClosed s
  | .stS items | .bDS items => ∀ c ∈ items, closed 0 c = true

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
    have hs : subst t 0 (aps conssL
        [conssChain its nilL, .var 0]) =
        aps conssL [conssChain its nilL, t] := by
      show subst t 0 (.app (.app conssL (conssChain its nilL))
        (.var 0)) = (.app (.app conssL (conssChain its nilL)) t)
      simp only [subst,
        subst_of_closed (closed_mono closed_conssL (Nat.zero_le 0)),
        subst_of_closed0 hxc t 0, subst_var_self t htcl]
    rwa [hs] at hh
  have hx : LRed (conssChain its nilL) (scottList its) :=
    conssChain_eval its nilL nilL hits Relation.ReflTransGen.refl
      closed_nilL
  have hsc : closed 0 (scottList its) = true :=
    closed_scottList hits
  exact h1.trans (conssCell_nf hx ht hsc htn)

/-- outer-seg eval: `osegApp s rest` folds the segment's semantic
    cells onto `rest`'s normal form. -/
theorem osegApp_eval (fsT fuelT : LTerm)
    (fuse : Bool) (fuel : Option LTerm)
    (hfs : LRed fsT (boolLit fuse))
    (hfuel : LRed fuelT (optionLit fuel))
    (hfjcl : ∀ v ∈ fuel, closed 0 v = true)
    (hfscl : closed 0 fsT = true) (hfucl : closed 0 fuelT = true) :
    ∀ (s : OSeg) (t tn : LTerm),
      osegClosed s → closed 0 t = true → LRed t tn →
      closed 0 tn = true →
      LRed (osegApp fsT fuelT s t)
           ((osegCells fuse fuel s).foldr cellLit tn) := by
  intro s t tn hcs htcl ht htn
  cases s with
  | frag segs =>
    show LRed (aps conssL [psegChain fsT fuelT segs nilL, t])
      ((osegCells fuse fuel (.frag segs)).foldr cellLit tn)
    show LRed _ ([scottList (psegSem fuse fuel segs)].foldr cellLit tn)
    rw [List.foldr_cons, List.foldr_nil]
    have hfrag := psegChain_eval fsT fuelT fuse fuel hfs hfuel hfjcl
      hfscl hfucl segs nilL nilL hcs closed_nilL
      Relation.ReflTransGen.refl closed_nilL
    have hsc : closed 0 (scottList (psegSem fuse fuel segs)) = true :=
      closed_scottList (closed_psegSem segs fuse fuel hcs hfjcl)
    exact conssCell_nf hfrag ht hsc htn
  | stS items =>
    show LRed (aps fsT
        [.abs (aps conssL [conssChain items nilL, .var 0]),
         .abs (.var 0), t]) _
    have h1 : LRed (aps fsT
        [.abs (aps conssL [conssChain items nilL, .var 0]),
         .abs (.var 0), t])
        (.app (if fuse
          then .abs (aps conssL [conssChain items nilL, .var 0])
          else .abs (.var 0)) t) := boolSel3_eval fuse hfs
    cases fuse
    · show LRed _ ((osegCells false fuel (.stS items)).foldr
        cellLit tn)
      show LRed _ tn
      exact h1.trans (idAbs_apply t tn htcl ht)
    · show LRed _ ((osegCells true fuel (.stS items)).foldr
        cellLit tn)
      show LRed _ ([scottList items].foldr cellLit tn)
      rw [List.foldr_cons, List.foldr_nil]
      exact h1.trans (consAbs_apply items t tn hcs htcl ht htn)
  | bDS items =>
    show LRed (aps fsT
        [.abs (.var 0),
         .abs (aps conssL [conssChain items nilL, .var 0]), t]) _
    have h1 : LRed (aps fsT
        [.abs (.var 0),
         .abs (aps conssL [conssChain items nilL, .var 0]), t])
        (.app (if fuse then .abs (.var 0)
          else .abs (aps conssL [conssChain items nilL, .var 0])) t) :=
      boolSel3_eval fuse hfs
    cases fuse
    · show LRed _ ((osegCells false fuel (.bDS items)).foldr
        cellLit tn)
      show LRed _ ([scottList items].foldr cellLit tn)
      rw [List.foldr_cons, List.foldr_nil]
      exact h1.trans (consAbs_apply items t tn hcs htcl ht htn)
    · show LRed _ ((osegCells true fuel (.bDS items)).foldr
        cellLit tn)
      show LRed _ tn
      exact h1.trans (idAbs_apply t tn htcl ht)

/-- the outer spine fold: the emitted program body onto tail `t`. -/
def osegChain (fsT fuelT : LTerm) (segs : List OSeg) (t : LTerm) :
    LTerm :=
  segs.foldr (fun s acc => osegApp fsT fuelT s acc) t

/-- program semantics: the fragment-list cells. -/
def progSem (fuse : Bool) (fuel : Option LTerm) (segs : List OSeg) :
    List LTerm :=
  segs.flatMap (osegCells fuse fuel)

/-- `osegChain` closedness. -/
theorem closed_osegApp (fsT fuelT : LTerm) (d : Nat)
    (hfs : closed d fsT = true) (hfu : closed d fuelT = true) :
    ∀ (s : OSeg) (t : LTerm),
      osegClosed s → closed d t = true →
      closed d (osegApp fsT fuelT s t) = true := by
  intro s t hcs htcl
  cases s with
  | frag segs =>
    show closed d (aps conssL
        [psegChain fsT fuelT segs nilL, t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨⟨closed_mono closed_conssL (Nat.zero_le d),
            ?_⟩, htcl⟩
    exact closed_psegChain fsT fuelT
      (closed_mono hfs (Nat.zero_le 0))
      (closed_mono hfu (Nat.zero_le 0)) segs nilL hcs closed_nilL
  | stS items =>
    show closed d (aps fsT
        [.abs (aps conssL [conssChain items nilL, .var 0]),
         .abs (.var 0), t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨⟨⟨hfs, ?_, by decide⟩, htcl⟩⟩
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨⟨closed_mono closed_conssL (Nat.zero_le (d + 1)),
            ?_⟩, by decide⟩
    exact closed_conssChain items nilL (d + 1)
      (fun c hc => closed_mono (hcs c hc :
        closed 0 c = true) (Nat.zero_le (d + 1)))
      (closed_mono closed_nilL (Nat.zero_le (d + 1)))
  | bDS items =>
    show closed d (aps fsT
        [.abs (.var 0),
         .abs (aps conssL [conssChain items nilL, .var 0]), t]) = true
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    refine ⟨⟨⟨hfs, by decide, ?_⟩, htcl⟩⟩
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨⟨closed_mono closed_conssL (Nat.zero_le (d + 1)),
            ?_⟩, by decide⟩
    exact closed_conssChain items nilL (d + 1)
      (fun c hc => closed_mono (hcs c hc :
        closed 0 c = true) (Nat.zero_le (d + 1)))
      (closed_mono closed_nilL (Nat.zero_le (d + 1)))

theorem closed_osegChain (fsT fuelT : LTerm)
    (hfs : closed 0 fsT = true) (hfu : closed 0 fuelT = true) :
    ∀ (segs : List OSeg) (t : LTerm),
      (∀ s ∈ segs, osegClosed s) → closed 0 t = true →
      closed 0 (osegChain fsT fuelT segs t) = true := by
  intro segs; induction segs with
  | nil => intro t _ h; exact h
  | cons s ss ih =>
    intro t hcs htcl
    show closed 0 (osegApp fsT fuelT s (osegChain fsT fuelT ss t)) =
        true
    exact closed_osegApp fsT fuelT 0 hfs hfu s _
      (hcs s List.mem_cons_self)
      (ih t (fun s' hs' => hcs s' (List.mem_cons_of_mem _ hs')) htcl)

/-- semantic spine cells are closed. -/
theorem closed_osegCells : ∀ (s : OSeg) (fuse : Bool)
    (fuel : Option LTerm),
    osegClosed s → (∀ v ∈ fuel, closed 0 v = true) →
    (∀ c ∈ segsO s, psegClosed s') →
    ∀ c ∈ osegCells fuse fuel s, closed 0 c = true := sorry

/-- outer-chain eval: `osegChain segs rest` folds the program's
    fragment cells onto `rest`'s normal form. -/
theorem osegChain_eval (fsT fuelT : LTerm)
    (fuse : Bool) (fuel : Option LTerm)
    (hfs : LRed fsT (boolLit fuse))
    (hfuel : LRed fuelT (optionLit fuel))
    (hfjcl : ∀ v ∈ fuel, closed 0 v = true)
    (hfscl : closed 0 fsT = true) (hfucl : closed 0 fuelT = true) :
    ∀ (segs : List OSeg) (t tn : LTerm),
      (∀ s ∈ segs, osegClosed s) → closed 0 t = true →
      LRed t tn → closed 0 tn = true →
      LRed (osegChain fsT fuelT segs t)
           ((progSem fuse fuel segs).foldr cellLit tn) := by
  intro segs; induction segs with
  | nil => intro t tn _ _ ht _; exact ht
  | cons s ss ih =>
    intro t tn hcs htcl ht htn
    show LRed (osegApp fsT fuelT s (osegChain fsT fuelT ss t)) _
    have hss := fun s' hs' => hcs s' (List.mem_cons_of_mem _ hs')
    have hinner := ih t tn hss htcl ht htn
    have hich : closed 0 ((progSem fuse fuel ss).foldr cellLit tn) =
        true :=
      closed_foldr_cellLit _ tn
        (fun c hc => closed_progSem ss fuse fuel hss hfjcl c hc) htn
    have htcl' : closed 0 (osegChain fsT fuelT ss t) = true :=
      closed_osegChain fsT fuelT hfscl hfucl ss t hss htcl
    have hstep := osegApp_eval fsT fuelT fuse fuel hfs hfuel hfjcl
      hfscl hfucl s (osegChain fsT fuelT ss t)
      ((progSem fuse fuel ss).foldr cellLit tn)
      (hcs s List.mem_cons_self) htcl' hinner hich
    show LRed _ ((progSem fuse fuel (s :: ss)).foldr cellLit tn)
    show LRed _ (((osegCells fuse fuel s) ++
      (progSem fuse fuel ss)).foldr cellLit tn)
    rw [List.foldr_append]
    exact hstep
'''

txt = txt.replace('\nend ISAR', block + '\nend ISAR')
io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('appended')
