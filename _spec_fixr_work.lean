import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- Batch M layer 3: EQSTR (bounded nibble-string equality) + ALOOK
-- Terms machine-emitted from the seed's own LC parser (_emit_lc.py).
-- ============================================================

/-- `λk2. k2·a·b·O` state cell — args sit literally under the abs
    (pairLit-style).  `.var` args address the enclosing context. -/
def eqSt (a b O : LTerm) : LTerm := .abs (aps (.var 0) [a, b, O])

/-- `(λh.λt. (K I))` — the isNil continuation cell from the source. -/
def isNilK : LTerm := .abs (.abs (aps klL [idL]))

/-- `(K I)` reduces to `KI` — `λy. I` is `.abs idL` = `kilL`. -/
theorem kiI_eval : LRed (aps klL [idL]) kilL :=
  LRed_of_hsteps (k := 1) (by
    simp [klL, idL, kilL, aps, List.foldl, hsteps, hstep, subst, shift])

/-- `K·I·x·y →* y`. -/
theorem kiApp_apply2 (x y : LTerm) :
    LRed (aps (aps klL [idL]) [x, y]) y :=
  (LRed_app_left (LRed_app_left kiI_eval)).trans (kilL_apply2 x y)

/-- `λn.λc. c·h·t` cell applied: `cellLit h t·X·Y →* Y·h·t` for
    closed cells. -/
theorem cellLit_apply2 (h t X Y : LTerm)
    (hh : closed 0 h = true) (ht : closed 0 t = true) :
    LRed (aps (cellLit h t) [X, Y]) (aps Y [h, t]) := by
  unfold cellLit
  exact LRed_of_hsteps (k := 2) (by
    simp [aps, List.foldl, hsteps, hstep, subst, shift_zero,
          shift_of_closed0 hh, shift_of_closed0 ht,
          subst_of_closed0 hh, subst_of_closed0 ht])

/-- `isNilK·h·t →* K·I → kilL`. -/
theorem isNilK_apply2 (h t : LTerm) :
    LRed (aps isNilK [h, t]) kilL :=
  (LRed_of_hsteps (k := 2) (by
    simp [isNilK, klL, idL, aps, List.foldl, hsteps, hstep,
          subst])).trans kiI_eval

/-- `lb·K·isNilK` is nilness: `scottList bs →* boolLit bs.isEmpty`. -/
theorem isNil_eval (bs : List LTerm)
    (hb : ∀ c ∈ bs, closed 0 c = true) :
    LRed (aps (scottList bs) [klL, isNilK]) (boolLit bs.isEmpty) := by
  cases bs with
  | nil =>
    simp only [scottList, List.foldr, List.isEmpty]
    exact klL_apply2 _ _
  | cons h t =>
    simp only [scottList, List.foldr, List.isEmpty, boolLit]
    exact (cellLit_apply2 h (scottList t) klL isNilK
          (hb _ List.mem_cons_self)
          (closed_scottList (fun c hc =>
            hb _ (List.mem_cons_of_mem _ hc)))).trans
      (isNilK_apply2 h (scottList t))

/-- `_STEP_E` — emitted from the seed source (see _emit_lc.py):
    `λacc. acc (λla.λlb.λo. o (la nilArm consArm) falseArm)`. -/
def stepEL : LTerm :=
  let kiApp := aps klL [idL]
  let falseSt := eqSt (.var 3) (.var 2) kiApp
  let nilSt := eqSt (.var 3) (.var 2)
    (aps (.var 2) [klL, isNilK])
  let lbNilSt := eqSt (.var 5) (.var 4) kiApp
  let contSt := eqSt (.var 3) (.var 1) klL
  let stopSt := eqSt (.var 3) (.var 1) kiApp
  let eqArm := .abs (.abs
    (aps eqnibL [.var 3, .var 1, contSt, stopSt]))
  let consArm := .abs (.abs (aps (.var 3) [lbNilSt, eqArm]))
  let sel := .abs (.abs (.abs
    (aps (.var 0) [aps (.var 2) [nilSt, consArm], falseSt])))
  .abs (.app (.var 0) sel)

/-- semantic eqStr continue-step — the `o = true` branch, split out so
    `eqStepSem`'s flag match stays the outer test. -/
def eqStepSemT (la lb : List (Fin 16)) :
    List (Fin 16) × List (Fin 16) × Bool :=
  match la, lb with
  | [], _ => ([], lb, lb.isEmpty)
  | ha :: ta, [] => (ha :: ta, [], false)
  | ha :: ta, hb :: tb => (ta, tb, decide (ha = hb))

/-- semantic eqStr step on `(la, lb, flag)` — flag tested first so
    the step reduces on literal flags with free lists. -/
def eqStepSem (la lb : List (Fin 16)) (o : Bool) :
    List (Fin 16) × List (Fin 16) × Bool :=
  match o with
  | false => (la, lb, false)
  | true => eqStepSemT la lb

theorem eqStepSem_ff (la lb : List (Fin 16)) :
    eqStepSem la lb false = (la, lb, false) := rfl

theorem eqStepSem_nil (lb : List (Fin 16)) :
    eqStepSem [] lb true = ([], lb, lb.isEmpty) := rfl

theorem eqStepSem_rnil (a0 : Fin 16) (ta : List (Fin 16)) :
    eqStepSem (a0 :: ta) [] true = (a0 :: ta, [], false) := rfl

theorem eqStepSem_cc (a0 : Fin 16) (ta : List (Fin 16)) (b0 : Fin 16)
    (tb : List (Fin 16)) :
    eqStepSem (a0 :: ta) (b0 :: tb) true =
      (ta, tb, decide (a0 = b0)) := rfl

/-- EQSTR extractor: `λla.λlb.λo. o (la (lb·K·isNilK) isNilK) (K I)`. -/
def eqExtrL : LTerm :=
  .abs (.abs (.abs (aps (.var 0) [
    aps (.var 2) [aps (.var 1) [klL, isNilK], isNilK],
    aps klL [idL]])))

/-- `EQSTR = λa.λb.λn. n·stepEL·init·extract`. -/
def eqStrL : LTerm :=
  .abs (.abs (.abs (aps (.var 0) [
    stepEL, eqSt (.var 3) (.var 2) klL, eqExtrL])))

theorem closed_isNilK : closed 0 isNilK = true := by decide

theorem closed_stepEL : closed 0 stepEL = true := by decide

theorem closed_eqExtrL : closed 0 eqExtrL = true := by decide

theorem closed_eqStrL : closed 0 eqStrL = true := by decide

theorem closed_eqSt {a b O : LTerm} (ha : closed 1 a = true)
    (hb : closed 1 b = true) (hO : closed 1 O = true) :
    closed 0 (eqSt a b O) = true := by
  simp only [eqSt, closed, aps, List.foldl, Bool.and_eq_true]
  exact ⟨⟨⟨by decide, ha⟩, hb⟩, hO⟩

/-- `stepEL·(eqSt a b O)` — five betas open the state cell and the
    selector to `O·A'·B'` with la/lb substituted into the arms. -/
theorem stepEL_open (a b O : LTerm)
    (ha : closed 0 a = true) (hb : closed 0 b = true)
    (hO : closed 0 O = true) :
    LRed (.app stepEL (eqSt a b O))
         (aps O
           [aps a
             [eqSt a b (aps b [klL, isNilK]),
              .abs (.abs (aps b
                [eqSt a b (aps klL [idL]),
                 .abs (.abs (aps eqnibL
                   [.var 3, .var 1,
                    eqSt (.var 3) (.var 1) klL,
                    eqSt (.var 3) (.var 1)
                      (aps klL [idL])]))]))],
            eqSt a b (aps klL [idL])]) :=
  LRed_of_hsteps (k := 5) (by
    have hst := closed_eqSt (closed_mono ha (Nat.zero_le 1))
      (closed_mono hb (Nat.zero_le 1)) (closed_mono hO (Nat.zero_le 1))
    simp [stepEL, eqSt, isNilK, aps, List.foldl, hsteps, hstep,
          subst, shift, shift_zero,
          shift_of_closed0 ha, shift_of_closed0 hb,
          shift_of_closed0 hO,
          subst_of_closed0 ha, subst_of_closed0 hb,
          subst_of_closed0 hO,
          subst_of_closed0 closed_klL, subst_of_closed0 closed_idL,
          subst_of_closed0 closed_eqnibL,
          shift_of_closed0 closed_klL, shift_of_closed0 closed_idL])

/-- the cons-arm's eqnib destructure with ha/ta substituted
    (closed args): `λhb.λtb. EQNIB ha hb T F`. -/
def eqArmSub (haT taT : LTerm) : LTerm :=
  .abs (.abs (aps eqnibL
    [haT, .var 1,
     eqSt taT (.var 1) klL,
     eqSt taT (.var 1) (aps klL [idL])]))

/-- one `_STEP_E` application mirrors `eqStepSem`: the state's list
    cells destructure, the flag short-circuits, and on a matched pair
    `EQNIB` chooses continue/stop.  Components are term-level with
    `LRed`-to-canonical invariants so thunk inputs (e.g. the len-bound
    unfolding) compose. -/
theorem stepE_eval (la lb : List (Fin 16)) (o : Bool)
    (aT bT O : LTerm)
    (ha : LRed aT (scottList (la.map nibLit)))
    (hb : LRed bT (scottList (lb.map nibLit)))
    (hO : LRed O (boolLit o))
    (hacl : closed 0 aT = true) (hbcl : closed 0 bT = true)
    (hOcl : closed 0 O = true) :
    ∃ aT' bT' O',
      LRed (.app stepEL (eqSt aT bT O)) (eqSt aT' bT' O') ∧
      LRed aT' (scottList ((eqStepSem la lb o).1.map nibLit)) ∧
      LRed bT' (scottList ((eqStepSem la lb o).2.1.map nibLit)) ∧
      LRed O' (boolLit (eqStepSem la lb o).2.2) ∧
      closed 0 aT' = true ∧ closed 0 bT' = true ∧
      closed 0 O' = true := by
  have hopen := stepEL_open aT bT O hacl hbcl hOcl
  have hflag : ∀ X Y : LTerm,
      LRed (aps O [X, Y]) (if o then X else Y) :=
    fun X Y =>
      (LRed_app_left (LRed_app_left hO)).trans (boolLit_sel o X Y)
  have hclA : ∀ c ∈ la.map nibLit, closed 0 c = true := by
    intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact closed_nibLit i
  have hclB : ∀ c ∈ lb.map nibLit, closed 0 c = true := by
    intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact closed_nibLit i
  cases o with
  | false =>
    rw [eqStepSem_ff]
    refine ⟨aT, bT, aps klL [idL], ?_, ha, hb, kiI_eval,
            hacl, hbcl,
            closed_app closed_klL closed_idL⟩
    exact hopen.trans (hflag _ _)
  | true =>
    cases la with
    | nil =>
      rw [eqStepSem_nil]
      refine ⟨aT, bT, aps bT [klL, isNilK], ?_, ha, hb, ?_, hacl, hbcl,
              closed_app (closed_app hbcl closed_klL) closed_isNilK⟩
      · exact hopen.trans ((hflag _ _).trans
          ((LRed_app_left (LRed_app_left ha)).trans
            (klL_apply2 _ _)))
      · have hm : (lb.map nibLit).isEmpty = lb.isEmpty := by
          cases lb <;> rfl
        exact hm ▸ ((LRed_app_left (LRed_app_left hb)).trans
          (isNil_eval _ hclB))
    | cons ha' ta =>
      simp only [List.map_cons, scottList, List.foldr] at ha
      -- A2' = λha.λta. b·X1·X2 with b,X1 already substituted
      have hA2 : ∀ hT tT : LTerm, closed 0 hT = true →
          closed 0 tT = true →
          LRed (aps (.abs (.abs (aps bT
                [eqSt aT bT (aps klL [idL]),
                 .abs (.abs (aps eqnibL
                   [.var 3, .var 1,
                    eqSt (.var 3) (.var 1) klL,
                    eqSt (.var 3) (.var 1) (aps klL [idL])]))])))
               [hT, tT])
            (aps bT [eqSt aT bT (aps klL [idL]), eqArmSub hT tT]) := by
        intro hT tT hht htt
        unfold eqArmSub
        exact LRed_of_hsteps (k := 2) (by
          simp [eqSt, aps, List.foldl, hsteps, hstep, subst,
                subst_of_closed0 hbcl, subst_of_closed0 hacl,
                shift_of_closed0 hht, subst_of_closed0 hht,
                shift_of_closed0 htt,
                subst_of_closed0 closed_klL, subst_of_closed0 closed_idL,
                subst_of_closed0 closed_eqnibL])
      have heq : ∀ hT tT hbT tbT : LTerm, closed 0 hT = true →
          closed 0 tT = true → closed 0 hbT = true →
          closed 0 tbT = true →
          LRed (aps (eqArmSub hT tT) [hbT, tbT])
            (aps eqnibL
              [hT, hbT, eqSt tT tbT klL, eqSt tT tbT (aps klL [idL])]) := by
        intro hT tT hbT tbT hht htt hhb htb
        unfold eqArmSub
        exact LRed_of_hsteps (k := 2) (by
          simp [eqSt, aps, List.foldl, hsteps, hstep, subst,
                subst_of_closed0 hht, subst_of_closed0 htt,
                shift_of_closed0 hhb, subst_of_closed0 hhb,
                shift_of_closed0 htb,
                subst_of_closed0 closed_klL, subst_of_closed0 closed_idL,
                subst_of_closed0 closed_eqnibL])
      -- the a-branch, decomposed
      have hclta : ∀ c ∈ ta.map nibLit, closed 0 c = true :=
        fun c hc => hclA c (List.mem_cons_of_mem _ hc)
      have hdestr : LRed (aps aT
            [eqSt aT bT (aps bT [klL, isNilK]),
             .abs (.abs (aps bT
               [eqSt aT bT (aps klL [idL]),
                .abs (.abs (aps eqnibL
                  [.var 3, .var 1,
                   eqSt (.var 3) (.var 1) klL,
                   eqSt (.var 3) (.var 1) (aps klL [idL])]))]))])
          (aps bT [eqSt aT bT (aps klL [idL]),
            eqArmSub (nibLit ha') (scottList (ta.map nibLit))]) :=
        (LRed_app_left (LRed_app_left ha)).trans
          ((cellLit_apply2 _ _ _ _ (closed_nibLit ha')
             (closed_scottList hclta)).trans
            (hA2 _ _ (closed_nibLit ha') (closed_scottList hclta)))
      cases lb with
      | nil =>
        rw [eqStepSem_rnil]
        refine ⟨aT, bT, aps klL [idL], ?_, ha, hb, kiI_eval,
                hacl, hbcl, closed_app closed_klL closed_idL⟩
        exact hopen.trans ((hflag _ _).trans
          (hdestr.trans ((LRed_app_left (LRed_app_left hb)).trans
            (klL_apply2 _ _))))
      | cons hb' tb =>
        rw [eqStepSem_cc]
        simp only [List.map_cons, scottList, List.foldr] at hb
        have hcltb : ∀ c ∈ tb.map nibLit, closed 0 c = true :=
          fun c hc => hclB c (List.mem_cons_of_mem _ hc)
        have hcons' : LRed (aps bT
              [eqSt aT bT (aps klL [idL]),
               eqArmSub (nibLit ha') (scottList (ta.map nibLit))])
            (aps eqnibL
              [nibLit ha', nibLit hb',
               eqSt (scottList (ta.map nibLit))
                    (scottList (tb.map nibLit)) klL,
               eqSt (scottList (ta.map nibLit))
                    (scottList (tb.map nibLit)) (aps klL [idL])]) :=
          (LRed_app_left (LRed_app_left hb)).trans
            ((cellLit_apply2 _ _ _ _ (closed_nibLit hb')
               (closed_scottList hcltb)).trans
              (heq _ _ _ _ (closed_nibLit ha')
                (closed_scottList hclta) (closed_nibLit hb')
                (closed_scottList hcltb)))
        -- eqnib head reduces to the flag; bool selects T/F arm
        have hsel : LRed (aps eqnibL
              [nibLit ha', nibLit hb',
               eqSt (scottList (ta.map nibLit))
                    (scottList (tb.map nibLit)) klL,
               eqSt (scottList (ta.map nibLit))
                    (scottList (tb.map nibLit)) (aps klL [idL])])
            (if decide (ha' = hb')
             then eqSt (scottList (ta.map nibLit))
                       (scottList (tb.map nibLit)) klL
             else eqSt (scottList (ta.map nibLit))
                       (scottList (tb.map nibLit)) (aps klL [idL])) :=
          (LRed_app_left (LRed_app_left (eqnib_eval ha' hb'))).trans
            (boolLit_sel _ _ _)
        cases hd : decide (ha' = hb') with
        | true =>
          rw [hd] at hsel
          refine ⟨scottList (ta.map nibLit),
                  scottList (tb.map nibLit), klL,
                  hopen.trans ((hflag _ _).trans
                    (hdestr.trans (hcons'.trans hsel))),
                  ?_, ?_, ?_, ?_, ?_, closed_klL⟩
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.refl
          · exact closed_scottList hclta
          · exact closed_scottList hcltb
        | false =>
          rw [hd] at hsel
          refine ⟨scottList (ta.map nibLit),
                  scottList (tb.map nibLit), aps klL [idL],
                  hopen.trans ((hflag _ _).trans
                    (hdestr.trans (hcons'.trans hsel))),
                  ?_, ?_, ?_, ?_, ?_,
                  closed_app closed_klL closed_idL⟩
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.refl
          · exact kiI_eval
          · exact closed_scottList hclta
          · exact closed_scottList hcltb

-- eqStr iteration layer ------------------------------------------------

/-- triple-view of the state for `eqRun`. -/
def eqStepSem3 (s : List (Fin 16) × List (Fin 16) × Bool) :
    List (Fin 16) × List (Fin 16) × Bool :=
  eqStepSem s.1 s.2.1 s.2.2

/-- semantic iterate — same recursion order as `iterL`. -/
def eqRun (s : List (Fin 16) × List (Fin 16) × Bool) : Nat →
    List (Fin 16) × List (Fin 16) × Bool
  | 0 => s
  | n + 1 => eqStepSem3 (eqRun s n)

/-- extraction semantics: flag ∧ both lists exhausted. -/
def eqFin (s : List (Fin 16) × List (Fin 16) × Bool) : Bool :=
  s.2.2 && s.1.isEmpty && s.2.1.isEmpty

theorem eqRun_shift (s : List (Fin 16) × List (Fin 16) × Bool)
    (n : Nat) : eqRun s (n + 1) = eqRun (eqStepSem3 s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show eqStepSem3 (eqRun s (n + 1)) = eqStepSem3 (eqRun (eqStepSem3 s) n)
    rw [ih]

theorem eqRun_split (s : List (Fin 16) × List (Fin 16) × Bool)
    (m k : Nat) : eqRun s (m + k) = eqRun (eqRun s m) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show eqStepSem3 (eqRun s (m + k)) = eqStepSem3 (eqRun (eqRun s m) k)
    rw [ih]

theorem eqRun_frozen (la lb : List (Fin 16)) (n : Nat) :
    eqRun (la, lb, false) n = (la, lb, false) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [eqRun, ih, eqStepSem3, eqStepSem_ff]

/-- a step preserves `la = []`. -/
theorem eqStepSem3_nil1 (s : List (Fin 16) × List (Fin 16) × Bool)
    (h : s.1 = []) : (eqStepSem3 s).1 = [] := by
  obtain ⟨l1, l2, o'⟩ := s
  have : l1 = [] := h
  subst this
  cases o' <;> rfl

/-- once `la` is exhausted the run keeps `la = []`. -/
theorem eqRun_nil1 (lb : List (Fin 16)) (o : Bool) (n : Nat) :
    (eqRun ([], lb, o) n).1 = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (eqStepSem3 (eqRun ([], lb, o) n)).1 = []
    exact eqStepSem3_nil1 _ ih

/-- one step preserves `eqFin` once `la = []`. -/
theorem eqFin_step_nil (s : List (Fin 16) × List (Fin 16) × Bool)
    (h : s.1 = []) :
    eqFin (eqStepSem3 s) = eqFin s := by
  obtain ⟨l1, l2, o'⟩ := s
  have : l1 = [] := h
  subst this
  cases o' <;>
    simp [eqFin, eqStepSem3, eqStepSem_ff, eqStepSem_nil,
          List.isEmpty, Bool.and_self, Bool.and_true, Bool.true_and]

/-- eqFin is stable once `la = []` (extra bound steps don't change
    the extracted answer). -/
theorem eqRun_nil_fin (lb : List (Fin 16)) (o : Bool) :
    ∀ n : Nat, eqFin (eqRun ([], lb, o) n) = (o && lb.isEmpty) := by
  intro n; induction n with
  | zero => cases o <;> rfl
  | succ n ih =>
    show eqFin (eqStepSem3 (eqRun ([], lb, o) n)) = (o && lb.isEmpty)
    rw [eqFin_step_nil _ (eqRun_nil1 lb o n)]
    exact ih

/-- `decide ([] = lb)` is `lb.isEmpty`. -/
theorem decide_nil_eq (lb : List (Fin 16)) :
    decide ([] = lb) = lb.isEmpty := by
  cases lb <;> rfl

/-- **`eqRunLen`**: running the equality machine for `la.length + m`
    steps from `(la, lb, true)` ends with extraction value
    `decide (la = lb)`. -/
theorem eqRunLen : ∀ (la lb : List (Fin 16)) (m : Nat),
    eqFin (eqRun (la, lb, true) (la.length + m)) =
      decide (la = lb) := by
  intro la lb
  induction la generalizing lb with
  | nil =>
    intro m
    show eqFin (eqRun ([], lb, true) (0 + m)) = decide ([] = lb)
    rw [Nat.zero_add, eqRun_nil_fin, decide_nil_eq,
        Bool.true_and]
  | cons ha' ta ih =>
    intro m
    show eqFin (eqRun (ha' :: ta, lb, true)
        (ta.length + 1 + m)) = decide (ha' :: ta = lb)
    rw [show ta.length + 1 + m = ta.length + m + 1 by omega,
        eqRun_shift]
    cases lb with
    | nil =>
      show eqFin (eqRun (eqStepSem (ha' :: ta) [] true)
          (ta.length + m)) = _
      rw [eqStepSem_rnil, eqRun_frozen]
      rfl
    | cons hb' tb =>
      show eqFin (eqRun (eqStepSem (ha' :: ta) (hb' :: tb) true)
          (ta.length + m)) = _
      rw [eqStepSem_cc]
      cases hd : decide (ha' = hb') with
      | false =>
        rw [eqRun_frozen]
        simp [eqFin, of_decide_eq_false hd]
      | true =>
        have h : ha' = hb' := of_decide_eq_true hd
        subst h
        show eqFin (eqRun (ta, tb, true) (ta.length + m)) = _
        rw [ih tb m]
        simp

-- term-level iteration + extraction ------------------------------------

/-- `eqSt a b O · k →* k·a·b·O` for closed components. -/
theorem eqSt_apply (a b O k : LTerm)
    (hac : closed 0 a = true) (hbc : closed 0 b = true)
    (hOc : closed 0 O = true) :
    LRed (.app (eqSt a b O) k) (aps k [a, b, O]) :=
  LRed_of_hsteps (k := 1) (by
    simp [eqSt, aps, List.foldl, hsteps, hstep, subst, shift_zero,
          subst_of_closed0 hac, subst_of_closed0 hbc,
          subst_of_closed0 hOc])

/-- iterated `_STEP_E` over the state cell mirrors `eqRun`. -/
theorem eqIter_eval : ∀ (n : Nat) (la lb : List (Fin 16)) (o : Bool)
    (aT bT O : LTerm),
    LRed aT (scottList (la.map nibLit)) →
    LRed bT (scottList (lb.map nibLit)) →
    LRed O (boolLit o) →
    closed 0 aT = true → closed 0 bT = true →
    closed 0 O = true →
    ∃ aT' bT' O',
      LRed (iterL stepEL (eqSt aT bT O) n) (eqSt aT' bT' O') ∧
      LRed aT' (scottList ((eqRun (la, lb, o) n).1.map nibLit)) ∧
      LRed bT' (scottList ((eqRun (la, lb, o) n).2.1.map nibLit)) ∧
      LRed O' (boolLit (eqRun (la, lb, o) n).2.2) ∧
      closed 0 aT' = true ∧ closed 0 bT' = true ∧
      closed 0 O' = true := by
  intro n
  induction n with
  | zero =>
    intro la lb o aT bT O ha hb hO hac hbc hOc
    exact ⟨aT, bT, O, Relation.ReflTransGen.refl, ha, hb, hO,
           hac, hbc, hOc⟩
  | succ n ih =>
    intro la lb o aT bT O ha hb hO hac hbc hOc
    obtain ⟨aT', bT', O', hiter, ha', hb', hO', hac', hbc', hOc'⟩ :=
      ih la lb o aT bT O ha hb hO hac hbc hOc
    obtain ⟨aT'', bT'', O'', hstep', ha'', hb'', hO'',
            hac'', hbc'', hOc''⟩ :=
      stepE_eval _ _ _ aT' bT' O' ha' hb' hO' hac' hbc' hOc'
    refine ⟨aT'', bT'', O'', ?_, ha'', hb'', hO'', hac'', hbc'', hOc''⟩
    show LRed (iterL stepEL (eqSt aT bT O) (n + 1))
              (eqSt aT'' bT'' O'')
    exact (LRed_app_right hiter).trans hstep'

/-- `eqExtrL` opens to the flag-selected extraction spine. -/
theorem eqExtr_open (a b O : LTerm)
    (hac : closed 0 a = true) (hbc : closed 0 b = true)
    (hOc : closed 0 O = true) :
    LRed (aps eqExtrL [a, b, O])
      (aps O [aps a [aps b [klL, isNilK], isNilK],
              aps klL [idL]]) :=
  LRed_of_hsteps (k := 3) (by
    simp [eqExtrL, aps, List.foldl, hsteps, hstep, subst,
          shift_of_closed0 hac, subst_of_closed0 hac,
          shift_of_closed0 hbc, subst_of_closed0 hbc,
          shift_of_closed0 hOc,
          subst_of_closed0 closed_klL, subst_of_closed0 closed_idL,
          subst_of_closed0 closed_isNilK])

/-- the extractor reduces to `boolLit (o && la.isEmpty && lb.isEmpty)`
    — the EQSTR answer. -/
theorem eqExtr_eval (la lb : List (Fin 16)) (o : Bool)
    (aT bT O : LTerm)
    (ha : LRed aT (scottList (la.map nibLit)))
    (hb : LRed bT (scottList (lb.map nibLit)))
    (hO : LRed O (boolLit o))
    (hacl : closed 0 aT = true) (hbcl : closed 0 bT = true)
    (hOcl : closed 0 O = true) :
    LRed (aps eqExtrL [aT, bT, O])
      (boolLit (o && la.isEmpty && lb.isEmpty)) := by
  have hopen := eqExtr_open aT bT O hacl hbcl hOcl
  have hflag : ∀ X Y : LTerm,
      LRed (aps O [X, Y]) (if o then X else Y) :=
    fun X Y =>
      (LRed_app_left (LRed_app_left hO)).trans (boolLit_sel o X Y)
  have hclB : ∀ c ∈ lb.map nibLit, closed 0 c = true := by
    intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact closed_nibLit i
  cases o with
  | false =>
    show LRed _ (boolLit false)
    exact hopen.trans ((hflag _ _).trans kiI_eval)
  | true =>
    show LRed _ (boolLit (la.isEmpty && lb.isEmpty))
    have hm : (lb.map nibLit).isEmpty = lb.isEmpty := by
      cases lb <;> rfl
    have hb' : LRed (aps bT [klL, isNilK]) (boolLit lb.isEmpty) :=
      hm ▸ ((LRed_app_left (LRed_app_left hb)).trans
        (isNil_eval _ hclB))
    cases la with
    | nil =>
      simp only [List.map_nil, scottList, List.foldr] at ha
      have hX : LRed (aps aT [aps bT [klL, isNilK], isNilK])
          (boolLit lb.isEmpty) :=
        (LRed_app_left (LRed_app_left ha)).trans
          ((klL_apply2 _ _).trans hb')
      exact hopen.trans ((hflag _ _).trans hX)
    | cons h t =>
      simp only [List.map_cons, scottList, List.foldr] at ha
      have hclt : ∀ c ∈ t.map nibLit, closed 0 c = true := by
        intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
        exact closed_nibLit i
      have hX : LRed (aps aT [aps bT [klL, isNilK], isNilK])
          (boolLit false) :=
        (LRed_app_left (LRed_app_left ha)).trans
          ((cellLit_apply2 _ _ _ _ (closed_nibLit h)
             (closed_scottList hclt)).trans (isNilK_apply2 _ _))
      show LRed _ (boolLit false)
      exact hopen.trans ((hflag _ _).trans hX)

/-- `EQSTR` opens to `n·stepEL·init·extr`. -/
theorem eqStr_open (a b n : LTerm)
    (hac : closed 0 a = true) (hbc : closed 0 b = true)
    (hnc : closed 0 n = true) :
    LRed (aps eqStrL [a, b, n])
         (aps n [stepEL, eqSt a b klL, eqExtrL]) :=
  LRed_of_hsteps (k := 3) (by
    simp [eqStrL, eqSt, aps, List.foldl, hsteps, hstep, subst,
          shift_of_closed0 hac, subst_of_closed0 hac,
          shift_of_closed0 hbc, subst_of_closed0 hbc,
          shift_of_closed0 hnc,
          subst_of_closed0 closed_klL,
          subst_of_closed0 closed_stepEL, subst_of_closed0 closed_eqExtrL])

/-- **`eqStr_eval`**: `EQSTR·a·b·n →* boolLit (decide (la = lb))`
    for `n ≥ la.length` — open, Church-bound to `iterL`, the
    `eqRun` iteration, then extraction via `eqFin` = `eqRunLen`. -/
theorem eqStr_eval (la lb : List (Fin 16)) (n : Nat)
    (hn : la.length ≤ n)
    (aT bT NT : LTerm)
    (ha : LRed aT (scottList (la.map nibLit)))
    (hb : LRed bT (scottList (lb.map nibLit)))
    (hN : LRed NT (succChain kilL n))
    (hacl : closed 0 aT = true) (hbcl : closed 0 bT = true)
    (hNcl : closed 0 NT = true) :
    LRed (aps eqStrL [aT, bT, NT]) (boolLit (decide (la = lb))) := by
  have hopen := eqStr_open aT bT NT hacl hbcl hNcl
  have hclI : closed 0 (eqSt aT bT klL) = true :=
    closed_eqSt (closed_mono hacl (Nat.zero_le 1))
      (closed_mono hbcl (Nat.zero_le 1))
      (closed_mono closed_klL (Nat.zero_le 1))
  have h1 : LRed (aps NT [stepEL, eqSt aT bT klL, eqExtrL])
      (.app (iterL stepEL (eqSt aT bT klL) n) eqExtrL) :=
    (LRed_app_left (LRed_app_left (LRed_app_left hN))).trans
      (LRed_app_left (succTower_iter n stepEL (eqSt aT bT klL)
        closed_stepEL hclI))
  obtain ⟨aF, bF, OF, hit, haF, hbF, hOF, hacF, hbcF, hOcF⟩ :=
    eqIter_eval n la lb true aT bT klL ha hb
      Relation.ReflTransGen.refl hacl hbcl closed_klL
  have h2 : LRed (.app (iterL stepEL (eqSt aT bT klL) n) eqExtrL)
      (aps eqExtrL [aF, bF, OF]) :=
    (LRed_app_left hit).trans
      (eqSt_apply aF bF OF eqExtrL hacF hbcF hOcF)
  have h3 : LRed (aps eqExtrL [aF, bF, OF])
      (boolLit (eqFin (eqRun (la, lb, true) n))) :=
    eqExtr_eval _ _ _ aF bF OF haF hbF hOF hacF hbcF hOcF
  have hfin : eqFin (eqRun (la, lb, true) n) = decide (la = lb) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [hm]; exact eqRunLen la lb m
  exact hopen.trans (h1.trans (h2.trans (hfin ▸ h3)))

-- ALOOK -----------------------------------------------------------------

/-- `_JUST = λv.λn.λj. j v` — the option-some constructor. -/
def justL : LTerm := .abs (.abs (.abs (aps (.var 0) [.var 2])))

theorem closed_justL : closed 0 justL = true := by decide

/-- option encoding over term values: nothing = `K`,
    `some v` = `justL·v`. -/
def optionLit : Option LTerm → LTerm
  | none => klL
  | some v => .app justL v

/-- the `_ALOOK` step with the key term inlined (the post-subst form
    the `alookL` unfold produces):
    `λacc.λe. e (λk2.λv2. eqStr keyT k2 (len·keyT)·(just·v2)·acc)`. -/
def alookStepK (keyT : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0)
    [.abs (.abs (aps eqStrL
      [keyT, .var 1, aps lenL [keyT],
       aps justL [.var 0], .var 3]))]))

theorem closed_alookStepK (keyT : LTerm) (hk : closed 0 keyT = true) :
    closed 0 (alookStepK keyT) = true := by
  have hk' : ∀ c, closed c keyT = true :=
    fun c => closed_mono hk (Nat.zero_le c)
  have he : ∀ c, closed c eqStrL = true :=
    fun c => closed_mono closed_eqStrL (Nat.zero_le c)
  have hl : ∀ c, closed c lenL = true :=
    fun c => closed_mono closed_lenL (Nat.zero_le c)
  have hj : ∀ c, closed c justL = true :=
    fun c => closed_mono closed_justL (Nat.zero_le c)
  simp only [alookStepK, closed, aps, List.foldl, Bool.and_eq_true,
             hk', he, hl, hj]
  decide

/-- `st·X·e →* e·kont` — the alook step opens to the pair
    destructure. -/
theorem alookStepK_open (keyT X e : LTerm)
    (hkc : closed 0 keyT = true) (hX : closed 0 X = true)
    (he : closed 0 e = true) :
    LRed (aps (alookStepK keyT) [X, e])
      (.app e (.abs (.abs (aps eqStrL
        [keyT, .var 1, aps lenL [keyT],
         aps justL [.var 0], X])))) :=
  LRed_of_hsteps (k := 2) (by
    simp [alookStepK, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed0 hkc,
          shift_of_closed0 hX, subst_of_closed0 hX,
          shift_of_closed0 he,
          subst_of_closed0 closed_eqStrL,
          subst_of_closed0 closed_lenL,
          subst_of_closed0 closed_justL])

/-- the kont applied to pair components opens the eqStr spine. -/
theorem alookKont_eval (keyT k2T v2T X : LTerm)
    (hkc : closed 0 keyT = true) (hk2 : closed 0 k2T = true)
    (hv2 : closed 0 v2T = true) (hX : closed 0 X = true) :
    LRed (aps (.abs (.abs (aps eqStrL
            [keyT, .var 1, aps lenL [keyT],
             aps justL [.var 0], X]))) [k2T, v2T])
      (aps eqStrL
        [keyT, k2T, aps lenL [keyT], aps justL [v2T], X]) :=
  LRed_of_hsteps (k := 2) (by
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed0 hkc,
          shift_of_closed0 hk2, subst_of_closed0 hk2,
          shift_of_closed0 hv2,
          subst_of_closed0 hX,
          subst_of_closed0 closed_eqStrL,
          subst_of_closed0 closed_lenL,
          subst_of_closed0 closed_justL])

/-- one `_ALOOK` step: destructure the pair cell, run `EQSTR`, and
    select `JUST v2` on match (overwrites — last match wins) or the
    accumulator otherwise. -/
theorem alookStep_eval (key : List (Fin 16)) (keyT : LTerm)
    (hkeyT : LRed keyT (scottList (key.map nibLit)))
    (hkeycl : closed 0 keyT = true)
    (k2 : List (Fin 16)) (v2 X : LTerm)
    (hv2 : closed 0 v2 = true) (hXcl : closed 0 X = true)
    (e : LTerm)
    (he : LRed e (aps pairSrcL
      [scottList (k2.map nibLit), v2]))
    (hecl : closed 0 e = true) :
    LRed (.app (.app (alookStepK keyT) X) e)
      (if decide (key = k2) then aps justL [v2] else X) := by
  have hclkey : ∀ c ∈ key.map nibLit, closed 0 c = true := by
    intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact closed_nibLit i
  have hclsk2 : closed 0 (scottList (k2.map nibLit)) = true :=
    closed_scottList (fun c hc => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      exact closed_nibLit i)
  have hlen : LRed (aps lenL [keyT]) (succChain kilL key.length) :=
    (LRed_app_right hkeyT).trans
      (List.length_map (f := nibLit) ▸ len_eval _ hclkey)
  have hopen := alookStepK_open keyT X e hkeycl hXcl hecl
  have hpair : LRed (.app e (.abs (.abs (aps eqStrL
        [keyT, .var 1, aps lenL [keyT], aps justL [.var 0], X]))))
      (aps eqStrL
        [keyT, scottList (k2.map nibLit), aps lenL [keyT],
         aps justL [v2], X]) :=
    (LRed_app_left he).trans
      ((LRed_app_left (pairSrc_nf _ _ hclsk2 hv2)).trans
        ((pairLit_apply _ _ _ hclsk2 hv2).trans
          (alookKont_eval keyT _ _ X hkeycl hclsk2 hv2 hXcl)))
  have hstr : LRed (aps eqStrL
        [keyT, scottList (k2.map nibLit), aps lenL [keyT],
         aps justL [v2], X])
      (aps (boolLit (decide (key = k2)))
        [aps justL [v2], X]) :=
    LRed_app_left (LRed_app_left
      (eqStr_eval key k2 key.length (Nat.le_refl _)
        keyT (scottList (k2.map nibLit)) (aps lenL [keyT])
        hkeyT Relation.ReflTransGen.refl hlen
        hkeycl hclsk2 (closed_app closed_lenL hkeycl)))
  exact hopen.trans (hpair.trans (hstr.trans (boolLit_sel _ _ _)))

/-- the fold over pair-cells mirrors `alookSem`: last matching key
    wins; `none` stays `K`. -/
theorem alookFold_eval (key : List (Fin 16)) (keyT : LTerm)
    (hkeyT : LRed keyT (scottList (key.map nibLit)))
    (hkeycl : closed 0 keyT = true)
    (es : List LTerm) (kvs : List (List (Fin 16) × LTerm))
    (h2 : List.Forall₂
      (fun e kv => LRed e (aps pairSrcL
          [scottList (kv.1.map nibLit), kv.2]) ∧
        closed 0 e = true ∧ closed 0 kv.2 = true) es kvs) :
    ∀ (X : LTerm) (a : Option LTerm),
      LRed X (optionLit a) → closed 0 X = true →
      LRed (es.foldl
            (fun acc e => .app (.app (alookStepK keyT) acc) e) X)
           (optionLit (kvs.foldl (fun acc kv =>
              if decide (key = kv.1) then some kv.2 else acc) a)) := by
  induction h2 with
  | nil =>
    intro X a hX _
    show LRed X (optionLit a)
    exact hX
  | cons he' h2' ih =>
    intro X a hX hXcl
    rename_i e kv es' kvs'
    obtain ⟨he, hecl, hv2⟩ := he'
    rw [List.foldl_cons, List.foldl_cons]
    have hstep := alookStep_eval key keyT hkeyT hkeycl kv.1 kv.2 X
      hv2 hXcl e he hecl
    have hcl : closed 0 (.app (.app (alookStepK keyT) X) e) = true :=
      closed_app (closed_app (closed_alookStepK keyT hkeycl)
        hXcl) hecl
    cases hd : decide (key = kv.1) with
    | true =>
      have hstep' : LRed (.app (.app (alookStepK keyT) X) e)
          (optionLit (some kv.2)) := by
        rw [hd] at hstep
        exact hstep.trans Relation.ReflTransGen.refl
      exact ih _ (some kv.2) hstep' hcl
    | false =>
      have hstep' : LRed (.app (.app (alookStepK keyT) X) e)
          (optionLit a) := by
        rw [hd] at hstep
        exact hstep.trans hX
      exact ih _ a hstep' hcl

/-- `_ALOOK = λmap.λkey. FOLDL step map K` — emitted. -/
def alookL : LTerm :=
  .abs (.abs (aps foldlL
    [.abs (.abs (aps (.var 0)
      [.abs (.abs (aps eqStrL
        [.var 4, .var 1, aps lenL [.var 4],
         aps justL [.var 0], .var 3]))])),
     .var 1, klL]))

theorem closed_alookL : closed 0 alookL = true := by decide

/-- `alookL` opens to the `foldlL` spine with the key substituted. -/
theorem alookL_open (mapT keyT : LTerm)
    (hmc : closed 0 mapT = true) (hkc : closed 0 keyT = true) :
    LRed (aps alookL [mapT, keyT])
      (aps foldlL [alookStepK keyT, mapT, klL]) :=
  LRed_of_hsteps (k := 2) (by
    simp [alookL, alookStepK, aps, List.foldl, hsteps, hstep, subst,
          shift_of_closed0 hmc, subst_of_closed0 hmc,
          shift_of_closed0 hkc,
          subst_of_closed0 closed_foldlL,
          subst_of_closed0 closed_eqStrL,
          subst_of_closed0 closed_lenL,
          subst_of_closed0 closed_justL,
          subst_of_closed0 closed_klL])

/-- **`alook_eval`**: `ALOOK·map·key` reduces to the option-encoded
    last-match lookup — `none ↦ K`, `some v ↦ justL·v`. -/
theorem alook_eval (key : List (Fin 16)) (keyT : LTerm)
    (hkeyT : LRed keyT (scottList (key.map nibLit)))
    (hkeycl : closed 0 keyT = true)
    (es : List LTerm) (kvs : List (List (Fin 16) × LTerm))
    (h2 : List.Forall₂
      (fun e kv => LRed e (aps pairSrcL
          [scottList (kv.1.map nibLit), kv.2]) ∧
        closed 0 e = true ∧ closed 0 kv.2 = true) es kvs)
    (hcles : ∀ e ∈ es, closed 0 e = true)
    (mapT : LTerm) (hmap : LRed mapT (scottList es))
    (hmapcl : closed 0 mapT = true) :
    LRed (aps alookL [mapT, keyT])
      (optionLit (kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv.2 else acc) none)) := by
  have hopen := alookL_open mapT keyT hmapcl hkeycl
  have hstep : ∀ (acc e : LTerm), closed 0 acc = true →
      closed 0 e = true →
      LRed (.app (.app (alookStepK keyT) acc) e)
           (.app (.app (alookStepK keyT) acc) e) ∧
      closed 0 (.app (.app (alookStepK keyT) acc) e) = true :=
    fun acc e hac he =>
      ⟨Relation.ReflTransGen.refl,
       closed_app (closed_app (closed_alookStepK keyT hkeycl) hac) he⟩
  have hfold := fold_eval (alookStepK keyT)
    (fun acc e => .app (.app (alookStepK keyT) acc) e)
    (closed_alookStepK keyT hkeycl) hstep mapT klL es
    hmapcl closed_klL hmap hcles
  have hred := alookFold_eval key keyT hkeyT hkeycl es kvs h2 klL
    none Relation.ReflTransGen.refl closed_klL
  exact hopen.trans (hfold.trans hred)

#print axioms stepE_eval
#print axioms eqIter_eval
#print axioms eqRunLen
#print axioms eqExtr_eval
#print axioms eqStr_eval
#print axioms alookStep_eval
#print axioms alookFold_eval
#print axioms alook_eval

end ISAR
