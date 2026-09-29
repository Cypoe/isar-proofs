import ISAR.LambdaFragment
import ISAR.BasisDev
import ISAR.HeapDev

/-!
Scratch: append-associativity as observational equivalence (`Join`)
of the λ-encoded spec vocabulary (spec_term.py `_FOLDL`/`_CONSS`/`_APPEND`).

Architecture:
  LTerm level (weak β, de Bruijn) —
    hstep?/hsteps: head-spine-only β evaluator + soundness.
    Fuel-bounded so it stops AT the claimed milestone term (discharge
    by rfl — subst/shift compute on symbolic leaves; all spec
    combinators are closed so splices under binders reduce cleanly).
    cell_unfold : GGB·(cellLit h t)·a →* GGB·t·(st·a·h)
    fold_read   : GGB·(scott cs)·a →* foldr cellLit a (rev cs)
    append_eval : APPEND·(scott as)·(scott bs) →* scott (as++bs)
    append_assoc: LJoin (APPEND (APPEND a b) c) (APPEND a (APPEND b c))
  Transport — compile_simulates_red (LRed→IRed) ∘
    translate_preserves_red (IRed→IRedBasis, lifted) ∘ Join.
-/

namespace ISAR

open Relation LTerm

-- de Bruijn encodings, faithful to spec_term.py ---------------------------

/-- Scott nil: `\n.\c. n` — the spec's `_NIL` shape. -/
def nilL : LTerm := .abs (.abs (.var 1))

/-- Scott cons-cell literal `\n.\c. c h t` — NF of `CONSS·h·t`. -/
def cellLit (h t : LTerm) : LTerm :=
  .abs (.abs (.app (.app (.var 0) (shift 2 0 h)) (shift 2 0 t)))

/-- `_CONSS = (\h2.\t2.\n2.\c2. c2 h2 t2)` — under the four binders
    h2=3, t2=2, n2=1, c2=0. -/
def conssL : LTerm :=
  .abs (.abs (.abs (.abs (.app (.app (.var 0) (.var 3)) (.var 2)))))

/-- fold step `s = \a.\h. CONSS·h·a` (shared by `_REV`/`_APPEND`). -/
def stepConsL : LTerm :=
  .abs (.abs (.app (.app conssL (.var 0)) (.var 1)))

/-- `G st = \g.\l2.\a2. l2 a2 (\h.\t. g g t (st a2 h))` — the worker
    inside `_FOLDL`'s `(\f. f f) G`. -/
def foldG (st : LTerm) : LTerm :=
  .abs (.abs (.abs (.app (.app (.var 1) (.var 0))
    (.abs (.abs (.app
      (.app (.app (.var 4) (.var 4)) (.var 0))
      (.app (.app (shift 5 0 st) (.var 2)) (.var 1))))))))

/-- `W = \f. f f` -/
def wl : LTerm := .abs (.app (.var 0) (.var 0))

/-- `_FOLDL = \st.\l.\a. W·(G st)·l·a` -/
def foldlL : LTerm :=
  .abs (.abs (.abs (.app (.app (.app wl (foldG (.var 2))) (.var 1))
    (.var 0))))

/-- `_REV`/`_APPEND` applied forms. -/
def revT (l : LTerm) : LTerm :=
  .app (.app (.app foldlL stepConsL) l) nilL
def appendT (xs ys : LTerm) : LTerm :=
  .app (.app (.app foldlL stepConsL) (revT xs)) ys

/-- Scott list literal from cell terms. -/
def scottList (cs : List LTerm) : LTerm := cs.foldr cellLit nilL

/-- `l` is a Scott list of `cs`. -/
def IsList (l : LTerm) (cs : List LTerm) : Prop := LRed l (scottList cs)

/-- λ-level observational equivalence: common weak-β reduct. -/
def LJoin (a b : LTerm) : Prop := ∃ u, LRed a u ∧ LRed b u

-- closedness (free-var bound) ----------------------------------------------

/-- All free de Bruijn indices below `c`. -/
def closed : Nat → LTerm → Bool
  | c, .var n => decide (n < c)
  | c, .abs b => closed (c + 1) b
  | c, .app f x => closed c f && closed c x

theorem closed_mono {t : LTerm} {c c' : Nat} (h : closed c t = true)
    (hc : c ≤ c') : closed c' t = true := by
  induction t generalizing c c' with
  | var n =>
      simp only [closed, decide_eq_true_eq] at h ⊢
      exact Nat.lt_of_lt_of_le h hc
  | abs b ih =>
      simp only [closed] at h ⊢
      exact ih h (Nat.succ_le_succ hc)
  | app f x ihf ihx =>
      simp only [closed, Bool.and_eq_true] at h ⊢
      exact ⟨ihf h.1 hc, ihx h.2 hc⟩

/-- Shifting a closed term is the identity. -/
theorem shift_of_closed {t : LTerm} {c : Nat} (h : closed c t = true) (d : Nat) :
    shift d c t = t := by
  induction t generalizing c with
  | var n =>
      simp only [closed, decide_eq_true_eq] at h
      simp only [shift]
      rw [if_pos h]
  | abs b ih =>
      simp only [closed] at h
      simp only [shift, ih h]
  | app f x ihf ihx =>
      simp only [closed, Bool.and_eq_true] at h
      simp only [shift, ihf h.1, ihx h.2]

/-- Substituting into a closed term is the identity. -/
theorem subst_of_closed {t : LTerm} {c : Nat} (h : closed c t = true)
    (s : LTerm) : subst s c t = t := by
  induction t generalizing c with
  | var n =>
      simp only [closed, decide_eq_true_eq] at h
      simp only [subst]
      rw [if_pos h]
  | abs b ih =>
      simp only [closed] at h
      simp only [subst, ih h]
  | app f x ihf ihx =>
      simp only [closed, Bool.and_eq_true] at h
      simp only [subst, ihf h.1, ihx h.2]

/-- Fully closed (`closed 0`): shift at any cutoff is the identity. -/
theorem shift_of_closed0 {t : LTerm} (h : closed 0 t = true) (d c : Nat) :
    shift d c t = t :=
  shift_of_closed (closed_mono h (Nat.zero_le c)) d

/-- Fully closed: subst at any cutoff is the identity. -/
theorem subst_of_closed0 {t : LTerm} (h : closed 0 t = true) (s : LTerm)
    (c : Nat) : subst s c t = t :=
  subst_of_closed (closed_mono h (Nat.zero_le c)) s

-- head-spine β evaluator + soundness ---------------------------------------

/-- Head-only β: step the leftmost head redex down the function spine;
    never descends into arguments; identity where no head redex.
    Matches the FOLDL unfold order; fuel bounds where it stops. -/
def hstep : LTerm → LTerm
  | .app f x =>
      match f with
      | .abs b => subst x 0 b
      | _ => .app (hstep f) x
  | t => t

def hsteps : Nat → LTerm → LTerm
  | 0, t => t
  | n + 1, t => hsteps n (hstep t)

/-- One head step is a valid weak-β reduction (refl where inert). -/
theorem hstep_red : ∀ t : LTerm, LRed t (hstep t) := by
  intro t
  induction t with
  | var n => exact Relation.ReflTransGen.refl
  | abs b => exact Relation.ReflTransGen.refl
  | app f x ihf _ =>
      cases f with
      | abs b => exact Relation.ReflTransGen.single (LStep.beta b x)
      | var n => exact Relation.ReflTransGen.refl
      | app f1 x1 => exact LRed_app_left ihf

theorem hsteps_red : ∀ (n : Nat) (t : LTerm), LRed t (hsteps n t) := by
  intro n
  induction n with
  | zero => intro t; exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro t
      exact (hstep_red t).trans (ih (hstep t))

/-- Certificate discharge: `hsteps k t = u` gives `LRed t u`. -/
theorem LRed_of_hsteps {t u : LTerm} {k : Nat} (h : hsteps k t = u) :
    LRed t u := h ▸ hsteps_red k t

-- sanity: the encodings actually compute -----------------------------------

/-- The once-unfolded worker — the computed reduct of `foldG st · foldG st`
    so milestones are what hsteps produces, not hand-derived indices. -/
def GGB (st : LTerm) : LTerm :=
  hsteps 1 (.app (foldG st) (foldG st))

/-- `gs st · l · a` — the running fold state. -/
def gsA (st l a : LTerm) : LTerm := .app (.app (.app (foldG st) (foldG st)) l) a

/-- `GGB st · l · a` -/
def ggbA (st l a : LTerm) : LTerm := .app (.app (GGB st) l) a

-- milestone probes: symbolic h=(var 0) t=(var 1) a=(var 2)
#eval hsteps 1 (gsA stepConsL (.var 0) (.var 1)) == ggbA stepConsL (.var 0) (.var 1)

-- the cell unfold: GGB·(cell h t)·a →* GGB·t·(st·a·h)
#eval (List.range 12).map fun k =>
    (k, hsteps k (ggbA stepConsL (cellLit (.var 0) (.var 1)) (.var 2))
      == ggbA stepConsL (.var 1)
          (.app (.app stepConsL (.var 2)) (.var 0)))

-- st·a·h →* cellLit h a
#eval (List.range 8).map fun k =>
    (k, hsteps k (.app (.app stepConsL (.var 2)) (.var 0))
      == cellLit (.var 0) (.var 2))
#eval hsteps 6 (.app (.app stepConsL (.var 2)) (.var 0))
#eval cellLit (.var 0) (.var 2)

-- nil unfold: GGB·nil·a →* a
#eval (List.range 8).map fun k =>
    (k, hsteps k (ggbA stepConsL nilL (.var 2)) == .var 2)

-- foldlL entry: foldlL·st·l·a →* GGB·l·a
#eval (List.range 8).map fun k =>
    (k, hsteps k (.app (.app (.app foldlL stepConsL) (.var 0)) (.var 1))
      == ggbA stepConsL (.var 0) (.var 1))

-- the lemmas -----------------------------------------------------------------

/-- `gs st · l · a` head-unfolds to the applied worker. -/
theorem gsA_to_ggb (st l a : LTerm) :
    LRed (gsA st l a) (ggbA st l a) :=
  LRed_of_hsteps (k := 1) rfl

/-- `_FOLDL·st·l·a →* GGB st·l·a` — entry unfold through W·G. -/
theorem foldl_to_ggb (st l a : LTerm) (hs : closed 0 st = true)
    (hl : closed 0 l = true) (ha : closed 0 a = true) :
    LRed (.app (.app (.app foldlL st) l) a) (ggbA st l a) :=
  LRed_of_hsteps (k := 5) (by
    simp [gsA, ggbA, GGB, foldlL, wl, foldG, nilL, cellLit, conssL,
          stepConsL, hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 hl, shift_of_closed0 ha,
          subst_of_closed0 hs, subst_of_closed0 hl, subst_of_closed0 ha])

/-- Cell unfold — one cons cell processed, tail passed on, accumulator
    updated.  The recursion reproduces `GGB` literally because every
    spec combinator is closed (shift of closed = id). -/
theorem cell_unfold (h t a : LTerm) (hh : closed 0 h = true)
    (ht : closed 0 t = true) (ha : closed 0 a = true) :
    LRed (ggbA stepConsL (cellLit h t) a)
         (ggbA stepConsL t (.app (.app stepConsL a) h)) :=
  LRed_of_hsteps (k := 7) (by
    simp [gsA, ggbA, GGB, foldlL, wl, foldG, nilL, cellLit, conssL,
          stepConsL, hsteps, hstep, subst, shift,
          shift_of_closed0 hh, shift_of_closed0 ht, shift_of_closed0 ha,
          subst_of_closed0 hh, subst_of_closed0 ht, subst_of_closed0 ha])

/-- `st·a·h →* cellLit h a` — the step produces a cell literal. -/
theorem stepCons_cell (h a : LTerm) (hh : closed 0 h = true)
    (ha : closed 0 a = true) :
    LRed (.app (.app stepConsL a) h) (cellLit h a) :=
  LRed_of_hsteps (k := 4) (by
    simp [cellLit, conssL, stepConsL, subst, shift, hsteps, hstep,
          shift_of_closed0 hh, shift_of_closed0 ha,
          subst_of_closed0 hh, subst_of_closed0 ha])

/-- `GGB·nil·a →* a`. -/
theorem nil_unfold (a : LTerm) (ha : closed 0 a = true) :
    LRed (ggbA stepConsL nilL a) a :=
  LRed_of_hsteps (k := 4) (by
    simp [gsA, ggbA, GGB, foldlL, wl, foldG, nilL, cellLit, conssL,
          stepConsL, hsteps, hstep, subst, shift,
          shift_of_closed0 ha, subst_of_closed0 ha])

-- closedness of the encodings ------------------------------------------------

theorem closed_app {f x : LTerm} (hf : closed 0 f = true)
    (hx : closed 0 x = true) : closed 0 (.app f x) = true := by
  simp only [closed, Bool.and_eq_true]; exact ⟨hf, hx⟩

theorem closed_cellLit {h t : LTerm} (hh : closed 0 h = true)
    (ht : closed 0 t = true) : closed 0 (cellLit h t) = true := by
  simp only [cellLit, closed, shift_of_closed0 hh, shift_of_closed0 ht,
             Bool.and_eq_true]
  exact ⟨⟨by decide, closed_mono hh (Nat.zero_le _)⟩,
    closed_mono ht (Nat.zero_le _)⟩

theorem closed_scottList {cs : List LTerm}
    (h : ∀ e ∈ cs, closed 0 e = true) : closed 0 (scottList cs) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [scottList, List.foldr_cons]
      exact closed_cellLit (h c List.mem_cons_self)
        (ih (fun e he => h e (List.mem_cons_of_mem c he)))

theorem closed_revT {l : LTerm} (h : closed 0 l = true) :
    closed 0 (revT l) = true :=
  closed_app (closed_app (closed_app (by decide) (by decide)) h) rfl

theorem closed_appendT {xs ys : LTerm} (hx : closed 0 xs = true)
    (hy : closed 0 ys = true) : closed 0 (appendT xs ys) = true :=
  closed_app (closed_app (closed_app (by decide) (by decide))
    (closed_revT hx)) hy

/-- Fold readback: `GGB·(scott cs)·a →* foldr cellLit a (rev cs)` —
    the cells cons onto the accumulator in reverse order.  Side
    conditions: cells and accumulator are closed (real payloads are). -/
theorem fold_read : ∀ (cs : List LTerm) (a : LTerm),
    (∀ e ∈ cs, closed 0 e = true) → closed 0 a = true →
    LRed (ggbA stepConsL (scottList cs) a)
         (cs.reverse.foldr cellLit a) := by
  intro cs
  induction cs with
  | nil =>
      intro a _ ha
      simp only [scottList, List.foldr_nil, List.reverse_nil]
      exact nil_unfold a ha
  | cons c cs ih =>
      intro a hcl ha
      have hc : closed 0 c = true := hcl c List.mem_cons_self
      have hcs : ∀ e ∈ cs, closed 0 e = true :=
        fun e he => hcl e (List.mem_cons_of_mem c he)
      have e1 : scottList (c :: cs) = cellLit c (scottList cs) := rfl
      rw [e1]
      have s2 : LRed (.app (.app stepConsL a) c) (cellLit c a) :=
        stepCons_cell c a hc ha
      have s2' : LRed
          (ggbA stepConsL (scottList cs) (.app (.app stepConsL a) c))
          (ggbA stepConsL (scottList cs) (cellLit c a)) :=
        LRed_app_right s2
      have s3 := ih (cellLit c a) hcs (closed_cellLit hc ha)
      have eq : (c :: cs).reverse.foldr cellLit a
              = cs.reverse.foldr cellLit (cellLit c a) := by
        simp [List.reverse_cons, List.foldr_append]
      rw [eq]
      exact (cell_unfold c (scottList cs) a hc (closed_scottList hcs) ha)
        |>.trans (s2'.trans s3)

/-- `_REV·(scott cs) →* scott (rev cs)` — REV is FOLDL onto nil. -/
theorem rev_eval (l : LTerm) (cs : List LTerm) (h : IsList l cs)
    (hl : closed 0 l = true) (hcs : ∀ e ∈ cs, closed 0 e = true) :
    LRed (revT l) (scottList cs.reverse) := by
  have e1 : LRed (revT l)
      (ggbA stepConsL l nilL) :=
    foldl_to_ggb stepConsL l nilL rfl hl rfl
  have e2 : LRed (ggbA stepConsL l nilL)
      (ggbA stepConsL (scottList cs) nilL) :=
    LRed_app_left (LRed_app_right h)
  have e3 := fold_read cs nilL hcs rfl
  have e4 : cs.reverse.foldr cellLit nilL = scottList cs.reverse := rfl
  exact e1.trans (e2.trans (e4 ▸ e3))

/-- `_APPEND·(scott as)·(scott bs) →* scott (as ++ bs)` — append computes
    list concatenation on the Scott encoding. -/
theorem append_eval (xs ys : LTerm) (as bs : List LTerm)
    (hx : IsList xs as) (hy : IsList ys bs)
    (has : ∀ e ∈ as, closed 0 e = true) (hbs : ∀ e ∈ bs, closed 0 e = true)
    (hcx : closed 0 xs = true) (hcy : closed 0 ys = true) :
    LRed (appendT xs ys) (scottList (as ++ bs)) := by
  have r1 := rev_eval xs as hx hcx has
  have hrev : ∀ e ∈ as.reverse, closed 0 e = true :=
    fun e he => has e (List.mem_reverse.mp he)
  have hsrev : closed 0 (scottList as.reverse) = true :=
    closed_scottList hrev
  have hsbs : closed 0 (scottList bs) = true := closed_scottList hbs
  -- congruence: revT xs → scott as.reverse inside the app spine
  have c1 : LRed (appendT xs ys)
      (.app (.app (.app foldlL stepConsL) (scottList as.reverse)) ys) :=
    LRed_app (LRed_app Relation.ReflTransGen.refl r1)
      Relation.ReflTransGen.refl
  have c2 : LRed
      (.app (.app (.app foldlL stepConsL) (scottList as.reverse)) ys)
      (ggbA stepConsL (scottList as.reverse) ys) :=
    foldl_to_ggb _ _ _ rfl hsrev hcy
  have c3 : LRed (ggbA stepConsL (scottList as.reverse) ys)
      (ggbA stepConsL (scottList as.reverse) (scottList bs)) :=
    LRed_app_right hy
  have c4 := fold_read as.reverse (scottList bs) hrev hsbs
  have e : as.reverse.reverse.foldr cellLit (scottList bs)
      = scottList (as ++ bs) := by
    rw [List.reverse_reverse]
    show as.foldr cellLit (scottList bs) = scottList (as ++ bs)
    rw [scottList, scottList, ← List.foldr_append]
  exact c1.trans (c2.trans (c3.trans (e ▸ c4)))

/-- **append_assoc on the λ-encoding**: left- and right-nested appends
    join to the same Scott list — the observational equality the
    balanced-emission question needed. -/
theorem append_assoc_L (a b c : LTerm) (as bs cs : List LTerm)
    (ha : IsList a as) (hb : IsList b bs) (hc : IsList c cs)
    (has : ∀ e ∈ as, closed 0 e = true) (hbs : ∀ e ∈ bs, closed 0 e = true)
    (hcs : ∀ e ∈ cs, closed 0 e = true)
    (hca : closed 0 a = true) (hcb : closed 0 b = true)
    (hcc : closed 0 c = true) :
    LJoin (appendT (appendT a b) c) (appendT a (appendT b c)) := by
  have hab : IsList (appendT a b) (as ++ bs) :=
    append_eval a b as bs ha hb has hbs hca hcb
  have hbc : IsList (appendT b c) (bs ++ cs) :=
    append_eval b c bs cs hb hc hbs hcs hcb hcc
  have hasbs : ∀ e ∈ as ++ bs, closed 0 e = true := by
    intro e he
    cases List.mem_append.mp he with
    | inl hm => exact has e hm
    | inr hm => exact hbs e hm
  have hbcs : ∀ e ∈ bs ++ cs, closed 0 e = true := by
    intro e he
    cases List.mem_append.mp he with
    | inl hm => exact hbs e hm
    | inr hm => exact hcs e hm
  have hL := append_eval (appendT a b) c (as ++ bs) cs hab hc hasbs hcs
    (closed_appendT hca hcb) hcc
  have hR := append_eval a (appendT b c) as (bs ++ cs) ha hbc has hbcs
    hca (closed_appendT hcb hcc)
  rw [← List.append_assoc] at hR
  exact Exists.intro _ ⟨hL, hR⟩

-- transport to the host basis -----------------------------------------------

/-- `translate_to_basis` lifts over multi-step reduction. -/
theorem translate_preserves_red {t u : ITerm} (h : IRed t u) :
    IRedBasis (translate_to_basis t) (translate_to_basis u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (translate_preserves_step hs)

/-- The basis-level statement: the host's `import_tree(expand_s=True)`
    terms — `translate_to_basis ∘ compile` — are `Join`-equivalent
    under either association.  This is the formal license for
    balanced vs right-nested emission of APPEND chains. -/
theorem append_assoc_basis (as bs cs : List LTerm)
    (has : ∀ e ∈ as, closed 0 e = true)
    (hbs : ∀ e ∈ bs, closed 0 e = true)
    (hcs : ∀ e ∈ cs, closed 0 e = true) :
    Join (translate_to_basis (compile
            (appendT (appendT (scottList as) (scottList bs))
              (scottList cs))))
         (translate_to_basis (compile
            (appendT (scottList as)
              (appendT (scottList bs) (scottList cs))))) := by
  obtain ⟨u, h1, h2⟩ := append_assoc_L
    (scottList as) (scottList bs) (scottList cs) as bs cs
    Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl
    has hbs hcs
    (closed_scottList has) (closed_scottList hbs) (closed_scottList hcs)
  exact ⟨translate_to_basis (compile u),
    translate_preserves_red (compile_simulates_red h1),
    translate_preserves_red (compile_simulates_red h2)⟩

#print axioms append_assoc_basis

end ISAR
