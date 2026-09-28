import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- host boundary classification — the fuel-license classes.
-- ============================================================

/-- `t·t` anywhere in the term — the vocabulary's only
    divergence-capable pattern (bounded by Scott-list spines inside
    the proven fold heads); on the external boundary it is the
    degenerate shape refused at import. -/
def hasSelfApp : LTerm → Bool
  | .var _ => false
  | .abs b => hasSelfApp b
  | .app f x => decide (f = x) || hasSelfApp f || hasSelfApp x

/-- `shift` is injective: renumbering preserves term equality. -/
theorem shift_inj : ∀ {d c : Nat} {t u : LTerm},
    shift d c t = shift d c u → t = u := by
  intro d c t
  induction t generalizing c with
  | var n =>
      intro u h
      cases u with
      | var m =>
          simp only [shift] at h
          split_ifs at h <;> simp only [LTerm.var.injEq] at h ⊢ <;>
            omega
      | abs u' =>
          simp only [shift] at h
          split_ifs at h
      | app _ _ =>
          simp only [shift] at h
          split_ifs at h
  | abs b ih =>
      intro u h
      cases u with
      | var m =>
          simp only [shift] at h
          split_ifs at h
      | abs u' =>
          simp only [shift, LTerm.abs.injEq] at h
          obtain rfl := ih h
          rfl
      | app _ _ =>
          simp only [shift] at h
          cases h
  | app f x ihf ihx =>
      intro u h
      cases u with
      | var m =>
          simp only [shift] at h
          split_ifs at h
      | abs _ =>
          simp only [shift] at h
          cases h
      | app f' x' =>
          simp only [shift, LTerm.app.injEq] at h
          obtain ⟨hf, hx⟩ := h
          obtain rfl := ihf hf
          obtain rfl := ihx hx
          rfl

/-- self-application is shift-invariant — a `t·t` node maps to a
    `(shift t)·(shift t)` node, nothing else appears. -/
theorem hasSelfApp_shift : ∀ (t : LTerm) (d c : Nat),
    hasSelfApp (shift d c t) = hasSelfApp t := by
  intro t
  induction t with
  | var n =>
      intro d c
      simp only [shift, hasSelfApp]
      split_ifs <;> simp only [hasSelfApp]
  | abs b ih =>
      intro d c
      simp only [shift, hasSelfApp, ih]
  | app f x ihf ihx =>
      intro d c
      simp only [shift, hasSelfApp, ihf, ihx]
      congr 1
      have hiff : (shift d c f = shift d c x) ↔ (f = x) :=
        ⟨fun h => shift_inj h, fun h => congrArg (shift d c) h⟩
      simp only [hiff]

/-- import-time structural gate for external lambda input: closed
    and self-application free. -/
def wfImportL (t : LTerm) : Bool := closed 0 t && !hasSelfApp t

/-- ISAR-term closedness: any `var` leaf is free (the bracket-
    abstracted surface has no binders). -/
def hasVarI : ITerm → Bool
  | .var _ => true
  | .app f x => hasVarI f || hasVarI x
  | _ => false

/-- `t·t` anywhere on the ISAR surface. -/
def hasSelfAppI : ITerm → Bool
  | .app f x => decide (f = x) || hasSelfAppI f || hasSelfAppI x
  | _ => false

/-- import-time structural gate for external ISAR input. -/
def wfImportI (t : ITerm) : Bool := !hasVarI t && !hasSelfAppI t

/-- host boundary class — where a term sits in the fuel license:
    `proven` is witnessed per term (a `Proven` certificate — an
    actual `LRed` to a normal form); `budgeted`/`rejected` are the
    decidable split of external input at import. -/
inductive HostClass where
  | proven | budgeted | rejected

/-- a dialect carries its own well-formedness predicate —
    degenerate-shape detection is an import-time structural check
    (closedness, arity, spine-boundedness), not a lambda-specific
    assumption. -/
structure BoundaryGate (T : Type) where
  wf : T → Bool

/-- decidable external classification under a gate: passing the
    import WF makes the term budgeted (the fuel bound is the
    contract); failing it refuses the term at import. -/
def classifyExt {T : Type} (g : BoundaryGate T) (t : T) : HostClass :=
  if g.wf t then .budgeted else .rejected

/-- the lambda-side gate. -/
def lambdaGate : BoundaryGate LTerm := ⟨wfImportL⟩

/-- the ISAR-side gate. -/
def isarGate : BoundaryGate ITerm := ⟨wfImportI⟩

/-- the witnessed class: membership IS an actual reduction to a
    normal form — fuel never appears in the statement.  On the
    proven path fuel is a bug fail-safe, not the termination
    argument. -/
def Proven (t : LTerm) : Prop := ∃ nf, LRed t nf

/-- a Scott list is selfApp-free when every cell is — the spine's
    own application nodes compare `.var 0`/shifted heads, which can
    never coincide. -/
theorem hasSelfApp_scottList : ∀ (cs : List LTerm),
    (∀ c ∈ cs, hasSelfApp c = false) →
    hasSelfApp (scottList cs) = false := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c t ih =>
      intro h
      have hc := h c List.mem_cons_self
      have ht := fun x hx => h x (List.mem_cons_of_mem c hx)
      have hih := ih ht
      show hasSelfApp (cellLit c (scottList t)) = false
      simp only [cellLit, hasSelfApp]
      have hv : ¬ ((.var 0 : LTerm) = shift 2 0 c) := by
        cases c <;> intro hcon <;> cases hcon
      have hne2 : ¬ (.app (.var 0) (shift 2 0 c) =
          shift 2 0 (scottList t)) := by
        intro hcon
        cases t <;> cases hcon
      simp only [decide_eq_false hne2, decide_eq_false hv,
        hasSelfApp_shift, hc, hih]
      rfl

/-- emitted data passes the import gate: a Scott list of closed,
    selfApp-free cells is closed and selfApp-free. -/
theorem wfImportL_scottList : ∀ (cs : List LTerm),
    (∀ c ∈ cs, closed 0 c = true ∧ hasSelfApp c = false) →
    wfImportL (scottList cs) = true := by
  intro cs h
  have hsa := hasSelfApp_scottList cs (fun c hc => (h c hc).2)
  have hcl := closed_scottList (fun c hc => (h c hc).1)
  simp only [wfImportL]
  rw [hcl, hsa]
  rfl

/-- external classification: a term passing the import gate is
    budgeted; one failing it is rejected. -/
theorem classifyExt_wf {T : Type} (g : BoundaryGate T) {t : T}
    (h : g.wf t = true) : classifyExt g t = .budgeted := by
  simp [classifyExt, h]

theorem classifyExt_notwf {T : Type} (g : BoundaryGate T) {t : T}
    (h : g.wf t = false) : classifyExt g t = .rejected := by
  simp [classifyExt, h]

/-- the program stage's output is proven-class — `program_eval` is
    exactly a `Proven` certificate, and fuel plays no role. -/
theorem program_proven (fuse : Bool) (fuel : Option LTerm)
    (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true)
    (hfjcl : ∀ v ∈ fuel, closed 0 v = true) :
    Proven (aps programT
        [boolLit fuse, optionLit fuel, rbbT, cbT, nbT]) :=
  ⟨_, program_eval fuse fuel rbbT cbT nbT hr hc hn hfjcl⟩

end ISAR
