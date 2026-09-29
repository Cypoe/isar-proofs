"""Append the host boundary classification block before the audit
section of SpecVocabulary.lean."""

BLOCK = '''
-- ---------- host boundary classification ---------------------

/-- `t·t` anywhere in the term — the vocabulary's only
    divergence-capable pattern (bounded by Scott-list spines inside
    the proven fold heads); on the external boundary it is the
    degenerate shape refused at import. -/
def hasSelfApp : LTerm → Bool
  | .var _ => false
  | .abs b => hasSelfApp b
  | .app f x => decide (f = x) || hasSelfApp f || hasSelfApp x

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

/-- a Scott list is selfApp-free when every cell is selfApp-free and
    none IS the cons cell (a `cellLit·cellLit` pair would be a real
    self-application and is correctly refused). -/
theorem hasSelfApp_scottList : ∀ (cs : List LTerm),
    (∀ c ∈ cs, hasSelfApp c = false ∧ c ≠ cellLit) →
    hasSelfApp (scottList cs) = false := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c t ih =>
      intro h
      have hc := h c List.mem_cons_self
      have ht : ∀ x ∈ t, hasSelfApp x = false ∧ x ≠ cellLit :=
        fun x hx => h x (List.mem_cons_of_mem c hx)
      show hasSelfApp (cellLit c (scottList t)) = false
      simp only [cellLit, aps, hasSelfApp]
      have hne : .app (.abs (.abs (.abs (.abs
            (.app (.app (.var 0) (.var 3)) (.var 2))))) c ≠
          scottList t := by
        cases t with
        | nil => intro hcon; cases hcon
        | cons y ys =>
            intro hcon
            have := congrArg (fun s => match s with
              | .app f _ => f | _ => .var 999) hcon
            simp only [scottList, List.foldr, cellLit, aps] at this
      have hfa : ¬ (.abs (.abs (.abs (.abs
            (.app (.app (.var 0) (.var 3)) (.var 2))))) = c) := hc.2
      simp only [decide_eq_false (m := hne), decide_eq_false
        (m := hfa), Bool.false_or, hc.1, ih ht, Bool.or_self]
'''

src = open('src/ISAR/SpecVocabulary.lean', encoding='utf-8').read()
marker = '-- ---------- axiom audit ---'
i = src.rindex(marker)
src = src[:i] + BLOCK + '\n' + src[i:]
open('src/ISAR/SpecVocabulary.lean', 'w', encoding='utf-8').write(src)
print('appended, chars:', len(src))
