import ISAR.Kernel

/-!
# Reduce — leftmost-outermost single-step interpreter

`step?` matches **IStep** redexes only (normβ, konstβ, compβ, sβ, appL, appR).
No dupβ/swapβ — those belong to `IStepBasis`, not the main reduction.

`reduceFuel` iterates `step?` up to a fuel bound.

Soundness: `step?_sound` proves `step? t = some u → IStep t u`.
-/

namespace ISAR

open ITerm in
/-- Leftmost-outermost one-step reduction matching `IStep`. -/
def step? : ITerm → Option ITerm
  | .app .norm x => some x
  | .app (.app .konst x) _ => some x
  | .app (.app (.app .comp f) g) x => some (.app f (.app g x))
  | .app (.app (.app .sₛ x) y) z => some (.app (.app x z) (.app y z))
  | .app f x =>
    match step? f with
    | some f' => some (.app f' x)
    | none =>
      match step? x with
      | some x' => some (.app f x')
      | none => none
  | _ => none

/-- Fuelled iteration of `step?`. -/
def reduceFuel : Nat → ITerm → ITerm
  | 0, t => t
  | n + 1, t =>
    match step? t with
    | some u => reduceFuel n u
    | none => t

/-- Count steps taken before normal form or fuel exhaustion. -/
def reduceCount : Nat → ITerm → Nat × ITerm
  | 0, t => (0, t)
  | n + 1, t =>
    match step? t with
    | some u =>
      let (k, r) := reduceCount n u
      (k + 1, r)
    | none => (0, t)

/-! ### Soundness -/

/-- Helper: when `step?` lands in the appL/appR fallback. -/
private theorem step?_fallback (f x u : ITerm)
    (ihf : ∀ u, step? f = some u → IStep f u)
    (ihx : ∀ u, step? x = some u → IStep x u)
    (h : (match step? f with
          | some f' => some (ITerm.app f' x)
          | none => match step? x with
                    | some x' => some (ITerm.app f x')
                    | none => none) = some u) :
    IStep (ITerm.app f x) u := by
  split at h
  next f' hf' => injection h with h; subst h; exact IStep.appL (ihf f' hf')
  next =>
    split at h
    next x' hx' => injection h with h; subst h; exact IStep.appR (ihx x' hx')
    next => simp at h

theorem step?_sound (t : ITerm) : ∀ u, step? t = some u → IStep t u := by
  induction t with
  | var _ => intro u h; simp [step?] at h
  | norm => intro u h; simp [step?] at h
  | konst => intro u h; simp [step?] at h
  | dup => intro u h; simp [step?] at h
  | swap => intro u h; simp [step?] at h
  | comp => intro u h; simp [step?] at h
  | sₛ => intro u h; simp [step?] at h
  | app f x ihf ihx =>
    intro u h
    -- Lean's equation compiler produces a cascade matching `f` up to 3 levels deep.
    -- We case-split on `f` to align with the definition's patterns.
    cases f with
    | var n => exact step?_fallback _ x u (ihf) ihx (by simpa [step?] using h)
    | norm => simp [step?] at h; subst h; exact IStep.normβ x
    | konst => exact step?_fallback _ x u (ihf) ihx (by simpa [step?] using h)
    | dup => exact step?_fallback _ x u (ihf) ihx (by simpa [step?] using h)
    | swap => exact step?_fallback _ x u (ihf) ihx (by simpa [step?] using h)
    | comp => exact step?_fallback _ x u (ihf) ihx (by simpa [step?] using h)
    | sₛ => exact step?_fallback _ x u (ihf) ihx (by simpa [step?] using h)
    | app f1 x1 =>
      cases f1 with
      | konst => simp [step?] at h; subst h; exact IStep.konstβ x1 x
      | var n => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
      | norm =>
        -- step? (.app (.app .norm x1) x) triggers fallback: step? on (.app .norm x1) first
        exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
      | dup => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
      | swap => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
      | comp => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
      | sₛ => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
      | app f2 x2 =>
        cases f2 with
        | comp => simp [step?] at h; subst h; exact IStep.compβ x2 x1 x
        | sₛ => simp [step?] at h; subst h; exact IStep.sβ x2 x1 x
        | var n => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
        | norm => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
        | konst => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
        | dup => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
        | swap => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)
        | app f3 x3 => exact step?_fallback _ x u ihf ihx (by simpa [step?] using h)

theorem reduceFuel_IRed (n : Nat) (t : ITerm) : IRed t (reduceFuel n t) := by
  induction n generalizing t with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    unfold reduceFuel
    split
    next u heq => exact Relation.ReflTransGen.head (step?_sound t u heq) (ih u)
    next => exact Relation.ReflTransGen.refl

/-! ### #eval / #guard on step? path -/

open ITerm in
#eval step? (app norm konst)

open ITerm in
#eval reduceFuel 10 (app norm konst)

open ITerm in
#eval reduceFuel 10 (app (app konst sₛ) norm)

open ITerm in
#eval reduceFuel 20 (app (app (app sₛ konst) konst) norm)

open ITerm in
private def B_term : ITerm := app (app sₛ (app konst sₛ)) konst

open ITerm in
#eval reduceCount 30 (app (app (app B_term konst) norm) sₛ)

open ITerm in
#guard reduceFuel 10 (app norm konst) == konst

open ITerm in
#guard reduceFuel 10 (app (app konst sₛ) norm) == sₛ

open ITerm in
#guard reduceFuel 20 (app (app (app sₛ konst) konst) norm) == norm

end ISAR
