import ISAR.DialectKernel

namespace ISAR

/--
An observational isomorphism between two dialects `D1` and `D2`.
It establishes that their observation spaces are isomorphic (via `f` and `g`),
and that they commute with decoding from the invariant substrate quotient.
-/
structure ObservationalIsomorphism (D1 D2 : Dialect) where
  f : D1.Obs → D2.Obs
  g : D2.Obs → D1.Obs
  f_congr : ∀ (o1 o2 : D1.Obs), D1.ObsEq o1 o2 → D2.ObsEq (f o1) (f o2)
  g_congr : ∀ (o1 o2 : D2.Obs), D2.ObsEq o1 o2 → D1.ObsEq (g o1) (g o2)
  f_g_inverse : ∀ (o : D2.Obs), D2.ObsEq (f (g o)) o
  g_f_inverse : ∀ (o : D1.Obs), D1.ObsEq (g (f o)) o
  commute : ∀ (q : InvariantLayer), D2.ObsEq (f (D1.decode q)) (D2.decode q)

/--
No Preferred Syntax Theorem:
If two dialects are observationally isomorphic, then for any state in the invariant substrate `q`,
their decoded observations are isomorphic. Thus, neither syntax is ontologically privileged; they are
just different representations of the same underlying substrate state.
-/
theorem no_preferred_syntax (D1 D2 : Dialect) (iso : ObservationalIsomorphism D1 D2) (q : InvariantLayer) :
    D2.ObsEq (iso.f (D1.decode q)) (D2.decode q) := by
  exact iso.commute q

/-- Observational isomorphism is reflexive. -/
def ObservationalIsomorphism.refl (D : Dialect) : ObservationalIsomorphism D D where
  f := id
  g := id
  f_congr := fun _ _ h => h
  g_congr := fun _ _ h => h
  f_g_inverse := fun o => D.is_equiv.refl o
  g_f_inverse := fun o => D.is_equiv.refl o
  commute := fun q => D.is_equiv.refl (D.decode q)

/-- Observational isomorphism is symmetric. -/
def ObservationalIsomorphism.symm {D1 D2 : Dialect} (iso : ObservationalIsomorphism D1 D2) :
    ObservationalIsomorphism D2 D1 where
  f := iso.g
  g := iso.f
  f_congr := iso.g_congr
  g_congr := iso.f_congr
  f_g_inverse := iso.g_f_inverse
  g_f_inverse := iso.f_g_inverse
  commute := by
    intro q
    -- 1. D2.ObsEq (iso.f (D1.decode q)) (D2.decode q)
    have h_comm := iso.commute q
    -- 2. D1.ObsEq (iso.g (iso.f (D1.decode q))) (iso.g (D2.decode q))
    have h_g := iso.g_congr _ _ h_comm
    -- 3. D1.ObsEq (iso.g (iso.f (D1.decode q))) (D1.decode q)
    have h_inv := iso.g_f_inverse (D1.decode q)
    -- 4. By symmetry and transitivity: D1.ObsEq (iso.g (D2.decode q)) (D1.decode q)
    exact D1.is_equiv.trans (D1.is_equiv.symm h_g) h_inv

/-- Observational isomorphism is transitive. -/
def ObservationalIsomorphism.trans {D1 D2 D3 : Dialect}
    (iso1 : ObservationalIsomorphism D1 D2) (iso2 : ObservationalIsomorphism D2 D3) :
    ObservationalIsomorphism D1 D3 where
  f := iso2.f ∘ iso1.f
  g := iso1.g ∘ iso2.g
  f_congr := fun _ _ h => iso2.f_congr _ _ (iso1.f_congr _ _ h)
  g_congr := fun _ _ h => iso1.g_congr _ _ (iso2.g_congr _ _ h)
  f_g_inverse := by
    intro o
    dsimp
    -- We know: D2.ObsEq (iso1.f (iso1.g (iso2.g o))) (iso2.g o)
    have h_inv1 := iso1.f_g_inverse (iso2.g o)
    -- By congruence: D3.ObsEq (iso2.f (iso1.f (iso1.g (iso2.g o)))) (iso2.f (iso2.g o))
    have h_cong := iso2.f_congr _ _ h_inv1
    -- We also know: D3.ObsEq (iso2.f (iso2.g o)) o
    have h_inv2 := iso2.f_g_inverse o
    exact D3.is_equiv.trans h_cong h_inv2
  g_f_inverse := by
    intro o
    dsimp
    -- We know: D2.ObsEq (iso2.g (iso2.f (iso1.f o))) (iso1.f o)
    have h_inv1 := iso2.g_f_inverse (iso1.f o)
    -- By congruence: D1.ObsEq (iso1.g (iso2.g (iso2.f (iso1.f o)))) (iso1.g (iso1.f o))
    have h_cong := iso1.g_congr _ _ h_inv1
    -- We also know: D1.ObsEq (iso1.g (iso1.f o)) o
    have h_inv2 := iso1.g_f_inverse o
    exact D1.is_equiv.trans h_cong h_inv2
  commute := by
    intro q
    dsimp
    -- 1. D3.ObsEq (iso2.f (iso2.g (iso2.f (iso1.f (D1.decode q))))) (iso2.f (iso1.f (D1.decode q)))
    -- Actually, simpler:
    -- D2.ObsEq (iso1.f (D1.decode q)) (D2.decode q)
    have h_comm1 := iso1.commute q
    -- D3.ObsEq (iso2.f (iso1.f (D1.decode q))) (iso2.f (D2.decode q))
    have h_f_congr := iso2.f_congr _ _ h_comm1
    -- D3.ObsEq (iso2.f (D2.decode q)) (D3.decode q)
    have h_comm2 := iso2.commute q
    exact D3.is_equiv.trans h_f_congr h_comm2

end ISAR
