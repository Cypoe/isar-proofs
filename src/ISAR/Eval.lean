import ISAR.Kernel
import ISAR.InvariantLayer

/-!
# Eval — computable reduce surface

`#eval` / `#guard` wrappers on the already-computable `cd` and `cd_loop_fuel`.
Imports **only** Kernel + InvariantLayer (no holonomic weight).

Helpers make it easy to build `ISKSubtype` values without manual proofs.
-/

namespace ISAR

/-! ### ISKSubtype smart constructors -/

def isk_norm : ISKSubtype := ⟨.norm, .norm⟩
def isk_konst : ISKSubtype := ⟨.konst, .konst⟩
def isk_s : ISKSubtype := ⟨.sₛ, .sₛ⟩

def isk_app (f x : ISKSubtype) : ISKSubtype :=
  ⟨.app f.val x.val, .app f.property x.property⟩

infixl:70 " ⬝ " => isk_app

instance : Repr ISKSubtype where
  reprPrec t p := reprPrec t.val p

/-! ### One-shot cd -/

def cd_isk (t : ISKSubtype) : ISKSubtype :=
  ⟨cd t.val, ISKTerm_cd t.property⟩

/-! ### Fuelled reduce (cd strategy) -/

def reduce_cd (fuel : Nat) (t : ISKSubtype) : ISKSubtype :=
  cd_loop_fuel fuel t

/-! ### Golden terms -/

/-- I x → x -/
def gold_Ix : ISKSubtype := isk_norm ⬝ isk_konst  -- I K → K

/-- K x y → x -/
def gold_Kxy : ISKSubtype := isk_konst ⬝ isk_s ⬝ isk_norm  -- K S I → S

/-- S K K x → x  (SKK is identity) -/
def gold_SKKx : ISKSubtype := isk_s ⬝ isk_konst ⬝ isk_konst ⬝ isk_norm
  -- S K K I → I

/-- S (K S) K  — the B combinator (composition) -/
def gold_B : ISKSubtype := isk_s ⬝ (isk_konst ⬝ isk_s) ⬝ isk_konst

/-- B f g x = f (g x) -/
def gold_Bfgx : ISKSubtype :=
  gold_B ⬝ isk_konst ⬝ isk_norm ⬝ isk_s  -- B K I S → K (I S) → K S

/-! ### #eval demonstrations -/

#eval cd_isk gold_Ix         -- should show konst
#eval reduce_cd 10 gold_Kxy  -- should show sₛ
#eval reduce_cd 10 gold_SKKx -- should show norm (I)
#eval reduce_cd 20 gold_Bfgx -- should show app konst sₛ  (K S)

/-! ### #guard (compile-time checked) -/

#guard (reduce_cd 10 gold_Ix).val == .konst
#guard (reduce_cd 10 gold_Kxy).val == .sₛ
#guard (reduce_cd 10 gold_SKKx).val == .norm
#guard (reduce_cd 20 gold_Bfgx).val == ITerm.app .konst .sₛ

end ISAR
