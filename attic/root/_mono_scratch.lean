def cnBool (b : Bool) : Fin 16 := ⟨if b then 1 else 0, by split <;> omega⟩

def byteCoutB (x y : Fin 16 × Fin 16) (cn : Fin 16) : Bool :=
  decide (16 ≤ x.2.val + y.2.val
    + (if 16 ≤ x.1.val + y.1.val + cn.val then 1 else 0))

theorem byteCoutB_mono (x y : Fin 16 × Fin 16) (c : Bool) :
    byteCoutB x y (cnBool c)
      = (byteCoutB x y 0 || (byteCoutB x y 1 && c)) := by
  cases c
  case false => simp [byteCoutB, cnBool]
  case true =>
    have hle : (if 16 ≤ x.1.val + y.1.val + 0 then (1 : Nat) else 0)
        ≤ (if 16 ≤ x.1.val + y.1.val + 1 then 1 else 0) := by
      split <;> split <;> omega
    simp only [byteCoutB, Bool.and_true, cnBool, ite_true,
               Fin.val_zero, Fin.val_one]
    cases hd : decide (16 ≤ x.2.val + y.2.val
        + (if 16 ≤ x.1.val + y.1.val + 0 then 1 else 0)) <;>
      simp_all <;> omega
