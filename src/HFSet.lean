inductive HF : Type where
  | empty : HF
  | insert : HF → HF → HF
deriving DecidableEq, Repr

axiom Nat.testBit_zero_number (i : Nat) : (0 : Nat).testBit i = false
axiom Nat.testBit_shiftl (a i : Nat) : (1 <<< a).testBit i = (i == a)

def toNat : HF → Nat
  | .empty => 0
  | .insert x y => toNat y ||| (1 <<< toNat x)

def ExtEq (x y : HF) : Prop :=
  toNat x = toNat y

def Mem (x y : HF) : Prop :=
  (toNat y).testBit (toNat x) = true

def HF.pair (x y : HF) : HF :=
  HF.insert x (HF.insert y HF.empty)

def HF.union : HF → HF → HF
  | .empty, y => y
  | .insert x z, y => HF.insert x (HF.union z y)

theorem ExtEq.refl (x : HF) : ExtEq x x := rfl
theorem ExtEq.symm {x y : HF} (h : ExtEq x y) : ExtEq y x := Eq.symm h
theorem ExtEq.trans {x y z : HF} (h1 : ExtEq x y) (h2 : ExtEq y z) : ExtEq x z :=
  Eq.trans h1 h2

theorem bool_or_iff (a b : Bool) : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

theorem mem_empty_iff (z : HF) : Mem z HF.empty ↔ False := by
  unfold Mem
  dsimp [toNat]
  rw [Nat.testBit_zero_number]
  simp

theorem mem_insert (x y z : HF) : Mem z (HF.insert x y) ↔ ExtEq z x ∨ Mem z y := by
  unfold Mem
  dsimp [toNat]
  rw [Nat.testBit_or, bool_or_iff, Nat.testBit_shiftl, beq_iff_eq]
  exact Or.comm

theorem mem_pair (x y z : HF) : Mem z (HF.pair x y) ↔ ExtEq z x ∨ ExtEq z y := by
  unfold HF.pair
  rw [mem_insert, mem_insert, mem_empty_iff]
  constructor
  · intro h
    cases h with
    | inl h1 => exact Or.inl h1
    | inr h2 =>
        cases h2 with
        | inl h3 => exact Or.inr h3
        | inr h4 => contradiction
  · intro h
    cases h with
    | inl h1 => exact Or.inl h1
    | inr h2 => exact Or.inr (Or.inl h2)

theorem toNat_union (x y : HF) : toNat (HF.union x y) = toNat x ||| toNat y := by
  induction x with
  | empty =>
      unfold HF.union
      dsimp [toNat]
      exact Eq.symm (Nat.zero_or (toNat y))
  | insert a b ih_a ih_b =>
      unfold HF.union
      dsimp [toNat]
      rw [ih_b]
      rw [Nat.or_assoc, Nat.or_comm (toNat y), ← Nat.or_assoc]

theorem mem_union (x y z : HF) : Mem z (HF.union x y) ↔ Mem z x ∨ Mem z y := by
  unfold Mem
  rw [toNat_union, Nat.testBit_or, bool_or_iff]
