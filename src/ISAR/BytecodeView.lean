import ISAR.TRSView

namespace ISAR

/-- Stack-based VM instructions. -/
inductive Instruction : Type where
  | push_I : Instruction
  | push_K : Instruction
  | push_S : Instruction
  | app : Instruction
deriving DecidableEq, Repr

/-- Execute a list of bytecode instructions on a VM stack of TTerms. -/
def run : List Instruction → List TTerm → List TTerm
  | [], stack => stack
  | Instruction.push_I :: insts, stack => run insts (TTerm.I :: stack)
  | Instruction.push_K :: insts, stack => run insts (TTerm.K :: stack)
  | Instruction.push_S :: insts, stack => run insts (TTerm.S :: stack)
  | Instruction.app :: insts, x :: y :: stack => run insts (TTerm.app y x :: stack)
  | Instruction.app :: insts, stack => run insts (TTerm.I :: stack)

/-- Step lemmas for VM execution when the stack is concrete. -/
theorem run_app_nil (insts : List Instruction) :
    run (Instruction.app :: insts) [] = run insts [TTerm.I] := rfl

theorem run_app_one (insts : List Instruction) (x : TTerm) :
    run (Instruction.app :: insts) [x] = run insts [TTerm.I, x] := rfl

theorem run_app_two (insts : List Instruction) (x y : TTerm) (stack : List TTerm) :
    run (Instruction.app :: insts) (x :: y :: stack) = run insts (TTerm.app y x :: stack) := rfl

/-- Compile a bytecode program by running it on an empty stack and taking the top term. -/
def compile_bytecode (p : List Instruction) : TTerm :=
  match run p [] with
  | x :: _ => x
  | [] => TTerm.I

/-- Decompile a TTerm into a list of postfix stack instructions. -/
def decompile : TTerm → List Instruction
  | TTerm.I => [Instruction.push_I]
  | TTerm.K => [Instruction.push_K]
  | TTerm.S => [Instruction.push_S]
  | TTerm.app t1 t2 => decompile t1 ++ decompile t2 ++ [Instruction.app]

/-- Lemma: Executing a concatenated program corresponds to staged execution. -/
theorem run_concat (p1 p2 : List Instruction) (stack : List TTerm) :
    run (p1 ++ p2) stack = run p2 (run p1 stack) := by
  induction p1 generalizing stack with
  | nil => rfl
  | cons inst p1' ih =>
      cases inst with
      | push_I =>
          dsimp [run, List.append]
          rw [ih]
      | push_K =>
          dsimp [run, List.append]
          rw [ih]
      | push_S =>
          dsimp [run, List.append]
          rw [ih]
      | app =>
          cases stack with
          | nil =>
              dsimp [List.append]
              rw [run_app_nil, run_app_nil]
              rw [ih]
          | cons x stack' =>
              cases stack' with
              | nil =>
                  dsimp [List.append]
                  rw [run_app_one, run_app_one]
                  rw [ih]
              | cons y stack'' =>
                  dsimp [List.append]
                  rw [run_app_two, run_app_two]
                  rw [ih]

/-- Lemma: Executing a decompiled TTerm on any stack pushes the term onto the stack. -/
theorem run_decompile_eq (t : TTerm) (stack : List TTerm) :
    run (decompile t) stack = t :: stack := by
  induction t generalizing stack with
  | I => rfl
  | K => rfl
  | S => rfl
  | app t1 t2 ih1 ih2 =>
      dsimp [decompile]
      rw [run_concat, run_concat]
      rw [ih1]
      rw [ih2]
      rfl

/-- Theorem: Compiling a decompiled TTerm returns the original term. -/
theorem compile_bytecode_decompile (t : TTerm) : compile_bytecode (decompile t) = t := by
  unfold compile_bytecode
  rw [run_decompile_eq]

/-- Observational equivalence for bytecode programs (evaluating to equivalent terms). -/
def bytecode_obs_eq (p1 p2 : List Instruction) : Prop :=
  OperEq (trs_encode (compile_bytecode p1)) (trs_encode (compile_bytecode p2))

/-- Observational equivalence is a setoid. -/
def bytecode_obs_equiv : Equivalence bytecode_obs_eq where
  refl p := OperEq.refl (trs_encode (compile_bytecode p))
  symm h := OperEq.symm h
  trans h1 h2 := OperEq.trans h1 h2

/-- Decode a quotient class of the substrate into a bytecode program. -/
noncomputable def decode_bytecode (q : InvariantLayer) : List Instruction :=
  decompile (trs_decode q)

/-- The concrete `Bytecode_Dialect : Dialect` instance. -/
noncomputable def Bytecode_Dialect : Dialect where
  Object := List Instruction
  Obs := List Instruction
  ObsEq := bytecode_obs_eq
  is_equiv := bytecode_obs_equiv
  eval := id
  encode := fun p => trs_encode (compile_bytecode p)
  decode := decode_bytecode
  preserves := by
    intro x
    unfold bytecode_obs_eq decode_bytecode
    dsimp
    have h_comp : ∀ t, compile_bytecode (decompile t) = t := compile_bytecode_decompile
    rw [h_comp]
    unfold trs_decode
    have h_eq : trs_encode (decode_raw (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid (trs_encode (compile_bytecode x))))) =
                InvariantLayer.canonical_rep (Quotient.mk operEqSetoid (trs_encode (compile_bytecode x))) := by
      exact trs_encode_decode_raw _
    rw [h_eq]
    exact canonical_rep_eq (trs_encode (compile_bytecode x))

end ISAR
