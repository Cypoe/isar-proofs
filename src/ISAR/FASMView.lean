import ISAR.BytecodeView
import ISAR.ObservationRegime

namespace ISAR

/-!
# FASM(g) view

Host `fasm_dialect.py` owns fasmg-flavored *text*. Lean presentations are the same
`List Instruction` stack programs as `BytecodeView` — one OperEq class, distinct
CoGen emit family on the host. No second β; no native assembler.
-/

/-- FASM presentation carrier (shared with bytecode VM). -/
abbrev FASMProg := List Instruction

/-- Same observational setoid as bytecode (OperEq of compiled terms). -/
abbrev fasm_obs_eq := bytecode_obs_eq
abbrev fasmObsSetoid := bytecodeObsSetoid
abbrev FASMObs := BytecodeObs

/-- Dialect instance: identical encode/decode/preserves to `Bytecode_Dialect`. -/
def FASM_Dialect : Dialect := Bytecode_Dialect

def fasmObsRegime : ObservationRegime FASMProg :=
  FASM_Dialect.observationRegime

def FASM_QuotientMapO : QuotientMapO FASMProg fasmObsRegime :=
  FASM_Dialect.toQuotientMapO

theorem FASM_Dialect_eq_Bytecode : FASM_Dialect = Bytecode_Dialect := rfl

end ISAR
