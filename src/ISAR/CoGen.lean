import ISAR.ObservationRegime

namespace ISAR

/-!
# CoGen / Realize (host spine first)

Thin shapes mirroring `host/cogen.py`. Proofs of loader soundness are later;
this module records the contract so dialects (e.g. FASM) attach under \(\mathcal O\),
not as ad-hoc emit.

Bootstrap = Realize under `operEqRegime` + machine context — never InvariantLayer "IT".
-/

/-- Loader family selected by budget (host may stub simd/gpu → graph). -/
inductive LoaderFamily where
  | graph
  | fasm
  | cpu
  | simd
  | gpu
  deriving DecidableEq, Repr

/-- Budget hint for `choose` (serial → graph/fasm/cpu, …). -/
inductive Budget where
  | serial
  | parallelPartial
  | fullTile
  deriving DecidableEq, Repr

/-- Pure selection result — no dialect text. -/
structure LoaderPlan where
  family : LoaderFamily
  sourcePiece : String
  budget : Budget

/-- Realization obligation: emitted loader must preserve a declared regime. -/
structure RealizeSpec (P : Type) where
  regime : ObservationRegime P
  -- Host carries strategy / MachineContext / probes; Lean keeps the O hook.

/-- Budget → preferred family (before catalog / arch features). -/
def preferFamily : Budget → LoaderFamily
  | .serial => .graph
  | .parallelPartial => .simd
  | .fullTile => .gpu

/--
IdentityRealize: plan reuses the graph piece. Host `emit` wraps `graph.lo`.
-/
def identityLoaderPlan : LoaderPlan where
  family := .graph
  sourcePiece := "graph.lo"
  budget := .serial

/--
FasmRealize: first non-identity emit family. Host still reduces via `graph.lo`;
presentation is FASM QuotientMap (see `FASMView` / `host/fasm_dialect.py`).
-/
def fasmLoaderPlan : LoaderPlan where
  family := .fasm
  sourcePiece := "graph.lo"
  budget := .serial

theorem preferFamily_serial : preferFamily .serial = .graph := rfl

theorem fasmLoaderPlan_family : fasmLoaderPlan.family = .fasm := rfl

end ISAR
