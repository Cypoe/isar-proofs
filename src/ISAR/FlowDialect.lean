import ISAR.FlowView

/-!
# FlowDialect — the Koru flow semantics over the wire grammar

The second rung of the Koru dialect story. `FlowView` gave the
*encoding* (a proved tagged-tree codec `KProg ↔ TTerm`); this file
gives the *semantics* — a fuel-bounded evaluator over the same
`KVal`/`KExpr`/`KArm`/`KFlow`/`KCallable`/`KProg` grammar.

The evaluator is a faithful port of the reference kernel
(`w:/src/koru/verify/semantics/FlowKernel.lean`, itself checked
against `src/comptime_eval.zig`), renamed onto the wire-prefixed
grammar: `runK` is `run`, `KCall` is `Call`, `KOutcome` is
`Outcome`, `KOracle` is `Oracle`. The dispatch semantics are
identical:

Vendored by hash, not a lake dep: this file's claimed upstream
revision is the LF-normalized sha256 below, checked by
`host/gates/flowkernel_drift.py` (obligation `GFK`, env-gated on a
reachable koru checkout) and by koru's own `flowkernel-mirror-not-drift`
invariant row on the source side. A kernel edit fires both ends
until the delta is ported and the pin re-set in the same commit:
  upstream-sha256: d958d9e07f77b2a8cbd50e24ff87735c0f0d704ca1f6c9d71b0b96b9c9f4ecd2

  * A call result is a three-case `KResult`: tagged `{some b, _}`,
    bare `{none, some v}`, void `{none, none}` — dispatching differs
    per case, and void + arms refuses outright.
  * Tagged dispatch scans only name-equal arms; bare dispatch makes
    every arm a candidate but refuses catchall/unnamed arms on
    contact; a binding arm on a payload-less result refuses; a
    non-bool/erroring guard refuses; `false` skips.
  * `#label` jumps re-enter the loop with the jump's evaluated args;
    any other label refuses. Head args are evaluated once in a fresh
    env of the call args; arm envs are children (payload shadows,
    outer names visible).
  * Resolution order: thunk (oracle leaf) → subflow → bare.
    Unknown names refuse. The oracle is the declared trust
    boundary — leaves are asserted, control is re-decided.

Declared divergences from the zig walker (wire-level choices, each a
refusal or an exactness strengthening — never a silent guess):

  * The builtin table is extended by the emission leg: `"len"`
    (`arr → int`) and `"intToString"` (`int → str`, decimal), plus
    `"chars"` (`str → arr` of UTF-8 byte ints), `"charsToString"`
    (`arr` of byte ints `→ str`, refusing outside 0‥255 and on
    invalid UTF-8), `"charToString"` (byte int `→ str`,
    ASCII-only — refuses outside 0‥127), `"contains"`
    (`str × str → bool`, substring predicate — a membership check
    the emitter would otherwise spell as a per-char invoke loop),
    `"push"` (`arr × v → arr`, pure functional append — the
    composite constructor the dialect lacked; `{n',text}` pairs
    are `[n',text]` arrs), and `"set"` (`arr × int × v → arr`,
    pure functional update — out-of-range refuses).
    These are stdlib names
    the kernel subset did
    not carry; the extension is strictly additive — previously
    deciding programs decide identically, and only previously-
    refusing builtin calls now decide. They exist because a
    compiler program must inspect list lengths, render integers,
    and mangle/escape names, and the wire has no other way.
  * `KVal.float n d` is an exact rational pair, not IEEE. `asKRat`
    normalizes `d < 0 → (-n, -d)` and REFUSES `d = 0` — the wire
    admits a shape the kernel does not invent a meaning for.
    Rational division refuses on a zero quotient denominator; `%`
    on floats refuses (no floor/trunc-mod on unnormalized pairs).
    Comparisons cross-multiply, sound because denominators are
    normalized positive.
  * `Val.int` is unbounded `Int` — i64 wrap not modeled (same bound
    as the reference kernel).
  * `evalKProg` evaluates oracle-free by default; corpus-asserted
    thunk leaves are a per-program `KOracle` argument.

`runK_mono` is ported too — fuel is a resource cap, never a
semantics change. The remaining deferred rung is
`FlowEvalCongruent` + `flowEvalDialect` at the bottom: one
`TTerm`-resident evaluator and one result codec away from a full
`Dialect` whose `Obs` is `Option KResult`.
-/

namespace ISAR

/-! ## Field accessors for the positional `KArm`

`KArm` is a single-constructor inductive with positional fields
(matching FlowKernel `Arm`'s field order); accessor defs give the
semantic code field syntax without changing the wire grammar. -/

def KArm.branch : KArm → String | .mk b _ _ _ _ _ => b
def KArm.catchall : KArm → Bool | .mk _ c _ _ _ _ => c
def KArm.bind : KArm → Option String | .mk _ _ b _ _ _ => b
def KArm.cond : KArm → Option KExpr | .mk _ _ _ c _ _ => c
def KArm.node : KArm → Option KArmNode | .mk _ _ _ _ n _ => n
def KArm.conts : KArm → List KArm | .mk _ _ _ _ _ c => c

/- Structural value equality — oracle arg tuples match literally.
A wire float compares on its raw `num/den` pair (the walker's value
equality is structural too); `1/2` and `2/4` are different oracle
arguments even though `kfloatBin` treats them as equal rationals.
Defined here, not derived on `FlowView`: the wire grammar file is
verify-only. -/
mutual
/-- Structural equality on wire values. -/
def kvalBEq : KVal → KVal → Bool
  | .int a, .int b => a == b
  | .float n1 d1, .float n2 d2 => n1 == n2 && d1 == d2
  | .bool a, .bool b => a == b
  | .str a, .str b => a == b
  | .arr a, .arr b => kvalsBEq a b
  | .cell a, .cell b => kcellsBEq a b
  | _, _ => false

def kvalsBEq : List KVal → List KVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => kvalBEq x y && kvalsBEq xs ys
  | _, _ => false

def kcellsBEq : List (String × KVal) → List (String × KVal) → Bool
  | [], [] => true
  | (n1, v1) :: xs, (n2, v2) :: ys =>
      n1 == n2 && kvalBEq v1 v2 && kcellsBEq xs ys
  | _, _ => false
end

instance : BEq KVal := ⟨kvalBEq⟩

/-- What one call produced — the walker's `ThunkResult`, three
honest cases. -/
structure KResult where
  branch : Option String := none
  payload : Option KVal := none
deriving BEq

/-- The declaration table. -/
abbrev KGraph := List (String × KCallable)

/-- Asserted call leaves: thunk/native calls the kernel cannot
evaluate are committed as `(name, args) → result` claims — the
declared trust boundary. Control around leaves is re-decided;
leaf values are asserted. -/
abbrev KOracle := List ((String × List (String × KVal)) × KResult)

abbrev KEnv := List (String × KVal)

def KEnv.lookup (e : KEnv) (s : String) : Option KVal :=
  (e.find? (·.1 == s)).map (·.2)

/-- Fresh env of a call's named args — a callee never sees the
caller's bindings. -/
def argKEnv (args : List (String × KVal)) : KEnv := args

/-- Zig `divTrunc`/`rem`/`mod` on Ints — trunc toward zero, not
`Int.ediv`'s floor. -/
def ktdiv (a b : Int) : Int :=
  if (a < 0) != (b < 0) then -(a.natAbs / b.natAbs : Int) else (a.natAbs / b.natAbs : Int)

def ktmod (a b : Int) : Int := a - b * ktdiv a b

/-- `fmod` on Ints — floor division remainder (`@mod` parity). -/
def kfmod (a b : Int) : Int := a - b * a.fdiv b

/-- `asKRat` — the float promotion boundary. A wire float `n/d` is
an exact rational; denominators are normalized positive, and `d = 0`
refuses rather than inventing an infinity. Ints promote `i ↦ (i,1)`. -/
def asKRat : KVal → Option (Int × Int)
  | .float n d => if d == 0 then none else if d < 0 then some (-n, -d) else some (n, d)
  | .int i => some (i, 1)
  | _ => none

/-- The rational arm of the numeric tower — exact arithmetic on
`num/den` pairs. Division refuses a zero quotient denominator; `%`
refuses outright (no floor/trunc-mod is meaningful on unnormalized
pairs — a declared divergence from the walker's `fmod`). -/
def kfloatBin : KBinOp → Int × Int → Int × Int → Option KVal
  | .add, (n1, d1), (n2, d2) => some (.float (n1 * d2 + n2 * d1) (d1 * d2))
  | .sub, (n1, d1), (n2, d2) => some (.float (n1 * d2 - n2 * d1) (d1 * d2))
  | .mul, (n1, d1), (n2, d2) => some (.float (n1 * n2) (d1 * d2))
  | .div, (n1, d1), (n2, d2) =>
      if d1 * n2 == 0 then none else some (.float (n1 * d2) (d1 * n2))
  | .mod, _, _ => none
  | .eq, (n1, d1), (n2, d2) => some (.bool (n1 * d2 == n2 * d1))
  | .ne, (n1, d1), (n2, d2) => some (.bool (n1 * d2 != n2 * d1))
  | .lt, (n1, d1), (n2, d2) => some (.bool (n1 * d2 < n2 * d1))
  | .le, (n1, d1), (n2, d2) => some (.bool (n1 * d2 ≤ n2 * d1))
  | .gt, (n1, d1), (n2, d2) => some (.bool (n1 * d2 > n2 * d1))
  | .ge, (n1, d1), (n2, d2) => some (.bool (n1 * d2 ≥ n2 * d1))
  | _, _, _ => none

def evalKBin : KBinOp → KVal → KVal → Option KVal
  -- Numeric tower: a float on either side promotes both through
  -- `asKRat` (non-numbers and `d = 0` refuse → TypeMismatch).
  | op, .float n d, b => (asKRat (.float n d)).bind fun af =>
      (asKRat b).bind (kfloatBin op af)
  | op, a, .float n d => (asKRat a).bind fun af =>
      (asKRat (.float n d)).bind (kfloatBin op af)
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int a, .int b => if b == 0 then none else some (.int (ktdiv a b))
  | .mod, .int a, .int b => if b == 0 then none else some (.int (ktmod a b))
  | .eq, .int a, .int b => some (.bool (a == b))
  | .ne, .int a, .int b => some (.bool (a != b))
  | .lt, .int a, .int b => some (.bool (a < b))
  | .le, .int a, .int b => some (.bool (a ≤ b))
  | .gt, .int a, .int b => some (.bool (a > b))
  | .ge, .int a, .int b => some (.bool (a ≥ b))
  | .eq, .bool a, .bool b => some (.bool (a == b))
  | .ne, .bool a, .bool b => some (.bool (a != b))
  | .eq, .str a, .str b => some (.bool (a == b))
  | .ne, .str a, .str b => some (.bool (a != b))
  | .concat, .str a, .str b => some (.str (a ++ b))
  | _, _, _ => none

def evalKUn : KUnOp → KVal → Option KVal
  | .not, .bool b => some (.bool !b)
  | .neg, .int i => some (.int (-i))
  | .neg, .float n d => some (.float (-n) d)
  | _, _ => none

mutual
/-- Evaluate a pure expression — `and`/`or`/`cond` short-circuit the
way the walker does; field resolves on cells (last binding wins);
indexing needs an array and an in-range int. -/
def evalKE : KEnv → KExpr → Option KVal
  | _, .lit v => some v
  | env, .var s => env.lookup s
  | env, .bin .and a b =>
      match evalKE env a with
      | some (.bool false) => some (.bool false)
      | some (.bool true) =>
          match evalKE env b with
          | some (.bool r) => some (.bool r)
          | _ => none
      | _ => none
  | env, .bin .or a b =>
      match evalKE env a with
      | some (.bool true) => some (.bool true)
      | some (.bool false) =>
          match evalKE env b with
          | some (.bool r) => some (.bool r)
          | _ => none
      | _ => none
  | env, .cond c t e =>
      match evalKE env c with
      | some (.bool true) => evalKE env t
      | some (.bool false) => evalKE env e
      | _ => none
  | env, .field obj name =>
      match evalKE env obj with
      | some (.cell fields) =>
          (fields.reverse.find? (·.1 == name)).map (·.2)
      | _ => none
  | env, .index obj idx =>
      match evalKE env obj, evalKE env idx with
      | some (.arr items), some (.int i) =>
          if i < 0 || items.length ≤ i.toNat then none else items[i.toNat]?
      | _, _ => none
  | env, .builtin name args => evalKBuiltin env name args
  | env, .bin op a b =>
      match evalKE env a, evalKE env b with
      | some x, some y => evalKBin op x y
      | _, _ => none
  | env, .un op a =>
      match evalKE env a with
      | some x => evalKUn op x
      | _ => none

/-- The builtin table over UNEVALUATED args — name first, then only
the argument positions it needs (`@as`'s type name is ignored).
Anything else refuses. -/
def evalKBuiltin (env : KEnv) (name : String) (args : List KExpr) : Option KVal :=
  match name, args with
  | "as", [_, v] => evalKE env v
  | "intCast", [e] =>
      match evalKE env e with
      | some (.int i) => some (.int i)
      | _ => none
  | "truncate", [e] =>
      match evalKE env e with
      | some (.int i) => some (.int i)
      | _ => none
  | "divTrunc", [ea, eb] =>
      match evalKE env ea, evalKE env eb with
      | some (.int a), some (.int b) =>
          if b == 0 then none else some (.int (ktdiv a b))
      | _, _ => none
  | "rem", [ea, eb] =>
      match evalKE env ea, evalKE env eb with
      | some (.int a), some (.int b) =>
          if b == 0 then none else some (.int (ktmod a b))
      | _, _ => none
  | "mod", [ea, eb] =>
      match evalKE env ea, evalKE env eb with
      | some (.int a), some (.int b) =>
          if b == 0 then none else some (.int (kfmod a b))
      | _, _ => none
  -- Emission-leg extensions (additive — see header): array length,
  -- decimal rendering, and str↔byte-array views — the things a
  -- compiler program cannot otherwise do on the wire.
  | "len", [e] =>
      match evalKE env e with
      | some (.arr items) => some (.int (items.length : Int))
      | _ => none
  | "intToString", [e] =>
      match evalKE env e with
      | some (.int i) => some (.str (toString i))
      | _ => none
  | "chars", [e] =>
      match evalKE env e with
      | some (.str s) =>
          some (.arr (s.toUTF8.data.toList.map fun b => .int b.toNat))
      | _ => none
  | "charsToString", [e] =>
      match evalKE env e with
      | some (.arr xs) =>
          match xs.mapM (fun
            | .int i =>
                if 0 ≤ i && i < 256 then
                  some (UInt8.ofNat i.toNat)
                else none
            | _ => none) with
          | some bs => (String.fromUTF8? ⟨bs.toArray⟩).map .str
          | none => none
      | _ => none
  | "charToString", [e] =>
      match evalKE env e with
      | some (.int i) =>
          if 0 ≤ i && i < 128 then
            some (.str (String.ofList [Char.ofNat i.toNat]))
          else none
      | _ => none
  | "contains", [ha, ne] =>
      match evalKE env ha, evalKE env ne with
      | some (.str h), some (.str n) =>
          some (.bool (h.contains n.toSlice))
      | _, _ => none
  | "push", [a, e] =>
      match evalKE env a, evalKE env e with
      | some (.arr xs), some v => some (.arr (xs ++ [v]))
      | _, _ => none
  | "set", [a, i, e] =>
      match evalKE env a, evalKE env i, evalKE env e with
      | some (.arr xs), some (.int n), some v =>
          if 0 ≤ n && n < xs.length then
            some (.arr (xs.set n.toNat v))
          else none
      | _, _, _ => none
  | _, _ => none
end

/-- All args are NAMED and evaluated at the call site. -/
def evalKArgs (env : KEnv) : List (String × KExpr) → Option (List (String × KVal))
  | [] => some []
  | (n, e) :: rest => do
      let v ← evalKE env e
      let vs ← evalKArgs env rest
      return (n, v) :: vs

/-- What a dispatch or arm walk produced. `done` is the walker's
`.none` outcome — terminal arm, chain ended, no result. `skip` is
internal: a guard rejected this arm; it never escapes `runK`. -/
inductive KOutcome where
  | result : KResult → KOutcome
  | jump : String → List (String × KVal) → KOutcome
  | done : KOutcome
  | skip : KOutcome
deriving BEq

/-- Evaluator tasks — one function so termination and monotonicity
are single inductions. -/
inductive KCall where
  | invoke : String → List (String × KVal) → KCall
  | flow : KFlow → List (String × KVal) → KCall
  | loop : KFlow → KEnv → List (String × KVal) → KCall
  | dispatchTag : KEnv → List KArm → String → KResult → KCall
  | dispatchBare : KEnv → List KArm → KResult → KCall
  | armTry : KEnv → KArm → KResult → KCall
  | armWalk : KEnv → KArm → KResult → KCall

/-- Unwrap a nested call's outcome to its `KResult` — inner refusals
propagate, and a non-result outcome where a result is required is
malformed. -/
def asKResult : Option KOutcome → Option KResult
  | some (.result r) => some r
  | _ => none

def KGraph.lookup (g : KGraph) (name : String) : Option KCallable :=
  (g.find? (·.1 == name)).map (·.2)

def KOracle.lookup (o : KOracle) (name : String) (args : List (String × KVal)) : Option KResult :=
  (o.find? (fun ((n, as), _) => n == name && as == args)).map (·.2)

/-- Bind an arm's payload into the flow env — a binding arm on a
payload-less result refuses. -/
def bindKArmEnv (a : KArm) (env : KEnv) (r : KResult) : Option KEnv :=
  match a.bind with
  | some b => r.payload.map fun v => (b, v) :: env
  | none => some env

/-- Evaluate an arm's `when` guard under the bound env — no guard is
`true`; an erroring or non-bool guard refuses; `false` skips. -/
def evalKGuard (env : KEnv) (a : KArm) : Option Bool :=
  match a.cond with
  | none => some true
  | some c =>
      match evalKE env c with
      | some (.bool b) => some b
      | _ => none

/-- One evaluator step — every call costs one fuel. Ported from
FlowKernel `run`: identical dispatch semantics on the wire grammar. -/
def runK (g : KGraph) (o : KOracle) : (fuel : Nat) → KCall → Option KOutcome
  | 0, _ => none
  | fuel + 1, .invoke name args =>
      match KGraph.lookup g name with
      | some .thunk => (KOracle.lookup o name args).map .result
      | some (.bare e) =>
          (evalKE (argKEnv args) e).map fun v =>
            .result { branch := none, payload := some v }
      | some (.subflow fl) => runK g o fuel (.flow fl args)
      | none => none
  | fuel + 1, .flow fl callArgs =>
      match evalKArgs (argKEnv callArgs) fl.head.2 with
      | none => none
      | some hargs => runK g o fuel (.loop fl (argKEnv callArgs) hargs)
  | fuel + 1, .loop fl env hargs =>
      match runK g o fuel (.invoke fl.head.1 hargs) with
      | some (.result r) =>
          if fl.arms.isEmpty then some (.result r)
          else
            match r.branch with
            | some b =>
                match runK g o fuel (.dispatchTag env fl.arms b r) with
                | none => none
                | some (.result rr) => some (.result rr)
                | some .done => some (.result {})
                | some (.jump lbl jargs) =>
                    if fl.preLabel == some lbl
                    then runK g o fuel (.loop fl env jargs)
                    else none
                | some .skip => none
            | none =>
                match runK g o fuel (.dispatchBare env fl.arms r) with
                | none => none
                | some (.result rr) => some (.result rr)
                | some .done => some (.result {})
                | some (.jump lbl jargs) =>
                    if fl.preLabel == some lbl
                    then runK g o fuel (.loop fl env jargs)
                    else none
                | some .skip => none
      | _ => none
  | fuel + 1, .dispatchTag env arms b r =>
      match arms with
      | [] => none
      | a :: rest =>
          if a.branch != b
          then runK g o fuel (.dispatchTag env rest b r)
          else
            match runK g o fuel (.armTry env a r) with
            | none => none
            | some .skip => runK g o fuel (.dispatchTag env rest b r)
            | some o1 => some o1
  | fuel + 1, .dispatchBare env arms r =>
      match r.payload with
      | none => none
      | some _ =>
          match arms with
          | [] => none
          | a :: rest =>
              if a.catchall || a.branch == ""
              then none
              else
                match runK g o fuel (.armTry env a r) with
                | none => none
                | some .skip => runK g o fuel (.dispatchBare env rest r)
                | some o1 => some o1
  | fuel + 1, .armTry env a r =>
      match bindKArmEnv a env r with
      | none => none
      | some env' =>
          match evalKGuard env' a with
          | none => none
          | some passes =>
              if passes then runK g o fuel (.armWalk env' a r) else some .skip
  | fuel + 1, .armWalk env a _ =>
      match a.node with
      | none => some .done
      | some .terminal => some .done
      | some (.jump lbl aexprs) =>
          (evalKArgs env aexprs).map (.jump lbl)
      | some (.invoke name aexprs) =>
          match evalKArgs env aexprs with
          | none => none
          | some hargs =>
              match runK g o fuel (.invoke name hargs) with
              | some (.result r) =>
                  if a.conts.isEmpty then some (.result r)
                  else runK g o fuel (match r.branch with
                    | some b => .dispatchTag env a.conts b r
                    | none => .dispatchBare env a.conts r)
              | _ => none
      | some (.produce e) =>
          (evalKE env e).map fun v => .result { branch := none, payload := some v }
      | some (.retCtor b e) =>
          (evalKE env e).map fun v => .result { branch := some b, payload := some v }

/-- Evaluate a whole program: entry call `p.entry(p.args)` under
`p.graph` and the asserted-call oracle. `none` = refusal: unknown
callable, missing asserted leaf, unhandled branch, guard/type
error, or fuel exhausted. -/
def evalKProg (p : KProg) (o : KOracle) (fuel : Nat) : Option KResult :=
  asKResult (runK p.graph o fuel (.invoke p.entry p.args))

/-! ## Fuel monotonicity — fuel is a resource cap, never a semantics change

Ported from FlowKernel `run_mono`, structurally identical: single
`runK` ⇒ single induction over fuel; every recursive call is at
strictly smaller fuel so the IH discharges every tail call. -/

theorem runK_mono (g : KGraph) (o : KOracle) :
    ∀ (fuel : Nat) (c : KCall) (x : KOutcome),
    runK g o fuel c = some x →
    runK g o (fuel + 1) c = some x := by
  intro fuel
  induction fuel with
  | zero =>
    intro c x h
    rw [runK] at h
    exact nomatch h
  | succ f ih =>
    intro c x h
    cases c with
    | invoke name args =>
      rw [runK] at h ⊢
      cases hlk : KGraph.lookup g name with
      | none => rw [hlk] at h; exact nomatch h
      | some cb =>
        rw [hlk] at h
        cases cb with
        | thunk => exact h
        | bare e => exact h
        | subflow fl => exact ih _ _ h
    | flow fl callArgs =>
      rw [runK] at h ⊢
      cases hargs : evalKArgs (argKEnv callArgs) fl.head.2 with
      | none => rw [hargs] at h; exact nomatch h
      | some hv => rw [hargs] at h; exact ih _ _ h
    | loop fl env hargs =>
      rw [runK] at h ⊢
      cases hr : runK g o f (.invoke fl.head.1 hargs) with
      | none => rw [hr] at h; exact nomatch h
      | some o1 =>
        rw [hr] at h
        cases o1 with
        | result r =>
          rw [ih _ _ hr]
          dsimp only at h ⊢
          cases hE : fl.arms.isEmpty with
          | true => rw [hE] at h; exact h
          | false =>
            rw [hE] at h
            cases hbr : r.branch with
            | some b =>
              rw [hbr] at h
              dsimp only at h ⊢
              cases hD : runK g o f (.dispatchTag env fl.arms b r) with
              | none => rw [hD] at h; exact nomatch h
              | some o2 =>
                rw [hD] at h
                rw [ih _ _ hD]
                cases o2 with
                | result rr => exact h
                | done => exact h
                | jump lbl jargs =>
                  dsimp only at h ⊢
                  cases hl : (fl.preLabel == some lbl) with
                  | true => rw [hl] at h; exact ih _ _ h
                  | false => rw [hl] at h; exact nomatch h
                | skip => exact nomatch h
            | none =>
              rw [hbr] at h
              dsimp only at h ⊢
              cases hD : runK g o f (.dispatchBare env fl.arms r) with
              | none => rw [hD] at h; exact nomatch h
              | some o2 =>
                rw [hD] at h
                rw [ih _ _ hD]
                cases o2 with
                | result rr => exact h
                | done => exact h
                | jump lbl jargs =>
                  dsimp only at h ⊢
                  cases hl : (fl.preLabel == some lbl) with
                  | true => rw [hl] at h; exact ih _ _ h
                  | false => rw [hl] at h; exact nomatch h
                | skip => exact nomatch h
        | done => exact nomatch h
        | jump _ _ => exact nomatch h
        | skip => exact nomatch h
    | dispatchTag env arms b r =>
      cases arms with
      | nil => rw [runK] at h; exact nomatch h
      | cons a rest =>
        rw [runK] at h ⊢
        cases hE : (a.branch != b) with
        | true => rw [hE] at h; exact ih _ _ h
        | false =>
          rw [hE] at h
          cases hD : runK g o f (.armTry env a r) with
          | none => rw [hD] at h; exact nomatch h
          | some o1 =>
            rw [hD] at h
            rw [ih _ _ hD]
            cases o1 with
            | skip => exact ih _ _ h
            | _ => exact h
    | dispatchBare env arms r =>
      cases arms with
      | nil =>
        rw [runK] at h
        cases hp : r.payload with
        | none => rw [hp] at h; exact nomatch h
        | some v => rw [hp] at h; exact nomatch h
      | cons a rest =>
        rw [runK] at h ⊢
        cases hp : r.payload with
        | none => rw [hp] at h; exact nomatch h
        | some v =>
          rw [hp] at h
          dsimp only at h ⊢
          cases hE : (a.catchall || a.branch == "") with
          | true => rw [hE] at h; exact nomatch h
          | false =>
            rw [hE] at h
            cases hD : runK g o f (.armTry env a r) with
            | none => rw [hD] at h; exact nomatch h
            | some o1 =>
              rw [hD] at h
              rw [ih _ _ hD]
              cases o1 with
              | skip => exact ih _ _ h
              | _ => exact h
    | armTry env a r =>
      rw [runK] at h ⊢
      cases hb : bindKArmEnv a env r with
      | none => rw [hb] at h; exact nomatch h
      | some env' =>
        rw [hb] at h
        dsimp only at h ⊢
        cases hg : evalKGuard env' a with
        | none => rw [hg] at h; exact nomatch h
        | some p =>
          rw [hg] at h
          dsimp only at h ⊢
          cases p with
          | true => exact ih _ _ h
          | false => exact h
    | armWalk env a r =>
      rw [runK] at h ⊢
      cases hn : KArm.node a with
      | none => rw [hn] at h; exact h
      | some nd =>
        rw [hn] at h
        cases nd with
        | terminal => exact h
        | jump lbl aexprs => exact h
        | invoke name aexprs =>
          dsimp only at h ⊢
          cases ha : evalKArgs env aexprs with
          | none => rw [ha] at h; exact nomatch h
          | some hargs =>
            rw [ha] at h
            dsimp only at h ⊢
            cases hr : runK g o f (.invoke name hargs) with
            | none => rw [hr] at h; exact nomatch h
            | some o1 =>
              rw [hr] at h
              cases o1 with
              | result r =>
                rw [ih _ _ hr]
                dsimp only at h ⊢
                cases hE : a.conts.isEmpty with
                | true => rw [hE] at h; exact h
                | false =>
                  rw [hE] at h
                  cases hbr : r.branch with
                  | some b => rw [hbr] at h; exact ih _ _ h
                  | none => rw [hbr] at h; exact ih _ _ h
              | done => exact nomatch h
              | jump _ _ => exact nomatch h
              | skip => exact nomatch h
        | produce e => exact h
        | retCtor b e => exact h

/-! ## Fixtures — committed evaluations

Each `theorem` is checked at compile time: `native_decide` makes the
kernel itself evaluate the fixture — a proof, not a test. -/

/-- Bare-return impls chained through untagged dispatch: `add(a:2,b:3)`
binds `s`, `mul(x:s,y:4)` binds `t`, `-> t` produces. -/
def kArith : KProg := {
  graph := [
    ("add", .bare (.bin .add (.var "a") (.var "b")))
  , ("mul", .bare (.bin .mul (.var "x") (.var "y")))
  , ("main", .subflow {
      preLabel := none
      head := ("add", [("a", .lit (.int 2)), ("b", .lit (.int 3))])
      arms := [ .mk "any" false (some "s") none
                  (some (.invoke "mul" [("x", .var "s"), ("y", .lit (.int 4))]))
                  [ .mk "t" false (some "t") none (some (.produce (.var "t"))) [] ] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_arith :
    evalKProg kArith [] 32 == some { branch := none, payload := some (.int 20) } := by
  native_decide

/-- Tagged result constructed by `=> go v` and dispatched by name. -/
def kTag : KProg := {
  graph := [
    ("mk", .bare (.lit (.int 0)))
  , ("inner", .subflow {
      preLabel := none
      head := ("mk", [])
      arms := [ .mk "any" false none none
                  (some (.retCtor "go" (.lit (.int 5)))) [] ] })
  , ("main", .subflow {
      preLabel := none
      head := ("inner", [])
      arms := [ .mk "go" false (some "v") none (some (.produce (.var "v"))) [] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_tag :
    evalKProg kTag [] 32 == some { branch := none, payload := some (.int 5) } := by
  native_decide

/-- A failing `when` guard skips the arm; the next matching arm
fires. -/
def kWhen : KProg := {
  graph := [
    ("mk", .bare (.lit (.int 0)))
  , ("inner", .subflow {
      preLabel := none
      head := ("mk", [])
      arms := [ .mk "any" false none none
                  (some (.retCtor "go" (.lit (.int 5)))) [] ] })
  , ("main", .subflow {
      preLabel := none
      head := ("inner", [])
      arms := [ .mk "go" false (some "v")
                  (some (.bin .lt (.var "v") (.lit (.int 0))))
                  (some (.produce (.lit (.int 99)))) []
              , .mk "go" false (some "v") none (some (.produce (.var "v"))) [] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_when_skip :
    evalKProg kWhen [] 32 == some { branch := none, payload := some (.int 5) } := by
  native_decide

/-- A tagged result no arm matches refuses — arms are scanned, none
eligible, the walker fails loudly. -/
def kNoMatch : KProg := {
  graph := [
    ("mk", .bare (.lit (.int 0)))
  , ("inner", .subflow {
      preLabel := none
      head := ("mk", [])
      arms := [ .mk "any" false none none
                  (some (.retCtor "go" (.lit (.int 5)))) [] ] })
  , ("main", .subflow {
      preLabel := none
      head := ("inner", [])
      arms := [ .mk "other" false none none
                  (some (.produce (.lit (.int 9)))) [] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_nomatch : evalKProg kNoMatch [] 32 == none := by
  native_decide

/-- A type error inside an arm body refuses — `int + bool` is not a
value. -/
def kBadType : KProg := {
  graph := [ ("bad", .bare (.bin .add (.lit (.int 1)) (.lit (.bool true)))) ]
  entry := "bad"
  args := [] }

theorem evalK_typeerr : evalKProg kBadType [] 8 == none := by
  native_decide

/-- Division by zero refuses. -/
def kDivZero : KProg := {
  graph := [ ("dv", .bare (.bin .div (.lit (.int 1)) (.lit (.int 0)))) ]
  entry := "dv"
  args := [] }

theorem evalK_divzero : evalKProg kDivZero [] 8 == none := by
  native_decide

/-- Thunk calls resolve through the oracle — the kernel does not
invent native results. -/
def kThunk : KProg := {
  graph := [
    ("tick", .thunk)
  , ("main", .subflow {
      preLabel := none
      head := ("tick", [])
      arms := [ .mk "go" false (some "i") none (some (.produce (.var "i"))) [] ] }) ]
  entry := "main"
  args := [] }

def kThunkO : KOracle :=
  [ (("tick", []), { branch := some "go", payload := some (.int 5) }) ]

theorem evalK_thunk :
    evalKProg kThunk kThunkO 16 == some { branch := none, payload := some (.int 5) } := by
  native_decide

theorem evalK_thunk_unasserted : evalKProg kThunk [] 16 == none := by
  native_decide

/-- A binding arm on a payload-less result refuses — `| go i` cannot
bind what was never delivered. -/
def kVoidBind : KProg := {
  graph := [
    ("tick", .thunk)
  , ("main", .subflow {
      preLabel := none
      head := ("tick", [])
      arms := [ .mk "go" false (some "i") none (some (.produce (.var "i"))) [] ] }) ]
  entry := "main"
  args := [] }

def kVoidO : KOracle :=
  [ (("tick", []), { branch := some "go", payload := none }) ]

theorem evalK_bind_no_payload : evalKProg kVoidBind kVoidO 16 == none := by
  native_decide

/-- A catchall arm hit during bare dispatch refuses — the walker's
loud wall. -/
def kCatchBare : KProg := {
  graph := [
    ("one", .bare (.lit (.int 1)))
  , ("main", .subflow {
      preLabel := none
      head := ("one", [])
      arms := [ .mk "" true none none (some (.produce (.lit (.int 9)))) [] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_catchall_bare : evalKProg kCatchBare [] 16 == none := by
  native_decide

/-- A VOID call plus arms is a refusal — `inner`'s chain ends
terminal, the result is void, and `main`'s arm can never see it. -/
def kVoidArms : KProg := {
  graph := [
    ("mk", .bare (.lit (.int 0)))
  , ("inner", .subflow {
      preLabel := none
      head := ("mk", [])
      arms := [ .mk "x" false none none (some .terminal) [] ] })
  , ("main", .subflow {
      preLabel := none
      head := ("inner", [])
      arms := [ .mk "y" false none none (some (.produce (.lit (.int 9)))) [] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_void_arms : evalKProg kVoidArms [] 32 == none := by
  native_decide

/-- The same chain without a dispatching caller: a terminal arm ends
the chain and `.done` surfaces as a void result. -/
theorem evalK_terminal_void :
    evalKProg { kVoidArms with entry := "inner" } [] 16 ==
      some { branch := none, payload := none } := by
  native_decide

/-- A `#label` loop: `again` re-enters with the jump's evaluated
args; the oracle decides per-arg-tuple; `stop` exits. -/
def kCount : KProg := {
  graph := [
    ("tick", .thunk)
  , ("count", .subflow {
      preLabel := some "again"
      head := ("tick", [("i", .var "i")])
      arms := [ .mk "next" false none none
                  (some (.jump "again" [("i", .lit (.int 1))])) []
              , .mk "stop" false (some "v") none
                  (some (.produce (.var "v"))) [] ] })
  , ("main", .subflow {
      preLabel := none
      head := ("count", [("i", .lit (.int 0))])
      arms := [] }) ]
  entry := "main"
  args := [] }

def kCountO : KOracle :=
  [ (("tick", [("i", .int 0)]), { branch := some "next", payload := none })
  , (("tick", [("i", .int 1)]), { branch := some "stop", payload := some (.int 7) }) ]

theorem evalK_count_loop :
    evalKProg kCount kCountO 64 == some { branch := none, payload := some (.int 7) } := by
  native_decide

/-- Exact rational arithmetic on wire floats: `1/2 + 1/3 = 5/6`. -/
theorem evalK_rat_add :
    evalKE [] (.bin .add (.lit (.float 1 2)) (.lit (.float 1 3)))
      == some (.float 5 6) := by
  native_decide

/-- A zero denominator refuses at the op boundary — the wire admits
the shape, the kernel does not invent a meaning. -/
theorem evalK_rat_zero_den :
    evalKE [] (.bin .add (.lit (.float 1 0)) (.lit (.int 2))) == none := by
  native_decide

/-- The emission-leg builtins: `len` renders array length,
`intToString` renders decimals — and both refuse on wrong types. -/
theorem evalK_len :
    evalKE [] (.builtin "len" [.lit (.arr [.int 1, .int 2, .int 3])])
      == some (.int 3) := by
  native_decide

theorem evalK_itoa :
    evalKE [] (.builtin "intToString" [.lit (.int (-12))])
      == some (.str "-12") := by
  native_decide

theorem evalK_len_refuses :
    evalKE [] (.builtin "len" [.lit (.int 3)]) == none := by
  native_decide

/-! ## The deferred rung — eval congruence

`evalKProg` decides what a wire program produces. `encProg` encodes it
into the substrate. What remains unclaimed — by design, matching the
FlowView header — is that substrate *reduction* of `encProg p`
computes what `runK` computes. That claim needs a `TTerm`-resident
evaluator plus a result codec; the obligation is stated here at full
strength (agreement on refusals too), parameterized on the two future
artefacts. `flowEvalDialect` shows the shape the discharge takes:
given the evaluator, the decoder, and the congruence, a real
`Dialect` instance falls out — `Obs = Option KResult`. -/

/-- The congruence obligation, stated for an arbitrary `TTerm`
evaluator and result decoder: on every tree OperEq-equivalent to
`encProg p` (the quotient's rep-freedom, so the claim is
evaluation-stable not rep-lucky), the encoded evaluation agrees
with `evalKProg` — including refusal. -/
def FlowEvalCongruent (iskEval : TTerm → Option TTerm)
    (decRes : TTerm → Option KResult) (fuel : Nat) : Prop :=
  ∀ (p : KProg) (t : TTerm),
    trs_obs_eq t (encProg p) →
    (iskEval t).bind decRes = evalKProg p [] fuel

/-- The dialect that exists one evaluator + one decoder + one
congruence proof away: `eval` is the kernel semantics, `decode`
runs the substrate class's canonical rep through the encoded
evaluator. `preserves` reduces to the congruence applied at the
rep `Quotient.out` picks — which is exactly why the obligation is
stated over ALL equivalent trees. Noncomputable: `Quotient.out`
is a choice. -/
noncomputable def flowEvalDialect (fuel : Nat) (iskEval : TTerm → Option TTerm)
    (decRes : TTerm → Option KResult)
    (h : FlowEvalCongruent iskEval decRes fuel) : Dialect where
  Object := KProg
  Obs := Option KResult
  ObsEq := (· = ·)
  is_equiv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }
  eval := fun p => evalKProg p [] fuel
  encode := fun p => trs_encode (encProg p)
  decode := fun q =>
    (iskEval (Quotient.out (trs_decode q))).bind decRes
  preserves := by
    intro x
    show (iskEval (Quotient.out (trs_decode
        (Quotient.mk operEqSetoid (trs_encode (encProg x)))))).bind decRes
        = evalKProg x [] fuel
    have hq : trs_decode (Quotient.mk operEqSetoid (trs_encode (encProg x)))
        = Quotient.mk trsObsSetoid (encProg x) := by
      show Quotient.mk trsObsSetoid (decode_raw (trs_encode (encProg x)))
          = Quotient.mk trsObsSetoid (encProg x)
      rw [decode_raw_trs_encode]
    have hout : Quotient.mk trsObsSetoid
          (Quotient.out (trs_decode
            (Quotient.mk operEqSetoid (trs_encode (encProg x)))))
        = Quotient.mk trsObsSetoid (encProg x) := by
      rw [hq]
      exact Quotient.out_eq _
    have heq := Quotient.exact hout
    exact h x _ heq

end ISAR
