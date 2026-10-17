import ISAR.BytecodeView

/-!
# FlowView — the Koru flow dialect

A `Dialect` instance whose `Object` is a Koru flow program —
`graph × entry × args` in the FlowKernel grammar (ported here as
`KVal`/`KExpr`/`KArmNode`/`KArm`/`KFlow`/`KCallable`/`KProg`, the
wire-expressible subset: floats travel as rational `num/den` pairs,
matching the claim wire).

Like `BytecodeView`, `Obs` is the quotient of the carrier under
"encodings are OperEq-equal" — the substrate's reduction IS the
semantic carrier the dialect design calls for. `preserves` is the
round trip `decode ⟦encode p⟧ = ⟦p⟧`, which reduces to
`decode_raw ∘ trs_encode = id`. The genuinely new content is the
codec: `encProg`/`decProg` give a tagged-tree embedding of the whole
program grammar into `TTerm`, and `decProg_encProg` proves `encode`
injective — the dialect is an embedding, not a decoration.

What this prototype does NOT claim: that substrate *reduction* of the
encoded program agrees with FlowKernel `eval`. That rung needs an
ISK-level evaluator for the flow walker — the compiler-correctness
half, deferred by design.
-/

namespace ISAR

/-- Koru values — the wire-expressible FlowKernel `Val`. -/
inductive KVal where
  | int : Int → KVal
  | float : Int → Int → KVal   -- rational `num/den`, the wire's float shape
  | bool : Bool → KVal
  | str : String → KVal
  | arr : List KVal → KVal
  | cell : List (String × KVal) → KVal

/-- Binary operators, same set as FlowKernel `BinOp`. -/
inductive KBinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or | concat

/-- Unary operators, same set as FlowKernel `UnOp`. -/
inductive KUnOp where
  | not | neg

/-- Pure expressions — FlowKernel `Expr`. -/
inductive KExpr where
  | lit : KVal → KExpr
  | var : String → KExpr
  | bin : KBinOp → KExpr → KExpr → KExpr
  | un : KUnOp → KExpr → KExpr
  | cond : KExpr → KExpr → KExpr → KExpr
  | field : KExpr → String → KExpr
  | index : KExpr → KExpr → KExpr
  | builtin : String → List KExpr → KExpr

/-- Arm node kinds — FlowKernel `ArmNode`. -/
inductive KArmNode where
  | terminal : KArmNode
  | jump : String → List (String × KExpr) → KArmNode
  | invoke : String → List (String × KExpr) → KArmNode
  | produce : KExpr → KArmNode
  | retCtor : String → KExpr → KArmNode

/-- A `| branch bind? when? |> node` arm — FlowKernel `Arm`. -/
inductive KArm where
  | mk : String → Bool → Option String → Option KExpr → Option KArmNode →
      List KArm → KArm

/-- A walkable flow: optional `#label`, head invocation, arms. -/
structure KFlow where
  preLabel : Option String
  head : String × List (String × KExpr)
  arms : List KArm

/-- Callable kinds — FlowKernel `Callable`. -/
inductive KCallable where
  | bare : KExpr → KCallable
  | thunk : KCallable
  | subflow : KFlow → KCallable

/-- The dialect object: the program half of a `[flow-eval]` claim —
resolved graph, entry name, evaluated entry args. -/
structure KProg where
  graph : List (String × KCallable)
  entry : String
  args : List (String × KVal)

/-! ## Tagged-tree codec into `TTerm`

Atoms `I`/`K`/`S` plus `app` are enough: tags are `I`-chains
(`tn n`), lists are `K`-headed cons cells over an `S` nil, and every
datum is `app (tn tag) (encList children)`. The shapes are disjoint:
a tag spine never has a `K` head, a cons cell's head is `app K _`
(which fails `tagOf` unless the payload is literally `I` — caught by
checking cons first). -/

/-- Tag `n`: `I` applied to itself n times on the right. -/
def tn : Nat → TTerm
  | 0 => .I
  | n+1 => .app (tn n) .I

/-- Back out a tag — `tagOf (tn n) = some n`. -/
def tagOf : TTerm → Option Nat
  | .app t .I => (tagOf t).map (· + 1)
  | .I => some 0
  | _ => none

theorem tagOf_tn (n : Nat) : tagOf (tn n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tn, tagOf, ih]

/-- `K`-headed cons over `S` nil. -/
def encList : List TTerm → TTerm
  | [] => .S
  | x :: xs => .app (.app .K x) (encList xs)

/-- List decode — cons check is ordered before anything else so the
`app K _` head can never be mistaken for a node tag. -/
def decList : TTerm → Option (List TTerm)
  | .S => some []
  | .app (.app .K x) xs => (decList xs).map (x :: ·)
  | _ => none

theorem decList_encList (xs : List TTerm) : decList (encList xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encList, decList, ih]

/-- A tagged node: `app (tn tag) childrenList`. -/
def node (tag : Nat) (kids : List TTerm) : TTerm :=
  .app (tn tag) (encList kids)

/-- Decode a node — `(tag, children)`. `app (app K _) _` (a cons cell)
and non-tag heads fail. -/
def decNode : TTerm → Option (Nat × List TTerm)
  | .app f a => (tagOf f).bind fun i => (decList a).map (i, ·)
  | _ => none

theorem decNode_node (tag : Nat) (kids : List TTerm) :
    decNode (node tag kids) = some (tag, kids) := by
  simp [node, decNode, tagOf_tn, decList_encList]

/-- Zigzag: `i ↦ 2i` (nonneg) or `2(-i-1)+1` (negative). -/
def zigzag : Int → Nat
  | i => if i < 0 then 2 * Int.natAbs (-i - 1) + 1 else 2 * Int.natAbs i

/-- Inverse zigzag: even `n` is `n/2`, odd `n` is `-((n+1)/2)`. -/
def unzigzag : Nat → Int
  | n => if n % 2 = 0 then Int.ofNat (n / 2) else -Int.ofNat ((n + 1) / 2)

theorem unzigzag_two_mul (n : Nat) : unzigzag (2 * n) = Int.ofNat n := by
  unfold unzigzag
  rw [if_pos (by omega)]
  congr 1
  omega

theorem unzigzag_two_mul_add_one (n : Nat) :
    unzigzag (2 * n + 1) = -Int.ofNat (n + 1) := by
  unfold unzigzag
  rw [if_neg (by omega)]
  have : (2 * n + 1 + 1) / 2 = n + 1 := by omega
  rw [this]

theorem unzigzag_zigzag (i : Int) : unzigzag (zigzag i) = i := by
  unfold zigzag
  by_cases h : i < 0
  · rw [if_pos h, unzigzag_two_mul_add_one]
    have habs : ((-i - 1).natAbs : Int) = -i - 1 :=
      Int.natAbs_of_nonneg (by omega)
    have h2 : ((-i).natAbs : Int) = -i := Int.natAbs_of_nonneg (by omega)
    have key : (-i - 1).natAbs + 1 = (-i).natAbs := by omega
    rw [key]
    have h3 : Int.ofNat ((-i).natAbs) = -i := Int.natAbs_of_nonneg (by omega)
    rw [h3]
    omega
  · rw [if_neg h, unzigzag_two_mul]
    simpa using Int.natAbs_of_nonneg (by omega : (0 : Int) ≤ i)

/-! ## Tagged-tree codec: `KProg ↔ TTerm`

Payload conventions: nats/chars/bools/ints encode as bare `tn`-cells
(`encIntT` uses zigzag); strings encode as `encList` of char cells;
`Option` encodes as `node 23 []` / `node 24 [x]`; named pairs are
`node 7` (KVal), `node 21` (KExpr), `node 31` (KCallable). -/

def encIntT (i : Int) : TTerm := tn (zigzag i)
def encCharT (c : Char) : TTerm := tn c.toNat
def encStrT (s : String) : TTerm := encList (s.toList.map encCharT)
def encBoolT (b : Bool) : TTerm := tn (if b then 1 else 0)
def encOptT : Option TTerm → TTerm
  | none => node 23 []
  | some t => node 24 [t]

def encBinOpN : KBinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
  | .eq => 5 | .ne => 6 | .lt => 7 | .le => 8 | .gt => 9 | .ge => 10
  | .and => 11 | .or => 12 | .concat => 13

def encUnOpN : KUnOp → Nat
  | .neg => 0 | .not => 1

mutual
def encVal : KVal → TTerm
  | .int i => node 1 [encIntT i]
  | .float n d => node 2 [encIntT n, encIntT d]
  | .bool b => node 3 [encBoolT b]
  | .str s => node 4 [encStrT s]
  | .arr xs => node 5 [encValList xs]
  | .cell fs => node 6 [encNamedValList fs]

def encValList : List KVal → TTerm
  | [] => .S
  | x :: xs => .app (.app .K (encVal x)) (encValList xs)

def encNamedValList : List (String × KVal) → TTerm
  | [] => .S
  | (n, v) :: xs =>
      .app (.app .K (node 7 [encStrT n, encVal v])) (encNamedValList xs)
end

mutual
def encExpr : KExpr → TTerm
  | .lit v => node 8 [encVal v]
  | .var n => node 9 [encStrT n]
  | .bin op l r => node 10 [tn (encBinOpN op), encExpr l, encExpr r]
  | .un op e => node 11 [tn (encUnOpN op), encExpr e]
  | .cond c t e => node 12 [encExpr c, encExpr t, encExpr e]
  | .field o n => node 13 [encExpr o, encStrT n]
  | .index o i => node 14 [encExpr o, encExpr i]
  | .builtin n args => node 15 [encStrT n, encExprList args]

def encExprList : List KExpr → TTerm
  | [] => .S
  | x :: xs => .app (.app .K (encExpr x)) (encExprList xs)

def encNamedExprs : List (String × KExpr) → TTerm
  | [] => .S
  | (n, e) :: xs =>
      .app (.app .K (node 21 [encStrT n, encExpr e])) (encNamedExprs xs)
end

def encArmNode : KArmNode → TTerm
  | .terminal => node 16 []
  | .jump t args => node 17 [encStrT t, encNamedExprs args]
  | .invoke t args => node 18 [encStrT t, encNamedExprs args]
  | .produce e => node 19 [encExpr e]
  | .retCtor c e => node 20 [encStrT c, encExpr e]

mutual
def encArm : KArm → TTerm
  | .mk branch catchall bind cond n conts =>
      node 22 [encStrT branch, encBoolT catchall,
               encOptT (bind.map encStrT), encOptT (cond.map encExpr),
               encOptT (n.map encArmNode), encArmList conts]

def encArmList : List KArm → TTerm
  | [] => .S
  | a :: as => .app (.app .K (encArm a)) (encArmList as)
end

def encHead (h : String × List (String × KExpr)) : TTerm :=
  node 26 [encStrT h.1, encNamedExprs h.2]

def encFlow (f : KFlow) : TTerm :=
  node 25 [encOptT (f.preLabel.map encStrT), encHead f.head,
           encArmList f.arms]

def encCallable : KCallable → TTerm
  | .bare e => node 27 [encExpr e]
  | .thunk => node 28 []
  | .subflow f => node 29 [encFlow f]

def encCallableList : List (String × KCallable) → TTerm
  | [] => .S
  | (n, c) :: xs =>
      .app (.app .K (node 31 [encStrT n, encCallable c]))
        (encCallableList xs)

def encProg (p : KProg) : TTerm :=
  node 30 [encCallableList p.graph, encStrT p.entry,
           encNamedValList p.args]

/-! ### Decoders (fuel-bounded; `none` is the structural refusal) -/

def decIntT (t : TTerm) : Option Int := (tagOf t).map unzigzag

def decStrT (t : TTerm) : Option String := do
  let cs ← decList t
  let l ← cs.mapM fun c => (tagOf c).map Char.ofNat
  return String.ofList l

def decBoolT (t : TTerm) : Option Bool :=
  (tagOf t).bind fun n => if n = 0 then some false
                          else if n = 1 then some true else none

def decBinOpN : Nat → Option KBinOp
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .div
  | 4 => some .mod | 5 => some .eq | 6 => some .ne | 7 => some .lt
  | 8 => some .le | 9 => some .gt | 10 => some .ge | 11 => some .and
  | 12 => some .or | 13 => some .concat | _ => none

def decUnOpN : Nat → Option KUnOp
  | 0 => some .neg | 1 => some .not | _ => none

/-- `f` is a depth budget; each recursion level spends 1. -/
def decOptT {α : Type} (d : Nat → TTerm → Option α) (f : Nat) (t : TTerm)
    : Option (Option α) := do
  let (tag, kids) ← decNode t
  match tag, kids with
  | 23, [] => return none
  | 24, [x] => return some (← d f x)
  | _, _ => Option.none

/-- Decode a `node tag […]` whose single child is a TTerm list of `d`-items. -/
def decKidsOf {α : Type} (d : Nat → TTerm → Option α) (f : Nat)
    (lt : TTerm) : Option (List α) := do
  let elems ← decList lt
  elems.mapM (d f)

/-- Fuel-ignoring string decoder, for `decOptT`'s uniform shape. -/
def decStrT' (_f : Nat) (t : TTerm) : Option String := decStrT t

/-- Decode one `node 7 [encStrT n, v]` field; the payload decoder `dv`
is supplied by the caller (the cell arm passes a fuel-reduced `decValF`). -/
def decNamedValP (dv : TTerm → Option KVal) (t : TTerm)
    : Option (String × KVal) := do
  let (ptag, pkids) ← decNode t
  match ptag, pkids with
  | 7, [n, v] => return (← decStrT n, ← dv v)
  | _, _ => Option.none

def decValF : Nat → TTerm → Option KVal
  | 0, _ => none
  | f+1, t => do
    let (tag, kids) ← decNode t
    match tag, kids with
    | 1, [i] => return .int (← decIntT i)
    | 2, [n, d] => return .float (← decIntT n) (← decIntT d)
    | 3, [b] => return .bool (← decBoolT b)
    | 4, [s] => return .str (← decStrT s)
    | 5, [xs] => return .arr (← decKidsOf (fun _ e => decValF f e) f xs)
    | 6, [fs] =>
        return .cell
          (← decKidsOf (fun _ p => decNamedValP (fun v => decValF f v) p)
            f fs)
    | _, _ => Option.none
termination_by f _ => f
decreasing_by all_goals omega

def decExprF : Nat → TTerm → Option KExpr
  | 0, _ => none
  | f+1, t => do
    let (tag, kids) ← decNode t
    match tag, kids with
    | 8, [v] => return .lit (← decValF f v)
    | 9, [n] => return .var (← decStrT n)
    | 10, [o, l, r] =>
        return .bin (← (tagOf o).bind decBinOpN) (← decExprF f l)
          (← decExprF f r)
    | 11, [o, e] =>
        return .un (← (tagOf o).bind decUnOpN) (← decExprF f e)
    | 12, [c, a, b] =>
        return .cond (← decExprF f c) (← decExprF f a) (← decExprF f b)
    | 13, [o, n] => return .field (← decExprF f o) (← decStrT n)
    | 14, [o, i] => return .index (← decExprF f o) (← decExprF f i)
    | 15, [n, xs] =>
        return .builtin (← decStrT n)
          (← decKidsOf (fun _ e => decExprF f e) f xs)
    | _, _ => Option.none
termination_by f _ => f
decreasing_by all_goals omega

def decNamedExprF (f : Nat) (t : TTerm) : Option (String × KExpr) := do
  let (tag, kids) ← decNode t
  match tag, kids with
  | 21, [n, e] => return (← decStrT n, ← decExprF f e)
  | _, _ => Option.none

def decNamedExprsF (f : Nat) (lt : TTerm) : Option (List (String × KExpr)) :=
  decKidsOf decNamedExprF f lt

def decArmNodeF : Nat → TTerm → Option KArmNode
  | 0, _ => none
  | f+1, t => do
    let (tag, kids) ← decNode t
    match tag, kids with
    | 16, [] => return .terminal
    | 17, [n, xs] => return .jump (← decStrT n) (← decNamedExprsF f xs)
    | 18, [n, xs] => return .invoke (← decStrT n) (← decNamedExprsF f xs)
    | 19, [e] => return .produce (← decExprF f e)
    | 20, [c, e] => return .retCtor (← decStrT c) (← decExprF f e)
    | _, _ => Option.none

def decArmF : Nat → TTerm → Option KArm
  | 0, _ => none
  | f+1, t => do
    let (tag, kids) ← decNode t
    match tag, kids with
    | 22, [br, ca, bi, co, nd, cs] =>
        return KArm.mk (← decStrT br) (← decBoolT ca)
          (← decOptT decStrT' f bi) (← decOptT decExprF f co)
          (← decOptT decArmNodeF f nd)
          (← decKidsOf (fun _ a => decArmF f a) f cs)
    | _, _ => Option.none
termination_by f _ => f
decreasing_by all_goals omega

def decHeadF (f : Nat) (t : TTerm)
    : Option (String × List (String × KExpr)) := do
  let (tag, kids) ← decNode t
  match tag, kids with
  | 26, [n, xs] => return (← decStrT n, ← decNamedExprsF f xs)
  | _, _ => Option.none

def decFlowF (f : Nat) (t : TTerm) : Option KFlow := do
  let (tag, kids) ← decNode t
  match tag, kids with
  | 25, [lb, hd, xs] =>
      return { preLabel := ← decOptT decStrT' f lb
               head := ← decHeadF f hd
               arms := ← decKidsOf (fun _ a => decArmF f a) f xs }
  | _, _ => Option.none

def decCallableF : Nat → TTerm → Option KCallable
  | 0, _ => none
  | f+1, t => do
    let (tag, kids) ← decNode t
    match tag, kids with
    | 27, [e] => return .bare (← decExprF f e)
    | 28, [] => return .thunk
    | 29, [fl] => return .subflow (← decFlowF f fl)
    | _, _ => Option.none

def decNamedCallableF (f : Nat) (t : TTerm)
    : Option (String × KCallable) := do
  let (tag, kids) ← decNode t
  match tag, kids with
  | 31, [n, c] => return (← decStrT n, ← decCallableF f c)
  | _, _ => Option.none

def decNamedValF (f : Nat) (t : TTerm) : Option (String × KVal) :=
  decNamedValP (fun v => decValF f v) t

/-- Term size: a safe fuel bound for every decoder at this tree. -/
def tsize : TTerm → Nat
  | .I | .K | .S => 1
  | .app f a => 1 + tsize f + tsize a

def decProg (t : TTerm) : Option KProg := do
  let (tag, kids) ← decNode t
  match tag, kids with
  | 30, [ds, e, as] =>
      return { graph := ← decKidsOf decNamedCallableF (tsize t) ds
               entry := ← decStrT e
               args := ← decKidsOf decNamedValF (tsize t) as }
  | _, _ => Option.none

/-! ### Round-trip theorems

Fuel discipline: `decXF f (encX x) = some x` whenever `tsize (encX x) ≤ f`
— children of a `node` are strict subterms, so each spent level keeps the
invariant. `decProg` tops up with `tsize t`, which always suffices. -/

theorem tsize_pos (t : TTerm) : 1 ≤ tsize t := by
  cases t with
  | app f a => simp only [tsize]; omega
  | _ => simp [tsize]

theorem tsize_mem_encList {xs : List TTerm} {x : TTerm}
    (h : x ∈ xs) : tsize x < tsize (encList xs) := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
      simp only [encList, tsize]
      cases h with
      | head => omega
      | tail _ h => have := ih h; omega

theorem tsize_encList_lt_node (tag : Nat) (kids : List TTerm) :
    tsize (encList kids) < tsize (node tag kids) := by
  simp [node, tsize]

/-- Kid of a `node` is a strict subterm — the fuel invariant's workhorse. -/
theorem tsize_lt_node_of_mem {x : TTerm} {tag : Nat} {kids : List TTerm}
    (h : x ∈ kids) : tsize x < tsize (node tag kids) :=
  lt_trans (tsize_mem_encList h) (tsize_encList_lt_node tag kids)

/-- Elements of `decList`'s output are its immediate kids — encode-side
form: a member of `kids` decoded from `encList kids`. -/
theorem tsize_lt_of_mem_encList {xs : List TTerm} {x : TTerm}
    (h : x ∈ xs) : tsize x < tsize (encList xs) :=
  tsize_mem_encList h

theorem decIntT_encIntT (i : Int) : decIntT (encIntT i) = some i := by
  simp [decIntT, encIntT, tagOf_tn, unzigzag_zigzag]

theorem decBoolT_encBoolT (b : Bool) : decBoolT (encBoolT b) = some b := by
  cases b <;> simp [decBoolT, encBoolT, tagOf_tn]

theorem decStrT_encCharT (c : Char) :
    (tagOf (encCharT c)).map Char.ofNat = some c := by
  simp [encCharT, tagOf_tn, Char.ofNat_toNat]

/-- `mapM` over an encoded list returns the originals when the element
decoder round-trips pointwise. -/
theorem mapM_enc_id {α : Type} (xs : List α) (enc : α → TTerm)
    (d : TTerm → Option α)
    (h : ∀ x ∈ xs, d (enc x) = some x) :
    (xs.map enc).mapM d = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.mapM_cons]
      rw [h x List.mem_cons_self]
      simp only [bind, Option.bind]
      rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl

theorem decStrT_encStrT' (l : List Char) :
    decStrT (encList (l.map encCharT)) = some (String.ofList l) := by
  unfold decStrT
  rw [decList_encList]
  simp only [bind, Option.bind]
  rw [mapM_enc_id l encCharT _ (fun c _ => decStrT_encCharT c)]
  simp only [pure]

theorem decStrT_encStrT (s : String) : decStrT (encStrT s) = some s := by
  unfold encStrT
  rw [decStrT_encStrT', String.ofList_toList]

theorem decBinOpN_encBinOpN (op : KBinOp) :
    decBinOpN (encBinOpN op) = some op := by
  cases op <;> rfl

theorem decUnOpN_encUnOpN (op : KUnOp) :
    decUnOpN (encUnOpN op) = some op := by
  cases op <;> rfl

/-! ### Bridge: specialized list encoders are `encList ∘ map` -/

theorem encValList_eq (xs : List KVal) :
    encValList xs = encList (xs.map encVal) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encValList, encList, List.map_cons, ih]

theorem encNamedValList_eq (xs : List (String × KVal)) :
    encNamedValList xs =
      encList (xs.map fun p => node 7 [encStrT p.1, encVal p.2]) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp [encNamedValList, encList, List.map_cons, ih]

theorem encExprList_eq (xs : List KExpr) :
    encExprList xs = encList (xs.map encExpr) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encExprList, encList, List.map_cons, ih]

theorem encNamedExprs_eq (xs : List (String × KExpr)) :
    encNamedExprs xs =
      encList (xs.map fun p => node 21 [encStrT p.1, encExpr p.2]) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp [encNamedExprs, encList, List.map_cons, ih]

theorem encArmList_eq (xs : List KArm) :
    encArmList xs = encList (xs.map encArm) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [encArmList, encList, List.map_cons, ih]

theorem encCallableList_eq (xs : List (String × KCallable)) :
    encCallableList xs =
      encList (xs.map fun p => node 31 [encStrT p.1, encCallable p.2]) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp [encCallableList, encList, List.map_cons, ih]

/-! ### `decOptT` round trips -/

theorem decOptT_str (o : Option String) (f : Nat) :
    decOptT decStrT' f (encOptT (o.map encStrT)) = some o := by
  cases o <;>
    simp [decOptT, encOptT, decNode_node, Option.map, bind, Option.bind,
      decStrT', decStrT_encStrT]

/-- Generic `decOptT` round trip: decodes `node 24 [x]` when the element
decoder round-trips at this fuel. -/
theorem decOptT_enc {α : Type} {d : Nat → TTerm → Option α}
    {o : Option α} {enc : α → TTerm} {f : Nat}
    (h : ∀ x, o = some x → d f (enc x) = some x) :
    decOptT d f (encOptT (o.map enc)) = some o := by
  cases o with
  | none => simp [decOptT, encOptT, decNode_node, Option.map, bind,
      Option.bind]
  | some x =>
      have hx := h x rfl
      simp [decOptT, encOptT, decNode_node, Option.map, bind, Option.bind,
        hx]



/-! ### Round trips per grammar level

Fuel invariant: `tsize (encX x) ≤ f → decXF f (encX x) = some x`.
Children of `node tag kids` are members of `kids` and strict subterms,
so spending one fuel level preserves the bound; induction is on the
fuel so the IH applies to *any* object — which is what list elements
need (`induction` cannot run on nested inductives). -/

/-- `decKidsOf` over an encoded list, with pointwise element round trip. -/
theorem decKidsOf_encList {α : Type} {d : Nat → TTerm → Option α}
    {f : Nat} {xs : List α} {enc : α → TTerm}
    (h : ∀ x ∈ xs, d f (enc x) = some x) :
    decKidsOf d f (encList (xs.map enc)) = some xs := by
  unfold decKidsOf
  rw [decList_encList]
  exact mapM_enc_id xs enc (d f) h

/-- Element-level round trip for `decNamedValP`. -/
theorem decNamedValP_enc (n : String) (v : KVal)
    (dv : TTerm → Option KVal) (hv : dv (encVal v) = some v) :
    decNamedValP dv (node 7 [encStrT n, encVal v]) = some (n, v) := by
  unfold decNamedValP
  rw [decNode_node]
  simp only [bind, Option.bind]
  rw [decStrT_encStrT]
  simp only []
  rw [hv]
  rfl

theorem decValF_encVal : ∀ (v : KVal) (f : Nat),
    tsize (encVal v) ≤ f → decValF f (encVal v) = some v := by
  intro v f
  induction f generalizing v with
  | zero => intro hf; have := tsize_pos (encVal v); omega
  | succ f' ih =>
      intro hf
      cases v with
      | int i =>
          simp only [encVal, decValF, decNode_node, bind, Option.bind]
          rw [decIntT_encIntT]
          simp
      | float n d =>
          simp only [encVal, decValF, decNode_node, bind, Option.bind]
          rw [decIntT_encIntT, decIntT_encIntT]
          simp
      | bool b =>
          simp only [encVal, decValF, decNode_node, bind, Option.bind]
          rw [decBoolT_encBoolT]
          simp
      | str s =>
          simp only [encVal, decValF, decNode_node, bind, Option.bind]
          rw [decStrT_encStrT]
          simp
      | arr xs =>
          simp only [encVal] at hf ⊢
          have hmem : ∀ x ∈ xs, tsize (encVal x) ≤ f' := fun x hx => by
            have h1 : encVal x ∈ xs.map encVal :=
              List.mem_map.mpr ⟨x, hx, rfl⟩
            have h2 := tsize_mem_encList h1
            rw [← encValList_eq] at h2
            have h3 := tsize_lt_node_of_mem (tag := 5)
              (kids := [encValList xs]) (List.mem_singleton.mpr rfl)
            omega
          simp only [decValF, decNode_node, bind, Option.bind]
          rw [encValList_eq,
            decKidsOf_encList (d := fun _ e => decValF f' e)
              (xs := xs) (enc := encVal) (fun x hx => ih x (hmem x hx))]
          simp
      | cell fs =>
          simp only [encVal] at hf ⊢
          have hmem : ∀ p ∈ fs, tsize (encVal p.2) ≤ f' := fun p hp => by
            have h1 : node 7 [encStrT p.1, encVal p.2] ∈
                fs.map (fun q => node 7 [encStrT q.1, encVal q.2]) :=
              List.mem_map.mpr ⟨p, hp, rfl⟩
            have h2 := tsize_mem_encList h1
            rw [← encNamedValList_eq] at h2
            have h3 : tsize (encVal p.2) <
                tsize (node 7 [encStrT p.1, encVal p.2]) :=
              tsize_lt_node_of_mem (x := encVal p.2) (by simp)
            have h4 := tsize_lt_node_of_mem (tag := 6)
              (kids := [encNamedValList fs]) (List.mem_singleton.mpr rfl)
            omega
          have hpairs : ∀ p ∈ fs,
              (fun _ e => decNamedValP (fun v => decValF f' v) e) f'
                (node 7 [encStrT p.1, encVal p.2]) = some p := by
            intro p hp
            obtain ⟨n, v⟩ := p
            show decNamedValP (fun v => decValF f' v)
              (node 7 [encStrT n, encVal v]) = some (n, v)
            exact decNamedValP_enc n v _ (ih v (hmem ⟨n, v⟩ hp))
          simp only [decValF, decNode_node, bind, Option.bind]
          rw [encNamedValList_eq,
            decKidsOf_encList
              (d := fun _ e => decNamedValP (fun v => decValF f' v) e)
              (xs := fs)
              (enc := fun q => node 7 [encStrT q.1, encVal q.2]) hpairs]
          simp

theorem decExprF_encExpr : ∀ (e : KExpr) (f : Nat),
    tsize (encExpr e) ≤ f → decExprF f (encExpr e) = some e := by
  intro e f
  induction f generalizing e with
  | zero => intro hf; have := tsize_pos (encExpr e); omega
  | succ f' ih =>
      intro hf
      cases e with
      | lit v =>
          simp only [encExpr] at hf ⊢
          have hb : tsize (encVal v) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encVal v) (tag := 8)
              (kids := [encVal v]) (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind]
          rw [decValF_encVal v f' hb]
          simp
      | var n =>
          simp only [encExpr, decExprF, decNode_node, bind, Option.bind]
          rw [decStrT_encStrT]
          simp
      | bin op l r =>
          simp only [encExpr] at hf ⊢
          have hl : tsize (encExpr l) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr l) (tag := 10)
              (kids := [tn (encBinOpN op), encExpr l, encExpr r])
              (by simp)
            omega
          have hr : tsize (encExpr r) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr r) (tag := 10)
              (kids := [tn (encBinOpN op), encExpr l, encExpr r])
              (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind, tagOf_tn]
          rw [decBinOpN_encBinOpN]
          simp only []
          rw [ih l hl]
          simp only []
          rw [ih r hr]
          simp
      | un op e =>
          simp only [encExpr] at hf ⊢
          have he : tsize (encExpr e) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr e) (tag := 11)
              (kids := [tn (encUnOpN op), encExpr e])
              (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind, tagOf_tn]
          rw [decUnOpN_encUnOpN]
          simp only []
          rw [ih e he]
          simp
      | cond c a b =>
          simp only [encExpr] at hf ⊢
          have hc : tsize (encExpr c) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr c) (tag := 12)
              (kids := [encExpr c, encExpr a, encExpr b]) (by simp)
            omega
          have ha : tsize (encExpr a) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr a) (tag := 12)
              (kids := [encExpr c, encExpr a, encExpr b]) (by simp)
            omega
          have hb : tsize (encExpr b) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr b) (tag := 12)
              (kids := [encExpr c, encExpr a, encExpr b]) (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind]
          rw [ih c hc]
          simp only []
          rw [ih a ha]
          simp only []
          rw [ih b hb]
          simp
      | field o n =>
          simp only [encExpr] at hf ⊢
          have ho : tsize (encExpr o) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr o) (tag := 13)
              (kids := [encExpr o, encStrT n]) (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind]
          rw [ih o ho]
          simp only []
          rw [decStrT_encStrT]
          simp
      | index o i =>
          simp only [encExpr] at hf ⊢
          have ho : tsize (encExpr o) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr o) (tag := 14)
              (kids := [encExpr o, encExpr i]) (by simp)
            omega
          have hi : tsize (encExpr i) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr i) (tag := 14)
              (kids := [encExpr o, encExpr i]) (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind]
          rw [ih o ho]
          simp only []
          rw [ih i hi]
          simp
      | builtin n args =>
          simp only [encExpr] at hf ⊢
          have hmem : ∀ x ∈ args, tsize (encExpr x) ≤ f' := fun x hx => by
            have h1 : encExpr x ∈ args.map encExpr :=
              List.mem_map.mpr ⟨x, hx, rfl⟩
            have h2 := tsize_mem_encList h1
            rw [← encExprList_eq] at h2
            have h3 := tsize_lt_node_of_mem (x := encExprList args)
              (tag := 15) (kids := [encStrT n, encExprList args]) (by simp)
            omega
          simp only [decExprF, decNode_node, bind, Option.bind]
          rw [decStrT_encStrT]
          simp only []
          rw [encExprList_eq,
            decKidsOf_encList (d := fun _ e => decExprF f' e)
              (xs := args) (enc := encExpr) (fun x hx => ih x (hmem x hx))]
          simp

/-! ### Remaining grammar levels -/

/-- Element round trip for a node-21 named expression. -/
theorem decNamedExprF_enc (n : String) (e : KExpr) (f : Nat)
    (he : decExprF f (encExpr e) = some e) :
    decNamedExprF f (node 21 [encStrT n, encExpr e]) = some (n, e) := by
  unfold decNamedExprF
  rw [decNode_node]
  simp only [bind, Option.bind]
  rw [decStrT_encStrT]
  simp only []
  rw [he]
  rfl

/-- `decNamedExprsF` over an encoded named-expression list. -/
theorem decNamedExprsF_enc (xs : List (String × KExpr)) (f : Nat)
    (h : ∀ p ∈ xs, tsize (encExpr p.2) ≤ f) :
    decNamedExprsF f (encNamedExprs xs) = some xs := by
  unfold decNamedExprsF
  rw [encNamedExprs_eq]
  exact decKidsOf_encList
    (d := decNamedExprF) (xs := xs)
    (enc := fun p => node 21 [encStrT p.1, encExpr p.2])
    (fun p hp => by
      obtain ⟨n, e⟩ := p
      show decNamedExprF f (node 21 [encStrT n, encExpr e])
        = some (n, e)
      exact decNamedExprF_enc n e f
        (decExprF_encExpr e f (h ⟨n, e⟩ hp)))

/-- Element bound inside an encoded named-expression list. -/
theorem expr_bound_of_namedExprs {xs : List (String × KExpr)}
    {p : String × KExpr} (hp : p ∈ xs) :
    tsize (encExpr p.2) < tsize (encNamedExprs xs) := by
  have h1 := tsize_lt_node_of_mem (x := encExpr p.2) (tag := 21)
    (kids := [encStrT p.1, encExpr p.2]) (by simp)
  have h2 : node 21 [encStrT p.1, encExpr p.2] ∈
      xs.map (fun q => node 21 [encStrT q.1, encExpr q.2]) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have h3 := tsize_mem_encList h2
  rw [← encNamedExprs_eq] at h3
  omega

theorem decArmNodeF_encArmNode : ∀ (a : KArmNode) (f : Nat),
    tsize (encArmNode a) ≤ f → decArmNodeF f (encArmNode a) = some a := by
  intro a f
  cases f with
  | zero => intro hf; have := tsize_pos (encArmNode a); omega
  | succ f' =>
      intro hf
      cases a with
      | terminal =>
          simp [encArmNode, decArmNodeF, decNode_node]
      | jump n args =>
          simp only [encArmNode] at hf ⊢
          have hmem : ∀ p ∈ args, tsize (encExpr p.2) ≤ f' :=
            fun p hp => by
              have h4 := tsize_lt_node_of_mem (x := encNamedExprs args)
                (tag := 17)
                (kids := [encStrT n, encNamedExprs args]) (by simp)
              have h5 := expr_bound_of_namedExprs hp
              omega
          simp only [decArmNodeF, decNode_node, bind, Option.bind]
          rw [decStrT_encStrT]
          simp only []
          rw [decNamedExprsF_enc args f' hmem]
          simp
      | invoke n args =>
          simp only [encArmNode] at hf ⊢
          have hmem : ∀ p ∈ args, tsize (encExpr p.2) ≤ f' :=
            fun p hp => by
              have h4 := tsize_lt_node_of_mem (x := encNamedExprs args)
                (tag := 18)
                (kids := [encStrT n, encNamedExprs args]) (by simp)
              have h5 := expr_bound_of_namedExprs hp
              omega
          simp only [decArmNodeF, decNode_node, bind, Option.bind]
          rw [decStrT_encStrT]
          simp only []
          rw [decNamedExprsF_enc args f' hmem]
          simp
      | produce e =>
          simp only [encArmNode] at hf ⊢
          have hb : tsize (encExpr e) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr e) (tag := 19)
              (kids := [encExpr e]) (List.mem_singleton.mpr rfl)
            omega
          simp only [decArmNodeF, decNode_node, bind, Option.bind]
          rw [decExprF_encExpr e f' hb]
          simp
      | retCtor c e =>
          simp only [encArmNode] at hf ⊢
          have hb : tsize (encExpr e) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr e) (tag := 20)
              (kids := [encStrT c, encExpr e]) (by simp)
            omega
          simp only [decArmNodeF, decNode_node, bind, Option.bind]
          rw [decStrT_encStrT]
          simp only []
          rw [decExprF_encExpr e f' hb]
          simp

theorem decArmF_encArm : ∀ (a : KArm) (f : Nat),
    tsize (encArm a) ≤ f → decArmF f (encArm a) = some a := by
  intro a f
  induction f generalizing a with
  | zero => intro hf; have := tsize_pos (encArm a); omega
  | succ f' ih =>
      intro hf
      obtain ⟨br, ca, bi, co, nd, cs⟩ := a
      simp only [encArm] at hf ⊢
      have hbound (t : TTerm) (ht : t ∈
          [encStrT br, encBoolT ca, encOptT (bi.map encStrT),
           encOptT (co.map encExpr), encOptT (nd.map encArmNode),
           encArmList cs]) : tsize t < f' + 1 := by
        have := tsize_lt_node_of_mem (tag := 22)
          (kids := [encStrT br, encBoolT ca, encOptT (bi.map encStrT),
            encOptT (co.map encExpr), encOptT (nd.map encArmNode),
            encArmList cs]) ht
        omega
      have hco : decOptT decExprF f' (encOptT (co.map encExpr))
          = some co := by
        apply decOptT_enc
        intro x hx
        have hmap : encOptT (co.map encExpr) = node 24 [encExpr x] := by
          rw [hx]; rfl
        have h1 := tsize_lt_node_of_mem (x := encExpr x) (tag := 24)
          (kids := [encExpr x]) (List.mem_singleton.mpr rfl)
        rw [← hmap] at h1
        have h2 := hbound (encOptT (co.map encExpr)) (by simp)
        exact decExprF_encExpr x f' (by omega)
      have hnd : decOptT decArmNodeF f' (encOptT (nd.map encArmNode))
          = some nd := by
        apply decOptT_enc
        intro x hx
        have hmap : encOptT (nd.map encArmNode)
            = node 24 [encArmNode x] := by
          rw [hx]; rfl
        have h1 := tsize_lt_node_of_mem (x := encArmNode x) (tag := 24)
          (kids := [encArmNode x]) (List.mem_singleton.mpr rfl)
        rw [← hmap] at h1
        have h2 := hbound (encOptT (nd.map encArmNode)) (by simp)
        exact decArmNodeF_encArmNode x f' (by omega)
      have hcs : ∀ a' ∈ cs, decArmF f' (encArm a') = some a' := by
        intro a' ha'
        apply ih a'
        have h1 : encArm a' ∈ cs.map encArm :=
          List.mem_map.mpr ⟨a', ha', rfl⟩
        have h2 := tsize_mem_encList h1
        rw [← encArmList_eq] at h2
        have h3 := hbound (encArmList cs) (by simp)
        omega
      simp only [decArmF, decNode_node, bind, Option.bind]
      rw [decStrT_encStrT]
      simp only []
      rw [decBoolT_encBoolT]
      simp only []
      rw [decOptT_str]
      simp only []
      rw [hco]
      simp only []
      rw [hnd]
      simp only []
      rw [encArmList_eq,
        decKidsOf_encList (d := fun _ a => decArmF f' a) (xs := cs)
          (enc := encArm) hcs]
      simp

theorem decHeadF_enc (n : String) (es : List (String × KExpr)) (f : Nat)
    (hb : ∀ p ∈ es, tsize (encExpr p.2) ≤ f) :
    decHeadF f (encHead (n, es)) = some (n, es) := by
  unfold decHeadF encHead
  rw [decNode_node]
  simp only [bind, Option.bind]
  rw [decStrT_encStrT]
  simp only []
  rw [decNamedExprsF_enc es f hb]
  rfl

theorem decFlowF_encFlow (fl : KFlow) (f : Nat)
    (hf : tsize (encFlow fl) ≤ f) :
    decFlowF f (encFlow fl) = some fl := by
  obtain ⟨pl, hd, arms⟩ := fl
  obtain ⟨hn, hargs⟩ := hd
  simp only [encFlow] at hf ⊢
  have heq : encHead (hn, hargs)
      = node 26 [encStrT hn, encNamedExprs hargs] := rfl
  have hhead : decHeadF f (encHead (hn, hargs)) = some (hn, hargs) := by
    apply decHeadF_enc
    intro p hp
    have h3 := expr_bound_of_namedExprs hp
    have h3b := tsize_lt_node_of_mem (x := encNamedExprs hargs)
      (tag := 26) (kids := [encStrT hn, encNamedExprs hargs])
      (by simp)
    rw [← heq] at h3b
    have h4 := tsize_lt_node_of_mem (x := encHead (hn, hargs))
      (tag := 25)
      (kids := [encOptT (pl.map encStrT), encHead (hn, hargs),
        encArmList arms]) (by simp)
    omega
  have harms : ∀ a' ∈ arms, decArmF f (encArm a') = some a' := by
    intro a' ha'
    apply decArmF_encArm
    have h1 : encArm a' ∈ arms.map encArm :=
      List.mem_map.mpr ⟨a', ha', rfl⟩
    have h2 := tsize_mem_encList h1
    rw [← encArmList_eq] at h2
    have h3 := tsize_lt_node_of_mem (x := encArmList arms) (tag := 25)
      (kids := [encOptT (pl.map encStrT), encHead (hn, hargs),
        encArmList arms]) (by simp)
    omega
  unfold decFlowF
  rw [decNode_node]
  simp only [bind, Option.bind]
  rw [decOptT_str]
  simp only []
  rw [hhead]
  simp only []
  rw [encArmList_eq,
    decKidsOf_encList (d := fun _ a => decArmF f a) (xs := arms)
      (enc := encArm) harms]
  rfl

theorem decCallableF_encCallable : ∀ (c : KCallable) (f : Nat),
    tsize (encCallable c) ≤ f → decCallableF f (encCallable c) = some c := by
  intro c f
  cases f with
  | zero => intro hf; have := tsize_pos (encCallable c); omega
  | succ f' =>
      intro hf
      cases c with
      | bare e =>
          simp only [encCallable] at hf ⊢
          have hb : tsize (encExpr e) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encExpr e) (tag := 27)
              (kids := [encExpr e]) (List.mem_singleton.mpr rfl)
            omega
          simp only [decCallableF, decNode_node, bind, Option.bind]
          rw [decExprF_encExpr e f' hb]
          simp
      | thunk =>
          simp [encCallable, decCallableF, decNode_node]
      | subflow fl =>
          simp only [encCallable] at hf ⊢
          have hb : tsize (encFlow fl) ≤ f' := by
            have := tsize_lt_node_of_mem (x := encFlow fl) (tag := 29)
              (kids := [encFlow fl]) (List.mem_singleton.mpr rfl)
            omega
          simp only [decCallableF, decNode_node, bind, Option.bind]
          rw [decFlowF_encFlow fl f' hb]
          simp

/-- Element round trip for a node-31 named callable. -/
theorem decNamedCallableF_enc (n : String) (c : KCallable) (f : Nat)
    (hc : decCallableF f (encCallable c) = some c) :
    decNamedCallableF f (node 31 [encStrT n, encCallable c])
      = some (n, c) := by
  unfold decNamedCallableF
  rw [decNode_node]
  simp only [bind, Option.bind]
  rw [decStrT_encStrT]
  simp only []
  rw [hc]
  rfl

/-- The headline codec theorem: a program round-trips through the
tagged-tree encoding under the `tsize` fuel bound. -/
theorem decProg_encProg (p : KProg) :
    decProg (encProg p) = some p := by
  obtain ⟨g, en, ag⟩ := p
  have heq : encProg ⟨g, en, ag⟩
      = node 30 [encCallableList g, encStrT en, encNamedValList ag] :=
    rfl
  have hg : decKidsOf decNamedCallableF (tsize (encProg ⟨g, en, ag⟩))
      (encCallableList g) = some g := by
    rw [encCallableList_eq]
    apply decKidsOf_encList
    intro q hq
    obtain ⟨n, c⟩ := q
    show decNamedCallableF (tsize (encProg ⟨g, en, ag⟩))
      (node 31 [encStrT n, encCallable c]) = some (n, c)
    apply decNamedCallableF_enc
    apply decCallableF_encCallable
    have h1 := tsize_lt_node_of_mem (x := encCallable c) (tag := 31)
      (kids := [encStrT n, encCallable c]) (by simp)
    have h2 : node 31 [encStrT n, encCallable c] ∈
        g.map (fun q' => node 31 [encStrT q'.1, encCallable q'.2]) :=
      List.mem_map.mpr ⟨⟨n, c⟩, hq, rfl⟩
    have h3 := tsize_mem_encList h2
    rw [← encCallableList_eq] at h3
    have h4 := tsize_lt_node_of_mem (x := encCallableList g) (tag := 30)
      (kids := [encCallableList g, encStrT en, encNamedValList ag])
      (by simp)
    rw [← heq] at h4
    omega
  have ha : decKidsOf decNamedValF (tsize (encProg ⟨g, en, ag⟩))
      (encNamedValList ag) = some ag := by
    rw [encNamedValList_eq]
    apply decKidsOf_encList
    intro q hq
    obtain ⟨n, v⟩ := q
    show decNamedValF (tsize (encProg ⟨g, en, ag⟩))
      (node 7 [encStrT n, encVal v]) = some (n, v)
    unfold decNamedValF
    apply decNamedValP_enc
    apply decValF_encVal
    have h1 := tsize_lt_node_of_mem (x := encVal v) (tag := 7)
      (kids := [encStrT n, encVal v]) (by simp)
    have h2 : node 7 [encStrT n, encVal v] ∈
        ag.map (fun q' => node 7 [encStrT q'.1, encVal q'.2]) :=
      List.mem_map.mpr ⟨⟨n, v⟩, hq, rfl⟩
    have h3 := tsize_mem_encList h2
    rw [← encNamedValList_eq] at h3
    have h4 := tsize_lt_node_of_mem (x := encNamedValList ag) (tag := 30)
      (kids := [encCallableList g, encStrT en, encNamedValList ag])
      (by simp)
    rw [← heq] at h4
    omega
  unfold decProg
  rw [heq, decNode_node]
  simp only [bind, Option.bind]
  rw [← heq]
  rw [hg]
  simp only []
  rw [decStrT_encStrT]
  simp only []
  rw [ha]
  rfl

/-! ### The `Dialect` instance

`Object = KProg`; the observation of a program is the OperEq-class of
its tagged-tree encoding (the same granularity TRSView uses — the tree
the substrate machine actually reduces). `decode` re-embeds a substrate
class as its canonical `TTerm`; `preserves` is the substrate's own
`decode_raw ∘ trs_encode = id`. The codec theorems above witness that
this encoding really is a faithful program format: every `KProg` is
recoverable from its tree by `decProg`. What remains unclaimed — by
design — is that SKI reduction of `encProg p` *evaluates* the flow
program the way FlowKernel does; that is the future ISK-level
evaluator rung. -/

/-- Observation: the program's encoding tree, modulo substrate equality. -/
abbrev FlowObs := TTermObs

/-- Substrate-level decode for the flow dialect: canonical tree of the
class. -/
def flow_decode (q : InvariantLayer) : FlowObs := trs_decode q

/-- `Flow_Dialect : Dialect` — a Koru program view into `TTerm`. -/
def Flow_Dialect : Dialect where
  Object := KProg
  Obs := FlowObs
  ObsEq := (· = ·)
  is_equiv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }
  eval := fun p => Quotient.mk trsObsSetoid (encProg p)
  encode := fun p => trs_encode (encProg p)
  decode := flow_decode
  preserves := by
    intro x
    change Quotient.mk trsObsSetoid
        (decode_raw (trs_encode (encProg x))) =
      Quotient.mk trsObsSetoid (encProg x)
    rw [decode_raw_trs_encode]
