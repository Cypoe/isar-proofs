import ISAR.LambdaFragment
import ISAR.BasisDev
import ISAR.HeapDev

/-!
# SpecVocabulary — λ-encoded spec vocabulary and its Join laws

The faithful de Bruijn λ-encodings of `spec_term.py`'s vocabulary
(`_FOLDL`/`_REV`/`_CONSS`/`_NIL`/`_APPEND`, the `_NIBADD`/`_NIBCARRY`/
`_B2N`/`_OR`/`_AND`/`_ADDBC` byte cells, `_B4ADD` zip-ripple and
`_B4CLA` carry-lookahead) together with their observational-equivalence
laws, transported to the host basis via `translate_to_basis ∘ compile`
— the `import_tree(expand_s=True)` terms.

* `append_assoc_basis` — left- and right-nested `_APPEND` chains are
  `Join`-equivalent (the balanced-emission license).
* `b4add_b4cla_basis` — ripple and carry-lookahead adders are
  `Join`-equivalent: the two vocabularies are observationally the same
  function on every 4-byte input.

Proof architecture: head-spine β evaluator `hstep`/`hsteps` (fuel-bounded
milestones discharged by `simp`), `closed 0` side-conditions rewriting
stuck `subst`/`shift` on closed payloads, finite-enumeration nibble
dispatch tables, and `LRed` congruence composition.  Weak β has no
ξ-rule, so milestones stop before outer pair-formation while the stuck
leaf applications stay `LRed`-reachable.
-/

namespace ISAR

open Relation LTerm

-- infrastructure (shared shape with _spec_assoc_work.lean) --------------

/-- Head-only β: step the leftmost head redex down the function spine;
    never descends into arguments; identity where no head redex. -/
def hstep : LTerm → LTerm
  | .app f x =>
      match f with
      | .abs b => subst x 0 b
      | _ => .app (hstep f) x
  | t => t

def hsteps : Nat → LTerm → LTerm
  | 0, t => t
  | n + 1, t => hsteps n (hstep t)

theorem hstep_red : ∀ t : LTerm, LRed t (hstep t) := by
  intro t
  induction t with
  | var n => exact Relation.ReflTransGen.refl
  | abs b => exact Relation.ReflTransGen.refl
  | app f x ihf _ =>
      cases f with
      | abs b => exact Relation.ReflTransGen.single (LStep.beta b x)
      | var n => exact Relation.ReflTransGen.refl
      | app f1 x1 => exact LRed_app_left ihf

theorem hsteps_red : ∀ (n : Nat) (t : LTerm), LRed t (hsteps n t) := by
  intro n
  induction n with
  | zero => intro t; exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro t
      exact (hstep_red t).trans (ih (hstep t))

/-- Certificate discharge: `hsteps k t = u` gives `LRed t u`. -/
theorem LRed_of_hsteps {t u : LTerm} {k : Nat} (h : hsteps k t = u) :
    LRed t u := h ▸ hsteps_red k t

/-- All free de Bruijn indices below `c`. -/
def closed : Nat → LTerm → Bool
  | c, .var n => decide (n < c)
  | c, .abs b => closed (c + 1) b
  | c, .app f x => closed c f && closed c x

theorem closed_mono {t : LTerm} {c c' : Nat} (h : closed c t = true)
    (hc : c ≤ c') : closed c' t = true := by
  induction t generalizing c c' with
  | var n =>
      simp only [closed, decide_eq_true_eq] at h ⊢
      exact Nat.lt_of_lt_of_le h hc
  | abs b ih =>
      simp only [closed] at h ⊢
      exact ih h (Nat.succ_le_succ hc)
  | app f x ihf ihx =>
      simp only [closed, Bool.and_eq_true] at h ⊢
      exact ⟨ihf h.1 hc, ihx h.2 hc⟩

theorem shift_of_closed {t : LTerm} {c : Nat} (h : closed c t = true) (d : Nat) :
    shift d c t = t := by
  induction t generalizing c with
  | var n =>
      simp only [closed, decide_eq_true_eq] at h
      simp only [shift]
      rw [if_pos h]
  | abs b ih =>
      simp only [closed] at h
      simp only [shift, ih h]
  | app f x ihf ihx =>
      simp only [closed, Bool.and_eq_true] at h
      simp only [shift, ihf h.1, ihx h.2]

theorem subst_of_closed {t : LTerm} {c : Nat} (h : closed c t = true)
    (s : LTerm) : subst s c t = t := by
  induction t generalizing c with
  | var n =>
      simp only [closed, decide_eq_true_eq] at h
      simp only [subst]
      rw [if_pos h]
  | abs b ih =>
      simp only [closed] at h
      simp only [subst, ih h]
  | app f x ihf ihx =>
      simp only [closed, Bool.and_eq_true] at h
      simp only [subst, ihf h.1, ihx h.2]

theorem shift_of_closed0 {t : LTerm} (h : closed 0 t = true) (d c : Nat) :
    shift d c t = t :=
  shift_of_closed (closed_mono h (Nat.zero_le c)) d

theorem subst_of_closed0 {t : LTerm} (h : closed 0 t = true) (s : LTerm)
    (c : Nat) : subst s c t = t :=
  subst_of_closed (closed_mono h (Nat.zero_le c)) s

theorem closed_app {f x : LTerm} (hf : closed 0 f = true)
    (hx : closed 0 x = true) : closed 0 (.app f x) = true := by
  simp only [closed, Bool.and_eq_true]; exact ⟨hf, hx⟩

/-- Full β-normalizer for `#eval` probes only (not used in proofs).
    hsteps-to-whnf, then recurse under binders/args. -/
def norm : Nat → LTerm → LTerm
  | 0, t => t
  | fuel + 1, t =>
      match hsteps fuel t with
      | .abs b => .abs (norm fuel b)
      | .app f x => .app (norm fuel f) (norm fuel x)
      | t => t

/-- λ-level observational equivalence: common weak-β reduct. -/
def LJoin (a b : LTerm) : Prop := ∃ u, LRed a u ∧ LRed b u

-- encodings, faithful to spec_term.py ------------------------------------

/-- n nested abstractions. -/
def absN : Nat → LTerm → LTerm
  | 0, t => t
  | n + 1, t => .abs (absN n t)

/-- Left-nested application spine. -/
def aps : LTerm → List LTerm → LTerm := List.foldl .app

/-- Nibble literal: `_sel_src k = (\c0. … \c15. c_k)` — the Scott-16
    selector.  Under 16 binders c_i is `var (15-i)`. -/
def nibLit : Fin 16 → LTerm := fun i => absN 16 (.var (15 - i.val))

/-- Church booleans. -/
def klL : LTerm := .abs (.abs (.var 1))    -- K  = λx.λy. x  (true)
def kilL : LTerm := .abs (.abs (.var 0))   -- KI = λx.λy. y  (false)

def boolLit : Bool → LTerm := fun b => if b then klL else kilL

/-- Scott nil: `\n.\c. n` — the spec's `K` nil. -/
def nilL : LTerm := .abs (.abs (.var 1))

/-- Pair literal NF `\f. f a b` — equal to `PAIR·a·b`'s reduct for closed
    a, b (the shifted forms coincide). -/
def pairLit (a b : LTerm) : LTerm := .abs (.app (.app (.var 0) a) b)

/-- `_PAIR_SRC = (\k5.\v5.\f6. f6 k5 v5)`. -/
def pairSrcL : LTerm :=
  .abs (.abs (.abs (.app (.app (.var 0) (.var 2)) (.var 1))))

/-- `_CONSS = (\h2.\t2.\n2.\c2. c2 h2 t2)` — h2=3, t2=2, n2=1, c2=0. -/
def conssL : LTerm :=
  .abs (.abs (.abs (.abs (.app (.app (.var 0) (.var 3)) (.var 2)))))

/-- Byte cell: pair of nibbles (lo, hi). -/
def byteLit (lo hi : Fin 16) : LTerm := pairLit (nibLit lo) (nibLit hi)

/-- bytes4 literal: LE cons-chain of byte cells. -/
def b4Lit (xs : List (Fin 16 × Fin 16)) : LTerm :=
  xs.foldr (fun p t => .app (.app conssL (byteLit p.1 p.2)) t) nilL

/-- Scott cons-cell literal `
.\c. c h t` — NF of `CONSS·h·t`. -/
def cellLit (h t : LTerm) : LTerm :=
  .abs (.abs (.app (.app (.var 0) (shift 2 0 h)) (shift 2 0 t)))

/-- Scott list literal from cell terms. -/
def scottList (cs : List LTerm) : LTerm := cs.foldr cellLit nilL

-- nibble op tables --------------------------------------------------------

/-- `_NIBADD = (\a. \b. a A_0 … A_15)` where `A_i = b sel_{i} sel_{i+1}…`
    (indices mod 16): a picks the i-th arg, b picks the j-th within. -/
def nibAddL : LTerm :=
  .abs (.abs (aps (.var 1) (List.ofFn fun i : Fin 16 =>
    aps (.var 0) (List.ofFn fun j : Fin 16 =>
      nibLit ⟨(i.val + j.val) % 16, by omega⟩))))

/-- `_NIBCARRY = (\a. \b. a C_0 … C_15)` where `C_i`'s j-th is BT iff
    i + j ≥ 16. -/
def nibCarryL : LTerm :=
  .abs (.abs (aps (.var 1) (List.ofFn fun i : Fin 16 =>
    aps (.var 0) (List.ofFn fun j : Fin 16 =>
      boolLit (decide (16 ≤ i.val + j.val))))))

/-- `_B2N = (\b. b sel1 sel0)` — bool → nibble carry. -/
def b2nL : LTerm := .abs (aps (.var 0) [nibLit 1, nibLit 0])

/-- `_OR = (\p. \q. p K q)`. -/
def orL : LTerm := .abs (.abs (aps (.var 1) [klL, .var 0]))

/-- `_AND = (\p. \q. p q (K I))`. -/
def andL : LTerm := .abs (.abs (aps (.var 1) [.var 0, kilL]))

-- closedness of the encodings --------------------------------------------

theorem closed_absN (n : Nat) (c : Nat) (t : LTerm) :
    closed c (absN n t) = closed (c + n) t := by
  induction n generalizing c with
  | zero => simp [absN]
  | succ n ih =>
      simp only [absN, closed]
      rw [ih]; congr 1; omega

theorem closed_nibLit (i : Fin 16) : closed 0 (nibLit i) = true := by
  have hi : i.val < 16 := i.isLt
  simp only [nibLit, closed_absN, closed, decide_eq_true_eq]
  omega

theorem closed_klL : closed 0 klL = true := by decide
theorem closed_kilL : closed 0 kilL = true := by decide
theorem closed_nilL : closed 0 nilL = true := by decide
theorem closed_conssL : closed 0 conssL = true := by decide
theorem closed_pairSrcL : closed 0 pairSrcL = true := by decide
theorem closed_nibAddL : closed 0 nibAddL = true := by decide
theorem closed_nibCarryL : closed 0 nibCarryL = true := by decide
theorem closed_b2nL : closed 0 b2nL = true := by decide
theorem closed_orL : closed 0 orL = true := by decide
theorem closed_andL : closed 0 andL = true := by decide

theorem closed_boolLit (b : Bool) : closed 0 (boolLit b) = true := by
  cases b <;> decide

theorem closed_pairLit {a b : LTerm} (ha : closed 1 a = true)
    (hb : closed 1 b = true) : closed 0 (pairLit a b) = true := by
  simp only [pairLit, closed, Bool.and_eq_true]
  exact ⟨⟨rfl, ha⟩, hb⟩

theorem closed_byteLit (lo hi : Fin 16) : closed 0 (byteLit lo hi) = true :=
  closed_pairLit (closed_mono (closed_nibLit lo) (Nat.zero_le 1))
    (closed_mono (closed_nibLit hi) (Nat.zero_le 1))

theorem closed_b4Lit (xs : List (Fin 16 × Fin 16)) :
    closed 0 (b4Lit xs) = true := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      simp only [b4Lit, List.foldr_cons]
      exact closed_app (closed_app closed_conssL
        (closed_byteLit p.1 p.2)) ih

/-- shift/subst lemmas for the literal encodings — the rewrites that keep
    milestone discharge un-stuck when `nibLit i` is a neutral term. -/
theorem shift_nibLit (i : Fin 16) (d c : Nat) :
    shift d c (nibLit i) = nibLit i :=
  shift_of_closed0 (closed_nibLit i) d c

theorem subst_nibLit (i : Fin 16) (s : LTerm) (c : Nat) :
    subst s c (nibLit i) = nibLit i :=
  subst_of_closed0 (closed_nibLit i) s c

theorem shift_boolLit (b : Bool) (d c : Nat) :
    shift d c (boolLit b) = boolLit b :=
  shift_of_closed0 (closed_boolLit b) d c

theorem subst_boolLit (b : Bool) (s : LTerm) (c : Nat) :
    subst s c (boolLit b) = boolLit b :=
  subst_of_closed0 (closed_boolLit b) s c

theorem shift_byteLit (lo hi : Fin 16) (d c : Nat) :
    shift d c (byteLit lo hi) = byteLit lo hi :=
  shift_of_closed0 (closed_byteLit lo hi) d c

theorem subst_byteLit (lo hi : Fin 16) (s : LTerm) (c : Nat) :
    subst s c (byteLit lo hi) = byteLit lo hi :=
  subst_of_closed0 (closed_byteLit lo hi) s c

-- nibble table lemmas (finite-decidable dispatch) -------------------------

/-- `NIBADD` applied to nibble literals: double dispatch computes
    `(i + j) mod 16`.  Each `Fin 16` enumeration instance is concrete, so
    `hsteps` evaluates — the symbolic-quantified `LRed` follows. -/
theorem nibadd_table : ∀ i j : Fin 16,
    hsteps 64 (aps nibAddL [nibLit i, nibLit j])
      = nibLit ⟨(i.val + j.val) % 16, by omega⟩ := by
  decide

theorem nibcarry_table : ∀ i j : Fin 16,
    hsteps 64 (aps nibCarryL [nibLit i, nibLit j])
      = boolLit (decide (16 ≤ i.val + j.val)) := by
  decide

theorem nibadd_correct (i j : Fin 16) :
    LRed (aps nibAddL [nibLit i, nibLit j])
         (nibLit ⟨(i.val + j.val) % 16, by omega⟩) :=
  LRed_of_hsteps (nibadd_table i j)

theorem nibcarry_correct (i j : Fin 16) :
    LRed (aps nibCarryL [nibLit i, nibLit j])
         (boolLit (decide (16 ≤ i.val + j.val))) :=
  LRed_of_hsteps (nibcarry_table i j)

theorem b2n_correct (b : Bool) :
    LRed (.app b2nL (boolLit b))
         (nibLit (if b then 1 else 0)) := by
  cases b <;>
    exact LRed_of_hsteps (k := 8) rfl

theorem or_correct (p q : Bool) :
    LRed (aps orL [boolLit p, boolLit q]) (boolLit (p || q)) := by
  cases p <;> cases q <;>
    exact LRed_of_hsteps (k := 12) rfl

theorem and_correct (p q : Bool) :
    LRed (aps andL [boolLit p, boolLit q]) (boolLit (p && q)) := by
  cases p <;> cases q <;>
    exact LRed_of_hsteps (k := 12) rfl

-- term builders -------------------------------------------------------

/-- `(\v1. … \vn. body) vn … v1` — `_lets` as a term builder: values are
    written in the context BEFORE their binder (each sees the earlier
    lets at indices +k). -/
def letsL : List LTerm → LTerm → LTerm
  | [], body => body
  | v :: vs, body => .app (.abs (letsL vs body)) v

/-- `_peel` as a term builder: `l K (\h.\t. t K (\h'.\t'. … body))` —
    n cons-cells destructured; each tail at `var 0` of its continuation. -/
def peelK : Nat → LTerm → LTerm → LTerm
  | 0, _, body => body
  | k + 1, l, body =>
      .app (.app l klL) (.abs (.abs (peelK k (.var 0) body)))

-- byte-level ops ------------------------------------------------------------
-- `_ADDBC x y cn -> pair(byte_cell, carry_bool)`, de Bruijn translation of
--   \x.\y.\cn. x (\xl.\xh. y (\yl.\yh.
--     (\t.(\clo.(\lo.(\u.(\cn2.(\cout.(\hi.
--       PAIR (PAIR lo hi) cout) (NIBADD u cn2))
--       (OR (NC xh yh)(NC u cn2))) (B2N clo)) (NIBADD xh yh))
--       (NIBADD t cn)) (OR (NC xl yl)(NC t cn))) (NIBADD xl yl)))

/-- Binder contexts inside LETS (innermost index 0):
    λt:    t=0 yh=1 yl=2 xh=3 xl=4 cn=5
    λclo:  clo=0 t=1 yh=2 yl=3 xh=4 xl=5 cn=6
    λlo:   lo=0 clo=1 t=2 yh=3 yl=4 xh=5 xl=6 cn=7
    λu:    u=0 lo=1 clo=2 t=3 yh=4 yl=5 xh=6 xl=7 cn=8
    λcn2:  cn2=0 u=1 lo=2 clo=3 t=4 yh=5 yl=6 xh=7 xl=8 cn=9
    λcout: cout=0 cn2=1 u=2 lo=3 clo=4 t=5 yh=6 yl=7 xh=8 xl=9 cn=10
    λhi:   hi=0 cout=1 cn2=2 u=3 lo=4 clo=5 t=6 -/
def addbcL : LTerm :=
  .abs (.abs (.abs                                    -- x y cn
    (.app (.var 2)                                    -- x .
      (.abs (.abs                                     -- xl xh
        (.app (.var 3)                                -- y .
          (.abs (.abs                                 -- yl yh
            (letsL
              [aps nibAddL [.var 3, .var 1],
               aps orL [aps nibCarryL [.var 4, .var 2],
                        aps nibCarryL [.var 0, .var 5]],
               aps nibAddL [.var 1, .var 6],
               aps nibAddL [.var 5, .var 3],
               .app b2nL (.var 2),
               aps orL [aps nibCarryL [.var 7, .var 5],
                        aps nibCarryL [.var 1, .var 0]],
               aps nibAddL [.var 2, .var 1]]
              (aps pairSrcL
                [aps pairSrcL [.var 4, .var 0], .var 1]))))))))))

/-- `_B4BC x y cn -> bool` — carry half only. -/
def b4bcL : LTerm :=
  .abs (.abs (.abs                                    -- x y cn
    (.app (.var 2)                                    -- x ·
      (.abs (.abs                                     -- xl xh
        (.app (.var 3)                                -- y ·
          (.abs (.abs                                 -- yl yh
            (letsL
              [aps nibAddL [.var 3, .var 1],           -- t   := xl+yl
               aps orL [aps nibCarryL [.var 4, .var 2], -- clo := cx|ct
                        aps nibCarryL [.var 0, .var 5]],
               .app b2nL (.var 0),                    -- cn2 := B2N clo
               aps nibAddL [.var 5, .var 3]]           -- hh  := xh+yh
              (aps orL [aps nibCarryL [.var 6, .var 4],
                        aps nibCarryL [.var 0, .var 1]]))))))))))
  -- BODY (λhh): cout = OR (NC xh yh) (NC hh cn2);  hh=0 cn2=1 yh=4 xh=6

/-- `_B4BS x y cn -> byte cell` — sum half. -/
def b4bsL : LTerm :=
  .abs (.abs (.abs                                    -- x y cn
    (.app (.var 2)
      (.abs (.abs
        (.app (.var 3)
          (.abs (.abs
            (letsL
              [aps nibAddL [.var 3, .var 1],           -- t   := xl+yl
               aps orL [aps nibCarryL [.var 4, .var 2], -- clo
                        aps nibCarryL [.var 0, .var 5]],
               aps nibAddL [.var 1, .var 6],           -- lo  := t+cn
               .app b2nL (.var 1),                    -- cn2 := B2N clo
               aps nibAddL [.var 6, .var 4]]           -- hh  := xh+yh
              (aps pairSrcL
                [.var 2, aps nibAddL [.var 0, .var 1]]))))))))))
  -- BODY (λhh): PAIR lo (NIBADD hh cn2);  hh=0 cn2=1 lo=2

-- fold machinery (same encoding as _spec_assoc_work.lean) ----------------------

/-- fold step `s = \a.\h. CONSS·h·a` (shared by `_REV`). -/
def stepConsL : LTerm :=
  .abs (.abs (.app (.app conssL (.var 0)) (.var 1)))

/-- `G st = \g.\l2.\a2. l2 a2 (\h.\t. g g t (st a2 h))`. -/
def foldG (st : LTerm) : LTerm :=
  .abs (.abs (.abs (.app (.app (.var 1) (.var 0))
    (.abs (.abs (.app
      (.app (.app (.var 4) (.var 4)) (.var 0))
      (.app (.app (shift 5 0 st) (.var 2)) (.var 1))))))))

/-- `W = \f. f f` -/
def wl : LTerm := .abs (.app (.var 0) (.var 0))

/-- `_FOLDL = \st.\l.\a. W·(G st)·l·a` -/
def foldlL : LTerm :=
  .abs (.abs (.abs (.app (.app (.app wl (foldG (.var 2))) (.var 1))
    (.var 0))))

/-- `_REV = \l. FOLDL·stepCons·l·K` -/
def revL : LTerm := .abs (aps foldlL [stepConsL, .var 0, klL])

-- bytes4 ripple (_B4ADD) -------------------------------------------------------

/-- The zip-ripple step:
    `\acc.\x. acc (\bl.\cs. cs (\cy.\ou. bl K (\hb.\tb.
      (ADDBC x hb cy) (\c.\s. PAIR tb (PAIR (B2N s) (CONSS c ou))))))`
    Binder indices:
    λacc.λx: x=0 acc=1 | λbl.λcs: cs=0 bl=1 x=2 | λcy.λou: ou=0 cy=1 bl=3 x=4
    λhb.λtb: tb=0 hb=1 ou=2 cy=3 x=6 | λc.λs: s=0 c=1 tb=2 ou=4. -/
def b4stepL : LTerm :=
  .abs (.abs
    (.app (.var 1)
      (.abs (.abs
        (.app (.var 0)
          (.abs (.abs
            (.app (.app (.var 3) klL)
              (.abs (.abs
                (.app (aps addbcL [.var 6, .var 1, .var 3])
                  (.abs (.abs
                    (aps pairSrcL
                      [.var 2,
                       aps pairSrcL [.app b2nL (.var 0),
                                     aps conssL [.var 1, .var 4]]]))))))))))))))

/-- fin = `\bl.\cs. cs (\cy.\ou. REV ou)`. -/
def b4finL : LTerm :=
  .abs (.abs (.app (.var 0) (.abs (.abs (.app revL (.var 0))))))

/-- `_B4ADD = \a.\b. (FOLDL·st·a·init)·fin`,
    init = `prs b (prs sel0 K)`. -/
def b4addL : LTerm :=
  .abs (.abs (.app
    (aps foldlL [b4stepL, .var 1,
      aps pairSrcL [.var 0, aps pairSrcL [nibLit 0, klL]]])
    b4finL))

-- bytes4 carry-lookahead (_B4CLA) ----------------------------------------------

/-- `_B4CLA = \a.\b. peel a·4 (peel b·4 (lets [g0,p0,g1,p1,g2,p2,c2,c3]
    (conss s0 …)))`.  At the lets level (16 peel binders):
    a-cells a_k = 15−2k (a0=15…a3=9), b-cells b_k = 7−2k (b0=7…b3=1). -/
def b4claL : LTerm :=
  .abs (.abs
    (peelK 4 (.var 1)
      (peelK 4 (.var 8)
        (letsL
          [aps b4bcL [.var 15, .var 7, nibLit 0],      -- g0
           aps b4bcL [.var 16, .var 8, nibLit 1],      -- p0
           aps b4bcL [.var 15, .var 7, nibLit 0],      -- g1
           aps b4bcL [.var 16, .var 8, nibLit 1],      -- p1
           aps b4bcL [.var 15, .var 7, nibLit 0],      -- g2
           aps b4bcL [.var 16, .var 8, nibLit 1],      -- p2
           aps orL [.var 3,
                    aps andL [.var 2, .var 5]],         -- c2 = g1|p1&g0
           aps orL [.var 2,                             -- c3 = g2|p2&c2x
                    aps andL [.var 1,
                      aps orL [.var 4,
                               aps andL [.var 3, .var 6]]]]]
          (aps conssL [aps b4bsL [.var 23, .var 15, nibLit 0],
            aps conssL [aps b4bsL [.var 21, .var 13,
                                   .app b2nL (.var 7)],
              aps conssL [aps b4bsL [.var 19, .var 11,
                                     .app b2nL (.var 1)],
                aps conssL [aps b4bsL [.var 17, .var 9,
                                       .app b2nL (.var 0)],
                            klL]]]])))))

-- sanity probes on concrete bytes --------------------------------------------

/-- Byte value: `lo + 16*hi`. -/
def byteVal (lo hi : Fin 16) : Nat := lo.val + 16 * hi.val

/-- Expected ADDBC result as (lo, hi, cout). -/
def addbcSpec (xl xh yl yh cn : Fin 16) : Fin 16 × Fin 16 × Bool :=
  let s := xl.val + yl.val + cn.val
  let clo := 16 ≤ s
  let lo : Fin 16 := ⟨s % 16, Nat.mod_lt _ (by omega)⟩
  let hsum := xh.val + yh.val + (if clo then 1 else 0)
  (lo, ⟨hsum % 16, Nat.mod_lt _ (by omega)⟩, 16 ≤ hsum)

#eval addbcSpec 3 4 5 6 0    -- (8, 9, false)
#eval addbcSpec 15 15 1 15 0 -- lo=(16)%16=0 clo; hi=(15+1+15)=31%16=15 cout

-- Byte-cell destructure + full ADDBC: concrete probe.  Expected result
-- 0x43 + 0x65 + 0 = 0xA8, no carry: lo=8 hi=10(0xA) cout=false.
-- inner pair stays `pairSrcL`-applied (hsteps is head-only). -/
#eval norm 600 (aps addbcL [byteLit ⟨3, by omega⟩ ⟨4, by omega⟩,
                              byteLit ⟨5, by omega⟩ ⟨6, by omega⟩,
                              nibLit ⟨0, by omega⟩])
  == pairLit (pairLit (nibLit ⟨8, by omega⟩) (nibLit ⟨10, by omega⟩))
             (boolLit false)

-- Carry case: 0x4F + 0x61 = 0xB0 — lo nibble 15+1=16 carries. -/
#eval norm 600 (aps addbcL [byteLit ⟨15, by omega⟩ ⟨4, by omega⟩,
                              byteLit ⟨1, by omega⟩ ⟨6, by omega⟩,
                              nibLit ⟨0, by omega⟩])
  == pairLit (pairLit (nibLit ⟨0, by omega⟩) (nibLit ⟨11, by omega⟩))
             (boolLit false)

-- Carry-out case: 0xFF + 0x01 = 0x00 carry 1. -/
#eval norm 600 (aps addbcL [byteLit ⟨15, by omega⟩ ⟨15, by omega⟩,
                              byteLit ⟨1, by omega⟩ ⟨0, by omega⟩,
                              nibLit ⟨0, by omega⟩])
  == pairLit (pairLit (nibLit ⟨0, by omega⟩) (nibLit ⟨0, by omega⟩))
             (boolLit true)

-- Carry-in case: 0x40 + 0x60 + cin 1 = 0xA1. -/
#eval norm 600 (aps addbcL [byteLit ⟨0, by omega⟩ ⟨4, by omega⟩,
                              byteLit ⟨0, by omega⟩ ⟨6, by omega⟩,
                              nibLit ⟨1, by omega⟩])
  == pairLit (pairLit (nibLit ⟨1, by omega⟩) (nibLit ⟨10, by omega⟩))
             (boolLit false)

-- BC probe: same inputs, carry-out bool only. -/
#eval norm 600 (aps b4bcL [byteLit ⟨15, by omega⟩ ⟨15, by omega⟩,
                             byteLit ⟨1, by omega⟩ ⟨0, by omega⟩,
                             nibLit ⟨0, by omega⟩])
  == boolLit true

#eval norm 600 (aps b4bcL [byteLit ⟨3, by omega⟩ ⟨4, by omega⟩,
                             byteLit ⟨5, by omega⟩ ⟨6, by omega⟩,
                             nibLit ⟨0, by omega⟩])
  == boolLit false

-- BS probe: byte sum only. -/
#eval norm 600 (aps b4bsL [byteLit ⟨15, by omega⟩ ⟨15, by omega⟩,
                             byteLit ⟨1, by omega⟩ ⟨0, by omega⟩,
                             nibLit ⟨0, by omega⟩])
  == pairLit (nibLit ⟨0, by omega⟩) (nibLit ⟨0, by omega⟩)

-- bytes4 probes --------------------------------------------------------------

/-- Expected bytes4 NF: cells already in cons-NF shape. -/
def cellNF (h t : LTerm) : LTerm := .abs (.abs (.app (.app (.var 0) h) t))
def b4NF (xs : List (Fin 16 × Fin 16)) : LTerm :=
  xs.foldr (fun p t => cellNF (byteLit p.1 p.2) t) nilL

-- 0x00000001 + 0xFFFFFFFF ≡ 0 mod 2^32 (full carry cascade + wraparound)
#eval norm 3000
    (aps b4addL [b4Lit [(⟨1, by omega⟩, ⟨0, by omega⟩),
                        (⟨0, by omega⟩, ⟨0, by omega⟩),
                        (⟨0, by omega⟩, ⟨0, by omega⟩),
                        (⟨0, by omega⟩, ⟨0, by omega⟩)],
                 b4Lit [(⟨15, by omega⟩, ⟨15, by omega⟩),
                        (⟨15, by omega⟩, ⟨15, by omega⟩),
                        (⟨15, by omega⟩, ⟨15, by omega⟩),
                        (⟨15, by omega⟩, ⟨15, by omega⟩)]])
  == b4NF [(⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩)]

-- same input through the carry-lookahead twin
#eval norm 3000
    (aps b4claL [b4Lit [(⟨1, by omega⟩, ⟨0, by omega⟩),
                        (⟨0, by omega⟩, ⟨0, by omega⟩),
                        (⟨0, by omega⟩, ⟨0, by omega⟩),
                        (⟨0, by omega⟩, ⟨0, by omega⟩)],
                 b4Lit [(⟨15, by omega⟩, ⟨15, by omega⟩),
                        (⟨15, by omega⟩, ⟨15, by omega⟩),
                        (⟨15, by omega⟩, ⟨15, by omega⟩),
                        (⟨15, by omega⟩, ⟨15, by omega⟩)]])
  == b4NF [(⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩)]

-- mixed: 0x01020304 + 0x0F0E0D0C = 0x10101010 (per-byte nibble carries)
#eval norm 3000
    (aps b4addL [b4Lit [(⟨4, by omega⟩, ⟨0, by omega⟩),
                        (⟨3, by omega⟩, ⟨0, by omega⟩),
                        (⟨2, by omega⟩, ⟨0, by omega⟩),
                        (⟨1, by omega⟩, ⟨0, by omega⟩)],
                 b4Lit [(⟨12, by omega⟩, ⟨0, by omega⟩),
                        (⟨13, by omega⟩, ⟨0, by omega⟩),
                        (⟨14, by omega⟩, ⟨0, by omega⟩),
                        (⟨15, by omega⟩, ⟨0, by omega⟩)]])
  == b4NF [(⟨0, by omega⟩, ⟨1, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩)]

#eval norm 3000
    (aps b4claL [b4Lit [(⟨4, by omega⟩, ⟨0, by omega⟩),
                        (⟨3, by omega⟩, ⟨0, by omega⟩),
                        (⟨2, by omega⟩, ⟨0, by omega⟩),
                        (⟨1, by omega⟩, ⟨0, by omega⟩)],
                 b4Lit [(⟨12, by omega⟩, ⟨0, by omega⟩),
                        (⟨13, by omega⟩, ⟨0, by omega⟩),
                        (⟨14, by omega⟩, ⟨0, by omega⟩),
                        (⟨15, by omega⟩, ⟨0, by omega⟩)]])
  == b4NF [(⟨0, by omega⟩, ⟨1, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩)]

-- the symbolic let-values of _ADDBC (unreduced table applications) ----------

/-- t = NIBADD xl yl -/
def tNib (xl yl : Fin 16) : LTerm := aps nibAddL [nibLit xl, nibLit yl]
/-- clo = OR (NC xl yl) (NC t cn) -/
def cloNib (xl yl cn : Fin 16) : LTerm :=
  aps orL [aps nibCarryL [nibLit xl, nibLit yl],
           aps nibCarryL [tNib xl yl, nibLit cn]]
/-- lo = NIBADD t cn -/
def loNib (xl yl cn : Fin 16) : LTerm :=
  aps nibAddL [tNib xl yl, nibLit cn]
/-- u = NIBADD xh yh -/
def uNib (xh yh : Fin 16) : LTerm := aps nibAddL [nibLit xh, nibLit yh]
/-- cn2 = B2N clo -/
def cn2Nib (xl yl cn : Fin 16) : LTerm := .app b2nL (cloNib xl yl cn)
/-- cout = OR (NC xh yh) (NC u cn2) -/
def coutNib (xl xh yl yh cn : Fin 16) : LTerm :=
  aps orL [aps nibCarryL [nibLit xh, nibLit yh],
           aps nibCarryL [uNib xh yh, cn2Nib xl yl cn]]
/-- hi = NIBADD u cn2 -/
def hiNib (xl xh yl yh cn : Fin 16) : LTerm :=
  aps nibAddL [uNib xh yh, cn2Nib xl yl cn]

/-- Spine milestone: hsteps stops at the pairSrc app-spine (k=16), args
    unreduced but LRed-reachable. -/
theorem addbc_spine (xl xh yl yh cn : Fin 16) :
    LRed (aps addbcL [byteLit xl xh, byteLit yl yh, nibLit cn])
         (aps pairSrcL
           [aps pairSrcL [loNib xl yl cn, hiNib xl xh yl yh cn],
            coutNib xl xh yl yh cn]) :=
  LRed_of_hsteps (k := 16) (by
    simp [addbcL, byteLit, pairLit, pairSrcL, letsL, aps,
          tNib, cloNib, loNib, uNib, cn2Nib, coutNib, hiNib,
          List.foldl, hsteps, hstep, subst, shift,
          subst_nibLit, shift_nibLit,
          subst_of_closed0, shift_of_closed0,
          closed, closed_app, closed_nibLit, closed_nibAddL,
          closed_nibCarryL, closed_orL, closed_b2nL, closed_pairSrcL,
          closed_klL, closed_byteLit])

/-- `PAIR·a·b →* pairLit a b` for closed a, b. -/
theorem pairSrc_nf (a b : LTerm) (ha : closed 0 a = true)
    (hb : closed 0 b = true) :
    LRed (aps pairSrcL [a, b]) (pairLit a b) :=
  LRed_of_hsteps (k := 2) (by
    simp [pairSrcL, pairLit, aps, List.foldl, hsteps, hstep, subst, shift,
          subst_of_closed0, shift_of_closed0, ha, hb])

-- leaf normalization -------------------------------------------------------

/-- nibble-literal equality lifts to `LRed` (closed-step reflexivity). -/
theorem nibLit_eq_red {a b : Fin 16} (h : a = b) :
    LRed (nibLit a) (nibLit b) := h ▸ Relation.ReflTransGen.refl

/-- `clo` resolves to the spec bool: `16 ≤ xl+yl+cn`. -/
theorem cloNib_eval (xl yl cn : Fin 16) :
    LRed (cloNib xl yl cn)
         (boolLit (decide (16 ≤ xl.val + yl.val + cn.val))) := by
  have h1 := nibcarry_correct xl yl
  have ht := nibadd_correct xl yl
  have h2 : LRed (aps nibCarryL [tNib xl yl, nibLit cn])
      (boolLit (decide
        (16 ≤ (xl.val + yl.val) % 16 + cn.val))) :=
    (LRed_app_left (LRed_app_right ht)).trans (nibcarry_correct _ _)
  have e : (decide (16 ≤ xl.val + yl.val)
        || decide (16 ≤ (xl.val + yl.val) % 16 + cn.val))
      = decide (16 ≤ xl.val + yl.val + cn.val) := by
    cases hA : decide (16 ≤ xl.val + yl.val) <;>
      cases hB : decide (16 ≤ (xl.val + yl.val) % 16 + cn.val) <;>
      cases hC : decide (16 ≤ xl.val + yl.val + cn.val) <;>
      simp_all [decide_eq_true_eq, decide_eq_false_iff_not,
                of_decide_eq_true, of_decide_eq_false] <;>
      omega
  unfold cloNib
  refine ((LRed_app_left (LRed_app_right h1)).trans
    ((LRed_app_right h2).trans (or_correct _ _))).trans ?_
  rw [e]

/-- `lo` resolves: `(xl+yl+cn) % 16`. -/
theorem loNib_eval (xl yl cn : Fin 16) :
    LRed (loNib xl yl cn)
         (nibLit ⟨(xl.val + yl.val + cn.val) % 16,
           Nat.mod_lt _ (by omega)⟩) := by
  have ht := nibadd_correct xl yl
  unfold loNib
  refine (LRed_app_left (LRed_app_right ht)).trans ?_
  exact (nibadd_correct
    ⟨(xl.val + yl.val) % 16, Nat.mod_lt _ (by omega)⟩ cn).trans
    (nibLit_eq_red (Fin.ext (by
      show ((xl.val + yl.val) % 16 + cn.val) % 16
        = (xl.val + yl.val + cn.val) % 16
      omega)))

/-- `u` resolves: `(xh+yh) % 16`. -/
theorem uNib_eval (xh yh : Fin 16) :
    LRed (uNib xh yh)
         (nibLit ⟨(xh.val + yh.val) % 16, Nat.mod_lt _ (by omega)⟩) :=
  nibadd_correct xh yh

/-- `cn2 = B2N clo` resolves to the carry nibble
    (`Fin.mk` of a Nat-ite so `.val` computes). -/
theorem cn2Nib_eval (xl yl cn : Fin 16) :
    LRed (cn2Nib xl yl cn)
         (nibLit ⟨if 16 ≤ xl.val + yl.val + cn.val then 1 else 0,
           by split <;> omega⟩) := by
  unfold cn2Nib
  refine (LRed_app_right (cloNib_eval xl yl cn)).trans ?_
  have hb := b2n_correct (decide (16 ≤ xl.val + yl.val + cn.val))
  exact hb.trans (nibLit_eq_red (Fin.ext (by
    simp [apply_ite, decide_eq_true_eq])))

/-- `cout` resolves: `16 ≤ xh+yh+cn2`. -/
theorem coutNib_eval (xl xh yl yh cn : Fin 16) :
    LRed (coutNib xl xh yl yh cn)
         (boolLit (decide (16 ≤ xh.val + yh.val
             + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))) := by
  have h1 := nibcarry_correct xh yh
  have hu := uNib_eval xh yh
  have hc := cn2Nib_eval xl yl cn
  have h2 : LRed (aps nibCarryL [uNib xh yh, cn2Nib xl yl cn])
      (boolLit (decide (16 ≤ (xh.val + yh.val) % 16
          + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))) :=
    (LRed_app_left (LRed_app_right hu)).trans
      ((LRed_app_right hc).trans (nibcarry_correct
        ⟨(xh.val + yh.val) % 16, Nat.mod_lt _ (by omega)⟩
        ⟨if 16 ≤ xl.val + yl.val + cn.val then 1 else 0,
         by split <;> omega⟩))
  have e : (decide (16 ≤ xh.val + yh.val)
        || decide (16 ≤ (xh.val + yh.val) % 16
            + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))
      = decide (16 ≤ xh.val + yh.val
          + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) := by
    cases hA : decide (16 ≤ xh.val + yh.val) <;>
      cases hC : decide (16 ≤ xl.val + yl.val + cn.val) <;>
      cases hD : decide (16 ≤ xh.val + yh.val
          + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) <;>
      simp_all [decide_eq_true_eq, decide_eq_false_iff_not,
                of_decide_eq_true, of_decide_eq_false] <;>
      omega
  unfold coutNib
  refine ((LRed_app_left (LRed_app_right h1)).trans
    ((LRed_app_right h2).trans (or_correct _ _))).trans ?_
  rw [e]

/-- `hi` resolves: `(xh+yh+cn2) % 16`. -/
theorem hiNib_eval (xl xh yl yh cn : Fin 16) :
    LRed (hiNib xl xh yl yh cn)
         (nibLit ⟨(xh.val + yh.val
             + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
           Nat.mod_lt _ (by omega)⟩) := by
  have hu := uNib_eval xh yh
  have hc := cn2Nib_eval xl yl cn
  unfold hiNib
  refine ((LRed_app_left (LRed_app_right hu)).trans
    ((LRed_app_right hc).trans (nibadd_correct
      ⟨(xh.val + yh.val) % 16, Nat.mod_lt _ (by omega)⟩
      ⟨if 16 ≤ xl.val + yl.val + cn.val then 1 else 0,
       by split <;> omega⟩))).trans ?_
  exact nibLit_eq_red (Fin.ext (by
    by_cases hP : 16 ≤ xl.val + yl.val + cn.val <;>
      simp_all <;> omega))

/-- ADDBC evaluation: `addbcL·(byteLit)·(byteLit)·(nibLit cn)`
    →* `pairSrc·(byteLit lo hi)·(boolLit cout)`. -/
theorem addbc_eval (xl xh yl yh cn : Fin 16) :
    LRed (aps addbcL [byteLit xl xh, byteLit yl yh, nibLit cn])
         (aps pairSrcL
           [byteLit
             ⟨(xl.val + yl.val + cn.val) % 16, Nat.mod_lt _ (by omega)⟩
             ⟨(xh.val + yh.val
                 + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
               Nat.mod_lt _ (by omega)⟩,
            boolLit (decide (16 ≤ xh.val + yh.val
                + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))]) := by
  have hm := addbc_spine xl xh yl yh cn
  have hlo := loNib_eval xl yl cn
  have hhi := hiNib_eval xl xh yl yh cn
  have hco := coutNib_eval xl xh yl yh cn
  have hcell : LRed (aps pairSrcL [loNib xl yl cn, hiNib xl xh yl yh cn])
      (byteLit
        ⟨(xl.val + yl.val + cn.val) % 16, Nat.mod_lt _ (by omega)⟩
        ⟨(xh.val + yh.val
            + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
          Nat.mod_lt _ (by omega)⟩) := by
    unfold byteLit pairLit
    exact (LRed_app_left (LRed_app_right hlo)).trans
      ((LRed_app_right hhi).trans
        (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _)))
  unfold aps at hm ⊢
  simp only [List.foldl] at hm ⊢
  exact hm.trans ((LRed_app_left (LRed_app_right hcell)).trans
    (LRed_app_right hco))

/-- `b4bcL` spine: destructures bytes and resolves the let-chain
    to the `coutNib` expression. -/
theorem b4bc_spine (xl xh yl yh cn : Fin 16) :
    LRed (aps b4bcL [byteLit xl xh, byteLit yl yh, nibLit cn])
         (coutNib xl xh yl yh cn) :=
  LRed_of_hsteps (k := 13) (by
    simp [b4bcL, byteLit, pairLit, letsL, aps,
          tNib, cloNib, uNib, cn2Nib, coutNib,
          List.foldl, hsteps, hstep, subst, shift,
          subst_nibLit, shift_nibLit,
          subst_of_closed0, shift_of_closed0,
          closed, closed_app, closed_nibLit, closed_nibAddL,
          closed_nibCarryL, closed_orL, closed_b2nL, closed_pairSrcL,
          closed_klL, closed_byteLit])

/-- `b4bcL` evaluation: byte carry-out. -/
theorem b4bc_eval (xl xh yl yh cn : Fin 16) :
    LRed (aps b4bcL [byteLit xl xh, byteLit yl yh, nibLit cn])
         (boolLit (decide (16 ≤ xh.val + yh.val
             + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))) :=
  (b4bc_spine xl xh yl yh cn).trans (coutNib_eval xl xh yl yh cn)

/-- `b4bsL` spine: resolves to `pairSrc·loNib·hiNib`. -/
theorem b4bs_spine (xl xh yl yh cn : Fin 16) :
    LRed (aps b4bsL [byteLit xl xh, byteLit yl yh, nibLit cn])
         (aps pairSrcL
           [loNib xl yl cn, hiNib xl xh yl yh cn]) :=
  LRed_of_hsteps (k := 14) (by
    simp [b4bsL, byteLit, pairLit, pairSrcL, letsL, aps,
          tNib, cloNib, loNib, uNib, cn2Nib, hiNib,
          List.foldl, hsteps, hstep, subst, shift,
          subst_nibLit, shift_nibLit,
          subst_of_closed0, shift_of_closed0,
          closed, closed_app, closed_nibLit, closed_nibAddL,
          closed_nibCarryL, closed_orL, closed_b2nL, closed_pairSrcL,
          closed_klL, closed_byteLit])

/-- `b4bsL` evaluation: byte sum cell. -/
theorem b4bs_eval (xl xh yl yh cn : Fin 16) :
    LRed (aps b4bsL [byteLit xl xh, byteLit yl yh, nibLit cn])
         (byteLit
           ⟨(xl.val + yl.val + cn.val) % 16, Nat.mod_lt _ (by omega)⟩
           ⟨(xh.val + yh.val
               + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
             Nat.mod_lt _ (by omega)⟩) := by
  have hm := b4bs_spine xl xh yl yh cn
  have hlo := loNib_eval xl yl cn
  have hhi := hiNib_eval xl xh yl yh cn
  unfold byteLit
  exact hm.trans ((LRed_app_left (LRed_app_right hlo)).trans
    ((LRed_app_right hhi).trans
      (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _))))

/-- step continuation `λv7.λv8. pairSrc bt (pairSrc (b2n v8) (conss v7 acc))` -/
def b4stepCont (bt acc : LTerm) : LTerm :=
  .abs (.abs (aps pairSrcL [bt,
    aps pairSrcL [.app b2nL (.var 0),
      aps conssL [.var 1, acc]]]))

theorem closed_b4stepCont {bt acc : LTerm} (hbt : closed 0 bt = true)
    (hacc : closed 0 acc = true) :
    closed 0 (b4stepCont bt acc) = true := by
  simp only [b4stepCont, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals
    first
      | decide
      | exact closed_mono hbt (Nat.zero_le _)
      | exact closed_mono hacc (Nat.zero_le _)
      | exact closed_mono closed_pairSrcL (Nat.zero_le _)
      | exact closed_mono closed_b2nL (Nat.zero_le _)
      | exact closed_mono closed_conssL (Nat.zero_le _)

-- spec arithmetic (nibble-form, matching the addbc decomposition) -----------

/-- carry nibble of a low-nibble triple sum. -/
def lowCarry (x y cn : Fin 16) : Fin 16 :=
  ⟨if 16 ≤ x.val + y.val + cn.val then 1 else 0, by split <;> omega⟩

/-- per-byte ripple step, in the nibble-decomposed form `addbc` computes:
    `(result byte, carry-out nibble)`. -/
def byteStepN (x y : Fin 16 × Fin 16) (cn : Fin 16) :
    (Fin 16 × Fin 16) × Fin 16 :=
  ((⟨(x.1.val + y.1.val + cn.val) % 16, Nat.mod_lt _ (by omega)⟩,
    ⟨(x.2.val + y.2.val + (lowCarry x.1 y.1 cn).val) % 16,
      Nat.mod_lt _ (by omega)⟩),
   ⟨if 16 ≤ x.2.val + y.2.val + (lowCarry x.1 y.1 cn).val then 1 else 0,
    by split <;> omega⟩)

/-- carry after processing `as` zipped against `bs` from carry-in `cn`. -/
def carryAfter : List (Fin 16 × Fin 16) → List (Fin 16 × Fin 16) →
    Fin 16 → Fin 16
  | [], _, cn => cn
  | a :: as, b :: bs, cn => carryAfter as bs (byteStepN a b cn).2
  | _ :: _, [], cn => cn

/-- result bytes in processing order. -/
def resList : List (Fin 16 × Fin 16) → List (Fin 16 × Fin 16) →
    Fin 16 → List (Fin 16 × Fin 16)
  | [], _, _ => []
  | a :: as, b :: bs, cn =>
      (byteStepN a b cn).1 :: resList as bs (byteStepN a b cn).2
  | _ :: _, [], _ => []

/-- `CONSS·h·t →* cellLit h t` for closed payloads. -/
theorem conss_nf (h t : LTerm) (hh : closed 0 h = true)
    (ht : closed 0 t = true) :
    LRed (aps conssL [h, t]) (cellLit h t) :=
  LRed_of_hsteps (k := 2) (by
    simp [cellLit, conssL, aps, List.foldl, hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0, closed, hh, ht])

/-- `pairLit B C · CONT` β-applies the step continuation. -/
theorem pairLit_apply2 (B C bt acc : LTerm)
    (hB : closed 0 B = true) (hC : closed 0 C = true)
    (hbt : closed 0 bt = true) (hacc : closed 0 acc = true) :
    LRed (.app (pairLit B C) (b4stepCont bt acc))
         (aps pairSrcL [bt,
           aps pairSrcL [.app b2nL C, aps conssL [B, acc]]]) :=
  LRed_of_hsteps (k := 3) (by
    simp [pairLit, b4stepCont, aps, List.foldl, hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0, closed,
          closed_pairSrcL, closed_b2nL, closed_conssL, hB, hC, hbt, hacc])

theorem closed_cellLit {h t : LTerm} (hh : closed 0 h = true)
    (ht : closed 0 t = true) : closed 0 (cellLit h t) = true := by
  simp only [cellLit, closed, shift_of_closed0 hh, shift_of_closed0 ht,
             Bool.and_eq_true]
  exact ⟨⟨by decide, closed_mono hh (Nat.zero_le _)⟩,
    closed_mono ht (Nat.zero_le _)⟩

/-- `b4stepL` spine: destructures state and b-cell, lands at the `addbc`
    call applied to the rebuild continuation. -/
theorem b4step_spine (h bh bt cn acc : LTerm)
    (hh : closed 0 h = true) (hbh : closed 0 bh = true)
    (hbt : closed 0 bt = true) (hcn : closed 0 cn = true)
    (hacc : closed 0 acc = true) :
    LRed (aps b4stepL
           [pairLit (.app (.app conssL bh) bt) (pairLit cn acc), h])
         (.app (aps addbcL [h, bh, cn]) (b4stepCont bt acc)) :=
  LRed_of_hsteps (k := 14) (by
    simp [b4stepL, pairLit, conssL, addbcL, b4stepCont, letsL, aps,
          List.foldl, hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0, closed, closed_app,
          closed_klL, closed_pairSrcL, closed_b2nL, closed_conssL,
          closed_nibAddL, closed_nibCarryL, closed_orL,
          hh, hbh, hbt, hcn, hacc])

/-- full byte-step evaluation. -/
theorem b4step_eval (xl xh yl yh cn : Fin 16) (bt acc : LTerm)
    (hbt : closed 0 bt = true) (hacc : closed 0 acc = true) :
    LRed (aps b4stepL
           [pairLit (.app (.app conssL (byteLit yl yh)) bt)
                    (pairLit (nibLit cn) acc),
            byteLit xl xh])
         (pairLit bt
           (pairLit
             (nibLit (byteStepN (xl, xh) (yl, yh) cn).2)
             (cellLit
               (byteLit (byteStepN (xl, xh) (yl, yh) cn).1.1
                        (byteStepN (xl, xh) (yl, yh) cn).1.2)
               acc))) := by
  have hm := b4step_spine (byteLit xl xh) (byteLit yl yh) bt
    (nibLit cn) acc
    (closed_byteLit xl xh) (closed_byteLit yl yh) hbt
    (closed_nibLit cn) hacc
  have h1 := addbc_eval xl xh yl yh cn
  have h2 : LRed (.app (aps addbcL [byteLit xl xh, byteLit yl yh,
                     nibLit cn]) (b4stepCont bt acc))
      (.app (pairLit
         (byteLit ⟨(xl.val + yl.val + cn.val) % 16,
                    Nat.mod_lt _ (by omega)⟩
                  ⟨(xh.val + yh.val
                      + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0))
                      % 16, Nat.mod_lt _ (by omega)⟩)
         (boolLit (decide (16 ≤ xh.val + yh.val
             + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))))
        (b4stepCont bt acc)) :=
    LRed_app_left (h1.trans (pairSrc_nf _ _
      (closed_byteLit _ _) (closed_boolLit _)))
  refine hm.trans (h2.trans ?_)
  refine (pairLit_apply2 _ _ _ _
    (closed_byteLit _ _) (closed_boolLit _) hbt hacc).trans ?_
  have hb2n : LRed (.app b2nL
        (boolLit (decide (16 ≤ xh.val + yh.val
            + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))))
      (nibLit (byteStepN (xl, xh) (yl, yh) cn).2) := by
    refine (b2n_correct _).trans (nibLit_eq_red ?_)
    apply Fin.ext
    simp [byteStepN, lowCarry, apply_ite, decide_eq_true_eq]
    split <;> simp_all <;> omega
  have hcell : LRed (aps conssL
        [byteLit ⟨(xl.val + yl.val + cn.val) % 16, Nat.mod_lt _ (by omega)⟩
                 ⟨(xh.val + yh.val
                     + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
                   Nat.mod_lt _ (by omega)⟩, acc])
      (cellLit (byteLit (byteStepN (xl, xh) (yl, yh) cn).1.1
                        (byteStepN (xl, xh) (yl, yh) cn).1.2) acc) := by
    refine (conss_nf _ _ (closed_byteLit _ _) hacc).trans ?_
    rw [show (⟨(xl.val + yl.val + cn.val) % 16,
               Nat.mod_lt _ (by omega)⟩ : Fin 16)
          = (byteStepN (xl, xh) (yl, yh) cn).1.1
        from Fin.ext rfl,
        show (⟨(xh.val + yh.val
                 + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
               Nat.mod_lt _ (by omega)⟩ : Fin 16)
          = (byteStepN (xl, xh) (yl, yh) cn).1.2
        from Fin.ext rfl]
  have hinner : LRed (aps pairSrcL
        [.app b2nL (boolLit (decide (16 ≤ xh.val + yh.val
            + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)))),
         aps conssL
           [byteLit ⟨(xl.val + yl.val + cn.val) % 16, Nat.mod_lt _ (by omega)⟩
                    ⟨(xh.val + yh.val
                        + (if 16 ≤ xl.val + yl.val + cn.val then 1 else 0)) % 16,
                      Nat.mod_lt _ (by omega)⟩, acc]])
      (pairLit (nibLit (byteStepN (xl, xh) (yl, yh) cn).2)
               (cellLit (byteLit (byteStepN (xl, xh) (yl, yh) cn).1.1
                                 (byteStepN (xl, xh) (yl, yh) cn).1.2) acc)) :=
    (LRed_app_left (LRed_app_right hb2n)).trans
      ((LRed_app_right hcell).trans
        (pairSrc_nf _ _ (closed_nibLit _)
          (closed_cellLit (closed_byteLit _ _) hacc)))
  exact (LRed_app_right hinner).trans
    (pairSrc_nf _ _ hbt
      (closed_pairLit
        (closed_mono (closed_nibLit _) (Nat.zero_le 1))
        (closed_mono (closed_cellLit (closed_byteLit _ _) hacc)
          (Nat.zero_le 1))))

-- GGB machinery (generic step) ----------------------------------------------

/-- once-unfolded worker — the computed reduct of `foldG st · foldG st`. -/
def GGB (st : LTerm) : LTerm :=
  hsteps 1 (.app (foldG st) (foldG st))

/-- `gs st · l · a` — the running fold state. -/
def gsA (st l a : LTerm) : LTerm :=
  .app (.app (.app (foldG st) (foldG st)) l) a

/-- `GGB st · l · a` -/
def ggbA (st l a : LTerm) : LTerm := .app (.app (GGB st) l) a

theorem gsA_to_ggb (st l a : LTerm) :
    LRed (gsA st l a) (ggbA st l a) :=
  LRed_of_hsteps (k := 1) rfl

/-- `_FOLDL·st·l·a →* GGB st·l·a` — entry unfold through W·G. -/
theorem foldl_to_ggb (st l a : LTerm) (hs : closed 0 st = true)
    (hl : closed 0 l = true) (ha : closed 0 a = true) :
    LRed (.app (.app (.app foldlL st) l) a) (ggbA st l a) :=
  LRed_of_hsteps (k := 5) (by
    simp [gsA, ggbA, GGB, foldlL, wl, foldG, nilL, cellLit, conssL,
          hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 hl, shift_of_closed0 ha,
          subst_of_closed0 hs, subst_of_closed0 hl, subst_of_closed0 ha])

/-- cell unfold for ANY closed step `st` — `st` only occurs shifted inside
    `foldG`, so the milestone is step-generic. -/
theorem cell_unfold (st h t a : LTerm) (hs : closed 0 st = true)
    (hh : closed 0 h = true) (ht : closed 0 t = true)
    (ha : closed 0 a = true) :
    LRed (ggbA st (cellLit h t) a)
         (ggbA st t (.app (.app st a) h)) :=
  LRed_of_hsteps (k := 7) (by
    simp [gsA, ggbA, GGB, foldlL, wl, foldG, nilL, cellLit, conssL,
          hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 hh, shift_of_closed0 ht,
          shift_of_closed0 ha,
          subst_of_closed0 hs, subst_of_closed0 hh, subst_of_closed0 ht,
          subst_of_closed0 ha])

/-- `GGB·nil·a →* a` for any closed step. -/
theorem nil_unfold (st a : LTerm) (hs : closed 0 st = true)
    (ha : closed 0 a = true) :
    LRed (ggbA st nilL a) a :=
  LRed_of_hsteps (k := 4) (by
    simp [gsA, ggbA, GGB, foldlL, wl, foldG, nilL, cellLit, conssL,
          hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 ha,
          subst_of_closed0 hs, subst_of_closed0 ha])

-- closedness of the word-level combinators ----------------------------------

theorem closed_foldlL : closed 0 foldlL = true := by decide
theorem closed_b4stepL : closed 0 b4stepL = true := by decide
theorem closed_b4finL : closed 0 b4finL = true := by decide
theorem closed_revL : closed 0 revL = true := by decide
theorem closed_stepConsL : closed 0 stepConsL = true := by decide
theorem closed_addbcL : closed 0 addbcL = true := by decide
theorem closed_b4bcL : closed 0 b4bcL = true := by decide
theorem closed_b4bsL : closed 0 b4bsL = true := by decide
theorem closed_b4addL : closed 0 b4addL = true := by decide
theorem closed_b4claL : closed 0 b4claL = true := by decide

theorem closed_scottList {cs : List LTerm}
    (h : ∀ e ∈ cs, closed 0 e = true) : closed 0 (scottList cs) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [scottList, List.foldr_cons]
      exact closed_cellLit (h c List.mem_cons_self)
        (ih (fun e he => h e (List.mem_cons_of_mem c he)))

/-- **Spine-bounded fixpoint**: `GGB st` over a Scott list of `cs`
    cells unfolds exactly `cs.length` times, threading the
    (unreduced) accumulator applications `st·acc·e`.  The `(\f. f f)`
    fixpoint is bounded by the input spine — recursion depth = list
    length, no undecidable branch.  Per-head termination then reduces
    to: each `st·acc·e` application on well-formed arguments reaches
    NF (the per-head obligation — bounded unfold for every
    non-fold vocabulary head). -/
theorem fold_run (st : LTerm) (hs : closed 0 st = true) :
    ∀ (cs : List LTerm) (a : LTerm),
      (∀ e ∈ cs, closed 0 e = true) → closed 0 a = true →
      LRed (ggbA st (scottList cs) a)
           (cs.foldl (fun acc e => .app (.app st acc) e) a) := by
  intro cs
  induction cs with
  | nil =>
    intro a _ ha
    simp only [scottList, List.foldl_nil]
    exact nil_unfold st a hs ha
  | cons c cs' ih =>
    intro a hcl ha
    have hc : closed 0 c = true := hcl c List.mem_cons_self
    have htail : ∀ e ∈ cs', closed 0 e = true :=
      fun e he => hcl e (List.mem_cons_of_mem c he)
    rw [show scottList (c :: cs') = cellLit c (scottList cs') from rfl]
    refine (cell_unfold st c _ a hs hc (closed_scottList htail) ha).trans ?_
    rw [List.foldl_cons]
    exact ih _ htail (closed_app (closed_app hs ha) hc)

/-- **Chain reduction**: if every step application `st·acc·e`
    reduces to a semantic result `σ acc e` (closed when its inputs
    are), then the whole `foldl` chain of unreduced applications
    reduces to the semantic `foldl` of `σ`.  Generalized over the
    syntactic/semantic accumulator pair `X`/`a` so the induction
    threads `LRed X a` through the cons case. -/
theorem foldl_red (st : LTerm) (σ : LTerm → LTerm → LTerm)
    (hstep : ∀ acc e, closed 0 acc = true → closed 0 e = true →
      LRed (.app (.app st acc) e) (σ acc e) ∧
      closed 0 (σ acc e) = true) :
    ∀ (cs : List LTerm) (X a : LTerm), LRed X a →
      (∀ e ∈ cs, closed 0 e = true) → closed 0 a = true →
      LRed (cs.foldl (fun acc e => .app (.app st acc) e) X)
           (cs.foldl σ a) := by
  intro cs
  induction cs with
  | nil => intro X a hXa _ _; exact hXa
  | cons c cs' ih =>
    intro X a hXa hcl ha
    have hc : closed 0 c = true := hcl c List.mem_cons_self
    have htail : ∀ e ∈ cs', closed 0 e = true :=
      fun e he => hcl e (List.mem_cons_of_mem c he)
    have hs' := hstep a c ha hc
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ ((LRed_app (LRed_app Relation.ReflTransGen.refl hXa)
      Relation.ReflTransGen.refl).trans hs'.1) htail hs'.2

/-- **FixSpine, composed**: a spine-bounded fold `GGB st` over the
    Scott list `scottList cs` reduces to the semantic `foldl` of `σ`,
    provided each step `st·acc·e` reduces to `σ acc e` on closed
    inputs.  This is the shared termination core — recursion depth is
    exactly `cs.length`, so any fold-family head is discharged by one
    per-step lemma (`hstep`), a bounded unfold, not a termination
    proof. -/
theorem spine_eval (st : LTerm) (σ : LTerm → LTerm → LTerm)
    (hs : closed 0 st = true)
    (hstep : ∀ acc e, closed 0 acc = true → closed 0 e = true →
      LRed (.app (.app st acc) e) (σ acc e) ∧
      closed 0 (σ acc e) = true) :
    ∀ (cs : List LTerm) (a : LTerm),
      (∀ e ∈ cs, closed 0 e = true) → closed 0 a = true →
      LRed (ggbA st (scottList cs) a) (cs.foldl σ a) :=
  fun cs a hcl ha =>
    (fold_run st hs cs a hcl ha).trans
      (foldl_red st σ hstep cs a a Relation.ReflTransGen.refl hcl ha)

/-- **Full fold head**: `foldlL·st·l·a →* cs.foldl σ a` whenever the
    list argument reduces to `scottList cs`.  This is the shape every
    fold-family head (`revL`, `appendT`, `b4add`, `_MAP`, `_JOIN`,
    `_NIBS2BYTES`) plugs into — the per-head obligation collapses to
    `hstep` plus `closed 0 st`. -/
theorem fold_eval (st : LTerm) (σ : LTerm → LTerm → LTerm)
    (hs : closed 0 st = true)
    (hstep : ∀ acc e, closed 0 acc = true → closed 0 e = true →
      LRed (.app (.app st acc) e) (σ acc e) ∧
      closed 0 (σ acc e) = true) :
    ∀ (l a : LTerm) (cs : List LTerm),
      closed 0 l = true → closed 0 a = true →
      LRed l (scottList cs) → (∀ e ∈ cs, closed 0 e = true) →
      LRed (.app (.app (.app foldlL st) l) a) (cs.foldl σ a) :=
  fun l a cs hl ha hlcs hcl =>
    (foldl_to_ggb st l a hs hl ha).trans
      ((LRed_app_left (LRed_app_right hlcs)).trans
        (spine_eval st σ hs hstep cs a hcl ha))

/-- `b4Lit` normalizes to the `cellLit`-chain Scott list. -/
theorem b4Lit_nf : ∀ (xs : List (Fin 16 × Fin 16)),
    LRed (b4Lit xs)
         (scottList (xs.map (fun p => byteLit p.1 p.2))) := by
  intro xs; induction xs with
  | nil => exact Relation.ReflTransGen.refl
  | cons p xs ih =>
      simp only [b4Lit, List.foldr_cons, List.map_cons, scottList]
      exact (LRed_app_right ih).trans
        (conss_nf _ _ (closed_byteLit _ _)
          (closed_scottList (fun e he => by
            simp only [List.mem_map] at he
            obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _)))

/-- fold state: `pairLit remB (pairLit cn acc)`. -/
def b4state (remB cn acc : LTerm) : LTerm :=
  pairLit remB (pairLit cn acc)


-- fold readback for the ripple step -----------------------------------------

theorem closed_b4state {remB cn acc : LTerm} (hr : closed 0 remB = true)
    (hc : closed 0 cn = true) (ha : closed 0 acc = true) :
    closed 0 (pairLit remB (pairLit cn acc)) = true :=
  closed_pairLit (closed_mono hr (Nat.zero_le 1))
    (closed_mono (closed_pairLit (closed_mono hc (Nat.zero_le 1))
      (closed_mono ha (Nat.zero_le 1))) (Nat.zero_le 1))

/-- closedness of a reversed-cell accumulator. -/
theorem closed_accRev {xs : List (Fin 16 × Fin 16)} {acc : LTerm}
    (h : closed 0 acc = true) :
    closed 0 (xs.foldr (fun p t => cellLit (byteLit p.1 p.2) t) acc)
      = true := by
  induction xs with
  | nil => exact h
  | cons p xs ih =>
      simp only [List.foldr_cons]
      exact closed_cellLit (closed_byteLit _ _) ih

/-- The fold run: `GGB b4step` over the Scott-encoded byte cells of `cs`
    ripples the carry through, consuming `bs` cells pairwise and pushing
    result bytes onto the accumulator (in reverse). -/
theorem b4fold_run : ∀ (cs : List (Fin 16 × Fin 16))
    (bs : List (Fin 16 × Fin 16)) (cn : Fin 16) (acc : LTerm),
    cs.length ≤ bs.length → closed 0 acc = true →
    LRed (ggbA b4stepL (scottList (cs.map (fun p => byteLit p.1 p.2)))
           (pairLit (b4Lit bs) (pairLit (nibLit cn) acc)))
         (pairLit (b4Lit (bs.drop cs.length))
           (pairLit (nibLit (carryAfter cs bs cn))
             ((resList cs bs cn).reverse.foldr
               (fun p t => cellLit (byteLit p.1 p.2) t) acc))) := by
  intro cs
  induction cs with
  | nil =>
    intro bs cn acc _ hacc
    simp only [scottList, List.map_nil, List.foldr_nil, List.drop_zero,
               carryAfter, resList, List.reverse_nil]
    exact nil_unfold b4stepL _ closed_b4stepL
      (closed_b4state (closed_b4Lit bs) (closed_nibLit cn) hacc)
  | cons c cs' ih =>
    intro bs cn acc hlen hacc
    cases bs with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons b bs' =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at hlen
      have htail : ∀ e ∈ cs'.map (fun p => byteLit p.1 p.2),
          closed 0 e = true := fun e he => by
        simp only [List.mem_map] at he
        obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _
      have hstate0 : closed 0 (pairLit (b4Lit (b :: bs'))
          (pairLit (nibLit cn) acc)) = true :=
        closed_b4state (closed_b4Lit _) (closed_nibLit cn) hacc
      have e0 : scottList ((c :: cs').map (fun p => byteLit p.1 p.2))
          = cellLit (byteLit c.1 c.2)
              (scottList (cs'.map (fun p => byteLit p.1 p.2))) := rfl
      rw [e0]
      have hstep : LRed
          (.app (.app b4stepL
            (pairLit (b4Lit (b :: bs')) (pairLit (nibLit cn) acc)))
            (byteLit c.1 c.2))
          (pairLit (b4Lit bs')
            (pairLit (nibLit (byteStepN c b cn).2)
              (cellLit (byteLit (byteStepN c b cn).1.1
                                (byteStepN c b cn).1.2) acc))) :=
        b4step_eval c.1 c.2 b.1 b.2 cn (b4Lit bs') acc
          (closed_b4Lit bs') hacc
      refine (cell_unfold b4stepL _ _ _ closed_b4stepL
        (closed_byteLit _ _) (closed_scottList htail) hstate0).trans ?_
      refine (LRed_app_right hstep).trans ?_
      have hih := ih bs' (byteStepN c b cn).2
        (cellLit (byteLit (byteStepN c b cn).1.1
                          (byteStepN c b cn).1.2) acc)
        hlen (closed_cellLit (closed_byteLit _ _) hacc)
      rw [show pairLit (b4Lit ((b :: bs').drop (c :: cs').length))
            (pairLit (nibLit (carryAfter (c :: cs') (b :: bs') cn))
              ((resList (c :: cs') (b :: bs') cn).reverse.foldr
                (fun p t => cellLit (byteLit p.1 p.2) t) acc))
          = pairLit (b4Lit (bs'.drop cs'.length))
            (pairLit (nibLit (carryAfter cs' bs' (byteStepN c b cn).2))
              ((resList cs' bs' (byteStepN c b cn).2).reverse.foldr
                (fun p t => cellLit (byteLit p.1 p.2) t)
                (cellLit (byteLit (byteStepN c b cn).1.1
                          (byteStepN c b cn).1.2) acc)))
        from by
          simp [carryAfter, resList, List.length_cons, List.reverse_cons,
                List.foldr_append]]
      exact hih

-- fin + rev stages ------------------------------------------------------------

/-- `b4finL` drops the leftover b-tail and carry, runs `revL` on the acc. -/
theorem b4fin_apply (X cn acc : LTerm) (hx : closed 0 X = true)
    (hcn : closed 0 cn = true) (hacc : closed 0 acc = true) :
    LRed (.app (pairLit X (pairLit cn acc)) b4finL) (.app revL acc) :=
  LRed_of_hsteps (k := 6) (by
    simp [b4finL, pairLit, hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0, closed, closed_app,
          hx, hcn, hacc, closed_revL])

/-- `st·a·h →* cellLit h a` — the stepCons step produces a cell literal. -/
theorem stepCons_cell (h a : LTerm) (hh : closed 0 h = true)
    (ha : closed 0 a = true) :
    LRed (.app (.app stepConsL a) h) (cellLit h a) :=
  LRed_of_hsteps (k := 4) (by
    simp [cellLit, conssL, stepConsL, subst, shift, hsteps, hstep,
          shift_of_closed0 hh, shift_of_closed0 ha,
          subst_of_closed0 hh, subst_of_closed0 ha])

/-- Fold readback for `stepConsL`: `GGB·(scott cs)·a →* rev-foldr cellLit`.
    One line through `spine_eval` — the generic FixSpine core carries
    the induction; the per-head obligation is only `stepCons_cell`. -/
theorem fold_read : ∀ (cs : List LTerm) (a : LTerm),
    (∀ e ∈ cs, closed 0 e = true) → closed 0 a = true →
    LRed (ggbA stepConsL (scottList cs) a)
         (cs.reverse.foldr cellLit a) := by
  intro cs a hcl ha
  have h := spine_eval stepConsL (fun acc e => cellLit e acc)
    closed_stepConsL
    (fun acc e hacc he =>
      ⟨stepCons_cell e acc he hacc, closed_cellLit he hacc⟩)
    cs a hcl ha
  rw [List.foldr_reverse]
  exact h

/-- `revL·l →* scottList cs.reverse` when `l →* scottList cs`. -/
theorem revL_eval (l : LTerm) (cs : List LTerm) (hl : closed 0 l = true)
    (hcs : ∀ e ∈ cs, closed 0 e = true) (h : LRed l (scottList cs)) :
    LRed (.app revL l) (scottList cs.reverse) := by
  have e1 : LRed (.app revL l)
      (.app (.app (.app foldlL stepConsL) l) klL) :=
    LRed_of_hsteps (k := 1) (by
      simp [revL, aps, List.foldl,
            hsteps, hstep, subst, shift,
            shift_of_closed0, subst_of_closed0, closed, closed_app,
            hl, closed_stepConsL, closed_foldlL, closed_klL])
  have e2 := foldl_to_ggb stepConsL l klL closed_stepConsL hl closed_klL
  have e3 : LRed (ggbA stepConsL l klL)
      (ggbA stepConsL (scottList cs) klL) :=
    LRed_app_left (LRed_app_right h)
  have e4 := fold_read cs klL hcs closed_klL
  have e5 : cs.reverse.foldr cellLit klL = scottList cs.reverse := rfl
  exact e1.trans (e2.trans (e3.trans (e5 ▸ e4)))

-- word-level ripple evaluation ----------------------------------------------

/-- `_B4ADD·(b4 as)·(b4 bs) →* scott (map byteOf (resList as bs 0))` —
    the ripple adder computes the byte-level ripple spec. -/
theorem b4add_eval (as bs : List (Fin 16 × Fin 16))
    (h : as.length = bs.length) :
    LRed (aps b4addL [b4Lit as, b4Lit bs])
         (scottList ((resList as bs 0).map (fun p => byteLit p.1 p.2))) := by
  have hstate0 : closed 0 (pairLit (b4Lit bs)
      (pairLit (nibLit 0) klL)) = true :=
    closed_b4state (closed_b4Lit bs) (closed_nibLit _) closed_klL
  have e1 : LRed (aps b4addL [b4Lit as, b4Lit bs])
      (.app (aps foldlL [b4stepL, b4Lit as,
              aps pairSrcL [b4Lit bs, aps pairSrcL [nibLit 0, klL]]])
            b4finL) :=
    LRed_of_hsteps (k := 2) (by
      simp [b4addL, aps, List.foldl, hsteps, hstep, subst, shift,
            shift_of_closed0, subst_of_closed0, closed, closed_app,
            closed_b4stepL, closed_b4finL, closed_foldlL, closed_pairSrcL,
            closed_nibLit, closed_klL, closed_b4Lit])
  have e2 : LRed (aps pairSrcL [b4Lit bs, aps pairSrcL [nibLit 0, klL]])
      (pairLit (b4Lit bs) (pairLit (nibLit 0) klL)) :=
    (LRed_app_right (pairSrc_nf _ _ (closed_nibLit _) closed_klL)).trans
      (pairSrc_nf _ _ (closed_b4Lit bs)
        (closed_pairLit (closed_mono (closed_nibLit _) (Nat.zero_le 1))
          (closed_mono closed_klL (Nat.zero_le 1))))
  refine e1.trans ((LRed_app_left (LRed_app_right e2)).trans ?_)
  refine (LRed_app_left (foldl_to_ggb b4stepL (b4Lit as) _
    closed_b4stepL (closed_b4Lit as) hstate0)).trans ?_
  refine (LRed_app_left (LRed_app_left (LRed_app_right
    (b4Lit_nf as)))).trans ?_
  refine (LRed_app_left (b4fold_run as bs 0 klL h.le closed_klL)).trans ?_
  have hdrop : b4Lit (bs.drop as.length) = nilL := by
    have hd : bs.drop as.length = [] := by
      rw [h]; exact List.drop_length
    rw [hd]; rfl
  rw [hdrop]
  refine (b4fin_apply nilL (nibLit (carryAfter as bs 0)) _ closed_nilL
    (closed_nibLit _) (closed_accRev closed_klL)).trans ?_
  have haccEq : (resList as bs 0).reverse.foldr
        (fun p t => cellLit (byteLit p.1 p.2) t) klL
      = scottList ((resList as bs 0).reverse.map
          (fun p => byteLit p.1 p.2)) := by
    simp only [scottList, List.foldr_map]
    rfl
  refine (revL_eval _ ((resList as bs 0).reverse.map
      (fun p => byteLit p.1 p.2)) (closed_accRev closed_klL)
    (fun e he => by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he; exact closed_byteLit _ _)
    (by rw [← haccEq])).trans ?_
  rw [← List.map_reverse, List.reverse_reverse]

-- CLA spine -----------------------------------------------------------------

/-- carry-cell application: `b4bc a b (nibLit c)`. -/
def claBC (a b : LTerm) (c : Fin 16) : LTerm := aps b4bcL [a, b, nibLit c]
def claBS (a b cn : LTerm) : LTerm := aps b4bsL [a, b, cn]

/-- expected CLA resolved spine. -/
def claSpine (a0 a1 a2 a3 b0 b1 b2 b3 : LTerm) : LTerm :=
  aps conssL [claBS a0 b0 (nibLit 0),
    aps conssL [claBS a1 b1 (.app b2nL (claBC a0 b0 0)),
      aps conssL [claBS a2 b2 (.app b2nL
          (aps orL [claBC a1 b1 0,
                    aps andL [claBC a1 b1 1, claBC a0 b0 0]])),
        aps conssL [claBS a3 b3 (.app b2nL
            (aps orL [claBC a2 b2 0,
                      aps andL [claBC a2 b2 1,
                        aps orL [claBC a1 b1 0,
                                 aps andL [claBC a1 b1 1, claBC a0 b0 0]]]])),
          klL]]]]

-- CLA evaluation -------------------------------------------------------------

/-- carry-out as a Bool, in the form `b4bcL` computes. -/
def byteCoutB (x y : Fin 16 × Fin 16) (cn : Fin 16) : Bool :=
  decide (16 ≤ x.2.val + y.2.val
    + (if 16 ≤ x.1.val + y.1.val + cn.val then 1 else 0))

/-- carry Bool as a nibble — the `Fin.mk`-of-`ite` form `byteStepN` produces. -/
def cnBool (b : Bool) : Fin 16 := ⟨if b then 1 else 0, by split <;> omega⟩

/-- the carry nibble equals `cnBool` of `byteCoutB`. -/
theorem byteStepN_snd_cnBool (x y : Fin 16 × Fin 16) (cn : Fin 16) :
    (byteStepN x y cn).2 = cnBool (byteCoutB x y cn) := by
  apply Fin.ext
  simp [byteStepN, lowCarry, byteCoutB, cnBool, decide_eq_true_eq]

/-- `b2n·(boolLit b)` in `cnBool` form. -/
theorem b2n_correctN (b : Bool) :
    LRed (.app b2nL (boolLit b)) (nibLit (cnBool b)) :=
  (b2n_correct b).trans (nibLit_eq_red (by cases b <;> decide))

/-- carry-out is monotone in carry-in — the algebraic content of the
    lookahead decomposition `cout(c) = g ∨ (p ∧ c)`. -/
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

/-- byte-sum evaluation in `byteStepN`-form. -/
theorem b4bs_evalN (x y : Fin 16 × Fin 16) (cn : Fin 16) :
    LRed (aps b4bsL [byteLit x.1 x.2, byteLit y.1 y.2, nibLit cn])
         (byteLit (byteStepN x y cn).1.1 (byteStepN x y cn).1.2) :=
  b4bs_eval x.1 x.2 y.1 y.2 cn

/-- `b4bcL` on byte cells produces the `byteCoutB` literal. -/
theorem b4bc_evalN (x y : Fin 16 × Fin 16) (cn : Fin 16) :
    LRed (aps b4bcL [byteLit x.1 x.2, byteLit y.1 y.2, nibLit cn])
         (boolLit (byteCoutB x y cn)) :=
  b4bc_eval x.1 x.2 y.1 y.2 cn

/-- `_B4CLA` evaluates to the same result list as the ripple. -/
theorem b4cla_eval (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 16 × Fin 16) :
    LRed (aps b4claL [b4Lit [a0, a1, a2, a3], b4Lit [b0, b1, b2, b3]])
         (scottList ((resList [a0, a1, a2, a3] [b0, b1, b2, b3] 0).map
           (fun p => byteLit p.1 p.2))) := by
  -- spine milestone
  have e1 : LRed (aps b4claL [b4Lit [a0, a1, a2, a3],
                    b4Lit [b0, b1, b2, b3]])
      (claSpine (byteLit a0.1 a0.2) (byteLit a1.1 a1.2)
        (byteLit a2.1 a2.2) (byteLit a3.1 a3.2)
        (byteLit b0.1 b0.2) (byteLit b1.1 b1.2)
        (byteLit b2.1 b2.2) (byteLit b3.1 b3.2)) :=
    LRed_of_hsteps (k := 58) (by
      simp [b4claL, claSpine, claBC, claBS, b4Lit, peelK, letsL,
            conssL, aps, List.foldl, List.foldr, List.map,
            List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
            hsteps, hstep, subst, shift,
            subst_nibLit, shift_nibLit, subst_of_closed0, shift_of_closed0,
            closed, closed_app, closed_nibLit, closed_nibAddL,
            closed_nibCarryL, closed_orL, closed_andL, closed_b2nL,
            closed_pairSrcL, closed_klL, closed_byteLit, closed_b4bcL,
            closed_b4bsL])
  -- per-byte carry literals
  have hG0 := b4bc_evalN a0 b0 0
  have hP1 := b4bc_evalN a1 b1 1
  have hG1 := b4bc_evalN a1 b1 0
  have hP2 := b4bc_evalN a2 b2 1
  have hG2 := b4bc_evalN a2 b2 0
  -- c2 expression: g1 || (p1 && g0)
  have hA1 : LRed (aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                   claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0])
      (boolLit (byteCoutB a1 b1 1 && byteCoutB a0 b0 0)) :=
    (LRed_app_left (LRed_app_right hP1)).trans
      ((LRed_app_right hG0).trans (and_correct _ _))
  have hC2 : LRed (aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
                   aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                             claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]])
      (boolLit (byteCoutB a1 b1 0
        || (byteCoutB a1 b1 1 && byteCoutB a0 b0 0))) :=
    (LRed_app_left (LRed_app_right hG1)).trans
      ((LRed_app_right hA1).trans (or_correct _ _))
  -- c3 expression: g2 || (p2 && c2)
  have hA2 : LRed (aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
                   aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
                     aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                               claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]])
      (boolLit (byteCoutB a2 b2 1
        && (byteCoutB a1 b1 0
          || (byteCoutB a1 b1 1 && byteCoutB a0 b0 0)))) :=
    (LRed_app_left (LRed_app_right hP2)).trans
      ((LRed_app_right hC2).trans (and_correct _ _))
  have hC3 : LRed (aps orL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 0,
                   aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
                     aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
                       aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                                 claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]]])
      (boolLit (byteCoutB a2 b2 0
        || (byteCoutB a2 b2 1
          && (byteCoutB a1 b1 0
            || (byteCoutB a1 b1 1 && byteCoutB a0 b0 0))))) :=
    (LRed_app_left (LRed_app_right hG2)).trans
      ((LRed_app_right hA2).trans (or_correct _ _))
  -- spec-side carry equalities
  have hc2eq : cnBool (byteCoutB a1 b1 0
      || (byteCoutB a1 b1 1 && byteCoutB a0 b0 0))
      = (byteStepN a1 b1 (byteStepN a0 b0 0).2).2 := by
    rw [byteStepN_snd_cnBool a1 b1 (byteStepN a0 b0 0).2,
        byteStepN_snd_cnBool a0 b0 0,
        byteCoutB_mono a1 b1 (byteCoutB a0 b0 0)]
  have hc3eq : cnBool (byteCoutB a2 b2 0 || (byteCoutB a2 b2 1
      && (byteCoutB a1 b1 0
        || (byteCoutB a1 b1 1 && byteCoutB a0 b0 0))))
      = (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2 := by
    rw [byteStepN_snd_cnBool a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2,
        byteStepN_snd_cnBool a1 b1 (byteStepN a0 b0 0).2,
        byteCoutB_mono a2 b2 (byteCoutB a1 b1 (byteStepN a0 b0 0).2),
        byteStepN_snd_cnBool a0 b0 0,
        byteCoutB_mono a1 b1 (byteCoutB a0 b0 0)]
  -- carry-nibble reductions
  have hcn1 : LRed (.app b2nL
      (claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0))
      (nibLit (byteStepN a0 b0 0).2) :=
    (LRed_app_right hG0).trans ((b2n_correctN _).trans
      (nibLit_eq_red (byteStepN_snd_cnBool a0 b0 0).symm))
  have hcn2 : LRed (.app b2nL
      (aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
        aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                  claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]))
      (nibLit (byteStepN a1 b1 (byteStepN a0 b0 0).2).2) :=
    (LRed_app_right hC2).trans ((b2n_correctN _).trans
      (nibLit_eq_red hc2eq))
  have hcn3 : LRed (.app b2nL
      (aps orL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 0,
        aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
          aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
            aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                      claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]]]))
      (nibLit (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2) :=
    (LRed_app_right hC3).trans ((b2n_correctN _).trans
      (nibLit_eq_red hc3eq))
  -- byte sums (carries rewritten through `hcn_i`)
  have hS0 : LRed (aps b4bsL [byteLit a0.1 a0.2, byteLit b0.1 b0.2, nibLit 0])
      (byteLit (byteStepN a0 b0 0).1.1 (byteStepN a0 b0 0).1.2) :=
    b4bs_evalN a0 b0 0
  have hS1 : LRed (aps b4bsL [byteLit a1.1 a1.2, byteLit b1.1 b1.2,
      .app b2nL (claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0)])
      (byteLit (byteStepN a1 b1 (byteStepN a0 b0 0).2).1.1
               (byteStepN a1 b1 (byteStepN a0 b0 0).2).1.2) :=
    (LRed_app_right hcn1).trans (b4bs_evalN a1 b1 _)
  have hS2 : LRed (aps b4bsL [byteLit a2.1 a2.2, byteLit b2.1 b2.2,
      .app b2nL (aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
        aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                  claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]])])
      (byteLit (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.1
               (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.2) :=
    (LRed_app_right hcn2).trans (b4bs_evalN a2 b2 _)
  have hS3 : LRed (aps b4bsL [byteLit a3.1 a3.2, byteLit b3.1 b3.2,
      .app b2nL (aps orL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 0,
        aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
          aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
            aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                      claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]]])])
      (byteLit (byteStepN a3 b3
        (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.1
               (byteStepN a3 b3
        (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.2) :=
    (LRed_app_right hcn3).trans (b4bs_evalN a3 b3 _)
  -- collapse the conss spine bottom-up
  have t3 : LRed
      (aps conssL [aps b4bsL [byteLit a3.1 a3.2, byteLit b3.1 b3.2,
          .app b2nL (aps orL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 0,
            aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
              aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
                aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                          claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]]])],
        klL])
      (cellLit (byteLit (byteStepN a3 b3
          (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.1
        (byteStepN a3 b3
          (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.2)
        klL) :=
    (LRed_app_left (LRed_app_right hS3)).trans
      (conss_nf _ _ (closed_byteLit _ _) closed_klL)
  have t2 : LRed
      (aps conssL [aps b4bsL [byteLit a2.1 a2.2, byteLit b2.1 b2.2,
          .app b2nL (aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
            aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                      claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]])],
        aps conssL [aps b4bsL [byteLit a3.1 a3.2, byteLit b3.1 b3.2,
          .app b2nL (aps orL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 0,
            aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
              aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
                aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                          claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]]])],
          klL]])
      (cellLit (byteLit (byteStepN a2 b2
          (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.1
        (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.2)
        (cellLit (byteLit (byteStepN a3 b3
            (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.1
          (byteStepN a3 b3
            (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.2)
          klL)) :=
    (LRed_app_left (LRed_app_right hS2)).trans
      ((LRed_app_right t3).trans
        (conss_nf _ _ (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _) closed_klL)))
  have t1 : LRed
      (aps conssL [aps b4bsL [byteLit a1.1 a1.2, byteLit b1.1 b1.2,
          .app b2nL (claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0)],
        aps conssL [aps b4bsL [byteLit a2.1 a2.2, byteLit b2.1 b2.2,
          .app b2nL (aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
            aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                      claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]])],
          aps conssL [aps b4bsL [byteLit a3.1 a3.2, byteLit b3.1 b3.2,
            .app b2nL (aps orL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 0,
              aps andL [claBC (byteLit a2.1 a2.2) (byteLit b2.1 b2.2) 1,
                aps orL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 0,
                  aps andL [claBC (byteLit a1.1 a1.2) (byteLit b1.1 b1.2) 1,
                            claBC (byteLit a0.1 a0.2) (byteLit b0.1 b0.2) 0]]]])],
            klL]]])
      (cellLit (byteLit (byteStepN a1 b1 (byteStepN a0 b0 0).2).1.1
        (byteStepN a1 b1 (byteStepN a0 b0 0).2).1.2)
        (cellLit (byteLit (byteStepN a2 b2
            (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.1
          (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.2)
          (cellLit (byteLit (byteStepN a3 b3
              (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.1
            (byteStepN a3 b3
              (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.2)
            klL))) :=
    (LRed_app_left (LRed_app_right hS1)).trans
      ((LRed_app_right t2).trans
        (conss_nf _ _ (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _)
            (closed_cellLit (closed_byteLit _ _) closed_klL))))
  have t0 : LRed (claSpine (byteLit a0.1 a0.2) (byteLit a1.1 a1.2)
        (byteLit a2.1 a2.2) (byteLit a3.1 a3.2)
        (byteLit b0.1 b0.2) (byteLit b1.1 b1.2)
        (byteLit b2.1 b2.2) (byteLit b3.1 b3.2))
      (cellLit (byteLit (byteStepN a0 b0 0).1.1 (byteStepN a0 b0 0).1.2)
        (cellLit (byteLit (byteStepN a1 b1 (byteStepN a0 b0 0).2).1.1
          (byteStepN a1 b1 (byteStepN a0 b0 0).2).1.2)
          (cellLit (byteLit (byteStepN a2 b2
              (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.1
            (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).1.2)
            (cellLit (byteLit (byteStepN a3 b3
                (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.1
              (byteStepN a3 b3
                (byteStepN a2 b2 (byteStepN a1 b1 (byteStepN a0 b0 0).2).2).2).1.2)
              klL)))) := by
    refine (LRed_app_left (LRed_app_right hS0)).trans ?_
    exact (LRed_app_right t1).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _)
            (closed_cellLit (closed_byteLit _ _) closed_klL))))
  exact e1.trans (t0.trans (by exact Relation.ReflTransGen.refl))

-- the equivalence -------------------------------------------------------

/-- λ-level: ripple and carry-lookahead share the `resList` reduct. -/
theorem b4add_b4cla_LJoin
    (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 16 × Fin 16) :
    LJoin (aps b4addL [b4Lit [a0, a1, a2, a3], b4Lit [b0, b1, b2, b3]])
          (aps b4claL [b4Lit [a0, a1, a2, a3], b4Lit [b0, b1, b2, b3]]) :=
  ⟨scottList ((resList [a0, a1, a2, a3] [b0, b1, b2, b3] 0).map
      (fun p => byteLit p.1 p.2)),
    b4add_eval [a0, a1, a2, a3] [b0, b1, b2, b3] rfl,
    b4cla_eval a0 a1 a2 a3 b0 b1 b2 b3⟩

-- transport to the host basis -----------------------------------------------

/-- `translate_to_basis` lifts over multi-step reduction. -/
theorem translate_preserves_red {t u : ITerm} (h : IRed t u) :
    IRedBasis (translate_to_basis t) (translate_to_basis u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (translate_preserves_step hs)

/-- The basis-level statement: the host's `import_tree(expand_s=True)`
    terms — `translate_to_basis ∘ compile` — for the zip-ripple `_B4ADD`
    and the carry-lookahead `_B4CLA` are `Join`-equivalent.  The two
    adder vocabularies are observationally the same function. -/
theorem b4add_b4cla_basis
    (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 16 × Fin 16) :
    Join (translate_to_basis (compile
            (aps b4addL [b4Lit [a0, a1, a2, a3],
                         b4Lit [b0, b1, b2, b3]])))
         (translate_to_basis (compile
            (aps b4claL [b4Lit [a0, a1, a2, a3],
                         b4Lit [b0, b1, b2, b3]]))) := by
  obtain ⟨u, h1, h2⟩ := b4add_b4cla_LJoin a0 a1 a2 a3 b0 b1 b2 b3
  exact ⟨translate_to_basis (compile u),
    translate_preserves_red (compile_simulates_red h1),
    translate_preserves_red (compile_simulates_red h2)⟩

#print axioms b4add_b4cla_basis

-- append associativity (_APPEND over Scott lists) --------------------------

/-- `_REV`/`_APPEND` applied forms. -/
def revT (l : LTerm) : LTerm :=
  .app (.app (.app foldlL stepConsL) l) nilL
def appendT (xs ys : LTerm) : LTerm :=
  .app (.app (.app foldlL stepConsL) (revT xs)) ys

/-- `l` is a Scott list of `cs`. -/
def IsList (l : LTerm) (cs : List LTerm) : Prop := LRed l (scottList cs)

theorem closed_revT {l : LTerm} (h : closed 0 l = true) :
    closed 0 (revT l) = true :=
  closed_app (closed_app (closed_app (by decide) (by decide)) h) rfl

theorem closed_appendT {xs ys : LTerm} (hx : closed 0 xs = true)
    (hy : closed 0 ys = true) : closed 0 (appendT xs ys) = true :=
  closed_app (closed_app (closed_app (by decide) (by decide))
    (closed_revT hx)) hy

/-- `_REV·(scott cs) →* scott (rev cs)` — REV is FOLDL onto nil. -/
theorem rev_eval (l : LTerm) (cs : List LTerm) (h : IsList l cs)
    (hl : closed 0 l = true) (hcs : ∀ e ∈ cs, closed 0 e = true) :
    LRed (revT l) (scottList cs.reverse) := by
  have e1 : LRed (revT l)
      (ggbA stepConsL l nilL) :=
    foldl_to_ggb stepConsL l nilL rfl hl rfl
  have e2 : LRed (ggbA stepConsL l nilL)
      (ggbA stepConsL (scottList cs) nilL) :=
    LRed_app_left (LRed_app_right h)
  have e3 := fold_read cs nilL hcs rfl
  have e4 : cs.reverse.foldr cellLit nilL = scottList cs.reverse := rfl
  exact e1.trans (e2.trans (e4 ▸ e3))

/-- `_APPEND·(scott as)·(scott bs) →* scott (as ++ bs)` — append computes
    list concatenation on the Scott encoding. -/
theorem append_eval (xs ys : LTerm) (as bs : List LTerm)
    (hx : IsList xs as) (hy : IsList ys bs)
    (has : ∀ e ∈ as, closed 0 e = true) (hbs : ∀ e ∈ bs, closed 0 e = true)
    (hcx : closed 0 xs = true) (hcy : closed 0 ys = true) :
    LRed (appendT xs ys) (scottList (as ++ bs)) := by
  have r1 := rev_eval xs as hx hcx has
  have hrev : ∀ e ∈ as.reverse, closed 0 e = true :=
    fun e he => has e (List.mem_reverse.mp he)
  have hsrev : closed 0 (scottList as.reverse) = true :=
    closed_scottList hrev
  have hsbs : closed 0 (scottList bs) = true := closed_scottList hbs
  -- congruence: revT xs → scott as.reverse inside the app spine
  have c1 : LRed (appendT xs ys)
      (.app (.app (.app foldlL stepConsL) (scottList as.reverse)) ys) :=
    LRed_app (LRed_app Relation.ReflTransGen.refl r1)
      Relation.ReflTransGen.refl
  have c2 : LRed
      (.app (.app (.app foldlL stepConsL) (scottList as.reverse)) ys)
      (ggbA stepConsL (scottList as.reverse) ys) :=
    foldl_to_ggb _ _ _ rfl hsrev hcy
  have c3 : LRed (ggbA stepConsL (scottList as.reverse) ys)
      (ggbA stepConsL (scottList as.reverse) (scottList bs)) :=
    LRed_app_right hy
  have c4 := fold_read as.reverse (scottList bs) hrev hsbs
  have e : as.reverse.reverse.foldr cellLit (scottList bs)
      = scottList (as ++ bs) := by
    rw [List.reverse_reverse]
    show as.foldr cellLit (scottList bs) = scottList (as ++ bs)
    rw [scottList, scottList, ← List.foldr_append]
  exact c1.trans (c2.trans (c3.trans (e ▸ c4)))

/-- **append_assoc on the λ-encoding**: left- and right-nested appends
    join to the same Scott list — the observational equality the
    balanced-emission question needed. -/
theorem append_assoc_L (a b c : LTerm) (as bs cs : List LTerm)
    (ha : IsList a as) (hb : IsList b bs) (hc : IsList c cs)
    (has : ∀ e ∈ as, closed 0 e = true) (hbs : ∀ e ∈ bs, closed 0 e = true)
    (hcs : ∀ e ∈ cs, closed 0 e = true)
    (hca : closed 0 a = true) (hcb : closed 0 b = true)
    (hcc : closed 0 c = true) :
    LJoin (appendT (appendT a b) c) (appendT a (appendT b c)) := by
  have hab : IsList (appendT a b) (as ++ bs) :=
    append_eval a b as bs ha hb has hbs hca hcb
  have hbc : IsList (appendT b c) (bs ++ cs) :=
    append_eval b c bs cs hb hc hbs hcs hcb hcc
  have hasbs : ∀ e ∈ as ++ bs, closed 0 e = true := by
    intro e he
    cases List.mem_append.mp he with
    | inl hm => exact has e hm
    | inr hm => exact hbs e hm
  have hbcs : ∀ e ∈ bs ++ cs, closed 0 e = true := by
    intro e he
    cases List.mem_append.mp he with
    | inl hm => exact hbs e hm
    | inr hm => exact hcs e hm
  have hL := append_eval (appendT a b) c (as ++ bs) cs hab hc hasbs hcs
    (closed_appendT hca hcb) hcc
  have hR := append_eval a (appendT b c) as (bs ++ cs) ha hbc has hbcs
    hca (closed_appendT hcb hcc)
  rw [← List.append_assoc] at hR
  exact Exists.intro _ ⟨hL, hR⟩

/-- The basis-level statement: the host's `import_tree(expand_s=True)`
    terms — `translate_to_basis ∘ compile` — are `Join`-equivalent
    under either association.  This is the formal license for
    balanced vs right-nested emission of APPEND chains. -/
theorem append_assoc_basis (as bs cs : List LTerm)
    (has : ∀ e ∈ as, closed 0 e = true)
    (hbs : ∀ e ∈ bs, closed 0 e = true)
    (hcs : ∀ e ∈ cs, closed 0 e = true) :
    Join (translate_to_basis (compile
            (appendT (appendT (scottList as) (scottList bs))
              (scottList cs))))
         (translate_to_basis (compile
            (appendT (scottList as)
              (appendT (scottList bs) (scottList cs))))) := by
  obtain ⟨u, h1, h2⟩ := append_assoc_L
    (scottList as) (scottList bs) (scottList cs) as bs cs
    Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl
    has hbs hcs
    (closed_scottList has) (closed_scottList hbs) (closed_scottList hcs)
  exact ⟨translate_to_basis (compile u),
    translate_preserves_red (compile_simulates_red h1),
    translate_preserves_red (compile_simulates_red h2)⟩

#print axioms append_assoc_basis
#print axioms spine_eval
#print axioms fold_eval

end ISAR
