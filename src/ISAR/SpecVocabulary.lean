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

-- Right-spine fixpoint (`_JOIN`, `_MAP`, `_PADTO`) --------------------
--
-- Mirror of the left-spine GGB machinery: the worker recurses on the
-- tail INSIDE the step (`st·h·(g·g·t)`), so `hstep` never reaches the
-- recursive self-application (it sits in argument position).  The
-- chain therefore carries `gsRA` raw and closes each step by one
-- `LRed_app_right` congruence — the structural difference from
-- `foldG`, where `g·g·t·(…)` keeps the recursion in spine position.

/-- `RG st z = \g.\l2. l2 z (\h.\t. st·h·(g·g·t))` — right-spine worker:
    the `(\f. f f)` fixpoint that recurses on the tail inside the step
    (`_JOIN`, `_MAP`, `_PADTO`).  Mirror of `foldG`: `st`/`z` must be
    closed so their shifts under the binders are no-ops. -/
def fixrG (st z : LTerm) : LTerm :=
  .abs (.abs (.app (.app (.var 0) (shift 2 0 z))
    (.abs (.abs (.app (.app (shift 4 0 st) (.var 1))
      (.app (.app (.var 3) (.var 3)) (.var 0)))))))

/-- once-unfolded right worker — computed reduct of `fixrG·fixrG`. -/
def RGR (st z : LTerm) : LTerm :=
  hsteps 1 (.app (fixrG st z) (fixrG st z))

/-- `(fixrG·fixrG)·l` — the running right-fold state. -/
def gsRA (st z l : LTerm) : LTerm :=
  .app (.app (fixrG st z) (fixrG st z)) l

/-- `RGR st z · l` -/
def rgrA (st z l : LTerm) : LTerm := .app (RGR st z) l

/-- `(W·(fixrG st z))·l` — the `(\f. f f)` entry applied to the spine. -/
def fixrA (st z l : LTerm) : LTerm :=
  .app (.app wl (fixrG st z)) l

theorem gsRA_to_rgrA (st z l : LTerm) :
    LRed (gsRA st z l) (rgrA st z l) :=
  LRed_of_hsteps (k := 1) rfl

/-- `W·(fixrG st z)·l →* RGR st z·l` — entry unfold through W·RG. -/
theorem fixr_to_rgr (st z l : LTerm) (hs : closed 0 st = true)
    (hz : closed 0 z = true) (hl : closed 0 l = true) :
    LRed (fixrA st z l) (rgrA st z l) :=
  LRed_of_hsteps (k := 2) (by
    simp [gsRA, rgrA, fixrA, RGR, fixrG, wl, nilL, cellLit, conssL,
          hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 hz,
          subst_of_closed0 hs, subst_of_closed0 hz])

/-- nil unfold for ANY closed step/nil-value —
    `RGR st z·nil →* z`. -/
theorem rnil_unfold (st z : LTerm) (hs : closed 0 st = true)
    (hz : closed 0 z = true) :
    LRed (rgrA st z nilL) z :=
  LRed_of_hsteps (k := 3) (by
    simp [gsRA, rgrA, RGR, fixrG, wl, nilL, cellLit, conssL,
          hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 hz,
          subst_of_closed0 hs, subst_of_closed0 hz])

/-- cell unfold for ANY closed step/nil-value —
    `RGR st z·(cell h t) →* st·h·(RGR st z·t)`.  `hstep` never descends
    into arguments, so the recursion `fixrG·fixrG·t` stays unreduced
    inside the step argument — one `LRed_app_right` congruence step
    (`gsRA_to_rgrA`) folds it into `RGR` form. -/
theorem rcell_unfold (st z h t : LTerm) (hs : closed 0 st = true)
    (hz : closed 0 z = true) (hh : closed 0 h = true)
    (ht : closed 0 t = true) :
    LRed (rgrA st z (cellLit h t))
         (.app (.app st h) (rgrA st z t)) :=
  (LRed_of_hsteps (k := 5) (by
    simp [gsRA, rgrA, RGR, fixrG, wl, nilL, cellLit, conssL,
          hsteps, hstep, subst, shift,
          shift_of_closed0 hs, shift_of_closed0 hz, shift_of_closed0 hh,
          shift_of_closed0 ht,
          subst_of_closed0 hs, subst_of_closed0 hz, subst_of_closed0 hh,
          subst_of_closed0 ht])).trans
    (LRed_app_right (gsRA_to_rgrA st z t))

/-- Right-spine unfold: `RGR st z` over `scottList cs` unfolds exactly
    `cs.length` times into the unreduced `foldr` chain
    `st·c·(st·c'·(…·z))`. -/
theorem spine_run_r (st z : LTerm) (hs : closed 0 st = true)
    (hz : closed 0 z = true) :
    ∀ (cs : List LTerm), (∀ e ∈ cs, closed 0 e = true) →
      LRed (rgrA st z (scottList cs))
           (cs.foldr (fun e r => .app (.app st e) r) z) := by
  intro cs; induction cs with
  | nil =>
    intro _
    simp only [scottList, List.foldr_nil]
    exact rnil_unfold st z hs hz
  | cons c cs' ih =>
    intro hcl
    have hc : closed 0 c = true := hcl c List.mem_cons_self
    have htail : ∀ e ∈ cs', closed 0 e = true :=
      fun e he => hcl e (List.mem_cons_of_mem c he)
    rw [show scottList (c :: cs') = cellLit c (scottList cs') from rfl,
        List.foldr_cons]
    exact (rcell_unfold st z c (scottList cs') hs hz hc
      (closed_scottList htail)).trans (LRed_app_right (ih htail))

/-- Closedness is preserved through a semantic `foldr`. -/
theorem closed_foldr (σ : LTerm → LTerm → LTerm) (z : LTerm)
    (hz : closed 0 z = true)
    (hσ : ∀ e r, closed 0 e = true → closed 0 r = true →
      closed 0 (σ e r) = true) :
    ∀ (cs : List LTerm), (∀ e ∈ cs, closed 0 e = true) →
      closed 0 (cs.foldr σ z) = true := by
  intro cs; induction cs with
  | nil => intro _; exact hz
  | cons c cs' ih =>
    intro hcl
    have hc : closed 0 c = true := hcl c List.mem_cons_self
    rw [List.foldr_cons]
    exact hσ c _ hc (ih (fun e he => hcl e (List.mem_cons_of_mem c he)))

/-- Right chain reduction: a `foldr` chain of unreduced step
    applications reduces to the semantic `foldr` of `σ`, given the
    per-step lemma `st·e·r →* σ e r` on closed inputs.  Mirror of
    `foldl_red` — simpler here: the unreduced recursion sits in the
    step's argument, so congruence composes directly without an
    accumulator-pair invariant. -/
theorem foldr_red (st z : LTerm) (σ : LTerm → LTerm → LTerm)
    (hz : closed 0 z = true)
    (hstep : ∀ e r, closed 0 e = true → closed 0 r = true →
      LRed (.app (.app st e) r) (σ e r) ∧
      closed 0 (σ e r) = true) :
    ∀ (cs : List LTerm), (∀ e ∈ cs, closed 0 e = true) →
      LRed (cs.foldr (fun e r => .app (.app st e) r) z)
           (cs.foldr σ z) := by
  intro cs; induction cs with
  | nil => intro _; exact Relation.ReflTransGen.refl
  | cons c cs' ih =>
    intro hcl
    have hc : closed 0 c = true := hcl c List.mem_cons_self
    have htail : ∀ e ∈ cs', closed 0 e = true :=
      fun e he => hcl e (List.mem_cons_of_mem c he)
    rw [List.foldr_cons, List.foldr_cons]
    refine (LRed_app_right (ih htail)).trans ?_
    exact (hstep c _ hc (closed_foldr σ z hz
      (fun e r he hr => (hstep e r he hr).2) cs' htail)).1

/-- **Right FixSpine, composed**: `RGR st z` over `scottList cs`
    reduces to the semantic `foldr` of `σ`.  Mirror of `spine_eval`. -/
theorem spine_eval_r (st z : LTerm) (σ : LTerm → LTerm → LTerm)
    (hs : closed 0 st = true) (hz : closed 0 z = true)
    (hstep : ∀ e r, closed 0 e = true → closed 0 r = true →
      LRed (.app (.app st e) r) (σ e r) ∧
      closed 0 (σ e r) = true) :
    ∀ (cs : List LTerm), (∀ e ∈ cs, closed 0 e = true) →
      LRed (rgrA st z (scottList cs)) (cs.foldr σ z) :=
  fun cs hcl => (spine_run_r st z hs hz cs hcl).trans
    (foldr_red st z σ hz hstep cs hcl)

/-- Right head form: `(W·fixrG)·l →* cs.foldr σ z` whenever
    `l →* scottList cs`.  The recipe for `_JOIN`, `_MAP`, and every
    right-spine fold head. -/
theorem fixr_eval (st z : LTerm) (σ : LTerm → LTerm → LTerm)
    (hs : closed 0 st = true) (hz : closed 0 z = true)
    (hstep : ∀ e r, closed 0 e = true → closed 0 r = true →
      LRed (.app (.app st e) r) (σ e r) ∧
      closed 0 (σ e r) = true) :
    ∀ (l : LTerm) (cs : List LTerm),
      closed 0 l = true → LRed l (scottList cs) →
      (∀ e ∈ cs, closed 0 e = true) →
      LRed (fixrA st z l) (cs.foldr σ z) :=
  fun l cs hl hlcs hcl =>
    (fixr_to_rgr st z l hs hz hl).trans
      ((LRed_app_right hlcs).trans
        (spine_eval_r st z σ hs hz hstep cs hcl))

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

-- _JOIN: the right-spine concat every stage's chunk emission uses ----

/-- `_APPEND` as a head: `\xs.\ys. FOLDL·stepCons·(REV xs)·ys`. -/
def appendL : LTerm :=
  .abs (.abs (aps foldlL [stepConsL, revT (.var 1), .var 0]))

theorem closed_appendL : closed 0 appendL = true := by decide

/-- `_JOIN = \l. W·(RG appendL nil)·l` — right-spine list concat. -/
def joinL : LTerm := .abs (fixrA appendL nilL (.var 0))

theorem closed_joinL : closed 0 joinL = true := by decide

/-- `appendL·xs·ys` β-unfolds to the `appendT xs ys` applied form. -/
theorem appendL_to_appendT (xs ys : LTerm) (hx : closed 0 xs = true)
    (hy : closed 0 ys = true) :
    LRed (.app (.app appendL xs) ys) (appendT xs ys) :=
  LRed_of_hsteps (k := 2) (by
    simp [appendL, appendT, revT, aps, List.foldl, hsteps, hstep, subst,
          shift, shift_of_closed0 hx, shift_of_closed0 hy,
          subst_of_closed0 hx, subst_of_closed0 hy,
          shift_of_closed0 closed_foldlL,
          subst_of_closed0 closed_foldlL,
          shift_of_closed0 closed_stepConsL,
          subst_of_closed0 closed_stepConsL,
          shift_of_closed0 closed_nilL,
          subst_of_closed0 closed_nilL])

/-- `joinL·l` β-unfolds to the generic right-fixpoint applied form.
    `appendL` stays folded — the embedded `shift 4 0 appendL` in
    `fixrG` rewrites atomically via `shift_of_closed0`. -/
theorem joinL_to_fixr (l : LTerm) (hl : closed 0 l = true) :
    LRed (.app joinL l) (fixrA appendL nilL l) :=
  LRed_of_hsteps (k := 1) (by
    simp [joinL, fixrA, fixrG, wl, nilL, hsteps, hstep, subst,
          shift, shift_of_closed0 hl, subst_of_closed0 hl,
          shift_of_closed0 closed_appendL,
          subst_of_closed0 closed_appendL,
          shift_of_closed0 closed_nilL, subst_of_closed0 closed_nilL])

/-- foldr of `appendT` over Scott-list cells flattens the lists. -/
theorem appendT_foldr_scott : ∀ (bss : List (List LTerm)),
    (∀ e ∈ bss.flatten, closed 0 e = true) →
    LRed ((bss.map scottList).foldr appendT nilL)
         (scottList bss.flatten) := by
  intro bss; induction bss with
  | nil => intro _; exact Relation.ReflTransGen.refl
  | cons bs bss' ih =>
    intro hcl
    rw [List.map_cons, List.foldr_cons, List.flatten_cons]
    have hbs : ∀ e ∈ bs, closed 0 e = true :=
      fun e he => hcl e (List.mem_append_left _ he)
    have htail : ∀ e ∈ bss'.flatten, closed 0 e = true :=
      fun e he => hcl e (List.mem_append_right _ he)
    refine (LRed_app_right (ih htail)).trans ?_
    exact append_eval _ _ _ _ Relation.ReflTransGen.refl
      Relation.ReflTransGen.refl hbs htail
      (closed_scottList hbs) (closed_scottList htail)

/-- **`_JOIN` eval**: `JOIN` over a Scott list of Scott lists reduces
    to the Scott list of the flattened elements — the concat every
    stage's chunk emission is built on.  First head discharged purely
    by `fixr_eval` — the per-head obligation is the two-step
    `appendL→appendT` unfold. -/
theorem join_eval (bss : List (List LTerm))
    (h : ∀ e ∈ bss.flatten, closed 0 e = true) :
    LRed (.app joinL (scottList (bss.map scottList)))
         (scottList bss.flatten) := by
  have hcells : ∀ e ∈ bss.map scottList, closed 0 e = true := by
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨bs, hbs, rfl⟩ := he
    exact closed_scottList
      (fun x hx => h x (List.mem_flatten.mpr ⟨bs, hbs, hx⟩))
  have hs' : ∀ e r, closed 0 e = true → closed 0 r = true →
      LRed (.app (.app appendL e) r) (appendT e r) ∧
      closed 0 (appendT e r) = true :=
    fun e r he hr =>
      ⟨appendL_to_appendT e r he hr, closed_appendT he hr⟩
  have e1 := fixr_eval appendL nilL appendT closed_appendL closed_nilL
    hs' _ _ (closed_scottList hcells) Relation.ReflTransGen.refl hcells
  exact (joinL_to_fixr _ (closed_scottList hcells)).trans
    (e1.trans (appendT_foldr_scott bss h))

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

-- Church numerals + iteration (_ZEROFILL, _num_src args) --------------
--
-- Third bounded pattern alongside the two spine fixpoints: Church
-- numerals unfold `n` applications of a step — measure = the numeral
-- itself.  `church_eval` is the unfold, `iter_red` the chain lemma
-- (sibling of `foldl_red`/`foldr_red`).

/-- `f^n·x` as a λ-body (var 1 = f, var 0 = x). -/
def churchBody : Nat → LTerm
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchBody n)

/-- Church numeral `\f.\x. f^n x` — `_church_src`. -/
def churchL (n : Nat) : LTerm := .abs (.abs (churchBody n))

/-- `f` applied `n` times to `z` — the iteration chain. -/
def iterL (f z : LTerm) : Nat → LTerm
  | 0 => z
  | n + 1 => .app f (iterL f z n)

/-- `σ` applied `n` times to `z` — the semantic iterate (metalevel). -/
def iterS (σ : LTerm → LTerm) (z : LTerm) : Nat → LTerm
  | 0 => z
  | n + 1 => σ (iterS σ z n)

theorem closed_churchBody (n : Nat) :
    closed 2 (churchBody n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [churchBody, closed]; exact ih

theorem closed_churchL (n : Nat) : closed 0 (churchL n) = true :=
  closed_churchBody n

theorem closed_iterL (f z : LTerm) (hf : closed 0 f = true)
    (hz : closed 0 z = true) (n : Nat) :
    closed 0 (iterL f z n) = true := by
  induction n with
  | zero => exact hz
  | succ n ih => exact closed_app hf ih

theorem closed_iterS (σ : LTerm → LTerm)
    (hσ : ∀ x, closed 0 x = true → closed 0 (σ x) = true)
    (z : LTerm) (hz : closed 0 z = true) (n : Nat) :
    closed 0 (iterS σ z n) = true := by
  induction n with
  | zero => exact hz
  | succ n ih => exact hσ _ ih

/-- `subst f 1` turns the Church body into the iteration chain on
    `var 0`. -/
theorem subst_churchBody (n : Nat) (f : LTerm)
    (hf : closed 0 f = true) :
    subst f 1 (churchBody n) = iterL f (.var 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [churchBody, subst, iterL, ih, shift_of_closed0 hf]

/-- `subst z 0` on the chain instantiates the base variable. -/
theorem subst_iterL (n : Nat) (f z : LTerm)
    (hf : closed 0 f = true) (hz : closed 0 z = true) :
    subst z 0 (iterL f (.var 0) n) = iterL f z n := by
  induction n with
  | zero =>
    simp only [iterL, subst]
    exact shift_of_closed0 hz 0 0
  | succ n ih =>
    simp only [iterL, subst]
    rw [subst_of_closed0 hf, ih]

/-- **Numeral unfold**: `churchL n·f·z →* f^n·z` — the third bounded
    form: Church iteration, measure = the numeral itself. -/
theorem church_eval (n : Nat) (f z : LTerm)
    (hf : closed 0 f = true) (hz : closed 0 z = true) :
    LRed (.app (.app (churchL n) f) z) (iterL f z n) :=
  LRed_of_hsteps (k := 2) (by
    simp only [churchL, hsteps, hstep, subst]
    rw [subst_churchBody n f hf, subst_iterL n f z hf hz])

/-- **Iter chain reduction**: if each `st·x →* σ x` on closed `x`,
    an `n`-fold application chain reduces to the `n`-fold semantic
    iterate.  Sibling of `foldl_red`/`foldr_red` for the numeral
    pattern. -/
theorem iter_red (st : LTerm) (σ : LTerm → LTerm)
    (hstep : ∀ x, closed 0 x = true →
      LRed (.app st x) (σ x) ∧ closed 0 (σ x) = true) :
    ∀ (n : Nat) (z : LTerm), closed 0 z = true →
      LRed (iterL st z n) (iterS σ z n) := by
  intro n z hz
  induction n generalizing z with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [iterL, iterS]
    have hcl : closed 0 (iterS σ z n) = true :=
      closed_iterS σ (fun e he => (hstep e he).2) z hz n
    exact (LRed_app_right (ih z hz)).trans (hstep _ hcl).1

-- _ZEROFILL: n zero-byte cells via Church iteration --------------------

/-- `_B0C` — the unreduced `PAIR sel0 sel0` byte literal. -/
def b0cT : LTerm := aps pairSrcL [nibLit 0, nibLit 0]

theorem closed_b0cT : closed 0 b0cT = true := by decide

/-- `_ZEROFILL`'s cons-step: `\l. CONSS B0C l`. -/
def zerostepL : LTerm := .abs (aps conssL [b0cT, .var 0])

theorem closed_zerostepL : closed 0 zerostepL = true := by decide

/-- `_ZEROFILL = \n. n·zerostep·K`. -/
def zerofillL : LTerm := .abs (aps (.var 0) [zerostepL, klL])

theorem closed_zerofillL : closed 0 zerofillL = true := by decide

/-- `zerostepL·x →* cellLit b0cT x` — the per-step lemma. -/
theorem zerostep_cell (x : LTerm) (hx : closed 0 x = true) :
    LRed (.app zerostepL x) (cellLit b0cT x) :=
  (LRed_of_hsteps (k := 1) (by
    simp [zerostepL, aps, List.foldl, hsteps, hstep, subst, shift,
          shift_of_closed0 hx, subst_of_closed0 hx,
          shift_of_closed0 closed_b0cT, subst_of_closed0 closed_b0cT,
          shift_of_closed0 closed_conssL,
          subst_of_closed0 closed_conssL])).trans
    (conss_nf b0cT x closed_b0cT hx)

/-- `iterS (cellLit b) z n` IS `replicate n b` folded into `z`. -/
theorem iterS_scott (b z : LTerm) :
    ∀ n : Nat, iterS (fun x => cellLit b x) z n
             = (List.replicate n b).foldr cellLit z := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterS, List.replicate_succ, List.foldr_cons, ih]

/-- **`_ZEROFILL` eval**: `ZEROFILL·(churchL n)` reduces to `n`
    zero-byte cells — numeral-unfold + iter_red.  The element NF is
    the unreduced `PAIR sel0 sel0` — weak-head normalization reaches
    the spine; element interiors normalize on consumption. -/
theorem zerofill_eval (n : Nat) :
    LRed (.app zerofillL (churchL n))
         (scottList (List.replicate n b0cT)) := by
  have e1 : LRed (.app zerofillL (churchL n))
      (iterL zerostepL klL n) :=
    (LRed_of_hsteps (k := 1) (by
      simp [zerofillL, aps, List.foldl, hsteps, hstep, subst, shift,
            shift_of_closed0 (closed_churchL n),
            subst_of_closed0 (closed_churchL n),
            shift_of_closed0 closed_zerostepL,
            subst_of_closed0 closed_zerostepL,
            shift_of_closed0 closed_klL,
            subst_of_closed0 closed_klL])).trans
      (church_eval n zerostepL klL closed_zerostepL closed_klL)
  have hs' : ∀ x, closed 0 x = true →
      LRed (.app zerostepL x) (cellLit b0cT x) ∧
      closed 0 (cellLit b0cT x) = true :=
    fun x hx => ⟨zerostep_cell x hx, closed_cellLit closed_b0cT hx⟩
  have hsc : iterS (fun x => cellLit b0cT x) klL n
      = scottList (List.replicate n b0cT) := by
    rw [iterS_scott]; rfl
  exact e1.trans ((iter_red zerostepL (fun x => cellLit b0cT x) hs'
    n klL closed_klL).trans (hsc ▸ Relation.ReflTransGen.refl))

#print axioms append_assoc_basis
#print axioms spine_eval
#print axioms fold_eval
#print axioms spine_eval_r
#print axioms fixr_eval
#print axioms join_eval
#print axioms zerofill_eval

-- ============================================================
-- _B4INC: bytes4 increment — peel + early-exit INCB carry chain.
-- ============================================================

-- nibble successor table ---------------------------------------

/-- `_NIBSUCC = (\a. a sel_1 sel_2 … sel_15 sel_0)` — picks succ. -/
def nibsuccL : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun j : Fin 16 =>
    nibLit ⟨(j.val + 1) % 16, by omega⟩))

theorem closed_nibsuccL : closed 0 nibsuccL = true := by decide

/-- `_NIBIS15 = (\a. a BF×15 BT)` — picks BT iff a = 15. -/
def nibis15L : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun j : Fin 16 =>
    boolLit (decide (j.val = 15))))

theorem closed_nibis15L : closed 0 nibis15L = true := by decide

theorem nibsucc_table : ∀ i : Fin 16,
    hsteps 24 (aps nibsuccL [nibLit i])
      = nibLit ⟨(i.val + 1) % 16, by omega⟩ := by
  decide

theorem nibis15_table : ∀ i : Fin 16,
    hsteps 24 (aps nibis15L [nibLit i])
      = boolLit (decide (i.val = 15)) := by
  decide

theorem nibsucc_correct (i : Fin 16) :
    LRed (aps nibsuccL [nibLit i])
         (nibLit ⟨(i.val + 1) % 16, by omega⟩) :=
  LRed_of_hsteps (nibsucc_table i)

theorem nibis15_correct (i : Fin 16) :
    LRed (aps nibis15L [nibLit i]) (boolLit (decide (i.val = 15))) :=
  LRed_of_hsteps (nibis15_table i)

-- bool dispatch ------------------------------------------------

/-- `boolLit b·x·y →* x`/`y` — Church-boolean if-then-else. -/
theorem boolLit_branch (b : Bool) (x y : LTerm)
    (hx : closed 0 x = true) (hy : closed 0 y = true) :
    LRed (aps (boolLit b) [x, y]) (if b then x else y) := by
  cases b <;>
    simp only [boolLit, aps, List.foldl, ite_true, ite_false] <;>
    exact LRed_of_hsteps (k := 2) (by
      simp [klL, kilL, hsteps, hstep, subst, shift,
            shift_of_closed0 hx, subst_of_closed0 hx,
            shift_of_closed0 hy, subst_of_closed0 hy])

-- INCB: byte increment → (byte', carry) -------------------------
--
-- `_INCB = \b. b (\lo.\hi. (NIBIS15 lo)
--   (PAIR (PAIR sel0 (NIBSUCC hi)) (NIBIS15 hi))
--   (PAIR (PAIR (NIBSUCC lo) hi) BF))`
-- b = byteLit lo hi = pairLit loN hiN — applied to the continuation
-- peels lo,hi into head position.

/-- `_INCB`'s continuation body, lo = var 1, hi = var 0. -/
def incbCont : LTerm :=
  .abs (.abs
    (aps (aps nibis15L [.var 1])
      [ aps pairSrcL
          [ aps pairSrcL [nibLit 0, aps nibsuccL [.var 0]],
            aps nibis15L [.var 0]],
        aps pairSrcL
          [ aps pairSrcL [aps nibsuccL [.var 1], .var 0],
            kilL ] ]))

/-- `_INCB = \b. b incbCont`. -/
def incbL : LTerm := .abs (.app (.var 0) incbCont)

theorem closed_incbCont : closed 2 incbCont = true := by decide

theorem closed_incbL : closed 0 incbL = true := by decide

/-- Byte-level semantic increment: (byte', carry-out). -/
def incByteN (lo hi : Fin 16) : (Fin 16 × Fin 16) × Bool :=
  if lo.val = 15 then
    (⟨0, ⟨(hi.val + 1) % 16, by omega⟩⟩, hi.val = 15)
  else
    ((⟨(lo.val + 1) % 16, by omega⟩, hi), false)

/-- `INCB·(byteLit lo hi)` — milestone: peel `b`, run `incbCont` — the
    `nibis15` dispatch over the two PAIR branches (raw apps inside). -/
theorem incb_unfold (lo hi : Fin 16) :
    LRed (.app incbL (byteLit lo hi))
         (aps (aps nibis15L [nibLit lo])
           [ aps pairSrcL
               [ aps pairSrcL [nibLit 0, aps nibsuccL [nibLit hi]],
                 aps nibis15L [nibLit hi]],
             aps pairSrcL
               [ aps pairSrcL [aps nibsuccL [nibLit lo], nibLit hi],
                 kilL ] ]) :=
  LRed_of_hsteps (k := 4) (by
    simp [incbL, incbCont, byteLit, pairLit, aps, List.foldl,
          hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0,
          closed_nibLit, closed_nibsuccL, closed_nibis15L,
          closed_pairSrcL, closed_kilL])

/-- Inner: normalize `pairSrcL·(nibsucc·hiN)·x` → `pairLit (nibLit hi') x`-
    shaped milestones — the ordering discipline: nibsucc normalizes in
    argument position before the pairSrc head collapses. -/
private theorem incb_branchA (hi : Fin 16) :
    LRed (aps pairSrcL
           [ aps pairSrcL [nibLit 0, aps nibsuccL [nibLit hi]],
             aps nibis15L [nibLit hi]])
         (pairLit (byteLit 0 ⟨(hi.val + 1) % 16, by omega⟩)
                  (boolLit (decide (hi.val = 15)))) := by
  have hs : LRed (aps nibsuccL [nibLit hi])
      (nibLit ⟨(hi.val + 1) % 16, by omega⟩) := nibsucc_correct hi
  have hc : LRed (aps nibis15L [nibLit hi])
      (boolLit (decide (hi.val = 15))) := nibis15_correct hi
  -- normalize inside the byte-pair: nibsucc in arg position, then
  -- pairSrc collapses to the byteLit.
  have hb : LRed (aps pairSrcL [nibLit 0, aps nibsuccL [nibLit hi]])
      (byteLit 0 ⟨(hi.val + 1) % 16, by omega⟩) :=
    (LRed_app_right hs).trans
      (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _))
  -- lift both normalizations into the outer pairSrc's arguments.
  exact ((LRed_app_left (LRed_app_right hb)).trans
    (LRed_app_right hc)).trans
    (pairSrc_nf _ _ (closed_byteLit _ _) (closed_boolLit _))

private theorem incb_branchB (lo hi : Fin 16) :
    LRed (aps pairSrcL
           [ aps pairSrcL [aps nibsuccL [nibLit lo], nibLit hi],
             kilL ])
         (pairLit (byteLit ⟨(lo.val + 1) % 16, by omega⟩ hi)
                  (boolLit false)) := by
  have hs : LRed (aps nibsuccL [nibLit lo])
      (nibLit ⟨(lo.val + 1) % 16, by omega⟩) := nibsucc_correct lo
  have hb : LRed (aps pairSrcL [aps nibsuccL [nibLit lo], nibLit hi])
      (byteLit ⟨(lo.val + 1) % 16, by omega⟩ hi) :=
    -- nibsucc sits in the FIRST argument: lift through app-left.
    (LRed_app_left (LRed_app_right hs)).trans
      (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _))
  exact ((LRed_app_left (LRed_app_right hb))).trans
    (pairSrc_nf _ _ (closed_byteLit _ _) closed_kilL)

/-- **`INCB` eval**: byte increment computes `incByteN` — (byte', carry)
    as a normalized pair.  All components reduce in argument position
    before the pairLit heads close over them. -/
theorem incb_eval (lo hi : Fin 16) :
    LRed (.app incbL (byteLit lo hi))
         (pairLit (Function.uncurry byteLit (incByteN lo hi).1)
                  (boolLit (incByteN lo hi).2)) := by
  have hA := incb_branchA hi
  have hB := incb_branchB lo hi
  -- lift both branch normalizations into the dispatch's arguments.
  have hdisp : LRed (aps (aps nibis15L [nibLit lo])
        [ aps pairSrcL
            [ aps pairSrcL [nibLit 0, aps nibsuccL [nibLit hi]],
              aps nibis15L [nibLit hi]],
          aps pairSrcL
            [ aps pairSrcL [aps nibsuccL [nibLit lo], nibLit hi],
              kilL ] ])
      (aps (boolLit (decide (lo.val = 15)))
        [ pairLit (byteLit 0 ⟨(hi.val + 1) % 16, by omega⟩)
                  (boolLit (decide (hi.val = 15))),
          pairLit (byteLit ⟨(lo.val + 1) % 16, by omega⟩ hi)
                  (boolLit false) ]) :=
    (LRed_app_left (LRed_app_left (nibis15_correct lo))).trans
      ((LRed_app_left (LRed_app_right hA)).trans
        (LRed_app_right hB))
  have hclosedA : closed 0 (pairLit (byteLit 0
      ⟨(hi.val + 1) % 16, by omega⟩)
      (boolLit (decide (hi.val = 15)))) = true :=
    closed_pairLit (closed_mono (closed_byteLit _ _) (Nat.zero_le 1))
      (closed_mono (closed_boolLit _) (Nat.zero_le 1))
  have hclosedB : closed 0 (pairLit (byteLit
      ⟨(lo.val + 1) % 16, by omega⟩ hi) (boolLit false)) = true :=
    closed_pairLit (closed_mono (closed_byteLit _ _) (Nat.zero_le 1))
      (closed_mono (closed_boolLit _) (Nat.zero_le 1))
  have hbr : LRed (aps (boolLit (decide (lo.val = 15)))
        [ pairLit (byteLit 0 ⟨(hi.val + 1) % 16, by omega⟩)
                  (boolLit (decide (hi.val = 15))),
          pairLit (byteLit ⟨(lo.val + 1) % 16, by omega⟩ hi)
                  (boolLit false) ])
      (if decide (lo.val = 15)
        then pairLit (byteLit 0 ⟨(hi.val + 1) % 16, by omega⟩)
                     (boolLit (decide (hi.val = 15)))
        else pairLit (byteLit ⟨(lo.val + 1) % 16, by omega⟩ hi)
                     (boolLit false)) :=
    boolLit_branch _ _ _ hclosedA hclosedB
  refine (incb_unfold lo hi).trans (hdisp.trans (hbr.trans ?_))
  by_cases h : lo.val = 15 <;>
    simp only [incByteN, h, decide_true, decide_false, ite_true,
               ite_false, Function.uncurry, List.map] <;>
    rfl

-- generic pair application ----------------------------------------

/-- `shift 0` is the identity on any term. -/
theorem shift_zero (c : Nat) (t : LTerm) : shift 0 c t = t := by
  induction t generalizing c with
  | var n => simp [shift]
  | abs b ih => simp [shift, ih]
  | app f x ihf ihx => simp [shift, ihf, ihx]

/-- β-hole cancellation: `shift 1 c` opens a hole at index `c`;
    `subst s c` fills it — net identity. -/
theorem subst_shift_succ (s : LTerm) (c : Nat) (t : LTerm) :
    subst s c (shift 1 c t) = t := by
  induction t generalizing c with
  | var n =>
      show subst s c (if n < c then .var n else .var (n + 1)) = .var n
      split
      · rename_i h
        show subst s c (.var n) = .var n
        simp [subst, h]
      · rename_i h
        show subst s c (.var (n + 1)) = .var n
        show (if n + 1 < c then .var (n + 1)
              else if n + 1 = c then shift c 0 s else .var n) = .var n
        rw [if_neg (by omega), if_neg (by omega)]
  | abs b ih =>
      show subst s c (LTerm.abs (shift 1 (c + 1) b)) = LTerm.abs b
      show LTerm.abs (subst s (c + 1) (shift 1 (c + 1) b)) = LTerm.abs b
      rw [ih]
  | app f x ihf ihx =>
      show subst s c (LTerm.app (shift 1 c f) (shift 1 c x)) = LTerm.app f x
      show LTerm.app (subst s c (shift 1 c f)) (subst s c (shift 1 c x)) =
        LTerm.app f x
      rw [ihf, ihx]

/-- `pairLit a b · k →* k·a·b` — the Church pair consumed by a
    two-argument continuation. -/
theorem pairLit_apply (a b k : LTerm) (ha : closed 0 a = true)
    (hb : closed 0 b = true) :
    LRed (.app (pairLit a b) k) (.app (.app k a) b) :=
  LRed_of_hsteps (k := 1) (by
    simp [pairLit, hsteps, hstep, subst, shift, shift_zero,
          shift_of_closed0 ha, subst_of_closed0 ha,
          shift_of_closed0 hb, subst_of_closed0 hb])

-- emit-tail normalization ------------------------------------------
--
-- `emit cells` = conss-fold into K=nilL.  Cells normalize inside-out:
-- the tail reduces in argument position before the outer conss
-- collapses — the only ordering that reaches `scottList` under a
-- no-under-binder LStep.

/-- emit tail: `_conss`-fold of cell terms into `nilL`. -/
def emitCells : List LTerm → LTerm := fun cs =>
  cs.foldr (fun c t => aps conssL [c, t]) nilL

theorem closed_emitCells {cs : List LTerm}
    (hcl : ∀ c ∈ cs, closed 0 c = true) :
    closed 0 (emitCells cs) = true := by
  induction cs with
  | nil => exact closed_nilL
  | cons c cs ih =>
    simp only [emitCells, List.foldr_cons]
    exact closed_app (closed_app closed_conssL
      (hcl c List.mem_cons_self))
      (ih (fun e he => hcl e (List.mem_cons_of_mem c he)))

/-- **`emit` NF**: the conss-fold normalizes to the `cellLit`-chain
    `scottList` — induction inside-out through `LRed_app_right`. -/
theorem emitCells_nf : ∀ (cs : List LTerm),
    (∀ c ∈ cs, closed 0 c = true) →
    LRed (emitCells cs) (scottList cs) := by
  intro cs hcl
  induction cs with
  | nil => exact Relation.ReflTransGen.refl
  | cons c cs ih =>
    have hcc : closed 0 c = true := hcl c List.mem_cons_self
    have hrest : closed 0 (scottList cs) = true :=
      closed_scottList (fun e he => hcl e (List.mem_cons_of_mem c he))
    simp only [emitCells, List.foldr_cons, scottList]
    exact (LRed_app_right
      (ih (fun e he => hcl e (List.mem_cons_of_mem c he)))).trans
      (conss_nf c _ hcc hrest)

-- the b4inc term ----------------------------------------------------
--
-- `_b4inc_body` = peel 4 byte cells, then the INCB early-exit chain.
-- de Bruijn tables (proved by construction):
--   at chain(i) — inside K2_{i-1}'s body, depth 8+2i:
--     b_i = var 7   (each level adds 2 binders; b_i moves down 2)
--   inside K2_i's λnb.λc body (depth 10+2i):
--     c_i = var 0,  nb_i = var 1,
--     nb_j (j<i) = 2(i-j)+1,
--     b_k        = 2i+9-2k   (b3=2i+3 … b0=2i+9)

/-- `emit(prefix ++ [nb_i] ++ [b_{i+1}..b_3])` inside K2_i's body.
    Literal cells (the `List.range` computation leaves opaque meta-terms
    that `subst` cannot descend into — keep it concrete). -/
def b4incEmit : Nat → LTerm
  | 0 => emitCells [.var 1, .var 7, .var 5, .var 3]
  | 1 => emitCells [.var 3, .var 1, .var 7, .var 5]
  | 2 => emitCells [.var 5, .var 3, .var 1, .var 7]
  | _ => emitCells [.var 7, .var 5, .var 3, .var 1]

/-- `λnb_i.λc_i. c_i·NEXT·EMIT` — level-i continuation. -/
def b4incK2 (i : Nat) (next : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0) [next, b4incEmit i]))

/-- chain(4): emit all four accumulated nb cells. -/
def b4incNext3 : LTerm := b4incEmit 3

def b4incChain3 : LTerm :=
  .app (.app incbL (.var 7)) (b4incK2 3 b4incNext3)
def b4incChain2 : LTerm :=
  .app (.app incbL (.var 7)) (b4incK2 2 b4incChain3)
def b4incChain1 : LTerm :=
  .app (.app incbL (.var 7)) (b4incK2 1 b4incChain2)
def b4incChain0 : LTerm :=
  .app (.app incbL (.var 7)) (b4incK2 0 b4incChain1)

/-- `_B4INC = \v. v K (λb0.λt0. t0 K (λb1.λt1. t1 K (λb2.λt2. t2 K
    (λb3.λt3. chain0))))`. -/
def b4incL : LTerm :=
  .abs (aps (.var 0)
    [klL, .abs (.abs (aps (.var 0)
    [klL, .abs (.abs (aps (.var 0)
    [klL, .abs (.abs (aps (.var 0)
    [klL, .abs (.abs b4incChain0)]))]))]))])

theorem closed_b4incL : closed 0 b4incL = true := by
  decide

-- value-parameterized chain (peel substitution applied) --------------
--
-- After the peel substitutes B_i := byteLit_i into the b-vars, each
-- level's emit-list is `[nb_0..nb_i]` (bound vars) ++ the remaining byte
-- suffix `[B_{i+1}..B_3]` (substituted literals, closed → unshifted).
-- nb_j sits at var (2(i-j)+1) inside K2_i's λnb.λc body.

/-- `λnb.λc. c·next·emit`. -/
def b4incK2V (next emit : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0) [next, emit]))

/-- `(INCB·bi)·K2_i`. -/
def b4incChainV (bi next : LTerm) : LTerm :=
  .app (.app incbL bi) next

/-- the milestone after the 4-cell peel: the INCB carry chain over the
    substituted cells, emit-lists literal. -/
def b4incMilestone (B0 B1 B2 B3 : LTerm) : LTerm :=
  let e3 := emitCells [.var 7, .var 5, .var 3, .var 1]
  let e2 := emitCells [.var 5, .var 3, .var 1, B3]
  let e1 := emitCells [.var 3, .var 1, B2, B3]
  let e0 := emitCells [.var 1, B1, B2, B3]
  let ch3 := b4incChainV B3 (b4incK2V e3 e3)
  let ch2 := b4incChainV B2 (b4incK2V ch3 e2)
  let ch1 := b4incChainV B1 (b4incK2V ch2 e1)
  b4incChainV B0 (b4incK2V ch1 e0)

/-- peel discharge: 4 cellLit destructures at 4 hsteps each. -/
theorem b4inc_peel (B0 B1 B2 B3 : LTerm)
    (h0 : closed 0 B0 = true) (h1 : closed 0 B1 = true)
    (h2 : closed 0 B2 = true) (h3 : closed 0 B3 = true)
    (hT3 : closed 0 (cellLit B3 nilL) = true)
    (hT2 : closed 0 (cellLit B2 (cellLit B3 nilL)) = true)
    (hT1 : closed 0 (cellLit B1 (cellLit B2 (cellLit B3 nilL))) = true) :
    LRed (.app b4incL (scottList [B0, B1, B2, B3]))
         (b4incMilestone B0 B1 B2 B3) :=
  LRed_of_hsteps (k := 17) (by
    simp [b4incL, scottList, cellLit, b4incMilestone, b4incChainV,
          b4incK2V, b4incChain0, b4incChain1, b4incChain2, b4incChain3,
          b4incK2, b4incNext3, b4incEmit, emitCells, aps,
          List.foldl, List.foldr, List.map, List.range, List.range',
          hsteps, hstep, subst, shift, shift_zero,
          shift_of_closed0, subst_of_closed0, closed, closed_app,
          closed_mono, closed_nilL, closed_klL, closed_conssL,
          closed_incbL, closed_pairSrcL, closed_nibsuccL,
          closed_nibis15L, h0, h1, h2, h3])

-- sanity: peel the emit result and decode cell lo nibbles.
--   input 0+1      → byte0 = (1,0): expect nibLit 1 = absN 16 (var 14)
--   input 0xFF…+1  → byte0 = (0,0), byte1 = (1,0)

-- bool dispatch + K2 application ---------------------------------------

/-- `boolLit b·a·e →* if b then a else e` — Church-bool selection. -/
theorem boolLit_sel (b : Bool) (a e : LTerm) :
    LRed (aps (boolLit b) [a, e]) (if b then a else e) := by
  cases b <;>
    · simp only [Bool.cond_true, Bool.cond_false, boolLit]
      exact LRed_of_hsteps (k := 2) (by
        simp [klL, kilL, aps, List.foldl, hsteps, hstep, subst, shift,
              shift_zero, subst_shift_succ])

/-- `K2·nb·c →* c·(subst nb-result of next)·(emit)` — the two betas.
    Substituted arguments are written as their evaluated substs. -/
theorem b4incK2_apply (nb c next emit : LTerm) :
    LRed (aps (b4incK2V next emit) [nb, c])
         (aps c [subst c 0 (subst nb 1 next),
                 subst c 0 (subst nb 1 emit)]) :=
  LRed_of_hsteps (k := 2) (by
    simp [b4incK2V, aps, List.foldl, hsteps, hstep, subst, shift,
          shift_zero, subst_shift_succ])

-- semantic carry chain ------------------------------------------------

/-- `incByteN` threaded over a byte list, little-endian: increment until
    the first byte that does not carry out. -/
def incBytes : List (Fin 16 × Fin 16) → Bool → List (Fin 16 × Fin 16)
  | [], _ => []
  | x :: xs, c =>
      if c then
        let r := incByteN x.1 x.2
        r.1 :: incBytes xs r.2
      else x :: xs

/-- One carry-chain level: `(INCB·B)·(λnb.λc. c·next·emit)` reduces to
    the carry-bool applied to the substituted continuations. -/
theorem b4inc_level_run (lo hi : Fin 16) (next emit : LTerm) :
    LRed (.app (.app incbL (byteLit lo hi)) (b4incK2V next emit))
         (aps (boolLit (incByteN lo hi).2)
           [ subst (boolLit (incByteN lo hi).2) 0
              (subst (Function.uncurry byteLit (incByteN lo hi).1) 1 next),
             subst (boolLit (incByteN lo hi).2) 0
              (subst (Function.uncurry byteLit (incByteN lo hi).1) 1 emit) ]) := by
  exact ((LRed_app_left (incb_eval lo hi)).trans
    (pairLit_apply _ _ _ (closed_byteLit _ _) (closed_boolLit _))).trans
    (b4incK2_apply _ _ _ _)

/-- **b4inc_eval**: the four-byte increment evaluates to the semantic
    carry chain `incBytes`, as a normalized Scott list. -/
theorem b4inc_eval_scott (x0 x1 x2 x3 : Fin 16 × Fin 16) :
    LRed (.app b4incL
           (scottList [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
                       byteLit x2.1 x2.2, byteLit x3.1 x3.2]))
         (scottList ((incBytes [x0, x1, x2, x3] true).map
                      fun p => byteLit p.1 p.2)) := by
  -- peel: 4 cells → carry chain
  refine (b4inc_peel _ _ _ _
    (closed_byteLit _ _) (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_byteLit _ _)
    (closed_cellLit (closed_byteLit _ _) closed_nilL)
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _) closed_nilL))
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL)))).trans ?_
  -- level 0
  refine (b4inc_level_run x0.1 x0.2 _ _).trans ?_
  -- evaluate the substituted continuations (concrete-syntax substs)
  have hN0 :
      subst (boolLit (incByteN x0.1 x0.2).2) 0
        (subst (Function.uncurry byteLit (incByteN x0.1 x0.2).1) 1
          (b4incChainV (byteLit x1.1 x1.2)
            (b4incK2V
              (b4incChainV (byteLit x2.1 x2.2)
                (b4incK2V
                  (b4incChainV (byteLit x3.1 x3.2)
                    (b4incK2V
                      (emitCells [.var 7, .var 5, .var 3, .var 1])
                      (emitCells [.var 7, .var 5, .var 3, .var 1])))
                  (emitCells [.var 5, .var 3, .var 1, byteLit x3.1 x3.2])))
              (emitCells [.var 3, .var 1, byteLit x2.1 x2.2,
                          byteLit x3.1 x3.2]))))
      = b4incChainV (byteLit x1.1 x1.2)
          (b4incK2V
            (b4incChainV (byteLit x2.1 x2.2)
              (b4incK2V
                (b4incChainV (byteLit x3.1 x3.2)
                  (b4incK2V
                    (emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       .var 5, .var 3, .var 1])
                    (emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       .var 5, .var 3, .var 1])))
                (emitCells
                  [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                   .var 3, .var 1, byteLit x3.1 x3.2])))
            (emitCells
              [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
               .var 1, byteLit x2.1 x2.2, byteLit x3.1 x3.2])) := by
    simp [b4incChainV, b4incK2V, emitCells, aps,
          List.foldr, List.foldl, Function.uncurry,
          subst, shift, shift_zero, subst_shift_succ,
          shift_of_closed0, subst_of_closed0, closed, closed_app,
          closed_mono, closed_byteLit, closed_boolLit, closed_incbL,
          closed_conssL, closed_nilL]
  have hE0 :
      subst (boolLit (incByteN x0.1 x0.2).2) 0
        (subst (Function.uncurry byteLit (incByteN x0.1 x0.2).1) 1
          (emitCells [.var 1, byteLit x1.1 x1.2, byteLit x2.1 x2.2,
                      byteLit x3.1 x3.2]))
      = emitCells
          [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
           byteLit x1.1 x1.2, byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
    simp [emitCells, aps, List.foldr, List.foldl, Function.uncurry,
          subst, shift, shift_zero, subst_shift_succ,
          shift_of_closed0, subst_of_closed0, closed, closed_app,
          closed_mono, closed_byteLit, closed_boolLit, closed_incbL,
          closed_conssL, closed_nilL]
  rw [hN0, hE0]
  -- carry dispatch at level 0
  refine (boolLit_sel _ _ _).trans ?_
  split_ifs with h0
  · -- carry out of byte0 → continue to level 1
      refine (b4inc_level_run x1.1 x1.2 _ _).trans ?_
      have hN1 :
          subst (boolLit (incByteN x1.1 x1.2).2) 0
            (subst (Function.uncurry byteLit (incByteN x1.1 x1.2).1) 1
              (b4incChainV (byteLit x2.1 x2.2)
                (b4incK2V
                  (b4incChainV (byteLit x3.1 x3.2)
                    (b4incK2V
                      (emitCells
                        [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                         .var 5, .var 3, .var 1])
                      (emitCells
                        [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                         .var 5, .var 3, .var 1])))
                  (emitCells
                    [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                     .var 3, .var 1, byteLit x3.1 x3.2]))))
          = b4incChainV (byteLit x2.1 x2.2)
              (b4incK2V
                (b4incChainV (byteLit x3.1 x3.2)
                  (b4incK2V
                    (emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                       .var 3, .var 1])
                    (emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                       .var 3, .var 1])))
                (emitCells
                  [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                   Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                   .var 1, byteLit x3.1 x3.2])) := by
        simp [b4incChainV, b4incK2V, emitCells, aps,
              List.foldr, List.foldl, Function.uncurry,
              subst, shift, shift_zero, subst_shift_succ,
              shift_of_closed0, subst_of_closed0, closed, closed_app,
              closed_mono, closed_byteLit, closed_boolLit, closed_incbL,
              closed_conssL, closed_nilL]
      have hE1 :
          subst (boolLit (incByteN x1.1 x1.2).2) 0
            (subst (Function.uncurry byteLit (incByteN x1.1 x1.2).1) 1
              (emitCells
                [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                 .var 1, byteLit x2.1 x2.2, byteLit x3.1 x3.2]))
          = emitCells
              [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
               Function.uncurry byteLit (incByteN x1.1 x1.2).1,
               byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        simp [emitCells, aps, List.foldr, List.foldl, Function.uncurry,
              subst, shift, shift_zero, subst_shift_succ,
              shift_of_closed0, subst_of_closed0, closed, closed_app,
              closed_mono, closed_byteLit, closed_boolLit, closed_incbL,
              closed_conssL, closed_nilL]
      rw [hN1, hE1]
      refine (boolLit_sel _ _ _).trans ?_
      split_ifs with h1
      · -- continue to level 2
          refine (b4inc_level_run x2.1 x2.2 _ _).trans ?_
          have hN2 :
              subst (boolLit (incByteN x2.1 x2.2).2) 0
                (subst (Function.uncurry byteLit
                          (incByteN x2.1 x2.2).1) 1
                  (b4incChainV (byteLit x3.1 x3.2)
                    (b4incK2V
                      (emitCells
                        [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                         Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                         .var 3, .var 1])
                      (emitCells
                        [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                         Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                         .var 3, .var 1]))))
              = b4incChainV (byteLit x3.1 x3.2)
                  (b4incK2V
                    (emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                       Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                       .var 1])
                    (emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                       Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                       .var 1])) := by
            simp [b4incChainV, b4incK2V, emitCells, aps,
                  List.foldr, List.foldl, Function.uncurry,
                  subst, shift, shift_zero, subst_shift_succ,
                  shift_of_closed0, subst_of_closed0, closed, closed_app,
                  closed_mono, closed_byteLit, closed_boolLit,
                  closed_incbL, closed_conssL, closed_nilL]
          have hE2 :
              subst (boolLit (incByteN x2.1 x2.2).2) 0
                (subst (Function.uncurry byteLit
                          (incByteN x2.1 x2.2).1) 1
                  (emitCells
                    [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                     Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                     .var 1, byteLit x3.1 x3.2]))
              = emitCells
                  [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                   Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                   Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                   byteLit x3.1 x3.2] := by
            simp [emitCells, aps, List.foldr, List.foldl,
                  Function.uncurry,
                  subst, shift, shift_zero, subst_shift_succ,
                  shift_of_closed0, subst_of_closed0, closed, closed_app,
                  closed_mono, closed_byteLit, closed_boolLit,
                  closed_incbL, closed_conssL, closed_nilL]
          rw [hN2, hE2]
          refine (boolLit_sel _ _ _).trans ?_
          split_ifs with h2
          · -- continue to level 3 (next = emit, carry wraps mod 2^32)
              refine (b4inc_level_run x3.1 x3.2 _ _).trans ?_
              have hN3 :
                  subst (boolLit (incByteN x3.1 x3.2).2) 0
                    (subst (Function.uncurry byteLit
                              (incByteN x3.1 x3.2).1) 1
                      (emitCells
                        [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                         Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                         Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                         .var 1]))
                  = emitCells
                      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                       Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                       Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                       Function.uncurry byteLit (incByteN x3.1 x3.2).1] := by
                simp [emitCells, aps, List.foldr, List.foldl,
                      Function.uncurry,
                      subst, shift, shift_zero, subst_shift_succ,
                      shift_of_closed0, subst_of_closed0, closed,
                      closed_app, closed_mono, closed_byteLit,
                      closed_boolLit, closed_incbL, closed_conssL,
                      closed_nilL]
              rw [hN3]
              refine (boolLit_sel _ _ _).trans ?_
              simp only [ite_self]
              have hnf3 := emitCells_nf
                [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                 Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                 Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                 Function.uncurry byteLit (incByteN x3.1 x3.2).1]
                (by
                  intro c hc
                  simp at hc
                  rcases hc with rfl | rfl | rfl | rfl <;>
                    exact closed_byteLit _ _)
              have heq3 : scottList
                  [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                   Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                   Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                   Function.uncurry byteLit (incByteN x3.1 x3.2).1]
                  = scottList (List.map (fun p => byteLit p.1 p.2)
                      (incBytes [x0, x1, x2, x3] true)) := by
                simp only [incBytes, h0, h1, h2, ite_true, ite_false,
                           ↓reduceIte, List.map_cons, List.map_nil,
                           Function.uncurry]
              rw [← heq3]
              assumption
          · -- byte2 carries no further → emit
            have hnf2 := emitCells_nf
              [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
               Function.uncurry byteLit (incByteN x1.1 x1.2).1,
               Function.uncurry byteLit (incByteN x2.1 x2.2).1,
               byteLit x3.1 x3.2]
              (by
                intro c hc
                simp at hc
                rcases hc with rfl | rfl | rfl | rfl <;>
                  exact closed_byteLit _ _)
            have heq2 : scottList
                [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
                 Function.uncurry byteLit (incByteN x1.1 x1.2).1,
                 Function.uncurry byteLit (incByteN x2.1 x2.2).1,
                 byteLit x3.1 x3.2]
                = scottList (List.map (fun p => byteLit p.1 p.2)
                    (incBytes [x0, x1, x2, x3] true)) := by
              simp only [incBytes, h0, h1, eq_false (h2), ite_true,
                         ite_false, ↓reduceIte, List.map_cons,
                         List.map_nil, Function.uncurry]
            rw [← heq2]
            assumption
      · -- byte1 emits [nb0, nb1, B2, B3]
        have hnf1 := emitCells_nf
          [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
           Function.uncurry byteLit (incByteN x1.1 x1.2).1,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2]
          (by
            intro c hc
            simp at hc
            rcases hc with rfl | rfl | rfl | rfl <;>
              first
              | exact closed_byteLit _ _
              | (simp [Function.uncurry]; exact closed_byteLit _ _))
        have heq1 : scottList
            [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
             Function.uncurry byteLit (incByteN x1.1 x1.2).1,
             byteLit x2.1 x2.2, byteLit x3.1 x3.2]
            = scottList (List.map (fun p => byteLit p.1 p.2)
                (incBytes [x0, x1, x2, x3] true)) := by
          simp only [incBytes, h0, eq_false (h1), ite_true, ite_false,
                     ↓reduceIte, List.map_cons, List.map_nil,
                     Function.uncurry]
        rw [← heq1]
        assumption
  · -- byte0 emits [nb0, B1, B2, B3]
    have hnf0 := emitCells_nf
      [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
       byteLit x1.1 x1.2, byteLit x2.1 x2.2,
       byteLit x3.1 x3.2]
      (by
        intro c hc
        simp at hc
        rcases hc with rfl | rfl | rfl | rfl <;>
          first
          | exact closed_byteLit _ _
          | (simp [Function.uncurry]; exact closed_byteLit _ _))
    have heq0 : scottList
        [Function.uncurry byteLit (incByteN x0.1 x0.2).1,
         byteLit x1.1 x1.2, byteLit x2.1 x2.2,
         byteLit x3.1 x3.2]
        = scottList (List.map (fun p => byteLit p.1 p.2)
            (incBytes [x0, x1, x2, x3] true)) := by
      simp only [incBytes, eq_false (h0), ite_true, ite_false,
                 ↓reduceIte, List.map_cons, List.map_nil,
                 Function.uncurry]
    rw [← heq0]
    assumption

/-- `b4inc` on the conss-fold literal — normalizes `b4Lit` to a
    scottList first. -/
theorem b4inc_eval (x0 x1 x2 x3 : Fin 16 × Fin 16) :
    LRed (aps b4incL [b4Lit [x0, x1, x2, x3]])
         (scottList ((incBytes [x0, x1, x2, x3] true).map
                      fun p => byteLit p.1 p.2)) := by
  refine (LRed_app_right (b4Lit_nf _)).trans ?_
  simp only [List.map]
  exact b4inc_eval_scott x0 x1 x2 x3

/-- `incBytes` preserves the cell count (carry only rewrites cells). -/
theorem incBytes_length :
    ∀ (xs : List (Fin 16 × Fin 16)) (c : Bool),
      (incBytes xs c).length = xs.length := by
  intro xs; induction xs with
  | nil => intro c; rfl
  | cons x xs ih =>
    intro c
    simp only [incBytes]
    cases c <;> simp [ih]

/-- Fold chain with an *encoded* semantic accumulator — the
    WF-closure form of `foldl_red`.  `enc : α → LTerm` encodes the
    semantic state, so the per-step hypothesis only has to hold for
    reachable (encoded) states: the shape-invariant lives in `α`,
    not in a global normal-form predicate. -/
theorem foldl_enc_red (st : LTerm) {α : Type} (enc : α → LTerm)
    (σ : α → LTerm → α) (hs : closed 0 st = true)
    (hstep : ∀ (a : α) (X e : LTerm), closed 0 X = true →
      LRed X (enc a) → closed 0 e = true →
      LRed (.app (.app st X) e) (enc (σ a e))) :
    ∀ (cs : List LTerm) (X : LTerm) (a : α),
      closed 0 X = true → LRed X (enc a) →
      (∀ e ∈ cs, closed 0 e = true) →
      LRed (cs.foldl (fun acc e => .app (.app st acc) e) X)
           (enc (cs.foldl σ a)) := by
  intro cs
  induction cs with
  | nil => intro X a _ hXa _; exact hXa
  | cons c cs' ih =>
    intro X a hX hXa hcl
    have hc : closed 0 c = true := hcl c List.mem_cons_self
    have htail : ∀ e ∈ cs', closed 0 e = true :=
      fun e he => hcl e (List.mem_cons_of_mem c he)
    have hs' := hstep a X c hX hXa hc
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (closed_app (closed_app hs hX) hc) hs' htail

/-- `_LENB4`'s step `λa.λx. B4INC a` — increments the bytes4
    accumulator, ignoring the cell. -/
def lenStepL : LTerm := .abs (.abs (.app b4incL (.var 1)))

theorem closed_lenStepL : closed 0 lenStepL = true := by decide

/-- `_b4_src 0` — the all-zero bytes4 accumulator seed. -/
def b4zeroBytes : List (Fin 16 × Fin 16) := [(0, 0), (0, 0), (0, 0), (0, 0)]

/-- `_LENB4 = λl. FOLDL lenStep l (b4Lit 0000)` — byte-list length as
    a bytes4 counter. -/
def lenb4L : LTerm :=
  .abs (aps foldlL [lenStepL, .var 0, b4Lit b4zeroBytes])

theorem closed_lenb4L : closed 0 lenb4L = true := by decide

/-- Unwrap the length-4 subtype accumulator of the `incBytes` fold. -/
theorem foldl_incBytes_val (cs : List LTerm)
    (xs : {xs : List (Fin 16 × Fin 16) // xs.length = 4}) :
    (cs.foldl (fun a _ => ⟨incBytes a.1 true,
        by rw [incBytes_length]; exact a.2⟩) xs).val =
      cs.foldl (fun a _ => incBytes a true) xs.val := by
  induction cs generalizing xs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih _

/-- One FOLDL step of `lenStepL`: `lenStep·X·e →* enc (incBytes xs)`
    whenever `X →* enc xs`. -/
theorem lenStep_cell {xs : List (Fin 16 × Fin 16)} (hxs : xs.length = 4)
    (X e : LTerm) (hX : closed 0 X = true)
    (hXa : LRed X (scottList (xs.map (fun p => byteLit p.1 p.2))))
    (he : closed 0 e = true) :
    LRed (.app (.app lenStepL X) e)
         (scottList ((incBytes xs true).map
                      (fun p => byteLit p.1 p.2))) := by
  cases xs with
  | nil => simp_all
  | cons p0 t0 =>
    cases t0 with
    | nil => simp_all
    | cons p1 t1 =>
      cases t1 with
      | nil => simp_all
      | cons p2 t2 =>
        cases t2 with
        | nil => simp_all
        | cons p3 t3 =>
          cases t3 with
          | nil =>
            -- two betas: (λa.λx. incbL·a)·X·e →* incbL·X
            have hX1 : closed 1 X = true := closed_mono hX (Nat.zero_le 1)
            have hi1 : closed 1 b4incL = true :=
              closed_mono closed_b4incL (Nat.zero_le 1)
            have hbeta : LRed (.app (.app lenStepL X) e)
                (.app b4incL X) :=
              LRed_of_hsteps (k := 2) (by
                simp [lenStepL, hsteps, hstep, subst, shift,
                      subst_of_closed hi1, shift_of_closed hX,
                      subst_of_closed0 hX, subst_of_closed0 closed_b4incL])
            exact hbeta.trans ((LRed_app_right hXa).trans
              (b4inc_eval_scott p0 p1 p2 p3))
          | cons p4 t4 =>
            simp only [List.length_cons] at hxs; omega

/-- `LENB4` evaluates a byte list's length as a bytes4 counter: each
    cell increments the accumulator (carry chain, mod 2³²). -/
theorem lenb4_eval (cs : List LTerm)
    (hcl : ∀ e ∈ cs, closed 0 e = true) :
    LRed (.app lenb4L (scottList cs))
         (scottList ((cs.foldl (fun xs _ => incBytes xs true)
                        b4zeroBytes).map (fun p => byteLit p.1 p.2))) := by
  -- β-open: lenb4L·l → FOLDL·lenStep·l·b4zero
  have hopen : LRed (.app lenb4L (scottList cs))
      (aps foldlL [lenStepL, scottList cs, b4Lit b4zeroBytes]) :=
    LRed_of_hsteps (k := 1) (by
      simp [lenb4L, aps, List.foldl, hsteps, hstep, subst, shift,
            shift_zero, subst_shift_succ, closed, closed_app,
            closed_mono, closed_foldlL, closed_lenStepL,
            closed_scottList, closed_b4Lit, closed_nilL,
            subst_of_closed, shift_of_closed, subst_of_closed0,
            shift_of_closed0])
  refine hopen.trans ?_
  -- unfold fixpoint → foldl application chain
  refine (foldl_to_ggb lenStepL (scottList cs) (b4Lit b4zeroBytes)
    closed_lenStepL (closed_scottList hcl) (closed_b4Lit _)).trans ?_
  refine (fold_run lenStepL closed_lenStepL cs (b4Lit b4zeroBytes) hcl
    (closed_b4Lit _)).trans ?_
  -- semantic fold over the encoded (length-4) accumulator
  refine (foldl_enc_red lenStepL
    (fun xs : {xs : List (Fin 16 × Fin 16) // xs.length = 4} =>
      scottList (xs.val.map (fun p => byteLit p.1 p.2)))
    (fun xs _ => ⟨incBytes xs.val true,
                  by rw [incBytes_length]; exact xs.prop⟩)
    closed_lenStepL
    (fun xs X e hX hXa he => lenStep_cell xs.prop X e hX hXa he)
    cs (b4Lit b4zeroBytes) ⟨b4zeroBytes, rfl⟩
    (closed_b4Lit _) (b4Lit_nf _) hcl).trans ?_
  -- unwrap the subtype accumulator
  rw [foldl_incBytes_val]

/-- `r·K·(λh.λt. h)·(λlo.λhi. lo)` — first cell's lo nibble. -/
def peelLo (r : LTerm) : LTerm :=
  .app (.app (.app r klL) (.abs (.abs (.var 1))))
    (.abs (.abs (.var 1)))

/-- second cell's lo nibble. -/
def peelLo2 (r : LTerm) : LTerm :=
  .app (.app (.app (.app (.app r klL) (.abs (.abs (.var 0))))
    klL) (.abs (.abs (.var 1)))) (.abs (.abs (.var 1)))

#eval hsteps 600 (peelLo
  (hsteps 400 (aps b4incL [b4Lit [(0, 0), (0, 0), (0, 0), (0, 0)]])))
-- 0xFF + 1: byte0 wraps, byte1 increments → second cell lo = nibLit 1
#eval hsteps 900 (peelLo2
  (hsteps 600 (aps b4incL
    [b4Lit [(15, 15), (0, 0), (0, 0), (0, 0)]])))


-- ============================================================
-- Batch A: nibble dispatch tables (NIB2NUM / NIBPAR / NIBANDE)
--          + EQNIB / NOT / EQB
-- (andL/orL already in SpecVocabulary; only evals added here)
-- ============================================================

/-- `_NIB2NUM = λa. a (churchL 0) … (churchL 15)` — nibble → Church
    numeral. -/
def nib2numL : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun j : Fin 16 => churchL j.val))

theorem closed_nib2numL : closed 0 nib2numL = true := by decide

/-- `_NIBPAR = λa. a (churchL (0&1)) …` — nibble → parity numeral. -/
def nibparL : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun j : Fin 16 => churchL (j.val % 2)))

theorem closed_nibparL : closed 0 nibparL = true := by decide

/-- `2·(i/2)` — the ALIGN512 low-nibble mask (`i & 0xE` for i<16). -/
def nibMaskE (i : Fin 16) : Fin 16 := ⟨2 * (i.val / 2), by omega⟩

/-- `_NIBANDE = λa. a sel_{0&E} … sel_{15&E}` — nibble mask for
    ALIGN512 (clears the low bit). -/
def nibandEL : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun j : Fin 16 => nibLit (nibMaskE j)))

theorem closed_nibandEL : closed 0 nibandEL = true := by decide

theorem nib2num_table : ∀ i : Fin 16,
    hsteps 24 (aps nib2numL [nibLit i]) = churchL i.val := by
  decide

theorem nibpar_table : ∀ i : Fin 16,
    hsteps 24 (aps nibparL [nibLit i]) = churchL (i.val % 2) := by
  decide

theorem nibandE_table : ∀ i : Fin 16,
    hsteps 24 (aps nibandEL [nibLit i]) = nibLit (nibMaskE i) := by
  decide

theorem nib2num_correct (i : Fin 16) :
    LRed (aps nib2numL [nibLit i]) (churchL i.val) :=
  LRed_of_hsteps (nib2num_table i)

theorem nibpar_correct (i : Fin 16) :
    LRed (aps nibparL [nibLit i]) (churchL (i.val % 2)) :=
  LRed_of_hsteps (nibpar_table i)

theorem nibandE_correct (i : Fin 16) :
    LRed (aps nibandEL [nibLit i]) (nibLit (nibMaskE i)) :=
  LRed_of_hsteps (nibandE_table i)

-- EQNIB: nibble equality ------------------------------------------------

/-- `EQNIB = λa.λb. a (b K KI …) (b KI K …) …` — double 16-table:
    row `i` selects `K` iff `b = i`. -/
def eqnibL : LTerm :=
  .abs (.abs (aps (.var 1) (List.ofFn fun i : Fin 16 =>
    aps (.var 0) (List.ofFn fun j : Fin 16 =>
      boolLit (decide (j.val = i.val))))))

theorem closed_eqnibL : closed 0 eqnibL = true := by decide

theorem eqnib_table : ∀ i j : Fin 16,
    hsteps 60 (aps eqnibL [nibLit i, nibLit j])
      = boolLit (decide (i = j)) := by
  decide

theorem eqnib_eval (i j : Fin 16) :
    LRed (aps eqnibL [nibLit i, nibLit j]) (boolLit (decide (i = j))) :=
  LRed_of_hsteps (eqnib_table i j)

-- NOT ---------------------------------------------------------------------

/-- `_NOT = λp. p KI K`. -/
def notL : LTerm := .abs (aps (.var 0) [kilL, klL])

theorem closed_notL : closed 0 notL = true := by decide

theorem not_table : ∀ p : Bool,
    hsteps 5 (aps notL [boolLit p]) = boolLit (!p) := by
  decide

theorem not_eval (p : Bool) :
    LRed (aps notL [boolLit p]) (boolLit (!p)) :=
  LRed_of_hsteps (not_table p)

theorem and_table : ∀ p q : Bool,
    hsteps 6 (aps andL [boolLit p, boolLit q]) = boolLit (p && q) := by
  decide

theorem or_table : ∀ p q : Bool,
    hsteps 6 (aps orL [boolLit p, boolLit q]) = boolLit (p || q) := by
  decide

theorem and_eval (p q : Bool) :
    LRed (aps andL [boolLit p, boolLit q]) (boolLit (p && q)) :=
  LRed_of_hsteps (and_table p q)

theorem or_eval (p q : Bool) :
    LRed (aps orL [boolLit p, boolLit q]) (boolLit (p || q)) :=
  LRed_of_hsteps (or_table p q)

-- EQB: byte equality -------------------------------------------------------

/-- `_EQB = λx.λy. x (λxl.λxh. y (λyl.λyh. AND (EQNIB xl yl)
    (EQNIB xh yh)))` — byte equality on pair cells. -/
def eqbL : LTerm :=
  .abs (.abs (.app (.var 1)
    (.abs (.abs (.app (.var 2)
      (.abs (.abs (aps andL
        [aps eqnibL [.var 3, .var 1],
         aps eqnibL [.var 2, .var 0]]))))))))

theorem closed_eqbL : closed 0 eqbL = true := by decide

/-- `EQB·(byteLit)·(byteLit) →* boolLit (a = b)` — peel both pairs,
    two eqnibs, one and. -/
theorem eqb_eval (xlo xhi ylo yhi : Fin 16) :
    LRed (aps eqbL [byteLit xlo xhi, byteLit ylo yhi])
         (boolLit (decide ((xlo, xhi) = (ylo, yhi)))) := by
  have hbeta : LRed (aps eqbL [byteLit xlo xhi, byteLit ylo yhi])
      (aps andL [aps eqnibL [nibLit xlo, nibLit ylo],
                 aps eqnibL [nibLit xhi, nibLit yhi]]) :=
    LRed_of_hsteps (k := 8) (by
      simp [eqbL, byteLit, pairLit, aps, List.foldl,
            hsteps, hstep, subst, shift,
            subst_of_closed0, shift_of_closed0, subst_of_closed,
            shift_of_closed, closed, closed_app, closed_absN,
            closed_mono, decide_eq_true_eq,
            closed_nibLit, closed_byteLit, closed_eqnibL,
            closed_andL, closed_klL, closed_kilL])
  refine hbeta.trans ?_
  refine (LRed_app (LRed_app_right (eqnib_eval xlo ylo))
      (eqnib_eval xhi yhi)).trans ?_
  refine (and_eval _ _).trans ?_
  have hbool : (decide (xlo = ylo) && decide (xhi = yhi))
      = decide ((xlo, xhi) = (ylo, yhi)) := by
    by_cases h1 : xlo = ylo <;> by_cases h2 : xhi = yhi <;> simp [h1, h2]
  rw [hbool]

-- ============================================================
-- Batch B: Church arithmetic (_ADD_SRC / _MUL_SRC), TAIL/HEAD,
--          numeral-iteration lemmas, isZero
-- ============================================================

/-- `iterL` composition: `f^m·(f^n·z) = f^(n+m)·z`. -/
theorem iterL_add : ∀ (n m : Nat) (f z : LTerm),
    iterL f (iterL f z n) m = iterL f z (n + m) := by
  intro n m f z
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ]
    show LTerm.app f (iterL f (iterL f z n) m)
       = LTerm.app f (iterL f z (n + m))
    rw [ih]

/-- `iterS (λx. iterL f x n)` nests `n`-iterates `m` times: `f^(m·n)`. -/
theorem iterS_iterL : ∀ (m n : Nat) (f z : LTerm),
    iterS (fun x => iterL f x n) z m = iterL f z (m * n) := by
  intro m n f z
  induction m with
  | zero => simp [iterS, iterL]
  | succ m ih =>
    simp only [iterS, ih]
    rw [iterL_add, Nat.succ_mul]

/-- `_ADD_SRC = λm.λn.λf.λx. m f (n f x)` — Church addition. -/
def churchAddL : LTerm :=
  .abs (.abs (.abs (.abs (.app (.app (.var 3) (.var 1))
    (.app (.app (.var 2) (.var 1)) (.var 0))))))

theorem closed_churchAddL : closed 0 churchAddL = true := by decide

/-- `ADD·(num m)·(num n)·f·z →* f^(m+n)·z` — application form (the
    numeral is only consumed by application downstream). -/
theorem churchAdd_eval (m n : Nat) (f z : LTerm)
    (hf : closed 0 f = true) (hz : closed 0 z = true) :
    LRed (aps churchAddL [churchL m, churchL n, f, z])
         (iterL f z (m + n)) := by
  have hbeta : LRed (aps churchAddL [churchL m, churchL n, f, z])
      (.app (.app (churchL m) f)
        (.app (.app (churchL n) f) z)) :=
    LRed_of_hsteps (k := 4) (by
      simp [churchAddL, aps, List.foldl, hsteps, hstep, subst, shift,
            subst_of_closed0, shift_of_closed0,
            closed_churchL, hf, hz])
  have hn := church_eval n f z hf hz
  have hX : closed 0 (iterL f z n) = true := closed_iterL f z hf hz n
  have hm := church_eval m f (iterL f z n) hf hX
  refine hbeta.trans ((LRed_app_right hn).trans (hm.trans ?_))
  rw [iterL_add, Nat.add_comm n m]

/-- `_MUL_SRC = λm.λn.λf. m (n f)` — Church multiplication. -/
def churchMulL : LTerm :=
  .abs (.abs (.abs (.app (.var 2) (.app (.var 1) (.var 0)))))

theorem closed_churchMulL : closed 0 churchMulL = true := by decide

/-- `MUL·(num m)·(num n)·f·z →* f^(m·n)·z`. -/
theorem churchMul_eval (m n : Nat) (f z : LTerm)
    (hf : closed 0 f = true) (hz : closed 0 z = true) :
    LRed (aps churchMulL [churchL m, churchL n, f, z])
         (iterL f z (m * n)) := by
  have hbeta : LRed (aps churchMulL [churchL m, churchL n, f, z])
      (.app (.app (churchL m) (.app (churchL n) f)) z) :=
    LRed_of_hsteps (k := 3) (by
      simp [churchMulL, aps, List.foldl, hsteps, hstep, subst, shift,
            subst_of_closed0, shift_of_closed0,
            closed_churchL, hf, hz])
  have hnf : closed 0 (.app (churchL n) f) = true :=
    closed_app (closed_churchL n) hf
  have hm := church_eval m (.app (churchL n) f) z hnf hz
  have hstep : ∀ x, closed 0 x = true →
      LRed (.app (.app (churchL n) f) x) (iterL f x n) ∧
      closed 0 (iterL f x n) = true :=
    fun x hx => ⟨church_eval n f x hf hx, closed_iterL f x hf hx n⟩
  have hiter := iter_red (.app (churchL n) f) (fun x => iterL f x n)
    hstep m z hz
  rw [iterS_iterL m n f z] at hiter
  exact hbeta.trans (hm.trans hiter)

-- TAIL / HEAD ---------------------------------------------------------------

/-- `_TAIL = λx. x K KI` — Scott-list tail. -/
def tailL : LTerm := .abs (aps (.var 0) [klL, kilL])

/-- `_HEAD = λx. x K K` — Scott-list head. -/
def headL : LTerm := .abs (aps (.var 0) [klL, klL])

theorem closed_tailL : closed 0 tailL = true := by decide
theorem closed_headL : closed 0 headL = true := by decide

/-- `TAIL·(cellLit h t) →* t`. -/
theorem tail_cell (h t : LTerm) (hh : closed 0 h = true)
    (ht : closed 0 t = true) :
    LRed (.app tailL (cellLit h t)) t :=
  LRed_of_hsteps (k := 5) (by
    simp [tailL, cellLit, klL, kilL, aps, List.foldl, hsteps, hstep,
          subst, shift, subst_of_closed0 ht, shift_of_closed0 ht,
          subst_of_closed0 hh, shift_of_closed0 hh])

/-- `HEAD·(cellLit h t) →* h`. -/
theorem head_cell (h t : LTerm) (hh : closed 0 h = true)
    (ht : closed 0 t = true) :
    LRed (.app headL (cellLit h t)) h :=
  LRed_of_hsteps (k := 5) (by
    simp [headL, cellLit, klL, kilL, aps, List.foldl, hsteps, hstep,
          subst, shift, subst_of_closed0 ht, shift_of_closed0 ht,
          subst_of_closed0 hh, shift_of_closed0 hh])

/-- `TAIL·nilL →* nilL` — tail of nil is nil. -/
theorem tail_nil : LRed (.app tailL nilL) nilL :=
  LRed_of_hsteps (k := 4) (by
    simp [tailL, nilL, klL, kilL, aps, List.foldl, hsteps, hstep,
          subst, shift])

/-- `TAIL·(scottList cs) →* scottList cs.tail`. -/
theorem tail_scott (cs : List LTerm)
    (hcl : ∀ e ∈ cs, closed 0 e = true) :
    LRed (.app tailL (scottList cs)) (scottList cs.tail) := by
  cases cs with
  | nil => exact tail_nil
  | cons h t =>
    have hh : closed 0 h = true := hcl h List.mem_cons_self
    have ht : closed 0 (scottList t) = true :=
      closed_scottList (fun e he => hcl e (List.mem_cons_of_mem _ he))
    exact tail_cell h (scottList t) hh ht

/-- `iterL TAIL (scott cs) n →* scott (cs.drop n)` — `n` tails drop
    `n` cells (saturating at nil, matching `List.drop`). -/
theorem iterL_tail_drop : ∀ (n : Nat) (cs : List LTerm),
    (∀ e ∈ cs, closed 0 e = true) →
    LRed (iterL tailL (scottList cs) n) (scottList (cs.drop n)) := by
  intro n
  induction n with
  | zero => intro cs _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro cs hcl
    simp only [iterL]
    refine (LRed_app_right (ih cs hcl)).trans ?_
    rw [← List.tail_drop]
    exact tail_scott (cs.drop n)
      (fun e he => hcl e ((List.drop_sublist n cs).mem he))

-- isZero --------------------------------------------------------------------

/-- `_PADLIST`'s zero-check step `λx. KI` — const-false. -/
def iszStepL : LTerm := .abs kilL

theorem closed_iszStepL : closed 0 iszStepL = true := by decide

/-- `iszStepL·x →* KI` for closed `x`. -/
theorem iszStep_cell (x : LTerm) (hx : closed 0 x = true) :
    LRed (.app iszStepL x) kilL :=
  LRed_of_hsteps (k := 1) (by
    simp [iszStepL, hsteps, hstep, subst, shift,
          subst_of_closed0 hx, shift_of_closed0 hx,
          subst_of_closed0 closed_kilL, shift_of_closed0 closed_kilL])

/-- `n·iszStep·K →* boolLit (n == 0)` — Church isZero. -/
theorem isZero_eval (n : Nat) :
    LRed (aps (churchL n) [iszStepL, klL])
         (boolLit (decide (n = 0))) := by
  have hchurch := church_eval n iszStepL klL closed_iszStepL closed_klL
  have hstep : ∀ x, closed 0 x = true →
      LRed (.app iszStepL x) kilL ∧ closed 0 kilL = true :=
    fun x hx => ⟨iszStep_cell x hx, closed_kilL⟩
  have hiter := iter_red iszStepL (fun _ => kilL) hstep n klL closed_klL
  have hiterS : iterS (fun _ => kilL) klL n
      = if n = 0 then klL else kilL := by
    cases n with
    | zero => rfl
    | succ n => simp [iterS]
  refine hchurch.trans (hiter.trans ?_)
  rw [hiterS]
  cases n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n => exact Relation.ReflTransGen.refl

-- ============================================================
-- Batch C: IsChurchNum (numeral-as-iteration-behaviour, closed
--          under ADD/MUL composition), U64
-- ============================================================

/-- A term behaves as the Church numeral `n` iff applying it to closed
    `f z` reduces to the `n`-fold iteration chain.  Intermediate
    `MUL`/`ADD` results are `λf. …` closures — not literal `churchL`s —
    so the invariant is stated by application behaviour. -/
def IsChurchNum (n : Nat) (M : LTerm) : Prop :=
  ∀ f z, closed 0 f = true → closed 0 z = true →
    LRed (aps M [f, z]) (iterL f z n)

theorem churchL_num (n : Nat) : IsChurchNum n (churchL n) :=
  fun f z hf hz => church_eval n f z hf hz

/-- `LRed`-transport: any reduct-convertible numeral keeps the count. -/
theorem IsChurchNum_of_red {n : Nat} {M N : LTerm}
    (h : LRed M N) (hN : IsChurchNum n N) : IsChurchNum n M :=
  fun f z hf hz =>
    (LRed_app_left (LRed_app_left h)).trans (hN f z hf hz)

/-- `ADD·M·N` is the `m+n` numeral when `M`,`N` are `m`,`n`. -/
theorem churchAdd_num (m n : Nat) (M N : LTerm)
    (hM : IsChurchNum m M) (hN : IsChurchNum n N)
    (hcM : closed 0 M = true) (hcN : closed 0 N = true) :
    IsChurchNum (m + n) (aps churchAddL [M, N]) := by
  intro f z hf hz
  have hbeta : LRed (aps churchAddL [M, N, f, z])
      (.app (.app M f) (.app (.app N f) z)) :=
    LRed_of_hsteps (k := 4) (by
      simp [churchAddL, aps, List.foldl, hsteps, hstep, subst, shift,
            shift_zero, subst_of_closed0 hcM, shift_of_closed0 hcM,
            subst_of_closed0 hcN, shift_of_closed0 hcN,
            subst_of_closed0 hf, shift_of_closed0 hf,
            subst_of_closed0 hz, shift_of_closed0 hz])
  have hnfz : LRed (.app (.app N f) z) (iterL f z n) := hN f z hf hz
  have hX : closed 0 (iterL f z n) = true := closed_iterL f z hf hz n
  refine hbeta.trans ((LRed_app_right hnfz).trans ?_)
  refine (hM f (iterL f z n) hf hX).trans ?_
  rw [iterL_add, Nat.add_comm n m]

/-- `MUL·M·N` is the `m·n` numeral when `M`,`N` are `m`,`n`. -/
theorem churchMul_num (m n : Nat) (M N : LTerm)
    (hM : IsChurchNum m M) (hN : IsChurchNum n N)
    (hcM : closed 0 M = true) (hcN : closed 0 N = true) :
    IsChurchNum (m * n) (aps churchMulL [M, N]) := by
  intro f z hf hz
  have hbeta : LRed (aps churchMulL [M, N, f, z])
      (.app (.app M (.app N f)) z) :=
    LRed_of_hsteps (k := 3) (by
      simp [churchMulL, aps, List.foldl, hsteps, hstep, subst, shift,
            subst_of_closed0 hcM, shift_of_closed0 hcM,
            subst_of_closed0 hcN, shift_of_closed0 hcN,
            subst_of_closed0 hf, shift_of_closed0 hf])
  have hnf : closed 0 (.app N f) = true := closed_app hcN hf
  have hm := hM (.app N f) z hnf hz
  have hstep : ∀ x, closed 0 x = true →
      LRed (.app (.app N f) x) (iterL f x n) ∧
      closed 0 (iterL f x n) = true :=
    fun x hx => ⟨hN f x hf hx, closed_iterL f x hf hx n⟩
  have hiter := iter_red (.app N f) (fun x => iterL f x n) hstep m z hz
  rw [iterS_iterL m n f z] at hiter
  exact hbeta.trans (hm.trans hiter)

/-- `NIB2NUM·(nibLit i)` is the `i`-numeral. -/
theorem nib2num_num (i : Fin 16) :
    IsChurchNum i.val (aps nib2numL [nibLit i]) :=
  IsChurchNum_of_red (nib2num_correct i) (churchL_num i.val)

/-- `NIBPAR·(nibLit i)` is the `(i&1)`-numeral. -/
theorem nibpar_num (i : Fin 16) :
    IsChurchNum (i.val % 2) (aps nibparL [nibLit i]) :=
  IsChurchNum_of_red (nibpar_correct i) (churchL_num (i.val % 2))

-- U64 ----------------------------------------------------------------------

/-- `_U64`'s four zero-byte tail cells (raw `conss` chain). -/
def u64Tail : LTerm :=
  aps conssL [b0cT, aps conssL [b0cT, aps conssL [b0cT,
    aps conssL [b0cT, nilL]]]]

theorem closed_u64Tail : closed 0 u64Tail = true := by decide

/-- `_U64 = λb. APPEND b tail4` — bytes4 → 8 LE cells (zero-extend). -/
def u64L : LTerm := .abs (aps appendL [.var 0, u64Tail])

theorem closed_u64L : closed 0 u64L = true := by decide

/-- elements of a `b0cT`-replicate are closed. -/
theorem closed_rep_b0c {e : LTerm} {n : Nat}
    (he : e ∈ List.replicate n b0cT) : closed 0 e = true := by
  rw [List.mem_replicate] at he
  exact he.2 ▸ closed_b0cT

/-- The raw tail reduces to the scottList of four `b0cT` cells. -/
theorem u64Tail_nf :
    LRed u64Tail (scottList (List.replicate 4 b0cT)) := by
  have h1 : LRed (aps conssL [b0cT, nilL])
      (scottList (List.replicate 1 b0cT)) :=
    conss_nf b0cT nilL closed_b0cT closed_nilL
  have h2 : LRed (aps conssL [b0cT, aps conssL [b0cT, nilL]])
      (scottList (List.replicate 2 b0cT)) :=
    (LRed_app_right h1).trans
      (conss_nf b0cT (scottList (List.replicate 1 b0cT)) closed_b0cT
        (closed_scottList (fun _ he => closed_rep_b0c he)))
  have h3 : LRed (aps conssL [b0cT,
        aps conssL [b0cT, aps conssL [b0cT, nilL]]])
      (scottList (List.replicate 3 b0cT)) :=
    (LRed_app_right h2).trans
      (conss_nf b0cT (scottList (List.replicate 2 b0cT)) closed_b0cT
        (closed_scottList (fun _ he => closed_rep_b0c he)))
  exact (LRed_app_right h3).trans
    (conss_nf b0cT (scottList (List.replicate 3 b0cT)) closed_b0cT
      (closed_scottList (fun _ he => closed_rep_b0c he)))

/-- `U64·(b4Lit xs) →* scottList (bytes ++ [b0cT×4])`. -/
theorem u64_eval (xs : List (Fin 16 × Fin 16)) :
    LRed (.app u64L (b4Lit xs))
      (scottList ((xs.map fun p => byteLit p.1 p.2)
        ++ List.replicate 4 b0cT)) := by
  -- β: u64L·B → appendL·B·tail4
  have hopen : LRed (.app u64L (b4Lit xs))
      (aps appendL [b4Lit xs, u64Tail]) :=
    LRed_of_hsteps (k := 1) (by
      simp [u64L, aps, List.foldl, hsteps, hstep, subst, shift,
            subst_of_closed0 (closed_b4Lit xs),
            shift_of_closed0 (closed_b4Lit xs),
            subst_of_closed0 closed_u64Tail,
            shift_of_closed0 closed_u64Tail,
            subst_of_closed0 closed_appendL,
            shift_of_closed0 closed_appendL])
  have htail_is : IsList u64Tail (List.replicate 4 b0cT) := u64Tail_nf
  have hb4_is : IsList (b4Lit xs)
      (xs.map fun p => byteLit p.1 p.2) := b4Lit_nf xs
  refine hopen.trans ((appendL_to_appendT _ _ (closed_b4Lit xs)
    closed_u64Tail).trans ?_)
  exact append_eval _ _ _ _ hb4_is htail_is
    (fun e he => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
      exact closed_byteLit _ _)
    (fun e he => closed_rep_b0c he)
    (closed_b4Lit xs) closed_u64Tail

-- ============================================================
-- Batch D: ALIGN512 / ALIGN4096 — B4ADD + peel + nibble mask
-- ============================================================

/-- `_b4_src 0x1FF` — the ALIGN512 addend (LE bytes). -/
def b4_1FF : List (Fin 16 × Fin 16) := [(15, 15), (1, 0), (0, 0), (0, 0)]

/-- `_b4_src 0xFFF` — the ALIGN4096 addend. -/
def b4_FFF : List (Fin 16 × Fin 16) := [(15, 15), (15, 0), (0, 0), (0, 0)]

/-- Emit body shared by both aligns, parameterized by the byte-1 cell:
    `conss B0C (conss CELL1 (conss b2 (conss b3 nil)))` under
    `λlo.λhi` (b1's nibble destructure).  Binders below λlo.λhi:
    hi=0, lo=1, b3=3, b2=5. -/
def alignEmit (cell1 : LTerm) : LTerm :=
  aps conssL [b0cT, aps conssL [cell1,
    aps conssL [.var 5, aps conssL [.var 3, nilL]]]]

/-- `_ALIGN512`'s inner `λlo.λhi. conss B0C (conss (PAIR (NIBANDE lo) hi)
    (conss b2 (conss b3 K)))`. -/
def align512K : LTerm :=
  .abs (.abs (alignEmit
    (aps pairSrcL [.app nibandEL (.var 1), .var 0])))

/-- `_ALIGN4096`'s inner `λlo.λhi. conss B0C (conss (PAIR sel0 hi)
    (conss b2 (conss b3 K)))`. -/
def align4096K : LTerm :=
  .abs (.abs (alignEmit
    (aps pairSrcL [nibLit 0, .var 0])))

/-- 4-cell peel continuation `λb0.λt0. t0 K (λb1.λt1. t1 K (λb2.λt2.
    t2 K (λb3.λt3. BODY)))` — `_peel` for names [b0..b3]. -/
def peel4K (BODY : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0) [klL,
    .abs (.abs (aps (.var 0) [klL,
      .abs (.abs (aps (.var 0) [klL,
        .abs (.abs BODY)]))]))]))

/-- `_ALIGN512 = λv. (λw. w K (peel4 BODY)) (B4ADD v 0x1FF)` with
    `BODY = b1·align512K`.  Under `λw λb0 λt0 λb1 λt1 λb2 λt2 λb3 λt3`:
    b1 = var 5. -/
def align512L : LTerm :=
  .abs (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
    (aps b4addL [.var 0, b4Lit b4_1FF]))

/-- `_ALIGN4096` — same skeleton, `0xFFF` addend, sel0 mask. -/
def align4096L : LTerm :=
  .abs (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align4096K)]))
    (aps b4addL [.var 0, b4Lit b4_FFF]))

theorem closed_align512L : closed 0 align512L = true := by decide
theorem closed_align4096L : closed 0 align4096L = true := by decide

-- empirical milestone check -------------------------------------------------


/-- Generic `peel4K` execution on abstract cells (same discharge shape as
    `b4inc_peel`): `scott4·K·peel4K(BODY)` → `BODY`-with-cells, where BODY is
    `.app (var 5) K2` — i.e. `b1`'s emit-continuation application. -/
theorem align512_peel (B0 B1 B2 B3 : LTerm)
    (h0 : closed 0 B0 = true) (h1 : closed 0 B1 = true)
    (h2 : closed 0 B2 = true) (h3 : closed 0 B3 = true)
    (hT3 : closed 0 (cellLit B3 nilL) = true)
    (hT2 : closed 0 (cellLit B2 (cellLit B3 nilL)) = true)
    (hT1 : closed 0 (cellLit B1 (cellLit B2 (cellLit B3 nilL))) = true) :
    LRed (aps (scottList [B0, B1, B2, B3])
             [klL, peel4K (.app (.var 5) align512K)])
      (.app B1 (.abs (.abs
        (aps conssL [b0cT,
          aps conssL [aps pairSrcL [.app nibandEL (.var 1), .var 0],
            aps conssL [B2, aps conssL [B3, nilL]]]])))) :=
  LRed_of_hsteps (k := 16) (by
    simp [peel4K, align512K, alignEmit, scottList, cellLit, aps,
          List.foldl, List.foldr, hsteps, hstep, subst, shift,
          shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_mono, closed_nilL, closed_klL, closed_conssL,
          closed_pairSrcL, closed_nibandEL, closed_b0cT,
          h0, h1, h2, h3, hT1, hT2, hT3])

/-- Same peel for the 4096 continuation (cell1 = `PAIR sel0 hi`). -/
theorem align4096_peel (B0 B1 B2 B3 : LTerm)
    (h0 : closed 0 B0 = true) (h1 : closed 0 B1 = true)
    (h2 : closed 0 B2 = true) (h3 : closed 0 B3 = true)
    (hT3 : closed 0 (cellLit B3 nilL) = true)
    (hT2 : closed 0 (cellLit B2 (cellLit B3 nilL)) = true)
    (hT1 : closed 0 (cellLit B1 (cellLit B2 (cellLit B3 nilL))) = true) :
    LRed (aps (scottList [B0, B1, B2, B3])
             [klL, peel4K (.app (.var 5) align4096K)])
      (.app B1 (.abs (.abs
        (aps conssL [b0cT,
          aps conssL [aps pairSrcL [nibLit 0, .var 0],
            aps conssL [B2, aps conssL [B3, nilL]]]])))) :=
  LRed_of_hsteps (k := 16) (by
    simp [peel4K, align4096K, alignEmit, scottList, cellLit, aps,
          List.foldl, List.foldr, hsteps, hstep, subst, shift,
          shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_mono, closed_nilL, closed_klL, closed_conssL,
          closed_pairSrcL, closed_nibandEL, closed_b0cT,
          closed_nibLit,
          h0, h1, h2, h3, hT1, hT2, hT3])

/-- `byteLit lo hi · (λlo.λhi.T) →* T[lo,hi]` — the emit-body entry. -/
theorem byteLit_apply2 (lo hi : Fin 16) (T : LTerm) :
    LRed (.app (byteLit lo hi) (.abs (.abs T)))
         (subst (nibLit hi) 0 (subst (nibLit lo) 1 T)) := by
  apply LRed_of_hsteps (k := 3)
  simp [byteLit, pairLit, hsteps, hstep, subst, shift, shift_zero,
        subst_shift_succ, subst_of_closed0, shift_of_closed0,
        closed_nibLit]

/-- peel + emit: `scott4·K·peel4K(b1·align512K) →* scottList` of the
    masked cells — byte0 := 0, byte1.lo &:= 0xE, bytes 2–3 passthrough. -/
theorem align512_peel_emit (w0 w1 w2 w3 : Fin 16 × Fin 16) :
    LRed (aps (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                          byteLit w2.1 w2.2, byteLit w3.1 w3.2])
             [klL, peel4K (.app (.var 5) align512K)])
      (scottList [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
                  byteLit w2.1 w2.2, byteLit w3.1 w3.2]) := by
  have hp := align512_peel (byteLit w0.1 w0.2) (byteLit w1.1 w1.2)
    (byteLit w2.1 w2.2) (byteLit w3.1 w3.2)
    (closed_byteLit _ _) (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_byteLit _ _)
    (closed_cellLit (closed_byteLit _ _) closed_nilL)
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _) closed_nilL))
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL)))
  have happ := byteLit_apply2 w1.1 w1.2
    (aps conssL [b0cT,
      aps conssL [aps pairSrcL [.app nibandEL (.var 1), .var 0],
        aps conssL [byteLit w2.1 w2.2,
          aps conssL [byteLit w3.1 w3.2, nilL]]]])
  have hsub : (subst (nibLit w1.2) 0 (subst (nibLit w1.1) 1
      (aps conssL [b0cT,
        aps conssL [aps pairSrcL [.app nibandEL (.var 1), .var 0],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]]))) =
      aps conssL [b0cT,
        aps conssL [aps pairSrcL [.app nibandEL (nibLit w1.1), nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]] := by
    simp [aps, List.foldl, subst, shift, subst_of_closed0, shift_of_closed0,
          closed_nibLit, closed_byteLit, closed_nibandEL, closed_b0cT,
          closed_conssL, closed_pairSrcL, closed_nilL]
  have hbody : LRed
      (.app (byteLit w1.1 w1.2)
        (.abs (.abs (aps conssL [b0cT,
          aps conssL [aps pairSrcL [.app nibandEL (.var 1), .var 0],
            aps conssL [byteLit w2.1 w2.2,
              aps conssL [byteLit w3.1 w3.2, nilL]]]]))))
      (aps conssL [b0cT,
        aps conssL [aps pairSrcL [.app nibandEL (nibLit w1.1), nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]]) :=
    hsub ▸ happ
  -- cell1: `PAIR (NIBANDE lo) hi →* byteLit (lo&E) hi`
  have hpr : LRed (aps pairSrcL [.app nibandEL (nibLit w1.1), nibLit w1.2])
      (byteLit (nibMaskE w1.1) w1.2) := by
    have h1 : LRed
        (.app (.app pairSrcL (.app nibandEL (nibLit w1.1))) (nibLit w1.2))
        (.app (.app pairSrcL (nibLit (nibMaskE w1.1))) (nibLit w1.2)) :=
      LRed_app_left (LRed_app_right (nibandE_correct w1.1))
    exact h1.trans (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _))
  -- emit chain, inside-out
  have hZ : LRed (aps conssL [byteLit w3.1 w3.2, nilL])
      (cellLit (byteLit w3.1 w3.2) nilL) :=
    conss_nf _ _ (closed_byteLit _ _) closed_nilL
  have hY : LRed (aps conssL [byteLit w2.1 w2.2,
        aps conssL [byteLit w3.1 w3.2, nilL]])
      (cellLit (byteLit w2.1 w2.2) (cellLit (byteLit w3.1 w3.2) nilL)) :=
    (LRed_app_right hZ).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL))
  have hc1 : LRed
      (aps conssL [aps pairSrcL [.app nibandEL (nibLit w1.1), nibLit w1.2],
        aps conssL [byteLit w2.1 w2.2,
          aps conssL [byteLit w3.1 w3.2, nilL]]])
      (cellLit (byteLit (nibMaskE w1.1) w1.2)
        (cellLit (byteLit w2.1 w2.2) (cellLit (byteLit w3.1 w3.2) nilL))) := by
    have h1 : LRed
        (aps conssL [aps pairSrcL [.app nibandEL (nibLit w1.1), nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]])
        (aps conssL [byteLit (nibMaskE w1.1) w1.2,
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]) :=
      LRed_app_left (LRed_app_right hpr)
    have h2 : LRed
        (aps conssL [byteLit (nibMaskE w1.1) w1.2,
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]])
        (aps conssL [byteLit (nibMaskE w1.1) w1.2,
          cellLit (byteLit w2.1 w2.2)
            (cellLit (byteLit w3.1 w3.2) nilL)]) :=
      LRed_app_right hY
    exact (h1.trans h2).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _) closed_nilL)))
  -- byte0 cell: `b0cT →* byteLit 0 0`, then collapse the outer conss
  have hb0 : LRed (.app conssL b0cT) (.app conssL (byteLit 0 0)) :=
    LRed_app_right (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _))
  have hfin : LRed
      (aps conssL [b0cT,
        aps conssL [aps pairSrcL [.app nibandEL (nibLit w1.1), nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]])
      (scottList [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
                  byteLit w2.1 w2.2, byteLit w3.1 w3.2]) :=
    ((LRed_app_left hb0).trans (LRed_app_right hc1)).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _)
            (closed_cellLit (closed_byteLit _ _) closed_nilL))))
  exact (hp.trans hbody).trans hfin

/-- `_ALIGN4096`'s peel+emit — same skeleton, cell1 = `PAIR sel0 hi`. -/
theorem align4096_peel_emit (w0 w1 w2 w3 : Fin 16 × Fin 16) :
    LRed (aps (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                          byteLit w2.1 w2.2, byteLit w3.1 w3.2])
             [klL, peel4K (.app (.var 5) align4096K)])
      (scottList [byteLit 0 0, byteLit 0 w1.2,
                  byteLit w2.1 w2.2, byteLit w3.1 w3.2]) := by
  have hp := align4096_peel (byteLit w0.1 w0.2) (byteLit w1.1 w1.2)
    (byteLit w2.1 w2.2) (byteLit w3.1 w3.2)
    (closed_byteLit _ _) (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_byteLit _ _)
    (closed_cellLit (closed_byteLit _ _) closed_nilL)
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _) closed_nilL))
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL)))
  have happ := byteLit_apply2 w1.1 w1.2
    (aps conssL [b0cT,
      aps conssL [aps pairSrcL [nibLit 0, .var 0],
        aps conssL [byteLit w2.1 w2.2,
          aps conssL [byteLit w3.1 w3.2, nilL]]]])
  have hsub : (subst (nibLit w1.2) 0 (subst (nibLit w1.1) 1
      (aps conssL [b0cT,
        aps conssL [aps pairSrcL [nibLit 0, .var 0],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]]))) =
      aps conssL [b0cT,
        aps conssL [aps pairSrcL [nibLit 0, nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]] := by
    simp [aps, List.foldl, subst, shift, subst_of_closed0, shift_of_closed0,
          closed_nibLit, closed_byteLit, closed_b0cT,
          closed_conssL, closed_pairSrcL, closed_nilL]
  have hbody : LRed
      (.app (byteLit w1.1 w1.2)
        (.abs (.abs (aps conssL [b0cT,
          aps conssL [aps pairSrcL [nibLit 0, .var 0],
            aps conssL [byteLit w2.1 w2.2,
              aps conssL [byteLit w3.1 w3.2, nilL]]]]))))
      (aps conssL [b0cT,
        aps conssL [aps pairSrcL [nibLit 0, nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]]) :=
    hsub ▸ happ
  have hpr : LRed (aps pairSrcL [nibLit 0, nibLit w1.2])
      (byteLit 0 w1.2) :=
    pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _)
  have hZ : LRed (aps conssL [byteLit w3.1 w3.2, nilL])
      (cellLit (byteLit w3.1 w3.2) nilL) :=
    conss_nf _ _ (closed_byteLit _ _) closed_nilL
  have hY : LRed (aps conssL [byteLit w2.1 w2.2,
        aps conssL [byteLit w3.1 w3.2, nilL]])
      (cellLit (byteLit w2.1 w2.2) (cellLit (byteLit w3.1 w3.2) nilL)) :=
    (LRed_app_right hZ).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL))
  have hc1 : LRed
      (aps conssL [aps pairSrcL [nibLit 0, nibLit w1.2],
        aps conssL [byteLit w2.1 w2.2,
          aps conssL [byteLit w3.1 w3.2, nilL]]])
      (cellLit (byteLit 0 w1.2)
        (cellLit (byteLit w2.1 w2.2) (cellLit (byteLit w3.1 w3.2) nilL))) := by
    have h1 : LRed
        (aps conssL [aps pairSrcL [nibLit 0, nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]])
        (aps conssL [byteLit 0 w1.2,
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]) :=
      LRed_app_left (LRed_app_right hpr)
    have h2 : LRed
        (aps conssL [byteLit 0 w1.2,
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]])
        (aps conssL [byteLit 0 w1.2,
          cellLit (byteLit w2.1 w2.2)
            (cellLit (byteLit w3.1 w3.2) nilL)]) :=
      LRed_app_right hY
    exact (h1.trans h2).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _) closed_nilL)))
  have hb0 : LRed (.app conssL b0cT) (.app conssL (byteLit 0 0)) :=
    LRed_app_right (pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _))
  have hfin : LRed
      (aps conssL [b0cT,
        aps conssL [aps pairSrcL [nibLit 0, nibLit w1.2],
          aps conssL [byteLit w2.1 w2.2,
            aps conssL [byteLit w3.1 w3.2, nilL]]]])
      (scottList [byteLit 0 0, byteLit 0 w1.2,
                  byteLit w2.1 w2.2, byteLit w3.1 w3.2]) :=
    ((LRed_app_left hb0).trans (LRed_app_right hc1)).trans
      (conss_nf _ _ (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _)
          (closed_cellLit (closed_byteLit _ _)
            (closed_cellLit (closed_byteLit _ _) closed_nilL))))
  exact (hp.trans hbody).trans hfin

/-- `resList` preserves length when the operand lengths agree. -/
theorem resList_length (as bs : List (Fin 16 × Fin 16)) (cn : Fin 16)
    (h : as.length = bs.length) :
    (resList as bs cn).length = as.length := by
  induction as generalizing bs cn with
  | nil => rfl
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      show ((byteStepN a b cn).1 ::
              resList as bs (byteStepN a b cn).2).length
        = (a :: as).length
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih bs _ (Nat.succ.inj h))

theorem exists_eq_of_length4 {α : Type} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tl⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · cases tl with
    | nil => exact ⟨a, b, c, d, rfl⟩
    | cons e tl => simp [List.length_cons] at h

/-- **`align512_eval`** — `ALIGN512·(b4 xs) →* scottList` of the aligned
    bytes: the `xs + 0x1FF` sum with byte0 := 0 and byte1.lo `& 0xE`. -/
theorem align512_eval (xs : List (Fin 16 × Fin 16))
    (hxs : xs.length = 4) :
    ∃ w0 w1 w2 w3,
      resList xs b4_1FF 0 = [w0, w1, w2, w3] ∧
      LRed (.app align512L (b4Lit xs))
        (scottList [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]) := by
  have hlen : (resList xs b4_1FF 0).length = 4 := by
    have h := resList_length xs b4_1FF 0 (by simp [b4_1FF]; exact hxs)
    rw [h, hxs]
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hlen
  refine ⟨w0, w1, w2, w3, hws, ?_⟩
  have hadd := b4add_eval xs b4_1FF (by simp [b4_1FF]; exact hxs)
  rw [hws] at hadd
  simp only [List.map_cons, List.map_nil] at hadd
  have hopen : LRed (.app align512L (b4Lit xs))
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (aps b4addL [b4Lit xs, b4Lit b4_1FF])) :=
    LRed_of_hsteps (k := 1) (by
      simp [align512L, hsteps, hstep, subst, shift, aps, List.foldl,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_b4Lit, closed_b4addL, closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT,
            peel4K, align512K, alignEmit])
  have harg : LRed
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (aps b4addL [b4Lit xs, b4Lit b4_1FF]))
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2])) :=
    LRed_app_right hadd
  have hbeta : LRed
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]))
      (aps (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                        byteLit w2.1 w2.2, byteLit w3.1 w3.2])
           [klL, peel4K (.app (.var 5) align512K)]) :=
    LRed_of_hsteps (k := 1) (by
      simp [hsteps, hstep, subst, shift, aps, List.foldl,
            peel4K, align512K, alignEmit,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_scottList, closed_byteLit, closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT])
  exact (hopen.trans harg).trans
    (hbeta.trans (align512_peel_emit w0 w1 w2 w3))

/-- **`align4096_eval`** — same skeleton; `xs + 0xFFF`, byte0 := 0,
    byte1.lo := 0. -/
theorem align4096_eval (xs : List (Fin 16 × Fin 16))
    (hxs : xs.length = 4) :
    ∃ w0 w1 w2 w3,
      resList xs b4_FFF 0 = [w0, w1, w2, w3] ∧
      LRed (.app align4096L (b4Lit xs))
        (scottList [byteLit 0 0, byteLit 0 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]) := by
  have hlen : (resList xs b4_FFF 0).length = 4 := by
    have h := resList_length xs b4_FFF 0 (by simp [b4_FFF]; exact hxs)
    rw [h, hxs]
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hlen
  refine ⟨w0, w1, w2, w3, hws, ?_⟩
  have hadd := b4add_eval xs b4_FFF (by simp [b4_FFF]; exact hxs)
  rw [hws] at hadd
  simp only [List.map_cons, List.map_nil] at hadd
  have hopen : LRed (.app align4096L (b4Lit xs))
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align4096K)]))
        (aps b4addL [b4Lit xs, b4Lit b4_FFF])) :=
    LRed_of_hsteps (k := 1) (by
      simp [align4096L, hsteps, hstep, subst, shift, aps, List.foldl,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_b4Lit, closed_b4addL, closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT,
            closed_nibLit, peel4K, align4096K, alignEmit])
  have harg : LRed
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align4096K)]))
        (aps b4addL [b4Lit xs, b4Lit b4_FFF]))
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align4096K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2])) :=
    LRed_app_right hadd
  have hbeta : LRed
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align4096K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]))
      (aps (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                        byteLit w2.1 w2.2, byteLit w3.1 w3.2])
           [klL, peel4K (.app (.var 5) align4096K)]) :=
    LRed_of_hsteps (k := 1) (by
      simp [hsteps, hstep, subst, shift, aps, List.foldl,
            peel4K, align4096K, alignEmit,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_scottList, closed_byteLit, closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT,
            closed_nibLit])
  exact (hopen.trans harg).trans
    (hbeta.trans (align4096_peel_emit w0 w1 w2 w3))





-- ============================================================
-- Batch E: PADLIST — peel b0 b1, rem = l0 + 16·h0 + 256·(l1 mod 2),
--          isZero-guarded TAIL-drop of ZEROFILL 512
-- ============================================================

/-- `_PADLIST`'s rem expression, under `λl1.λh1` — context
    `h1 l1 h0 l0 t1 b1 t0 b0 v`: l1 = var 1, h0 = var 2, l0 = var 3.
    `ADD (ADD (NIB2NUM l0) (MUL 16 (NIB2NUM h0))) (MUL 256 (NIBPAR l1))`. -/
def padRemL : LTerm :=
  aps churchAddL
    [aps churchAddL [aps nib2numL [.var 3],
       aps churchMulL [churchL 16, aps nib2numL [.var 2]]],
     aps churchMulL [churchL 256, aps nibparL [.var 1]]]

/-- `λrem. (rem·(λx.KI)·K)·K·(rem·TAIL·(ZEROFILL 512))` — the
    zero-remainder guard. -/
def padGuardL : LTerm :=
  .abs (aps (aps (.var 0) [iszStepL, klL])
        [klL, aps (.var 0) [tailL, .app zerofillL (churchL 512)]])

/-- `_PADLIST`'s byte body, under `λb1.λt1` — context
    `t1 b1 t0 b0 v`: b1 = var 1, b0 = var 3.
    `b0 (λl0.λh0. b1 (λl1.λh1. INNER))`. -/
def padBodyL : LTerm :=
  .app (.var 3)
    (.abs (.abs
      (.app (.var 3)
        (.abs (.abs (.app padGuardL padRemL))))))

/-- `_PADLIST = λv. v K (λb0.λt0. t0 K (λb1.λt1. BODY))`. -/
def padlistL : LTerm :=
  .abs (aps (.var 0) [klL,
    .abs (.abs (aps (.var 0) [klL, .abs (.abs padBodyL)]))])

/-- `padRemL` after the `l0,h0` substitution — `l1` still at var 1. -/
def padRemL1 (l0 h0 : Fin 16) : LTerm :=
  aps churchAddL
    [aps churchAddL [aps nib2numL [nibLit l0],
       aps churchMulL [churchL 16, aps nib2numL [nibLit h0]]],
     aps churchMulL [churchL 256, aps nibparL [.var 1]]]

/-- `padRemL` fully nibble-substituted. -/
def padRemInst (l0 h0 l1 : Fin 16) : LTerm :=
  aps churchAddL
    [aps churchAddL [aps nib2numL [nibLit l0],
       aps churchMulL [churchL 16, aps nib2numL [nibLit h0]]],
     aps churchMulL [churchL 256, aps nibparL [nibLit l1]]]

/-- Semantic remainder: `len & 511` = byte0 + byte1's parity byte. -/
def padRemN (x0 x1 : Fin 16 × Fin 16) : Nat :=
  x0.1.val + 16 * x0.2.val + 256 * (x1.1.val % 2)

/-- Output cells: `zeros((512 − rem) mod 512)` — nil on aligned
    input, else the 512-zero block minus `rem` cells. -/
def padCells (r : Nat) : List LTerm :=
  if r = 0 then [] else (List.replicate 512 b0cT).drop r

theorem closed_padGuardL : closed 0 padGuardL = true := by
  have hz : closed 0 (.app zerofillL (churchL 512)) = true :=
    closed_app closed_zerofillL (closed_churchL 512)
  simp only [padGuardL, aps, List.foldl, closed, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨Nat.zero_lt_one,
    closed_mono closed_iszStepL (Nat.zero_le 1)⟩,
    closed_mono closed_klL (Nat.zero_le 1)⟩,
    closed_mono closed_klL (Nat.zero_le 1)⟩,
    ⟨⟨Nat.zero_lt_one,
    closed_mono closed_tailL (Nat.zero_le 1)⟩,
    ⟨closed_mono closed_zerofillL (Nat.zero_le 1),
     closed_mono (closed_churchL 512) (Nat.zero_le 1)⟩⟩⟩

theorem closed_padGuardL_any (c : Nat) : closed c padGuardL = true :=
  closed_mono closed_padGuardL (Nat.zero_le c)

theorem closed_padRemL_c {c : Nat} (h : 4 ≤ c) :
    closed c padRemL = true := by
  have hmo : ∀ {t : LTerm}, closed 0 t = true → closed c t = true :=
    fun ht => closed_mono ht (Nat.zero_le c)
  simp only [padRemL, aps, List.foldl, closed, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨hmo closed_churchAddL,
    ⟨⟨hmo closed_churchAddL,
      ⟨hmo closed_nib2numL, Nat.lt_of_lt_of_le (by decide) h⟩⟩,
    ⟨⟨hmo closed_churchMulL, hmo (closed_churchL 16)⟩,
     ⟨hmo closed_nib2numL, Nat.lt_of_lt_of_le (by decide) h⟩⟩⟩⟩,
   ⟨⟨hmo closed_churchMulL, hmo (closed_churchL 256)⟩,
    ⟨hmo closed_nibparL, Nat.lt_of_lt_of_le (by decide) h⟩⟩⟩

theorem closed_padlistL : closed 0 padlistL = true := by
  have hmo : ∀ {t : LTerm} (c : Nat), closed 0 t = true →
      closed c t = true :=
    fun c ht => closed_mono ht (Nat.zero_le c)
  have h9 : closed 9 padRemL = true :=
    closed_padRemL_c (by decide)
  simp only [padlistL, padBodyL, aps, List.foldl,
    closed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨Nat.zero_lt_one, hmo 1 closed_klL⟩,
    ⟨⟨by decide, hmo 3 closed_klL⟩,
      ⟨by decide,
        ⟨by decide, ⟨hmo 9 closed_padGuardL, h9⟩⟩⟩⟩⟩

/-- closedness of `padBodyL` at any context depth ≥ 4. -/
theorem closed_padBodyL_c {c : Nat} (h : 4 ≤ c) :
    closed c padBodyL = true := by
  simp only [padBodyL, closed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨Nat.lt_of_lt_of_le (by decide : 3 < 4) h,
    ⟨Nat.lt_trans (Nat.lt_of_lt_of_le (by decide : 3 < 4) h)
        (by omega : c < c + 2),
      ⟨closed_padGuardL_any _,
        closed_padRemL_c (by omega : 4 ≤ c + 4)⟩⟩⟩

-- closed-at-any-depth lemmas (conditional-rewrite friendly forms) --

theorem closed_nilL_any (c : Nat) : closed c nilL = true :=
  closed_mono closed_nilL (Nat.zero_le c)
theorem closed_klL_any (c : Nat) : closed c klL = true :=
  closed_mono closed_klL (Nat.zero_le c)
theorem closed_iszStepL_any (c : Nat) : closed c iszStepL = true :=
  closed_mono closed_iszStepL (Nat.zero_le c)
theorem closed_tailL_any (c : Nat) : closed c tailL = true :=
  closed_mono closed_tailL (Nat.zero_le c)
theorem closed_zerofillL_any (c : Nat) : closed c zerofillL = true :=
  closed_mono closed_zerofillL (Nat.zero_le c)
theorem closed_churchL_any (n c : Nat) : closed c (churchL n) = true :=
  closed_mono (closed_churchL n) (Nat.zero_le c)
theorem closed_nibLit_any (i : Fin 16) (c : Nat) :
    closed c (nibLit i) = true :=
  closed_mono (closed_nibLit i) (Nat.zero_le c)
theorem closed_byteLit_any (lo hi : Fin 16) (c : Nat) :
    closed c (byteLit lo hi) = true :=
  closed_mono (closed_byteLit lo hi) (Nat.zero_le c)
theorem closed_nib2numL_any (c : Nat) : closed c nib2numL = true :=
  closed_mono closed_nib2numL (Nat.zero_le c)
theorem closed_nibparL_any (c : Nat) : closed c nibparL = true :=
  closed_mono closed_nibparL (Nat.zero_le c)
theorem closed_churchAddL_any (c : Nat) :
    closed c churchAddL = true :=
  closed_mono closed_churchAddL (Nat.zero_le c)
theorem closed_churchMulL_any (c : Nat) :
    closed c churchMulL = true :=
  closed_mono closed_churchMulL (Nat.zero_le c)

/-- 2-cell peel of a 4-list: `scott4·K·peel2(BODY) →* BODY-inst`. -/
theorem padlist_peel (B0 B1 B2 B3 : LTerm)
    (h0 : closed 0 B0 = true) (h1 : closed 0 B1 = true)
    (h2 : closed 0 B2 = true) (h3 : closed 0 B3 = true)
    (hT2 : closed 0 (cellLit B2 (cellLit B3 nilL)) = true)
    (hT1 : closed 0 (cellLit B1 (cellLit B2 (cellLit B3 nilL)))
      = true) :
    LRed (aps (scottList [B0, B1, B2, B3])
             [klL, .abs (.abs (aps (.var 0) [klL,
                 .abs (.abs padBodyL)]))])
      (.app B0 (.abs (.abs (.app B1
        (.abs (.abs (.app padGuardL padRemL))))))) :=
  LRed_of_hsteps (k := 8) (by
    simp [scottList, cellLit, aps, List.foldl, List.foldr, hsteps, hstep,
          padBodyL, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, subst_of_closed,
          shift_of_closed, closed, closed_app, closed_mono,
          closed_nilL, closed_klL,
          closed_padGuardL_any, closed_padRemL_c,
          h0, h1, h2, h3, hT1, hT2])

/-- isZero on a behavioral numeral: `M·iszStep·K →* boolLit (n == 0)`. -/
theorem isZero_num {n : Nat} {M : LTerm} (hM : IsChurchNum n M) :
    LRed (aps M [iszStepL, klL]) (boolLit (decide (n = 0))) := by
  have hstep : ∀ x, closed 0 x = true →
      LRed (.app iszStepL x) kilL ∧ closed 0 kilL = true :=
    fun x hx => ⟨iszStep_cell x hx, closed_kilL⟩
  have hiter := iter_red iszStepL (fun _ => kilL) hstep n klL closed_klL
  have hiterS : iterS (fun _ => kilL) klL n
      = if n = 0 then klL else kilL := by
    cases n with
    | zero => rfl
    | succ n => simp [iterS]
  refine (hM iszStepL klL closed_iszStepL closed_klL).trans (hiter.trans ?_)
  rw [hiterS]
  cases n <;> exact Relation.ReflTransGen.refl

/-- the pad leg: `rem·TAIL·(ZEROFILL 512) →* scottList (rep512.drop n)`. -/
theorem padLeg_num {n : Nat} {M : LTerm} (hM : IsChurchNum n M) :
    LRed (aps M [tailL, .app zerofillL (churchL 512)])
         (scottList ((List.replicate 512 b0cT).drop n)) := by
  have hcl : ∀ e ∈ List.replicate 512 b0cT, closed 0 e = true :=
    fun _ he => closed_rep_b0c he
  have h1 : LRed (aps M [tailL, .app zerofillL (churchL 512)])
      (aps M [tailL, scottList (List.replicate 512 b0cT)]) :=
    LRed_app_right (zerofill_eval 512)
  have h2 : LRed (aps M [tailL, scottList (List.replicate 512 b0cT)])
      (iterL tailL (scottList (List.replicate 512 b0cT)) n) :=
    hM tailL _ closed_tailL (closed_scottList hcl)
  exact (h1.trans h2).trans (iterL_tail_drop n _ hcl)

/-- `rem`'s behavioral numeral: `l0 + 16·h0 + 256·(l1 mod 2)`. -/
theorem padRem_num (l0 h0 l1 : Fin 16) :
    IsChurchNum (l0.val + 16 * h0.val + 256 * (l1.val % 2))
      (padRemInst l0 h0 l1) := by
  show IsChurchNum (l0.val + 16 * h0.val + 256 * (l1.val % 2))
      (aps churchAddL
        [aps churchAddL [aps nib2numL [nibLit l0],
           aps churchMulL [churchL 16, aps nib2numL [nibLit h0]]],
         aps churchMulL [churchL 256, aps nibparL [nibLit l1]]])
  have hlo : IsChurchNum (l0.val + 16 * h0.val)
      (aps churchAddL [aps nib2numL [nibLit l0],
        aps churchMulL [churchL 16, aps nib2numL [nibLit h0]]]) :=
    churchAdd_num _ _ _ _ (nib2num_num l0)
      (churchMul_num _ _ _ _ (churchL_num 16) (nib2num_num h0)
        (closed_churchL 16)
        (closed_app closed_nib2numL (closed_nibLit h0)))
      (closed_app closed_nib2numL (closed_nibLit l0))
      (closed_app (closed_app closed_churchMulL (closed_churchL 16))
        (closed_app closed_nib2numL (closed_nibLit h0)))
  have hhi : IsChurchNum (256 * (l1.val % 2))
      (aps churchMulL [churchL 256, aps nibparL [nibLit l1]]) :=
    churchMul_num _ _ _ _ (churchL_num 256) (nibpar_num l1)
      (closed_churchL 256)
      (closed_app closed_nibparL (closed_nibLit l1))
  exact churchAdd_num _ _ _ _ hlo hhi
    (closed_app (closed_app closed_churchAddL
      (closed_app closed_nib2numL (closed_nibLit l0)))
      (closed_app (closed_app closed_churchMulL (closed_churchL 16))
        (closed_app closed_nib2numL (closed_nibLit h0))))
    (closed_app (closed_app closed_churchMulL (closed_churchL 256))
      (closed_app closed_nibparL (closed_nibLit l1)))

/-- `PADLIST·(b4 xs) →* scottList (padCells (padRemN x0 x1))` — the
    zero-padding segment `zeros(align512 len − len)`. -/
theorem padlist_eval (x0 x1 x2 x3 : Fin 16 × Fin 16) :
    LRed (.app padlistL (b4Lit [x0, x1, x2, x3]))
         (scottList (padCells (padRemN x0 x1))) := by
  have hopen : LRed (.app padlistL (b4Lit [x0,x1,x2,x3]))
      (aps (b4Lit [x0,x1,x2,x3]) [klL,
        .abs (.abs (aps (.var 0) [klL, .abs (.abs padBodyL)]))]) := by
    simp only [padlistL]
    exact LRed_of_hsteps (k := 1) (by
      simp [aps, List.foldl, hsteps, hstep, subst, shift,
            shift_zero, subst_shift_succ, subst_of_closed0,
            subst_of_closed, closed, closed_app, closed_mono,
            closed_klL_any, closed_padBodyL_c])
  have hnf : LRed (aps (b4Lit [x0,x1,x2,x3]) [klL,
        .abs (.abs (aps (.var 0) [klL, .abs (.abs padBodyL)]))])
      (aps (scottList [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
                        byteLit x2.1 x2.2, byteLit x3.1 x3.2])
             [klL, .abs (.abs (aps (.var 0) [klL,
                .abs (.abs padBodyL)]))]) :=
    LRed_app_left (LRed_app_left (b4Lit_nf _))
  have hpeel := padlist_peel
    (byteLit x0.1 x0.2) (byteLit x1.1 x1.2)
    (byteLit x2.1 x2.2) (byteLit x3.1 x3.2)
    (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _) closed_nilL))
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL)))
  have happ0 := byteLit_apply2 x0.1 x0.2
    (.app (byteLit x1.1 x1.2)
      (.abs (.abs (.app padGuardL padRemL))))
  have hsub0 : subst (nibLit x0.2) 0 (subst (nibLit x0.1) 1
      (.app (byteLit x1.1 x1.2)
        (.abs (.abs (.app padGuardL padRemL))))) =
      .app (byteLit x1.1 x1.2)
        (.abs (.abs (.app padGuardL (padRemL1 x0.1 x0.2)))) := by
    simp [padRemL, padRemL1, aps, List.foldl, subst, shift,
          shift_zero, subst_shift_succ, subst_of_closed0,
          shift_of_closed0, subst_of_closed, shift_of_closed,
          closed, closed_app, closed_mono,
          closed_padGuardL_any, closed_nibLit_any, closed_byteLit_any,
          closed_churchL_any, closed_nib2numL_any, closed_nibparL_any,
          closed_churchAddL_any, closed_churchMulL_any]
  have happ1 := byteLit_apply2 x1.1 x1.2
    (.app padGuardL (padRemL1 x0.1 x0.2))
  have hsub1 : subst (nibLit x1.2) 0 (subst (nibLit x1.1) 1
      (.app padGuardL (padRemL1 x0.1 x0.2))) =
      .app padGuardL (padRemInst x0.1 x0.2 x1.1) := by
    simp [padRemL1, padRemInst, aps, List.foldl, subst, shift,
          shift_zero, subst_shift_succ, subst_of_closed0,
          shift_of_closed0, subst_of_closed, shift_of_closed,
          closed, closed_app, closed_mono,
          closed_padGuardL_any, closed_nibLit_any,
          closed_churchL_any, closed_nib2numL_any, closed_nibparL_any,
          closed_churchAddL_any, closed_churchMulL_any]
  have hbeta : LRed (.app padGuardL (padRemInst x0.1 x0.2 x1.1))
      (aps (aps (padRemInst x0.1 x0.2 x1.1) [iszStepL, klL])
        [klL, aps (padRemInst x0.1 x0.2 x1.1)
          [tailL, .app zerofillL (churchL 512)]]) := by
    apply LRed_of_hsteps (k := 1)
    simp [padGuardL, aps, List.foldl, hsteps, hstep, subst, shift,
          shift_zero, subst_shift_succ, subst_of_closed0,
          shift_of_closed0, subst_of_closed, shift_of_closed,
          closed, closed_app, closed_mono,
          closed_iszStepL_any, closed_klL_any, closed_tailL_any,
          closed_zerofillL_any, closed_churchL_any]
  have hrem : IsChurchNum (padRemN x0 x1)
      (padRemInst x0.1 x0.2 x1.1) :=
    padRem_num x0.1 x0.2 x1.1
  have hisz : LRed (aps (padRemInst x0.1 x0.2 x1.1) [iszStepL, klL])
      (boolLit (decide (padRemN x0 x1 = 0))) := isZero_num hrem
  have hpad : LRed (aps (padRemInst x0.1 x0.2 x1.1)
        [tailL, .app zerofillL (churchL 512)])
      (scottList ((List.replicate 512 b0cT).drop (padRemN x0 x1))) :=
    padLeg_num hrem
  have hdisp : LRed (aps (aps (padRemInst x0.1 x0.2 x1.1)
        [iszStepL, klL])
        [klL, aps (padRemInst x0.1 x0.2 x1.1)
          [tailL, .app zerofillL (churchL 512)]])
      (aps (boolLit (decide (padRemN x0 x1 = 0)))
        [klL, scottList
          ((List.replicate 512 b0cT).drop (padRemN x0 x1))]) :=
    (LRed_app_left (LRed_app_left hisz)).trans (LRed_app_right hpad)
  have htail : LRed
      (if decide (padRemN x0 x1 = 0) then klL
       else scottList
         ((List.replicate 512 b0cT).drop (padRemN x0 x1)))
      (scottList (padCells (padRemN x0 x1))) := by
    cases hd : decide (padRemN x0 x1 = 0) with
    | true =>
        have h0 : padRemN x0 x1 = 0 := of_decide_eq_true hd
        rw [padCells, if_pos h0]
        exact Relation.ReflTransGen.refl
    | false =>
        have h0 : ¬ padRemN x0 x1 = 0 := of_decide_eq_false hd
        simp only [padCells, if_neg h0]
        exact Relation.ReflTransGen.refl
  exact hopen.trans (hnf.trans (hpeel.trans
    ((hsub0 ▸ happ0).trans ((hsub1 ▸ happ1).trans
      (hbeta.trans (hdisp.trans
        ((boolLit_sel _ _ _).trans htail)))))))


-- ============================================================
-- Batch F: scottList-input variants — the assembly stage feeds
-- scottList NFs between lets; the b4Lit-typed state slots get
-- cellLit-carriers (the conss collapse is already done).
-- ============================================================

/-- `b4stepL` spine on a `cellLit`-formed `remB` — the `conss`
    collapse is skipped (2 steps saved vs `b4step_spine`). -/
theorem b4step_spine_scott (h bh bt cn acc : LTerm)
    (hh : closed 0 h = true) (hbh : closed 0 bh = true)
    (hbt : closed 0 bt = true) (hcn : closed 0 cn = true)
    (hacc : closed 0 acc = true) :
    LRed (aps b4stepL
           [pairLit (cellLit bh bt) (pairLit cn acc), h])
         (.app (aps addbcL [h, bh, cn]) (b4stepCont bt acc)) :=
  LRed_of_hsteps (k := 12) (by
    simp [b4stepL, pairLit, cellLit, addbcL, b4stepCont, letsL, aps,
          List.foldl, hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0, closed, closed_app,
          closed_klL, closed_pairSrcL, closed_b2nL, closed_conssL,
          closed_nibAddL, closed_nibCarryL, closed_orL,
          hh, hbh, hbt, hcn, hacc])

/-- full byte-step evaluation on a cellLit-carried state. -/
theorem b4step_eval_scott (xl xh yl yh cn : Fin 16) (bt acc : LTerm)
    (hbt : closed 0 bt = true) (hacc : closed 0 acc = true) :
    LRed (aps b4stepL
           [pairLit (cellLit (byteLit yl yh) bt)
                    (pairLit (nibLit cn) acc),
            byteLit xl xh])
         (pairLit bt
           (pairLit
             (nibLit (byteStepN (xl, xh) (yl, yh) cn).2)
             (cellLit
               (byteLit (byteStepN (xl, xh) (yl, yh) cn).1.1
                        (byteStepN (xl, xh) (yl, yh) cn).1.2)
               acc))) := by
  have hm := b4step_spine_scott (byteLit xl xh) (byteLit yl yh) bt
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

/-- `b4fold_run` on a scottList-carried `remB` state. -/
theorem b4fold_run_scott : ∀ (cs : List (Fin 16 × Fin 16))
    (bs : List (Fin 16 × Fin 16)) (cn : Fin 16) (acc : LTerm),
    cs.length ≤ bs.length → closed 0 acc = true →
    LRed (ggbA b4stepL (scottList (cs.map (fun p => byteLit p.1 p.2)))
           (pairLit (scottList (bs.map (fun p => byteLit p.1 p.2)))
             (pairLit (nibLit cn) acc)))
         (pairLit (scottList ((bs.drop cs.length).map
                    (fun p => byteLit p.1 p.2)))
           (pairLit (nibLit (carryAfter cs bs cn))
             ((resList cs bs cn).reverse.foldr
               (fun p t => cellLit (byteLit p.1 p.2) t) acc))) := by
  intro cs
  induction cs with
  | nil =>
    intro bs cn acc _ hacc
    simp only [scottList, List.map_nil, List.foldr_nil, List.drop_zero,
               carryAfter, resList, List.reverse_nil]
    have hcl : ∀ e ∈ bs.map (fun p => byteLit p.1 p.2),
        closed 0 e = true := fun e he => by
      simp only [List.mem_map] at he
      obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _
    exact nil_unfold b4stepL _ closed_b4stepL
      (closed_b4state (closed_scottList hcl) (closed_nibLit cn) hacc)
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
      have hstate0 : closed 0
          (pairLit (scottList ((b :: bs').map (fun p => byteLit p.1 p.2)))
            (pairLit (nibLit cn) acc)) = true :=
        closed_b4state
          (closed_scottList (fun e he => by
            simp only [List.mem_map] at he
            obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _))
          (closed_nibLit cn) hacc
      have e0 : scottList ((c :: cs').map (fun p => byteLit p.1 p.2))
          = cellLit (byteLit c.1 c.2)
              (scottList (cs'.map (fun p => byteLit p.1 p.2))) := rfl
      have e1 : scottList ((b :: bs').map (fun p => byteLit p.1 p.2))
          = cellLit (byteLit b.1 b.2)
              (scottList (bs'.map (fun p => byteLit p.1 p.2))) := rfl
      rw [e0, e1]
      have hstep := b4step_eval_scott c.1 c.2 b.1 b.2 cn
        (scottList (bs'.map (fun p => byteLit p.1 p.2))) acc
        (closed_scottList (fun e he => by
          simp only [List.mem_map] at he
          obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _)) hacc
      refine (cell_unfold b4stepL _ _ _ closed_b4stepL
        (closed_byteLit _ _) (closed_scottList htail) hstate0).trans ?_
      refine (LRed_app_right hstep).trans ?_
      have hih := ih bs' (byteStepN (c.1, c.2) (b.1, b.2) cn).2
        (cellLit (byteLit (byteStepN (c.1, c.2) (b.1, b.2) cn).1.1
                          (byteStepN (c.1, c.2) (b.1, b.2) cn).1.2) acc)
        hlen (closed_cellLit (closed_byteLit _ _) hacc)
      rw [show pairLit (scottList (((b :: bs').drop (c :: cs').length).map
                (fun p => byteLit p.1 p.2)))
            (pairLit (nibLit (carryAfter (c :: cs') (b :: bs') cn))
              ((resList (c :: cs') (b :: bs') cn).reverse.foldr
                (fun p t => cellLit (byteLit p.1 p.2) t) acc))
          = pairLit (scottList ((bs'.drop cs'.length).map
                (fun p => byteLit p.1 p.2)))
            (pairLit (nibLit (carryAfter cs' bs' (byteStepN c b cn).2))
              ((resList cs' bs' (byteStepN c b cn).2).reverse.foldr
                (fun p t => cellLit (byteLit p.1 p.2) t)
                (cellLit (byteLit (byteStepN c b cn).1.1
                          (byteStepN c b cn).1.2) acc)))
        from by
          simp [carryAfter, resList, List.length_cons, List.reverse_cons,
                List.foldr_append]]
      exact hih

/-- `B4ADD` on scottList-carried operands. -/
theorem b4add_eval_scott (as bs : List (Fin 16 × Fin 16))
    (h : as.length = bs.length) :
    LRed (aps b4addL [scottList (as.map (fun p => byteLit p.1 p.2)),
                      scottList (bs.map (fun p => byteLit p.1 p.2))])
         (scottList ((resList as bs 0).map
           (fun p => byteLit p.1 p.2))) := by
  have hclA : ∀ e ∈ as.map (fun p => byteLit p.1 p.2),
      closed 0 e = true := fun e he => by
    simp only [List.mem_map] at he
    obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _
  have hclB : ∀ e ∈ bs.map (fun p => byteLit p.1 p.2),
      closed 0 e = true := fun e he => by
    simp only [List.mem_map] at he
    obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _
  have hstate0 : closed 0 (pairLit
      (scottList (bs.map (fun p => byteLit p.1 p.2)))
      (pairLit (nibLit 0) klL)) = true :=
    closed_b4state (closed_scottList hclB) (closed_nibLit _) closed_klL
  have e1 : LRed (aps b4addL [scottList (as.map (fun p => byteLit p.1 p.2)),
                      scottList (bs.map (fun p => byteLit p.1 p.2))])
      (.app (aps foldlL [b4stepL,
              scottList (as.map (fun p => byteLit p.1 p.2)),
              aps pairSrcL [scottList (bs.map (fun p => byteLit p.1 p.2)),
                aps pairSrcL [nibLit 0, klL]]])
            b4finL) :=
    LRed_of_hsteps (k := 2) (by
      simp [b4addL, aps, List.foldl, hsteps, hstep, subst, shift,
            shift_zero, subst_shift_succ,
            shift_of_closed0, subst_of_closed0, closed, closed_app,
            closed_b4stepL, closed_b4finL, closed_foldlL, closed_pairSrcL,
            closed_nibLit, closed_klL, closed_scottList, hclA, hclB])
  have e2 : LRed (aps pairSrcL [scottList (bs.map (fun p => byteLit p.1 p.2)),
                    aps pairSrcL [nibLit 0, klL]])
      (pairLit (scottList (bs.map (fun p => byteLit p.1 p.2)))
        (pairLit (nibLit 0) klL)) :=
    (LRed_app_right (pairSrc_nf _ _ (closed_nibLit _) closed_klL)).trans
      (pairSrc_nf _ _ (closed_scottList hclB)
        (closed_pairLit (closed_mono (closed_nibLit _) (Nat.zero_le 1))
          (closed_mono closed_klL (Nat.zero_le 1))))
  refine e1.trans ((LRed_app_left (LRed_app_right e2)).trans ?_)
  refine (LRed_app_left (foldl_to_ggb b4stepL
    (scottList (as.map (fun p => byteLit p.1 p.2))) _
    closed_b4stepL (closed_scottList hclA) hstate0)).trans ?_
  refine (LRed_app_left (b4fold_run_scott as bs 0 klL h.le
    closed_klL)).trans ?_
  have hdrop : scottList ((bs.drop as.length).map
      (fun p => byteLit p.1 p.2)) = nilL := by
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

/-- `U64` on a scottList input — the append path is already
    `IsList`-parameterized, so this is `u64_eval` minus `b4Lit_nf`. -/
theorem u64_eval_scott (xs : List (Fin 16 × Fin 16)) :
    LRed (.app u64L (scottList (xs.map (fun p => byteLit p.1 p.2))))
      (scottList ((xs.map fun p => byteLit p.1 p.2)
        ++ List.replicate 4 b0cT)) := by
  have hxcl : ∀ e ∈ xs.map (fun p => byteLit p.1 p.2),
      closed 0 e = true := fun e he => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    exact closed_byteLit _ _
  have hsc : closed 0 (scottList (xs.map (fun p => byteLit p.1 p.2)))
      = true := closed_scottList hxcl
  have hopen : LRed (.app u64L (scottList (xs.map
        (fun p => byteLit p.1 p.2))))
      (aps appendL [scottList (xs.map (fun p => byteLit p.1 p.2)),
        u64Tail]) :=
    LRed_of_hsteps (k := 1) (by
      simp [u64L, aps, List.foldl, hsteps, hstep, subst, shift,
            subst_of_closed0 hsc, shift_of_closed0 hsc,
            subst_of_closed0 closed_u64Tail,
            shift_of_closed0 closed_u64Tail,
            subst_of_closed0 closed_appendL,
            shift_of_closed0 closed_appendL])
  have htail_is : IsList u64Tail (List.replicate 4 b0cT) := u64Tail_nf
  have hb4_is : IsList (scottList (xs.map fun p => byteLit p.1 p.2))
      (xs.map fun p => byteLit p.1 p.2) := Relation.ReflTransGen.refl
  refine hopen.trans ((appendL_to_appendT _ _ hsc
    closed_u64Tail).trans ?_)
  exact append_eval _ _ _ _ hb4_is htail_is hxcl
    (fun e he => closed_rep_b0c he) hsc closed_u64Tail

/-- `ALIGN512` on a scottList input — `B4ADD` gets a scott operand and a
    literal mask (normalized via `b4Lit_nf`). -/
theorem align512_eval_scott (xs : List (Fin 16 × Fin 16))
    (hxs : xs.length = 4) :
    ∃ w0 w1 w2 w3,
      resList xs b4_1FF 0 = [w0, w1, w2, w3] ∧
      LRed (.app align512L (scottList (xs.map (fun p => byteLit p.1 p.2))))
        (scottList [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]) := by
  have hlen : (resList xs b4_1FF 0).length = 4 := by
    have h := resList_length xs b4_1FF 0 (by simp [b4_1FF]; exact hxs)
    rw [h, hxs]
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hlen
  refine ⟨w0, w1, w2, w3, hws, ?_⟩
  have hxcl : ∀ e ∈ xs.map (fun p => byteLit p.1 p.2),
      closed 0 e = true := fun e he => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    exact closed_byteLit _ _
  have hscX : closed 0 (scottList (xs.map (fun p => byteLit p.1 p.2)))
      = true := closed_scottList hxcl
  have hmask : LRed (aps b4addL [scottList (xs.map
        (fun p => byteLit p.1 p.2)), b4Lit b4_1FF])
      (scottList ((resList xs b4_1FF 0).map (fun p => byteLit p.1 p.2))) :=
    (LRed_app_right (b4Lit_nf b4_1FF)).trans
      (b4add_eval_scott xs b4_1FF (by simp [b4_1FF]; exact hxs))
  have hadd := hmask
  rw [hws] at hadd
  simp only [List.map_cons, List.map_nil] at hadd
  have hopen : LRed (.app align512L
        (scottList (xs.map (fun p => byteLit p.1 p.2))))
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (aps b4addL [scottList (xs.map (fun p => byteLit p.1 p.2)),
          b4Lit b4_1FF])) :=
    LRed_of_hsteps (k := 1) (by
      simp [align512L, hsteps, hstep, subst, shift, aps, List.foldl,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_scottList, hxcl, closed_b4Lit, closed_b4addL,
            closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT,
            peel4K, align512K, alignEmit])
  have harg : LRed
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (aps b4addL [scottList (xs.map (fun p => byteLit p.1 p.2)),
          b4Lit b4_1FF]))
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2])) :=
    LRed_app_right hadd
  have hbeta : LRed
      (.app (.abs (aps (.var 0) [klL, peel4K (.app (.var 5) align512K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]))
      (aps (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                        byteLit w2.1 w2.2, byteLit w3.1 w3.2])
           [klL, peel4K (.app (.var 5) align512K)]) :=
    LRed_of_hsteps (k := 1) (by
      simp [hsteps, hstep, subst, shift, aps, List.foldl,
            peel4K, align512K, alignEmit,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_scottList, closed_byteLit, closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT])
  exact (hopen.trans harg).trans
    (hbeta.trans (align512_peel_emit w0 w1 w2 w3))

/-- `ALIGN4096` on a scottList input — same skeleton, `b4_FFF` mask. -/
theorem align4096_eval_scott (xs : List (Fin 16 × Fin 16))
    (hxs : xs.length = 4) :
    ∃ w0 w1 w2 w3,
      resList xs b4_FFF 0 = [w0, w1, w2, w3] ∧
      LRed (.app align4096L (scottList (xs.map (fun p => byteLit p.1 p.2))))
        (scottList [byteLit 0 0, byteLit 0 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]) := by
  have hlen : (resList xs b4_FFF 0).length = 4 := by
    have h := resList_length xs b4_FFF 0 (by simp [b4_FFF]; exact hxs)
    rw [h, hxs]
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hlen
  refine ⟨w0, w1, w2, w3, hws, ?_⟩
  have hxcl : ∀ e ∈ xs.map (fun p => byteLit p.1 p.2),
      closed 0 e = true := fun e he => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    exact closed_byteLit _ _
  have hadd : LRed (aps b4addL [scottList (xs.map
        (fun p => byteLit p.1 p.2)), b4Lit b4_FFF])
      (scottList ((resList xs b4_FFF 0).map (fun p => byteLit p.1 p.2))) :=
    (LRed_app_right (b4Lit_nf b4_FFF)).trans
      (b4add_eval_scott xs b4_FFF (by simp [b4_FFF]; exact hxs))
  rw [hws] at hadd
  simp only [List.map_cons, List.map_nil] at hadd
  have hopen : LRed (.app align4096L
        (scottList (xs.map (fun p => byteLit p.1 p.2))))
      (.app (.abs (aps (.var 0)
          [klL, peel4K (.app (.var 5) align4096K)]))
        (aps b4addL [scottList (xs.map (fun p => byteLit p.1 p.2)),
          b4Lit b4_FFF])) :=
    LRed_of_hsteps (k := 1) (by
      simp [align4096L, hsteps, hstep, subst, shift, aps, List.foldl,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_scottList, hxcl, closed_b4Lit, closed_b4addL,
            closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT,
            closed_nibLit, peel4K, align4096K, alignEmit])
  have harg : LRed
      (.app (.abs (aps (.var 0)
          [klL, peel4K (.app (.var 5) align4096K)]))
        (aps b4addL [scottList (xs.map (fun p => byteLit p.1 p.2)),
          b4Lit b4_FFF]))
      (.app (.abs (aps (.var 0)
          [klL, peel4K (.app (.var 5) align4096K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2])) :=
    LRed_app_right hadd
  have hbeta : LRed
      (.app (.abs (aps (.var 0)
          [klL, peel4K (.app (.var 5) align4096K)]))
        (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                    byteLit w2.1 w2.2, byteLit w3.1 w3.2]))
      (aps (scottList [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
                        byteLit w2.1 w2.2, byteLit w3.1 w3.2])
           [klL, peel4K (.app (.var 5) align4096K)]) :=
    LRed_of_hsteps (k := 1) (by
      simp [hsteps, hstep, subst, shift, aps, List.foldl,
            peel4K, align4096K, alignEmit,
            shift_zero, subst_of_closed0, shift_of_closed0,
            closed_scottList, closed_byteLit, closed_klL, closed_nilL,
            closed_conssL, closed_pairSrcL, closed_nibandEL, closed_b0cT,
            closed_nibLit])
  exact (hopen.trans harg).trans
    (hbeta.trans (align4096_peel_emit w0 w1 w2 w3))

/-- `PADLIST` on a scottList input — `padlist_peel` already takes the
    scott form; this is `padlist_eval` minus the `b4Lit_nf` bridge. -/
theorem padlist_eval_scott (x0 x1 x2 x3 : Fin 16 × Fin 16) :
    LRed (.app padlistL (scottList [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
          byteLit x2.1 x2.2, byteLit x3.1 x3.2]))
         (scottList (padCells (padRemN x0 x1))) := by
  have hopen : LRed (.app padlistL (scottList [byteLit x0.1 x0.2,
        byteLit x1.1 x1.2, byteLit x2.1 x2.2, byteLit x3.1 x3.2]))
      (aps (scottList [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
            byteLit x2.1 x2.2, byteLit x3.1 x3.2])
        [klL, .abs (.abs (aps (.var 0) [klL, .abs (.abs padBodyL)]))]) := by
    simp only [padlistL]
    exact LRed_of_hsteps (k := 1) (by
      simp [aps, List.foldl, hsteps, hstep, subst, shift,
            shift_zero, subst_shift_succ, subst_of_closed0,
            subst_of_closed, closed, closed_app, closed_mono,
            closed_scottList, closed_byteLit,
            closed_klL_any, closed_padBodyL_c])
  have hpeel := padlist_peel
    (byteLit x0.1 x0.2) (byteLit x1.1 x1.2)
    (byteLit x2.1 x2.2) (byteLit x3.1 x3.2)
    (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_byteLit _ _) (closed_byteLit _ _)
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _) closed_nilL))
    (closed_cellLit (closed_byteLit _ _)
      (closed_cellLit (closed_byteLit _ _)
        (closed_cellLit (closed_byteLit _ _) closed_nilL)))
  have happ0 := byteLit_apply2 x0.1 x0.2
    (.app (byteLit x1.1 x1.2)
      (.abs (.abs (.app padGuardL padRemL))))
  have hsub0 : subst (nibLit x0.2) 0 (subst (nibLit x0.1) 1
      (.app (byteLit x1.1 x1.2)
        (.abs (.abs (.app padGuardL padRemL))))) =
      .app (byteLit x1.1 x1.2)
        (.abs (.abs (.app padGuardL (padRemL1 x0.1 x0.2)))) := by
    simp [padRemL, padRemL1, aps, List.foldl, subst, shift,
          shift_zero, subst_shift_succ, subst_of_closed0,
          shift_of_closed0, subst_of_closed, shift_of_closed,
          closed, closed_app, closed_mono,
          closed_padGuardL_any, closed_nibLit_any, closed_byteLit_any,
          closed_churchL_any, closed_nib2numL_any, closed_nibparL_any,
          closed_churchAddL_any, closed_churchMulL_any]
  have happ1 := byteLit_apply2 x1.1 x1.2
    (.app padGuardL (padRemL1 x0.1 x0.2))
  have hsub1 : subst (nibLit x1.2) 0 (subst (nibLit x1.1) 1
      (.app padGuardL (padRemL1 x0.1 x0.2))) =
      .app padGuardL (padRemInst x0.1 x0.2 x1.1) := by
    simp [padRemL1, padRemInst, aps, List.foldl, subst, shift,
          shift_zero, subst_shift_succ, subst_of_closed0,
          shift_of_closed0, subst_of_closed, shift_of_closed,
          closed, closed_app, closed_mono,
          closed_padGuardL_any, closed_nibLit_any,
          closed_churchL_any, closed_nib2numL_any, closed_nibparL_any,
          closed_churchAddL_any, closed_churchMulL_any]
  have hbeta : LRed (.app padGuardL (padRemInst x0.1 x0.2 x1.1))
      (aps (aps (padRemInst x0.1 x0.2 x1.1) [iszStepL, klL])
        [klL, aps (padRemInst x0.1 x0.2 x1.1)
          [tailL, .app zerofillL (churchL 512)]]) := by
    apply LRed_of_hsteps (k := 1)
    simp [padGuardL, aps, List.foldl, hsteps, hstep, subst, shift,
          shift_zero, subst_shift_succ, subst_of_closed0,
          shift_of_closed0, subst_of_closed, shift_of_closed,
          closed, closed_app, closed_mono,
          closed_iszStepL_any, closed_klL_any, closed_tailL_any,
          closed_zerofillL_any, closed_churchL_any]
  have hrem : IsChurchNum (padRemN x0 x1)
      (padRemInst x0.1 x0.2 x1.1) :=
    padRem_num x0.1 x0.2 x1.1
  have hisz : LRed (aps (padRemInst x0.1 x0.2 x1.1) [iszStepL, klL])
      (boolLit (decide (padRemN x0 x1 = 0))) := isZero_num hrem
  have hpad : LRed (aps (padRemInst x0.1 x0.2 x1.1)
        [tailL, .app zerofillL (churchL 512)])
      (scottList ((List.replicate 512 b0cT).drop (padRemN x0 x1))) :=
    padLeg_num hrem
  have hdisp : LRed (aps (aps (padRemInst x0.1 x0.2 x1.1)
        [iszStepL, klL])
        [klL, aps (padRemInst x0.1 x0.2 x1.1)
          [tailL, .app zerofillL (churchL 512)]])
      (aps (boolLit (decide (padRemN x0 x1 = 0)))
        [klL, scottList
          ((List.replicate 512 b0cT).drop (padRemN x0 x1))]) :=
    (LRed_app_left (LRed_app_left hisz)).trans (LRed_app_right hpad)
  have htail : LRed
      (if decide (padRemN x0 x1 = 0) then klL
       else scottList
         ((List.replicate 512 b0cT).drop (padRemN x0 x1)))
      (scottList (padCells (padRemN x0 x1))) := by
    cases hd : decide (padRemN x0 x1 = 0) with
    | true =>
        have h0 : padRemN x0 x1 = 0 := of_decide_eq_true hd
        rw [padCells, if_pos h0]
        exact Relation.ReflTransGen.refl
    | false =>
        have h0 : ¬ padRemN x0 x1 = 0 := of_decide_eq_false hd
        simp only [padCells, if_neg h0]
        exact Relation.ReflTransGen.refl
  exact hopen.trans (hpeel.trans
    ((hsub0 ▸ happ0).trans ((hsub1 ▸ happ1).trans
      (hbeta.trans (hdisp.trans
        ((boolLit_sel _ _ _).trans htail))))))

/-- A conss-chain of closed cells normalizes to the scottList — the
    JOIN argument's chunk-list shape. -/
theorem conssChain_nf : ∀ (cs : List LTerm),
    (∀ e ∈ cs, closed 0 e = true) →
    LRed (cs.foldr (fun h t => aps conssL [h, t]) nilL)
         (scottList cs) := by
  intro cs; induction cs with
  | nil => intro _; exact Relation.ReflTransGen.refl
  | cons c cs' ih =>
      intro hcl
      rw [List.foldr_cons]
      exact (LRed_app_right (ih (fun e he =>
        hcl e (List.mem_cons_of_mem _ he)))).trans
        (conss_nf _ _ (hcl c (List.mem_cons_self))
          (closed_scottList (fun e he =>
            hcl e (List.mem_cons_of_mem _ he))))

-- axiom audits ---------------------------------------------------------------
#print axioms emitCells_nf
#print axioms pairLit_apply
#print axioms boolLit_sel
#print axioms b4incK2_apply
#print axioms b4inc_level_run
#print axioms b4inc_peel
#print axioms b4inc_eval_scott
#print axioms b4inc_eval
#print axioms incBytes_length
#print axioms foldl_enc_red
#print axioms lenStep_cell
#print axioms foldl_incBytes_val
#print axioms lenb4_eval
#print axioms nib2num_correct
#print axioms nibpar_correct
#print axioms nibandE_correct
#print axioms eqnib_eval
#print axioms eqb_eval
#print axioms churchAdd_eval
#print axioms churchMul_eval
#print axioms tail_scott
#print axioms isZero_eval
#print axioms u64_eval
#print axioms align512_peel
#print axioms align512_peel_emit
#print axioms align512_eval
#print axioms align4096_eval
#print axioms padlist_peel
#print axioms padlist_eval
#print axioms isZero_num
#print axioms padLeg_num
#print axioms padRem_num



#print axioms b4step_eval_scott
#print axioms b4fold_run_scott
#print axioms b4add_eval_scott
#print axioms u64_eval_scott
#print axioms align512_eval_scott
#print axioms align4096_eval_scott
#print axioms padlist_eval_scott
#print axioms conssChain_nf

-- ============================================================
-- Batch G: assembly machinery — composed numerals, chunk-chain
-- congruence, literal-byte chunks, the beta primitive.
-- ============================================================

/-- `ZEROFILL·M` for any `n`-behaving numeral — the `_num_src`
    MUL/ADD-composites land here, not at `churchL`-form. -/
theorem zerofill_num (n : Nat) (M : LTerm) (hM : IsChurchNum n M)
    (hc : closed 0 M = true) :
    LRed (.app zerofillL M) (scottList (List.replicate n b0cT)) := by
  have e1 : LRed (.app zerofillL M) (aps M [zerostepL, klL]) :=
    LRed_of_hsteps (k := 1) (by
      simp [zerofillL, aps, List.foldl, hsteps, hstep, subst, shift,
            shift_of_closed0 hc, subst_of_closed0 hc,
            shift_of_closed0 closed_zerostepL,
            subst_of_closed0 closed_zerostepL,
            shift_of_closed0 closed_klL, subst_of_closed0 closed_klL])
  have hs' : ∀ x, closed 0 x = true →
      LRed (.app zerostepL x) (cellLit b0cT x) ∧
      closed 0 (cellLit b0cT x) = true :=
    fun x hx => ⟨zerostep_cell x hx, closed_cellLit closed_b0cT hx⟩
  have hsc : iterS (fun x => cellLit b0cT x) klL n
      = scottList (List.replicate n b0cT) := by
    rw [iterS_scott]; rfl
  exact e1.trans ((hM zerostepL klL closed_zerostepL closed_klL).trans
    ((iter_red zerostepL (fun x => cellLit b0cT x) hs' n klL
      closed_klL).trans (hsc ▸ Relation.ReflTransGen.refl)))

/-- `_num_src 58` — `MUL 2 (ADD (MUL 14 2) 1)` (29 is prime). -/
def nz58 : LTerm := aps churchMulL [churchL 2,
  aps churchAddL [aps churchMulL [churchL 14, churchL 2], churchL 1]]

/-- `_num_src 64` — `MUL 16 4`. -/
def nz64 : LTerm := aps churchMulL [churchL 16, churchL 4]

/-- `_num_src 112` — `MUL 16 7`. -/
def nz112 : LTerm := aps churchMulL [churchL 16, churchL 7]

theorem closed_nz58 : closed 0 nz58 = true := by decide
theorem closed_nz64 : closed 0 nz64 = true := by decide
theorem closed_nz112 : closed 0 nz112 = true := by decide

theorem nz58_num : IsChurchNum 58 nz58 :=
  churchMul_num 2 (14 * 2 + 1) _ _
    (churchL_num 2)
    (churchAdd_num (14 * 2) 1 _ _
      (churchMul_num 14 2 _ _ (churchL_num 14) (churchL_num 2)
        (closed_churchL 14) (closed_churchL 2))
      (churchL_num 1)
      (by decide) (closed_churchL 1))
    (closed_churchL 2) (by decide)

theorem nz64_num : IsChurchNum 64 nz64 :=
  churchMul_num 16 4 _ _ (churchL_num 16) (churchL_num 4)
    (closed_churchL 16) (closed_churchL 4)

theorem nz112_num : IsChurchNum 112 nz112 :=
  churchMul_num 16 7 _ _ (churchL_num 16) (churchL_num 7)
    (closed_churchL 16) (closed_churchL 7)

/-- Pointwise `LRed` lifts into a `conss`-chain — the chunk-list
    congruence. -/
theorem conssChain_map_red : ∀ {cs cs' : List LTerm},
    List.Forall₂ LRed cs cs' →
    LRed (cs.foldr (fun h t => aps conssL [h, t]) nilL)
         (cs'.foldr (fun h t => aps conssL [h, t]) nilL) := by
  intro cs cs' h; induction h with
  | nil => exact Relation.ReflTransGen.refl
  | cons hhead _ ih =>
      simp only [List.foldr_cons]
      exact (LRed_app_left (LRed_app_right hhead)).trans
        (LRed_app_right ih)

/-- `_bytes_src` chunk: `conss (PAIR sel sel) · …` chain normalizes to
    the scottList of byteLit cells — `PAIR sel sel` collapses to the
    `pairLit`-form via `pairSrc_nf`, then `conssChain_nf`. -/
theorem bytesChunk_nf (bs : List (Fin 16 × Fin 16)) :
    LRed (bs.foldr (fun p t => aps conssL
             [aps pairSrcL [nibLit p.1, nibLit p.2], t]) nilL)
         (scottList (bs.map (fun p => byteLit p.1 p.2))) := by
  induction bs with
  | nil => exact Relation.ReflTransGen.refl
  | cons p bs' ih =>
      simp only [List.foldr_cons, List.map_cons]
      have hcell : LRed (aps pairSrcL [nibLit p.1, nibLit p.2])
          (byteLit p.1 p.2) :=
        pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _)
      exact ((LRed_app_left (LRed_app_right hcell)).trans
        (LRed_app_right ih)).trans
        (conss_nf _ _ (closed_byteLit _ _)
          (closed_scottList (fun e he => by
            obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
            exact closed_byteLit _ _)))

/-- one beta step — the let primitive. -/
theorem beta_app (B V : LTerm) :
    LRed (.app (.abs B) V) (subst V 0 B) :=
  LRed_of_hsteps (k := 1) rfl

#print axioms zerofill_num
#print axioms nz58_num
#print axioms conssChain_map_red
#print axioms bytesChunk_nf

-- ============================================================
-- Batch H: pack2Of — the PE image writer (post-link pack stage).
--   λtext. λidata. λdatab. λstackres. LETS + JOIN over 53 chunks.
-- ============================================================

/-- `_bytes_src` chunk — conss-chain of UNREDUCED `PAIR sel sel`
    cells (faithful: `_prs`-apps, one step above `byteLit`). -/
def bytesChunk (bs : List (Fin 16 × Fin 16)) : LTerm :=
  bs.foldr (fun p t => aps conssL
    [aps pairSrcL [nibLit p.1, nibLit p.2], t]) nilL

theorem closed_bytesChunk (bs : List (Fin 16 × Fin 16)) :
    closed 0 (bytesChunk bs) = true := by
  induction bs with
  | nil => exact closed_nilL
  | cons p bs' ih =>
      simp only [bytesChunk, List.foldr_cons]
      exact closed_app (closed_app closed_conssL
        (closed_app (closed_app closed_pairSrcL (closed_nibLit _))
          (closed_nibLit _))) ih

theorem closed_bytesChunk_any (c : Nat)
    (bs : List (Fin 16 × Fin 16)) :
    closed c (bytesChunk bs) = true :=
  closed_mono (closed_bytesChunk bs) (Nat.zero_le c)

-- PE byte constants (nibble pairs, little-endian) -----------------

def bMZ : List (Fin 16 × Fin 16) := [(13, 4), (10, 5)]
def b40 : List (Fin 16 × Fin 16) := [(0, 4), (0, 0), (0, 0), (0, 0)]
def bPE : List (Fin 16 × Fin 16) := [(0, 5), (5, 4), (0, 0), (0, 0)]
/-- `<HHIIIHH 0x8664,3,0,0,0,0xF0,0x22>` — COFF header, 20 bytes. -/
def bCOFF : List (Fin 16 × Fin 16) :=
  [(4,6),(6,8),(3,0),(0,0),(0,0),(0,0),(0,0),(0,0),
   (0,0),(0,0),(0,0),(0,0),(0,15),(0,0),(2,2),(0,0)]
/-- `<HBB 0x20B,0,0>` — optional-header magic + linker version. -/
def b20B : List (Fin 16 × Fin 16) := [(11,0),(2,0),(0,0),(0,0)]
def bZero4 : List (Fin 16 × Fin 16) := [(0,0),(0,0),(0,0),(0,0)]
/-- `<I 0x1000>` — 0x00 0x10 0x00 0x00. -/
def b1000 : List (Fin 16 × Fin 16) := [(0,0),(0,1),(0,0),(0,0)]
/-- `<Q 0x140000000>` — image base. -/
def bQ14 : List (Fin 16 × Fin 16) :=
  [(0,0),(0,0),(0,0),(0,4),(1,0),(0,0),(0,0),(0,0)]
/-- `<II 0x1000,0x200>` — section/file alignment. -/
def bAlign : List (Fin 16 × Fin 16) :=
  [(0,0),(0,1),(0,0),(0,0),(0,0),(2,0),(0,0),(0,0)]
/-- `<HHHHHH 6,0,0,0,6,0>` — OS/image/subsys versions. -/
def bVers : List (Fin 16 × Fin 16) :=
  [(6,0),(0,0),(0,0),(0,0),(0,0),(0,0),
   (0,0),(0,0),(6,0),(0,0),(0,0),(0,0)]
/-- `<II 0x200,0>` — checksum field pair (SizeOfImage follows). -/
def bII20 : List (Fin 16 × Fin 16) :=
  [(0,0),(2,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)]
/-- `<HH 3,0x8100>` — subsystem 3, DLL characteristics 0x8100. -/
def bSub : List (Fin 16 × Fin 16) := [(3,0),(0,0),(0,0),(1,8)]
/-- `<QQQ 0x1000,0x100000,0x1000>` — stack reserve/commit/heap. -/
def bStack : List (Fin 16 × Fin 16) :=
  [(0,0),(0,1),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),
   (0,0),(0,0),(0,1),(0,0),(0,0),(0,0),(0,0),(0,0),
   (0,0),(0,1),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)]
/-- `<II 0,16>` — loader flags, number of directories. -/
def bDirs : List (Fin 16 × Fin 16) :=
  [(0,0),(0,0),(0,0),(0,0),(0,1),(0,0),(0,0),(0,0)]
def bZero8 : List (Fin 16 × Fin 16) :=
  [(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)]
/-- `<I 0x2000>` — idata RVA. -/
def b2000 : List (Fin 16 × Fin 16) := [(0,0),(0,2),(0,0),(0,0)]
/-- `.text\0\0\0` section name. -/
def bText : List (Fin 16 × Fin 16) :=
  [(14,2),(4,7),(5,6),(8,7),(4,7),(0,0),(0,0),(0,0)]
/-- `<I 0x200>` — raw data offset/size base. -/
def b200 : List (Fin 16 × Fin 16) := [(0,0),(2,0),(0,0),(0,0)]
/-- `<I 0x60000020>` — .text characteristics. -/
def bTextFl : List (Fin 16 × Fin 16) := [(0,2),(0,0),(0,0),(0,6)]
/-- `.idata\0\0` section name. -/
def bIdata : List (Fin 16 × Fin 16) :=
  [(14,2),(9,6),(4,6),(1,6),(4,7),(1,6),(0,0),(0,0)]
/-- `<I 0x40000040>` — .idata characteristics. -/
def bIdataFl : List (Fin 16 × Fin 16) := [(0,4),(0,0),(0,0),(0,4)]
/-- `.data\0\0\0` section name. -/
def bData : List (Fin 16 × Fin 16) :=
  [(14,2),(4,6),(1,6),(4,7),(1,6),(0,0),(0,0),(0,0)]
/-- `<I 0x3000>` — .data RVA. -/
def b3000 : List (Fin 16 × Fin 16) := [(0,0),(0,3),(0,0),(0,0)]
/-- `<I 0xC0000040>` — .data characteristics. -/
def bDataFl : List (Fin 16 × Fin 16) := [(0,4),(0,0),(0,0),(0,12)]

-- let-binding values, in their binder contexts -------------------

/-- `LENB4 text` — under [sr,d,i,t]: text = var 3. -/
def ltV : LTerm := .app lenb4L (.var 3)
/-- `LENB4 idata` — under [lt,sr,d,i,t]: idata = var 3. -/
def liV : LTerm := .app lenb4L (.var 3)
/-- `LENB4 datab` — under [li,lt,sr,d,i,t]: datab = var 3. -/
def ldV : LTerm := .app lenb4L (.var 3)
/-- `ALIGN512 lt` — under [ld,li,lt,…]: lt = var 2. -/
def trawV : LTerm := .app align512L (.var 2)
/-- `ALIGN512 li` — under [traw,ld,li,lt,…]: li = var 2. -/
def irawV : LTerm := .app align512L (.var 2)
/-- `ALIGN512 ld` — under [iraw,traw,ld,li,lt,…]: ld = var 2. -/
def drawV : LTerm := .app align512L (.var 2)
/-- `B4ADD (b4 0x200) traw` — under [draw,iraw,traw,…]: traw = var 2. -/
def iptrV : LTerm := aps b4addL [bytesChunk b200, .var 2]
/-- `B4ADD iptr iraw` — under [iptr,draw,iraw,…]: iptr=0, iraw=2. -/
def dptrV : LTerm := aps b4addL [.var 0, .var 2]
/-- `B4ADD iraw draw` — under [dptr,iptr,draw,iraw,…]:
    iraw=3, draw=2. -/
def iddrV : LTerm := aps b4addL [.var 3, .var 2]
/-- `ALIGN4096 (B4ADD (b4 0x3000) ld)` — under
    [iddr,dptr,iptr,draw,iraw,traw,ld,…]: ld = var 6. -/
def imgV : LTerm := .app align4096L (aps b4addL [bytesChunk b3000, .var 6])

/-- the 53 JOIN chunks — context
    [img,iddr,dptr,iptr,draw,iraw,traw,ld,li,lt,sr,d,i,t]:
    img=0,iddr=1,dptr=2,iptr=3,draw=4,iraw=5,traw=6,ld=7,li=8,
    lt=9,sr=10,d=11,i=12,t=13. -/
def packChunks : List LTerm := [
  bytesChunk bMZ,                                   -- "MZ"
  .app zerofillL nz58,                              -- pad to 0x40
  bytesChunk b40,                                   -- PE header offset
  bytesChunk bPE,                                   -- "PE\0\0"
  bytesChunk bCOFF,                                 -- COFF header
  bytesChunk b20B,                                  -- opt magic+linkver
  .var 6,                                           -- traw (SizeOfCode)
  .var 1,                                           -- iddr (SizeOfInitData)
  bytesChunk bZero4,                                -- SizeOfUninitData
  bytesChunk b1000,                                 -- EntryPoint
  bytesChunk b1000,                                 -- BaseOfCode
  bytesChunk bQ14,                                  -- ImageBase
  bytesChunk bAlign,                                -- Section/FileAlign
  bytesChunk bVers,                                 -- versions
  bytesChunk bZero4,                                -- Win32Version
  .var 0,                                           -- img (SizeOfImage)
  bytesChunk bII20,                                 -- SizeOfHeaders+cksum
  bytesChunk bSub,                                  -- subsystem+DLLchar
  .app u64L (.var 10),                              -- stackres
  bytesChunk bStack,                                -- stack/heap
  bytesChunk bDirs,                                 -- loader flags, ndirs
  bytesChunk bZero8,                                -- export dir (empty)
  bytesChunk b2000,                                 -- import dir RVA
  .var 8,                                           -- li (import dir size)
  .app zerofillL nz112,                             -- rest of dirs
  bytesChunk bText,                                 -- ".text"
  .var 9,                                           -- lt
  bytesChunk b1000,                                 -- .text RVA
  .var 6,                                           -- traw
  bytesChunk b200,                                  -- .text raw ptr
  .app zerofillL (churchL 12),                      -- section rest
  bytesChunk bTextFl,                               -- .text flags
  bytesChunk bIdata,                                -- ".idata"
  .var 8,                                           -- li
  bytesChunk b2000,                                 -- .idata RVA
  .var 5,                                           -- iraw
  .var 3,                                           -- iptr
  .app zerofillL (churchL 12),
  bytesChunk bIdataFl,
  bytesChunk bData,                                 -- ".data"
  .var 7,                                           -- ld
  bytesChunk b3000,
  .var 4,                                           -- draw
  .var 2,                                           -- dptr
  .app zerofillL (churchL 12),
  bytesChunk bDataFl,
  .app zerofillL nz64,                              -- pad to 0x200
  .var 13,                                          -- text
  .app padlistL (.var 9),                           -- PADLIST lt
  .var 12,                                          -- idata
  .app padlistL (.var 8),                           -- PADLIST li
  .var 11,                                          -- datab
  .app padlistL (.var 7)]                           -- PADLIST ld

/-- `JOIN (conss-chain chunks)`. -/
def packBody : LTerm :=
  .app joinL (packChunks.foldr (fun c t => aps conssL [c, t]) nilL)

-- the let chain, innermost-last: each `app (abs NEXT) val` ----------
def packL9 : LTerm := .app (.abs packBody) imgV
def packL8 : LTerm := .app (.abs packL9) iddrV
def packL7 : LTerm := .app (.abs packL8) dptrV
def packL6 : LTerm := .app (.abs packL7) iptrV
def packL5 : LTerm := .app (.abs packL6) drawV
def packL4 : LTerm := .app (.abs packL5) irawV
def packL3 : LTerm := .app (.abs packL4) trawV
def packL2 : LTerm := .app (.abs packL3) ldV
def packL1 : LTerm := .app (.abs packL2) liV
def packLets : LTerm := .app (.abs packL1) ltV

/-- `pack2Of = λtext. λidata. λdatab. λstackres. lets+JOIN`. -/
def pack2L : LTerm := .abs (.abs (.abs (.abs packLets)))

-- closedness ------------------------------------------------------

theorem closed_joinL_any (c : Nat) : closed c joinL = true :=
  closed_mono closed_joinL (Nat.zero_le c)
theorem closed_conssL_any (c : Nat) : closed c conssL = true :=
  closed_mono closed_conssL (Nat.zero_le c)
theorem closed_pairSrcL_any (c : Nat) : closed c pairSrcL = true :=
  closed_mono closed_pairSrcL (Nat.zero_le c)
theorem closed_lenb4L_any (c : Nat) : closed c lenb4L = true :=
  closed_mono closed_lenb4L (Nat.zero_le c)
theorem closed_align512L_any (c : Nat) : closed c align512L = true :=
  closed_mono closed_align512L (Nat.zero_le c)
theorem closed_align4096L_any (c : Nat) : closed c align4096L = true :=
  closed_mono closed_align4096L (Nat.zero_le c)
theorem closed_b4addL_any (c : Nat) : closed c b4addL = true :=
  closed_mono closed_b4addL (Nat.zero_le c)
theorem closed_u64L_any (c : Nat) : closed c u64L = true :=
  closed_mono closed_u64L (Nat.zero_le c)
theorem closed_padlistL_any (c : Nat) : closed c padlistL = true :=
  closed_mono closed_padlistL (Nat.zero_le c)
theorem closed_nz58_any (c : Nat) : closed c nz58 = true :=
  closed_mono closed_nz58 (Nat.zero_le c)
theorem closed_nz64_any (c : Nat) : closed c nz64 = true :=
  closed_mono closed_nz64 (Nat.zero_le c)
theorem closed_nz112_any (c : Nat) : closed c nz112 = true :=
  closed_mono closed_nz112 (Nat.zero_le c)

theorem closed_pack2L : closed 0 pack2L = true := by
  simp [pack2L, packLets, packL1, packL2, packL3, packL4, packL5,
        packL6, packL7, packL8, packL9, packBody, packChunks,
        ltV, liV, ldV, trawV, irawV, drawV, iptrV, dptrV, iddrV, imgV,
        bytesChunk, bMZ, b40, bPE, bCOFF, b20B, bZero4, b1000, bQ14,
        bAlign, bVers, bII20, bSub, bStack, bDirs, bZero8, b2000,
        bText, b200, bTextFl, bIdata, bIdataFl, bData, b3000, bDataFl,
        nz58, nz64, nz112,
        closed, List.foldr, List.foldl, aps,
        closed_lenb4L_any, closed_align512L_any, closed_align4096L_any,
        closed_b4addL_any, closed_u64L_any, closed_padlistL_any,
        closed_zerofillL_any, closed_joinL_any, closed_conssL_any,
        closed_pairSrcL_any, closed_nibLit_any,
        closed_churchL_any, closed_churchMulL_any, closed_churchAddL_any,
        closed_nz58_any, closed_nz64_any, closed_nz112_any,
        closed_nilL_any]

-- the instantiated chunk list: let-values substituted -------------

/-- `packChunks` after all 14 betas — each var resolved to its
    (instantiated) let-value; `T I D S` the section inputs. -/
def packChunksInst (T I D S : LTerm) : List LTerm := [
  bytesChunk bMZ,                                   -- "MZ"
  .app zerofillL nz58,                              -- pad to 0x40
  bytesChunk b40,                                   -- PE header offset
  bytesChunk bPE,                                   -- "PE\0\0"
  bytesChunk bCOFF,                                 -- COFF header
  bytesChunk b20B,                                  -- opt magic+linkver
  .app align512L (.app lenb4L T),                   -- traw
  aps b4addL [.app align512L (.app lenb4L I),
              .app align512L (.app lenb4L D)],      -- iddr
  bytesChunk bZero4,                                -- SizeOfUninitData
  bytesChunk b1000,                                 -- EntryPoint
  bytesChunk b1000,                                 -- BaseOfCode
  bytesChunk bQ14,                                  -- ImageBase
  bytesChunk bAlign,                                -- Section/FileAlign
  bytesChunk bVers,                                 -- versions
  bytesChunk bZero4,                                -- Win32Version
  .app align4096L (aps b4addL [bytesChunk b3000,
    .app lenb4L D]),                                -- img
  bytesChunk bII20,                                 -- SizeOfHeaders+cksum
  bytesChunk bSub,                                  -- subsystem+DLLchar
  .app u64L S,                                      -- stackres
  bytesChunk bStack,                                -- stack/heap
  bytesChunk bDirs,                                 -- loader flags, ndirs
  bytesChunk bZero8,                                -- export dir (empty)
  bytesChunk b2000,                                 -- import dir RVA
  .app lenb4L I,                                    -- li
  .app zerofillL nz112,                             -- rest of dirs
  bytesChunk bText,                                 -- ".text"
  .app lenb4L T,                                    -- lt
  bytesChunk b1000,                                 -- .text RVA
  .app align512L (.app lenb4L T),                   -- traw
  bytesChunk b200,                                  -- .text raw ptr
  .app zerofillL (churchL 12),                      -- section rest
  bytesChunk bTextFl,                               -- .text flags
  bytesChunk bIdata,                                -- ".idata"
  .app lenb4L I,                                    -- li
  bytesChunk b2000,                                 -- .idata RVA
  .app align512L (.app lenb4L I),                   -- iraw
  aps b4addL [bytesChunk b200,
    .app align512L (.app lenb4L T)],                -- iptr
  .app zerofillL (churchL 12),
  bytesChunk bIdataFl,
  bytesChunk bData,                                 -- ".data"
  .app lenb4L D,                                    -- ld
  bytesChunk b3000,
  .app align512L (.app lenb4L D),                   -- draw
  aps b4addL [aps b4addL [bytesChunk b200,
                .app align512L (.app lenb4L T)],
              .app align512L (.app lenb4L I)],      -- dptr
  .app zerofillL (churchL 12),
  bytesChunk bDataFl,
  .app zerofillL nz64,                              -- pad to 0x200
  T,                                                -- text
  .app padlistL (.app lenb4L T),                    -- PADLIST lt
  I,                                                -- idata
  .app padlistL (.app lenb4L I),                    -- PADLIST li
  D,                                                -- datab
  .app padlistL (.app lenb4L D)]                    -- PADLIST ld

/-- `conss`-chain over a chunk list — the JOIN argument's shape. -/
def chunkChain (cs : List LTerm) : LTerm :=
  cs.foldr (fun c t => aps conssL [c, t]) nilL

-- semantic image ----------------------------------------------------

/-- byte-list → cell-list. -/
def bm (xs : List (Fin 16 × Fin 16)) : List LTerm :=
  xs.map (fun p => byteLit p.1 p.2)

/-- `_LENB4`'s semantic count — bytes4 incremented once per cell. -/
def len4 (xs : List (Fin 16 × Fin 16)) : List (Fin 16 × Fin 16) :=
  xs.foldl (fun a _ => incBytes a true) b4zeroBytes

theorem len4_length (xs : List (Fin 16 × Fin 16)) :
    (len4 xs).length = 4 := by
  have h : ∀ (xs acc : List (Fin 16 × Fin 16)),
      (xs.foldl (fun a _ => incBytes a true) acc).length
      = acc.length := by
    intro xs; induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, incBytes_length]
  rw [len4, h]; rfl

/-- `ALIGN512`'s semantic output bytes: `resList` destructured, byte0
    := 0, byte1.lo `& 0xE`. -/
def align512Bytes (xs : List (Fin 16 × Fin 16)) :
    List (Fin 16 × Fin 16) :=
  match resList xs b4_1FF 0 with
  | [_, w1, w2, w3] => [(0, 0), (nibMaskE w1.1, w1.2), w2, w3]
  | _ => []

/-- `ALIGN4096`'s semantic output bytes: byte1 := `PAIR sel0 hi`. -/
def align4096Bytes (xs : List (Fin 16 × Fin 16)) :
    List (Fin 16 × Fin 16) :=
  match resList xs b4_FFF 0 with
  | [_, w1, w2, w3] => [(0, 0), (0, w1.2), w2, w3]
  | _ => []

theorem align512Bytes_length (xs : List (Fin 16 × Fin 16))
    (h : xs.length = 4) : (align512Bytes xs).length = 4 := by
  have hl : (resList xs b4_1FF 0).length = 4 := by
    rw [resList_length _ _ _ (by simp [b4_1FF]; exact h), h]
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hl
  simp [align512Bytes, hws]

theorem align4096Bytes_length (xs : List (Fin 16 × Fin 16))
    (h : xs.length = 4) : (align4096Bytes xs).length = 4 := by
  have hl : (resList xs b4_FFF 0).length = 4 := by
    rw [resList_length _ _ _ (by simp [b4_FFF]; exact h), h]
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hl
  simp [align4096Bytes, hws]

/-- `PADLIST`'s remainder from a length-list (`0` on short input —
    unreachable on `len4` outputs). -/
def padRemOf (xs : List (Fin 16 × Fin 16)) : Nat :=
  match xs with
  | x0 :: x1 :: _ => padRemN x0 x1
  | _ => 0

/-- the 53 chunk cell-lists — the PE image's byte payload by section. -/
def pack2Cells (tb ib db sb : List (Fin 16 × Fin 16)) : List (List LTerm) :=
  let ltB := len4 tb
  let liB := len4 ib
  let ldB := len4 db
  let trawB := align512Bytes ltB
  let irawB := align512Bytes liB
  let drawB := align512Bytes ldB
  let iptrB := resList b200 trawB 0
  let dptrB := resList iptrB irawB 0
  let iddrB := resList irawB drawB 0
  let imgB := align4096Bytes (resList b3000 ldB 0)
  [ bm bMZ, List.replicate 58 b0cT, bm b40, bm bPE, bm bCOFF, bm b20B,
    bm trawB, bm iddrB,
    bm bZero4, bm b1000, bm b1000, bm bQ14, bm bAlign, bm bVers,
    bm bZero4, bm imgB, bm bII20, bm bSub,
    bm sb ++ List.replicate 4 b0cT,
    bm bStack, bm bDirs, bm bZero8, bm b2000,
    bm liB, List.replicate 112 b0cT, bm bText, bm ltB, bm b1000,
    bm trawB, bm b200, List.replicate 12 b0cT, bm bTextFl,
    bm bIdata, bm liB, bm b2000, bm irawB, bm iptrB,
    List.replicate 12 b0cT, bm bIdataFl, bm bData, bm ldB, bm b3000,
    bm drawB, bm dptrB, List.replicate 12 b0cT, bm bDataFl,
    List.replicate 64 b0cT,
    bm tb, padCells (padRemOf ltB), bm ib, padCells (padRemOf liB),
    bm db, padCells (padRemOf ldB) ]

-- the 14-beta milestone ------------------------------------------------

set_option maxHeartbeats 8000000 in
theorem pack2_open (T I D S : LTerm)
    (hT : closed 0 T = true) (hI : closed 0 I = true)
    (hD : closed 0 D = true) (hS : closed 0 S = true) :
    LRed (aps pack2L [T, I, D, S])
         (.app joinL (chunkChain (packChunksInst T I D S))) :=
  LRed_of_hsteps (k := 14) (by
    simp [pack2L, packLets, packL1, packL2, packL3, packL4, packL5,
          packL6, packL7, packL8, packL9, packBody, packChunks,
          packChunksInst, chunkChain,
          ltV, liV, ldV, trawV, irawV, drawV, iptrV, dptrV, iddrV, imgV,
          bytesChunk, bMZ, b40, bPE, bCOFF, b20B, bZero4, b1000, bQ14,
          bAlign, bVers, bII20, bSub, bStack, bDirs, bZero8, b2000,
          bText, b200, bTextFl, bIdata, bIdataFl, bData, b3000, bDataFl,
          nz58, nz64, nz112,
          aps, List.foldl, List.foldr,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, subst_of_closed,
          shift_of_closed0, shift_of_closed,
          closed, closed_app, closed_mono,
          hT, hI, hD, hS,
          closed_lenb4L_any, closed_align512L_any, closed_align4096L_any,
          closed_b4addL_any, closed_u64L_any, closed_padlistL_any,
          closed_zerofillL_any, closed_joinL_any, closed_conssL_any,
          closed_pairSrcL_any, closed_nibLit_any, closed_churchL_any,
          closed_churchMulL_any, closed_churchAddL_any,
          closed_nz58_any, closed_nz64_any, closed_nz112_any,
          closed_klL_any, closed_nilL_any, closed_bytesChunk_any])

-- closedness of packCells elements --------------------------------------

theorem closed_bm {e : LTerm} {xs : List (Fin 16 × Fin 16)}
    (he : e ∈ bm xs) : closed 0 e = true := by
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
  exact closed_byteLit _ _

theorem closed_padCells {e : LTerm} {r : Nat}
    (he : e ∈ padCells r) : closed 0 e = true := by
  simp only [padCells] at he
  split at he
  · simp at he
  · exact closed_rep_b0c
      (List.Sublist.mem he (List.drop_sublist _ _))

-- bridge: fold over mapped cells = fold over the bytes -------------------

theorem foldl_const_step_map {α β γ : Type} (l : List α) (g : α → β)
    (f : γ → γ) (acc : γ) :
    (l.map g).foldl (fun a _ => f a) acc
      = l.foldl (fun a _ => f a) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih _

-- closedness of every cell the image produces ----------------------------

theorem closed_bm_app_rep {e : LTerm} {xs : List (Fin 16 × Fin 16)}
    {n : Nat} (he : e ∈ bm xs ++ List.replicate n b0cT) :
    closed 0 e = true := by
  rcases List.mem_append.mp he with h|h <;>
    first | exact closed_bm h | exact closed_rep_b0c h

theorem closed_pack2Cells_flat {e : LTerm} {tb ib db sb}
    (he : e ∈ (pack2Cells tb ib db sb).flatten) :
    closed 0 e = true := by
  obtain ⟨cs, hcs, he⟩ := List.mem_flatten.mp he
  simp only [pack2Cells, List.mem_cons, List.not_mem_nil,
             or_false] at hcs
  rcases hcs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact closed_bm he
    | exact closed_padCells he
    | exact closed_rep_b0c he
    | exact closed_bm_app_rep he

-- the assembly ------------------------------------------------------------

set_option maxHeartbeats 8000000 in
theorem pack2_eval (tb ib db sb : List (Fin 16 × Fin 16)) :
    LRed (aps pack2L [scottList (bm tb), scottList (bm ib),
                      scottList (bm db), scottList (bm sb)])
         (scottList (pack2Cells tb ib db sb).flatten) := by
  -- input closedness
  have hclT : ∀ e ∈ bm tb, closed 0 e = true := fun _ h => closed_bm h
  have hclI : ∀ e ∈ bm ib, closed 0 e = true := fun _ h => closed_bm h
  have hclD : ∀ e ∈ bm db, closed 0 e = true := fun _ h => closed_bm h
  have hclS : ∀ e ∈ bm sb, closed 0 e = true := fun _ h => closed_bm h
  have hscT : closed 0 (scottList (bm tb)) = true := closed_scottList hclT
  have hscI : closed 0 (scottList (bm ib)) = true := closed_scottList hclI
  have hscD : closed 0 (scottList (bm db)) = true := closed_scottList hclD
  have hscS : closed 0 (scottList (bm sb)) = true := closed_scottList hclS
  -- LENB4 legs
  have hlt : LRed (.app lenb4L (scottList (bm tb)))
      (scottList (bm (len4 tb))) := by
    have h := lenb4_eval (bm tb) hclT
    simp only [bm] at h
    rw [foldl_const_step_map] at h
    exact h
  have hli : LRed (.app lenb4L (scottList (bm ib)))
      (scottList (bm (len4 ib))) := by
    have h := lenb4_eval (bm ib) hclI
    simp only [bm] at h
    rw [foldl_const_step_map] at h
    exact h
  have hld : LRed (.app lenb4L (scottList (bm db)))
      (scottList (bm (len4 db))) := by
    have h := lenb4_eval (bm db) hclD
    simp only [bm] at h
    rw [foldl_const_step_map] at h
    exact h
  -- lengths
  have hlt4 : (len4 tb).length = 4 := len4_length tb
  have hli4 : (len4 ib).length = 4 := len4_length ib
  have hld4 : (len4 db).length = 4 := len4_length db
  have htraw4 : (align512Bytes (len4 tb)).length = 4 :=
    align512Bytes_length _ hlt4
  have hiraw4 : (align512Bytes (len4 ib)).length = 4 :=
    align512Bytes_length _ hli4
  have hdraw4 : (align512Bytes (len4 db)).length = 4 :=
    align512Bytes_length _ hld4
  have hiptr4 : (resList b200 (align512Bytes (len4 tb)) 0).length = 4 := by
    rw [resList_length _ _ _ (by rw [htraw4]; rfl), show b200.length = 4 from rfl]
  -- ALIGN legs (existential destructures)
  have htraw : LRed (.app align512L (scottList (bm (len4 tb))))
      (scottList (bm (align512Bytes (len4 tb)))) := by
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align512_eval_scott (len4 tb) hlt4
    have heq : bm (align512Bytes (len4 tb)) =
        [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
         byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
      simp [align512Bytes, hws, bm]
    rw [heq]; exact hred
  have hiraw : LRed (.app align512L (scottList (bm (len4 ib))))
      (scottList (bm (align512Bytes (len4 ib)))) := by
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align512_eval_scott (len4 ib) hli4
    have heq : bm (align512Bytes (len4 ib)) =
        [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
         byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
      simp [align512Bytes, hws, bm]
    rw [heq]; exact hred
  have hdraw : LRed (.app align512L (scottList (bm (len4 db))))
      (scottList (bm (align512Bytes (len4 db)))) := by
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align512_eval_scott (len4 db) hld4
    have heq : bm (align512Bytes (len4 db)) =
        [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
         byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
      simp [align512Bytes, hws, bm]
    rw [heq]; exact hred
  -- B4ADD congruence helper
  have hb4add : ∀ {A B : LTerm} {as bs : List (Fin 16 × Fin 16)},
      LRed A (scottList (bm as)) → LRed B (scottList (bm bs)) →
      as.length = bs.length →
      LRed (aps b4addL [A, B]) (scottList (bm (resList as bs 0))) := by
    intro A B as bs hA hB hl
    exact ((LRed_app_left (LRed_app_right hA)).trans
      (LRed_app_right hB)).trans (b4add_eval_scott as bs hl)
  -- composed let-value legs
  have htrawT : LRed (.app align512L (.app lenb4L (scottList (bm tb))))
      (scottList (bm (align512Bytes (len4 tb)))) :=
    (LRed_app_right hlt).trans htraw
  have hirawT : LRed (.app align512L (.app lenb4L (scottList (bm ib))))
      (scottList (bm (align512Bytes (len4 ib)))) :=
    (LRed_app_right hli).trans hiraw
  have hdrawT : LRed (.app align512L (.app lenb4L (scottList (bm db))))
      (scottList (bm (align512Bytes (len4 db)))) :=
    (LRed_app_right hld).trans hdraw
  have hiptrT : LRed (aps b4addL [bytesChunk b200,
        .app align512L (.app lenb4L (scottList (bm tb)))])
      (scottList (bm (resList b200 (align512Bytes (len4 tb)) 0))) :=
    hb4add (bytesChunk_nf b200) htrawT (by rw [htraw4]; rfl)
  have hdptrT : LRed (aps b4addL [aps b4addL [bytesChunk b200,
        .app align512L (.app lenb4L (scottList (bm tb)))],
        .app align512L (.app lenb4L (scottList (bm ib)))])
      (scottList (bm (resList (resList b200 (align512Bytes (len4 tb)) 0)
        (align512Bytes (len4 ib)) 0))) :=
    hb4add hiptrT hirawT (by rw [hiptr4, hiraw4])
  have hiddrT : LRed (aps b4addL
        [.app align512L (.app lenb4L (scottList (bm ib))),
         .app align512L (.app lenb4L (scottList (bm db)))])
      (scottList (bm (resList (align512Bytes (len4 ib))
        (align512Bytes (len4 db)) 0))) :=
    hb4add hirawT hdrawT (by rw [hiraw4, hdraw4])
  have himgT : LRed (.app align4096L (aps b4addL [bytesChunk b3000,
        .app lenb4L (scottList (bm db))]))
      (scottList (bm (align4096Bytes (resList b3000 (len4 db) 0)))) := by
    have hpre : LRed (aps b4addL [bytesChunk b3000,
          .app lenb4L (scottList (bm db))])
        (scottList (bm (resList b3000 (len4 db) 0))) :=
      hb4add (bytesChunk_nf b3000) hld (by rw [hld4]; rfl)
    have hlen4' : (resList b3000 (len4 db) 0).length = 4 := by
      rw [resList_length _ _ _ (by rw [hld4]; rfl)]
      rfl
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align4096_eval_scott (resList b3000 (len4 db) 0) hlen4'
    have h2 : LRed (.app align4096L (scottList (bm (resList b3000
          (len4 db) 0))))
        (scottList (bm (align4096Bytes (resList b3000 (len4 db) 0)))) := by
      have heq : bm (align4096Bytes (resList b3000 (len4 db) 0)) =
          [byteLit 0 0, byteLit 0 w1.2,
           byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
        simp [align4096Bytes, hws, bm]
      rw [heq]; exact hred
    exact (LRed_app_right hpre).trans h2
  -- PADLIST legs
  have hpadT : LRed (.app padlistL (.app lenb4L (scottList (bm tb))))
      (scottList (padCells (padRemOf (len4 tb)))) := by
    obtain ⟨x0, x1, x2, x3, hx⟩ := exists_eq_of_length4 hlt4
    have h2 : LRed (.app padlistL (scottList (bm (len4 tb))))
        (scottList (padCells (padRemOf (len4 tb)))) := by
      have heq : bm (len4 tb) =
          [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        rw [hx]; rfl
      have heq2 : padCells (padRemOf (len4 tb)) =
          padCells (padRemN x0 x1) := by
        rw [hx]; rfl
      rw [heq, heq2]; exact padlist_eval_scott x0 x1 x2 x3
    exact (LRed_app_right hlt).trans h2
  have hpadI : LRed (.app padlistL (.app lenb4L (scottList (bm ib))))
      (scottList (padCells (padRemOf (len4 ib)))) := by
    obtain ⟨x0, x1, x2, x3, hx⟩ := exists_eq_of_length4 hli4
    have h2 : LRed (.app padlistL (scottList (bm (len4 ib))))
        (scottList (padCells (padRemOf (len4 ib)))) := by
      have heq : bm (len4 ib) =
          [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        rw [hx]; rfl
      have heq2 : padCells (padRemOf (len4 ib)) =
          padCells (padRemN x0 x1) := by
        rw [hx]; rfl
      rw [heq, heq2]; exact padlist_eval_scott x0 x1 x2 x3
    exact (LRed_app_right hli).trans h2
  have hpadD : LRed (.app padlistL (.app lenb4L (scottList (bm db))))
      (scottList (padCells (padRemOf (len4 db)))) := by
    obtain ⟨x0, x1, x2, x3, hx⟩ := exists_eq_of_length4 hld4
    have h2 : LRed (.app padlistL (scottList (bm (len4 db))))
        (scottList (padCells (padRemOf (len4 db)))) := by
      have heq : bm (len4 db) =
          [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        rw [hx]; rfl
      have heq2 : padCells (padRemOf (len4 db)) =
          padCells (padRemN x0 x1) := by
        rw [hx]; rfl
      rw [heq, heq2]; exact padlist_eval_scott x0 x1 x2 x3
    exact (LRed_app_right hld).trans h2
  -- ZEROFILL chunks
  have hZF58 : LRed (.app zerofillL nz58)
      (scottList (List.replicate 58 b0cT)) :=
    zerofill_num 58 nz58 nz58_num closed_nz58
  have hZF64 : LRed (.app zerofillL nz64)
      (scottList (List.replicate 64 b0cT)) :=
    zerofill_num 64 nz64 nz64_num closed_nz64
  have hZF112 : LRed (.app zerofillL nz112)
      (scottList (List.replicate 112 b0cT)) :=
    zerofill_num 112 nz112 nz112_num closed_nz112
  have hZF12 : LRed (.app zerofillL (churchL 12))
      (scottList (List.replicate 12 b0cT)) :=
    zerofill_num 12 (churchL 12) (churchL_num 12) (closed_churchL 12)
  -- the 53-chunk Forall₂
  have hForall : List.Forall₂ LRed
      (packChunksInst (scottList (bm tb)) (scottList (bm ib))
        (scottList (bm db)) (scottList (bm sb)))
      ((pack2Cells tb ib db sb).map scottList) := by
    simp only [packChunksInst, pack2Cells, List.map_cons, List.map_nil]
    repeat' (first | apply List.Forall₂.nil | apply List.Forall₂.cons)
    all_goals first
      | exact hZF58 | exact hZF64 | exact hZF112 | exact hZF12
      | exact hlt | exact hli | exact hld
      | exact htrawT | exact hirawT | exact hdrawT
      | exact hiptrT | exact hdptrT | exact hiddrT | exact himgT
      | exact hpadT | exact hpadI | exact hpadD
      | exact u64_eval_scott _
      | exact bytesChunk_nf _
      | exact Relation.ReflTransGen.refl
  -- chain collapse + join
  have hflat : ∀ e ∈ (pack2Cells tb ib db sb).flatten,
      closed 0 e = true := fun _ h => closed_pack2Cells_flat h
  have hcells : ∀ e ∈ (pack2Cells tb ib db sb).map scottList,
      closed 0 e = true := by
    intro e he
    obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp he
    exact closed_scottList (fun x hx =>
      hflat x (List.mem_flatten.mpr ⟨bs, hbs, hx⟩))
  have hchain : LRed (chunkChain (packChunksInst (scottList (bm tb))
        (scottList (bm ib)) (scottList (bm db)) (scottList (bm sb))))
      (scottList ((pack2Cells tb ib db sb).map scottList)) :=
    (conssChain_map_red hForall).trans (conssChain_nf _ hcells)
  exact ((pack2_open _ _ _ _ hscT hscI hscD hscS).trans
    (LRed_app_right hchain)).trans (join_eval _ hflat)

#print axioms pack2_open
#print axioms len4_length
#print axioms align512Bytes_length
#print axioms align4096Bytes_length
#print axioms foldl_const_step_map
#print axioms closed_pack2Cells_flat
#print axioms pack2_eval

-- ============================================================
-- Batch I: tuple-state iterate + MAP/NIBODD/NIBS2BYTES — the
-- leaves behind dataOf / idataOf (the packOf section builders).
-- ============================================================

/-- `subst` distributes over the `aps` spine. -/
theorem subst_aps (s : LTerm) : ∀ (xs : List LTerm) (e : LTerm),
    subst s 0 (aps e xs)
      = aps (subst s 0 e) (xs.map (subst s 0)) := by
  intro xs; induction xs with
  | nil => intro e; rfl
  | cons x xs ih =>
      intro e
      show subst s 0 (aps (.app e x) xs)
        = aps (subst s 0 e) ((subst s 0 x) :: xs.map (subst s 0))
      rw [ih]
      rfl

/-- `closed c` lifts over `app`. -/
theorem closed_app_c {c : Nat} {f x : LTerm}
    (hf : closed c f = true) (hx : closed c x = true) :
    closed c (.app f x) = true := by
  simp only [closed, Bool.and_eq_true]; exact ⟨hf, hx⟩

/-- `closed c` over an `aps` spine. -/
theorem closed_aps {c : Nat} : ∀ {f : LTerm} {xs : List LTerm},
    closed c f = true → (∀ e ∈ xs, closed c e = true) →
    closed c (aps f xs) = true := by
  intro f xs; induction xs generalizing f with
  | nil => intro hf _; exact hf
  | cons x xs ih =>
      intro hf hx
      show closed c (aps (.app f x) xs) = true
      exact ih (closed_app_c hf (hx x List.mem_cons_self))
        (fun e he => hx e (List.mem_cons_of_mem _ he))

/-- `_prs`/n-ary record: `λk. k x0 … xₙ₋₁` — the `_STEP` tuple
    encoding (`(λk2. k2 a b c …)`). -/
def tupleL (xs : List LTerm) : LTerm :=
  .abs (aps (.var 0) (xs.map (shift 1 0)))

/-- `tupleL xs · k →* k x0 … xₙ₋₁` — record destructure.  The
    `shift 1 0` hole is exactly cancelled by the beta `subst` —
    no closedness side-conditions. -/
theorem tupleL_apply (xs : List LTerm) (k : LTerm) :
    LRed (.app (tupleL xs) k) (aps k xs) := by
  apply LRed_of_hsteps (k := 1)
  show subst k 0 (aps (.var 0) (xs.map (shift 1 0))) = aps k xs
  rw [subst_aps]
  simp only [subst, shift, List.map_map]
  show aps (shift 0 0 k) (xs.map (subst k 0 ∘ shift 1 0)) = aps k xs
  rw [shift_zero]
  have hmap : xs.map (subst k 0 ∘ shift 1 0) = xs := by
    simp only [Function.comp_def, subst_shift_succ]
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, ih]
  rw [hmap]

/-- `tupleL xs` is closed when all entries are. -/
theorem closed_tupleL {xs : List LTerm}
    (h : ∀ e ∈ xs, closed 0 e = true) : closed 0 (tupleL xs) = true := by
  show closed 1 (aps (.var 0) (xs.map (shift 1 0))) = true
  apply closed_aps
  · rfl
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    rw [shift_of_closed0 (h x hx)]
    exact closed_mono (h x hx) (Nat.zero_le 1)

/-- `iterT` — semantic tuple-state iterate (metalevel). -/
def iterT (F : List LTerm → List LTerm) (s : List LTerm)
    : Nat → List LTerm
  | 0 => s
  | n + 1 => F (iterT F s n)

/-- iterate over a tuple-state: `iterL step (tupleL s) n →* tupleL
    (iterT F s n)` when `step·(tupleL s) →* tupleL (F s)` preserves
    the encoding invariant. -/
theorem iterTuple_red (step : LTerm) (F : List LTerm → List LTerm)
    (hstep : ∀ s, (∀ e ∈ s, closed 0 e = true) →
      LRed (.app step (tupleL s)) (tupleL (F s)) ∧
      (∀ e ∈ F s, closed 0 e = true)) :
    ∀ (n : Nat) (s : List LTerm), (∀ e ∈ s, closed 0 e = true) →
      LRed (iterL step (tupleL s) n) (tupleL (iterT F s n)) := by
  intro n; induction n with
  | zero => intro s _; exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro s hs
      have hclF : ∀ (m : Nat), ∀ e ∈ iterT F s m,
          closed 0 e = true := by
        intro m; induction m with
        | zero => exact hs
        | succ m ihm =>
            simp only [iterT]
            exact (hstep _ ihm).2
      show LRed (.app step (iterL step (tupleL s) n))
        (tupleL (iterT F s (n + 1)))
      have hmid : LRed (.app step (iterL step (tupleL s) n))
          (.app step (tupleL (iterT F s n))) :=
        LRed_app_right (ih s hs)
      exact hmid.trans (hstep _ (hclF n)).1

-- _NIBODD: nibble → bool (K at odd positions) --------------------------

/-- `_NIBODD = \a. a K (KI) K (KI) …` — 16-table, BT iff odd. -/
def niboddL : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun j : Fin 16 =>
    boolLit (decide (j.val % 2 = 1))))

theorem closed_niboddL : closed 0 niboddL = true := by decide

theorem nibodd_table : ∀ i : Fin 16,
    hsteps 24 (aps niboddL [nibLit i])
      = boolLit (decide (i.val % 2 = 1)) := by
  decide

theorem nibodd_eval (i : Fin 16) :
    LRed (aps niboddL [nibLit i]) (boolLit (decide (i.val % 2 = 1))) :=
  LRed_of_hsteps (nibodd_table i)

-- _MAP: lazy per-element map (self-application fixpoint) ---------------

/-- `MAP`'s step: `\h.\t. CONSS (f·h) t` — `f` kept at var-depth 2
    under the two binders. -/
def mapStepL (f : LTerm) : LTerm :=
  .abs (.abs (aps conssL [.app (shift 2 0 f) (.var 1), .var 0]))

/-- `_MAP = \f2. \l2. W·(fixrG (mapStep f2) nil)·l2`. -/
def mapL : LTerm :=
  .abs (.abs (fixrA (mapStepL (.var 1)) nilL (.var 0)))

theorem closed_mapStepL {f : LTerm} (hf : closed 0 f = true) :
    closed 0 (mapStepL f) = true := by
  show closed 2 (aps conssL
      [.app (shift 2 0 f) (.var 1), .var 0]) = true
  apply closed_aps
  · exact closed_mono closed_conssL (Nat.zero_le 2)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl|rfl <;>
      first
      | (exact closed_app_c (by
            rw [shift_of_closed0 hf]
            exact closed_mono hf (Nat.zero_le 2)) rfl)
      | rfl

theorem closed_mapL : closed 0 mapL = true := by decide

theorem closed_wl : closed 0 wl = true := by decide

/-- `fixrG` is closed when its step and nil-value are. -/
theorem closed_fixrG {st z : LTerm}
    (hs : closed 0 st = true) (hz : closed 0 z = true) :
    closed 0 (fixrG st z) = true := by
  show closed 2 (.app (.app (.var 0) (shift 2 0 z)) _) = true
  refine closed_app_c (closed_app_c rfl ?_) ?_
  · rw [shift_of_closed0 hz]; exact closed_mono hz (Nat.zero_le 2)
  · show closed 4 _ = true
    refine closed_app_c (closed_app_c ?_ rfl)
        (closed_app_c (closed_app_c rfl rfl) rfl)
    rw [shift_of_closed0 hs]; exact closed_mono hs (Nat.zero_le 4)

/-- `_MAP` on a Scott list: lazy per-element `f`-application,
    cells stay `f·c`-shaped (unreduced). -/
theorem map_eval (f l : LTerm) (cs : List LTerm)
    (hf : closed 0 f = true) (hl : closed 0 l = true)
    (hcl : ∀ e ∈ cs, closed 0 e = true)
    (hlcs : LRed l (scottList cs)) :
    LRed (aps mapL [f, l])
        (scottList (cs.map (fun c => .app f c))) := by
  have hst : ∀ e r, closed 0 e = true → closed 0 r = true →
      LRed (.app (.app (mapStepL f) e) r)
          (cellLit (.app f e) r) ∧
      closed 0 (cellLit (.app f e) r) = true := by
    intro e r he hr
    have hfe : closed 0 (.app f e) = true := closed_app hf he
    have hbeta : LRed (.app (.app (mapStepL f) e) r)
        (aps conssL [.app f e, r]) :=
      LRed_of_hsteps (k := 2) (by
        simp [mapStepL, aps, List.foldl, hsteps, hstep, subst, shift,
              shift_zero, subst_shift_succ,
              subst_of_closed0, shift_of_closed0, closed, closed_app,
              hf, he, hfe, closed_conssL])
    exact ⟨hbeta.trans (conss_nf _ _ hfe hr),
      closed_cellLit hfe hr⟩
  have hopen : LRed (aps mapL [f, l])
      (fixrA (mapStepL f) nilL l) :=
    LRed_of_hsteps (k := 2) (by
      unfold mapL fixrA fixrG wl mapStepL
      simp [aps, List.foldl, hsteps, hstep, subst, shift,
            shift_zero, subst_shift_succ,
            subst_of_closed0 hf, shift_of_closed0 hf,
            subst_of_closed0 closed_conssL, shift_of_closed0 closed_conssL,
            subst_of_closed0 closed_nilL, shift_of_closed0 closed_nilL,
            subst_of_closed0 closed_wl, shift_of_closed0 closed_wl])
  have hmain := fixr_eval (mapStepL f) nilL _ (closed_mapStepL hf)
    closed_nilL hst l cs hl hlcs hcl
  have hconv : cs.foldr (fun e r => cellLit (.app f e) r) nilL
      = scottList (cs.map (fun c => .app f c)) := by
    simp only [scottList, List.foldr_map]
  exact hopen.trans (hconv ▸ hmain)

-- _NIBS2BYTES: pairwise fold over nibble list ---------------------------

/-- Worker `\g.\l2. l2 K (\hi.\t. t K (\lo.\t2.
    conss (PAIR lo hi) (g g t2)))` — pops `hi` first, then `lo` off the
    tail, emits `PAIR lo hi`.  Odd trailing nibble hits `t = nil` and
    is dropped. -/
def nibs2G : LTerm :=
  .abs (.abs (.app (.app (.var 0) nilL)
    (.abs (.abs (.app (.app (.var 0) nilL)
      (.abs (.abs (.app
        (.app conssL (.app (.app pairSrcL (.var 1)) (.var 3)))
        (.app (.app (.var 5) (.var 5)) (.var 0))))))))))

/-- `_NIBS2BYTES = \l. ((\f. f f) nibs2G) l`. -/
def nibs2bytesL : LTerm := .abs (.app (.app wl nibs2G) (.var 0))

theorem closed_nibs2G : closed 0 nibs2G = true := by decide

theorem closed_nibs2bytesL : closed 0 nibs2bytesL = true := by decide

/-- `(G·G)·cellLit hi (cellLit lo t)` consumes the pair and re-arms.
    Count verified on closed literals below. -/
example :
    hsteps 10 (.app (.app nibs2G nibs2G)
        (cellLit (nibLit 0) (cellLit (nibLit 1) nilL)))
      = .app (.app conssL
          (.app (.app pairSrcL (nibLit 1)) (nibLit 0)))
          (.app (.app nibs2G nibs2G) nilL) := by decide

/-- `(G·G)·nilL →* nilL`: empty input. -/
theorem nibs2_nil : hsteps 5 (.app (.app nibs2G nibs2G) nilL) = nilL := by
  decide

/-- `(G·G)·cellLit a nil →* nilL`: odd trailing nibble dropped. -/
theorem nibs2_single (a : LTerm) :
    hsteps 8 (.app (.app nibs2G nibs2G) (cellLit a nilL)) = nilL := by
  unfold nibs2G cellLit nilL
  simp [hsteps, hstep, subst, shift, shift_zero]

/-- General pair-step with closedness erasure for symbolic payloads. -/
theorem nibs2_step (hi lo t : LTerm)
    (hhi : closed 0 hi = true) (hlo : closed 0 lo = true)
    (ht : closed 0 t = true) :
    LRed (.app (.app nibs2G nibs2G)
        (cellLit hi (cellLit lo t)))
      (.app (.app conssL (.app (.app pairSrcL lo) hi))
        (.app (.app nibs2G nibs2G) t)) :=
  LRed_of_hsteps (k := 10) (by
    unfold nibs2G cellLit nilL
    simp [hsteps, hstep, subst, shift, shift_zero,
          subst_of_closed0 hhi, shift_of_closed0 hhi,
          subst_of_closed0 hlo, shift_of_closed0 hlo,
          subst_of_closed0 ht, shift_of_closed0 ht,
          subst_of_closed0 closed_pairSrcL,
          shift_of_closed0 closed_pairSrcL,
          subst_of_closed0 closed_conssL,
          shift_of_closed0 closed_conssL])

/-- Two-element fold over a list (pairs consumed left-to-right). -/
def foldr2 (σ : LTerm → LTerm → LTerm → LTerm) (z : LTerm) :
    List LTerm → LTerm
  | [] => z
  | [_] => z
  | hi :: lo :: t => σ hi lo (foldr2 σ z t)

/-- Phase 1: the worker spine unpacks pairs into `conss`-applications;
    the `(G·G)·scott t` tail sits at app-argument depth so
    `LRed_app_right` congruence folds in the induction hypothesis. -/
theorem nibs2_run : ∀ (cs : List LTerm),
    (∀ e ∈ cs, closed 0 e = true) →
    LRed (.app (.app nibs2G nibs2G) (scottList cs))
        (foldr2 (fun hi lo r =>
          .app (.app conssL (.app (.app pairSrcL lo) hi)) r)
          nilL cs) := by
  intro cs; induction cs using foldr2.induct with
  | case1 =>
      intro _; exact LRed_of_hsteps nibs2_nil
  | case2 a =>
      intro _
      simp only [foldr2]
      simp only [scottList, List.foldr_cons, List.foldr_nil]
      exact LRed_of_hsteps (nibs2_single a)
  | case3 hi lo t ih =>
      intro hcl
      have hhi : closed 0 hi = true := hcl hi List.mem_cons_self
      have hlo : closed 0 lo = true :=
        hcl lo (List.mem_cons_of_mem hi List.mem_cons_self)
      have htail : ∀ e ∈ t, closed 0 e = true :=
        fun e he => hcl e
          (List.mem_cons_of_mem hi (List.mem_cons_of_mem lo he))
      have hstep : LRed
          (.app (.app nibs2G nibs2G)
            (cellLit hi (cellLit lo (scottList t))))
          (.app (.app conssL (.app (.app pairSrcL lo) hi))
            (.app (.app nibs2G nibs2G) (scottList t))) :=
        nibs2_step hi lo (scottList t) hhi hlo (closed_scottList htail)
      simp only [scottList, List.foldr_cons, foldr2]
      exact hstep.trans (LRed_app_right (ih htail))

/-- Pair-wise semantic cell list: `hi::lo::t ↦ PAIR lo hi`. -/
def nibPairUp : List LTerm → List LTerm
  | [] => []
  | [_] => []
  | hi :: lo :: t => .app (.app pairSrcL lo) hi :: nibPairUp t

/-- `foldr2` preserves closedness. -/
theorem closed_foldr2 (σ : LTerm → LTerm → LTerm → LTerm) (z : LTerm)
    (hz : closed 0 z = true)
    (hσ : ∀ a b r, closed 0 a = true → closed 0 b = true →
      closed 0 r = true → closed 0 (σ a b r) = true) :
    ∀ (cs : List LTerm), (∀ e ∈ cs, closed 0 e = true) →
      closed 0 (foldr2 σ z cs) = true := by
  intro cs; induction cs using foldr2.induct with
  | case1 | case2 => intro _; exact hz
  | case3 a b t ih =>
      intro hcl
      simp only [foldr2]
      exact hσ a b _ (hcl a List.mem_cons_self)
        (hcl b (List.mem_cons_of_mem a List.mem_cons_self))
        (ih (fun e he => hcl e
          (List.mem_cons_of_mem a (List.mem_cons_of_mem b he))))

/-- Phase 2: pointwise `conss`-normalization — each `conss·p·r`
    collapses to `cellLit p r`. -/
theorem nibs2_foldr_red : ∀ (cs : List LTerm),
    (∀ e ∈ cs, closed 0 e = true) →
    LRed (foldr2 (fun hi lo r =>
            .app (.app conssL (.app (.app pairSrcL lo) hi)) r)
          nilL cs)
        (foldr2 (fun hi lo r =>
          cellLit (.app (.app pairSrcL lo) hi) r) nilL cs) := by
  intro cs; induction cs using foldr2.induct with
  | case1 | case2 => intro _; exact Relation.ReflTransGen.refl
  | case3 hi lo t ih =>
      intro hcl
      have hhi : closed 0 hi = true := hcl hi List.mem_cons_self
      have hlo : closed 0 lo = true :=
        hcl lo (List.mem_cons_of_mem hi List.mem_cons_self)
      have htail : ∀ e ∈ t, closed 0 e = true :=
        fun e he => hcl e
          (List.mem_cons_of_mem hi (List.mem_cons_of_mem lo he))
      have hpair : closed 0 (.app (.app pairSrcL lo) hi) = true :=
        closed_app (closed_app closed_pairSrcL hlo) hhi
      have hfold : closed 0 (foldr2 (fun hi lo r =>
            cellLit (.app (.app pairSrcL lo) hi) r) nilL t) = true :=
        closed_foldr2 _ _ closed_nilL (fun a b r ha hb hr =>
          closed_cellLit (closed_app (closed_app closed_pairSrcL hb)
            ha) hr) t htail
      simp only [foldr2]
      exact (LRed_app_right (ih htail)).trans
        (conss_nf _ _ hpair hfold)

/-- `foldr2` of `cellLit`-cells is the `scottList` of `nibPairUp`. -/
theorem nibPairUp_scott : ∀ (cs : List LTerm),
    foldr2 (fun hi lo r =>
        cellLit (.app (.app pairSrcL lo) hi) r) nilL cs
      = scottList (nibPairUp cs) := by
  intro cs; induction cs using nibPairUp.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 hi lo t ih =>
      simp only [foldr2, nibPairUp, scottList, List.foldr_cons]
      exact congrArg (cellLit _) ih

/-- `_NIBS2BYTES·scott(cs) →* scottList (nibPairUp cs)`. -/
theorem nibs2bytes_eval (cs : List LTerm)
    (hcl : ∀ e ∈ cs, closed 0 e = true) :
    LRed (.app nibs2bytesL (scottList cs))
        (scottList (nibPairUp cs)) := by
  have hGG : closed 0 (.app nibs2G nibs2G) = true :=
    closed_app closed_nibs2G closed_nibs2G
  have hopen : LRed (.app nibs2bytesL (scottList cs))
      (.app (.app nibs2G nibs2G) (scottList cs)) :=
    LRed_of_hsteps (k := 2) (by
      unfold nibs2bytesL nibs2G wl
      simp [hsteps, hstep, subst, shift, shift_zero,
            subst_of_closed0 closed_conssL,
            shift_of_closed0 closed_conssL,
            subst_of_closed0 closed_pairSrcL,
            shift_of_closed0 closed_pairSrcL,
            subst_of_closed0 closed_nilL,
            shift_of_closed0 closed_nilL])
  rw [← nibPairUp_scott cs]
  exact hopen.trans ((nibs2_run cs hcl).trans
    (nibs2_foldr_red cs hcl))

-- batch I axiom audit ---------------------------------------------------

#print axioms tupleL_apply
#print axioms iterTuple_red
#print axioms nibodd_eval
#print axioms map_eval
#print axioms nibs2_step
#print axioms nibs2_run
#print axioms nibs2bytes_eval


-- ============================================================
-- Batch J: dataOf / idataOf — section builders over tuple-state
--   iterates (STEP_D, STEP_ID), projections, NIBS2BYTES names.
-- ============================================================
-- _STEP_D / dataOf ------------------------------------------------------

/-- `\l2. conss B0C l2` — the zero-grow step iterated by the slot's
    size numeral. -/
def consB0L : LTerm := .abs (.app (.app conssL b0cT) (.var 0))

theorem closed_consB0L : closed 0 consB0L = true := by decide

/-- `\k2. k2 t (B4ADD o szb) (conss (PAIR nm o) u) (szn consB0 z)` —
    the STEP_D success continuation.  Binder ctx in the source:
    `[k2, r3, szb, r2, szn, r1, nm, t, p, z, u, o, l, acc]`. -/
def stepDK3 : LTerm :=
  .abs (.abs (.abs (aps (.var 0)
    [.var 7,
     .app (.app b4addL (.var 11)) (.var 2),
     .app (.app conssL
       (.app (.app pairSrcL (.var 6)) (.var 11))) (.var 10),
     .app (.app (.var 4) consB0L) (.var 9)])))

/-- `\szn.\r2. r2 N3 K3`.  Binder ctx `[r2, szn, r1, nm, t, p, z, u, o, l,
    acc]` — `N3 = tupleL [t,o,u,z]` at `[4,8,7,6]`. -/
def stepDK2 : LTerm :=
  .abs (.abs (.app (.app (.var 0)
    (tupleL [.var 4, .var 8, .var 7, .var 6])) stepDK3))

/-- `\nm.\r1. r1 N2 K2`.  Binder ctx `[r1, nm, t, p, z, u, o, l, acc]`. -/
def stepDK1 : LTerm :=
  .abs (.abs (.app (.app (.var 0)
    (tupleL [.var 2, .var 6, .var 5, .var 4])) stepDK2))

/-- `\p.\t. p N1 K1`.  Binder ctx `[t, p, z, u, o, l, acc]`. -/
def stepDC : LTerm :=
  .abs (.abs (.app (.app (.var 1)
    (tupleL [.var 0, .var 4, .var 3, .var 2])) stepDK1))

/-- `\l.\o.\u.\z. l N0 C`.  Binder ctx `[z, u, o, l, acc]`. -/
def stepDSel : LTerm :=
  .abs (.abs (.abs (.abs (.app (.app (.var 3)
    (tupleL [.var 3, .var 2, .var 1, .var 0])) stepDC))))

/-- `_STEP_D = \acc. acc SEL`. -/
def dataStepL : LTerm := .abs (.app (.var 0) stepDSel)

theorem closed_dataStepL : closed 0 dataStepL = true := by decide

/-- empirical: pair-step count on closed literals -/
example :
    hsteps 22 (.app dataStepL
        (tupleL [cellLit (cellLit nilL
                  (cellLit nilL (cellLit nilL nilL)))
                nilL,
                 nilL, nilL, nilL]))
      = tupleL [nilL,
          .app (.app b4addL nilL) nilL,
          .app (.app conssL
            (.app (.app pairSrcL nilL) nilL)) nilL,
          .app (.app nilL consB0L) nilL] := by decide
/-- STEP_D on a cons-slot: `(E::T, o,u,z) ↦ (T, B4ADD o szb,
    CONSS (PAIR nm o) u, szn consB0 z)` — 22-step milestone
    (count verified empirically on closed literals above). -/
theorem dataStep_cons (nm szn szb T o u z : LTerm)
    (hnm : closed 0 nm = true) (hszn : closed 0 szn = true)
    (hszb : closed 0 szb = true) (hT : closed 0 T = true)
    (ho : closed 0 o = true) (hu : closed 0 u = true)
    (hz : closed 0 z = true) :
    LRed (.app dataStepL
        (tupleL [cellLit
            (cellLit nm (cellLit szn (cellLit szb nilL))) T,
          o, u, z]))
      (tupleL [T, .app (.app b4addL o) szb,
        .app (.app conssL (.app (.app pairSrcL nm) o)) u,
        .app (.app szn consB0L) z]) :=
  LRed_of_hsteps (k := 22) (by
    simp [dataStepL, stepDSel, stepDC, stepDK1, stepDK2, stepDK3,
          tupleL, cellLit, aps, List.foldl, List.map,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_cellLit, closed_tupleL,
          closed_b4addL, closed_conssL, closed_pairSrcL,
          closed_consB0L, closed_b0cT, closed_nilL,
          hnm, hszn, hszb, hT, ho, hu, hz])

/-- empirical: nil-step count on closed literals -/
example :
    hsteps 8 (.app dataStepL (tupleL [nilL, nilL, nilL, nilL]))
      = tupleL [nilL, nilL, nilL, nilL] := by decide

/-- STEP_D on the empty slot list is the identity on the tuple. -/
theorem dataStep_nil (o u z : LTerm)
    (ho : closed 0 o = true) (hu : closed 0 u = true)
    (hz : closed 0 z = true) :
    LRed (.app dataStepL (tupleL [nilL, o, u, z]))
        (tupleL [nilL, o, u, z]) :=
  LRed_of_hsteps (k := 8) (by
    simp [dataStepL, stepDSel, stepDC, stepDK1, stepDK2, stepDK3,
          consB0L, tupleL, cellLit, nilL, aps, List.foldl, List.map,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_cellLit, closed_tupleL,
          closed_b4addL, closed_conssL, closed_pairSrcL,
          closed_consB0L, closed_nilL, ho, hu, hz])

/-- Slot encoding: `[nm, szn, szb]` — a 3-element Scott list. -/
def slotEnc (e : LTerm × LTerm × LTerm) : LTerm :=
  scottList [e.1, e.2.1, e.2.2]

theorem closed_slotEnc {e : LTerm × LTerm × LTerm}
    (h1 : closed 0 e.1 = true) (h2 : closed 0 e.2.1 = true)
    (h3 : closed 0 e.2.2 = true) :
    closed 0 (slotEnc e) = true := by
  unfold slotEnc scottList
  simp only [List.foldr_cons, List.foldr_nil]
  exact closed_cellLit h1 (closed_cellLit h2
    (closed_cellLit h3 closed_nilL))

/-- Semantic STEP_D on the `(off, syms, zeros)` triple. -/
def dataStepSem (st : LTerm × LTerm × LTerm)
    (e : LTerm × LTerm × LTerm) : LTerm × LTerm × LTerm :=
  (.app (.app b4addL st.1) e.2.2,
   .app (.app conssL (.app (.app pairSrcL e.1) st.1)) st.2.1,
   .app (.app e.2.1 consB0L) st.2.2)

/-- dataOf state after k steps: `l`-slot = remaining slots,
    `(o,u,z)` = `dataStepSem`-fold over the consumed prefix. -/
def dataAfterK (k : Nat) (es : List (LTerm × LTerm × LTerm))
    (o u z : LTerm) : List LTerm :=
  let st := (es.take k).foldl dataStepSem (o, u, z)
  [scottList ((es.drop k).map slotEnc), st.1, st.2.1, st.2.2]

/-- Semantic fixed point: full fold over the slot list. -/
def dataFinal (es : List (LTerm × LTerm × LTerm))
    : LTerm × LTerm × LTerm :=
  es.foldl dataStepSem (bytesChunk b3000, nilL, nilL)

/-- `dataStepSem` preserves component closedness. -/
theorem closed_dataStepSem {st e : LTerm × LTerm × LTerm}
    (ho : closed 0 st.1 = true) (hu : closed 0 st.2.1 = true)
    (hz : closed 0 st.2.2 = true)
    (h1 : closed 0 e.1 = true) (h2 : closed 0 e.2.1 = true)
    (h3 : closed 0 e.2.2 = true) :
    closed 0 (dataStepSem st e).1 = true ∧
    closed 0 (dataStepSem st e).2.1 = true ∧
    closed 0 (dataStepSem st e).2.2 = true := by
  unfold dataStepSem
  exact ⟨closed_app (closed_app closed_b4addL ho) h3,
         closed_app (closed_app closed_conssL
           (closed_app (closed_app closed_pairSrcL h1) ho)) hu,
         closed_app (closed_app h2 closed_consB0L) hz⟩

/-- `dataStepSem`-fold over a closed prefix stays closed. -/
theorem closed_dataAfterK {k : Nat} {es : List (LTerm×LTerm×LTerm)}
    {o u z : LTerm}
    (hcl : ∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.1 = true
        ∧ closed 0 e.2.2 = true)
    (ho : closed 0 o = true) (hu : closed 0 u = true)
    (hz : closed 0 z = true) :
    closed 0 ((es.take k).foldl dataStepSem (o,u,z)).1 = true ∧
    closed 0 ((es.take k).foldl dataStepSem (o,u,z)).2.1 = true ∧
    closed 0 ((es.take k).foldl dataStepSem (o,u,z)).2.2 = true := by
  have hfold : ∀ (pref : List (LTerm×LTerm×LTerm)) (o u z : LTerm),
      closed 0 o = true → closed 0 u = true → closed 0 z = true →
      (∀ e ∈ pref, closed 0 e.1 = true ∧ closed 0 e.2.1 = true
          ∧ closed 0 e.2.2 = true) →
      closed 0 (pref.foldl dataStepSem (o,u,z)).1 = true ∧
      closed 0 (pref.foldl dataStepSem (o,u,z)).2.1 = true ∧
      closed 0 (pref.foldl dataStepSem (o,u,z)).2.2 = true := by
    intro pref
    induction pref with
    | nil => intro _ _ _ ho' hu' hz' _; exact ⟨ho', hu', hz'⟩
    | cons a t ihp =>
        intro o u z ho' hu' hz' hp
        have ha := hp a List.mem_cons_self
        have hstep := closed_dataStepSem (st := (o, u, z)) (e := a)
          ho' hu' hz' ha.1 ha.2.1 ha.2.2
        simp only [List.foldl_cons]
        exact ihp _ _ _ hstep.1 hstep.2.1 hstep.2.2
          (fun e he => hp e (List.mem_cons_of_mem a he))
  exact hfold (es.take k) o u z ho hu hz
    (fun e he => hcl e (List.mem_of_mem_take he))

/-- Tuple-state iterate for STEP_D: after k steps the state is
    `dataAfterK k`.  Bespoke induction on the meta-level slot list —
    `iterTuple_red`'s `F` cannot destructure the Scott-encoded
    element at term level without an unshift oracle. -/
theorem dataOf_iterK : ∀ (k : Nat)
    (es : List (LTerm × LTerm × LTerm)) (o u z : LTerm),
    k ≤ es.length →
    (∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.1 = true
        ∧ closed 0 e.2.2 = true) →
    closed 0 o = true → closed 0 u = true → closed 0 z = true →
    LRed (iterL dataStepL (tupleL (dataAfterK 0 es o u z)) k)
        (tupleL (dataAfterK k es o u z)) := by
  intro k es o u z
  induction k with
  | zero => intro _ _ _ _ _; exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro hk hcl ho hu hz
      have hlt : k < es.length := hk
      show LRed (.app dataStepL
          (iterL dataStepL (tupleL (dataAfterK 0 es o u z)) k))
        (tupleL (dataAfterK (k+1) es o u z))
      have hmid := LRed_app_right (f := dataStepL)
        (ih (Nat.le_of_succ_le hk) hcl ho hu hz)
      -- unfold afterK k into the cons-cell shape dataStep_cons needs
      have hdrop : es.drop k = es[k] :: es.drop (k+1) :=
        (List.getElem_cons_drop (as := es) hlt).symm
      have hstep1 : LRed
          (.app dataStepL (tupleL (dataAfterK k es o u z)))
          (tupleL (dataAfterK (k+1) es o u z)) := by
        have hk1 : dataAfterK k es o u z =
            [cellLit (cellLit es[k].1
                (cellLit es[k].2.1 (cellLit es[k].2.2 nilL)))
              (scottList ((es.drop (k+1)).map slotEnc)),
             ((es.take k).foldl dataStepSem (o,u,z)).1,
             ((es.take k).foldl dataStepSem (o,u,z)).2.1,
             ((es.take k).foldl dataStepSem (o,u,z)).2.2] := by
          unfold dataAfterK
          simp only [hdrop, List.map_cons, scottList, slotEnc,
            List.foldr_cons, List.foldr_nil]
        have hk2 : dataAfterK (k+1) es o u z =
            [scottList ((es.drop (k+1)).map slotEnc),
             .app (.app b4addL
               ((es.take k).foldl dataStepSem (o,u,z)).1) es[k].2.2,
             .app (.app conssL
               (.app (.app pairSrcL es[k].1)
                 ((es.take k).foldl dataStepSem (o,u,z)).1))
               ((es.take k).foldl dataStepSem (o,u,z)).2.1,
             .app (.app es[k].2.1 consB0L)
               ((es.take k).foldl dataStepSem (o,u,z)).2.2] := by
          unfold dataAfterK
          rw [List.take_add_one, List.getElem?_eq_getElem hlt]
          simp only [Option.toList_some, List.foldl_append,
            List.foldl_cons, List.foldl_nil, dataStepSem]
        rw [hk1, hk2]
        obtain ⟨h1, h2, h3⟩ := hcl es[k] (List.getElem_mem hlt)
        have hT : closed 0 (scottList ((es.drop (k+1)).map slotEnc))
            = true := by
          apply closed_scottList
          intro x hx
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
          obtain ⟨h1', h2', h3'⟩ := hcl e' (List.mem_of_mem_drop he')
          exact closed_slotEnc h1' h2' h3'
        obtain ⟨ho', hu', hz'⟩ := closed_dataAfterK
          (k := k) (es := es) (o := o) (u := u) (z := z)
          hcl ho hu hz
        exact dataStep_cons es[k].1 es[k].2.1 es[k].2.2
          (scottList ((es.drop (k+1)).map slotEnc))
          ((es.take k).foldl dataStepSem (o,u,z)).1
          ((es.take k).foldl dataStepSem (o,u,z)).2.1
          ((es.take k).foldl dataStepSem (o,u,z)).2.2
          h1 h2 h3 hT ho' hu' hz'
      exact hmid.trans hstep1

/-- `\l.\o.\u.\z.\f. f z u` — the `_prs z u` finalizer:
    `PRS z u = \f6. f6 z u` under 4 state binders. -/
def dataFinL : LTerm :=
  .abs (.abs (.abs (.abs
    (.abs (.app (.app (.var 0) (.var 1)) (.var 2))))))

theorem closed_dataFinL : closed 0 dataFinL = true := by decide

/-- `dataFinL·l·o·u·z →* pairLit z u` — the 4-beta projection. -/
theorem dataFin_eval (l o u z : LTerm)
    (ho : closed 0 o = true) (hu : closed 0 u = true)
    (hz : closed 0 z = true) :
    LRed (aps dataFinL [l, o, u, z]) (pairLit z u) :=
  LRed_of_hsteps (k := 4) (by
    simp [dataFinL, pairLit, aps, List.foldl,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          ho, hu, hz])

/-- `data_src n = \slots. (church n · STEP_D · init) FIN`
    with `init = tupleL [slots, b4 0x3000, K, K]`. -/
def dataOfL (n : Nat) : LTerm :=
  .abs (.app
    (.app (.app (churchL n) dataStepL)
      (tupleL [.var 0, bytesChunk b3000, nilL, nilL]))
    dataFinL)

theorem closed_dataOfL (n : Nat) : closed 0 (dataOfL n) = true := by
  unfold dataOfL
  simp only [closed, Bool.and_eq_true]
  refine ⟨⟨⟨closed_mono (closed_churchL n) (Nat.zero_le 1),
      closed_mono closed_dataStepL (Nat.zero_le 1)⟩, ?_⟩,
    closed_mono closed_dataFinL (Nat.zero_le 1)⟩
  show closed 2 (aps (.var 0)
      ([.var 0, bytesChunk b3000, nilL, nilL].map
        (shift 1 0))) = true
  apply closed_aps
  · rfl
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    simp only [List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · decide
    · rw [shift_of_closed0 (closed_bytesChunk b3000)]
      exact closed_mono (closed_bytesChunk b3000) (Nat.zero_le 2)
    · rw [shift_of_closed0 closed_nilL]
      exact closed_mono closed_nilL (Nat.zero_le 2)
    · rw [shift_of_closed0 closed_nilL]
      exact closed_mono closed_nilL (Nat.zero_le 2)

/-- `dataOf` evaluation: iterate STEP_D over the slot list, then
    project `(z, u)` — the zero-byte list and the `(nm, off)` symbol
    table. -/
theorem dataOf_eval (es : List (LTerm × LTerm × LTerm))
    (hcl : ∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.1 = true
        ∧ closed 0 e.2.2 = true) :
    LRed (.app (dataOfL es.length) (scottList (es.map slotEnc)))
      (pairLit (dataFinal es).2.2 (dataFinal es).2.1) := by
  have hclosedS : closed 0 (scottList (es.map slotEnc)) = true := by
    apply closed_scottList
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2, h3⟩ := hcl e' he'
    exact closed_slotEnc h1 h2 h3
  have hinit : closed 0 (tupleL [scottList (es.map slotEnc),
      bytesChunk b3000, nilL, nilL]) = true :=
    closed_tupleL (fun e he => by
      simp only [List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact hclosedS
      · exact closed_bytesChunk b3000
      · exact closed_nilL
      · exact closed_nilL)
  -- 1 beta: open dataOfL, instantiating `slots`
  have hopen : LRed
      (.app (dataOfL es.length) (scottList (es.map slotEnc)))
      (.app
        (.app (.app (churchL es.length) dataStepL)
          (tupleL [scottList (es.map slotEnc),
                   bytesChunk b3000, nilL, nilL]))
        dataFinL) :=
    LRed_of_hsteps (k := 1) (by
      simp [dataOfL, tupleL, aps, List.foldl, List.map,
            hsteps, hstep, subst, shift, shift_zero,
            subst_shift_succ,
            subst_of_closed0, shift_of_closed0, closed, closed_app,
            closed_churchL, closed_dataStepL, closed_dataFinL,
            closed_bytesChunk, closed_nilL, hclosedS])
  -- Church iterate → tuple-state iterate → final tuple
  have hiter : LRed
      (.app (.app (churchL es.length) dataStepL)
        (tupleL [scottList (es.map slotEnc),
                 bytesChunk b3000, nilL, nilL]))
      (iterL dataStepL
        (tupleL [scottList (es.map slotEnc),
                 bytesChunk b3000, nilL, nilL]) es.length) :=
    church_eval es.length dataStepL _ closed_dataStepL hinit
  have hrun : LRed
      (iterL dataStepL
        (tupleL [scottList (es.map slotEnc),
                 bytesChunk b3000, nilL, nilL]) es.length)
      (tupleL [nilL, (dataFinal es).1, (dataFinal es).2.1,
               (dataFinal es).2.2]) := by
    have h := dataOf_iterK es.length es
      (bytesChunk b3000) nilL nilL (Nat.le_refl _) hcl
      (closed_bytesChunk b3000) closed_nilL closed_nilL
    have h0 : dataAfterK 0 es (bytesChunk b3000) nilL nilL =
        [scottList (es.map slotEnc),
         bytesChunk b3000, nilL, nilL] := by
      simp only [dataAfterK, List.take_zero, List.drop_zero,
        List.foldl_nil]
    have hn : dataAfterK es.length es (bytesChunk b3000) nilL nilL =
        [nilL, (dataFinal es).1, (dataFinal es).2.1,
         (dataFinal es).2.2] := by
      simp only [dataAfterK, dataFinal, List.take_length,
        List.drop_length, List.map_nil, scottList, List.foldr_nil]
    rwa [h0, hn] at h
  -- finalizer: tupleL·FIN → aps → pairLit z u
  have hfin : LRed
      (.app (tupleL [nilL, (dataFinal es).1, (dataFinal es).2.1,
                     (dataFinal es).2.2])
        dataFinL)
      (pairLit (dataFinal es).2.2 (dataFinal es).2.1) := by
    have h := tupleL_apply [nilL, (dataFinal es).1,
      (dataFinal es).2.1, (dataFinal es).2.2] dataFinL
    have hf := closed_dataAfterK (k := es.length) (es := es)
      (o := bytesChunk b3000) (u := nilL) (z := nilL) hcl
      (closed_bytesChunk b3000) closed_nilL closed_nilL
    have hf' : closed 0 (dataFinal es).1 = true ∧
        closed 0 (dataFinal es).2.1 = true ∧
        closed 0 (dataFinal es).2.2 = true := by
      have heq : es.take es.length = es := List.take_length
      rw [heq] at hf
      exact hf
    exact h.trans (dataFin_eval nilL _ _ _
      hf'.1 hf'.2.1 hf'.2.2)
  exact hopen.trans ((LRed_app_left
      (hiter.trans hrun)).trans hfin)

-- _STEP_ID / idataOf -------------------------------------------------------

/-- "iat_" nibble prefix consed onto a name — 'i'=0x69, 'a'=0x61,
    't'=0x74, '_'=0x5f, low nibble first per byte. -/
def iatPrefix (nm : LTerm) : LTerm :=
  .app (.app conssL (nibLit 9))
    (.app (.app conssL (nibLit 6))
      (.app (.app conssL (nibLit 1))
        (.app (.app conssL (nibLit 6))
          (.app (.app conssL (nibLit 4))
            (.app (.app conssL (nibLit 7))
              (.app (.app conssL (nibLit 15))
                (.app (.app conssL (nibLit 5)) nm)))))))

theorem closed_iatPrefix {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (iatPrefix nm) = true := by
  unfold iatPrefix
  repeat (first | exact closed_app (closed_app closed_conssL
    (closed_nibLit _)) h)

/-- `<B 0x0008>` — the IAT stride. -/
def b8 : List (Fin 16 × Fin 16) := [(8,0),(0,0),(0,0),(0,0)]

/-- `<B 0x0000>` — record padding bytes. -/
def bz1 : List (Fin 16 × Fin 16) := [(0,0)]

/-- `<B 0x0000 0x0000>` — record head bytes. -/
def bz2 : List (Fin 16 × Fin 16) := [(0,0),(0,0)]

-- `<B 0x00×8>` — ILT/IAT null terminator: reuse `bZero8`.

/-- "kernel32.dll\x00" bytes (lo,hi nibble pairs). -/
def bKernel : List (Fin 16 × Fin 16) :=
  [(11,6),(5,6),(2,7),(14,6),(5,6),(12,6),(3,3),(2,3),(14,2),
   (4,6),(12,6),(12,6),(0,0)]

/-- `<B 0x2028>` — IDT original-first-thunk field. -/
def b2028 : List (Fin 16 × Fin 16) := [(8,2),(0,2),(0,0),(0,0)]

-- semantic step constructors (the let-values, as app-terms) ---------------

/-- `NIBS2BYTES·nm`. -/
def idNmb (nm : LTerm) : LTerm := .app nibs2bytesL nm

/-- `JOIN [bytes(00,00), nmb, bytes(00)]`. -/
def idBrec (nm : LTerm) : LTerm :=
  .app joinL (scottList
    [bytesChunk bz2, idNmb nm, bytesChunk bz1])

/-- `LENB4·brec`. -/
def idRln (nm : LTerm) : LTerm := .app lenb4L (idBrec nm)

/-- `λb0. λt0. b0 (λbl. λbh. NIBODD bl)` — the `_peel` continuation:
    destructures LENB4's first byte, applies NIBODD to its lo nibble. -/
def idOddK : LTerm :=
  .abs (.abs (.app (.var 1)
    (.abs (.abs (.app niboddL (.var 1))))))

theorem closed_idOddK : closed 0 idOddK = true := by decide

/-- `peel rln [b0] (b0·λbl.λbh. NIBODD·bl)`. -/
def idOdd (nm : LTerm) : LTerm :=
  .app (.app (idRln nm) nilL) idOddK

/-- `odd (APPEND brec 00) brec` — conditional pad. -/
def idRec (nm : LTerm) : LTerm :=
  .app (.app (idOdd nm)
    (.app (.app appendL (idBrec nm)) (bytesChunk bz1)))
    (idBrec nm)

/-- `LENB4·rec`. -/
def idRl2 (nm : LTerm) : LTerm := .app lenb4L (idRec nm)

/-- `B4ADD (b4 0x2000) o` — hint/name RVA. -/
def idHrv (o : LTerm) : LTerm :=
  .app (.app b4addL (bytesChunk b2000)) o

-- _STEP_ID term -----------------------------------------------------------

/-- `\k2. k2 t (B4ADD o rl2) (B4ADD oi 8) (conss hrv rv)
    (conss rec rc) (conss (PAIR (iat_ nm) oi) sy)` —
    binder ctx [k2,hrv,rl2,rec,odd,rln,brec,nmb,t,nm,sy,rc,rv,oi,o,l]. -/
def idK2Body : LTerm :=
  .abs (aps (.var 0)
    [.var 8,
     .app (.app b4addL (.var 14)) (.var 2),
     .app (.app b4addL (.var 13)) (bytesChunk b8),
     .app (.app conssL (.var 1)) (.var 12),
     .app (.app conssL (.var 3)) (.var 11),
     .app (.app conssL
       (.app (.app pairSrcL (iatPrefix (.var 9))) (.var 13)))
       (.var 10)])

/-- `λnm. λt.` + the 7-let chain.  Binder ctx inside the lets:
    `[nmb,t,nm,sy,rc,rv,oi,o,l]` growing per let. -/
def idStepC : LTerm :=
  .abs (.abs
    (.app (.abs
      (.app (.abs
        (.app (.abs
          (.app (.abs
            (.app (.abs
              (.app (.abs
                (.app (.abs idK2Body)
                  (.app (.app b4addL (bytesChunk b2000))
                    (.var 12))))
                (.app lenb4L (.var 0))))
              (.app (.app (.var 0)
                (.app (.app appendL (.var 2)) (bytesChunk bz1)))
                (.var 2))))
            (.app (.app (.var 0) nilL) idOddK)))
          (.app lenb4L (.var 0))))
        (.app joinL (scottList
          [bytesChunk bz2, .var 0, bytesChunk bz1]))))
      (.app nibs2bytesL (.var 1))))

/-- `λl.λo.λoi.λrv.λrc.λsy. l N0 C` — ctx [sy,rc,rv,oi,o,l]:
    l=5,o=4,oi=3,rv=2,rc=1,sy=0. -/
def idStepSel : LTerm :=
  .abs (.abs (.abs (.abs (.abs (.abs
    (.app (.app (.var 5)
      (tupleL [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0]))
      idStepC))))))

/-- `_STEP_ID = λacc. acc SEL`. -/
def idataStepL : LTerm := .abs (.app (.var 0) idStepSel)

theorem closed_idataStepL : closed 0 idataStepL = true := by decide

-- empirical: cons-step count on closed literals — the let-instances
-- land on the `idNmb/idBrec/…` semantic forms.
set_option maxHeartbeats 1600000 in
example :
    hsteps 19 (.app idataStepL
        (tupleL [cellLit nilL nilL,
                 nilL, nilL, nilL, nilL, nilL]))
      = tupleL [nilL,
          .app (.app b4addL nilL) (idRl2 nilL),
          .app (.app b4addL nilL) (bytesChunk b8),
          .app (.app conssL (idHrv nilL)) nilL,
          .app (.app conssL (idRec nilL)) nilL,
          .app (.app conssL
            (.app (.app pairSrcL (iatPrefix nilL)) nilL)) nilL] := by
  decide

/-- STEP_ID on a cons-cell: `(nm::T, o,oi,rv,rc,sy) ↦
    (T, o+rl2, oi+8, hrv::rv, rec::rc, (iat_nm,oi)::sy)` —
    19-step milestone (count verified on literals above). -/
theorem idataStep_cons (nm T o oi rv rc sy : LTerm)
    (hnm : closed 0 nm = true) (hT : closed 0 T = true)
    (ho : closed 0 o = true) (hoi : closed 0 oi = true)
    (hrv : closed 0 rv = true) (hrc : closed 0 rc = true)
    (hsy : closed 0 sy = true) :
    LRed (.app idataStepL
        (tupleL [cellLit nm T, o, oi, rv, rc, sy]))
      (tupleL [T, .app (.app b4addL o) (idRl2 nm),
        .app (.app b4addL oi) (bytesChunk b8),
        .app (.app conssL (idHrv o)) rv,
        .app (.app conssL (idRec nm)) rc,
        .app (.app conssL
          (.app (.app pairSrcL (iatPrefix nm)) oi)) sy]) :=
  LRed_of_hsteps (k := 19) (by
    simp [idataStepL, idStepSel, idStepC, idK2Body, idOddK,
          idNmb, idBrec, idRln, idOdd, idRec, idRl2, idHrv,
          iatPrefix, tupleL, cellLit, scottList,
          aps, List.foldl, List.map, List.foldr,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_cellLit, closed_tupleL, closed_scottList,
          closed_nibs2bytesL, closed_joinL, closed_lenb4L,
          closed_appendL, closed_niboddL, closed_idOddK,
          closed_b4addL, closed_conssL, closed_pairSrcL,
          closed_bytesChunk, closed_nibLit, closed_nilL,
          hnm, hT, ho, hoi, hrv, hrc, hsy])

/-- empirical: nil-step count on closed literals -/
example :
    hsteps 10 (.app idataStepL
        (tupleL [nilL, nilL, nilL, nilL, nilL, nilL]))
      = tupleL [nilL, nilL, nilL, nilL, nilL, nilL] := by decide

/-- STEP_ID on the empty import list is the identity. -/
theorem idataStep_nil (o oi rv rc sy : LTerm)
    (ho : closed 0 o = true) (hoi : closed 0 oi = true)
    (hrv : closed 0 rv = true) (hrc : closed 0 rc = true)
    (hsy : closed 0 sy = true) :
    LRed (.app idataStepL
        (tupleL [nilL, o, oi, rv, rc, sy]))
        (tupleL [nilL, o, oi, rv, rc, sy]) :=
  LRed_of_hsteps (k := 10) (by
    simp [idataStepL, idStepSel, idStepC, idK2Body, idOddK,
          iatPrefix, tupleL, cellLit, scottList, nilL,
          aps, List.foldl, List.map, List.foldr,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_cellLit, closed_tupleL, closed_scottList,
          closed_nibs2bytesL, closed_joinL, closed_lenb4L,
          closed_appendL, closed_niboddL, closed_idOddK,
          closed_b4addL, closed_conssL, closed_pairSrcL,
          closed_bytesChunk, closed_nibLit, closed_nilL,
          ho, hoi, hrv, hrc, hsy])

-- idata semantic state -----------------------------------------------------

/-- Semantic STEP_ID on the `(o, oi, rv, rc, sy)` 5-state. -/
def idataStepSem (st : LTerm × LTerm × LTerm × LTerm × LTerm)
    (nm : LTerm) : LTerm × LTerm × LTerm × LTerm × LTerm :=
  (.app (.app b4addL st.1) (idRl2 nm),
   .app (.app b4addL st.2.1) (bytesChunk b8),
   .app (.app conssL (idHrv st.1)) st.2.2.1,
   .app (.app conssL (idRec nm)) st.2.2.2.1,
   .app (.app conssL
     (.app (.app pairSrcL (iatPrefix nm)) st.2.1)) st.2.2.2.2)

/-- idata state after k steps. -/
def idataAfterK (k : Nat) (es : List LTerm)
    (o oi rv rc sy : LTerm) : List LTerm :=
  let st := (es.take k).foldl idataStepSem (o, oi, rv, rc, sy)
  [scottList (es.drop k), st.1, st.2.1, st.2.2.1, st.2.2.2.1,
   st.2.2.2.2]

/-- Semantic fixed point over the import list. -/
def idataFinal (es : List LTerm) (namesOff iatB : List (Fin 16 × Fin 16))
    : LTerm × LTerm × LTerm × LTerm × LTerm :=
  es.foldl idataStepSem
    (bytesChunk namesOff, bytesChunk iatB, nilL, nilL, nilL)

theorem closed_idNmb {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (idNmb nm) = true :=
  closed_app closed_nibs2bytesL h

theorem closed_idBrec {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (idBrec nm) = true := by
  unfold idBrec
  apply closed_app closed_joinL
  apply closed_scottList
  intro x hx
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact closed_bytesChunk bz2
  · exact closed_idNmb h
  · exact closed_bytesChunk bz1

theorem closed_idRln {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (idRln nm) = true :=
  closed_app closed_lenb4L (closed_idBrec h)

theorem closed_idOdd {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (idOdd nm) = true :=
  closed_app (closed_app (closed_idRln h) closed_nilL) closed_idOddK

theorem closed_idRec {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (idRec nm) = true := by
  unfold idRec
  exact closed_app (closed_app (closed_idOdd h)
    (closed_app (closed_app closed_appendL (closed_idBrec h))
      (closed_bytesChunk bz1))) (closed_idBrec h)

theorem closed_idRl2 {nm : LTerm} (h : closed 0 nm = true) :
    closed 0 (idRl2 nm) = true :=
  closed_app closed_lenb4L (closed_idRec h)

theorem closed_idHrv {o : LTerm} (h : closed 0 o = true) :
    closed 0 (idHrv o) = true :=
  closed_app (closed_app closed_b4addL (closed_bytesChunk b2000)) h

/-- `idataStepSem` preserves component closedness. -/
theorem closed_idataStepSem {st : LTerm×LTerm×LTerm×LTerm×LTerm}
    {nm : LTerm}
    (ho : closed 0 st.1 = true) (hoi : closed 0 st.2.1 = true)
    (hrv : closed 0 st.2.2.1 = true)
    (hrc : closed 0 st.2.2.2.1 = true)
    (hsy : closed 0 st.2.2.2.2 = true)
    (hnm : closed 0 nm = true) :
    closed 0 (idataStepSem st nm).1 = true ∧
    closed 0 (idataStepSem st nm).2.1 = true ∧
    closed 0 (idataStepSem st nm).2.2.1 = true ∧
    closed 0 (idataStepSem st nm).2.2.2.1 = true ∧
    closed 0 (idataStepSem st nm).2.2.2.2 = true := by
  unfold idataStepSem
  exact ⟨closed_app (closed_app closed_b4addL ho)
           (closed_idRl2 hnm),
         closed_app (closed_app closed_b4addL hoi)
           (closed_bytesChunk b8),
         closed_app (closed_app closed_conssL (closed_idHrv ho)) hrv,
         closed_app (closed_app closed_conssL (closed_idRec hnm)) hrc,
         closed_app (closed_app closed_conssL
           (closed_app (closed_app closed_pairSrcL
             (closed_iatPrefix hnm)) hoi)) hsy⟩

/-- `idataStepSem`-fold over a closed prefix stays closed. -/
theorem closed_idataAfterK {k : Nat} {es : List LTerm}
    {o oi rv rc sy : LTerm}
    (hcl : ∀ e ∈ es, closed 0 e = true)
    (ho : closed 0 o = true) (hoi : closed 0 oi = true)
    (hrv : closed 0 rv = true) (hrc : closed 0 rc = true)
    (hsy : closed 0 sy = true) :
    closed 0 ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).1
        = true ∧
    closed 0 ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.1
        = true ∧
    closed 0 ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.1
        = true ∧
    closed 0 ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.1
        = true ∧
    closed 0 ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.2
        = true := by
  have hfold : ∀ (pref : List LTerm)
      (o oi rv rc sy : LTerm),
      closed 0 o = true → closed 0 oi = true →
      closed 0 rv = true → closed 0 rc = true →
      closed 0 sy = true →
      (∀ e ∈ pref, closed 0 e = true) →
      closed 0 (pref.foldl idataStepSem (o,oi,rv,rc,sy)).1 = true ∧
      closed 0 (pref.foldl idataStepSem (o,oi,rv,rc,sy)).2.1 = true ∧
      closed 0 (pref.foldl idataStepSem (o,oi,rv,rc,sy)).2.2.1
          = true ∧
      closed 0 (pref.foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.1
          = true ∧
      closed 0 (pref.foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.2
          = true := by
    intro pref
    induction pref with
    | nil =>
        intro _ _ _ _ _ ho' hoi' hrv' hrc' hsy' _
        exact ⟨ho', hoi', hrv', hrc', hsy'⟩
    | cons a t ihp =>
        intro o oi rv rc sy ho' hoi' hrv' hrc' hsy' hp
        have ha := hp a List.mem_cons_self
        have hstep := closed_idataStepSem
          (st := (o, oi, rv, rc, sy)) (nm := a)
          ho' hoi' hrv' hrc' hsy' ha
        simp only [List.foldl_cons]
        exact ihp _ _ _ _ _ hstep.1 hstep.2.1 hstep.2.2.1
          hstep.2.2.2.1 hstep.2.2.2.2
          (fun e he => hp e (List.mem_cons_of_mem a he))
  exact hfold (es.take k) o oi rv rc sy ho hoi hrv hrc hsy
    (fun e he => hcl e (List.mem_of_mem_take he))

/-- Tuple-state iterate for STEP_ID. -/
theorem idataOf_iterK : ∀ (k : Nat) (es : List LTerm)
    (o oi rv rc sy : LTerm),
    k ≤ es.length →
    (∀ e ∈ es, closed 0 e = true) →
    closed 0 o = true → closed 0 oi = true →
    closed 0 rv = true → closed 0 rc = true →
    closed 0 sy = true →
    LRed (iterL idataStepL
        (tupleL (idataAfterK 0 es o oi rv rc sy)) k)
        (tupleL (idataAfterK k es o oi rv rc sy)) := by
  intro k es o oi rv rc sy
  induction k with
  | zero => intro _ _ _ _ _ _ _; exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro hk hcl ho hoi hrv hrc hsy
      have hlt : k < es.length := hk
      show LRed (.app idataStepL
          (iterL idataStepL
            (tupleL (idataAfterK 0 es o oi rv rc sy)) k))
        (tupleL (idataAfterK (k+1) es o oi rv rc sy))
      have hmid := LRed_app_right (f := idataStepL)
        (ih (Nat.le_of_succ_le hk) hcl ho hoi hrv hrc hsy)
      have hdrop : es.drop k = es[k] :: es.drop (k+1) :=
        (List.getElem_cons_drop (as := es) hlt).symm
      have hstep1 : LRed
          (.app idataStepL (tupleL (idataAfterK k es o oi rv rc sy)))
          (tupleL (idataAfterK (k+1) es o oi rv rc sy)) := by
        have hk1 : idataAfterK k es o oi rv rc sy =
            [cellLit es[k] (scottList (es.drop (k+1))),
             ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).1,
             ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.1,
             ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.1,
             ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.1,
             ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.2]
            := by
          unfold idataAfterK
          simp only [hdrop, scottList, List.foldr_cons]
        have hk2 : idataAfterK (k+1) es o oi rv rc sy =
            [scottList (es.drop (k+1)),
             .app (.app b4addL
               ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).1)
               (idRl2 es[k]),
             .app (.app b4addL
               ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.1)
               (bytesChunk b8),
             .app (.app conssL (idHrv
               ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).1))
               ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.1,
             .app (.app conssL (idRec es[k]))
               ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.1,
             .app (.app conssL
               (.app (.app pairSrcL (iatPrefix es[k]))
                 ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.1))
               ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.2]
            := by
          unfold idataAfterK
          rw [List.take_add_one, List.getElem?_eq_getElem hlt]
          simp only [Option.toList_some, List.foldl_append,
            List.foldl_cons, List.foldl_nil, idataStepSem]
        rw [hk1, hk2]
        obtain ⟨ho', hoi', hrv', hrc', hsy'⟩ := closed_idataAfterK
          (k := k) (es := es) (o := o) (oi := oi) (rv := rv)
          (rc := rc) (sy := sy) hcl ho hoi hrv hrc hsy
        have hT : closed 0 (scottList (es.drop (k+1))) = true := by
          apply closed_scottList
          intro x hx
          exact hcl x (List.mem_of_mem_drop hx)
        exact idataStep_cons es[k]
          (scottList (es.drop (k+1)))
          ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).1
          ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.1
          ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.1
          ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.1
          ((es.take k).foldl idataStepSem (o,oi,rv,rc,sy)).2.2.2.2
          (hcl es[k] (List.getElem_mem hlt)) hT
          ho' hoi' hrv' hrc' hsy'
      exact hmid.trans hstep1

-- _IDATA_FIN finalizer -----------------------------------------------------

/-- `B4ADD (b4 0x2000) o` — the directory-name RVA (same shape as
    `idHrv` but kept separate: it lives in the finalizer, not the
    step). -/
def idDrva (o : LTerm) : LTerm :=
  .app (.app b4addL (bytesChunk b2000)) o

/-- `JOIN (REV (conss (bytes 8×00) (MAP U64 rv)))` — the ILT/IAT. -/
def idIlt (rv : LTerm) : LTerm :=
  .app joinL (.app revL
    (.app (.app conssL (bytesChunk bZero8))
      (.app (.app mapL u64L) rv)))

/-- `JOIN [b4 0x2028, b4 0, b4 0, drva, iat4, ZEROFILL 20]` — the
    import directory table entry. -/
def idIdt (o : LTerm) (iat4 : List (Fin 16 × Fin 16)) : LTerm :=
  .app joinL (scottList
    [bytesChunk b2028, bytesChunk bZero4, bytesChunk bZero4,
     idDrva o, bytesChunk iat4, .app zerofillL (churchL 20)])

/-- `JOIN (REV rc)` — the hint/name + record area. -/
def idNams (rc : LTerm) : LTerm := .app joinL (.app revL rc)

/-- `JOIN [idt, ilt, ilt, nams, kernel32.dll\x00]` — the section body. -/
def idBody (o rv rc : LTerm) (iat4 : List (Fin 16 × Fin 16)) : LTerm :=
  .app joinL (scottList
    [idIdt o iat4, idIlt rv, idIlt rv, idNams rc,
     bytesChunk bKernel])

/-- `λl.λo.λoi.λrv.λrc.λsy. LETS[drva,ilt,idt,nams,body]
    (PRS body sy)` — `_IDATA_FIN`.  Let-binding ctx grows
    `[drva,sy,rc,rv,oi,o,l]` → `[body,…,l]`. -/
def idFinL (iat4 : List (Fin 16 × Fin 16)) : LTerm :=
  .abs (.abs (.abs (.abs (.abs (.abs
    (.app (.abs                       -- drva
      (.app (.abs                     -- ilt
        (.app (.abs                   -- idt
          (.app (.abs                 -- nams
            (.app (.abs               -- body
              (.app (.app pairSrcL (.var 0)) (.var 5)))
              (.app joinL (scottList
                [.var 1, .var 2, .var 2, .var 0,
                 bytesChunk bKernel]))))
            (.app joinL (.app revL (.var 4)))))
          (.app joinL (scottList
            [bytesChunk b2028, bytesChunk bZero4, bytesChunk bZero4,
             .var 1, bytesChunk iat4,
             .app zerofillL (churchL 20)]))))
        (.app joinL (.app revL
          (.app (.app conssL (bytesChunk bZero8))
            (.app (.app mapL u64L) (.var 3)))))))
      (.app (.app b4addL (bytesChunk b2000)) (.var 4))))))))

theorem closed_revL_any (c : Nat) : closed c revL = true :=
  closed_mono closed_revL (Nat.zero_le c)

theorem closed_mapL_any (c : Nat) : closed c mapL = true :=
  closed_mono closed_mapL (Nat.zero_le c)

theorem closed_appendL_any (c : Nat) : closed c appendL = true :=
  closed_mono closed_appendL (Nat.zero_le c)

theorem closed_nibs2bytesL_any (c : Nat) :
    closed c nibs2bytesL = true :=
  closed_mono closed_nibs2bytesL (Nat.zero_le c)

theorem closed_niboddL_any (c : Nat) : closed c niboddL = true :=
  closed_mono closed_niboddL (Nat.zero_le c)

theorem closed_iatPrefix_any (c : Nat) {nm : LTerm}
    (h : closed c nm = true) : closed c (iatPrefix nm) = true := by
  simp [iatPrefix, closed, Bool.and_eq_true,
    closed_conssL_any, closed_nibLit_any, h]

theorem closed_idFinL (iat4 : List (Fin 16 × Fin 16)) :
    closed 0 (idFinL iat4) = true := by
  simp [idFinL, scottList, cellLit,
        closed, shift, List.foldr, List.foldl, List.map, aps,
        shift_of_closed0, subst_of_closed0,
        closed_joinL_any, closed_revL_any, closed_mapL_any,
        closed_appendL_any, closed_u64L_any, closed_zerofillL_any,
        closed_churchL_any, closed_b4addL_any, closed_conssL_any,
        closed_pairSrcL_any, closed_nibLit_any, closed_nilL_any,
        closed_bytesChunk, closed_bytesChunk_any]

-- empirical: FIN count on closed literals — 6 state betas + 5 lets
-- + 2 pairSrc betas = 13.
set_option maxHeartbeats 1600000 in
example :
    hsteps 13 (aps (idFinL bZero4)
        [nilL, nilL, nilL, nilL, nilL, nilL])
      = pairLit (idBody nilL nilL nilL bZero4) nilL := by decide

/-- `idFinL·l·o·oi·rv·rc·sy →* pairLit (idBody o rv rc) sy`. -/
theorem idFin_eval (l o oi rv rc sy : LTerm)
    (iat4 : List (Fin 16 × Fin 16))
    (ho : closed 0 o = true) (hoi : closed 0 oi = true)
    (hrv : closed 0 rv = true) (hrc : closed 0 rc = true)
    (hsy : closed 0 sy = true) :
    LRed (aps (idFinL iat4) [l, o, oi, rv, rc, sy])
        (pairLit (idBody o rv rc iat4) sy) :=
  LRed_of_hsteps (k := 13) (by
    simp [idFinL, idBody, idIdt, idIlt, idDrva, idNams, pairLit,
          pairSrcL, scottList, cellLit, iatPrefix,
          aps, List.foldl, List.map, List.foldr,
          hsteps, hstep, subst, shift, shift_zero, subst_shift_succ,
          subst_of_closed0, shift_of_closed0, closed, closed_app,
          closed_cellLit, closed_scottList,
          closed_joinL, closed_revL, closed_mapL, closed_appendL,
          closed_u64L, closed_zerofillL, closed_churchL,
          closed_b4addL, closed_conssL, closed_pairSrcL,
          closed_bytesChunk, closed_nibLit, closed_nilL,
          ho, hoi, hrv, hrc, hsy])

/-- `idata_src n` — `(church n · STEP_ID · init) FIN` with
    `init = tupleL [imports, namesOff, iatB, K, K, K]`.  The three
    placeholder bytes4 are parameters (they depend on n_imp). -/
def idataOfL (n : Nat) (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    : LTerm :=
  .abs (.app
    (.app (.app (churchL n) idataStepL)
      (tupleL [.var 0, bytesChunk namesOff, bytesChunk iatB,
               nilL, nilL, nilL]))
    (idFinL iat4))

theorem closed_idataOfL (n : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16)) :
    closed 0 (idataOfL n namesOff iatB iat4) = true := by
  unfold idataOfL
  simp only [closed, Bool.and_eq_true]
  refine ⟨⟨⟨closed_mono (closed_churchL n) (Nat.zero_le 1),
      closed_mono closed_idataStepL (Nat.zero_le 1)⟩, ?_⟩,
    closed_mono (closed_idFinL iat4) (Nat.zero_le 1)⟩
  show closed 2 (aps (.var 0)
      ([.var 0, bytesChunk namesOff, bytesChunk iatB,
        nilL, nilL, nilL].map (shift 1 0))) = true
  apply closed_aps
  · rfl
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    simp only [List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · rw [shift_of_closed0 (closed_bytesChunk namesOff)]
      exact closed_mono (closed_bytesChunk namesOff)
        (Nat.zero_le 2)
    · rw [shift_of_closed0 (closed_bytesChunk iatB)]
      exact closed_mono (closed_bytesChunk iatB) (Nat.zero_le 2)
    · rw [shift_of_closed0 closed_nilL]
      exact closed_mono closed_nilL (Nat.zero_le 2)
    · rw [shift_of_closed0 closed_nilL]
      exact closed_mono closed_nilL (Nat.zero_le 2)
    · rw [shift_of_closed0 closed_nilL]
      exact closed_mono closed_nilL (Nat.zero_le 2)

/-- `idataOf` evaluation: iterate STEP_ID over the import names, then
    project `(body, sy)` — the section bytes and the
    `(iat_nm, oi)` symbol table. -/
theorem idataOf_eval (es : List LTerm)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hcl : ∀ e ∈ es, closed 0 e = true) :
    LRed (.app (idataOfL es.length namesOff iatB iat4)
        (scottList es))
      (pairLit
        (idBody (idataFinal es namesOff iatB).1
                (idataFinal es namesOff iatB).2.2.1
                (idataFinal es namesOff iatB).2.2.2.1 iat4)
        (idataFinal es namesOff iatB).2.2.2.2) := by
  have hclosedS : closed 0 (scottList es) = true :=
    closed_scottList (fun x hx => hcl x hx)
  have hinit : closed 0 (tupleL [scottList es,
      bytesChunk namesOff, bytesChunk iatB,
      nilL, nilL, nilL]) = true :=
    closed_tupleL (fun e he => by
      simp only [List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hclosedS
      · exact closed_bytesChunk namesOff
      · exact closed_bytesChunk iatB
      · exact closed_nilL
      · exact closed_nilL
      · exact closed_nilL)
  have hopen : LRed
      (.app (idataOfL es.length namesOff iatB iat4)
        (scottList es))
      (.app
        (.app (.app (churchL es.length) idataStepL)
          (tupleL [scottList es, bytesChunk namesOff,
                   bytesChunk iatB, nilL, nilL, nilL]))
        (idFinL iat4)) :=
    LRed_of_hsteps (k := 1) (by
      simp [idataOfL, tupleL, aps, List.foldl, List.map,
            hsteps, hstep, subst, shift, shift_zero,
            subst_shift_succ,
            subst_of_closed0, shift_of_closed0, closed, closed_app,
            closed_churchL, closed_idataStepL, closed_idFinL,
            closed_bytesChunk, closed_nilL, hclosedS])
  have hiter : LRed
      (.app (.app (churchL es.length) idataStepL)
        (tupleL [scottList es, bytesChunk namesOff,
                 bytesChunk iatB, nilL, nilL, nilL]))
      (iterL idataStepL
        (tupleL [scottList es, bytesChunk namesOff,
                 bytesChunk iatB, nilL, nilL, nilL]) es.length) :=
    church_eval es.length idataStepL _ closed_idataStepL hinit
  have hrun : LRed
      (iterL idataStepL
        (tupleL [scottList es, bytesChunk namesOff,
                 bytesChunk iatB, nilL, nilL, nilL]) es.length)
      (tupleL [nilL, (idataFinal es namesOff iatB).1,
               (idataFinal es namesOff iatB).2.1,
               (idataFinal es namesOff iatB).2.2.1,
               (idataFinal es namesOff iatB).2.2.2.1,
               (idataFinal es namesOff iatB).2.2.2.2]) := by
    have h := idataOf_iterK es.length es
      (bytesChunk namesOff) (bytesChunk iatB) nilL nilL nilL
      (Nat.le_refl _) hcl
      (closed_bytesChunk namesOff) (closed_bytesChunk iatB)
      closed_nilL closed_nilL closed_nilL
    have h0 : idataAfterK 0 es
        (bytesChunk namesOff) (bytesChunk iatB) nilL nilL nilL =
        [scottList es, bytesChunk namesOff, bytesChunk iatB,
         nilL, nilL, nilL] := by
      simp only [idataAfterK, List.take_zero, List.drop_zero,
        List.foldl_nil]
    have hn : idataAfterK es.length es
        (bytesChunk namesOff) (bytesChunk iatB) nilL nilL nilL =
        [nilL, (idataFinal es namesOff iatB).1,
         (idataFinal es namesOff iatB).2.1,
         (idataFinal es namesOff iatB).2.2.1,
         (idataFinal es namesOff iatB).2.2.2.1,
         (idataFinal es namesOff iatB).2.2.2.2] := by
      simp only [idataAfterK, idataFinal, List.take_length,
        List.drop_length, scottList, List.foldr_nil]
    rwa [h0, hn] at h
  have hfin : LRed
      (.app (tupleL [nilL, (idataFinal es namesOff iatB).1,
                     (idataFinal es namesOff iatB).2.1,
                     (idataFinal es namesOff iatB).2.2.1,
                     (idataFinal es namesOff iatB).2.2.2.1,
                     (idataFinal es namesOff iatB).2.2.2.2])
        (idFinL iat4))
      (pairLit
        (idBody (idataFinal es namesOff iatB).1
                (idataFinal es namesOff iatB).2.2.1
                (idataFinal es namesOff iatB).2.2.2.1 iat4)
        (idataFinal es namesOff iatB).2.2.2.2) := by
    have h := tupleL_apply [nilL, (idataFinal es namesOff iatB).1,
      (idataFinal es namesOff iatB).2.1,
      (idataFinal es namesOff iatB).2.2.1,
      (idataFinal es namesOff iatB).2.2.2.1,
      (idataFinal es namesOff iatB).2.2.2.2] (idFinL iat4)
    obtain ⟨ho', hoi', hrv', hrc', hsy'⟩ := closed_idataAfterK
      (k := es.length) (es := es)
      (o := bytesChunk namesOff) (oi := bytesChunk iatB)
      (rv := nilL) (rc := nilL) (sy := nilL) hcl
      (closed_bytesChunk namesOff) (closed_bytesChunk iatB)
      closed_nilL closed_nilL closed_nilL
    have heq : es.take es.length = es := List.take_length
    rw [heq] at ho' hoi' hrv' hrc' hsy'
    exact h.trans (idFin_eval nilL _ _ _ _ _ iat4
      ho' hoi' hrv' hrc' hsy')
  exact hopen.trans ((LRed_app_left
      (hiter.trans hrun)).trans hfin)


-- batch J axiom audit ---------------------------------------------------

#print axioms dataStep_cons
#print axioms dataStep_nil
#print axioms dataOf_iterK
#print axioms dataFin_eval
#print axioms dataOf_eval
#print axioms idataStep_cons
#print axioms idataStep_nil
#print axioms idataOf_iterK
#print axioms idFin_eval
#print axioms idataOf_eval

-- ============================================================
-- Batch K: packOf — section normalization + pack_src assembly.
-- ============================================================

-- K0 foundations ----------------------------------------------------

/-- `(incByteN lo hi)` new lo-nibble flips parity. -/
theorem incByteN_parity (lo hi : Fin 16) :
    (incByteN lo hi).1.1.val % 2 = (lo.val + 1) % 2 := by
  unfold incByteN
  by_cases h : lo.val = 15
  · simp [h]
  · simp only [h, ite_false]
    omega

/-- `incBytes` under carry-in: the head cell is `incByteN`-updated. -/
theorem incBytes_head (x : Fin 16 × Fin 16)
    (xs : List (Fin 16 × Fin 16)) :
    (incBytes (x :: xs) true).head? =
      some (incByteN x.1 x.2).1 := by
  simp [incBytes]

/-- The incBytes-fold byte0.lo parity is the cell-count parity. -/
theorem lenFold_parity : ∀ (cs : List LTerm) (x : Fin 16 × Fin 16)
    (xs : List (Fin 16 × Fin 16)),
    ∃ p, (cs.foldl (fun a _ => incBytes a true) (x :: xs)).head?
        = some p
      ∧ p.1.val % 2 = (x.1.val + cs.length) % 2 := by
  intro cs; induction cs with
  | nil =>
    intro x xs
    exact ⟨x, rfl, by simp⟩
  | cons c cs ih =>
    intro x xs
    rw [List.foldl_cons]
    obtain ⟨p, hp1, hp2⟩ := ih (incByteN x.1 x.2).1
      (incBytes xs (incByteN x.1 x.2).2)
    refine ⟨p, ?_, ?_⟩
    · rw [← hp1]
      simp [incBytes]
    · rw [hp2]
      have hpar := incByteN_parity x.1 x.2
      have hstep : ((incByteN x.1 x.2).1.1.val + cs.length) % 2
          = (x.1.val + (cs.length + 1)) % 2 := by
        have h1 := Nat.add_mod (incByteN x.1 x.2).1.1.val cs.length 2
        rw [hpar] at h1
        rw [h1]
        rw [show x.1.val + (cs.length + 1) = (x.1.val + 1) + cs.length
            from by omega]
        rw [Nat.add_mod]
        omega
      simpa [List.length_cons] using hstep

/-- The `lenb4` output fold preserves length 4. -/
theorem lenFold_len4 {α : Type} (cs : List α)
    (acc : List (Fin 16 × Fin 16)) (hacc : acc.length = 4) :
    (cs.foldl (fun a _ => incBytes a true) acc).length = 4 := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons c cs ih =>
    rw [List.foldl_cons]
    exact ih _ (by rw [incBytes_length]; exact hacc)

-- nibs2bytes semantic bytes -----------------------------------------

/-- Semantic `_NIBS2BYTES`: pairs `(h,l)` to byte `(l,h)` — the lo
    nibble is the second list element (LE nibble order). -/
def nibs2bytesB : List (Fin 16) → List (Fin 16 × Fin 16)
  | [] => []
  | [_] => []
  | hi :: lo :: t => (lo, hi) :: nibs2bytesB t

/-- `nibPairUp` on nibble literals is `nibs2bytesB` at the cell level
    (pairSrc thunks, thawed by consumers at spine position). -/
theorem nibPairUp_nibLit : ∀ (ns : List (Fin 16)),
    nibPairUp (ns.map nibLit) =
      (nibs2bytesB ns).map
        (fun p => .app (.app pairSrcL (nibLit p.1)) (nibLit p.2)) := by
  intro ns; induction ns using nibs2bytesB.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 hi lo t ih =>
    simp [List.map_cons, nibPairUp, nibs2bytesB, ih]

theorem nibs2bytesB_length : ∀ (ns : List (Fin 16)),
    (nibs2bytesB ns).length = ns.length / 2 := by
  intro ns; induction ns using nibs2bytesB.induct with
  | case1 => rfl
  | case2 a => simp [nibs2bytesB]
  | case3 hi lo t ih =>
    simp [nibs2bytesB, ih, List.length_cons]
    omega

-- thunk-fold machinery -----------------------------------------------

/-- `foldr appendT` over closed terms is closed. -/
theorem closed_appendT_foldr : ∀ (us : List LTerm),
    (∀ u ∈ us, closed 0 u = true) →
    closed 0 (us.foldr appendT nilL) = true := by
  intro us
  induction us with
  | nil => intro _; exact closed_nilL
  | cons u us ih2 =>
    intro hu
    simp only [List.foldr_cons]
    exact closed_appendT (hu u List.mem_cons_self)
      (ih2 (fun v hv => hu v (List.mem_cons_of_mem u hv)))

/-- `foldr appendT` over thunk elements: each `t` reduces to a
    `scottList` before its append consumes it. -/
theorem appendT_foldr_thunks : ∀ (ts : List LTerm)
    (bss : List (List LTerm)),
    List.Forall₂ (fun t bs => LRed t (scottList bs)) ts bss →
    (∀ e ∈ bss.flatten, closed 0 e = true) →
    (∀ t ∈ ts, closed 0 t = true) →
    LRed (ts.foldr appendT nilL) (scottList bss.flatten) := by
  intro ts
  induction ts with
  | nil =>
    intro bss h _ _
    cases h
    exact Relation.ReflTransGen.refl
  | cons t ts' ih =>
    intro bss h hcl htcl
    cases bss with
    | nil => cases h
    | cons b bss' =>
      cases h with
      | cons hth htail =>
      simp only [List.foldr_cons, List.flatten_cons]
      have hrev : LRed (revT t) (revT (scottList b)) :=
        LRed_app_left (LRed_app_right hth)
      have hap : LRed (appendT t (ts'.foldr appendT nilL))
          (appendT (scottList b) (ts'.foldr appendT nilL)) :=
        LRed_app_left (LRed_app_right hrev)
      have hrest : IsList (ts'.foldr appendT nilL) bss'.flatten :=
        ih bss' htail
          (fun e he => by
            obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
            exact hcl e (List.mem_flatten.mpr
              ⟨w, List.mem_cons_of_mem b hw, hew⟩))
          (fun u hu => htcl u (List.mem_cons_of_mem t hu))
      have hbcl : ∀ e ∈ b, closed 0 e = true :=
        fun e he => hcl e (List.mem_flatten.mpr
          ⟨b, List.mem_cons_self, he⟩)
      have hrestcl : ∀ e ∈ bss'.flatten, closed 0 e = true :=
        fun e he => by
          obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
          exact hcl e (List.mem_flatten.mpr
            ⟨w, List.mem_cons_of_mem b hw, hew⟩)
      have hrestT : closed 0 (ts'.foldr appendT nilL) = true :=
        closed_appendT_foldr ts'
          (fun u hu => htcl u (List.mem_cons_of_mem t hu))
      exact hap.trans (append_eval _ _ _ _
        Relation.ReflTransGen.refl hrest hbcl hrestcl
        (closed_scottList hbcl) hrestT)

/-- `JOIN` over a Scott list of thunk elements: each thunk reduces to
    its `scottList` before append consumes it. -/
theorem join_thunks_eval (ts : List LTerm) (bss : List (List LTerm))
    (h : List.Forall₂ (fun t bs => LRed t (scottList bs)) ts bss)
    (hcl : ∀ e ∈ bss.flatten, closed 0 e = true)
    (htcl : ∀ t ∈ ts, closed 0 t = true) :
    LRed (.app joinL (scottList ts)) (scottList bss.flatten) := by
  have hs'' : ∀ e r, closed 0 e = true → closed 0 r = true →
      LRed (.app (.app appendL e) r) (appendT e r) ∧
      closed 0 (appendT e r) = true :=
    fun e r he hr =>
      ⟨appendL_to_appendT e r he hr, closed_appendT he hr⟩
  have e1 := fixr_eval appendL nilL appendT closed_appendL closed_nilL
    hs'' _ _ (closed_scottList htcl) Relation.ReflTransGen.refl htcl
  exact (joinL_to_fixr _ (closed_scottList htcl)).trans
    (e1.trans (appendT_foldr_thunks _ _ h hcl htcl))

-- per-record evals ---------------------------------------------------

/-- `brec` cells: `[00,00] ++ nibs2bytes-cells ++ [00]` —
    `nibPairUp` cells stay pairSrc-thunks. -/
def brecCells (ns : List (Fin 16)) : List LTerm :=
  bm bz2 ++ nibPairUp (ns.map nibLit) ++ bm bz1

theorem closed_brecCells (ns : List (Fin 16)) :
    ∀ e ∈ brecCells ns, closed 0 e = true := by
  intro e he
  rw [brecCells] at he
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h2 | h2
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h2
      exact closed_byteLit _ _
    · rw [nibPairUp_nibLit] at h2
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp h2
      exact closed_app (closed_app closed_pairSrcL
        (closed_nibLit _)) (closed_nibLit _)
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    exact closed_byteLit _ _

/-- `brec` thunk → its cell list.  `JOIN` on a 3-thunk Scott list. -/
theorem idBrec_eval (ns : List (Fin 16)) :
    LRed (idBrec (scottList (ns.map nibLit)))
      (scottList (brecCells ns)) := by
  simp only [idBrec, idNmb]
  have hcl : ∀ t ∈ [bytesChunk bz2,
      .app nibs2bytesL (scottList (ns.map nibLit)),
      bytesChunk bz1], closed 0 t = true := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact closed_bytesChunk bz2
    · exact closed_app closed_nibs2bytesL
        (closed_scottList (fun e he => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
          exact closed_nibLit i))
    · exact closed_bytesChunk bz1
  have hf := join_thunks_eval
    [bytesChunk bz2, .app nibs2bytesL (scottList (ns.map nibLit)),
     bytesChunk bz1]
    [bm bz2, nibPairUp (ns.map nibLit), bm bz1]
    (List.Forall₂.cons (bytesChunk_nf bz2)
      (List.Forall₂.cons
        (nibs2bytes_eval _ (fun e he => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
          exact closed_nibLit i))
        (List.Forall₂.cons (bytesChunk_nf bz1) List.Forall₂.nil)))
    (closed_brecCells ns) hcl
  have hflat : [bm bz2, nibPairUp (ns.map nibLit), bm bz1].flatten
      = brecCells ns := by
    simp [List.flatten, brecCells]
  rwa [hflat] at hf

/-- term-list version of `len4`: the incBytes fold over cells. -/
def lenFoldT (cs : List LTerm) : List (Fin 16 × Fin 16) :=
  cs.foldl (fun a _ => incBytes a true) b4zeroBytes

/-- `LENB4·brec` — count of the record cells as bytes4. -/
theorem idRln_eval (ns : List (Fin 16)) :
    LRed (idRln (scottList (ns.map nibLit)))
      (scottList (bm (lenFoldT (brecCells ns)))) := by
  simp only [idRln]
  exact (LRed_app_right (idBrec_eval ns)).trans
    (lenb4_eval _ (closed_brecCells ns))

/-- `rln K (λb0.λt0. b0 (λbl.λbh. NIBODD bl))` on a len4 scottList
    reduces to `NIBODD·(nibLit b0.lo)`. -/
theorem idOdd_peel (w0 w1 w2 w3 : Fin 16 × Fin 16) :
    LRed (.app (.app (scottList
        [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
         byteLit w2.1 w2.2, byteLit w3.1 w3.2]) nilL) idOddK)
      (.app niboddL (nibLit w0.1)) :=
  LRed_of_hsteps (k := 7) (by
    simp [scottList, cellLit, idOddK, byteLit, pairLit,
          List.foldr, hsteps, hstep, subst, shift,
          subst_of_closed0, shift_of_closed0,
          closed_nibLit, closed_niboddL, closed_nilL])

/-- `odd` = parity of the brec cell count. -/
theorem idOdd_eval (ns : List (Fin 16)) :
    LRed (idOdd (scottList (ns.map nibLit)))
      (boolLit (decide ((brecCells ns).length % 2 = 1))) := by
  simp only [idOdd]
  have hln : (lenFoldT (brecCells ns)).length = 4 :=
    lenFold_len4 _ _ (by decide)
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hln
  have hrln : LRed
      (.app (.app (idRln (scottList (ns.map nibLit))) nilL) idOddK)
      (.app (.app (scottList (bm (lenFoldT (brecCells ns)))) nilL)
        idOddK) :=
    LRed_app_left (LRed_app_left (idRln_eval ns))
  have hbm : bm (lenFoldT (brecCells ns)) =
      [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
       byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
    rw [hws]; rfl
  have hpeel := idOdd_peel w0 w1 w2 w3
  rw [hbm] at hrln
  have hodd := (hrln.trans hpeel).trans (nibodd_eval w0.1)
  -- parity bridge: w0.lo % 2 = cell count % 2
  have hdef : ((0, 0) :: [(0, 0), (0, 0), (0, 0)] :
      List (Fin 16 × Fin 16)) = b4zeroBytes := rfl
  obtain ⟨p, hp1, hp2⟩ := lenFold_parity (brecCells ns)
    (0, 0) [(0, 0), (0, 0), (0, 0)]
  rw [hdef] at hp1
  have hp1' : (lenFoldT (brecCells ns)).head? = some p := hp1
  rw [hws] at hp1'
  have hp0 : p = w0 := (Option.some.inj hp1').symm
  have hpar : w0.1.val % 2 = (brecCells ns).length % 2 := by
    rw [hp0] at hp2
    simpa using hp2
  rw [← hpar]
  exact hodd

-- idRec / idRl2 / idHrv / zChain ---------------------------------------

/-- `rec` cells: `brec` padded by `[00]` when the count is odd —
    `odd (APPEND brec 00) brec` at cell level. -/
def recCells (ns : List (Fin 16)) : List LTerm :=
  if (brecCells ns).length % 2 = 1
  then brecCells ns ++ bm bz1 else brecCells ns

theorem closed_recCells (ns : List (Fin 16)) :
    ∀ e ∈ recCells ns, closed 0 e = true := by
  intro e he
  by_cases hp : (brecCells ns).length % 2 = 1
  · simp only [recCells, if_pos hp] at he
    rcases List.mem_append.mp he with h | h
    · exact closed_brecCells ns e h
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
      exact closed_byteLit _ _
  · simp only [recCells, if_neg hp] at he
    exact closed_brecCells ns e he

/-- closedness of the `idBrec` term on a nibble-literal name list. -/
theorem closed_idBrec_scott (ns : List (Fin 16)) :
    closed 0 (idBrec (scottList (ns.map nibLit))) = true := by
  have hsc : closed 0 (scottList (ns.map nibLit)) = true :=
    closed_scottList (fun e he => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      exact closed_nibLit i)
  show closed 0 (.app joinL (scottList
    [bytesChunk bz2, idNmb (scottList (ns.map nibLit)),
     bytesChunk bz1])) = true
  refine closed_app closed_joinL
    (closed_scottList (fun e he => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact closed_bytesChunk bz2
  · exact closed_app closed_nibs2bytesL hsc
  · exact closed_bytesChunk bz1

/-- `odd (APPEND brec 00) brec` — the import record with parity pad. -/
theorem idRec_eval (ns : List (Fin 16)) :
    LRed (idRec (scottList (ns.map nibLit)))
      (scottList (recCells ns)) := by
  simp only [idRec]
  have hb := closed_idBrec_scott ns
  have hA : LRed
      (.app (.app appendL (idBrec (scottList (ns.map nibLit))))
        (bytesChunk bz1))
      (scottList (brecCells ns ++ bm bz1)) :=
    (appendL_to_appendT _ _ hb (closed_bytesChunk bz1)).trans
      (append_eval _ _ _ _ (idBrec_eval ns)
        (bytesChunk_nf bz1) (closed_brecCells ns)
        (fun e he => by
          obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
          exact closed_byteLit _ _)
        hb (closed_bytesChunk bz1))
  have hsel : LRed
      (.app (.app (idOdd (scottList (ns.map nibLit)))
        (.app (.app appendL (idBrec (scottList (ns.map nibLit))))
          (bytesChunk bz1)))
        (idBrec (scottList (ns.map nibLit))))
      (if decide ((brecCells ns).length % 2 = 1) = true
        then .app (.app appendL (idBrec (scottList (ns.map nibLit))))
          (bytesChunk bz1)
        else idBrec (scottList (ns.map nibLit))) :=
    (LRed_app_left (LRed_app_left (idOdd_eval ns))).trans
      (boolLit_sel _ _ _)
  by_cases hp : (brecCells ns).length % 2 = 1
  · have hd : decide ((brecCells ns).length % 2 = 1) = true := by
      simp [hp]
    rw [hd] at hsel
    simp at hsel
    have hrc : recCells ns = brecCells ns ++ bm bz1 := by
      simp only [recCells]; exact if_pos hp
    rw [hrc]
    exact hsel.trans hA
  · have hd : decide ((brecCells ns).length % 2 = 1) = false := by
      simp [hp]
    rw [hd] at hsel
    simp at hsel
    have hrc : recCells ns = brecCells ns := by
      simp only [recCells]; exact if_neg hp
    rw [hrc]
    exact hsel.trans (idBrec_eval ns)

/-- `LENB4·rec` — the padded record's byte count. -/
theorem idRl2_eval (ns : List (Fin 16)) :
    LRed (idRl2 (scottList (ns.map nibLit)))
      (scottList (bm (lenFoldT (recCells ns)))) := by
  simp only [idRl2]
  exact (LRed_app_right (idRec_eval ns)).trans
    (lenb4_eval _ (closed_recCells ns))

/-- `B4ADD <B 0x2000>·o` — hint/name RVA = offset + .idata base. -/
theorem idHrv_eval (o : LTerm) (bs : List (Fin 16 × Fin 16))
    (ho : LRed o (scottList (bs.map (fun p => byteLit p.1 p.2))))
    (hlen : b2000.length = bs.length) :
    LRed (idHrv o)
      (scottList ((resList b2000 bs 0).map
        (fun p => byteLit p.1 p.2))) := by
  simp only [idHrv]
  have h1 : LRed
      (.app (.app b4addL (bytesChunk b2000)) o)
      (aps b4addL [scottList (bm b2000),
                   scottList (bs.map (fun p => byteLit p.1 p.2))]) :=
    (LRed_app_left (LRed_app_right (bytesChunk_nf b2000))).trans
      (LRed_app_right ho)
  exact h1.trans (b4add_eval_scott _ _ hlen)

/-- `szn consB0 z` — Church-iterated `CONSS B0C` prepends `n`
    `b0cT`-thunks onto the zero-list.  `consB0L` is `zerostepL`. -/
theorem zChain_eval (n : Nat) (zs : List LTerm)
    (hzs : ∀ e ∈ zs, closed 0 e = true) :
    LRed (.app (.app (churchL n) consB0L) (scottList zs))
      (scottList (List.replicate n b0cT ++ zs)) := by
  have hstep : ∀ x, closed 0 x = true →
      LRed (.app consB0L x) (cellLit b0cT x) ∧
      closed 0 (cellLit b0cT x) = true :=
    fun x hx => ⟨zerostep_cell x hx,
      closed_cellLit closed_b0cT hx⟩
  have h3 : ∀ n : Nat,
      iterS (fun z => cellLit b0cT z) (scottList zs) n
      = scottList (List.replicate n b0cT ++ zs) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      show cellLit b0cT
          (iterS (fun z => cellLit b0cT z) (scottList zs) n)
        = scottList (List.replicate (n + 1) b0cT ++ zs)
      rw [ih]
      rfl
  have h1 := church_eval n consB0L (scottList zs)
    closed_consB0L (closed_scottList hzs)
  have h2 := iter_red consB0L (fun z => cellLit b0cT z) hstep n
    (scottList zs) (closed_scottList hzs)
  exact h1.trans ((h3 n) ▸ h2)

#print axioms incByteN_parity
#print axioms lenFold_parity
#print axioms nibPairUp_nibLit
#print axioms nibs2bytesB_length
#print axioms join_thunks_eval
#print axioms idBrec_eval
#print axioms idRln_eval
#print axioms idOdd_eval
#print axioms idRec_eval
#print axioms idRl2_eval
#print axioms idHrv_eval
#print axioms zChain_eval

-- ============================================================
-- Batch K layer 2: ILT/IDT/NAMS/DRVA/BODY section normalization.
-- ============================================================

-- Forall₂ plumbing ----------------------------------------------------

theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {xs xs' : List α} {ys ys' : List β}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ R xs' ys') :
    List.Forall₂ R (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => simpa using h'
  | cons hr _ ih =>
    simp only [List.cons_append]
    exact List.Forall₂.cons hr ih

theorem forall₂_reverse {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    List.Forall₂ R xs.reverse ys.reverse := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih =>
    rw [List.reverse_cons, List.reverse_cons]
    exact forall₂_append ih (List.Forall₂.cons hr List.Forall₂.nil)

-- per-element U64 thunk ------------------------------------------------

/-- `U64·e` on a thunk `e → scott(bm xs)` normalizes to the
    `xs ++ 4×00` cell list. -/
theorem u64_thunk_eval (e : LTerm) (xs : List (Fin 16 × Fin 16))
    (he : LRed e (scottList (xs.map (fun p => byteLit p.1 p.2)))) :
    LRed (.app u64L e)
      (scottList (xs.map (fun p => byteLit p.1 p.2)
        ++ List.replicate 4 b0cT)) :=
  (LRed_app_right he).trans (u64_eval_scott xs)

/-- Forall₂ lift across `map (u64L ·_)`: per-element thunk evals. -/
theorem forall₂_u64_thunks (rvs : List LTerm)
    (xv : List (List (Fin 16 × Fin 16)))
    (h : List.Forall₂ (fun e xs =>
      LRed e (scottList (xs.map (fun p => byteLit p.1 p.2))))
      rvs xv) :
    List.Forall₂ (fun t bs => LRed t (scottList bs))
      (rvs.map (fun e => .app u64L e))
      (xv.map (fun xs => xs.map (fun p => byteLit p.1 p.2)
        ++ List.replicate 4 b0cT)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih =>
    exact List.Forall₂.cons (u64_thunk_eval _ _ hr) ih

-- ILT/IAT --------------------------------------------------------------

/-- `ilt` cells: reversed per-import `u64` lists, `8×00` terminator. -/
def iltCells (xv : List (List (Fin 16 × Fin 16))) : List LTerm :=
  ((xv.map (fun xs => bm xs ++ List.replicate 4 b0cT)).reverse
    ++ [bm bZero8]).flatten

theorem closed_iltCells (xv : List (List (Fin 16 × Fin 16))) :
    ∀ e ∈ iltCells xv, closed 0 e = true := by
  intro e he
  simp only [iltCells] at he
  obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
  rcases List.mem_append.mp hw with hw | hw
  · rw [List.mem_reverse] at hw
    obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_append.mp hew with h2 | h2
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h2
      exact closed_byteLit _ _
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp h2
      exact closed_b0cT
  · simp only [List.mem_singleton] at hw
    rw [hw] at hew
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
    exact closed_byteLit _ _

/-- `JOIN (REV (conss (bytes 8×00) (MAP U64 rv)))`. -/
theorem idIlt_eval (rv : LTerm) (rvs : List LTerm)
    (xv : List (List (Fin 16 × Fin 16)))
    (hrv : LRed rv (scottList rvs))
    (hper : List.Forall₂ (fun e xs => LRed e (scottList (bm xs)))
      rvs xv)
    (hcl : ∀ e ∈ rvs, closed 0 e = true)
    (hrvc : closed 0 rv = true) :
    LRed (idIlt rv) (scottList (iltCells xv)) := by
  simp only [idIlt]
  have hmap := map_eval u64L rv rvs closed_u64L hrvc hcl hrv
  have hclm : ∀ e ∈ rvs.map (fun e => .app u64L e),
      closed 0 e = true := fun e he => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact closed_app closed_u64L (hcl x hx)
  have hcons : IsList
      (.app (.app conssL (bytesChunk bZero8))
        (.app (.app mapL u64L) rv))
      (bytesChunk bZero8 :: rvs.map (fun e => .app u64L e)) :=
    (LRed_app_right hmap).trans
      (conss_nf _ _ (closed_bytesChunk bZero8)
        (closed_scottList hclm))
  have hconssT : closed 0
      (.app (.app conssL (bytesChunk bZero8))
        (.app (.app mapL u64L) rv)) = true :=
    closed_app (closed_app closed_conssL (closed_bytesChunk bZero8))
      (closed_app (closed_app closed_mapL closed_u64L) hrvc)
  have hrev := revL_eval _ _ hconssT (fun e he => by
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact closed_bytesChunk bZero8
      · exact hclm e he)
    hcons
  rw [List.reverse_cons] at hrev
  have hF := forall₂_append (forall₂_reverse (forall₂_u64_thunks
      rvs xv hper))
    (List.Forall₂.cons (bytesChunk_nf bZero8) List.Forall₂.nil)
  have htcl : ∀ t ∈ (rvs.map (fun e => .app u64L e)).reverse
      ++ [bytesChunk bZero8], closed 0 t = true := by
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · rw [List.mem_reverse] at h
      exact hclm t h
    · simp only [List.mem_singleton] at h
      rw [h]; exact closed_bytesChunk bZero8
  show LRed (.app joinL (.app revL
      (.app (.app conssL (bytesChunk bZero8))
        (.app (.app mapL u64L) rv))))
      (scottList (iltCells xv))
  exact (LRed_app_right hrev).trans
    (join_thunks_eval _ _ hF (closed_iltCells xv) htcl)

-- NAMS -----------------------------------------------------------------

/-- `JOIN (REV rc)` — records reversed into the names area. -/
theorem idNams_eval (rc : LTerm) (rcs : List LTerm)
    (rbs : List (List LTerm))
    (hrc : LRed rc (scottList rcs))
    (hper : List.Forall₂ (fun e bs => LRed e (scottList bs)) rcs rbs)
    (hclf : ∀ e ∈ rbs.flatten, closed 0 e = true)
    (hclr : ∀ e ∈ rcs, closed 0 e = true)
    (hrcc : closed 0 rc = true) :
    LRed (idNams rc) (scottList rbs.reverse.flatten) := by
  simp only [idNams]
  have hrev := revL_eval rc rcs hrcc hclr hrc
  have hF : List.Forall₂ (fun t bs => LRed t (scottList bs))
      rcs.reverse rbs.reverse := forall₂_reverse hper
  have hrevcl : ∀ e ∈ rcs.reverse, closed 0 e = true :=
    fun e he => hclr e (List.mem_reverse.mp he)
  have hbcl : ∀ e ∈ rbs.reverse.flatten, closed 0 e = true :=
    fun e he => by
      obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
      exact hclf e (List.mem_flatten.mpr
        ⟨w, List.mem_reverse.mp hw, hew⟩)
  exact (LRed_app_right hrev).trans
    (join_thunks_eval _ _ hF hbcl hrevcl)

-- DRVA -----------------------------------------------------------------

/-- `drva = B4ADD <B 0x2000>·o` — same term as `idHrv`. -/
theorem idDrva_eval (o : LTerm) (bs : List (Fin 16 × Fin 16))
    (ho : LRed o (scottList (bs.map (fun p => byteLit p.1 p.2))))
    (hlen : b2000.length = bs.length) :
    LRed (idDrva o)
      (scottList ((resList b2000 bs 0).map
        (fun p => byteLit p.1 p.2))) :=
  idHrv_eval o bs ho hlen

theorem closed_idDrva {o : LTerm} (h : closed 0 o = true) :
    closed 0 (idDrva o) = true :=
  closed_app (closed_app closed_b4addL (closed_bytesChunk b2000)) h

theorem closed_idIlt {rv : LTerm} (h : closed 0 rv = true) :
    closed 0 (idIlt rv) = true := by
  show closed 0 (.app joinL (.app revL
    (.app (.app conssL (bytesChunk bZero8))
      (.app (.app mapL u64L) rv)))) = true
  exact closed_app closed_joinL (closed_app closed_revL
    (closed_app (closed_app closed_conssL (closed_bytesChunk bZero8))
      (closed_app (closed_app closed_mapL closed_u64L) h)))

theorem closed_idNams {rc : LTerm} (h : closed 0 rc = true) :
    closed 0 (idNams rc) = true :=
  closed_app closed_joinL (closed_app closed_revL h)

-- IDT ------------------------------------------------------------------

/-- `idt` cells: `[0x2028, 0, 0, drva, iat4, 20×00]` flattened. -/
def idtCells (os iat4 : List (Fin 16 × Fin 16)) : List LTerm :=
  [bm b2028, bm bZero4, bm bZero4, bm (resList b2000 os 0),
   bm iat4, List.replicate 20 b0cT].flatten

theorem closed_idtCells (os iat4 : List (Fin 16 × Fin 16)) :
    ∀ e ∈ idtCells os iat4, closed 0 e = true := by
  intro e he
  simp only [idtCells] at he
  obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
    exact closed_byteLit _ _
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
    exact closed_byteLit _ _
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
    exact closed_byteLit _ _
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
    exact closed_byteLit _ _
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
    exact closed_byteLit _ _
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hew
    exact closed_b0cT

theorem closed_idIdt {o : LTerm} (h : closed 0 o = true)
    (iat4 : List (Fin 16 × Fin 16)) :
    closed 0 (idIdt o iat4) = true := by
  show closed 0 (.app joinL (scottList
    [bytesChunk b2028, bytesChunk bZero4, bytesChunk bZero4,
     idDrva o, bytesChunk iat4,
     .app zerofillL (churchL 20)])) = true
  apply closed_app closed_joinL
  apply closed_scottList
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact closed_bytesChunk b2028
  · exact closed_bytesChunk bZero4
  · exact closed_bytesChunk bZero4
  · exact closed_idDrva h
  · exact closed_bytesChunk iat4
  · exact closed_app closed_zerofillL (closed_churchL 20)

/-- `JOIN [b4 0x2028, b4 0, b4 0, drva, iat4, ZEROFILL 20]`. -/
theorem idIdt_eval (o : LTerm) (os iat4 : List (Fin 16 × Fin 16))
    (ho : LRed o (scottList (os.map (fun p => byteLit p.1 p.2))))
    (hlen : b2000.length = os.length)
    (hoc : closed 0 o = true) :
    LRed (idIdt o iat4) (scottList (idtCells os iat4)) := by
  simp only [idIdt]
  have hF : List.Forall₂ (fun t bs => LRed t (scottList bs))
      [bytesChunk b2028, bytesChunk bZero4, bytesChunk bZero4,
       idDrva o, bytesChunk iat4, .app zerofillL (churchL 20)]
      [bm b2028, bm bZero4, bm bZero4, bm (resList b2000 os 0),
       bm iat4, List.replicate 20 b0cT] :=
    List.Forall₂.cons (bytesChunk_nf b2028)
      (List.Forall₂.cons (bytesChunk_nf bZero4)
        (List.Forall₂.cons (bytesChunk_nf bZero4)
          (List.Forall₂.cons (idDrva_eval o os ho hlen)
            (List.Forall₂.cons (bytesChunk_nf iat4)
              (List.Forall₂.cons
                (zerofill_num 20 (churchL 20) (churchL_num 20)
                  (closed_churchL 20))
                List.Forall₂.nil)))))
  have htcl : ∀ t ∈ [bytesChunk b2028, bytesChunk bZero4,
      bytesChunk bZero4, idDrva o, bytesChunk iat4,
      .app zerofillL (churchL 20)], closed 0 t = true := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact closed_bytesChunk b2028
    · exact closed_bytesChunk bZero4
    · exact closed_bytesChunk bZero4
    · exact closed_idDrva hoc
    · exact closed_bytesChunk iat4
    · exact closed_app closed_zerofillL (closed_churchL 20)
  show LRed (.app joinL (scottList
      [bytesChunk b2028, bytesChunk bZero4, bytesChunk bZero4,
       idDrva o, bytesChunk iat4, .app zerofillL (churchL 20)]))
      (scottList (idtCells os iat4))
  have h := join_thunks_eval _ _ hF (closed_idtCells os iat4) htcl
  -- join's RHS is `scottList (bss.flatten)` = `scottList (idtCells …)`
  exact h

-- BODY -----------------------------------------------------------------

theorem closed_idBody {o rv rc : LTerm}
    (ho : closed 0 o = true) (hrv : closed 0 rv = true)
    (hrc : closed 0 rc = true) (iat4 : List (Fin 16 × Fin 16)) :
    closed 0 (idBody o rv rc iat4) = true := by
  show closed 0 (.app joinL (scottList
    [idIdt o iat4, idIlt rv, idIlt rv, idNams rc,
     bytesChunk bKernel])) = true
  apply closed_app closed_joinL
  apply closed_scottList
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact closed_idIdt ho iat4
  · exact closed_idIlt hrv
  · exact closed_idIlt hrv
  · exact closed_idNams hrc
  · exact closed_bytesChunk bKernel

/-- `JOIN [idt, ilt, ilt, nams, kernel32.dll\x00]` — the .idata body. -/
theorem idBody_eval (o rv rc : LTerm)
    (os iat4 : List (Fin 16 × Fin 16))
    (xv : List (List (Fin 16 × Fin 16)))
    (rvs rcs : List LTerm) (rbs : List (List LTerm))
    (ho : LRed o (scottList (os.map (fun p => byteLit p.1 p.2))))
    (hlen : b2000.length = os.length)
    (hrv : LRed rv (scottList rvs))
    (hper : List.Forall₂ (fun e xs => LRed e (scottList (bm xs)))
      rvs xv)
    (hclv : ∀ e ∈ rvs, closed 0 e = true)
    (hrc : LRed rc (scottList rcs))
    (hper2 : List.Forall₂ (fun e bs => LRed e (scottList bs)) rcs rbs)
    (hclf : ∀ e ∈ rbs.flatten, closed 0 e = true)
    (hclr : ∀ e ∈ rcs, closed 0 e = true)
    (hoc : closed 0 o = true) (hrvc : closed 0 rv = true)
    (hrcc : closed 0 rc = true) :
    LRed (idBody o rv rc iat4)
      (scottList ([idtCells os iat4, iltCells xv, iltCells xv,
        rbs.reverse.flatten, bm bKernel].flatten)) := by
  simp only [idBody]
  have hF : List.Forall₂ (fun t bs => LRed t (scottList bs))
      [idIdt o iat4, idIlt rv, idIlt rv, idNams rc,
       bytesChunk bKernel]
      [idtCells os iat4, iltCells xv, iltCells xv,
       rbs.reverse.flatten, bm bKernel] :=
    List.Forall₂.cons (idIdt_eval o os iat4 ho hlen hoc)
      (List.Forall₂.cons
        (idIlt_eval rv rvs xv hrv hper hclv hrvc)
        (List.Forall₂.cons
          (idIlt_eval rv rvs xv hrv hper hclv hrvc)
          (List.Forall₂.cons
            (idNams_eval rc rcs rbs hrc hper2 hclf hclr hrcc)
            (List.Forall₂.cons (bytesChunk_nf bKernel)
              List.Forall₂.nil))))
  have htcl : ∀ t ∈ [idIdt o iat4, idIlt rv, idIlt rv, idNams rc,
      bytesChunk bKernel], closed 0 t = true := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact closed_idIdt hoc iat4
    · exact closed_idIlt hrvc
    · exact closed_idIlt hrvc
    · exact closed_idNams hrcc
    · exact closed_bytesChunk bKernel
  have hbcl : ∀ e ∈ [idtCells os iat4, iltCells xv, iltCells xv,
      rbs.reverse.flatten, bm bKernel].flatten,
      closed 0 e = true := by
    intro e he
    obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact closed_idtCells os iat4 e hew
    · exact closed_iltCells xv e hew
    · exact closed_iltCells xv e hew
    · obtain ⟨w2, hw2, hew2⟩ := List.mem_flatten.mp hew
      exact hclf e (List.mem_flatten.mpr
        ⟨w2, List.mem_reverse.mp hw2, hew2⟩)
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hew
      exact closed_byteLit _ _
  exact join_thunks_eval _ _ hF hbcl htcl

#print axioms forall₂_append
#print axioms forall₂_reverse
#print axioms u64_thunk_eval
#print axioms forall₂_u64_thunks
#print axioms idIlt_eval
#print axioms idNams_eval
#print axioms idDrva_eval
#print axioms idIdt_eval
#print axioms idBody_eval


-- ============================================================
-- Batch K layer 3: packL port + pack_eval assembly.
-- pack_src = λt.λi.λs.λr. LETS[idr, dat, idata=idr·K, datab=dat·K]
--   (pack_body) — the idata/datab lets are pre-composed into a
--   direct pack2L application spine (β-equivalent: pack2L already
--   binds idata/datab/stackres around the same packLets body).
-- ============================================================

-- K projection --------------------------------------------------

/-- `K a b → a` — unconditional (subst_shift_succ is exact
    hole-cancellation; no closedness needed). -/
theorem klL_apply2 (a b : LTerm) :
    LRed (aps klL [a, b]) a := by
  show LRed (.app (.app klL a) b) a
  exact LRed_of_hsteps (k := 2) (by
    simp [klL, hsteps, hstep, subst, subst_shift_succ])

/-- `PAIR a b · K →* a` — first projection. -/
theorem pairLit_fst (a b : LTerm) (ha : closed 0 a = true)
    (hb : closed 0 b = true) :
    LRed (.app (pairLit a b) klL) a :=
  (pairLit_apply a b klL ha hb).trans (klL_apply2 a b)

-- dataOf's z-component ------------------------------------------

/-- The z-component of a `dataStepSem` fold is a standalone fold:
    `z ↦ (szn·CONSB0)·z` per slot. -/
theorem dataStepSem_z : ∀ (es : List (LTerm × LTerm × LTerm))
    (st : LTerm × LTerm × LTerm),
    (es.foldl dataStepSem st).2.2 =
      es.foldl (fun z e => .app (.app e.2.1 consB0L) z) st.2.2 := by
  intro es; induction es with
  | nil => intro st; rfl
  | cons e es ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih (dataStepSem st e)]
    rfl

/-- z-cell semantics: sizes reversed, each contributing `n` zero
    cells.  (The foldl emits the LAST slot's padding first.) -/
def zCellsN (szs : List Nat) : List LTerm :=
  szs.reverse.flatMap (fun n => List.replicate n b0cT)

theorem closed_zCellsN (szs : List Nat) :
    ∀ e ∈ zCellsN szs, closed 0 e = true := by
  intro e he
  simp only [zCellsN, List.mem_flatMap, List.mem_reverse] at he
  obtain ⟨n, _, hn⟩ := he
  exact closed_rep_b0c hn

/-- The accumulated zero-chain normalizes: each `(churchL n)·CONSB0`
    prefix contributes `replicate n b0cT` cells. -/
theorem zFold_eval : ∀ (es : List (LTerm × LTerm × LTerm))
    (szs : List Nat) (init : LTerm) (ics : List LTerm),
    es.map (fun e => e.2.1) = szs.map churchL →
    LRed init (scottList ics) →
    (∀ e ∈ ics, closed 0 e = true) →
    (∀ e ∈ es, closed 0 e.2.1 = true) →
    LRed (es.foldl (fun z e => .app (.app e.2.1 consB0L) z) init)
         (scottList ((szs.reverse.flatMap
           (fun n => List.replicate n b0cT)) ++ ics)) := by
  intro es; induction es with
  | nil =>
    intro szs init ics hmap hinit hics _
    simp only [List.map_nil] at hmap
    have hszs : szs = [] := List.map_eq_nil_iff.mp hmap.symm
    subst hszs
    simp only [List.reverse_nil, List.flatMap_nil, List.nil_append,
               List.foldl_nil]
    exact hinit
  | cons e es' ih =>
    intro szs init ics hmap hinit hics hcl
    cases szs with
    | nil => simp at hmap
    | cons sz szs' =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hsz, hrest⟩ := hmap
      rw [List.foldl_cons]
      have hstep : LRed (.app (.app e.2.1 consB0L) init)
          (scottList (List.replicate sz b0cT ++ ics)) := by
        rw [hsz]
        exact (LRed_app_right hinit).trans
          (zChain_eval sz ics hics)
      have hcells : (sz :: szs').reverse.flatMap
          (fun n => List.replicate n b0cT) ++ ics
          = szs'.reverse.flatMap (fun n => List.replicate n b0cT)
            ++ (List.replicate sz b0cT ++ ics) := by
        simp only [List.reverse_cons, List.flatMap_append,
                   List.flatMap_cons, List.flatMap_nil,
                   List.append_nil]
        exact List.append_assoc _ _ _
      rw [hcells]
      exact ih szs' _ _ hrest hstep
        (fun x hx => by
          rcases List.mem_append.mp hx with h | h
          · exact closed_rep_b0c h
          · exact hics x h)
        (fun e' he' => hcl e' (List.mem_cons_of_mem _ he'))

/-- closedness of the whole `dataStepSem` fold. -/
theorem closed_dataFold : ∀ (es : List (LTerm × LTerm × LTerm))
    (st : LTerm × LTerm × LTerm),
    closed 0 st.1 = true → closed 0 st.2.1 = true →
    closed 0 st.2.2 = true →
    (∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.1 = true ∧
      closed 0 e.2.2 = true) →
    closed 0 (es.foldl dataStepSem st).1 = true ∧
    closed 0 (es.foldl dataStepSem st).2.1 = true ∧
    closed 0 (es.foldl dataStepSem st).2.2 = true := by
  intro es; induction es with
  | nil => intro st h1 h2 h3 _; exact ⟨h1, h2, h3⟩
  | cons e es ih =>
    intro st h1 h2 h3 hcl
    simp only [List.foldl_cons]
    exact ih (dataStepSem st e)
      (closed_dataStepSem h1 h2 h3
        (hcl e List.mem_cons_self).1
        (hcl e List.mem_cons_self).2.1
        (hcl e List.mem_cons_self).2.2).1
      (closed_dataStepSem h1 h2 h3
        (hcl e List.mem_cons_self).1
        (hcl e List.mem_cons_self).2.1
        (hcl e List.mem_cons_self).2.2).2.1
      (closed_dataStepSem h1 h2 h3
        (hcl e List.mem_cons_self).1
        (hcl e List.mem_cons_self).2.1
        (hcl e List.mem_cons_self).2.2).2.2
      (fun e' he' => hcl e' (List.mem_cons_of_mem _ he'))

theorem closed_dataFinal (es : List (LTerm × LTerm × LTerm))
    (hcl : ∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.1 = true ∧
      closed 0 e.2.2 = true) :
    closed 0 (dataFinal es).1 = true ∧
    closed 0 (dataFinal es).2.1 = true ∧
    closed 0 (dataFinal es).2.2 = true := by
  unfold dataFinal
  exact closed_dataFold es _
    (closed_bytesChunk b3000) closed_nilL closed_nilL hcl

/-- `dat·K` — the datab section: `dataOf`'s pair's first component,
    the accumulated zero-run. -/
theorem datK_eval (es : List (LTerm × LTerm × LTerm))
    (szs : List Nat)
    (hmap : es.map (fun e => e.2.1) = szs.map churchL)
    (hcl : ∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.1 = true ∧
      closed 0 e.2.2 = true) :
    LRed (.app (.app (dataOfL es.length)
          (scottList (es.map slotEnc))) klL)
         (scottList (zCellsN szs)) := by
  have hf := closed_dataFinal es hcl
  have hz0 : LRed
      (.app (.app (dataOfL es.length) (scottList (es.map slotEnc)))
        klL)
      ((dataFinal es).2.2) := by
    have h1 := dataOf_eval es hcl
    exact (LRed_app_left h1).trans
      (pairLit_fst _ _ hf.2.2 hf.2.1)
  have hz1 : (dataFinal es).2.2 =
      es.foldl (fun z e => .app (.app e.2.1 consB0L) z) nilL := by
    unfold dataFinal
    exact dataStepSem_z es _
  have hz2 : LRed
      (es.foldl (fun z e => .app (.app e.2.1 consB0L) z) nilL)
      (scottList ((szs.reverse.flatMap
        (fun n => List.replicate n b0cT)) ++ [])) :=
    zFold_eval es szs nilL [] hmap
      Relation.ReflTransGen.refl
      (fun e he => by simp at he)
      (fun e he => (hcl e he).2.1)
  rw [List.append_nil] at hz2
  rw [hz1] at hz0
  show LRed (.app (.app (dataOfL es.length)
        (scottList (es.map slotEnc))) klL)
      (scottList (zCellsN szs))
  simp only [zCellsN]
  exact hz0.trans hz2

-- idataFinal components -----------------------------------------

-- nm-generic evals: the leaf evals are stated for literal
-- `scottList (ns.map nibLit)` inputs; the fold carries thunk terms
-- `nm` with `LRed nm (scottList …)`.  Each `_of` replays the leaf
-- proof with the input reduction fed at the thunk position.

/-- `NIBS2BYTES·nm` on a reducible name. -/
theorem idNmb_of {nm : LTerm} {ns : List (Fin 16)}
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (_hc : closed 0 nm = true) :
    LRed (idNmb nm) (scottList (nibPairUp (ns.map nibLit))) := by
  simp only [idNmb]
  exact (LRed_app_right hnm).trans (nibs2bytes_eval _
    (fun e he => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      exact closed_nibLit i))

/-- `idBrec` on a reducible name. -/
theorem idBrec_of {nm : LTerm} {ns : List (Fin 16)}
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (hc : closed 0 nm = true) :
    LRed (idBrec nm) (scottList (brecCells ns)) := by
  simp only [idBrec, idNmb]
  have hcl : ∀ t ∈ [bytesChunk bz2,
      .app nibs2bytesL nm, bytesChunk bz1], closed 0 t = true := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact closed_bytesChunk bz2
    · exact closed_app closed_nibs2bytesL hc
    · exact closed_bytesChunk bz1
  have hf := join_thunks_eval
    [bytesChunk bz2, .app nibs2bytesL nm, bytesChunk bz1]
    [bm bz2, nibPairUp (ns.map nibLit), bm bz1]
    (List.Forall₂.cons (bytesChunk_nf bz2)
      (List.Forall₂.cons (idNmb_of hnm hc)
        (List.Forall₂.cons (bytesChunk_nf bz1) List.Forall₂.nil)))
    (closed_brecCells ns) hcl
  have hflat : [bm bz2, nibPairUp (ns.map nibLit), bm bz1].flatten
      = brecCells ns := by simp [List.flatten, brecCells]
  rwa [hflat] at hf

/-- `idRln` on a reducible name. -/
theorem idRln_of {nm : LTerm} {ns : List (Fin 16)}
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (hc : closed 0 nm = true) :
    LRed (idRln nm) (scottList (bm (lenFoldT (brecCells ns)))) := by
  simp only [idRln]
  have h := (LRed_app_right (idBrec_of hnm hc)).trans
    (lenb4_eval _ (closed_brecCells ns))
  simpa only [lenFoldT, bm] using h

/-- `idOdd` on a reducible name. -/
theorem idOdd_of {nm : LTerm} {ns : List (Fin 16)}
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (hc : closed 0 nm = true) :
    LRed (idOdd nm)
      (boolLit (decide ((brecCells ns).length % 2 = 1))) := by
  simp only [idOdd]
  have hln : (lenFoldT (brecCells ns)).length = 4 :=
    lenFold_len4 _ _ (by decide)
  obtain ⟨w0, w1, w2, w3, hws⟩ := exists_eq_of_length4 hln
  have hrln : LRed
      (.app (.app (idRln nm) nilL) idOddK)
      (.app (.app (scottList (bm (lenFoldT (brecCells ns)))) nilL)
        idOddK) :=
    LRed_app_left (LRed_app_left (idRln_of hnm hc))
  have hbm : bm (lenFoldT (brecCells ns)) =
      [byteLit w0.1 w0.2, byteLit w1.1 w1.2,
       byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
    rw [hws]; rfl
  have hpeel := idOdd_peel w0 w1 w2 w3
  rw [hbm] at hrln
  have hodd := (hrln.trans hpeel).trans (nibodd_eval w0.1)
  have hdef : ((0, 0) :: [(0, 0), (0, 0), (0, 0)] :
      List (Fin 16 × Fin 16)) = b4zeroBytes := rfl
  obtain ⟨p, hp1, hp2⟩ := lenFold_parity (brecCells ns)
    (0, 0) [(0, 0), (0, 0), (0, 0)]
  rw [hdef] at hp1
  have hp1' : (lenFoldT (brecCells ns)).head? = some p := hp1
  rw [hws] at hp1'
  have hp0 : p = w0 := (Option.some.inj hp1').symm
  have hpar : w0.1.val % 2 = (brecCells ns).length % 2 := by
    rw [hp0] at hp2
    simpa using hp2
  rw [← hpar]
  exact hodd

/-- `idRec` on a reducible name. -/
theorem idRec_of {nm : LTerm} {ns : List (Fin 16)}
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (hc : closed 0 nm = true) :
    LRed (idRec nm) (scottList (recCells ns)) := by
  simp only [idRec]
  have hb := closed_idBrec hc
  have hA : LRed
      (.app (.app appendL (idBrec nm)) (bytesChunk bz1))
      (scottList (brecCells ns ++ bm bz1)) :=
    (appendL_to_appendT _ _ hb (closed_bytesChunk bz1)).trans
      (append_eval _ _ _ _ (idBrec_of hnm hc)
        (bytesChunk_nf bz1) (closed_brecCells ns)
        (fun e he => by
          obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
          exact closed_byteLit _ _)
        hb (closed_bytesChunk bz1))
  have hsel : LRed
      (.app (.app (idOdd nm)
        (.app (.app appendL (idBrec nm)) (bytesChunk bz1)))
        (idBrec nm))
      (if decide ((brecCells ns).length % 2 = 1) = true
        then .app (.app appendL (idBrec nm)) (bytesChunk bz1)
        else idBrec nm) :=
    (LRed_app_left (LRed_app_left (idOdd_of hnm hc))).trans
      (boolLit_sel _ _ _)
  by_cases hp : (brecCells ns).length % 2 = 1
  · have hd : decide ((brecCells ns).length % 2 = 1) = true := by
      simp [hp]
    rw [hd] at hsel
    simp at hsel
    have hrc : recCells ns = brecCells ns ++ bm bz1 := by
      simp only [recCells]; exact if_pos hp
    rw [hrc]
    exact hsel.trans hA
  · have hd : decide ((brecCells ns).length % 2 = 1) = false := by
      simp [hp]
    rw [hd] at hsel
    simp at hsel
    have hrc : recCells ns = brecCells ns := by
      simp only [recCells]; exact if_neg hp
    rw [hrc]
    exact hsel.trans (idBrec_of hnm hc)

/-- `idRl2` on a reducible name — the o-fold's addend. -/
theorem idRl2_of {nm : LTerm} {ns : List (Fin 16)}
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (hc : closed 0 nm = true) :
    LRed (idRl2 nm)
      (scottList (bm (lenFoldT (recCells ns)))) := by
  simp only [idRl2]
  have h := (LRed_app_right (idRec_of hnm hc)).trans
    (lenb4_eval _ (closed_recCells ns))
  simpa only [lenFoldT, bm] using h

-- relations carried through the idata fold ---------------------

/-- rv thunk ↔ its byte image: `idHrv oT` with `oT →* <oB>` and
    `xs = resList b2000 oB`. -/
def rvRel (t : LTerm) (xs : List (Fin 16 × Fin 16)) : Prop :=
  ∃ oT oBs, t = idHrv oT ∧ xs = resList b2000 oBs 0 ∧
    LRed oT (scottList (bm oBs)) ∧ oBs.length = 4 ∧
    closed 0 oT = true

/-- rc thunk ↔ its cell image: `idRec nm` with `nm →* <ns>`. -/
def rcRel (t : LTerm) (bs : List LTerm) : Prop :=
  ∃ nm ns, t = idRec nm ∧ bs = recCells ns ∧
    LRed nm (scottList (ns.map nibLit)) ∧ closed 0 nm = true

/-- Flatten rvRel to the plain eval relation `idIlt_eval` needs. -/
theorem rvRel_eval {t : LTerm} {xs : List (Fin 16 × Fin 16)}
    (h : rvRel t xs) : LRed t (scottList (bm xs)) := by
  obtain ⟨oT, oBs, rfl, rfl, ho, hlen, _⟩ := h
  exact idHrv_eval oT oBs ho (by rw [hlen]; rfl)

theorem rvRel_closed {t : LTerm} {xs : List (Fin 16 × Fin 16)}
    (h : rvRel t xs) : closed 0 t = true := by
  obtain ⟨oT, _, rfl, _, _, _, hc⟩ := h
  exact closed_idHrv hc

/-- Flatten rcRel to the plain eval relation `idNams_eval` needs. -/
theorem rcRel_eval {t : LTerm} {bs : List LTerm} (h : rcRel t bs) :
    LRed t (scottList bs) := by
  obtain ⟨nm, ns, rfl, rfl, hnm, hc⟩ := h
  exact idRec_of hnm hc

theorem rcRel_closed {t : LTerm} {bs : List LTerm} (h : rcRel t bs) :
    closed 0 t = true := by
  obtain ⟨nm, _, rfl, _, _, hc⟩ := h
  exact closed_idRec hc

theorem rcRel_cells_closed {bs : List LTerm} {t : LTerm}
    (h : rcRel t bs) : ∀ e ∈ bs, closed 0 e = true := by
  obtain ⟨nm, ns, _, rfl, _, _⟩ := h
  exact closed_recCells ns

-- the joint fold -------------------------------------------------

/-- Semantic o-component: fold of `resList` over the per-import
    record lengths. -/
def oBytesOf (nsl : List (List (Fin 16)))
    (oB : List (Fin 16 × Fin 16)) : List (Fin 16 × Fin 16) :=
  nsl.foldl (fun a ns => resList a (lenFoldT (recCells ns)) 0) oB

/-- Semantic oi-component: `b8`-stride fold. -/
def oiBytesOf (nsl : List (List (Fin 16)))
    (oiB : List (Fin 16 × Fin 16)) : List (Fin 16 × Fin 16) :=
  nsl.foldl (fun a _ => resList a b8 0) oiB

/-- o-state terms at each step (scanl, length n+1). -/
def oScanT (es : List LTerm) (o : LTerm) : List LTerm :=
  es.scanl (fun a nm => aps b4addL [a, idRl2 nm]) o

/-- oi-state terms at each step. -/
def oiScanT (es : List LTerm) (oi : LTerm) : List LTerm :=
  es.scanl (fun a _ => aps b4addL [a, bytesChunk b8]) oi

/-- Semantic o-bytes at each step. -/
def oScanB (nsl : List (List (Fin 16))) (oB : List (Fin 16 × Fin 16))
    : List (List (Fin 16 × Fin 16)) :=
  nsl.scanl (fun a ns => resList a (lenFoldT (recCells ns)) 0) oB

/-- rv thunk cells added by the fold (newest-first): `idHrv` of the
    pre-step o-state. -/
def rvNew (es : List LTerm) (o : LTerm) : List LTerm :=
  ((es.zip (oScanT es o).dropLast).reverse).map
    (fun p => idHrv p.2)

/-- xv cells added — the rv thunks' byte images. -/
def xvNew (nsl : List (List (Fin 16))) (oB : List (Fin 16 × Fin 16))
    : List (List (Fin 16 × Fin 16)) :=
  ((nsl.zip (oScanB nsl oB).dropLast).reverse).map
    (fun p => resList b2000 p.2 0)

/-- rc thunk cells added (newest-first). -/
def rcNew (es : List LTerm) : List LTerm := es.reverse.map idRec

/-- rc semantic cells added. -/
def rbsNew (nsl : List (List (Fin 16))) : List (List LTerm) :=
  nsl.reverse.map recCells

/-- sy thunk cells added: `PAIR (prefix nm) oi` per import. -/
def syNew (es : List LTerm) (oi : LTerm) : List LTerm :=
  ((es.zip (oiScanT es oi).dropLast).reverse).map
    (fun p => aps pairSrcL [iatPrefix p.1, p.2])

-- list plumbing for the concrete cons-steps ---------------------

theorem dropLast_cons_ne {α : Type} (a : α) (l : List α)
    (h : l ≠ []) : (a :: l).dropLast = a :: l.dropLast := by
  cases l with
  | nil => exact absurd rfl h
  | cons b t => rfl

theorem scanl_ne_nil {α β : Type} (f : α → β → α) (es : List β)
    (a : α) : es.scanl f a ≠ [] := by
  cases es with
  | nil => simp [List.scanl]
  | cons b t => rw [List.scanl_cons]; simp

/-- cons-step for the zip-with-prestate-scan pattern:
    `(e::es)` zipped against its own scan keeps the pre-update
    accumulator `a` for `e`, so the newest cell is `g e a` LAST
    before reversal — i.e. first in the emitted order. -/
theorem zipScan_cons {α β γ : Type}
    (step : α → β → α) (g : β → α → γ)
    (e : β) (es : List β) (a : α) :
    (((e :: es).zip ((e :: es).scanl step a).dropLast).reverse).map
      (fun p => g p.1 p.2)
    = (((es.zip (es.scanl step (step a e)).dropLast).reverse).map
       (fun p => g p.1 p.2)) ++ [g e a] := by
  rw [List.scanl_cons,
      dropLast_cons_ne _ _ (scanl_ne_nil _ _ _),
      List.zip_cons_cons, List.reverse_cons, List.map_append]
  rfl

theorem rvNew_cons (e : LTerm) (es : List LTerm) (o : LTerm) :
    rvNew (e :: es) o
    = rvNew es (aps b4addL [o, idRl2 e]) ++ [idHrv o] := by
  simp only [rvNew, oScanT]
  exact zipScan_cons _ (fun _ a => idHrv a) _ _ _

theorem xvNew_cons (ns : List (Fin 16)) (nsl : List (List (Fin 16)))
    (oB : List (Fin 16 × Fin 16)) :
    xvNew (ns :: nsl) oB
    = xvNew nsl (resList oB (lenFoldT (recCells ns)) 0)
      ++ [resList b2000 oB 0] := by
  simp only [xvNew, oScanB]
  exact zipScan_cons _ (fun _ a => resList b2000 a 0) _ _ _

theorem syNew_cons (e : LTerm) (es : List LTerm) (oi : LTerm) :
    syNew (e :: es) oi
    = syNew es (aps b4addL [oi, bytesChunk b8])
      ++ [aps pairSrcL [iatPrefix e, oi]] := by
  simp only [syNew, oiScanT]
  exact zipScan_cons _ (fun nm a => aps pairSrcL [iatPrefix nm, a])
    _ _ _

theorem rcNew_cons (e : LTerm) (es : List LTerm) :
    rcNew (e :: es) = rcNew es ++ [idRec e] := by
  simp only [rcNew, List.reverse_cons, List.map_append,
             List.map_cons, List.map_nil]

theorem rbsNew_cons (ns : List (Fin 16)) (nsl : List (List (Fin 16))) :
    rbsNew (ns :: nsl) = rbsNew nsl ++ [recCells ns] := by
  simp only [rbsNew, List.reverse_cons, List.map_append,
             List.map_cons, List.map_nil]

theorem oBytesOf_cons (ns : List (Fin 16)) (nsl : List (List (Fin 16)))
    (oB : List (Fin 16 × Fin 16)) :
    oBytesOf (ns :: nsl) oB
    = oBytesOf nsl (resList oB (lenFoldT (recCells ns)) 0) := by
  simp only [oBytesOf, List.foldl_cons]

theorem oiBytesOf_cons (ns : List (Fin 16)) (nsl : List (List (Fin 16)))
    (oiB : List (Fin 16 × Fin 16)) :
    oiBytesOf (ns :: nsl) oiB = oiBytesOf nsl (resList oiB b8 0) := by
  simp only [oiBytesOf, List.foldl_cons]

/-- One coupled `idataStepSem` step, all five components.  The
    returned witnesses carry the prepended thunk cells (rv/rc/sy
    grow at the list head — the fold prepends, so newest-first). -/
theorem idataStep_eval
    (o oi rv rc sy : LTerm) (oB oiB : List (Fin 16 × Fin 16))
    (rvTs rcTs syTs : List LTerm)
    (xv : List (List (Fin 16 × Fin 16))) (rbs : List (List LTerm))
    (nm : LTerm) (ns : List (Fin 16))
    (hnm : LRed nm (scottList (ns.map nibLit)))
    (hclnm : closed 0 nm = true)
    (ho : LRed o (scottList (bm oB))) (hob : oB.length = 4)
    (hoi : LRed oi (scottList (bm oiB))) (hoib : oiB.length = 4)
    (hrv : LRed rv (scottList rvTs)) (hrc : LRed rc (scottList rcTs))
    (hsy : LRed sy (scottList syTs))
    (hFrv : List.Forall₂ rvRel rvTs xv)
    (hFrc : List.Forall₂ rcRel rcTs rbs)
    (hclv : ∀ e ∈ rvTs, closed 0 e = true)
    (hclr : ∀ e ∈ rcTs, closed 0 e = true)
    (hcls : ∀ e ∈ syTs, closed 0 e = true)
    (hoc : closed 0 o = true) (hoic : closed 0 oi = true)
    (hrvc : closed 0 rv = true) (hrcc : closed 0 rc = true)
    (hsyc : closed 0 sy = true) :
    let st' := idataStepSem (o, oi, rv, rc, sy) nm
    LRed st'.1
      (scottList (bm (resList oB (lenFoldT (recCells ns)) 0))) ∧
    (resList oB (lenFoldT (recCells ns)) 0).length = 4 ∧
    LRed st'.2.1 (scottList (bm (resList oiB b8 0))) ∧
    (resList oiB b8 0).length = 4 ∧
    LRed st'.2.2.1 (scottList (idHrv o :: rvTs)) ∧
    List.Forall₂ rvRel (idHrv o :: rvTs)
      (resList b2000 oB 0 :: xv) ∧
    LRed st'.2.2.2.1 (scottList (idRec nm :: rcTs)) ∧
    List.Forall₂ rcRel (idRec nm :: rcTs) (recCells ns :: rbs) ∧
    LRed st'.2.2.2.2
      (scottList (aps pairSrcL [iatPrefix nm, oi] :: syTs)) ∧
    closed 0 st'.1 = true ∧ closed 0 st'.2.1 = true ∧
    closed 0 st'.2.2.1 = true ∧ closed 0 st'.2.2.2.1 = true ∧
    closed 0 st'.2.2.2.2 = true := by
  show LRed _ _ ∧ _ ∧ _
  have hob' : (resList oB (lenFoldT (recCells ns)) 0).length = 4 := by
    rw [resList_length _ _ _ (by
      rw [hob]; exact (lenFold_len4 _ _ (by decide)).symm)]
    exact hob
  have hoib' : (resList oiB b8 0).length = 4 := by
    rw [resList_length _ _ _ (by rw [hoib]; rfl)]; exact hoib
  have hb4 : ∀ {A B : LTerm} {as bs : List (Fin 16 × Fin 16)},
      LRed A (scottList (bm as)) → LRed B (scottList (bm bs)) →
      as.length = bs.length →
      LRed (aps b4addL [A, B]) (scottList (bm (resList as bs 0))) := by
    intro A B as bs hA hB hl
    exact ((LRed_app_left (LRed_app_right hA)).trans
      (LRed_app_right hB)).trans (b4add_eval_scott as bs hl)
  have hrl2 := idRl2_of hnm hclnm
  refine ⟨?_, hob', ?_, hoib', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- o' = b4add o (idRl2 nm)
    exact hb4 ho hrl2 (by
      rw [hob]; exact (lenFold_len4 _ _ (by decide)).symm)
  · -- oi' = b4add oi <B8>
    exact hb4 hoi (bytesChunk_nf b8) (by rw [hoib]; rfl)
  · -- rv' = conss (idHrv o) rv
    show LRed (.app (.app conssL (idHrv o)) rv) _
    exact (LRed_app_right hrv).trans
      (conss_nf _ _ (closed_idHrv hoc)
        (closed_scottList hclv))
  · exact List.Forall₂.cons ⟨o, oB, rfl, rfl, ho, hob, hoc⟩ hFrv
  · -- rc' = conss (idRec nm) rc
    show LRed (.app (.app conssL (idRec nm)) rc) _
    exact (LRed_app_right hrc).trans
      (conss_nf _ _ (closed_idRec hclnm)
        (closed_scottList hclr))
  · exact List.Forall₂.cons ⟨nm, ns, rfl, rfl, hnm, hclnm⟩ hFrc
  · -- sy' = conss (pairSrc (prefix nm) oi) sy
    show LRed (.app (.app conssL (aps pairSrcL [iatPrefix nm, oi])) sy) _
    exact (LRed_app_right hsy).trans
      (conss_nf _ _
        (closed_app (closed_app closed_pairSrcL
          (closed_iatPrefix hclnm)) hoic)
        (closed_scottList hcls))
  · exact closed_app (closed_app closed_b4addL hoc)
      (closed_idRl2 hclnm)
  · exact closed_app (closed_app closed_b4addL hoic)
      (closed_bytesChunk b8)
  · exact closed_app (closed_app closed_conssL
      (closed_idHrv hoc)) hrvc
  · exact closed_app (closed_app closed_conssL
      (closed_idRec hclnm)) hrcc
  · exact closed_app (closed_app closed_conssL
      (closed_app (closed_app closed_pairSrcL
        (closed_iatPrefix hclnm)) hoic)) hsyc

/-- The full `idataStepSem` fold — all five component evals at once.
    Existential witnesses: `rvN`/`rcN`/`syN` are the newly prepended
    thunk cells (newest-first), `xvN`/`rbsN` their semantic images. -/
theorem idataFold_eval :
    ∀ (es : List LTerm) (nsl : List (List (Fin 16))),
    List.Forall₂ (fun nm ns =>
        LRed nm (scottList (ns.map nibLit))) es nsl →
    (∀ e ∈ es, closed 0 e = true) →
    ∀ (o oi rv rc sy : LTerm) (oB oiB : List (Fin 16 × Fin 16))
      (rvTs rcTs syTs : List LTerm)
      (xv : List (List (Fin 16 × Fin 16)))
      (rbs : List (List LTerm)),
    LRed o (scottList (bm oB)) → oB.length = 4 →
    LRed oi (scottList (bm oiB)) → oiB.length = 4 →
    LRed rv (scottList rvTs) → LRed rc (scottList rcTs) →
    LRed sy (scottList syTs) →
    List.Forall₂ rvRel rvTs xv → List.Forall₂ rcRel rcTs rbs →
    (∀ e ∈ rvTs, closed 0 e = true) →
    (∀ e ∈ rcTs, closed 0 e = true) →
    (∀ e ∈ syTs, closed 0 e = true) →
    closed 0 o = true → closed 0 oi = true →
    closed 0 rv = true → closed 0 rc = true →
    closed 0 sy = true →
    LRed (es.foldl idataStepSem (o, oi, rv, rc, sy)).1
      (scottList (bm (oBytesOf nsl oB))) ∧
    (oBytesOf nsl oB).length = 4 ∧
    LRed (es.foldl idataStepSem (o, oi, rv, rc, sy)).2.1
      (scottList (bm (oiBytesOf nsl oiB))) ∧
    (oiBytesOf nsl oiB).length = 4 ∧
    LRed (es.foldl idataStepSem (o, oi, rv, rc, sy)).2.2.1
      (scottList (rvNew es o ++ rvTs)) ∧
    List.Forall₂ rvRel (rvNew es o ++ rvTs) (xvNew nsl oB ++ xv) ∧
    LRed (es.foldl idataStepSem (o, oi, rv, rc, sy)).2.2.2.1
      (scottList (rcNew es ++ rcTs)) ∧
    List.Forall₂ rcRel (rcNew es ++ rcTs) (rbsNew nsl ++ rbs) ∧
    LRed (es.foldl idataStepSem (o, oi, rv, rc, sy)).2.2.2.2
      (scottList (syNew es oi ++ syTs)) ∧
    (∀ e ∈ syNew es oi, closed 0 e = true) ∧
    (∀ e ∈ rvNew es o, closed 0 e = true) ∧
    (∀ e ∈ rcNew es, closed 0 e = true) ∧
    (∀ e ∈ (rbsNew nsl).flatten, closed 0 e = true) := by
  intro es nsl hF
  induction hF with
  | nil =>
    intro _ o oi rv rc sy oB oiB rvTs rcTs syTs xv rbs
      ho hob hoi hoib hrv hrc hsy hFrv hFrc hclv hclr hcls
      hoc hoic hrvc hrcc hsyc
    refine ⟨ho, ?_, hoi, ?_, hrv, hFrv, hrc, hFrc, hsy, ?_, ?_, ?_, ?_⟩
    · exact hob
    · exact hoib
    · intro e he; simp [syNew, oiScanT, List.scanl] at he
    · intro e he; simp [rvNew, oScanT, List.scanl] at he
    · intro e he; simp [rcNew] at he
    · intro e he; simp [rbsNew] at he
  | cons hmnm hrest ih =>
    rename_i nm ns es' nsl'
    intro hclnm' o oi rv rc sy oB oiB rvTs rcTs syTs xv rbs
      ho hob hoi hoib hrv hrc hsy hFrv hFrc hclv hclr hcls
      hoc hoic hrvc hrcc hsyc
    have hclnm : closed 0 nm = true := hclnm' nm List.mem_cons_self
    have hstep := idataStep_eval o oi rv rc sy oB oiB rvTs rcTs syTs
      xv rbs nm ns hmnm hclnm ho hob hoi hoib hrv hrc hsy hFrv hFrc
      hclv hclr hcls hoc hoic hrvc hrcc hsyc
    obtain ⟨h1o, h1ob, h1oi, h1oib, h1rv, h1Frv, h1rc, h1Frc, h1sy,
            c1, c2, c3, c4, c5⟩ := hstep
    rw [List.foldl_cons]
    have ihh := ih (fun e he => hclnm' e (List.mem_cons_of_mem _ he))
      _ _ _ _ _ _ _ _ _ _ _ _ h1o h1ob h1oi h1oib h1rv h1rc h1sy
      h1Frv h1Frc
      (fun e he => by
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact closed_idHrv hoc
        · exact hclv e he)
      (fun e he => by
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact closed_idRec hclnm
        · exact hclr e he)
      (fun e he => by
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact closed_app (closed_app closed_pairSrcL
            (closed_iatPrefix hclnm)) hoic
        · exact hcls e he)
      c1 c2 c3 c4 c5
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12,
            f13⟩ := ihh
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [oBytesOf_cons]; exact f1
    · simp only [oBytesOf_cons]; exact f2
    · simp only [oiBytesOf_cons]; exact f3
    · simp only [oiBytesOf_cons]; exact f4
    · rw [rvNew_cons, List.append_assoc, List.singleton_append]
      exact f5
    · rw [rvNew_cons, xvNew_cons, List.append_assoc,
          List.singleton_append, List.append_assoc,
          List.singleton_append]
      exact f6
    · rw [rcNew_cons, List.append_assoc, List.singleton_append]
      exact f7
    · rw [rcNew_cons, rbsNew_cons, List.append_assoc,
          List.singleton_append, List.append_assoc,
          List.singleton_append]
      exact f8
    · rw [syNew_cons, List.append_assoc, List.singleton_append]
      exact f9
    · rw [syNew_cons]
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact f10 e h
      · simp only [List.mem_singleton] at h
        rw [h]
        exact closed_app (closed_app closed_pairSrcL
          (closed_iatPrefix hclnm)) hoic
    · rw [rvNew_cons]
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact f11 e h
      · simp only [List.mem_singleton] at h
        rw [h]; exact closed_idHrv hoc
    · rw [rcNew_cons]
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact f12 e h
      · simp only [List.mem_singleton] at h
        rw [h]; exact closed_idRec hclnm
    · rw [rbsNew_cons]
      intro e he
      obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
      rcases List.mem_append.mp hw with h | h
      · exact f13 e (List.mem_flatten.mpr ⟨w, h, hew⟩)
      · simp only [List.mem_singleton] at h
        rw [h] at hew
        exact closed_recCells ns e hew

/-- Forall₂ implication (parametric). -/
theorem forall₂_imp {α β : Type} {R S : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : ∀ a b, R a b → S a b) (hF : List.Forall₂ R xs ys) :
    List.Forall₂ S xs ys := by
  induction hF with
  | nil => exact List.Forall₂.nil
  | cons hhd htl ih => exact List.Forall₂.cons (h _ _ hhd) ih

/-- `(idataOf·imports)·K →* scottList (idata section cells)` — the
    `idr K` projection, folded state and `idBody` composed. -/
theorem idrK_eval (es : List LTerm) (nsl : List (List (Fin 16)))
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hF : List.Forall₂ (fun nm ns =>
        LRed nm (scottList (ns.map nibLit))) es nsl)
    (hcl : ∀ e ∈ es, closed 0 e = true)
    (hn4 : namesOff.length = 4) (hi4 : iatB.length = 4) :
    LRed (.app (.app (idataOfL es.length namesOff iatB iat4)
          (scottList es)) klL)
      (scottList ([idtCells (oBytesOf nsl namesOff) iat4,
        iltCells (xvNew nsl namesOff), iltCells (xvNew nsl namesOff),
        (rbsNew nsl).reverse.flatten, bm bKernel].flatten)) := by
  have hf := idataFold_eval es nsl hF hcl
    (bytesChunk namesOff) (bytesChunk iatB) nilL nilL nilL
    namesOff iatB [] [] [] [] []
    (bytesChunk_nf namesOff) hn4 (bytesChunk_nf iatB) hi4
    Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl
    List.Forall₂.nil List.Forall₂.nil
    (fun e he => by simp at he) (fun e he => by simp at he)
    (fun e he => by simp at he)
    (closed_bytesChunk namesOff) (closed_bytesChunk iatB)
    closed_nilL closed_nilL closed_nilL
  obtain ⟨ho, holen, _hoi, _hoilen, hrv, hFrv, hrc, hFrc, _hsy,
          _hsycl, hrvcl, hrccl, hrbcl⟩ := hf
  rw [List.append_nil] at hrv hFrv hrc hFrc
  rw [List.append_nil] at hFrv hFrc
  have hcf := closed_idataAfterK (es := es) (k := es.length)
    (o := bytesChunk namesOff) (oi := bytesChunk iatB)
    (rv := nilL) (rc := nilL) (sy := nilL)
    hcl (closed_bytesChunk namesOff) (closed_bytesChunk iatB)
    closed_nilL closed_nilL closed_nilL
  rw [List.take_length] at hcf
  obtain ⟨c1, _c2, c3, c4, c5⟩ := hcf
  have hId := idataOf_eval es namesOff iatB iat4 hcl
  have hproj : LRed (.app (.app (idataOfL es.length namesOff iatB iat4)
        (scottList es)) klL)
      (idBody (idataFinal es namesOff iatB).1
              (idataFinal es namesOff iatB).2.2.1
              (idataFinal es namesOff iatB).2.2.2.1 iat4) :=
    (LRed_app_left hId).trans
      (pairLit_fst _ _ (closed_idBody c1 c3 c4 iat4) c5)
  have hbody := idBody_eval _ _ _ (oBytesOf nsl namesOff) iat4
    (xvNew nsl namesOff) (rvNew es (bytesChunk namesOff))
    (rcNew es) (rbsNew nsl)
    ho (by rw [holen]; rfl) hrv
    (forall₂_imp (fun _ _ h => rvRel_eval h) hFrv) hrvcl
    hrc (forall₂_imp (fun _ _ h => rcRel_eval h) hFrc)
    hrbcl hrccl c1 c3 c4
  exact hproj.trans hbody

/-- The .idata section's cell image. -/
def idataCells (nsl : List (List (Fin 16)))
    (namesOff iat4 : List (Fin 16 × Fin 16)) : List LTerm :=
  [idtCells (oBytesOf nsl namesOff) iat4,
   iltCells (xvNew nsl namesOff), iltCells (xvNew nsl namesOff),
   (rbsNew nsl).reverse.flatten, bm bKernel].flatten

theorem closed_idataCells {nsl : List (List (Fin 16))}
    {namesOff iat4 : List (Fin 16 × Fin 16)}
    {e : LTerm} (he : e ∈ idataCells nsl namesOff iat4) :
    closed 0 e = true := by
  unfold idataCells at he
  obtain ⟨w, hw, hew⟩ := List.mem_flatten.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact closed_idtCells _ _ _ hew
  · exact closed_iltCells _ _ hew
  · exact closed_iltCells _ _ hew
  · obtain ⟨bs, hbs, hmem⟩ := List.mem_flatten.mp hew
    rw [List.mem_reverse] at hbs
    obtain ⟨ns, _, rfl⟩ := List.mem_map.mp hbs
    exact closed_recCells ns _ hmem
  · exact closed_bm hew

/-- `lenb4`'s count over an arbitrary cell list (cells = bytes). -/
def len4C (cs : List LTerm) : List (Fin 16 × Fin 16) :=
  cs.foldl (fun xs _ => incBytes xs true) b4zeroBytes

theorem len4C_length (cs : List LTerm) : (len4C cs).length = 4 := by
  have h : ∀ (xs : List LTerm) (acc : List (Fin 16 × Fin 16)),
      (xs.foldl (fun a _ => incBytes a true) acc).length
        = acc.length := by
    intro xs; induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, incBytes_length]
  rw [len4C, h]; rfl

/-- `pack2Cells` generalized to cell-list sections: `idata`/`datab`
    arrive as thunk-cell lists (their length still counts bytes). -/
def packCellsG (tb : List (Fin 16 × Fin 16)) (iC dC : List LTerm)
    (sb : List (Fin 16 × Fin 16)) : List (List LTerm) :=
  let ltB := len4 tb
  let liB := len4C iC
  let ldB := len4C dC
  let trawB := align512Bytes ltB
  let irawB := align512Bytes liB
  let drawB := align512Bytes ldB
  let iptrB := resList b200 trawB 0
  let dptrB := resList iptrB irawB 0
  let iddrB := resList irawB drawB 0
  let imgB := align4096Bytes (resList b3000 ldB 0)
  [ bm bMZ, List.replicate 58 b0cT, bm b40, bm bPE, bm bCOFF, bm b20B,
    bm trawB, bm iddrB,
    bm bZero4, bm b1000, bm b1000, bm bQ14, bm bAlign, bm bVers,
    bm bZero4, bm imgB, bm bII20, bm bSub,
    bm sb ++ List.replicate 4 b0cT,
    bm bStack, bm bDirs, bm bZero8, bm b2000,
    bm liB, List.replicate 112 b0cT, bm bText, bm ltB, bm b1000,
    bm trawB, bm b200, List.replicate 12 b0cT, bm bTextFl,
    bm bIdata, bm liB, bm b2000, bm irawB, bm iptrB,
    List.replicate 12 b0cT, bm bIdataFl, bm bData, bm ldB, bm b3000,
    bm drawB, bm dptrB, List.replicate 12 b0cT, bm bDataFl,
    List.replicate 64 b0cT,
    bm tb, padCells (padRemOf ltB), iC, padCells (padRemOf liB),
    dC, padCells (padRemOf ldB) ]

theorem closed_packCellsG_flat {e : LTerm} {tb iC dC sb}
    (hiC : ∀ x ∈ iC, closed 0 x = true)
    (hdC : ∀ x ∈ dC, closed 0 x = true)
    (he : e ∈ (packCellsG tb iC dC sb).flatten) :
    closed 0 e = true := by
  obtain ⟨cs, hcs, hm⟩ := List.mem_flatten.mp he
  simp only [packCellsG, List.mem_cons, List.not_mem_nil] at hcs
  repeat' (first | subst hcs | (obtain rfl | hcs := hcs))
  all_goals (first
    | exact closed_bm hm
    | exact closed_padCells hm
    | exact closed_rep_b0c hm
    | exact closed_bm_app_rep hm
    | exact hiC _ hm
    | exact hdC _ hm)

-- the packL port -------------------------------------------------
-- packOf's let chain: outer args at +4 under the 4 pre-lets.
-- Context inside packLetsP: datab=0, idata=1, dat=2, idr=3,
-- stackres=4, slots=5, imports=6, text=7.

def pltV : LTerm := .app lenb4L (.var 7)    -- lt = LENB4 text
def pliV : LTerm := .app lenb4L (.var 2)    -- li = LENB4 idata
def pldV : LTerm := .app lenb4L (.var 2)    -- ld = LENB4 datab

/-- `packChunks` at the deeper context: text→17, idata→11, datab→10,
    stackres→14; let-vars 0–9 unchanged. -/
def packChunksP : List LTerm := [
  bytesChunk bMZ,
  .app zerofillL nz58,
  bytesChunk b40,
  bytesChunk bPE,
  bytesChunk bCOFF,
  bytesChunk b20B,
  .var 6,
  .var 1,
  bytesChunk bZero4,
  bytesChunk b1000,
  bytesChunk b1000,
  bytesChunk bQ14,
  bytesChunk bAlign,
  bytesChunk bVers,
  bytesChunk bZero4,
  .var 0,
  bytesChunk bII20,
  bytesChunk bSub,
  .app u64L (.var 14),                     -- stackres
  bytesChunk bStack,
  bytesChunk bDirs,
  bytesChunk bZero8,
  bytesChunk b2000,
  .var 8,
  .app zerofillL nz112,
  bytesChunk bText,
  .var 9,
  bytesChunk b1000,
  .var 6,
  bytesChunk b200,
  .app zerofillL (churchL 12),
  bytesChunk bTextFl,
  bytesChunk bIdata,
  .var 8,
  bytesChunk b2000,
  .var 5,
  .var 3,
  .app zerofillL (churchL 12),
  bytesChunk bIdataFl,
  bytesChunk bData,
  .var 7,
  bytesChunk b3000,
  .var 4,
  .var 2,
  .app zerofillL (churchL 12),
  bytesChunk bDataFl,
  .app zerofillL nz64,
  .var 17,                                 -- text
  .app padlistL (.var 9),
  .var 11,                                 -- idata
  .app padlistL (.var 8),
  .var 10,                                 -- datab
  .app padlistL (.var 7)]

def packBodyP : LTerm :=
  .app joinL (packChunksP.foldr (fun c t => aps conssL [c, t]) nilL)

def packL9P : LTerm := .app (.abs packBodyP) imgV
def packL8P : LTerm := .app (.abs packL9P) iddrV
def packL7P : LTerm := .app (.abs packL8P) dptrV
def packL6P : LTerm := .app (.abs packL7P) iptrV
def packL5P : LTerm := .app (.abs packL6P) drawV
def packL4P : LTerm := .app (.abs packL5P) irawV
def packL3P : LTerm := .app (.abs packL4P) trawV
def packL2P : LTerm := .app (.abs packL3P) pldV
def packL1P : LTerm := .app (.abs packL2P) pliV
def packLetsP : LTerm := .app (.abs packL1P) pltV

/-- The 4 pre-lets of `packOf`, innermost-last (same idiom as
    `packL1`–`packL9`): `datab = dat·K`, `idata = idr·K`,
    `dat = dataOf slots`, `idr = idataOf imports`. -/
def packP3 : LTerm :=
  .app (.abs packLetsP) (.app (.var 1) klL)          -- datab = dat·K
def packP2 : LTerm :=
  .app (.abs packP3) (.app (.var 1) klL)             -- idata = idr·K
def packP1 (nSlot : Nat) : LTerm :=
  .app (.abs packP2) (.app (dataOfL nSlot) (.var 2)) -- dat = dataOf slots
def packP0 (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16)) : LTerm :=
  .app (.abs (packP1 nSlot))
    (.app (idataOfL nImp namesOff iatB iat4) (.var 2))
                                                   -- idr = idataOf imports
/-- `packOf n_imp n_slot namesOff iatB iat4 =
    λtext. λimports. λslots. λstackres. <pre-lets + pack body>`. -/
def packL (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16)) : LTerm :=
  .abs (.abs (.abs (.abs (packP0 nImp nSlot namesOff iatB iat4))))

set_option maxHeartbeats 8000000 in
/-- The 18-β milestone: `packL` applied to closed section inputs opens
    to `JOIN` over the instantiated chunk chain, with `idata`/`datab`
    the `·K` projections of the section builders. -/
theorem pack_open (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (T I D S : LTerm)
    (hT : closed 0 T = true) (hI : closed 0 I = true)
    (hD : closed 0 D = true) (hS : closed 0 S = true) :
    LRed (aps (packL nImp nSlot namesOff iatB iat4) [T, I, D, S])
      (.app joinL (chunkChain (packChunksInst T
        (.app (.app (idataOfL nImp namesOff iatB iat4) I) klL)
        (.app (.app (dataOfL nSlot) D) klL) S))) :=
  LRed_of_hsteps (k := 18) (by
    simp [packL, packP0, packP1, packP2, packP3, packLetsP,
          packL1P, packL2P, packL3P, packL4P,
          packL5P, packL6P, packL7P, packL8P, packL9P, packBodyP,
          packChunksP, packChunksInst, chunkChain,
          pltV, pliV, pldV, trawV, irawV, drawV, iptrV, dptrV,
          iddrV, imgV,
          bytesChunk, bMZ, b40, bPE, bCOFF, b20B, bZero4, b1000, bQ14,
          bAlign, bVers, bII20, bSub, bStack, bDirs, bZero8, b2000,
          bText, b200, bTextFl, bIdata, bIdataFl, bData, b3000,
          bDataFl, nz58, nz64, nz112,
          aps, List.foldl, List.foldr,
          hsteps, hstep, subst, shift,
          subst_of_closed0, shift_of_closed0,
          closed_mono,
          hT, hI, hD, hS,
          closed_lenb4L_any, closed_align512L_any,
          closed_align4096L_any, closed_b4addL_any, closed_u64L_any,
          closed_padlistL_any, closed_zerofillL_any, closed_joinL_any,
          closed_conssL_any, closed_pairSrcL_any, closed_nibLit_any,
          closed_churchL_any, closed_churchMulL_any,
          closed_churchAddL_any,
          closed_klL_any, closed_nilL_any,
          closed_idataOfL, closed_dataOfL])

set_option maxHeartbeats 8000000 in
/-- `pack_eval`: `packL` applied to raw section inputs produces the
    full PE image — `idata`/`datab` are the `·K`-projected section
    builders, normalized through `idrK_eval`/`datK_eval`. -/
theorem pack_eval (tb : List (Fin 16 × Fin 16))
    (es : List LTerm) (nsl : List (List (Fin 16)))
    (slots : List (LTerm × LTerm × LTerm)) (szs : List Nat)
    (sb namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hF : List.Forall₂ (fun nm ns =>
        LRed nm (scottList (ns.map nibLit))) es nsl)
    (hcle : ∀ e ∈ es, closed 0 e = true)
    (hmap : slots.map (fun e => e.2.1) = szs.map churchL)
    (hcls : ∀ e ∈ slots, closed 0 e.1 = true ∧
        closed 0 e.2.1 = true ∧ closed 0 e.2.2 = true)
    (hn4 : namesOff.length = 4) (hi4 : iatB.length = 4) :
    LRed (aps (packL es.length slots.length namesOff iatB iat4)
          [scottList (bm tb), scottList es,
           scottList (slots.map slotEnc), scottList (bm sb)])
      (scottList (packCellsG tb (idataCells nsl namesOff iat4)
        (zCellsN szs) sb).flatten) := by
  have hclT : ∀ e ∈ bm tb, closed 0 e = true := fun _ h => closed_bm h
  have hclI : ∀ e ∈ idataCells nsl namesOff iat4, closed 0 e = true :=
    fun _ h => closed_idataCells h
  have hclD : ∀ e ∈ zCellsN szs, closed 0 e = true :=
    fun _ h => closed_zCellsN szs _ h
  have hclS : ∀ e ∈ bm sb, closed 0 e = true := fun _ h => closed_bm h
  have hscT : closed 0 (scottList (bm tb)) = true :=
    closed_scottList hclT
  have hscI : closed 0 (scottList es) = true := closed_scottList hcle
  have hscD : closed 0 (scottList (slots.map slotEnc)) = true :=
    closed_scottList (fun x hx => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2, h3⟩ := hcls e' he'
      exact closed_slotEnc h1 h2 h3)
  have hscS : closed 0 (scottList (bm sb)) = true :=
    closed_scottList hclS
  -- the two `·K` projections normalize to their cell images
  have hIV : LRed (.app (.app (idataOfL es.length namesOff iatB iat4)
        (scottList es)) klL)
      (scottList (idataCells nsl namesOff iat4)) := by
    have h := idrK_eval es nsl namesOff iatB iat4 hF hcle hn4 hi4
    simpa only [idataCells] using h
  have hDV : LRed (.app (.app (dataOfL slots.length)
        (scottList (slots.map slotEnc))) klL)
      (scottList (zCellsN szs)) :=
    datK_eval slots szs hmap hcls
  -- LENB4 legs
  have hlt : LRed (.app lenb4L (scottList (bm tb)))
      (scottList (bm (len4 tb))) := by
    have h := lenb4_eval (bm tb) hclT
    simp only [bm] at h
    rw [foldl_const_step_map] at h
    exact h
  have hli : LRed (.app lenb4L (.app (.app (idataOfL es.length
        namesOff iatB iat4) (scottList es)) klL))
      (scottList (bm (len4C (idataCells nsl namesOff iat4)))) := by
    have h := (LRed_app_right hIV).trans
      (lenb4_eval _ hclI)
    simpa only [bm, len4C] using h
  have hld : LRed (.app lenb4L (.app (.app (dataOfL slots.length)
        (scottList (slots.map slotEnc))) klL))
      (scottList (bm (len4C (zCellsN szs)))) := by
    have h := (LRed_app_right hDV).trans (lenb4_eval _ hclD)
    simpa only [bm, len4C] using h
  -- lengths
  have hlt4 : (len4 tb).length = 4 := len4_length tb
  have hli4 : (len4C (idataCells nsl namesOff iat4)).length = 4 :=
    len4C_length _
  have hld4 : (len4C (zCellsN szs)).length = 4 := len4C_length _
  have htraw4 : (align512Bytes (len4 tb)).length = 4 :=
    align512Bytes_length _ hlt4
  have hiraw4 :
      (align512Bytes (len4C (idataCells nsl namesOff iat4))).length = 4
      := align512Bytes_length _ hli4
  have hdraw4 : (align512Bytes (len4C (zCellsN szs))).length = 4 :=
    align512Bytes_length _ hld4
  have hiptr4 : (resList b200 (align512Bytes (len4 tb)) 0).length = 4
      := by
    rw [resList_length _ _ _ (by rw [htraw4]; rfl),
        show b200.length = 4 from rfl]
  -- ALIGN legs
  have htraw : LRed (.app align512L (scottList (bm (len4 tb))))
      (scottList (bm (align512Bytes (len4 tb)))) := by
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align512_eval_scott (len4 tb) hlt4
    have heq : bm (align512Bytes (len4 tb)) =
        [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
         byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
      simp [align512Bytes, hws, bm]
    rw [heq]; exact hred
  have hiraw : LRed (.app align512L
        (scottList (bm (len4C (idataCells nsl namesOff iat4)))))
      (scottList (bm (align512Bytes
        (len4C (idataCells nsl namesOff iat4))))) := by
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align512_eval_scott (len4C (idataCells nsl namesOff iat4)) hli4
    have heq : bm (align512Bytes (len4C (idataCells nsl namesOff iat4)))
        = [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
           byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
      simp [align512Bytes, hws, bm]
    rw [heq]; exact hred
  have hdraw : LRed (.app align512L
        (scottList (bm (len4C (zCellsN szs)))))
      (scottList (bm (align512Bytes (len4C (zCellsN szs))))) := by
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align512_eval_scott (len4C (zCellsN szs)) hld4
    have heq : bm (align512Bytes (len4C (zCellsN szs))) =
        [byteLit 0 0, byteLit (nibMaskE w1.1) w1.2,
         byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
      simp [align512Bytes, hws, bm]
    rw [heq]; exact hred
  -- B4ADD congruence helper
  have hb4add : ∀ {A B : LTerm} {as bs : List (Fin 16 × Fin 16)},
      LRed A (scottList (bm as)) → LRed B (scottList (bm bs)) →
      as.length = bs.length →
      LRed (aps b4addL [A, B])
        (scottList (bm (resList as bs 0))) := by
    intro A B as bs hA hB hl
    exact ((LRed_app_left (LRed_app_right hA)).trans
      (LRed_app_right hB)).trans (b4add_eval_scott as bs hl)
  -- composed let-value legs
  have htrawT : LRed (.app align512L (.app lenb4L (scottList (bm tb))))
      (scottList (bm (align512Bytes (len4 tb)))) :=
    (LRed_app_right hlt).trans htraw
  have hirawT : LRed (.app align512L (.app lenb4L
        (.app (.app (idataOfL es.length namesOff iatB iat4)
          (scottList es)) klL)))
      (scottList (bm (align512Bytes
        (len4C (idataCells nsl namesOff iat4))))) :=
    (LRed_app_right hli).trans hiraw
  have hdrawT : LRed (.app align512L (.app lenb4L
        (.app (.app (dataOfL slots.length)
          (scottList (slots.map slotEnc))) klL)))
      (scottList (bm (align512Bytes (len4C (zCellsN szs))))) :=
    (LRed_app_right hld).trans hdraw
  have hiptrT : LRed (aps b4addL [bytesChunk b200,
        .app align512L (.app lenb4L (scottList (bm tb)))])
      (scottList (bm (resList b200 (align512Bytes (len4 tb)) 0))) :=
    hb4add (bytesChunk_nf b200) htrawT (by rw [htraw4]; rfl)
  have hdptrT : LRed (aps b4addL [aps b4addL [bytesChunk b200,
        .app align512L (.app lenb4L (scottList (bm tb)))],
        .app align512L (.app lenb4L
          (.app (.app (idataOfL es.length namesOff iatB iat4)
            (scottList es)) klL))])
      (scottList (bm (resList (resList b200 (align512Bytes (len4 tb)) 0)
        (align512Bytes (len4C (idataCells nsl namesOff iat4))) 0))) :=
    hb4add hiptrT hirawT (by rw [hiptr4, hiraw4])
  have hiddrT : LRed (aps b4addL
        [.app align512L (.app lenb4L
          (.app (.app (idataOfL es.length namesOff iatB iat4)
            (scottList es)) klL)),
         .app align512L (.app lenb4L
          (.app (.app (dataOfL slots.length)
            (scottList (slots.map slotEnc))) klL))])
      (scottList (bm (resList
        (align512Bytes (len4C (idataCells nsl namesOff iat4)))
        (align512Bytes (len4C (zCellsN szs))) 0))) :=
    hb4add hirawT hdrawT (by rw [hiraw4, hdraw4])
  have himgT : LRed (.app align4096L (aps b4addL [bytesChunk b3000,
        .app lenb4L (.app (.app (dataOfL slots.length)
          (scottList (slots.map slotEnc))) klL)]))
      (scottList (bm (align4096Bytes
        (resList b3000 (len4C (zCellsN szs)) 0)))) := by
    have hpre : LRed (aps b4addL [bytesChunk b3000,
          .app lenb4L (.app (.app (dataOfL slots.length)
            (scottList (slots.map slotEnc))) klL)])
        (scottList (bm (resList b3000 (len4C (zCellsN szs)) 0))) :=
      hb4add (bytesChunk_nf b3000) hld (by rw [hld4]; rfl)
    have hlen4' : (resList b3000 (len4C (zCellsN szs)) 0).length = 4
        := by
      rw [resList_length _ _ _ (by rw [hld4]; rfl)]
      rfl
    obtain ⟨w0, w1, w2, w3, hws, hred⟩ :=
      align4096_eval_scott (resList b3000 (len4C (zCellsN szs)) 0)
        hlen4'
    have h2 : LRed (.app align4096L (scottList (bm (resList b3000
          (len4C (zCellsN szs)) 0))))
        (scottList (bm (align4096Bytes
          (resList b3000 (len4C (zCellsN szs)) 0)))) := by
      have heq : bm (align4096Bytes (resList b3000
            (len4C (zCellsN szs)) 0)) =
          [byteLit 0 0, byteLit 0 w1.2,
           byteLit w2.1 w2.2, byteLit w3.1 w3.2] := by
        simp [align4096Bytes, hws, bm]
      rw [heq]; exact hred
    exact (LRed_app_right hpre).trans h2
  -- PADLIST legs
  have hpadT : LRed (.app padlistL (.app lenb4L (scottList (bm tb))))
      (scottList (padCells (padRemOf (len4 tb)))) := by
    obtain ⟨x0, x1, x2, x3, hx⟩ := exists_eq_of_length4 hlt4
    have h2 : LRed (.app padlistL (scottList (bm (len4 tb))))
        (scottList (padCells (padRemOf (len4 tb)))) := by
      have heq : bm (len4 tb) =
          [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        rw [hx]; rfl
      have heq2 : padCells (padRemOf (len4 tb)) =
          padCells (padRemN x0 x1) := by
        rw [hx]; rfl
      rw [heq, heq2]; exact padlist_eval_scott x0 x1 x2 x3
    exact (LRed_app_right hlt).trans h2
  have hpadI : LRed (.app padlistL (.app lenb4L
        (.app (.app (idataOfL es.length namesOff iatB iat4)
          (scottList es)) klL)))
      (scottList (padCells (padRemOf
        (len4C (idataCells nsl namesOff iat4))))) := by
    obtain ⟨x0, x1, x2, x3, hx⟩ := exists_eq_of_length4 hli4
    have h2 : LRed (.app padlistL (scottList
          (bm (len4C (idataCells nsl namesOff iat4)))))
        (scottList (padCells (padRemOf
          (len4C (idataCells nsl namesOff iat4))))) := by
      have heq : bm (len4C (idataCells nsl namesOff iat4)) =
          [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        rw [hx]; rfl
      have heq2 : padCells (padRemOf (len4C
            (idataCells nsl namesOff iat4))) =
          padCells (padRemN x0 x1) := by
        rw [hx]; rfl
      rw [heq, heq2]; exact padlist_eval_scott x0 x1 x2 x3
    exact (LRed_app_right hli).trans h2
  have hpadD : LRed (.app padlistL (.app lenb4L
        (.app (.app (dataOfL slots.length)
          (scottList (slots.map slotEnc))) klL)))
      (scottList (padCells (padRemOf (len4C (zCellsN szs))))) := by
    obtain ⟨x0, x1, x2, x3, hx⟩ := exists_eq_of_length4 hld4
    have h2 : LRed (.app padlistL (scottList
          (bm (len4C (zCellsN szs)))))
        (scottList (padCells (padRemOf (len4C (zCellsN szs))))) := by
      have heq : bm (len4C (zCellsN szs)) =
          [byteLit x0.1 x0.2, byteLit x1.1 x1.2,
           byteLit x2.1 x2.2, byteLit x3.1 x3.2] := by
        rw [hx]; rfl
      have heq2 : padCells (padRemOf (len4C (zCellsN szs))) =
          padCells (padRemN x0 x1) := by
        rw [hx]; rfl
      rw [heq, heq2]; exact padlist_eval_scott x0 x1 x2 x3
    exact (LRed_app_right hld).trans h2
  -- ZEROFILL chunks
  have hZF58 : LRed (.app zerofillL nz58)
      (scottList (List.replicate 58 b0cT)) :=
    zerofill_num 58 nz58 nz58_num closed_nz58
  have hZF64 : LRed (.app zerofillL nz64)
      (scottList (List.replicate 64 b0cT)) :=
    zerofill_num 64 nz64 nz64_num closed_nz64
  have hZF112 : LRed (.app zerofillL nz112)
      (scottList (List.replicate 112 b0cT)) :=
    zerofill_num 112 nz112 nz112_num closed_nz112
  have hZF12 : LRed (.app zerofillL (churchL 12))
      (scottList (List.replicate 12 b0cT)) :=
    zerofill_num 12 (churchL 12) (churchL_num 12) (closed_churchL 12)
  -- the 53-chunk Forall₂
  have hForall : List.Forall₂ LRed
      (packChunksInst (scottList (bm tb))
        (.app (.app (idataOfL es.length namesOff iatB iat4)
          (scottList es)) klL)
        (.app (.app (dataOfL slots.length)
          (scottList (slots.map slotEnc))) klL)
        (scottList (bm sb)))
      ((packCellsG tb (idataCells nsl namesOff iat4)
        (zCellsN szs) sb).map scottList) := by
    simp only [packChunksInst, packCellsG, idataCells,
               List.map_cons, List.map_nil]
    repeat' (first | apply List.Forall₂.nil | apply List.Forall₂.cons)
    all_goals first
      | exact hZF58 | exact hZF64 | exact hZF112 | exact hZF12
      | exact hlt | exact hli | exact hld
      | exact htrawT | exact hirawT | exact hdrawT
      | exact hiptrT | exact hdptrT | exact hiddrT | exact himgT
      | exact hpadT | exact hpadI | exact hpadD
      | exact hIV | exact hDV
      | exact u64_eval_scott _
      | exact bytesChunk_nf _
      | exact Relation.ReflTransGen.refl
  -- chain collapse + join
  have hflat : ∀ e ∈ (packCellsG tb (idataCells nsl namesOff iat4)
        (zCellsN szs) sb).flatten, closed 0 e = true :=
    fun _ h => closed_packCellsG_flat hclI hclD h
  have hcells : ∀ e ∈ (packCellsG tb (idataCells nsl namesOff iat4)
        (zCellsN szs) sb).map scottList, closed 0 e = true := by
    intro e he
    obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp he
    exact closed_scottList (fun x hx =>
      hflat x (List.mem_flatten.mpr ⟨bs, hbs, hx⟩))
  have hchain : LRed (chunkChain (packChunksInst (scottList (bm tb))
        (.app (.app (idataOfL es.length namesOff iatB iat4)
          (scottList es)) klL)
        (.app (.app (dataOfL slots.length)
          (scottList (slots.map slotEnc))) klL)
        (scottList (bm sb))))
      (scottList ((packCellsG tb (idataCells nsl namesOff iat4)
        (zCellsN szs) sb).map scottList)) :=
    (conssChain_map_red hForall).trans (conssChain_nf _ hcells)
  exact ((pack_open es.length slots.length namesOff iatB iat4
        _ _ _ _ hscT hscI hscD hscS).trans
    (LRed_app_right hchain)).trans (join_eval _ hflat)

#print axioms idrK_eval
#print axioms pack_open
#print axioms pack_eval
#print axioms idataFold_eval
#print axioms idataStep_eval



-- ============================================================
-- Batch L: linkOf — link_src = λimports. λslots.
--   let idr = idataOf imports; let dat = dataOf slots;
--   PAIR (PAIR (idr K) (dat K)) (APPEND (idr KI) (dat KI)).
-- Layer 1: KI-projection, dataFinal u-component fold, link_open.
-- ============================================================

/-- `KI a b → b` — unconditional. -/
theorem kilL_apply2 (a b : LTerm) :
    LRed (aps kilL [a, b]) b := by
  show LRed (.app (.app kilL a) b) b
  exact LRed_of_hsteps (k := 2) (by
    simp [kilL, hsteps, hstep, subst, shift_zero])

/-- `PAIR a b · KI →* b` — second projection. -/
theorem pairLit_snd (a b : LTerm) (ha : closed 0 a = true)
    (hb : closed 0 b = true) :
    LRed (.app (pairLit a b) kilL) b :=
  (pairLit_apply a b kilL ha hb).trans (kilL_apply2 a b)

-- dataOf's u-component (symbol table: PAIR nm offset) -------------

/-- dataOf o-state terms at each step: `b4add` over `e.2.2`. -/
def oScanD (es : List (LTerm × LTerm × LTerm)) (o : LTerm) :
    List LTerm :=
  es.scanl (fun a e => aps b4addL [a, e.2.2]) o

/-- u thunk cells added by the fold (newest-first): `PAIR nm o_pre`. -/
def uNewD (es : List (LTerm × LTerm × LTerm)) (o : LTerm) :
    List LTerm :=
  ((es.zip (oScanD es o).dropLast).reverse).map
    (fun p => aps pairSrcL [p.1.1, p.2])

theorem uNewD_cons (e : LTerm × LTerm × LTerm)
    (es : List (LTerm × LTerm × LTerm)) (o : LTerm) :
    uNewD (e :: es) o
    = uNewD es (aps b4addL [o, e.2.2])
      ++ [aps pairSrcL [e.1, o]] := by
  simp only [uNewD, oScanD]
  exact zipScan_cons _
    (fun (e' : LTerm × LTerm × LTerm) a => aps pairSrcL [e'.1, a])
    _ _ _

/-- The `(o,u)` pair as a standalone fold state — the `z`-component
    dropped. -/
def ouStepD (st : LTerm × LTerm) (e : LTerm × LTerm × LTerm) :
    LTerm × LTerm :=
  (aps b4addL [st.1, e.2.2],
   aps conssL [aps pairSrcL [e.1, st.1], st.2])

/-- The u-component of a `dataStepSem` fold is the standalone
    `ouStepD` fold's second projection. -/
theorem dataStepSem_u : ∀ (es : List (LTerm × LTerm × LTerm))
    (st : LTerm × LTerm × LTerm),
    (es.foldl dataStepSem st).2.1 =
      (es.foldl ouStepD (st.1, st.2.1)).2 := by
  intro es; induction es with
  | nil => intro st; rfl
  | cons e es ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih (dataStepSem st e)]
    rfl

/-- The `ouStepD` fold's u-projection evaluates to the `uNewD` cell
    list prepended to the initial cells. -/
theorem uFold_eval : ∀ (es : List (LTerm × LTerm × LTerm))
    (o u : LTerm) (ics : List LTerm),
    LRed u (scottList ics) →
    (∀ c ∈ ics, closed 0 c = true) →
    closed 0 o = true →
    (∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.2 = true) →
    LRed ((es.foldl ouStepD (o, u)).2)
         (scottList (uNewD es o ++ ics)) := by
  intro es; induction es with
  | nil =>
    intro o u ics hu _ _ _
    simp only [List.foldl_nil, uNewD, oScanD, List.scanl_nil,
               List.zip_nil_left,
               List.reverse_nil, List.map_nil, List.nil_append]
    exact hu
  | cons e es' ih =>
    intro o u ics hu hics ho hcl
    obtain ⟨he1, he22⟩ := hcl e List.mem_cons_self
    have hcl' : ∀ e' ∈ es',
        closed 0 e'.1 = true ∧ closed 0 e'.2.2 = true :=
      fun e' he' => hcl e' (List.mem_cons_of_mem _ he')
    have hcell : closed 0 (aps pairSrcL [e.1, o]) = true :=
      closed_aps closed_pairSrcL (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h
        · exact h ▸ he1
        · exact h ▸ ho)
    have ho' : closed 0 (aps b4addL [o, e.2.2]) = true :=
      closed_aps closed_b4addL (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h
        · exact h ▸ ho
        · exact h ▸ he22)
    have hstep : LRed (ouStepD (o, u) e).2
        (scottList (aps pairSrcL [e.1, o] :: ics)) := by
      show LRed (aps conssL [aps pairSrcL [e.1, o], u]) _
      have c1 : LRed (aps conssL [aps pairSrcL [e.1, o], u])
          (aps conssL [aps pairSrcL [e.1, o], scottList ics]) :=
        LRed_app_right hu
      have c2 : LRed
          (aps conssL [aps pairSrcL [e.1, o], scottList ics])
          (cellLit (aps pairSrcL [e.1, o]) (scottList ics)) :=
        conss_nf _ _ hcell (closed_scottList hics)
      exact c1.trans c2
    simp only [List.foldl_cons]
    rw [uNewD_cons, List.append_assoc, List.singleton_append]
    exact ih _ _ _ hstep
      (fun c hc => by
        rcases List.mem_cons.mp hc with h | h
        · exact h ▸ hcell
        · exact hics c h)
      ho' hcl'

-- linkL port ------------------------------------------------------

/-- The `I` combinator `λx. x`. -/
def idL : LTerm := .abs (.var 0)

theorem closed_idL : closed 0 idL = true := by decide

/-- `K I` reduces to `KI` in one step. -/
theorem kiSrc_nf : LRed (.app klL idL) kilL :=
  LRed_of_hsteps (k := 1) (by
    simp [kilL, idL, klL, hsteps, hstep, subst, shift])

/-- linkOf body under `[imports, slots, idr, dat]`:
    `PAIR (PAIR (idr·K) (dat·K)) (APPEND (idr·KI) (dat·KI))`. -/
def linkBody : LTerm := aps pairSrcL
  [aps pairSrcL [.app (.var 1) klL, .app (.var 0) klL],
   aps appendL [.app (.var 1) (.app klL idL),
                .app (.var 0) (.app klL idL)]]

/-- `λimports. λslots. (λidr. (λdat. body) (dataOf·slots))
    (idataOf·imports)` — the `_lets` port, first binding outermost. -/
def linkL (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16)) : LTerm :=
  .abs (.abs (.app
    (.abs (.app (.abs linkBody) (.app (dataOfL nSlot) (.var 1))))
    (.app (idataOfL nImp namesOff iatB iat4) (.var 1))))

theorem closed_linkBody : closed 4 linkBody = true := by decide

theorem closed_linkL (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16)) :
    closed 0 (linkL nImp nSlot namesOff iatB iat4) = true := by
  unfold linkL
  simp only [closed, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono closed_linkBody (by decide)
    | exact closed_mono (closed_dataOfL nSlot) (by decide)
    | exact closed_mono
        (closed_idataOfL nImp namesOff iatB iat4) (by decide)

/-- `linkL·i·s →* PAIR-src (PAIR-src (idrK) (datK))
    (APPEND (idrKI) (datKI))` — 4 β-steps (2 λs + 2 lets).  The
    `pairSrc`/`appendL` applications stay unreduced. -/
theorem link_open (i s : LTerm) (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hi : closed 0 i = true) (hs : closed 0 s = true) :
    LRed (.app (.app (linkL nImp nSlot namesOff iatB iat4) i) s)
      (aps pairSrcL
        [aps pairSrcL
          [.app (.app (idataOfL nImp namesOff iatB iat4) i) klL,
           .app (.app (dataOfL nSlot) s) klL],
         aps appendL
          [.app (.app (idataOfL nImp namesOff iatB iat4) i)
               (.app klL idL),
           .app (.app (dataOfL nSlot) s) (.app klL idL)]]) := by
  have hId : closed 0
      (.app (idataOfL nImp namesOff iatB iat4) i) = true :=
    closed_app (closed_idataOfL _ _ _ _) hi
  have hD : closed 0
      (.app (dataOfL nSlot) s) = true :=
    closed_app (closed_dataOfL _) hs
  exact LRed_of_hsteps (k := 4) (by
    unfold linkL linkBody aps
    simp [List.foldl, hsteps, hstep, subst, shift,
          subst_of_closed0, shift_of_closed0,
          hi, hs, closed_idataOfL, closed_dataOfL,
          closed_klL, closed_idL, closed_appendL,
          closed_pairSrcL])

/-- `linkOf imports slots → pairLit sections-pair sym-append` — the
    pairLit normal form; section and symbol components stay thunked
    (they project under consumers' continuations). -/
theorem link_eval (i s : LTerm) (nImp nSlot : Nat)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hi : closed 0 i = true) (hs : closed 0 s = true) :
    LRed (.app (.app (linkL nImp nSlot namesOff iatB iat4) i) s)
      (pairLit
        (aps pairSrcL
          [.app (.app (idataOfL nImp namesOff iatB iat4) i) klL,
           .app (.app (dataOfL nSlot) s) klL])
        (aps appendL
          [.app (.app (idataOfL nImp namesOff iatB iat4) i)
               (.app klL idL),
           .app (.app (dataOfL nSlot) s) (.app klL idL)])) := by
  have hId : closed 0
      (.app (idataOfL nImp namesOff iatB iat4) i) = true :=
    closed_app (closed_idataOfL _ _ _ _) hi
  have hD : closed 0
      (.app (dataOfL nSlot) s) = true :=
    closed_app (closed_dataOfL _) hs
  have hX : closed 0 (aps pairSrcL
      [.app (.app (idataOfL nImp namesOff iatB iat4) i) klL,
       .app (.app (dataOfL nSlot) s) klL]) = true := by
    apply closed_aps closed_pairSrcL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hId closed_klL
    · exact closed_app hD closed_klL
  have hY : closed 0 (aps appendL
      [.app (.app (idataOfL nImp namesOff iatB iat4) i)
           (.app klL idL),
       .app (.app (dataOfL nSlot) s) (.app klL idL)]) = true := by
    apply closed_aps closed_appendL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hId (closed_app closed_klL closed_idL)
    · exact closed_app hD (closed_app closed_klL closed_idL)
  exact (link_open i s nImp nSlot namesOff iatB iat4 hi hs).trans
    (pairSrc_nf _ _ hX hY)

-- u-component closedness ------------------------------------------

/-- `oScanD` members are closed when the seed and all size-terms are. -/
theorem closed_oScanD : ∀ (es : List (LTerm × LTerm × LTerm))
    (o : LTerm), closed 0 o = true →
    (∀ e ∈ es, closed 0 e.2.2 = true) →
    ∀ t ∈ oScanD es o, closed 0 t = true := by
  intro es; induction es with
  | nil =>
    intro o ho _ t ht
    simp only [oScanD, List.scanl_nil, List.mem_singleton] at ht
    exact ht ▸ ho
  | cons e es' ih =>
    intro o ho hcl t ht
    simp only [oScanD, List.scanl_cons, List.mem_cons] at ht
    rcases ht with h | h
    · exact h ▸ ho
    · exact ih _
        (closed_aps closed_b4addL (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ho
          · exact hcl e List.mem_cons_self))
        (fun e' he' => hcl e' (List.mem_cons_of_mem _ he')) _ h

/-- `uNewD` members are closed `PAIR`-thunks. -/
theorem closed_uNewD : ∀ (es : List (LTerm × LTerm × LTerm))
    (o : LTerm), closed 0 o = true →
    (∀ e ∈ es, closed 0 e.1 = true ∧ closed 0 e.2.2 = true) →
    ∀ t ∈ uNewD es o, closed 0 t = true := by
  intro es; induction es with
  | nil =>
    intro o _ _ t ht
    simp [uNewD, oScanD, List.scanl] at ht
  | cons e es' ih =>
    intro o ho hcl t ht
    rw [uNewD_cons] at ht
    rcases List.mem_append.mp ht with h | h
    · exact ih _
        (closed_aps closed_b4addL (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ho
          · exact (hcl e List.mem_cons_self).2))
        (fun e' he' => hcl e' (List.mem_cons_of_mem _ he')) _ h
    · simp only [List.mem_singleton] at h
      rw [h]
      apply closed_aps closed_pairSrcL
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (hcl e List.mem_cons_self).1
      · exact ho

-- consumer projections --------------------------------------------

/-- `L K K` — the .idata section cells. -/
theorem linkKK_eval (esI : List LTerm) (nsl : List (List (Fin 16)))
    (esD : List (LTerm × LTerm × LTerm))
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hF : List.Forall₂ (fun nm ns =>
        LRed nm (scottList (ns.map nibLit))) esI nsl)
    (hclI : ∀ e ∈ esI, closed 0 e = true)
    (hn4 : namesOff.length = 4) (hi4 : iatB.length = 4)
    (hclD : ∀ e ∈ esD, closed 0 e.1 = true ∧ closed 0 e.2.1 = true ∧
        closed 0 e.2.2 = true) :
    LRed (.app (.app (.app (.app
        (linkL esI.length esD.length namesOff iatB iat4)
        (scottList esI)) (scottList (esD.map slotEnc)))
        klL) klL)
      (scottList (idataCells nsl namesOff iat4)) := by
  have hI : closed 0 (scottList esI) = true := closed_scottList hclI
  have hS : closed 0 (scottList (esD.map slotEnc)) = true :=
    closed_scottList (fun e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      obtain ⟨h1, h2, h3⟩ := hclD x hx
      exact closed_slotEnc h1 h2 h3)
  have hIdT : closed 0 (.app (idataOfL esI.length namesOff iatB iat4)
      (scottList esI)) = true :=
    closed_app (closed_idataOfL _ _ _ _) hI
  have hDT : closed 0 (.app (dataOfL esD.length)
      (scottList (esD.map slotEnc))) = true :=
    closed_app (closed_dataOfL _) hS
  have hXc : closed 0 (aps pairSrcL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) klL,
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) klL]) = true := by
    apply closed_aps closed_pairSrcL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hIdT closed_klL
    · exact closed_app hDT closed_klL
  have hYc : closed 0 (aps appendL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) (.app klL idL),
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) (.app klL idL)]) = true := by
    apply closed_aps closed_appendL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hIdT (closed_app closed_klL closed_idL)
    · exact closed_app hDT (closed_app closed_klL closed_idL)
  have h1 := link_eval (scottList esI)
    (scottList (esD.map slotEnc)) esI.length esD.length
    namesOff iatB iat4 hI hS
  have h2 : LRed (.app (.app (.app
      (linkL esI.length esD.length namesOff iatB iat4)
      (scottList esI)) (scottList (esD.map slotEnc))) klL)
      (aps pairSrcL
        [.app (.app (idataOfL esI.length namesOff iatB iat4)
              (scottList esI)) klL,
         .app (.app (dataOfL esD.length)
              (scottList (esD.map slotEnc))) klL]) :=
    (LRed_app_left h1).trans (pairLit_fst _ _ hXc hYc)
  have h3 : LRed (.app (aps pairSrcL
        [.app (.app (idataOfL esI.length namesOff iatB iat4)
              (scottList esI)) klL,
         .app (.app (dataOfL esD.length)
              (scottList (esD.map slotEnc))) klL]) klL)
      (.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) klL) :=
    (LRed_app_left (pairSrc_nf _ _
      (closed_app hIdT closed_klL)
      (closed_app hDT closed_klL))).trans
      (pairLit_fst _ _
        (closed_app hIdT closed_klL) (closed_app hDT closed_klL))
  exact (LRed_app_left h2).trans
    (h3.trans (idrK_eval esI nsl namesOff iatB iat4 hF hclI hn4 hi4))

/-- `L K (K I)` — the .data section (zero-run) cells. -/
theorem linkKKI_eval (esD : List (LTerm × LTerm × LTerm))
    (szs : List Nat) (esI : List LTerm)
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hmap : esD.map (fun e => e.2.1) = szs.map churchL)
    (hclD : ∀ e ∈ esD, closed 0 e.1 = true ∧ closed 0 e.2.1 = true ∧
        closed 0 e.2.2 = true)
    (hclI : ∀ e ∈ esI, closed 0 e = true) :
    LRed (.app (.app (.app (.app
        (linkL esI.length esD.length namesOff iatB iat4)
        (scottList esI)) (scottList (esD.map slotEnc)))
        klL) kilL)
      (scottList (zCellsN szs)) := by
  have hI : closed 0 (scottList esI) = true := closed_scottList hclI
  have hS : closed 0 (scottList (esD.map slotEnc)) = true :=
    closed_scottList (fun e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      obtain ⟨h1, h2, h3⟩ := hclD x hx
      exact closed_slotEnc h1 h2 h3)
  have hIdT : closed 0 (.app (idataOfL esI.length namesOff iatB iat4)
      (scottList esI)) = true :=
    closed_app (closed_idataOfL _ _ _ _) hI
  have hDT : closed 0 (.app (dataOfL esD.length)
      (scottList (esD.map slotEnc))) = true :=
    closed_app (closed_dataOfL _) hS
  have hXc : closed 0 (aps pairSrcL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) klL,
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) klL]) = true := by
    apply closed_aps closed_pairSrcL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hIdT closed_klL
    · exact closed_app hDT closed_klL
  have hYc : closed 0 (aps appendL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) (.app klL idL),
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) (.app klL idL)]) = true := by
    apply closed_aps closed_appendL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hIdT (closed_app closed_klL closed_idL)
    · exact closed_app hDT (closed_app closed_klL closed_idL)
  have h1 := link_eval (scottList esI)
    (scottList (esD.map slotEnc)) esI.length esD.length
    namesOff iatB iat4 hI hS
  have h2 : LRed (.app (.app (.app
      (linkL esI.length esD.length namesOff iatB iat4)
      (scottList esI)) (scottList (esD.map slotEnc))) klL)
      (aps pairSrcL
        [.app (.app (idataOfL esI.length namesOff iatB iat4)
              (scottList esI)) klL,
         .app (.app (dataOfL esD.length)
              (scottList (esD.map slotEnc))) klL]) :=
    (LRed_app_left h1).trans (pairLit_fst _ _ hXc hYc)
  have h3 : LRed (.app (aps pairSrcL
        [.app (.app (idataOfL esI.length namesOff iatB iat4)
              (scottList esI)) klL,
         .app (.app (dataOfL esD.length)
              (scottList (esD.map slotEnc))) klL]) kilL)
      (.app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) klL) :=
    (LRed_app_left (pairSrc_nf _ _
      (closed_app hIdT closed_klL)
      (closed_app hDT closed_klL))).trans
      (pairLit_snd _ _
        (closed_app hIdT closed_klL) (closed_app hDT closed_klL))
  exact (LRed_app_left h2).trans
    (h3.trans (datK_eval esD szs hmap hclD))

/-- `L (K I)` — the merged symbol table: idata symbols then data
    symbols, matching `_APPEND (idr KI) (dat KI)`. -/
theorem linkKI_eval (esI : List LTerm) (nsl : List (List (Fin 16)))
    (esD : List (LTerm × LTerm × LTerm))
    (namesOff iatB iat4 : List (Fin 16 × Fin 16))
    (hF : List.Forall₂ (fun nm ns =>
        LRed nm (scottList (ns.map nibLit))) esI nsl)
    (hclI : ∀ e ∈ esI, closed 0 e = true)
    (hn4 : namesOff.length = 4) (hi4 : iatB.length = 4)
    (hclD : ∀ e ∈ esD, closed 0 e.1 = true ∧ closed 0 e.2.1 = true ∧
        closed 0 e.2.2 = true) :
    LRed (.app (.app (.app
        (linkL esI.length esD.length namesOff iatB iat4)
        (scottList esI)) (scottList (esD.map slotEnc)))
        kilL)
      (scottList (syNew esI (bytesChunk iatB) ++
                  uNewD esD (bytesChunk b3000))) := by
  have hI : closed 0 (scottList esI) = true := closed_scottList hclI
  have hS : closed 0 (scottList (esD.map slotEnc)) = true :=
    closed_scottList (fun e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      obtain ⟨h1, h2, h3⟩ := hclD x hx
      exact closed_slotEnc h1 h2 h3)
  have hIdT : closed 0 (.app (idataOfL esI.length namesOff iatB iat4)
      (scottList esI)) = true :=
    closed_app (closed_idataOfL _ _ _ _) hI
  have hDT : closed 0 (.app (dataOfL esD.length)
      (scottList (esD.map slotEnc))) = true :=
    closed_app (closed_dataOfL _) hS
  have hXc : closed 0 (aps pairSrcL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) klL,
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) klL]) = true := by
    apply closed_aps closed_pairSrcL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hIdT closed_klL
    · exact closed_app hDT closed_klL
  have hYc : closed 0 (aps appendL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) (.app klL idL),
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) (.app klL idL)]) = true := by
    apply closed_aps closed_appendL
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact closed_app hIdT (closed_app closed_klL closed_idL)
    · exact closed_app hDT (closed_app closed_klL closed_idL)
  have h1 := link_eval (scottList esI)
    (scottList (esD.map slotEnc)) esI.length esD.length
    namesOff iatB iat4 hI hS
  have h2 : LRed (.app (.app (.app
      (linkL esI.length esD.length namesOff iatB iat4)
      (scottList esI)) (scottList (esD.map slotEnc))) kilL)
      (aps appendL
        [.app (.app (idataOfL esI.length namesOff iatB iat4)
              (scottList esI)) (.app klL idL),
         .app (.app (dataOfL esD.length)
              (scottList (esD.map slotEnc))) (.app klL idL)]) :=
    (LRed_app_left h1).trans (pairLit_snd _ _ hXc hYc)
  -- idr·KI → the idata symbols
  have hcf := closed_idataAfterK (es := esI) (k := esI.length)
    (o := bytesChunk namesOff) (oi := bytesChunk iatB)
    (rv := nilL) (rc := nilL) (sy := nilL)
    hclI (closed_bytesChunk namesOff) (closed_bytesChunk iatB)
    closed_nilL closed_nilL closed_nilL
  rw [List.take_length] at hcf
  obtain ⟨c1, _c2, c3, c4, c5⟩ := hcf
  have hf := idataFold_eval esI nsl hF hclI
    (bytesChunk namesOff) (bytesChunk iatB) nilL nilL nilL
    namesOff iatB [] [] [] [] []
    (bytesChunk_nf namesOff) hn4 (bytesChunk_nf iatB) hi4
    Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl
    List.Forall₂.nil List.Forall₂.nil
    (fun e he => by simp at he) (fun e he => by simp at he)
    (fun e he => by simp at he)
    (closed_bytesChunk namesOff) (closed_bytesChunk iatB)
    closed_nilL closed_nilL closed_nilL
  obtain ⟨_, _, _, _, _, _, _, _, hsy, hsycl, _, _, _⟩ := hf
  rw [List.append_nil] at hsy
  have hsyT : LRed (.app (.app (idataOfL esI.length namesOff iatB iat4)
        (scottList esI)) kilL)
      (idataFinal esI namesOff iatB).2.2.2.2 :=
    (LRed_app_left (idataOf_eval esI namesOff iatB iat4 hclI)).trans
      (pairLit_snd _ _ (closed_idBody c1 c3 c4 iat4) c5)
  have hA : LRed (.app (.app (idataOfL esI.length namesOff iatB iat4)
        (scottList esI)) (.app klL idL))
      (scottList (syNew esI (bytesChunk iatB))) :=
    (LRed_app_right kiSrc_nf).trans (hsyT.trans hsy)
  -- dat·KI → the data symbols
  have hfd := closed_dataFinal esD hclD
  have huT : LRed (.app (.app (dataOfL esD.length)
        (scottList (esD.map slotEnc))) kilL)
      (dataFinal esD).2.1 :=
    (LRed_app_left (dataOf_eval esD hclD)).trans
      (pairLit_snd _ _ hfd.2.2 hfd.2.1)
  have huf := uFold_eval esD (bytesChunk b3000) nilL []
      Relation.ReflTransGen.refl
      (fun e he => by simp at he)
      (closed_bytesChunk b3000)
      (fun e he => ⟨(hclD e he).1, (hclD e he).2.2⟩)
  rw [List.append_nil] at huf
  have hu' : (dataFinal esD).2.1 =
      (esD.foldl ouStepD (bytesChunk b3000, nilL)).2 := by
    unfold dataFinal
    rw [dataStepSem_u]
  rw [hu'] at huT
  have hB : LRed (.app (.app (dataOfL esD.length)
        (scottList (esD.map slotEnc))) (.app klL idL))
      (scottList (uNewD esD (bytesChunk b3000))) :=
    (LRed_app_right kiSrc_nf).trans (huT.trans huf)
  -- append the two symbol lists
  have h3 : LRed (aps appendL
      [.app (.app (idataOfL esI.length namesOff iatB iat4)
            (scottList esI)) (.app klL idL),
       .app (.app (dataOfL esD.length)
            (scottList (esD.map slotEnc))) (.app klL idL)])
      (appendT
        (.app (.app (idataOfL esI.length namesOff iatB iat4)
              (scottList esI)) (.app klL idL))
        (.app (.app (dataOfL esD.length)
              (scottList (esD.map slotEnc))) (.app klL idL))) :=
    appendL_to_appendT _ _
      (closed_app hIdT (closed_app closed_klL closed_idL))
      (closed_app hDT (closed_app closed_klL closed_idL))
  have h4 := append_eval _ _ _ _ hA hB
    hsycl
    (closed_uNewD esD (bytesChunk b3000)
      (closed_bytesChunk b3000)
      (fun e he => ⟨(hclD e he).1, (hclD e he).2.2⟩))
    (closed_app hIdT (closed_app closed_klL closed_idL))
    (closed_app hDT (closed_app closed_klL closed_idL))
  exact h2.trans (h3.trans h4)

#print axioms pairLit_snd
#print axioms uFold_eval
#print axioms link_open
#print axioms link_eval
#print axioms linkKK_eval
#print axioms linkKKI_eval
#print axioms linkKI_eval

-- ============================================================
-- Batch M layer 1: assembleOf primitives —
--   nibnot/notb (byte complement), nib2b4 (nibble→bytes4 lift).
-- ============================================================

/-- `_NIBNOT` — nibble complement `15 − i` as a 16-dispatch table. -/
def nibnotL : LTerm :=
  .abs (aps (.var 0) (List.ofFn fun i : Fin 16 =>
    nibLit ⟨15 - i.val, by omega⟩))

theorem closed_nibnotL : closed 0 nibnotL = true := by decide

theorem nibnot_table : ∀ i : Fin 16,
    hsteps 17 (aps nibnotL [nibLit i]) = nibLit ⟨15 - i.val, by omega⟩ := by
  decide

/-- nibble complement `15 − i`. -/
def nibNot (i : Fin 16) : Fin 16 := ⟨15 - i.val, by omega⟩

theorem nibnot_eval (i : Fin 16) :
    LRed (aps nibnotL [nibLit i]) (nibLit (nibNot i)) :=
  LRed_of_hsteps (nibnot_table i)

/-- `_NOTB = λx. x (λl.λh. PAIR (NIBNOT l) (NIBNOT h))` —
    byte-cell complement. -/
def notbL : LTerm :=
  .abs (.app (.var 0)
    (.abs (.abs (aps pairSrcL
      [.app nibnotL (.var 1), .app nibnotL (.var 0)]))))

theorem closed_notbL : closed 0 notbL = true := by decide

/-- `NOTB (byteLit lo hi) →* byteLit (15−lo) (15−hi)`. -/
theorem notb_eval (lo hi : Fin 16) :
    LRed (.app notbL (byteLit lo hi))
      (byteLit (nibNot lo) (nibNot hi)) := by
  have c1 : LRed (.app notbL (byteLit lo hi))
      (aps pairSrcL
        [.app nibnotL (nibLit lo), .app nibnotL (nibLit hi)]) :=
    LRed_of_hsteps (k := 4) (by
      simp [notbL, byteLit, pairLit, aps, List.foldl,
            hsteps, hstep, subst, shift, subst_of_closed0,
            shift_of_closed0, closed_nibLit,
            closed_nibnotL, closed_pairSrcL])
  have c2 : LRed (aps pairSrcL
      [.app nibnotL (nibLit lo), .app nibnotL (nibLit hi)])
      (byteLit (nibNot lo) (nibNot hi)) := by
    show LRed (aps pairSrcL
        [.app nibnotL (nibLit lo), .app nibnotL (nibLit hi)])
      (pairLit (nibLit (nibNot lo)) (nibLit (nibNot hi)))
    have h1 : LRed (aps pairSrcL
        [.app nibnotL (nibLit lo), .app nibnotL (nibLit hi)])
        (aps pairSrcL
          [nibLit (nibNot lo), nibLit (nibNot hi)]) :=
      LRed_app (LRed_app Relation.ReflTransGen.refl
        (nibnot_eval lo)) (nibnot_eval hi)
    exact h1.trans (pairSrc_nf _ _
      (closed_nibLit _) (closed_nibLit _))
  exact c1.trans c2

/-- `_NIB2B4 = λn5. CONSS (PAIR n5 s0) (CONSS b0c (CONSS b0c
    (CONSS b0c K)))`. -/
def nib2b4L : LTerm :=
  .abs (aps conssL
    [aps pairSrcL [.var 0, nibLit 0],
     aps conssL [b0cT, aps conssL [b0cT,
       aps conssL [b0cT, klL]]]])

theorem closed_nib2b4L : closed 0 nib2b4L = true := by
  decide

/-- `NIB2B4 n →* scottList [PAIR n 0, b0c, b0c, b0c]` — the first
    cell stays a `pairSrc` thunk, matching Python's lazy cells. -/
theorem nib2b4_eval (n : Fin 16) :
    LRed (.app nib2b4L (nibLit n))
      (scottList [aps pairSrcL [nibLit n, nibLit 0],
        b0cT, b0cT, b0cT]) := by
  have hb0 : closed 0 b0cT = true := by
    unfold b0cT
    exact closed_aps closed_pairSrcL (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact closed_nibLit _)
  have c1 : LRed (.app nib2b4L (nibLit n))
      (aps conssL
        [aps pairSrcL [nibLit n, nibLit 0],
         aps conssL [b0cT, aps conssL [b0cT,
           aps conssL [b0cT, klL]]]]) :=
    LRed_of_hsteps (k := 1) (by
      simp [nib2b4L, aps, List.foldl, hsteps, hstep, subst,
            shift_of_closed0, subst_of_closed0,
            closed_nibLit, closed_conssL, closed_pairSrcL,
            closed_klL, hb0])
  refine c1.trans ?_
  show LRed (aps conssL [aps pairSrcL [nibLit n, nibLit 0], _]) _
  have hcell : closed 0 (aps pairSrcL [nibLit n, nibLit 0]) = true :=
    closed_aps closed_pairSrcL (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact closed_nibLit _)
  have t1 : LRed (aps conssL [b0cT,
      aps conssL [b0cT, aps conssL [b0cT, klL]]])
      (cellLit b0cT (cellLit b0cT (cellLit b0cT klL))) := by
    have s1 : LRed (aps conssL [b0cT, klL])
        (cellLit b0cT klL) :=
      conss_nf _ _ hb0 closed_klL
    have s2 : LRed (aps conssL [b0cT, aps conssL [b0cT, klL]])
        (cellLit b0cT (cellLit b0cT klL)) :=
      (LRed_app_right s1).trans
        (conss_nf _ _ hb0 (closed_cellLit hb0 closed_klL))
    exact (LRed_app_right s2).trans
      (conss_nf _ _ hb0 (closed_cellLit hb0
        (closed_cellLit hb0 closed_klL)))
  refine (LRed_app_right t1).trans ?_
  have s0 : LRed (aps conssL [aps pairSrcL [nibLit n, nibLit 0],
      cellLit b0cT (cellLit b0cT (cellLit b0cT klL))])
      (cellLit (aps pairSrcL [nibLit n, nibLit 0])
        (cellLit b0cT (cellLit b0cT (cellLit b0cT klL)))) :=
    conss_nf _ _ hcell (closed_cellLit hb0
      (closed_cellLit hb0 (closed_cellLit hb0 closed_klL)))
  exact s0

#print axioms nibnot_eval
#print axioms notb_eval
#print axioms nib2b4_eval

end ISAR
