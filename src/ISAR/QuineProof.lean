/-
  QuineProof.lean
  Formal Proof of Quine Encryption in Lean 4
  ===========================================

  This file formalizes:
  1. Term representation of structural graphs.
  2. Confluence and uniqueness of normal forms (e-graph reduction).
  3. Preimage resistance and forward secrecy of the anchor chain.
  4. Structural homomorphism of semantic masking and restoration.
-/

-- ============================================================================
-- 1. TERM REPRESENTATION OF STRUCTURAL GRAPHS
-- ============================================================================

inductive Term where
  | atom : String → Term
  | pair : Term → Term → Term
  | op   : String → Term → Term
  | hash : Term → Term
  deriving DecidableEq, Repr

-- ============================================================================
-- 2. REWRITE SYSTEM & CONFLUENCE
-- ============================================================================

-- Reflexive-transitive closure of a binary relation
inductive ReducesStar (R : Term → Term → Prop) : Term → Term → Prop where
  | refl (t : Term) : ReducesStar R t t
  | trans (t1 t2 t3 : Term) : R t1 t2 → ReducesStar R t2 t3 → ReducesStar R t1 t3

def IsNormalForm (R : Term → Term → Prop) (t : Term) : Prop :=
  ∀ t', ¬ R t t'

-- Theorem: A normal form cannot reduce further under ReducesStar to anything other than itself
theorem normal_form_reduces_star_eq {R : Term → Term → Prop} {t : Term} {t' : Term}
  (hnf : IsNormalForm R t) (hr : ReducesStar R t t') : t = t' := by
  cases hr with
  | refl => rfl
  | trans t1 t2 t3 hr1 hr2 =>
    have hnot := hnf t2
    contradiction

-- Theorem 1: Determinism of Normal Forms (Confluence implies unique normal forms)
theorem uniqueness_of_normal_forms {R : Term → Term → Prop}
  (h_confl : ∀ {t t1 t2 : Term}, ReducesStar R t t1 → ReducesStar R t t2 → ∃ t3, ReducesStar R t1 t3 ∧ ReducesStar R t2 t3)
  {t : Term} {t1 : Term} {t2 : Term} (h1 : ReducesStar R t t1) (h2 : ReducesStar R t t2)
  (hnf1 : IsNormalForm R t1) (hnf2 : IsNormalForm R t2) : t1 = t2 := by
  have ⟨t3, ht1, ht2⟩ := h_confl h1 h2
  have heq1 := normal_form_reduces_star_eq hnf1 ht1
  have heq2 := normal_form_reduces_star_eq hnf2 ht2
  subst heq1 heq2
  rfl

-- ============================================================================
-- 3. CRYPTOGRAPHIC ANCHOR CHAIN & FORWARD SECRECY
-- ============================================================================

-- Inductive predicate modeling the adversary's capability to derive information.
inductive Derivable (S : List Term) : Term → Prop where
  | member (t : Term) (h : t ∈ S) : Derivable S t
  | pair_intro (t1 t2 : Term) (h1 : Derivable S t1) (h2 : Derivable S t2) : Derivable S (Term.pair t1 t2)
  | pair_elim_left (t1 t2 : Term) (h : Derivable S (Term.pair t1 t2)) : Derivable S t1
  | pair_elim_right (t1 t2 : Term) (h : Derivable S (Term.pair t1 t2)) : Derivable S t2
  | op_intro (name : String) (t : Term) (h : Derivable S t) : Derivable S (Term.op name t)
  | op_elim (name : String) (t : Term) (h : Derivable S (Term.op name t)) : Derivable S t
  | hash_intro (t : Term) (h : Derivable S t) : Derivable S (Term.hash t)

-- Helper: Term size definition
def termSize : Term → Nat
  | Term.atom _ => 1
  | Term.pair t1 t2 => termSize t1 + termSize t2 + 1
  | Term.op _ t => termSize t + 1
  | Term.hash t => termSize t + 1

-- Helper: Term contains no hash of nf
def NoHash (nf : Term) : Term → Prop
  | Term.atom _ => True
  | Term.pair t1 t2 => NoHash nf t1 ∧ NoHash nf t2
  | Term.op _ t => NoHash nf t
  | Term.hash t => t ≠ nf ∧ NoHash nf t

-- Helper: Size properties
theorem size_pos (t : Term) : termSize t > 0 := by
  induction t <;> simp [termSize]

theorem size_contains_hash {nf : Term} {t : Term} (h : ¬ NoHash nf t) : termSize t ≥ termSize (Term.hash nf) := by
  induction t with
  | atom _ =>
    simp [NoHash] at h
  | pair t1 t2 ih1 ih2 =>
    simp [NoHash] at h
    by_cases h1 : NoHash nf t1
    · have h2 : ¬ NoHash nf t2 := h h1
      have ih := ih2 h2
      simp [termSize] at *
      omega
    · have ih := ih1 h1
      simp [termSize] at *
      omega
  | op _ t ih =>
    simp [NoHash] at h
    have ih' := ih h
    simp [termSize] at *
    omega
  | hash t ih =>
    simp [NoHash] at h
    by_cases heq : t = nf
    · subst heq
      exact Nat.le_refl _
    · simp [heq] at h
      have ih' := ih h
      simp [termSize] at *
      omega

theorem nohash_nf (nf : Term) : NoHash nf nf := by
  by_cases h : NoHash nf nf
  · exact h
  · have h_size := size_contains_hash h
    simp [termSize] at h_size
    have h_false := Nat.not_succ_le_self (termSize nf) h_size
    exact False.elim h_false

-- Helper: Substitution function
def subst (nf : Term) (d : Term) : Term → Term
  | Term.atom s => Term.atom s
  | Term.pair t1 t2 => Term.pair (subst nf d t1) (subst nf d t2)
  | Term.op name t => Term.op name (subst nf d t)
  | Term.hash t =>
    if t = nf then
      d
    else
      Term.hash (subst nf d t)

theorem subst_noop {nf : Term} {d : Term} {t : Term} (h : NoHash nf t) : subst nf d t = t := by
  induction t with
  | atom _ => rfl
  | pair t1 t2 ih1 ih2 =>
    simp [NoHash] at h
    cases h with
    | intro h1 h2 =>
      simp [subst, ih1 h1, ih2 h2]
  | op _ t ih =>
    simp [NoHash] at h
    simp [subst, ih h]
  | hash t ih =>
    simp [NoHash] at h
    cases h with
    | intro h1 h2 =>
      simp [subst, h1, ih h2]

theorem mem_map_of_mem {α β : Type} (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ l.map f := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head =>
      exact List.Mem.head (List.map f xs)
    | tail _ hxs =>
      exact List.Mem.tail (f x) (ih hxs)

theorem derivable_mono (S1 S2 : List Term) (h_sub : ∀ x ∈ S1, x ∈ S2)
  {t : Term} (h : Derivable S1 t) : Derivable S2 t := by
  induction h with
  | member t h_mem => exact Derivable.member _ (h_sub t h_mem)
  | pair_intro t1 t2 h1 h2 ih1 ih2 => exact Derivable.pair_intro _ _ ih1 ih2
  | pair_elim_left t1 t2 h ih => exact Derivable.pair_elim_left _ _ ih
  | pair_elim_right t1 t2 h ih => exact Derivable.pair_elim_right _ _ ih
  | op_intro name t h ih => exact Derivable.op_intro _ _ ih
  | op_elim name t h ih => exact Derivable.op_elim _ _ ih
  | hash_intro t h ih => exact Derivable.hash_intro _ ih

theorem derivable_subst_map (S : List Term) (nf : Term) (d : Term) (hd : Derivable (S.map (subst nf d)) d)
  {t : Term} (h : Derivable S t) : Derivable (S.map (subst nf d)) (subst nf d t) := by
  induction h with
  | member t h_mem =>
    exact Derivable.member _ (mem_map_of_mem (subst nf d) h_mem)
  | pair_intro t1 t2 h1 h2 ih1 ih2 =>
    simp [subst]
    exact Derivable.pair_intro _ _ ih1 ih2
  | pair_elim_left t1 t2 h ih =>
    exact Derivable.pair_elim_left _ _ ih
  | pair_elim_right t1 t2 h ih =>
    exact Derivable.pair_elim_right _ _ ih
  | op_intro name t h ih =>
    simp [subst]
    exact Derivable.op_intro _ _ ih
  | op_elim name t h ih =>
    exact Derivable.op_elim _ _ ih
  | hash_intro t h ih =>
    simp [subst]
    split
    · exact hd
    · exact Derivable.hash_intro _ ih

theorem derivable_cut (S1 S2 : List Term) (h_sub : ∀ x ∈ S1, Derivable S2 x)
  {t : Term} (h : Derivable S1 t) : Derivable S2 t := by
  induction h with
  | member t h_mem => exact h_sub t h_mem
  | pair_intro t1 t2 h1 h2 ih1 ih2 => exact Derivable.pair_intro _ _ ih1 ih2
  | pair_elim_left t1 t2 h ih => exact Derivable.pair_elim_left _ _ ih
  | pair_elim_right t1 t2 h ih => exact Derivable.pair_elim_right _ _ ih
  | op_intro name t h ih => exact Derivable.op_intro _ _ ih
  | op_elim name t h ih => exact Derivable.op_elim _ _ ih
  | hash_intro t h ih => exact Derivable.hash_intro _ ih

theorem map_subst_noop {nf : Term} {d : Term} {l : List Term} (h : ∀ x ∈ l, NoHash nf x) : l.map (subst nf d) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map]
    have h_head := h x List.mem_cons_self
    have h_tail : ∀ y ∈ xs, NoHash nf y := by
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)
    rw [subst_noop h_head, ih h_tail]
    constructor <;> rfl

-- BuiltFromHash helper for empty list case
inductive BuiltFromHash (nf : Term) : Term → Prop where
  | base : BuiltFromHash nf (Term.hash nf)
  | pair_intro {t1 t2 : Term} (h1 : BuiltFromHash nf t1) (h2 : BuiltFromHash nf t2) : BuiltFromHash nf (Term.pair t1 t2)
  | op_intro {o : String} {t : Term} (h : BuiltFromHash nf t) : BuiltFromHash nf (Term.op o t)
  | hash_intro {t : Term} (h : BuiltFromHash nf t) : BuiltFromHash nf (Term.hash t)

theorem built_from_hash_size {nf : Term} {t : Term} (h : BuiltFromHash nf t) : termSize t > termSize nf := by
  induction h with
  | base =>
    simp [termSize]
  | pair_intro h1 h2 ih1 ih2 =>
    simp [termSize]
    omega
  | op_intro h ih =>
    simp [termSize]
    omega
  | hash_intro h ih =>
    simp [termSize]
    omega

theorem derivable_single_hash_imp {nf : Term} {S : List Term} {t : Term} (hS : S = [Term.hash nf]) (h : Derivable S t) : BuiltFromHash nf t := by
  induction h generalizing hS with
  | member t h_mem =>
    subst hS
    cases h_mem
    · exact BuiltFromHash.base
    · rename_i hxs
      cases hxs
  | pair_intro t1 t2 h1 h2 ih1 ih2 =>
    exact BuiltFromHash.pair_intro (ih1 hS) (ih2 hS)
  | pair_elim_left t1 t2 h ih =>
    have ih' := ih hS
    cases ih' with
    | pair_intro h1 h2 => exact h1
  | pair_elim_right t1 t2 h ih =>
    have ih' := ih hS
    cases ih' with
    | pair_intro h1 h2 => exact h2
  | op_intro name t h ih =>
    exact BuiltFromHash.op_intro (ih hS)
  | op_elim name t h ih =>
    have ih' := ih hS
    cases ih' with
    | op_intro h1 => exact h1
  | hash_intro t h ih =>
    exact BuiltFromHash.hash_intro (ih hS)

theorem derivable_single_hash_nf {nf : Term} (h : Derivable [Term.hash nf] nf) : False := by
  have h_built := derivable_single_hash_imp rfl h
  have h_size := built_from_hash_size h_built
  omega

theorem built_from_hash_not_nohash {nf : Term} {t : Term} (h : BuiltFromHash nf t) : ¬ NoHash nf t := by
  induction h with
  | base =>
    simp [NoHash]
  | pair_intro h1 h2 ih1 ih2 =>
    simp [NoHash]
    intro _
    exact ih2
  | op_intro h ih =>
    simp [NoHash]
    exact ih
  | hash_intro h ih =>
    simp [NoHash]
    intro _
    exact ih

-- ============================================================================
-- NOTE ON THE SECURITY MODEL:
-- The theorems below are proven in a Dolev-Yao style SYMBOLIC MODEL (Term Algebra).
-- In this model, cryptographic primitives like `hash` are represented as algebraic
-- constructors that are completely opaque (i.e. no term `t` can be derived from
-- `Term.hash t` unless `t` is already derivable).
-- ============================================================================

-- Theorem: Non-deducibility of preimages in the symbolic model (Symbolic Hash One-Wayness)
theorem non_deducibility_of_preimages_symbolic (S : List Term) (nf : Term) (h_nohash : ∀ x ∈ S, NoHash nf x) :
  ¬ Derivable S nf → ¬ Derivable (Term.hash nf :: S) nf := by
  intro h_not h_der
  cases S with
  | nil =>
    exact derivable_single_hash_nf h_der
  | cons d S_tail =>
    have hd : Derivable (d :: S_tail) d := Derivable.member _ List.mem_cons_self
    have hd_mapped : Derivable ((Term.hash nf :: d :: S_tail).map (subst nf d)) d := by
      simp [List.map, subst]
      exact Derivable.member _ List.mem_cons_self
    have h_sub := derivable_subst_map (Term.hash nf :: d :: S_tail) nf d hd_mapped h_der
    have h_sub' : Derivable (d :: (d :: S_tail).map (subst nf d)) nf := by
      simp [List.map, subst, subst_noop (nohash_nf nf)] at h_sub
      exact h_sub
    have h_map_eq : (d :: S_tail).map (subst nf d) = (d :: S_tail) := map_subst_noop h_nohash
    rw [h_map_eq] at h_sub'
    have h_cut : ∀ x ∈ d :: (d :: S_tail), Derivable (d :: S_tail) x := by
      intro x h_mem
      cases h_mem with
      | head => exact hd
      | tail _ hxs => exact Derivable.member _ hxs
    exact h_not (derivable_cut _ _ h_cut h_sub')

-- Theorem: Hash Non-Interference in the symbolic model (Symbolic Hash Independence)
theorem hash_noninterference_symbolic (S : List Term) (nf : Term) (t' : Term) (_h_ne : nf ≠ t') (h_nohash_S : ∀ x ∈ S, NoHash nf x) (h_nohash_t' : NoHash nf t') :
  ¬ Derivable S t' → ¬ Derivable (Term.hash nf :: S) t' := by
  intro h_not h_der
  cases S with
  | nil =>
    have h_built := derivable_single_hash_imp rfl h_der
    have h_not_nohash := built_from_hash_not_nohash h_built
    contradiction
  | cons d S_tail =>
    have hd : Derivable (d :: S_tail) d := Derivable.member _ List.mem_cons_self
    have hd_mapped : Derivable ((Term.hash nf :: d :: S_tail).map (subst nf d)) d := by
      simp [List.map, subst]
      exact Derivable.member _ List.mem_cons_self
    have h_sub := derivable_subst_map (Term.hash nf :: d :: S_tail) nf d hd_mapped h_der
    have h_sub' : Derivable (d :: (d :: S_tail).map (subst nf d)) t' := by
      simp [List.map, subst, subst_noop h_nohash_t'] at h_sub
      exact h_sub
    have h_map_eq : (d :: S_tail).map (subst nf d) = (d :: S_tail) := map_subst_noop h_nohash_S
    rw [h_map_eq] at h_sub'
    have h_cut : ∀ x ∈ d :: (d :: S_tail), Derivable (d :: S_tail) x := by
      intro x h_mem
      cases h_mem with
      | head => exact hd
      | tail _ hxs => exact Derivable.member _ hxs
    exact h_not (derivable_cut _ _ h_cut h_sub')

-- Lemma: General Secrecy Preservation
theorem hash_preserves_non_derivability (S : List Term) (nf : Term) (t' : Term)
  (h_nohash_S : ∀ x ∈ S, NoHash nf x) (h_nohash_t' : NoHash nf t') :
  ¬ Derivable S t' → ¬ Derivable (Term.hash nf :: S) t' := by
  intro h_not
  by_cases h : nf = t'
  · subst h
    exact non_deducibility_of_preimages_symbolic S nf h_nohash_S h_not
  · exact hash_noninterference_symbolic S nf t' h h_nohash_S h_nohash_t' h_not

/-- Symbolic Secrecy: The normal form `nf` is not derivable from the adversary's view `S`. -/
def SymbolicallySecret (S : List Term) (nf : Term) : Prop :=
  ¬ Derivable S nf

-- Theorem 2: Forward Secrecy of the Anchor Chain (One-Step / Per-Anchor Secrecy)
theorem forward_secrecy (S : List Term) (nf : Term)
  (h_nohash_S : ∀ x ∈ S, NoHash nf x)
  (h_not_derivable : ¬ Derivable S nf) :
  ¬ Derivable (Term.hash nf :: S) nf := by
  apply non_deducibility_of_preimages_symbolic S nf h_nohash_S h_not_derivable

/-- Anchor chain state: an evolving context `S` and a list of normal forms `nfs` with their anchors. -/
structure AnchorChain where
  S   : List Term         -- adversary-visible structural terms
  nfs : List Term         -- semantic normal forms, in order

/-- Expose all anchors for a chain by consing their hashes onto S. -/
def exposeAnchors (c : AnchorChain) : List Term :=
  let anchors := c.nfs.map (fun nf => Term.hash nf)
  anchors ++ c.S

-- ChainIndependence predicate
def ChainIndependent (nfs : List Term) (S : List Term) : Prop :=
  List.Nodup nfs ∧
  (∀ x ∈ nfs, ∀ y ∈ S, NoHash x y) ∧
  (∀ x ∈ nfs, ∀ y ∈ nfs, x ≠ y → NoHash x y)

theorem derivable_under_hashes (S : List Term) (nfs : List Term) (t : Term)
  (h_not : ¬ Derivable S t)
  (h_nohash : ∀ x ∈ nfs, NoHash x t)
  (h_nohash_S : ∀ x ∈ nfs, ∀ y ∈ S, NoHash x y)
  (h_nohash_self : ∀ x ∈ nfs, ∀ y ∈ nfs, x ≠ y → NoHash x y)
  (h_nodup : List.Nodup nfs) :
  ¬ Derivable (nfs.map (fun nf => Term.hash nf) ++ S) t := by
  induction nfs with
  | nil =>
    exact h_not
  | cons x xs ih =>
    have h_nodup_xs : List.Nodup xs := by
      cases h_nodup with
      | cons _ h2 => exact h2
    have h_not_mem_xs : x ∉ xs := by
      cases h_nodup with
      | cons h1 h2 =>
        intro h_in
        exact (h1 x h_in) rfl
    have h_nohash_xs : ∀ y ∈ xs, NoHash y t := by
      intro y hy
      exact h_nohash y (List.mem_cons_of_mem x hy)
    have h_nohash_S_xs : ∀ y ∈ xs, ∀ z ∈ S, NoHash y z := by
      intro y hy z hz
      exact h_nohash_S y (List.mem_cons_of_mem x hy) z hz
    have h_nohash_self_xs : ∀ y ∈ xs, ∀ z ∈ xs, y ≠ z → NoHash y z := by
      intro y hy z hz h_ne
      exact h_nohash_self y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz) h_ne
    have ih' := ih h_nohash_xs h_nohash_S_xs h_nohash_self_xs h_nodup_xs
    have h_nohash_S' : ∀ y ∈ (xs.map (fun nf => Term.hash nf) ++ S), NoHash x y := by
      intro y hy
      rw [List.mem_append] at hy
      cases hy with
      | inl h_xs =>
        have ⟨z, hz_mem, hz_eq⟩ := List.mem_map.mp h_xs
        subst hz_eq
        simp [NoHash]
        have h_ne : x ≠ z := by
          intro hc
          subst hc
          exact h_not_mem_xs hz_mem
        refine ⟨h_ne.symm, ?_⟩
        exact h_nohash_self x List.mem_cons_self z (List.mem_cons_of_mem x hz_mem) h_ne
      | inr h_S =>
        exact h_nohash_S x List.mem_cons_self y h_S
    have h_nohash_xt : NoHash x t := h_nohash x List.mem_cons_self
    exact hash_preserves_non_derivability (xs.map (fun nf => Term.hash nf) ++ S) x t h_nohash_S' h_nohash_xt ih'

-- Theorem 2 (Generalized): Chain Forward Secrecy (Symbolic Model)
theorem chain_forward_secrecy (c : AnchorChain) (h_ind : ChainIndependent c.nfs c.S)
  (h_opaque : ∀ nf ∈ c.nfs, SymbolicallySecret c.S nf) :
  ∀ nf ∈ c.nfs, SymbolicallySecret (exposeAnchors c) nf := by
  intro nf hmem
  have h_op := h_opaque nf hmem
  have h_nodup : List.Nodup c.nfs := h_ind.1
  have h_nohash_S : ∀ x ∈ c.nfs, ∀ y ∈ c.S, NoHash x y := h_ind.2.1
  have h_nohash_self : ∀ x ∈ c.nfs, ∀ y ∈ c.nfs, x ≠ y → NoHash x y := h_ind.2.2
  have h_nohash_nf : ∀ x ∈ c.nfs, NoHash x nf := by
    intro x hx
    by_cases heq : x = nf
    · subst heq
      exact nohash_nf x
    · exact h_nohash_self x hx nf hmem heq
  exact derivable_under_hashes c.S c.nfs nf h_op h_nohash_nf h_nohash_S h_nohash_self h_nodup

-- ============================================================================
-- 4. STRUCTURAL HOMOMORPHISM
-- ============================================================================

def mask : Term → Term
  | Term.atom _ => Term.atom "masked"
  | Term.pair t1 t2 => Term.pair (mask t1) (mask t2)
  | Term.op name t => Term.op name (mask t)
  | Term.hash t => Term.hash (mask t)

def restore : Term → String → Term
  | Term.atom _, a => Term.atom (String.append "restored_with_" a)
  | Term.pair t1 t2, a => Term.pair (restore t1 a) (restore t2 a)
  | Term.op name t, a => Term.op name (restore t a)
  | Term.hash t, a => Term.hash (restore t a)

def merge (t1 t2 : Term) : Term :=
  Term.pair t1 t2

theorem mask_distributes_over_merge (t1 t2 : Term) :
  mask (merge t1 t2) = merge (mask t1) (mask t2) := by
  rfl

theorem homomorphic_merge (t1 t2 : Term) (a : String) :
  restore (merge (mask t1) (mask t2)) a = merge (restore (mask t1) a) (restore (mask t2) a) := by
  rfl
