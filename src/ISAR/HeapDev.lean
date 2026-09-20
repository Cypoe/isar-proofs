import ISAR.GraphDev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Insert

/-!
# Heap-level development — the non-linear path

`GraphDev` models the host `Graph.cd` as an append-only relation: the
readback `dagUnfold` quotients away `fwd` redirects and hash-consing.
This file models the heap itself — nodes, forward chains (`repr`), and
the redirect discipline the host `Graph` maintains — so the shared-dag
(non-linear) execution path is covered by proofs, for the live runtime
*and* for compile-time evaluation (cogen/specialization run the same
`cd`).

Design notes:

- **No memo in the model.**  Under the seal discipline (`mo[out] = out`
  on every produced result node, cleared per round) the host's memo is
  semantically transparent — a hit returns exactly the node the relation
  derives.  Without the seal the host can over-develop shared subtrees
  mid-round; the seal is a small host change that makes round semantics
  exactly `DevChain`.
- **Interning is guarded.**  `mkApp` may return a fresh node or an
  existing one with the same children, but a redirect may never target a
  node that resolved-reaches its source — the no-ancestor condition that
  keeps the resolved dag acyclic.
-/

namespace ISAR

/-- Heap: node table + forwards. `fw[i] = none` means `i` is a
    representative ("rep"); `some j` means `i` reads as `j`. -/
structure Heap where
  ns : List GNode
  fw : List (Option Nat)

def Heap.len (h : Heap) : Nat := h.ns.length

/-- Follow the forward chain.  `seen` carries visited nodes; a repeat
    means a forward cycle (dead code under `FwOk`).  Terminates because
    the unvisited in-range set strictly shrinks. -/
def resolveS (fw : List (Option Nat)) (seen : Finset Nat) (i : Nat) :
    Option Nat :=
  if i ∈ seen then none
  else
    match hnode : fw[i]? with
    | none => none
    | some none => some i
    | some (some j) => resolveS fw (insert i seen) j
termination_by (Finset.range fw.length \ seen).card
decreasing_by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hnode
  have hi : i ∈ Finset.range fw.length \ seen :=
    Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hlt, ‹i ∉ seen›⟩
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem hi

/-- Representative of `i`: the end of its forward chain, or `i` itself
    when resolution fails (dead code under `FwOk`). -/
def Heap.repr (h : Heap) (i : Nat) : Nat :=
  (resolveS h.fw ∅ i).getD i

/-- `i` is a representative (no outgoing forward). -/
def Heap.isRep (h : Heap) (i : Nat) : Prop := h.fw[i]? = some none

/-- Fresh allocation: append the node and a fresh rep slot.  Mirrors
    `Graph.mk_node` (without interning — interning is folded into the
    redirect guards). -/
def Heap.push (h : Heap) (n : GNode) : Heap :=
  ⟨h.ns ++ [n], h.fw ++ [none]⟩

/-- Forward-table well-formedness: every in-range index resolves to an
    in-range rep. -/
def FwOk (fw : List (Option Nat)) : Prop :=
  ∀ i, i < fw.length →
    ∃ r, r < fw.length ∧ fw[r]? = some none ∧ resolveS fw ∅ i = some r

/-- `resolveS` result is always a rep below the table length. -/
theorem resolveS_spec {fw : List (Option Nat)} {seen : Finset Nat} {i r : Nat}
    (h : resolveS fw seen i = some r) :
    r < fw.length ∧ fw[r]? = some none := by
  fun_induction resolveS fw seen i generalizing r
  case case1 s i hiseen => simp at h
  case case2 s i hiseen hv => simp at h
  case case3 s i hiseen hv =>
    obtain rfl : i = r := by simpa using h
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hv
    exact ⟨hlt, hv⟩
  case case4 s i hiseen j hv ih => exact ih h

theorem resolveS_rep {fw : List (Option Nat)} {seen : Finset Nat} {i : Nat}
    (hseen : i ∉ seen) (hrep : fw[i]? = some none) :
    resolveS fw seen i = some i := by
  rw [resolveS, if_neg hseen, hrep]

/-- Under `FwOk`, `repr` always lands on an in-range rep. -/
theorem Heap.repr_spec {h : Heap} (hfw : FwOk h.fw) {i : Nat}
    (hi : i < h.fw.length) :
    h.repr i < h.fw.length ∧ h.fw[h.repr i]? = some none ∧
      resolveS h.fw ∅ i = some (h.repr i) := by
  obtain ⟨r, hrlt, hrep, hres⟩ := hfw i hi
  have hrepr : h.repr i = r := by
    simp only [Heap.repr, hres, Option.getD_some]
  subst hrepr
  exact ⟨hrlt, hrep, hres⟩

theorem Heap.repr_eq {h : Heap} (hfw : FwOk h.fw) {i : Nat}
    (hi : i < h.fw.length) :
    resolveS h.fw ∅ i = some (h.repr i) :=
  (h.repr_spec hfw hi).2.2



/-- The redirect lemma: writing `fw[src] := some dst` (both reps,
    `src ≠ dst`) retargets chains that ended at `src` onto `dst`; all
    other chains are unchanged.  This is the host `Graph.redirect` at
    the level of `repr`. -/
theorem resolveS_set {fw : List (Option Nat)} {src dst : Nat}
    (hsrc : fw[src]? = some none) (hdst : fw[dst]? = some none)
    (hne : src ≠ dst)
    {seen : Finset Nat} {m r : Nat} (hdseen : dst ∉ seen)
    (h : resolveS fw seen m = some r) :
    resolveS (fw.set src (some dst)) seen m =
      some (if r = src then dst else r) := by
  fun_induction resolveS fw seen m generalizing r
  case case1 s m hmseen => simp at h
  case case2 s m hmseen hv => simp at h
  case case3 s m hmseen hv =>
    -- `m` is a rep in `fw`; the old run returned `m` itself.
    have hmr : m = r := Option.some.inj h
    rw [← hmr]
    rcases Nat.decEq m src with hmi | hmi
    · -- `m ≠ src`: the rep is untouched.
      have h2 : resolveS (fw.set src (some dst)) s m = some m :=
        resolveS_rep hmseen ((List.getElem?_set_ne (Ne.symm hmi)).trans hv)
      rw [h2, if_neg hmi]
    · -- `m = src`: the new run follows the fresh edge to `dst`.
      rw [if_pos hmi]
      obtain ⟨hilt, _⟩ := List.getElem?_eq_some_iff.1 hsrc
      have hset : (fw.set src (some dst))[m]? = some (some dst) := by
        rw [hmi]; exact List.getElem?_set_self hilt
      have hstep : resolveS (fw.set src (some dst)) s m =
          resolveS (fw.set src (some dst)) (insert m s) dst := by
        rw [resolveS, if_neg hmseen, hset]
      rw [hstep]
      have hd2 : dst ∉ insert m s := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun hc => hne (hc.trans hmi).symm, hdseen⟩
      have hdrep : (fw.set src (some dst))[dst]? = some none := by
        rw [List.getElem?_set_ne hne]; exact hdst
      exact resolveS_rep hd2 hdrep
  case case4 s m hmseen n hv ih =>
    -- `m → n` in `fw`; the new run takes the same hop (m is a non-rep,
    -- hence `m ≠ src`).
    obtain ⟨hmlt, -⟩ := List.getElem?_eq_some_iff.1 hv
    have hmi : m ≠ src := by
      intro hc; subst hc; rw [hv] at hsrc; simp at hsrc
    have hstep : resolveS (fw.set src (some dst)) s m =
        resolveS (fw.set src (some dst)) (insert m s) n := by
      rw [resolveS, if_neg hmseen, List.getElem?_set_ne (Ne.symm hmi), hv]
    rw [hstep]
    have hdn : dst ∉ insert m s := by
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, hdseen⟩
      intro hc; subst hc
      rw [hv] at hdst; simp at hdst
    exact ih hdn h

/-- Extension: `resolveS` is unchanged when the table grows on the
    right (existing entries untouched).  This covers heap allocation. -/
theorem resolveS_extend {fw fw' : List (Option Nat)}
    (hext : ∀ k, k < fw.length → fw'[k]? = fw[k]?)
    {seen : Finset Nat} {i r : Nat} (h : resolveS fw seen i = some r) :
    resolveS fw' seen i = some r := by
  fun_induction resolveS fw seen i generalizing r
  case case1 s i hiseen => simp at h
  case case2 s i hiseen hv => simp at h
  case case3 s i hiseen hv =>
    obtain rfl : i = r := by simpa using h
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hv
    rw [resolveS, if_neg hiseen, hext i hlt, hv]
  case case4 s i hiseen j hv ih =>
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hv
    have h2 : resolveS fw' s i = resolveS fw' (insert i s) j := by
      rw [resolveS, if_neg hiseen, hext i hlt, hv]
    rw [h2]
    exact ih h

/-- Resolved-child relation: `j` is the representative of a child of
    the node `i` resolves to.  Readback recurses along this relation;
    `repr` may jump forwards, so index order cannot bound it. -/
def RChild (h : Heap) (j i : Nat) : Prop :=
  ∃ l r, h.ns[h.repr i]? = some (GNode.app l r) ∧
    (h.repr l = j ∨ h.repr r = j)

/-- Resolved strict reachability. -/
def RSub (h : Heap) (j i : Nat) : Prop :=
  Relation.TransGen (RChild h) j i

/-- The resolved dag has no cycles.  Interning and redirects must not
    create one — this is the guard the host's hash-consing side-steps
    and the proof obligation a compile-time evaluator shares. -/
def Acyc (h : Heap) : Prop := ∀ i, ¬ RSub h i i

/-- A heap whose node table is a dag, whose forwards resolve, and whose
    resolved view is acyclic. -/
structure HeapWf (h : Heap) : Prop where
  dagwf : DagWf h.ns
  fwlen : h.fw.length = h.ns.length
  fwok : FwOk h.fw
  acyc : Acyc h

/-- Everything resolved-below `i`, in range.  The strict-descendant
    count is the termination measure for `heapUnfold`. -/
noncomputable def RSubSet (h : Heap) (i : Nat) : Finset Nat := by
  classical
  exact (Finset.range h.len).filter (fun j => RSub h j i)

/-- Resolved children are in range. -/
theorem RChild_lt {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j i) : j < h.len := by
  obtain ⟨l, r, hnode, hj⟩ := hc
  obtain ⟨hlt, hnode'⟩ := List.getElem?_eq_some_iff.1 hnode
  obtain ⟨hli, hri⟩ := hwf.dagwf (h.repr i) hlt l r hnode'
  have hlf : l < h.fw.length := by rw [hwf.fwlen]; omega
  have hrf : r < h.fw.length := by rw [hwf.fwlen]; omega
  rcases hj with hjl | hjr
  next =>
    rw [← hjl]
    show h.repr l < h.ns.length
    rw [← hwf.fwlen]
    exact (h.repr_spec hwf.fwok hlf).1
  next =>
    rw [← hjr]
    show h.repr r < h.ns.length
    rw [← hwf.fwlen]
    exact (h.repr_spec hwf.fwok hrf).1

/-- The strict-descendant count drops along a resolved-child step. -/
theorem RSubSet_lt {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j i) : (RSubSet h j).card < (RSubSet h i).card := by
  have hsub : RSubSet h j ⊆ RSubSet h i := by
    intro k hk
    simp only [RSubSet, Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨hk.1, Relation.TransGen.trans hk.2 (Relation.TransGen.single hc)⟩
  have hji : j ∈ RSubSet h i := by
    simp only [RSubSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨RChild_lt hwf hc, Relation.TransGen.single hc⟩
  have hnj : j ∉ RSubSet h j := by
    simp only [RSubSet, Finset.mem_filter]
    intro hmem
    exact hwf.acyc j hmem.2
  exact Finset.card_lt_card
    (Finset.ssubset_iff.2 ⟨j, hnj, Finset.insert_subset_iff.2 ⟨hji, hsub⟩⟩)

/-- Redirect a heap: `src ↦ dst` in the forward table.  Mirrors
    `Graph.redirect` (which redirects resolved reps). -/
def Heap.redirect (h : Heap) (src dst : Nat) : Heap :=
  ⟨h.ns, h.fw.set src (some dst)⟩

theorem FwOk_redirect {h : Heap} (hfw : FwOk h.fw) {src dst : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hdlt : dst < h.fw.length) :
    FwOk ((h.redirect src dst).fw) := by
  intro m hm
  have hmlt : m < h.fw.length := by simpa [Heap.redirect] using hm
  obtain ⟨r, hrlt, hrep, hres⟩ := hfw m hmlt
  have hde : dst ∉ (∅ : Finset Nat) := by simp
  rcases Nat.decEq r src with heq | heq
  · -- `r ≠ src`: the representative is unchanged.
    refine Exists.intro r (And.intro ?_ (And.intro ?_ ?_))
    next =>
      rw [show (h.redirect src dst).fw = h.fw.set src (some dst) from rfl,
          List.length_set]
      exact hrlt
    next =>
      rw [show (h.redirect src dst).fw = h.fw.set src (some dst) from rfl,
          List.getElem?_set_ne (Ne.symm heq)]
      exact hrep
    next =>
      rw [show (h.redirect src dst).fw = h.fw.set src (some dst) from rfl,
          resolveS_set hsrc hdst hne hde hres, if_neg heq]
  · -- `r = src`: the representative is now `dst`.
    refine Exists.intro dst (And.intro ?_ (And.intro ?_ ?_))
    next =>
      rw [show (h.redirect src dst).fw = h.fw.set src (some dst) from rfl,
          List.length_set]
      exact hdlt
    next =>
      rw [show (h.redirect src dst).fw = h.fw.set src (some dst) from rfl,
          List.getElem?_set_ne hne]
      exact hdst
    next =>
      rw [show (h.redirect src dst).fw = h.fw.set src (some dst) from rfl,
          resolveS_set hsrc hdst hne hde hres, if_pos heq]

/-- Allocating a fresh node appends a rep to the forward table. -/
theorem FwOk_push {fw : List (Option Nat)} (hfw : FwOk fw) :
    FwOk (fw ++ [none]) := by
  intro i hi
  have hlen : (fw ++ [none]).length = fw.length + 1 := by simp
  rw [hlen] at hi
  rcases Nat.lt_or_ge i fw.length with hlt | hge
  case inl =>
    obtain ⟨r, hrlt, hrep, hres⟩ := hfw i hlt
    refine Exists.intro r (And.intro ?_ (And.intro ?_ ?_))
    next =>
      rw [hlen]; omega
    next =>
      rw [List.getElem?_append_left hrlt]; exact hrep
    next =>
      exact resolveS_extend (fun k hk => List.getElem?_append_left hk) hres
  case inr =>
    have hi2 : i = fw.length := by omega
    subst hi2
    refine Exists.intro fw.length (And.intro ?_ (And.intro ?_ ?_))
    next =>
      rw [hlen]; omega
    next =>
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    next =>
      rw [resolveS, if_neg (by simp), List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self]
      rfl

/-- `repr` is stable under allocation (the new slot is a fresh rep). -/
theorem Heap.repr_push {h : Heap} (hfw : FwOk h.fw) (n : GNode) {i : Nat}
    (hi : i < h.fw.length) :
    (h.push n).repr i = h.repr i := by
  obtain ⟨r, -, -, hres⟩ := hfw i hi
  show (resolveS (h.fw ++ [none]) ∅ i).getD i = h.repr i
  rw [resolveS_extend (fun k hk => List.getElem?_append_left hk) hres]
  simp [Heap.repr, hres, Option.getD_some]

/-- `h.len` unfolds to `h.ns.length`. -/
theorem Heap.len_eq (h : Heap) : h.len = h.ns.length := rfl

/-- The fresh index resolves to itself. -/
theorem Heap.repr_push_fresh {h : Heap} (hlen : h.fw.length = h.ns.length)
    (n : GNode) : (h.push n).repr h.len = h.len := by
  show (resolveS (h.fw ++ [none]) ∅ h.ns.length).getD h.ns.length = h.ns.length
  rw [← hlen]
  rw [resolveS, if_neg (by simp)]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Out-of-range lookups resolve to `none`. -/
theorem resolveS_oob {fw : List (Option Nat)} {seen : Finset Nat} {i : Nat}
    (hseen : i ∉ seen) (hi : fw.length ≤ i) :
    resolveS fw seen i = none := by
  rw [resolveS, if_neg hseen]
  have hn : fw[i]? = none := List.getElem?_eq_none_iff.mpr hi
  rw [hn]

/-- The only node resolving to the fresh index is the fresh index:
    no old forward slot can point at `h.len` under `FwOk` (it would
    have resolved out-of-bounds before the push). -/
theorem resolveS_push_fresh {h : Heap} (hwf : HeapWf h) (n : GNode)
    {seen : Finset Nat} {c : Nat}
    (hr : resolveS (h.push n).fw seen c = some h.len) : c = h.len := by
  fun_induction resolveS (h.push n).fw seen c
  case case1 s m hmseen => simp at hr
  case case2 s m hmseen hv => simp at hr
  case case3 s m hmseen hv => simpa using hr
  case case4 s m hmseen j hv ih =>
    have hjl : j = h.len := ih hr
    subst hjl
    have hflen : (h.push n).fw.length = h.fw.length + 1 := by
      simp [Heap.push]
    have hmlt : m < h.fw.length + 1 := by
      have hb := (List.getElem?_eq_some_iff.1 hv).1
      omega
    rcases Nat.lt_or_ge m h.fw.length with hlt | hge
    case inl =>
      -- `m < fw.length`: the old table would forward `m` to `len`,
      -- then hit out-of-bounds — contradicting `FwOk`.
      have hv' : h.fw[m]? = some (some h.len) := by
        have h1 : (h.push n).fw = h.fw ++ [none] := rfl
        rw [h1, List.getElem?_append_left hlt] at hv
        exact hv
      obtain ⟨rc, hrc, hrep, hres⟩ := hwf.fwok m hlt
      rw [resolveS, if_neg (by simp), hv'] at hres
      simp at hres
      have hle : h.len = h.fw.length := by
        rw [Heap.len_eq]; exact hwf.fwlen.symm
      have hnotmem : h.len ∉ ({m} : Finset Nat) := by
        intro hc2
        simp at hc2
        omega
      rw [resolveS_oob hnotmem (le_of_eq hle.symm)] at hres
      simp at hres
    case inr =>
      -- `m ≥ fw.length` with `m < fw.length + 1` gives `m = len` — the goal.
      have h2 : h.len = h.fw.length := by
        rw [Heap.len_eq]; exact hwf.fwlen.symm
      omega

/-- `repr` on the pushed heap never maps to the fresh index unless the
    argument *is* the fresh index. -/
theorem repr_push_eq_len {h : Heap} (hwf : HeapWf h) (n : GNode) {c : Nat}
    (hc : (h.push n).repr c = h.len) : c = h.len := by
  unfold Heap.repr at hc
  cases hres : resolveS (h.push n).fw ∅ c with
  | none =>
      rw [hres] at hc
      simp at hc
      exact hc
  | some r =>
      rw [hres] at hc
      simp at hc
      subst hc
      exact resolveS_push_fresh hwf n hres

/-- Allocation preserves `DagWf` when the pushed node's children are
    in range of the *old* table. -/
theorem DagWf_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) :
    DagWf (h.push n).ns := by
  intro i hi l r hnode
  have hnode' : (h.ns ++ [n])[i]? = some (GNode.app l r) := by
    have h2 : (h.push n).ns[i]? = some (GNode.app l r) :=
      (List.getElem?_eq_some_iff).2 ⟨hi, hnode⟩
    rw [show (h.push n).ns = h.ns ++ [n] from rfl] at h2
    exact h2
  have hilen : i < h.ns.length + 1 := by
    have hl : (h.ns ++ [n]).length = h.ns.length + 1 := by simp
    have : i < (h.ns ++ [n]).length := hi
    omega
  rcases Nat.lt_or_ge i h.ns.length with hlt | hge
  case inl =>
    rw [List.getElem?_append_left hlt] at hnode'
    exact hwf.dagwf i hlt l r (List.getElem?_eq_some_iff.1 hnode').2
  case inr =>
    have hi2 : i = h.ns.length := by omega
    subst hi2
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hnode'
    simp at hnode'
    subst hnode'
    exact hn l r rfl

/-- The fresh index is never a resolved child (nothing can point at it
    and resolving to it means being it). -/
theorem RChild_fresh_source {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) {i : Nat}
    (hc : RChild (h.push n) h.len i) : False := by
  obtain ⟨l, r, hnode, hj⟩ := hc
  have hlt : (h.push n).repr i < (h.push n).ns.length :=
    (List.getElem?_eq_some_iff.1 hnode).1
  have hwf' : DagWf (h.push n).ns := DagWf_push hwf hn
  obtain ⟨hli, hri⟩ := hwf' ((h.push n).repr i) hlt l r
    (List.getElem?_eq_some_iff.1 hnode).2
  rcases hj with hjl | hjr
  next =>
    have hle : l = h.len := repr_push_eq_len hwf n hjl
    subst hle
    rw [Heap.len_eq] at hli
    rw [show (h.push n).ns = h.ns ++ [n] from rfl] at hlt
    simp at hlt
    omega
  next =>
    have hle : r = h.len := repr_push_eq_len hwf n hjr
    subst hle
    rw [Heap.len_eq] at hri
    rw [show (h.push n).ns = h.ns ++ [n] from rfl] at hlt
    simp at hlt
    omega

/-- The fresh index starts no `RSub` chain. -/
theorem RSub_fresh_source {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) {i : Nat}
    (hsub : RSub (h.push n) h.len i) : False := by
  suffices hs : ∀ j, RSub (h.push n) j i → j ≠ h.len from hs _ hsub rfl
  intro j hj
  induction hj using Relation.TransGen.head_induction_on with
  | single hstep =>
      intro hje
      subst hje
      exact RChild_fresh_source hwf hn hstep
  | head hstep _hsub _ih =>
      intro hje
      subst hje
      exact RChild_fresh_source hwf hn hstep

/-- Out-of-range indices have no resolved children. -/
theorem RChild_oob_parent {h : Heap} (hfwlen : h.fw.length = h.ns.length) {j i : Nat}
    (hi : h.len ≤ i) : ¬ RChild h j i := by
  rw [Heap.len_eq] at hi
  intro hc
  obtain ⟨l, r, hnode, _⟩ := hc
  have hrep : h.repr i = i := by
    unfold Heap.repr
    rw [resolveS_oob (by simp) (by rw [hfwlen]; exact hi)]
    rfl
  have hlt : h.repr i < h.ns.length := (List.getElem?_eq_some_iff.1 hnode).1
  omega

/-- Resolved-child parents are in range. -/
theorem RChild_parent_lt {h : Heap} (hfwlen : h.fw.length = h.ns.length) {j i : Nat}
    (hc : RChild h j i) : i < h.len := by
  rcases Nat.lt_or_ge i h.len with hi | hi
  case inl => exact hi
  case inr => exact absurd hc (RChild_oob_parent hfwlen hi)

/-- `RSub` chain sources (descendant ends) are in range. -/
theorem RSub_source_lt {h : Heap} (hwf : HeapWf h) {i j : Nat}
    (hsub : RSub h i j) : i < h.len := by
  induction hsub using Relation.TransGen.head_induction_on with
  | single hstep => exact RChild_lt hwf hstep
  | head hstep _hsub _ih => exact RChild_lt hwf hstep

/-- Resolved children in the *pushed* heap are below `h.len` — proved
    from the old invariant plus `DagWf_push`, without needing `Acyc` of
    the new heap (avoids circularity in `Acyc_push`). -/
theorem RChild_push_child_lt {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) {j i : Nat}
    (hc : RChild (h.push n) j i) : j < h.len := by
  obtain ⟨l, r, hnode, hj⟩ := hc
  have hlt : (h.push n).repr i < (h.push n).ns.length :=
    (List.getElem?_eq_some_iff.1 hnode).1
  have hwf' : DagWf (h.push n).ns := DagWf_push hwf hn
  obtain ⟨hli, hri⟩ := hwf' ((h.push n).repr i) hlt l r
    (List.getElem?_eq_some_iff.1 hnode).2
  have hle : (h.push n).repr i ≤ h.len := by
    have hlen' : (h.push n).ns.length = h.ns.length + 1 := by
      show (h.ns ++ [n]).length = h.ns.length + 1; simp
    rw [Heap.len_eq]
    omega
  rcases hj with hjl | hjr
  next =>
    have hlf : l < h.fw.length := by
      rw [hwf.fwlen]; rw [Heap.len_eq] at hle; omega
    rw [← hjl, Heap.repr_push hwf.fwok n hlf]
    rw [Heap.len_eq, ← hwf.fwlen]
    exact (h.repr_spec hwf.fwok hlf).1
  next =>
    have hrf : r < h.fw.length := by
      rw [hwf.fwlen]; rw [Heap.len_eq] at hle; omega
    rw [← hjr, Heap.repr_push hwf.fwok n hrf]
    rw [Heap.len_eq, ← hwf.fwlen]
    exact (h.repr_spec hwf.fwok hrf).1

/-- `RSub` sources in the pushed heap are below `h.len` — the fresh
    index never starts a chain, for free. -/
theorem RSub_source_lt_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) {i j : Nat}
    (hsub : RSub (h.push n) i j) : i < h.len := by
  induction hsub using Relation.TransGen.head_induction_on with
  | single hstep => exact RChild_push_child_lt hwf hn hstep
  | head hstep _hsub _ih => exact RChild_push_child_lt hwf hn hstep

/-- Allocation preserves resolved-child edges on old parents. -/
theorem RChild_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) {j i : Nat}
    (hi : i < h.len) : RChild (h.push n) j i ↔ RChild h j i := by
  have hifw : i < h.fw.length := by rw [hwf.fwlen]; exact hi
  have hri : (h.push n).repr i = h.repr i := Heap.repr_push hwf.fwok n hifw
  constructor
  next =>
    intro hc
    obtain ⟨l, r, hnode, hj⟩ := hc
    rw [hri] at hnode
    obtain ⟨r', hrlt, hrepa, hres⟩ := hwf.fwok i hifw
    have hrep : h.repr i = r' := by unfold Heap.repr; rw [hres]; rfl
    have hlt : h.repr i < h.ns.length := by
      have hle : h.ns.length = h.fw.length := hwf.fwlen.symm
      omega
    have hnode' : h.ns[h.repr i]? = some (GNode.app l r) := by
      rw [show (h.push n).ns = h.ns ++ [n] from rfl,
          List.getElem?_append_left hlt] at hnode
      exact hnode
    obtain ⟨hlb, hrb⟩ := hwf.dagwf (h.repr i) hlt l r
      (List.getElem?_eq_some_iff.1 hnode').2
    have hlf : l < h.fw.length := by rw [hwf.fwlen]; omega
    have hrf : r < h.fw.length := by rw [hwf.fwlen]; omega
    refine ⟨l, r, hnode', ?_⟩
    rcases hj with hjl | hjr
    next =>
      left
      rw [Heap.repr_push hwf.fwok n hlf] at hjl
      exact hjl
    next =>
      right
      rw [Heap.repr_push hwf.fwok n hrf] at hjr
      exact hjr
  next =>
    intro hc
    obtain ⟨l, r, hnode, hj⟩ := hc
    have hlt : h.repr i < h.ns.length := (List.getElem?_eq_some_iff.1 hnode).1
    have hnode' : (h.push n).ns[(h.push n).repr i]? = some (GNode.app l r) := by
      rw [hri, show (h.push n).ns = h.ns ++ [n] from rfl,
          List.getElem?_append_left hlt]
      exact hnode
    obtain ⟨hlb, hrb⟩ := hwf.dagwf (h.repr i) hlt l r
      (List.getElem?_eq_some_iff.1 hnode).2
    have hlf : l < h.fw.length := by rw [hwf.fwlen]; omega
    have hrf : r < h.fw.length := by rw [hwf.fwlen]; omega
    refine ⟨l, r, hnode', ?_⟩
    rcases hj with hjl | hjr
    next => left; rw [← hjl, Heap.repr_push hwf.fwok n hlf]
    next => right; rw [← hjr, Heap.repr_push hwf.fwok n hrf]

/-- Allocation preserves `RSub` on old endpoints. -/
theorem RSub_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) {j i : Nat}
    (hi : i < h.len) : RSub (h.push n) j i ↔ RSub h j i := by
  constructor
  next =>
    intro hsub
    induction hsub with
    | single hstep =>
        exact Relation.TransGen.single ((RChild_push hwf hn hi).mp hstep)
    | tail hbc hstep ih =>
        have hci := (RChild_push hwf hn hi).mp hstep
        exact Relation.TransGen.tail (ih (RChild_lt hwf hci)) hci
  next =>
    intro hsub
    induction hsub with
    | single hstep =>
        exact Relation.TransGen.single ((RChild_push hwf hn hi).mpr hstep)
    | tail hbc hstep ih =>
        exact Relation.TransGen.tail (ih (RChild_lt hwf hstep))
          ((RChild_push hwf hn hi).mpr hstep)

/-- `push` keeps the forward/table length invariant. -/
theorem push_fwlen {h : Heap} (hwf : HeapWf h) (n : GNode) :
    (h.push n).fw.length = (h.push n).ns.length := by
  show (h.fw ++ [none]).length = (h.ns ++ [n]).length
  simp [hwf.fwlen]

/-- Allocation preserves acyclicity. -/
theorem Acyc_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) :
    Acyc (h.push n) := by
  intro i hsub
  rcases Nat.lt_or_ge i h.len with hi | hi
  case inl =>
    exact hwf.acyc i ((RSub_push hwf hn hi).mp hsub)
  case inr =>
    have hlt' : i < h.len := RSub_source_lt_push hwf hn hsub
    omega

/-- Allocation preserves `HeapWf`: the pushed node's children must point
    into the old table (the host's `mk_app` obligation). -/
theorem HeapWf_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) :
    HeapWf (h.push n) where
  dagwf := DagWf_push hwf hn
  fwlen := push_fwlen hwf n
  fwok := FwOk_push hwf.fwok
  acyc := Acyc_push hwf hn

/-- `RChild` agrees on old parents after allocation. -/
theorem RChild_push_old {h : Heap} (hwf : HeapWf h) (n : GNode) {j i : Nat}
    (hi : i < h.len) : RChild (h.push n) j i ↔ RChild h j i := by
  have hfl : h.fw.length = h.ns.length := hwf.fwlen
  constructor
  next =>
    intro hc
    obtain ⟨l, r, hnode, hj⟩ := hc
    have hri : h.repr i < h.fw.length :=
      (h.repr_spec hwf.fwok (by rw [hwf.fwlen]; exact hi)).1
    have hrep : (h.push n).repr i = h.repr i :=
      h.repr_push hwf.fwok n (by rw [hwf.fwlen]; exact hi)
    rw [hrep] at hnode
    rw [show (h.push n).ns = h.ns ++ [n] from rfl] at hnode
    rw [List.getElem?_append_left (by rw [hwf.fwlen] at hri; exact hri)]
      at hnode
    obtain ⟨hli, hri'⟩ := hwf.dagwf (h.repr i)
      (by rw [← hwf.fwlen]; exact hri) l r
      (List.getElem?_eq_some_iff.1 hnode).2
    have hlf : l < h.fw.length := by rw [hwf.fwlen]; omega
    have hrf : r < h.fw.length := by rw [hwf.fwlen]; omega
    refine ⟨l, r, hnode, ?_⟩
    rcases hj with hjl | hjr
    next =>
      left
      rw [← hjl]
      exact (h.repr_push hwf.fwok n hlf).symm
    next =>
      right
      rw [← hjr]
      exact (h.repr_push hwf.fwok n hrf).symm
  next =>
    intro hc
    obtain ⟨l, r, hnode, hj⟩ := hc
    have hri : h.repr i < h.fw.length :=
      (h.repr_spec hwf.fwok (by rw [hwf.fwlen]; exact hi)).1
    obtain ⟨hli, hri'⟩ := hwf.dagwf (h.repr i)
      (by rw [← hwf.fwlen]; exact hri) l r
      (List.getElem?_eq_some_iff.1 hnode).2
    have hlf : l < h.fw.length := by rw [hwf.fwlen]; omega
    have hrf : r < h.fw.length := by rw [hwf.fwlen]; omega
    refine ⟨l, r, ?_, ?_⟩
    next =>
      rw [show (h.push n).ns = h.ns ++ [n] from rfl]
      rw [h.repr_push hwf.fwok n (by rw [hwf.fwlen]; exact hi)]
      rw [List.getElem?_append_left (by rw [hwf.fwlen] at hri; exact hri)]
      exact hnode
    next =>
      rcases hj with hjl | hjr
      next =>
        left
        rw [← hjl, h.repr_push hwf.fwok n hlf]
      next =>
        right
        rw [← hjr, h.repr_push hwf.fwok n hrf]

/-- Heap-level readback: resolve `i`, unfold its node, recurse into the
    *resolved* children.  Terminates because the strict-descendant set
    shrinks (each step moves to a `RChild`, and acyclicity keeps the
    descent strict).  `hwf` carries the invariants the measure needs. -/
noncomputable def heapUnfold (h : Heap) (hwf : HeapWf h) (i : Nat) :
    ITerm :=
  match hnode : h.ns[h.repr i]? with
  | some (GNode.app l r) =>
      ITerm.app (heapUnfold h hwf (h.repr l)) (heapUnfold h hwf (h.repr r))
  | some (GNode.atom a) => a.toTerm
  | some (GNode.var n) => ITerm.var n
  | none => ITerm.var 0
termination_by (RSubSet h i).card
decreasing_by
  all_goals
    exact RSubSet_lt hwf ⟨_, _, hnode,
      by first | exact Or.inl rfl | exact Or.inr rfl⟩

/-- `repr` after a redirect. -/
theorem Heap.repr_redirect {h : Heap} (hfw : FwOk h.fw) {src dst m : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hm : m < h.fw.length) :
    (h.redirect src dst).repr m =
      if h.repr m = src then dst else h.repr m := by
  obtain ⟨r, hrlt, hrep, hres⟩ := hfw m hm
  have hde : dst ∉ (∅ : Finset Nat) := by simp
  have hrepr : h.repr m = r := by
    simp only [Heap.repr, hres, Option.getD_some]
  show (resolveS (h.fw.set src (some dst)) ∅ m).getD m = _
  rw [resolveS_set hsrc hdst hne hde hres]
  simp [hrepr]

/-- `repr` of a representative is itself. -/
theorem Heap.repr_of_isRep {h : Heap} {x : Nat}
    (hx : h.fw[x]? = some none) : h.repr x = x := by
  unfold Heap.repr
  rw [resolveS, if_neg (by simp), hx]
  rfl

/-- Representatives stay in range under `FwOk`. -/
theorem Heap.isRep_of_repr {h : Heap} (hfw : FwOk h.fw) {x : Nat}
    (hx : x < h.fw.length) : h.isRep (h.repr x) := by
  obtain ⟨r, -, hrep, hres⟩ := hfw x hx
  have : h.repr x = r := by unfold Heap.repr; rw [hres]; rfl
  rw [this]; exact hrep

/-- `redirect` keeps `fw`/`ns` lengths aligned. -/
theorem redirect_fwlen {h : Heap} (hwf : HeapWf h) (src dst : Nat) :
    (h.redirect src dst).fw.length = (h.redirect src dst).ns.length := by
  show (h.fw.set src (some dst)).length = h.ns.length
  rw [List.length_set]; exact hwf.fwlen

/-- Resolved-child edges after `src ↦ dst`: the parent reads the node at
    `σ i` (`dst` when `i` resolved to `src`), and each child is lifted
    through `σ` — so a post-redirect edge is an old edge into `σ i`
    whose child resolves as `σ a = j`. -/
theorem RChild_redirect {h : Heap} (hwf : HeapWf h) {src dst j i : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst)
    (hc : RChild (h.redirect src dst) j i) :
    ∃ a, h.isRep a ∧
      RChild h a (if h.repr i = src then dst else h.repr i) ∧
      ((a = j ∧ a ≠ src) ∨ (a = src ∧ j = dst)) := by
  have hi : i < h.len := RChild_parent_lt (redirect_fwlen hwf src dst) hc
  obtain ⟨l, r, hnode, hj⟩ := hc
  have hifw : i < h.fw.length := by rw [hwf.fwlen]; exact hi
  have hri : (h.redirect src dst).repr i =
      if h.repr i = src then dst else h.repr i :=
    Heap.repr_redirect hwf.fwok hsrc hdst hne hifw
  rw [hri] at hnode
  have hnode' : h.ns[if h.repr i = src then dst else h.repr i]? =
      some (GNode.app l r) := by
    have h1 : (h.redirect src dst).ns = h.ns := rfl
    rw [h1] at hnode
    exact hnode
  -- `σ i` is an old rep, so `RChild h a (σ i)` unfolds on the same node.
  have hsig : h.isRep (if h.repr i = src then dst else h.repr i) := by
    rcases Nat.decEq (h.repr i) src with hnos | hys
    case isTrue =>
      rw [if_pos hys]; exact hdst
    case isFalse =>
      rw [if_neg hnos]; exact Heap.isRep_of_repr hwf.fwok hifw
  have hlt : (if h.repr i = src then dst else h.repr i) < h.ns.length :=
    (List.getElem?_eq_some_iff.1 hnode').1
  obtain ⟨hlb, hrb⟩ := hwf.dagwf _ hlt l r
    (List.getElem?_eq_some_iff.1 hnode').2
  have hlf : l < h.fw.length := by rw [hwf.fwlen]; omega
  have hrf : r < h.fw.length := by rw [hwf.fwlen]; omega
  have hrl : (h.redirect src dst).repr l =
      if h.repr l = src then dst else h.repr l :=
    Heap.repr_redirect hwf.fwok hsrc hdst hne hlf
  have hrr : (h.redirect src dst).repr r =
      if h.repr r = src then dst else h.repr r :=
    Heap.repr_redirect hwf.fwok hsrc hdst hne hrf
  have hrepsig : h.repr (if h.repr i = src then dst else h.repr i) =
      (if h.repr i = src then dst else h.repr i) :=
    Heap.repr_of_isRep hsig
  rcases hj with hjl | hjr
  next =>
    rw [hrl] at hjl
    refine ⟨h.repr l, Heap.isRep_of_repr hwf.fwok hlf, ?_, ?_⟩
    next =>
      refine ⟨l, r, ?_, Or.inl rfl⟩
      rw [hrepsig]; exact hnode'
    next =>
      rcases Nat.decEq (h.repr l) src with hnos | hys
      case isTrue =>
        rw [if_pos hys] at hjl
        exact Or.inr ⟨hys, hjl.symm⟩
      case isFalse =>
        rw [if_neg hnos] at hjl
        exact Or.inl ⟨hjl, hnos⟩
  next =>
    rw [hrr] at hjr
    refine ⟨h.repr r, Heap.isRep_of_repr hwf.fwok hrf, ?_, ?_⟩
    next =>
      refine ⟨l, r, ?_, Or.inr rfl⟩
      rw [hrepsig]; exact hnode'
    next =>
      rcases Nat.decEq (h.repr r) src with hnos | hys
      case isTrue =>
        rw [if_pos hys] at hjr
        exact Or.inr ⟨hys, hjr.symm⟩
      case isFalse =>
        rw [if_neg hnos] at hjr
        exact Or.inl ⟨hjr, hnos⟩

/-- Post-redirect `repr` values are old representatives and never `src`
    (`src` is unreachable through `repr` after the redirect). -/
theorem redirect_repr_isRep {h : Heap} (hwf : HeapWf h) {src dst c : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hc : c < h.fw.length) :
    h.isRep ((h.redirect src dst).repr c) ∧
    (h.redirect src dst).repr c ≠ src := by
  rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hc]
  rcases Nat.decEq (h.repr c) src with hnos | hys
  case isTrue =>
    rw [if_pos hys]; exact ⟨hdst, Ne.symm hne⟩
  case isFalse =>
    rw [if_neg hnos]
    exact ⟨Heap.isRep_of_repr hwf.fwok hc, hnos⟩

/-- `σ` is the identity on post-redirect `repr` values. -/
theorem sigma_eq_of_post {h : Heap} (hwf : HeapWf h) {src dst j c : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hc : c < h.fw.length)
    (hj : (h.redirect src dst).repr c = j) :
    (if h.repr j = src then dst else h.repr j) = j := by
  obtain ⟨hrep, hne2⟩ := redirect_repr_isRep hwf hsrc hdst hne hc
  rw [hj] at hrep hne2
  have hrepj : h.repr j = j := Heap.repr_of_isRep hrep
  rw [if_neg (by rw [hrepj]; exact hne2)]
  exact hrepj

/-- Lifting a post-redirect `RSub` chain to old chains: either a plain
    old chain to `σ i`, or a chain that reaches `dst`, teleports to
    `src`, and continues to `σ i`. -/
theorem RSub_redirect {h : Heap} (hwf : HeapWf h) {src dst j i : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst)
    (hsub : RSub (h.redirect src dst) j i) :
    ∃ c, h.isRep c ∧
      ((c = j ∧ c ≠ src) ∨ (c = src ∧ j = dst)) ∧
      (RSub h c (if h.repr i = src then dst else h.repr i) ∨
       (RSub h c dst ∧
        RSub h src (if h.repr i = src then dst else h.repr i))) := by
  induction hsub with
  | single hstep =>
      obtain ⟨a, har, hstep', haj⟩ := RChild_redirect hwf hsrc hdst hne hstep
      exact ⟨a, har, haj, Or.inl (Relation.TransGen.single hstep')⟩
  | tail hbc hstep ih =>
      rename_i b cc
      obtain ⟨a, har, hstep', hab⟩ := RChild_redirect hwf hsrc hdst hne hstep
      -- `b` is a post-redirect rep, hence `σ b = b`.
      obtain ⟨l0, r0, hnode0, hjb⟩ := hstep
      have hb0 : (h.redirect src dst).repr cc < (h.redirect src dst).ns.length :=
        (List.getElem?_eq_some_iff.1 hnode0).1
      have hwf'd : DagWf (h.redirect src dst).ns := hwf.dagwf
      obtain ⟨hl0, hr0⟩ := hwf'd _ hb0 l0 r0
        (List.getElem?_eq_some_iff.1 hnode0).2
      have hl0' : l0 < h.fw.length := by
        have h1 : (h.redirect src dst).ns.length = h.ns.length := rfl
        rw [h1] at hb0
        rw [hwf.fwlen]; omega
      have hr0' : r0 < h.fw.length := by
        have h1 : (h.redirect src dst).ns.length = h.ns.length := rfl
        rw [h1] at hb0
        rw [hwf.fwlen]; omega
      have hsb : (if h.repr b = src then dst else h.repr b) = b := by
        rcases hjb with hj1 | hj2
        next => exact sigma_eq_of_post hwf hsrc hdst hne hl0' hj1
        next => exact sigma_eq_of_post hwf hsrc hdst hne hr0' hj2
      rw [hsb] at ih
      obtain ⟨c, hcr, hjc, hchain⟩ := ih
      rcases hab with ⟨h1, -⟩ | ⟨h2, h3⟩
      next =>
        -- `a = b`: contiguous old edge `b → σ cc` composed after ih.
        rcases hchain with hc1 | ⟨hc2a, hc2b⟩
        next =>
          exact ⟨c, hcr, hjc, Or.inl
            (Relation.TransGen.tail hc1 (by rw [h1] at hstep'; exact hstep'))⟩
        next =>
          exact ⟨c, hcr, hjc, Or.inr ⟨hc2a,
            Relation.TransGen.tail hc2b (by rw [h1] at hstep'; exact hstep')⟩⟩
      next =>
        -- `a = src, b = dst`: the teleport step.
        subst h3
        rcases hchain with hc1 | ⟨hc2a, hc2b⟩
        next =>
          exact ⟨c, hcr, hjc, Or.inr ⟨hc1,
            Relation.TransGen.single (by rw [h2] at hstep'; exact hstep')⟩⟩
        next =>
          exact ⟨c, hcr, hjc, Or.inr ⟨hc2a,
            Relation.TransGen.single (by rw [h2] at hstep'; exact hstep')⟩⟩

/-- Redirect preserves acyclicity when `dst` does not resolve-reach
    `src` — the splice guard: merging `src` into `dst` closes a cycle
    exactly when an old path `dst →+ src` exists. -/
theorem Acyc_redirect {h : Heap} (hwf : HeapWf h) {src dst : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hguard : ¬ RSub h src dst) :
    Acyc (h.redirect src dst) := by
  intro i hsub
  obtain ⟨c, hcr, hjc, hchain⟩ := RSub_redirect hwf hsrc hdst hne hsub
  rcases hjc with ⟨h1, h2⟩ | ⟨h3, h4⟩
  next =>
    -- `c = i`, `i ≠ src`: `i` is a rep, so `σ i = i`.
    subst h1
    have hrep : h.repr c = c := Heap.repr_of_isRep hcr
    have hsi : (if h.repr c = src then dst else h.repr c) = c := by
      rw [if_neg (by rw [hrep]; exact h2)]
      exact hrep
    rw [hsi] at hchain
    rcases hchain with hc1 | ⟨hc2a, hc2b⟩
    next => exact hwf.acyc c hc1
    next =>
      exact hguard (Relation.TransGen.trans hc2b hc2a)
  next =>
    -- `c = src`, `i = dst`: after both substs, `σ i = i` and the
    -- guard is `¬ RSub h c i` — it kills both disjuncts.
    subst h4
    subst h3
    have hrd : h.repr i = i := Heap.repr_of_isRep hdst
    have hsd : (if h.repr i = c then i else h.repr i) = i := by
      rw [if_neg (by rw [hrd]; exact Ne.symm hne)]
      exact hrd
    rw [hsd] at hchain
    rcases hchain with hc1 | ⟨-, hc2b⟩
    next => exact hguard hc1
    next => exact hguard hc2b

/-- `HeapWf` under redirect: the node table is untouched, the forward
    table keeps resolving (`FwOk_redirect`), and acyclicity holds under
    the splice guard `¬ RSub h src dst`. -/
theorem HeapWf_redirect {h : Heap} (hwf : HeapWf h) {src dst : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hguard : ¬ RSub h src dst) :
    HeapWf (h.redirect src dst) where
  dagwf := hwf.dagwf
  fwlen := redirect_fwlen hwf src dst
  fwok := FwOk_redirect hwf.fwok hsrc hdst hne
    (List.getElem?_eq_some_iff.1 hdst).1
  acyc := Acyc_redirect hwf hsrc hdst hne hguard

end ISAR
