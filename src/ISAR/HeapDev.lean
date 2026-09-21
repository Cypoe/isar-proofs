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

/-- `repr` is idempotent (a rep resolves to itself). -/
theorem Heap.repr_idem {h : Heap} (hfw : FwOk h.fw) {i : Nat}
    (hi : i < h.fw.length) : h.repr (h.repr i) = h.repr i := by
  obtain ⟨r, -, hrep, hres⟩ := hfw i hi
  have hri : h.repr i = r := by unfold Heap.repr; rw [hres]; rfl
  rw [hri]
  exact Heap.repr_of_isRep hrep

/-- Readback is a function of the representative, not the index. -/
theorem heapUnfold_repr {h : Heap} (hwf : HeapWf h) {i : Nat}
    (hi : i < h.len) :
    heapUnfold h hwf i = heapUnfold h hwf (h.repr i) := by
  have hri : h.repr (h.repr i) = h.repr i :=
    Heap.repr_idem hwf.fwok (by rw [hwf.fwlen]; exact hi)
  conv_rhs => rw [heapUnfold]
  rw [hri]
  conv_lhs => rw [heapUnfold]

/-- `t'` is `t` with some occurrences of `s` replaced by `T` — the
    readback effect of `src ↦ dst` (a `repr`-level splice). -/
inductive Splice (s T : ITerm) : ITerm → ITerm → Prop where
  | refl {t : ITerm} : Splice s T t t
  | here : Splice s T s T
  | app {a b a' b' : ITerm} :
      Splice s T a a' → Splice s T b b' → Splice s T (.app a b) (.app a' b')

/-- Splicing is substitutive under reduction: if `s →* T` then the
    spliced term is reachable. -/
theorem Splice_red {s T a b : ITerm}
    (hsp : Splice s T a b) (hred : IRedBasis s T) : IRedBasis a b := by
  induction hsp with
  | refl => exact Relation.ReflTransGen.refl
  | here => exact hred
  | app ha hb iha ihb => exact IRedBasis_app iha ihb

/-- Observational equivalence of terms: both reduce to a common
    reduct.  This is the equivalence heap-level sharing must preserve —
    `GraphDev` proved syntactic `cdBasis`-equality; here redirects can
    interleave developments, so readbacks only agree up to `Join`. -/
def Join (a b : ITerm) : Prop := ∃ u, IRedBasis a u ∧ IRedBasis b u

theorem Join.refl (t : ITerm) : Join t t := ⟨t, .refl, .refl⟩

theorem Join.symm {a b : ITerm} (h : Join a b) : Join b a :=
  let ⟨u, ha, hb⟩ := h; ⟨u, hb, ha⟩

theorem Join.trans {a b c : ITerm} (h₁ : Join a b) (h₂ : Join b c) :
    Join a c := by
  obtain ⟨u, hau, hbu⟩ := h₁
  obtain ⟨v, hbv, hcv⟩ := h₂
  obtain ⟨w, huw, hvw⟩ := IRedBasis_confluence hbu hbv
  exact ⟨w, hau.trans huw, hcv.trans hvw⟩

theorem Join_app {a a' b b' : ITerm} (ha : Join a a') (hb : Join b b') :
    Join (.app a b) (.app a' b') := by
  obtain ⟨u, hau, hbu⟩ := ha
  obtain ⟨v, hav, hbv⟩ := hb
  exact ⟨.app u v, IRedBasis_app hau hav, IRedBasis_app hbu hbv⟩

theorem Join_of_ired {a b : ITerm} (h : IRedBasis a b) : Join a b :=
  ⟨b, h, .refl⟩

theorem Join.ired_l {a b c : ITerm} (h : IRedBasis a b)
    (hbc : Join b c) : Join a c := by
  obtain ⟨u, hbu, hcu⟩ := hbc
  exact ⟨u, h.trans hbu, hcu⟩

theorem Join.ired_r {a b c : ITerm} (h : IRedBasis b c)
    (hab : Join a b) : Join a c := by
  obtain ⟨u, hau, hbu⟩ := hab
  obtain ⟨w, hcw, huw⟩ := IRedBasis_confluence h hbu
  exact ⟨w, hau.trans huw, hcw⟩

/-- `cd` lands below `t`; a term joins its own development. -/
theorem Join_cd_self (t : ITerm) : Join (cdBasis t) t :=
  (Join_of_ired (cdBasis_ired t)).symm

/-- Reduction commutes with `cdBasis` up to joining. -/
theorem cdJoin {a b : ITerm} (h : IRedBasis a b) :
    Join (cdBasis a) (cdBasis b) := by
  obtain ⟨u, h₁, h₂⟩ := IRedBasis_confluence (cdBasis_ired a)
    (h.trans (cdBasis_ired b))
  exact ⟨u, h₁, h₂⟩

/-- Joining commutes with `cdBasis`. -/
theorem cdJoin_of_join {a b : ITerm} (h : Join a b) :
    Join (cdBasis a) (cdBasis b) := by
  obtain ⟨u, hau, hbu⟩ := h
  exact Join.trans (cdJoin hau) (cdJoin hbu).symm

/-- A development result joins the input: `Join a (cd b)` collapses to
    `Join b a` since `b →* cd b`. -/
theorem Join_cd_left {a b : ITerm} (h : Join a (cdBasis b)) :
    Join b a :=
  (h.trans (Join_cd_self b)).symm

/-- Splicing `Join`-equivalent endpoints keeps the terms `Join`
    equivalent — redirects preserve readback observational class. -/
theorem Splice_join {s T a b : ITerm} (hsp : Splice s T a b)
    (hst : Join s T) : Join a b := by
  induction hsp with
  | refl => exact Join.refl _
  | here => exact hst
  | app _ _ iha ihb => exact Join_app iha ihb

/-- `cd` fixes atoms. -/
theorem cdBasis_atom (a : GAtom) : cdBasis a.toTerm = a.toTerm := by
  cases a <;> rfl

/-- `cd` fixes variables. -/
theorem cdBasis_var (n : Nat) : cdBasis (.var n) = .var n := rfl

/-- Out-of-range indices resolve to themselves. -/
theorem Heap.repr_oob {h : Heap} {i : Nat} (hi : h.fw.length ≤ i) :
    h.repr i = i := by
  unfold Heap.repr
  rw [resolveS_oob (by simp) hi]
  rfl

/-- `repr'` and `repr` commute: `repr' (repr x) = repr' x`.  The σ-map
    is idempotent because `repr` is. -/
theorem Heap.repr_redirect_repr {h : Heap} (hfw : FwOk h.fw) {src dst x : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hx : x < h.fw.length) :
    (h.redirect src dst).repr (h.repr x) = (h.redirect src dst).repr x := by
  have hrlt : h.repr x < h.fw.length := (h.repr_spec hfw hx).1
  rw [Heap.repr_redirect hfw hsrc hdst hne hrlt,
      Heap.repr_redirect hfw hsrc hdst hne hx,
      Heap.repr_idem hfw hx]

/-- The readback substitution lemma: after `src ↦ dst`, every index's
    unfold is the old unfold with each `unfold src`-subtree replaced by
    `unfold' dst`.  This is the sharing step — nodes that resolved to
    `src` now read the redirect target. -/
theorem heapUnfold_redirect {h : Heap} (hwf : HeapWf h) {src dst : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hguard : ¬ RSub h src dst) :
    ∀ i, Splice
      (heapUnfold h hwf src)
      (heapUnfold (h.redirect src dst)
        (HeapWf_redirect hwf hsrc hdst hne hguard) dst)
      (heapUnfold h hwf i)
      (heapUnfold (h.redirect src dst)
        (HeapWf_redirect hwf hsrc hdst hne hguard) i) := by
  intro i
  generalize hcard : (RSubSet h i).card = m
  induction m using Nat.strong_induction_on generalizing i with
  | h m ih =>
      rcases lt_or_ge i h.fw.length with hlt | hge
      next =>
        rcases Nat.decEq (h.repr i) src with hrne | hreq
        next =>
          -- `repr i ≠ src`: the node is read as before; children are
          -- spliced by the induction hypothesis.
          have hri' : (h.redirect src dst).repr i = h.repr i := by
            rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hlt, if_neg hrne]
          have hb : h.repr i < h.ns.length := by
            rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hlt).1
          rcases hnode : h.ns[h.repr i]? with _ | g
          next => -- impossible: `repr i < ns.length`
            exfalso
            rw [List.getElem?_eq_none_iff] at hnode; omega
          next =>
            cases g with
            | atom a =>
              have hnc : (h.redirect src dst).ns[h.repr i]? =
                  some (GNode.atom a) := hnode
              have e1 : heapUnfold h hwf i = a.toTerm := by
                conv_lhs => rw [heapUnfold]; rw [hnode]
              have e2 : heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard) i =
                  a.toTerm := by
                conv_lhs => rw [heapUnfold]; rw [hri', hnc]
              rw [e1, e2]; exact Splice.refl
            | var n =>
              have hnc : (h.redirect src dst).ns[h.repr i]? =
                  some (GNode.var n) := hnode
              have e1 : heapUnfold h hwf i = .var n := by
                conv_lhs => rw [heapUnfold]; rw [hnode]
              have e2 : heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard) i =
                  .var n := by
                conv_lhs => rw [heapUnfold]; rw [hri', hnc]
              rw [e1, e2]; exact Splice.refl
            | app l r =>
              obtain ⟨hplt, hget⟩ := List.getElem?_eq_some_iff.1 hnode
              obtain ⟨hllt, hrlt⟩ := hwf.dagwf (h.repr i) hplt l r hget
              have hll : l < h.fw.length := by
                rw [hwf.fwlen]; exact lt_trans hllt hb
              have hrr : r < h.fw.length := by
                rw [hwf.fwlen]; exact lt_trans hrlt hb
              have hnc : (h.redirect src dst).ns[h.repr i]? =
                  some (GNode.app l r) := hnode
              have e1 : heapUnfold h hwf i =
                  .app (heapUnfold h hwf (h.repr l))
                       (heapUnfold h hwf (h.repr r)) := by
                conv_lhs => rw [heapUnfold]
                rw [hnode]
              have e2 : heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard) i =
                  .app (heapUnfold (h.redirect src dst)
                          (HeapWf_redirect hwf hsrc hdst hne hguard)
                          ((h.redirect src dst).repr l))
                       (heapUnfold (h.redirect src dst)
                          (HeapWf_redirect hwf hsrc hdst hne hguard)
                          ((h.redirect src dst).repr r)) := by
                conv_lhs => rw [heapUnfold]
                rw [hri', hnc]
              have hcl : RChild h (h.repr l) i := ⟨l, r, hnode, Or.inl rfl⟩
              have hcr : RChild h (h.repr r) i := ⟨l, r, hnode, Or.inr rfl⟩
              have ihl := ih (RSubSet h (h.repr l)).card
                (by rw [← hcard]; exact RSubSet_lt hwf hcl) (h.repr l) rfl
              have ihr := ih (RSubSet h (h.repr r)).card
                (by rw [← hcard]; exact RSubSet_lt hwf hcr) (h.repr r) rfl
              have hrll : h.repr l < (h.redirect src dst).len := by
                rw [Heap.len_eq]; show h.repr l < h.ns.length
                rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hll).1
              have hrlr : h.repr r < (h.redirect src dst).len := by
                rw [Heap.len_eq]; show h.repr r < h.ns.length
                rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hrr).1
              have eql : heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard)
                    ((h.redirect src dst).repr l) =
                  heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard) (h.repr l) := by
                have hc : (h.redirect src dst).repr (h.repr l) =
                    (h.redirect src dst).repr l :=
                  Heap.repr_redirect_repr hwf.fwok hsrc hdst hne hll
                rw [← hc]
                exact (heapUnfold_repr
                  (HeapWf_redirect hwf hsrc hdst hne hguard) hrll).symm
              have eqr : heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard)
                    ((h.redirect src dst).repr r) =
                  heapUnfold (h.redirect src dst)
                    (HeapWf_redirect hwf hsrc hdst hne hguard) (h.repr r) := by
                have hc : (h.redirect src dst).repr (h.repr r) =
                    (h.redirect src dst).repr r :=
                  Heap.repr_redirect_repr hwf.fwok hsrc hdst hne hrr
                rw [← hc]
                exact (heapUnfold_repr
                  (HeapWf_redirect hwf hsrc hdst hne hguard) hrlr).symm
              rw [e1, e2, eql, eqr]
              exact Splice.app ihl ihr
        next =>
          -- `repr i = src`: the whole subtree becomes `unfold' dst`.
          have hri' : (h.redirect src dst).repr i = dst := by
            rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hlt, if_pos hreq]
          have hi' : i < (h.redirect src dst).len := by
            rw [Heap.len_eq]; show i < h.ns.length
            rw [← hwf.fwlen]; exact hlt
          have e1 : heapUnfold h hwf i = heapUnfold h hwf src := by
            rw [heapUnfold_repr hwf
                  (by rw [Heap.len_eq, ← hwf.fwlen]; exact hlt), hreq]
          have e2 : heapUnfold (h.redirect src dst)
                (HeapWf_redirect hwf hsrc hdst hne hguard) i =
              heapUnfold (h.redirect src dst)
                (HeapWf_redirect hwf hsrc hdst hne hguard) dst := by
            rw [heapUnfold_repr (HeapWf_redirect hwf hsrc hdst hne hguard)
                  hi', hri']
          rw [e1, e2]; exact Splice.here
      next => -- `i` out of range: both sides read nothing.
        have hri : h.repr i = i := Heap.repr_oob hge
        have hri' : (h.redirect src dst).repr i = i := by
          apply Heap.repr_oob
          show (h.fw.set src (some dst)).length ≤ i
          rw [List.length_set]; exact hge
        have hnone : h.ns[i]? = none := by
          rw [List.getElem?_eq_none_iff, ← hwf.fwlen]; exact hge
        have hnone' : (h.redirect src dst).ns[i]? = none := hnone
        have e1 : heapUnfold h hwf i = .var 0 := by
          conv_lhs => rw [heapUnfold]; rw [hri, hnone]
        have e2 : heapUnfold (h.redirect src dst)
              (HeapWf_redirect hwf hsrc hdst hne hguard) i = .var 0 := by
          conv_lhs => rw [heapUnfold]; rw [hri', hnone']
        rw [e1, e2]; exact Splice.refl

/-- `mk_app`: allocate a fresh `app l r` node or return an interned
    representative — the host's hash-consing.  The interned case only
    promises a `Join`: the table hit may be a node whose readback
    merely agrees with `app (unfold l) (unfold r)` observationally
    (its raw children can themselves be redirect sources). -/
def MkApp (h : Heap) (l r : Nat) (h' : Heap) (o : Nat) : Prop :=
  (h' = h.push (GNode.app l r) ∧ o = h.len ∧ l < h.len ∧ r < h.len) ∨
  (h' = h ∧ o < h.len ∧ h.fw[o]? = some none ∧
    ∀ hwf : HeapWf h,
      Join (heapUnfold h hwf o)
        (.app (heapUnfold h hwf l) (heapUnfold h hwf r)))

/-- Resolved-node redex check: children are read through `repr`,
    matching the host's `kind[self.repr(child)]` in `_fun_arg`. -/
def isRedexNodeR (h : Heap) (i : Nat) : Bool :=
  match h.ns[i]? with
  | some (.app l _) =>
      match h.ns[h.repr l]? with
      | some (.atom .norm) => true
      | some (.app kl _) =>
          match h.ns[h.repr kl]? with
          | some (.atom .konst) | some (.atom .dup) => true
          | some (.app kll _) =>
              match h.ns[h.repr kll]? with
              | some (.atom .comp) | some (.atom .swap) => true
              | _ => false
          | _ => false
      | _ => false
  | _ => false

/-- Preconditions for `redirect s d` to preserve `HeapWf`: source is
    still a rep, target is a rep, they differ, and splicing `s` into
    `d`'s subtree-position creates no cycle. -/
def RedirectOk (h : Heap) (s d : Nat) : Prop :=
  h.fw[s]? = some none ∧ h.fw[d]? = some none ∧ s ≠ d ∧ ¬ RSub h s d

/-- Heap-level complete development: `HDev D h i h' o D'` — developing
    node `i` in heap `h` under memo `D` (reps already developed this
    round — the seal makes results memoized too) yields heap `h'`,
    output index `o`, and extended memo `D'`.  One constructor per
    `Graph.cd` clause; `hit` is the memo path. -/
inductive HDev : Finset Nat → Heap → Nat → Heap → Nat → Finset Nat → Prop where
  | hit {D : Finset Nat} {h : Heap} {i : Nat} :
      h.repr i ∈ D → HDev D h i h (h.repr i) D
  | atom {D : Finset Nat} {h : Heap} {i : Nat} {a : GAtom} :
      h.ns[h.repr i]? = some (GNode.atom a) → h.repr i ∉ D →
      HDev D h i h (h.repr i) (insert (h.repr i) D)
  | var {D : Finset Nat} {h : Heap} {i n : Nat} :
      h.ns[h.repr i]? = some (GNode.var n) → h.repr i ∉ D →
      HDev D h i h (h.repr i) (insert (h.repr i) D)
  | norm_red {D : Finset Nat} {h h₁ : Heap} {i l r j : Nat}
      {D₁ : Finset Nat} :
      h.ns[h.repr i]? = some (GNode.app l r) →
      h.ns[h.repr l]? = some (GNode.atom GAtom.norm) →
      h.repr i ∉ D →
      HDev D h r h₁ j D₁ →
      RedirectOk h₁ (h.repr i) j →
      HDev D h i (h₁.redirect (h.repr i) j) j (insert j D₁)
  | konst_red {D : Finset Nat} {h h₁ : Heap} {i l r kl kr j : Nat}
      {D₁ : Finset Nat} :
      h.ns[h.repr i]? = some (GNode.app l r) →
      h.ns[h.repr l]? = some (GNode.app kl kr) →
      h.ns[h.repr kl]? = some (GNode.atom GAtom.konst) →
      h.repr i ∉ D →
      HDev D h kr h₁ j D₁ →
      RedirectOk h₁ (h.repr i) j →
      HDev D h i (h₁.redirect (h.repr i) j) j (insert j D₁)
  | dup_red {D : Finset Nat} {h h₁ h₂ h₃ h₄ : Heap}
      {i l r kl kr jx jf a b : Nat}
      {D₁ D₂ : Finset Nat} :
      h.ns[h.repr i]? = some (GNode.app l r) →
      h.ns[h.repr l]? = some (GNode.app kl kr) →
      h.ns[h.repr kl]? = some (GNode.atom GAtom.dup) →
      h.repr i ∉ D →
      HDev D h r h₁ jx D₁ →
      HDev D₁ h₁ kr h₂ jf D₂ →
      MkApp h₂ jf jx h₃ a → MkApp h₃ a jx h₄ b →
      RedirectOk h₄ (h.repr i) b →
      HDev D h i (h₄.redirect (h.repr i) b) b (insert b D₂)
  | comp_red {D : Finset Nat} {h h₁ h₂ h₃ h₄ h₅ : Heap}
      {i l r kl kr kll klr jf jg jx a b : Nat}
      {D₁ D₂ D₃ : Finset Nat} :
      h.ns[h.repr i]? = some (GNode.app l r) →
      h.ns[h.repr l]? = some (GNode.app kl kr) →
      h.ns[h.repr kl]? = some (GNode.app kll klr) →
      h.ns[h.repr kll]? = some (GNode.atom GAtom.comp) →
      h.repr i ∉ D →
      HDev D h klr h₁ jf D₁ →
      HDev D₁ h₁ kr h₂ jg D₂ →
      HDev D₂ h₂ r h₃ jx D₃ →
      MkApp h₃ jg jx h₄ a → MkApp h₄ jf a h₅ b →
      RedirectOk h₅ (h.repr i) b →
      HDev D h i (h₅.redirect (h.repr i) b) b (insert b D₃)
  | swap_red {D : Finset Nat} {h h₁ h₂ h₃ h₄ h₅ : Heap}
      {i l r kl kr kll klr jf jx jy a b : Nat}
      {D₁ D₂ D₃ : Finset Nat} :
      h.ns[h.repr i]? = some (GNode.app l r) →
      h.ns[h.repr l]? = some (GNode.app kl kr) →
      h.ns[h.repr kl]? = some (GNode.app kll klr) →
      h.ns[h.repr kll]? = some (GNode.atom GAtom.swap) →
      h.repr i ∉ D →
      HDev D h klr h₁ jf D₁ →
      HDev D₁ h₁ kr h₂ jx D₂ →
      HDev D₂ h₂ r h₃ jy D₃ →
      MkApp h₃ jf jy h₄ a → MkApp h₄ a jx h₅ b →
      RedirectOk h₅ (h.repr i) b →
      HDev D h i (h₅.redirect (h.repr i) b) b (insert b D₃)
  | app_dev {D : Finset Nat} {h h₁ h₂ h₃ : Heap} {i l r jf jx o : Nat}
      {D₁ D₂ : Finset Nat} :
      h.ns[h.repr i]? = some (GNode.app l r) →
      (∀ W : HeapWf h,
        isRedexHead (heapUnfold h W (h.repr l)) = false) →
      h.repr i ∉ D →
      HDev D h l h₁ jf D₁ →
      HDev D₁ h₁ r h₂ jx D₂ →
      MkApp h₂ jf jx h₃ o →
      RedirectOk h₃ (h.repr i) o →
      HDev D h i (h₃.redirect (h.repr i) o) o (insert o D₂)

/-- `t` occurs in `u` (reflexive). -/
inductive Occ (t : ITerm) : ITerm → Prop where
  | here : Occ t t
  | left {a b : ITerm} : Occ t a → Occ t (.app a b)
  | right {a b : ITerm} : Occ t b → Occ t (.app a b)

theorem Occ_trans {t u v : ITerm} (h₁ : Occ t u) (h₂ : Occ u v) :
    Occ t v := by
  induction h₂ with
  | here => exact h₁
  | left _ ih => exact Occ.left ih
  | right _ ih => exact Occ.right ih

/-- Term size, for the occurrence/strict-subterm argument. -/
def tsize : ITerm → Nat
  | .app f x => tsize f + tsize x + 1
  | _ => 1

theorem Occ_size {t u : ITerm} (h : Occ t u) : tsize t ≤ tsize u := by
  induction h with
  | here => exact Nat.le_refl _
  | left _ ih =>
    show tsize t ≤ tsize _ + tsize _ + 1; omega
  | right _ ih =>
    show tsize t ≤ tsize _ + tsize _ + 1; omega

/-- `t` occurs strictly inside `u`. -/
def SOcc (t u : ITerm) : Prop :=
  ∃ a b, u = .app a b ∧ (Occ t a ∨ Occ t b)

theorem Occ_of_SOcc {a b : ITerm} (h : SOcc a b) : Occ a b := by
  obtain ⟨x, y, hxy, hmem⟩ := h
  subst hxy
  exact hmem.elim Occ.left Occ.right

theorem SOcc_trans {a b c : ITerm} (h₁ : SOcc a b) (h₂ : SOcc b c) :
    SOcc a c := by
  obtain ⟨x, y, hxy, hmem⟩ := h₂
  subst hxy
  have hab : Occ a b := Occ_of_SOcc h₁
  exact ⟨x, y, rfl, hmem.elim
    (fun hb => Or.inl (Occ_trans hab hb))
    (fun hb => Or.inr (Occ_trans hab hb))⟩

theorem SOcc_size {t u : ITerm} (h : SOcc t u) :
    tsize t < tsize u := by
  obtain ⟨a, b, hu, hmem⟩ := h
  subst hu
  show tsize t < tsize a + tsize b + 1
  rcases hmem with hmem | hmem <;>
    have hle := Occ_size hmem <;> omega

theorem SOcc_irrefl {t : ITerm} : ¬ SOcc t t := by
  intro h
  exact absurd (SOcc_size h) (Nat.lt_irrefl _)

/-- A resolved child reads back as a strict subterm. -/
theorem heapUnfold_child_occ {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j i) :
    SOcc (heapUnfold h hwf j) (heapUnfold h hwf i) := by
  obtain ⟨l, r, hnode, hjl⟩ := hc
  have e : heapUnfold h hwf i =
      .app (heapUnfold h hwf (h.repr l))
           (heapUnfold h hwf (h.repr r)) := by
    conv_lhs => rw [heapUnfold]
    rw [hnode]
  rw [e]
  rcases hjl with hjl | hjl
  next =>
    refine ⟨_, _, rfl, Or.inl ?_⟩
    rw [← hjl]; exact Occ.here
  next =>
    refine ⟨_, _, rfl, Or.inr ?_⟩
    rw [← hjl]; exact Occ.here

/-- Resolved descendants read back as strict subterms. -/
theorem heapUnfold_occ {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hsub : RSub h j i) :
    SOcc (heapUnfold h hwf j) (heapUnfold h hwf i) := by
  induction hsub with
  | single hc => exact heapUnfold_child_occ hwf hc
  | tail _ hstep ih =>
    exact SOcc_trans ih (heapUnfold_child_occ hwf hstep)

/-- Below `dst`, the redirect is invisible to readback: any node in
    `dst`'s post-redirect subtree either is `dst` or reads back
    identically to before.  Positions resolving to `src` would force
    `unfold' dst` to be a strict subterm of itself. -/
theorem heapUnfold_redirect_below {h : Heap} (hwf : HeapWf h)
    {src dst : Nat}
    (hsrc : h.fw[src]? = some none) (hdst : h.fw[dst]? = some none)
    (hne : src ≠ dst) (hguard : ¬ RSub h src dst) :
    ∀ i, i = dst ∨ RSub (h.redirect src dst) i dst →
      heapUnfold (h.redirect src dst)
        (HeapWf_redirect hwf hsrc hdst hne hguard) i =
      heapUnfold h hwf i := by
  intro i
  generalize hcard : (RSubSet (h.redirect src dst) i).card = m
  induction m using Nat.strong_induction_on generalizing i with
  | h m ih =>
    intro hbel
    set hwf' := HeapWf_redirect hwf hsrc hdst hne hguard with hwf'e
    have hlen : (h.redirect src dst).len = h.len := rfl
    have hi : i < h.len := by
      rcases hbel with hii | hsub
      next =>
        rw [hii, Heap.len_eq, ← hwf.fwlen]
        exact (List.getElem?_eq_some_iff.1 hdst).1
      next =>
        induction hsub using Relation.TransGen.head_induction_on with
        | single hstep =>
          have hlt := RChild_lt hwf' hstep
          rw [hlen] at hlt; exact hlt
        | head hstep _hsub _ih =>
          have hlt := RChild_lt hwf' hstep
          rw [hlen] at hlt; exact hlt
    have hlt : i < h.fw.length := by rw [hwf.fwlen]; exact hi
    rcases Nat.decEq (h.repr i) src with hrne | hreq
    next =>
      -- `repr i ≠ src`: the node is read as before; children by ih.
      have hri' : (h.redirect src dst).repr i = h.repr i := by
        rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hlt, if_neg hrne]
      have hb : h.repr i < h.ns.length := by
        rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hlt).1
      rcases hnode : h.ns[h.repr i]? with _ | g
      next =>
        exfalso
        rw [List.getElem?_eq_none_iff] at hnode; omega
      next =>
        cases g with
        | atom a =>
          have hnc : (h.redirect src dst).ns[h.repr i]? =
              some (GNode.atom a) := hnode
          have e1 : heapUnfold h hwf i = a.toTerm := by
            conv_lhs => rw [heapUnfold]; rw [hnode]
          have e2 : heapUnfold (h.redirect src dst) hwf' i =
              a.toTerm := by
            conv_lhs => rw [heapUnfold]; rw [hri', hnc]
          rw [e1, e2]
        | var n =>
          have hnc : (h.redirect src dst).ns[h.repr i]? =
              some (GNode.var n) := hnode
          have e1 : heapUnfold h hwf i = .var n := by
            conv_lhs => rw [heapUnfold]; rw [hnode]
          have e2 : heapUnfold (h.redirect src dst) hwf' i =
              .var n := by
            conv_lhs => rw [heapUnfold]; rw [hri', hnc]
          rw [e1, e2]
        | app l r =>
          obtain ⟨hplt, hget⟩ := List.getElem?_eq_some_iff.1 hnode
          obtain ⟨hllt, hrlt⟩ := hwf.dagwf (h.repr i) hplt l r hget
          have hll : l < h.fw.length := by
            rw [hwf.fwlen]; exact lt_trans hllt hb
          have hrr : r < h.fw.length := by
            rw [hwf.fwlen]; exact lt_trans hrlt hb
          have hnc : (h.redirect src dst).ns[h.repr i]? =
              some (GNode.app l r) := hnode
          have hnc' : (h.redirect src dst).ns[(h.redirect src dst).repr i]? =
              some (GNode.app l r) := by
            rw [hri']; exact hnc
          have e1 : heapUnfold h hwf i =
              .app (heapUnfold h hwf (h.repr l))
                   (heapUnfold h hwf (h.repr r)) := by
            conv_lhs => rw [heapUnfold]
            rw [hnode]
          have e2 : heapUnfold (h.redirect src dst) hwf' i =
              .app (heapUnfold (h.redirect src dst) hwf'
                     ((h.redirect src dst).repr l))
                   (heapUnfold (h.redirect src dst) hwf'
                     ((h.redirect src dst).repr r)) := by
            conv_lhs => rw [heapUnfold]
            rw [hri', hnc]
          -- each child: `repr' c = dst` is either a cycle (dead) or the
          -- `repr c = dst` case; otherwise `repr' c = repr c` and ih.
          have child : ∀ c : Nat, c < h.fw.length →
              RChild (h.redirect src dst)
                ((h.redirect src dst).repr c) i →
              heapUnfold (h.redirect src dst) hwf'
                ((h.redirect src dst).repr c) =
              heapUnfold h hwf (h.repr c) := by
            intro c hcw hcc
            have hcre : (h.redirect src dst).repr c =
                if h.repr c = src then dst else h.repr c :=
              Heap.repr_redirect hwf.fwok hsrc hdst hne hcw
            have hsubc : RSub (h.redirect src dst)
                ((h.redirect src dst).repr c) i :=
              Relation.TransGen.single hcc
            have hbelc : (h.redirect src dst).repr c = dst ∨
                RSub (h.redirect src dst)
                  ((h.redirect src dst).repr c) dst := by
              rcases hbel with hii | hsi
              next =>
                rw [hii] at hsubc
                exact Or.inr hsubc
              next =>
                exact Or.inr (Relation.TransGen.trans hsubc hsi)
            have hdec : (RSubSet (h.redirect src dst)
                ((h.redirect src dst).repr c)).card < m := by
              rw [← hcard]; exact RSubSet_lt hwf' hcc
            rcases Nat.decEq ((h.redirect src dst).repr c) dst
              with hcd | hcd
            next =>
              -- `repr' c ≠ dst`: `repr c` can't be `src`, so `repr' c =
              -- repr c` and the ih applies.
              have hcs : h.repr c ≠ src := by
                intro hcs
                rw [hcre, if_pos hcs] at hcd
                exact hcd rfl
              have hcre' : (h.redirect src dst).repr c = h.repr c := by
                rw [hcre, if_neg hcs]
              have eih := ih _ hdec ((h.redirect src dst).repr c)
                rfl hbelc
              rw [hcre'] at eih ⊢
              exact eih
            next =>
              -- `repr' c = dst`: `repr c = src` would cycle back into
              -- `dst`'s subtree; `repr c = dst` closes via ih at `dst`.
              rcases Nat.decEq (h.repr c) src with hcs | hcs
              next =>
                have hcd' : h.repr c = dst := by
                  have h0 := hcd
                  rw [hcre, if_neg hcs] at h0
                  exact h0
                have hcc' : RChild (h.redirect src dst) dst i := by
                  obtain ⟨l', r', hn', hm'⟩ := hcc
                  exact ⟨l', r', hn', hm'.elim
                    (fun e => Or.inl (e.trans hcd))
                    (fun e => Or.inr (e.trans hcd))⟩
                have hdec' : (RSubSet (h.redirect src dst) dst).card
                    < m := by
                  rw [← hcard]; exact RSubSet_lt hwf' hcc'
                have eih := ih _ hdec' dst rfl (Or.inl rfl)
                rw [hcd, hcd']
                exact eih
              next =>
                exfalso
                have hcc' : RChild (h.redirect src dst) dst i := by
                  obtain ⟨l', r', hn', hm'⟩ := hcc
                  exact ⟨l', r', hn', hm'.elim
                    (fun e => Or.inl (e.trans hcd))
                    (fun e => Or.inr (e.trans hcd))⟩
                have hdsub : RSub (h.redirect src dst) dst dst := by
                  rcases hbel with hii | hsi
                  next =>
                    have hs := Relation.TransGen.single hcc'
                    rw [hii] at hs
                    exact hs
                  next =>
                    exact Relation.TransGen.trans
                      (Relation.TransGen.single hcc') hsi
                exact hwf'.acyc dst hdsub
          have ecl := child l hll ⟨l, r, hnc', Or.inl rfl⟩
          have ecr := child r hrr ⟨l, r, hnc', Or.inr rfl⟩
          rw [e1, e2, ecl, ecr]
    next =>
      -- `repr i = src`: below `dst` this is impossible — it would make
      -- `unfold' dst` a strict subterm of itself.
      exfalso
      have hri' : (h.redirect src dst).repr i = dst := by
        rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hlt, if_pos hreq]
      rcases hbel with hii | hsi
      next =>
        rw [hii] at hreq
        have hrd : h.repr dst = dst := by
          show (resolveS h.fw ∅ dst).getD dst = dst
          rw [resolveS_rep (by simp) hdst]
          rfl
        rw [hrd] at hreq
        exact hne hreq.symm
      next =>
        have hi' : i < (h.redirect src dst).len := by
          rw [hlen]; exact hi
        have e : heapUnfold (h.redirect src dst) hwf' i =
            heapUnfold (h.redirect src dst) hwf' dst := by
          rw [heapUnfold_repr hwf' hi', hri']
        have hocc := heapUnfold_occ hwf' hsi
        rw [e] at hocc
        exact SOcc_irrefl hocc

/-- Allocation does not change old readbacks. -/
theorem heapUnfold_push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len)
    (hwf' : HeapWf (h.push n)) :
    ∀ i, i < h.len →
      heapUnfold (h.push n) hwf' i = heapUnfold h hwf i := by
  intro i
  generalize hcard : (RSubSet h i).card = m
  induction m using Nat.strong_induction_on generalizing i with
  | h m ih =>
    intro hi
    have hif : i < h.fw.length := by rw [hwf.fwlen]; exact hi
    have hri : (h.push n).repr i = h.repr i :=
      Heap.repr_push hwf.fwok n hif
    have hrb : h.repr i < h.ns.length := by
      rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hif).1
    rcases hnode : h.ns[h.repr i]? with _ | g
    next =>
      exfalso
      rw [List.getElem?_eq_none_iff] at hnode; omega
    next =>
      have hnode' : (h.push n).ns[h.repr i]? = some g := by
        show (h.ns ++ [n])[h.repr i]? = some g
        rw [List.getElem?_append_left hrb]; exact hnode
      cases g with
      | atom a =>
        have e1 : heapUnfold h hwf i = a.toTerm := by
          conv_lhs => rw [heapUnfold]; rw [hnode]
        have e2 : heapUnfold (h.push n) hwf' i = a.toTerm := by
          conv_lhs => rw [heapUnfold]; rw [hri, hnode']
        rw [e1, e2]
      | var k =>
        have e1 : heapUnfold h hwf i = .var k := by
          conv_lhs => rw [heapUnfold]; rw [hnode]
        have e2 : heapUnfold (h.push n) hwf' i = .var k := by
          conv_lhs => rw [heapUnfold]; rw [hri, hnode']
        rw [e1, e2]
      | app l r =>
        obtain ⟨hplt, hget⟩ := List.getElem?_eq_some_iff.1 hnode
        obtain ⟨hllt, hrlt⟩ := hwf.dagwf (h.repr i) hplt l r hget
        have hll : l < h.fw.length := by rw [hwf.fwlen]; omega
        have hrr : r < h.fw.length := by rw [hwf.fwlen]; omega
        have hrl : (h.push n).repr l = h.repr l :=
          Heap.repr_push hwf.fwok n hll
        have hrrp : (h.push n).repr r = h.repr r :=
          Heap.repr_push hwf.fwok n hrr
        have e1 : heapUnfold h hwf i =
            .app (heapUnfold h hwf (h.repr l))
                 (heapUnfold h hwf (h.repr r)) := by
          conv_lhs => rw [heapUnfold]; rw [hnode]
        have e2 : heapUnfold (h.push n) hwf' i =
            .app (heapUnfold (h.push n) hwf' ((h.push n).repr l))
                 (heapUnfold (h.push n) hwf' ((h.push n).repr r)) := by
          conv_lhs => rw [heapUnfold]
          rw [hri]; rw [show (h.push n).ns[h.repr i]? = _ from hnode']
        rw [e1, e2, hrl, hrrp]
        have hcl : RChild h (h.repr l) i := ⟨l, r, hnode, Or.inl rfl⟩
        have hcr : RChild h (h.repr r) i := ⟨l, r, hnode, Or.inr rfl⟩
        have hlb : h.repr l < h.len := by
          rw [Heap.len_eq]; show h.repr l < h.ns.length
          rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hll).1
        have hrb2 : h.repr r < h.len := by
          rw [Heap.len_eq]; show h.repr r < h.ns.length
          rw [← hwf.fwlen]; exact (h.repr_spec hwf.fwok hrr).1
        have ihl := ih _ (by rw [← hcard]; exact RSubSet_lt hwf hcl)
          (h.repr l) rfl hlb
        have ihr := ih _ (by rw [← hcard]; exact RSubSet_lt hwf hcr)
          (h.repr r) rfl hrb2
        rw [ihl, ihr]

/-- Heap evolution: `h'` grew from `h` (indices stable, table extended)
    and every old readback joins the new one — redirects splice
    developed results into old positions. -/
def HLe {h h' : Heap} (hwf : HeapWf h) (hwf' : HeapWf h') : Prop :=
  h.len ≤ h'.len ∧
    ∀ j, j < h.len → Join (heapUnfold h hwf j) (heapUnfold h' hwf' j)

theorem HLe.refl {h : Heap} (hwf : HeapWf h) : HLe hwf hwf :=
  ⟨Nat.le_refl _, fun _ _ => Join.refl _⟩

theorem HLe.trans {h₁ h₂ h₃ : Heap} {w₁ : HeapWf h₁} {w₂ : HeapWf h₂}
    {w₃ : HeapWf h₃} (h12 : HLe w₁ w₂) (h23 : HLe w₂ w₃) :
    HLe w₁ w₃ := by
  refine ⟨h12.1.trans h23.1, ?_⟩
  intro j hj
  exact Join.trans (h12.2 j hj)
    (h23.2 j (Nat.lt_of_lt_of_le hj h12.1))

/-- Allocation extends the heap order. -/
theorem HLe.push {h : Heap} (hwf : HeapWf h) {n : GNode}
    (hn : ∀ l r, n = GNode.app l r → l < h.len ∧ r < h.len) :
    HLe hwf (HeapWf_push hwf hn) := by
  refine ⟨?_, ?_⟩
  next =>
    show h.ns.length ≤ (h.ns ++ [n]).length
    rw [List.length_append]; omega
  next =>
    intro j hj
    rw [heapUnfold_push hwf hn (HeapWf_push hwf hn) j hj]
    exact Join.refl _

/-- A sound redirect extends the heap order: every old readback gets
    `src`-subtrees spliced to `dst`, and the two join. -/
theorem HLe.redirect {h : Heap} (hwf : HeapWf h) {src dst : Nat}
    (hok : RedirectOk h src dst)
    (hsd : Join (heapUnfold h hwf src) (heapUnfold h hwf dst)) :
    HLe hwf (HeapWf_redirect hwf hok.1 hok.2.1 hok.2.2.1 hok.2.2.2) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro j _
  have hsp := heapUnfold_redirect hwf hok.1 hok.2.1 hok.2.2.1 hok.2.2.2 j
  have hself : heapUnfold (h.redirect src dst)
      (HeapWf_redirect hwf hok.1 hok.2.1 hok.2.2.1 hok.2.2.2) dst =
      heapUnfold h hwf dst :=
    heapUnfold_redirect_below hwf hok.1 hok.2.1 hok.2.2.1 hok.2.2.2 dst
      (Or.inl rfl)
  rw [hself] at hsp
  exact Splice_join hsp hsd

/-- `mk_app` extends the heap order. -/
theorem MkApp_hle {h h' : Heap} {l r o : Nat} (hwf : HeapWf h)
    (hwf' : HeapWf h') (hm : MkApp h l r h' o) : HLe hwf hwf' := by
  rcases hm with ⟨hhp, -, hlb, hrb⟩ | ⟨hhe, -, -, -⟩
  next =>
    subst hhp
    exact HLe.push hwf (fun l0 r0 e => by
      cases e; exact ⟨hlb, hrb⟩)
  next =>
    subst hhe
    exact HLe.refl hwf

/-- The `mk_app` readback spec: the output unfolds to the application
    of the argument readbacks, up to joining. -/
theorem MkApp_join {h h' : Heap} {l r o : Nat}
    (hwf : HeapWf h) (hwf' : HeapWf h') (hm : MkApp h l r h' o) :
    Join (heapUnfold h' hwf' o)
      (.app (heapUnfold h' hwf' l) (heapUnfold h' hwf' r)) := by
  rcases hm with ⟨hhp, hoe, hlb, hrb⟩ | ⟨hhe, -, -, hj⟩
  next =>
    subst hhp; subst hoe
    -- `o = h.len` is fresh: its readback is exactly `app l r`.
    have hre : (h.push (GNode.app l r)).repr h.len = h.len := by
      show (resolveS (h.fw ++ [none]) ∅ h.ns.length).getD h.ns.length =
          h.ns.length
      rw [← hwf.fwlen]
      rw [resolveS, if_neg (by simp)]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have e : heapUnfold (h.push (GNode.app l r)) hwf' h.len =
        .app (heapUnfold (h.push (GNode.app l r)) hwf'
               ((h.push (GNode.app l r)).repr l))
             (heapUnfold (h.push (GNode.app l r)) hwf'
               ((h.push (GNode.app l r)).repr r)) := by
      conv_lhs => rw [heapUnfold]
      rw [hre]
      rw [show (h.push (GNode.app l r)).ns[h.len]? =
          some (GNode.app l r) from by
        show (h.ns ++ [GNode.app l r])[h.ns.length]? = _
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl]
    rw [e]
    have hnl : ∀ l0 r0, GNode.app l r = GNode.app l0 r0 →
        l0 < h.len ∧ r0 < h.len := fun l0 r0 e0 => by
      cases e0; exact ⟨hlb, hrb⟩
    have hlp : (h.push (GNode.app l r)).repr l = h.repr l :=
      Heap.repr_push hwf.fwok _ (by rw [hwf.fwlen]; exact hlb)
    have hrp : (h.push (GNode.app l r)).repr r = h.repr r :=
      Heap.repr_push hwf.fwok _ (by rw [hwf.fwlen]; exact hrb)
    have hrlb : h.repr l < h.len := by
      rw [Heap.len_eq, ← hwf.fwlen]
      exact (h.repr_spec hwf.fwok (by rw [hwf.fwlen]; exact hlb)).1
    have hrrb : h.repr r < h.len := by
      rw [Heap.len_eq, ← hwf.fwlen]
      exact (h.repr_spec hwf.fwok (by rw [hwf.fwlen]; exact hrb)).1
    rw [hlp, hrp,
        heapUnfold_push hwf hnl hwf' (h.repr l) hrlb,
        heapUnfold_push hwf hnl hwf' (h.repr r) hrrb,
        heapUnfold_push hwf hnl hwf' l hlb,
        heapUnfold_push hwf hnl hwf' r hrb,
        heapUnfold_repr hwf hlb, heapUnfold_repr hwf hrb]
    exact Join.refl _
  next =>
    subst hhe; exact hj hwf'

/-- The `mk_app` output is an in-range rep. -/
theorem MkApp_out {h h' : Heap} {l r o : Nat} (hwf : HeapWf h)
    (hm : MkApp h l r h' o) :
    o < h'.len ∧ h'.fw[o]? = some none := by
  rcases hm with ⟨hhp, hoe, -, -⟩ | ⟨hhe, holt, horep, -⟩
  next =>
    subst hhp; subst hoe
    refine ⟨?_, ?_⟩
    next =>
      show h.ns.length < (h.ns ++ [GNode.app l r]).length
      rw [List.length_append]; simp
    next =>
      show (h.fw ++ [none])[h.ns.length]? = some none
      rw [← hwf.fwlen]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
  next =>
    subst hhe; exact ⟨holt, horep⟩

/-- `repr` stays in range. -/
theorem Heap.repr_lt {h : Heap} (hwf : HeapWf h) {i : Nat}
    (hi : i < h.len) : h.repr i < h.len := by
  have hb := (h.repr_spec hwf.fwok (by rw [hwf.fwlen]; exact hi)).1
  rw [hwf.fwlen] at hb; exact hb

/-- Left child of an in-range app node is in range. -/
theorem heap_child_lt_l {h : Heap} (hwf : HeapWf h) {p c r : Nat}
    (hp : p < h.len) (hn : h.ns[p]? = some (GNode.app c r)) :
    c < h.len := by
  obtain ⟨hplt, hget⟩ := List.getElem?_eq_some_iff.1 hn
  exact Nat.lt_trans (hwf.dagwf p hplt c r hget).1 hp

/-- Right child of an in-range app node is in range. -/
theorem heap_child_lt_r {h : Heap} (hwf : HeapWf h) {p c r : Nat}
    (hp : p < h.len) (hn : h.ns[p]? = some (GNode.app c r)) :
    r < h.len := by
  obtain ⟨hplt, hget⟩ := List.getElem?_eq_some_iff.1 hn
  exact Nat.lt_trans (hwf.dagwf p hplt c r hget).2 hp

/-- Readback of an atom node. -/
theorem heapUnfold_atom {h : Heap} (hwf : HeapWf h) {i : Nat} {a : GAtom}
    (hn : h.ns[h.repr i]? = some (GNode.atom a)) :
    heapUnfold h hwf i = a.toTerm := by
  conv_lhs => rw [heapUnfold]; rw [hn]

/-- Readback of a var node. -/
theorem heapUnfold_var {h : Heap} (hwf : HeapWf h) {i n : Nat}
    (hn : h.ns[h.repr i]? = some (GNode.var n)) :
    heapUnfold h hwf i = .var n := by
  conv_lhs => rw [heapUnfold]; rw [hn]

/-- Readback of an app node. -/
theorem heapUnfold_app {h : Heap} (hwf : HeapWf h) {i l r : Nat}
    (hn : h.ns[h.repr i]? = some (GNode.app l r)) :
    heapUnfold h hwf i =
      .app (heapUnfold h hwf (h.repr l)) (heapUnfold h hwf (h.repr r)) := by
  conv_lhs => rw [heapUnfold]; rw [hn]

/-- The resolved-node redex check computes the term-level redex head
    of the left child's readback — the host correspondence for `cd`'s
    fall-through branch. -/
theorem isRedexNodeR_eq {h : Heap} (hwf : HeapWf h) {i l r : Nat}
    (hn : h.ns[h.repr i]? = some (GNode.app l r)) :
    isRedexNodeR h (h.repr i) =
      isRedexHead (heapUnfold h hwf (h.repr l)) := by
  have hplt : h.repr i < h.len := (List.getElem?_eq_some_iff.1 hn).1
  have hlt : l < h.len := heap_child_lt_l hwf hplt hn
  have hrl : h.repr l < h.len := h.repr_lt hwf hlt
  have hidem : h.repr (h.repr l) = h.repr l :=
    Heap.repr_idem hwf.fwok (by rw [hwf.fwlen]; exact hlt)
  simp only [isRedexNodeR, hn]
  cases hgl : h.ns[h.repr l]? with
  | none =>
      exfalso
      rw [List.getElem?_eq_none_iff] at hgl
      have hb : h.repr l < h.ns.length := hrl
      omega
  | some gl =>
      cases gl with
      | atom a =>
          have hgl' : h.ns[h.repr (h.repr l)]? = some (.atom a) := by
            rw [hidem]; exact hgl
          rw [heapUnfold_atom hwf hgl']
          cases a <;> rfl
      | var n =>
          have hgl' : h.ns[h.repr (h.repr l)]? = some (.var n) := by
            rw [hidem]; exact hgl
          rw [heapUnfold_var hwf hgl']
          rfl
      | app kl kr =>
          have hgl' : h.ns[h.repr (h.repr l)]? = some (.app kl kr) := by
            rw [hidem]; exact hgl
          rw [heapUnfold_app hwf hgl']
          have hklt : kl < h.len := heap_child_lt_l hwf hrl hgl
          have hrk : h.repr kl < h.len := h.repr_lt hwf hklt
          have hidemk : h.repr (h.repr kl) = h.repr kl :=
            Heap.repr_idem hwf.fwok (by rw [hwf.fwlen]; exact hklt)
          simp only []
          cases hgk : h.ns[h.repr kl]? with
          | none =>
              exfalso
              rw [List.getElem?_eq_none_iff] at hgk
              have hb : h.repr kl < h.ns.length := hrk
              omega
          | some gk =>
              cases gk with
              | atom a =>
                  have hgk' : h.ns[h.repr (h.repr kl)]? =
                      some (.atom a) := by
                    rw [hidemk]; exact hgk
                  rw [heapUnfold_atom hwf hgk']
                  cases a <;> rfl
              | var n =>
                  have hgk' : h.ns[h.repr (h.repr kl)]? =
                      some (.var n) := by
                    rw [hidemk]; exact hgk
                  rw [heapUnfold_var hwf hgk']
                  rfl
              | app kll klr =>
                  have hgk' : h.ns[h.repr (h.repr kl)]? =
                      some (.app kll klr) := by
                    rw [hidemk]; exact hgk
                  rw [heapUnfold_app hwf hgk']
                  have hkllt : kll < h.len :=
                    heap_child_lt_l hwf hrk hgk
                  have hrkl : h.repr kll < h.len :=
                    h.repr_lt hwf hkllt
                  have hideml : h.repr (h.repr kll) = h.repr kll :=
                    Heap.repr_idem hwf.fwok
                      (by rw [hwf.fwlen]; exact hkllt)
                  simp only []
                  cases hgl2 : h.ns[h.repr kll]? with
                  | none =>
                      exfalso
                      rw [List.getElem?_eq_none_iff] at hgl2
                      have hb : h.repr kll < h.ns.length := hrkl
                      omega
                  | some g2 =>
                      cases g2 with
                      | atom a =>
                          have hgl2' : h.ns[h.repr (h.repr kll)]? =
                              some (.atom a) := by
                            rw [hideml]; exact hgl2
                          rw [heapUnfold_atom hwf hgl2']
                          cases a <;> rfl
                      | var n =>
                          have hgl2' : h.ns[h.repr (h.repr kll)]? =
                              some (.var n) := by
                            rw [hideml]; exact hgl2
                          rw [heapUnfold_var hwf hgl2']
                          rfl
                      | app ka kb =>
                          have hgl2' : h.ns[h.repr (h.repr kll)]? =
                              some (.app ka kb) := by
                            rw [hideml]; exact hgl2
                          rw [heapUnfold_app hwf hgl2']
                          rfl

/-- `mk_app` preserves well-formedness; the output is an in-range
    rep. -/
theorem MkApp_wf {h h' : Heap} {l r o : Nat} (hwf : HeapWf h)
    (hm : MkApp h l r h' o) (hl : l < h.len) (hr : r < h.len) :
    ∃ hwf' : HeapWf h', h.len ≤ h'.len ∧ o < h'.len ∧
      h'.fw[o]? = some none := by
  rcases hm with ⟨hhp, hoe, -, -⟩ | ⟨hhe, holt, horep, -⟩
  next =>
    subst hhp; subst hoe
    refine ⟨HeapWf_push hwf (fun l0 r0 e0 => by
      cases e0; exact ⟨hl, hr⟩), ?_, ?_, ?_⟩
    next =>
      show h.ns.length ≤ (h.ns ++ [GNode.app l r]).length
      rw [List.length_append]; omega
    next =>
      show h.ns.length < (h.ns ++ [GNode.app l r]).length
      rw [List.length_append]; simp
    next =>
      show (h.fw ++ [none])[h.ns.length]? = some none
      rw [← hwf.fwlen]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
  next =>
    subst hhe; exact ⟨hwf, Nat.le_refl _, holt, horep⟩

/-- `HDev` preserves heap well-formedness: heaps only grow and the
    output index is in range. -/
theorem HDev_wf {D D' : Finset Nat} {h h' : Heap} {i o : Nat}
    (hd : HDev D h i h' o D') (hwf : HeapWf h) (hi : i < h.len) :
    ∃ hwf' : HeapWf h', h.len ≤ h'.len ∧ o < h'.len := by
  induction hd with
  | hit =>
      exact ⟨hwf, Nat.le_refl _, Heap.repr_lt hwf hi⟩
  | atom hn hmem =>
      exact ⟨hwf, Nat.le_refl _, Heap.repr_lt hwf hi⟩
  | var hn hmem =>
      exact ⟨hwf, Nat.le_refl _, Heap.repr_lt hwf hi⟩
  | norm_red hn_i hn_l hmem hdr hok ih =>
      have hrlt := heap_child_lt_r hwf (Heap.repr_lt hwf hi) hn_i
      obtain ⟨w₁, hle1, hjlt⟩ := ih hwf hrlt
      exact ⟨HeapWf_redirect w₁ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hle1, hjlt⟩
  | konst_red hn_i hn_l hn_kl hmem hdr hok ih =>
      have hrilt := Heap.repr_lt hwf hi
      have hrllt := Heap.repr_lt hwf (heap_child_lt_l hwf hrilt hn_i)
      have hkrlt := heap_child_lt_r hwf hrllt hn_l
      obtain ⟨w₁, hle1, hjlt⟩ := ih hwf hkrlt
      exact ⟨HeapWf_redirect w₁ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hle1, hjlt⟩
  | dup_red hn_i hn_l hn_kl hmem hdrx hdrf hmk1 hmk2 hok ihx ihf =>
      have hrilt := Heap.repr_lt hwf hi
      have hrlt := heap_child_lt_r hwf hrilt hn_i
      have hrllt := Heap.repr_lt hwf (heap_child_lt_l hwf hrilt hn_i)
      have hkrlt := heap_child_lt_r hwf hrllt hn_l
      obtain ⟨w₁, le1, jxlt⟩ := ihx hwf hrlt
      obtain ⟨w₂, le2, jflt⟩ := ihf w₁
        (Nat.lt_of_lt_of_le hkrlt le1)
      obtain ⟨w₃, le3, halt, -⟩ := MkApp_wf w₂ hmk1 jflt
        (Nat.lt_of_lt_of_le jxlt le2)
      obtain ⟨w₄, le4, hblt, -⟩ := MkApp_wf w₃ hmk2 halt
        (Nat.lt_of_lt_of_le jxlt (le2.trans le3))
      exact ⟨HeapWf_redirect w₄ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        le1.trans (le2.trans (le3.trans le4)), hblt⟩
  | comp_red hn_i hn_l hn_kl hn_kll hmem hdf hdg hdx hmk1 hmk2 hok
      ihf ihg ihx =>
      have hrilt := Heap.repr_lt hwf hi
      have hrlt := heap_child_lt_r hwf hrilt hn_i
      have hrllt := Heap.repr_lt hwf (heap_child_lt_l hwf hrilt hn_i)
      have hkrlt := heap_child_lt_r hwf hrllt hn_l
      have hrkllt := Heap.repr_lt hwf (heap_child_lt_l hwf hrllt hn_l)
      have hklrlt := heap_child_lt_r hwf hrkllt hn_kl
      obtain ⟨w₁, le1, jflt⟩ := ihf hwf hklrlt
      obtain ⟨w₂, le2, jglt⟩ := ihg w₁
        (Nat.lt_of_lt_of_le hkrlt le1)
      obtain ⟨w₃, le3, jxlt⟩ := ihx w₂
        (Nat.lt_of_lt_of_le hrlt (le1.trans le2))
      obtain ⟨w₄, le4, halt, -⟩ := MkApp_wf w₃ hmk1
        (Nat.lt_of_lt_of_le jglt le3) jxlt
      obtain ⟨w₅, le5, hblt, -⟩ := MkApp_wf w₄ hmk2
        (Nat.lt_of_lt_of_le jflt (le2.trans (le3.trans le4))) halt
      exact ⟨HeapWf_redirect w₅ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        le1.trans (le2.trans (le3.trans (le4.trans le5))), hblt⟩
  | swap_red hn_i hn_l hn_kl hn_kll hmem hdf hdx hdy hmk1 hmk2 hok
      ihf ihx ihy =>
      have hrilt := Heap.repr_lt hwf hi
      have hrlt := heap_child_lt_r hwf hrilt hn_i
      have hrllt := Heap.repr_lt hwf (heap_child_lt_l hwf hrilt hn_i)
      have hkrlt := heap_child_lt_r hwf hrllt hn_l
      have hrkllt := Heap.repr_lt hwf (heap_child_lt_l hwf hrllt hn_l)
      have hklrlt := heap_child_lt_r hwf hrkllt hn_kl
      obtain ⟨w₁, le1, jflt⟩ := ihf hwf hklrlt
      obtain ⟨w₂, le2, jxlt⟩ := ihx w₁
        (Nat.lt_of_lt_of_le hkrlt le1)
      obtain ⟨w₃, le3, jylt⟩ := ihy w₂
        (Nat.lt_of_lt_of_le hrlt (le1.trans le2))
      obtain ⟨w₄, le4, halt, -⟩ := MkApp_wf w₃ hmk1
        (Nat.lt_of_lt_of_le jflt (le2.trans le3)) jylt
      obtain ⟨w₅, le5, hblt, -⟩ := MkApp_wf w₄ hmk2 halt
        (Nat.lt_of_lt_of_le jxlt (le3.trans le4))
      exact ⟨HeapWf_redirect w₅ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        le1.trans (le2.trans (le3.trans (le4.trans le5))), hblt⟩
  | app_dev hn_i hguard hmem hdl hdr hmk hok ihl ihr =>
      have hrilt := Heap.repr_lt hwf hi
      have hllt := heap_child_lt_l hwf hrilt hn_i
      have hrlt := heap_child_lt_r hwf hrilt hn_i
      obtain ⟨w₁, le1, jflt⟩ := ihl hwf hllt
      obtain ⟨w₂, le2, jxlt⟩ := ihr w₁
        (Nat.lt_of_lt_of_le hrlt le1)
      obtain ⟨w₃, le3, holt, -⟩ := MkApp_wf w₂ hmk
        (Nat.lt_of_lt_of_le jflt le2) jxlt
      exact ⟨HeapWf_redirect w₃ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        le1.trans (le2.trans le3), holt⟩

/-- **Soundness of heap-level complete development.**  The output
    readback joins `cdBasis` of the input readback — `GraphDev`'s
    `DevRel_sound` lifted through forwarding redirects, allocation, and
    hash-consing (`MkApp`).  `HLe` records that intermediate heaps only
    splice developed results into old positions. -/
theorem HDev_sound {D D' : Finset Nat} {h h' : Heap} {i o : Nat}
    (hwf : HeapWf h) (hd : HDev D h i h' o D') (hi : i < h.len) :
    ∃ hwf' : HeapWf h',
      o < h'.len ∧ HLe hwf hwf' ∧
      Join (heapUnfold h' hwf' o) (cdBasis (heapUnfold h hwf i)) := by
  induction hd with
  | hit hmem =>
      rename_i D₀ h i
      refine ⟨hwf, Heap.repr_lt hwf hi, HLe.refl hwf, ?_⟩
      rw [← heapUnfold_repr hwf hi]
      exact Join_of_ired (cdBasis_ired _)
  | atom hn hmem =>
      rename_i D₀ h i a
      refine ⟨hwf, Heap.repr_lt hwf hi, HLe.refl hwf, ?_⟩
      rw [← heapUnfold_repr hwf hi, heapUnfold_atom hwf hn, cdBasis_atom]
      exact Join.refl _
  | var hn hmem =>
      rename_i D₀ h i n
      refine ⟨hwf, Heap.repr_lt hwf hi, HLe.refl hwf, ?_⟩
      rw [← heapUnfold_repr hwf hi, heapUnfold_var hwf hn, cdBasis_var]
      exact Join.refl _
  | norm_red hn_i hn_l hmem hdr hok ih =>
      rename_i D₀ h h₁ i l r j D₁
      have hrilt : h.repr i < h.len := Heap.repr_lt hwf hi
      have hllt : l < h.len := heap_child_lt_l hwf hrilt hn_i
      have hrlt : r < h.len := heap_child_lt_r hwf hrilt hn_i
      obtain ⟨w₁, hjlt, hle1, ihj⟩ := ih hwf hrlt
      have e_l : heapUnfold h hwf (h.repr l) = .norm := by
        rw [← heapUnfold_repr hwf hllt]
        exact heapUnfold_atom hwf hn_l
      have e_i : heapUnfold h hwf i =
          .app .norm (heapUnfold h hwf (h.repr r)) := by
        rw [heapUnfold_app hwf hn_i, e_l]
      have hcd : cdBasis (heapUnfold h hwf i) =
          cdBasis (heapUnfold h hwf r) := by
        rw [e_i]
        show cdBasis (heapUnfold h hwf (h.repr r)) =
            cdBasis (heapUnfold h hwf r)
        rw [← heapUnfold_repr hwf hrlt]
      have ihj' : Join (heapUnfold h₁ w₁ j)
          (cdBasis (heapUnfold h hwf i)) := by
        rw [hcd]; exact ihj
      have hsd : Join (heapUnfold h₁ w₁ (h.repr i))
          (heapUnfold h₁ w₁ j) := by
        have h1 := (hle1.2 (h.repr i) hrilt).symm
        rw [← heapUnfold_repr hwf hi] at h1
        exact h1.trans (Join_cd_left ihj')
      refine ⟨HeapWf_redirect w₁ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hjlt, hle1.trans (HLe.redirect w₁ hok hsd), ?_⟩
      rw [heapUnfold_redirect_below w₁ hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2 j (Or.inl rfl)]
      exact ihj'
  | konst_red hn_i hn_l hn_kl hmem hdr hok ih =>
      rename_i D₀ h h₁ i l r kl kr j D₁
      have hrilt : h.repr i < h.len := Heap.repr_lt hwf hi
      have hllt : l < h.len := heap_child_lt_l hwf hrilt hn_i
      have hrlt : r < h.len := heap_child_lt_r hwf hrilt hn_i
      have hrllt : h.repr l < h.len := Heap.repr_lt hwf hllt
      have hkllt : kl < h.len := heap_child_lt_l hwf hrllt hn_l
      have hkrlt : kr < h.len := heap_child_lt_r hwf hrllt hn_l
      obtain ⟨w₁, hjlt, hle1, ihj⟩ := ih hwf hkrlt
      have e_kl : heapUnfold h hwf (h.repr kl) = .konst := by
        rw [← heapUnfold_repr hwf hkllt]
        exact heapUnfold_atom hwf hn_kl
      have e_l : heapUnfold h hwf (h.repr l) =
          .app .konst (heapUnfold h hwf (h.repr kr)) := by
        rw [← heapUnfold_repr hwf hllt]
        rw [heapUnfold_app hwf hn_l, e_kl]
      have e_i : heapUnfold h hwf i =
          .app (.app .konst (heapUnfold h hwf (h.repr kr)))
            (heapUnfold h hwf (h.repr r)) := by
        rw [heapUnfold_app hwf hn_i, e_l]
      have hcd : cdBasis (heapUnfold h hwf i) =
          cdBasis (heapUnfold h hwf kr) := by
        rw [e_i]
        show cdBasis (heapUnfold h hwf (h.repr kr)) =
            cdBasis (heapUnfold h hwf kr)
        rw [← heapUnfold_repr hwf hkrlt]
      have ihj' : Join (heapUnfold h₁ w₁ j)
          (cdBasis (heapUnfold h hwf i)) := by
        rw [hcd]; exact ihj
      have hsd : Join (heapUnfold h₁ w₁ (h.repr i))
          (heapUnfold h₁ w₁ j) := by
        have h1 := (hle1.2 (h.repr i) hrilt).symm
        rw [← heapUnfold_repr hwf hi] at h1
        exact h1.trans (Join_cd_left ihj')
      refine ⟨HeapWf_redirect w₁ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hjlt, hle1.trans (HLe.redirect w₁ hok hsd), ?_⟩
      rw [heapUnfold_redirect_below w₁ hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2 j (Or.inl rfl)]
      exact ihj'
  | dup_red hn_i hn_l hn_kl hmem hdrx hdrf hmk1 hmk2 hok ihx ihf =>
      rename_i D₀ h h₁ h₂ h₃ h₄ i l r kl kr jx jf a b D₁ D₂
      have hrilt : h.repr i < h.len := Heap.repr_lt hwf hi
      have hllt : l < h.len := heap_child_lt_l hwf hrilt hn_i
      have hrlt : r < h.len := heap_child_lt_r hwf hrilt hn_i
      have hrllt : h.repr l < h.len := Heap.repr_lt hwf hllt
      have hkllt : kl < h.len := heap_child_lt_l hwf hrllt hn_l
      have hkrlt : kr < h.len := heap_child_lt_r hwf hrllt hn_l
      obtain ⟨w₁, jxlt, hle1, ihxj⟩ := ihx hwf hrlt
      obtain ⟨w₂, jflt, hle2, ihfj⟩ := ihf w₁
        (Nat.lt_of_lt_of_le hkrlt hle1.1)
      obtain ⟨w₃, le3, halt, -⟩ := MkApp_wf w₂ hmk1 jflt
        (Nat.lt_of_lt_of_le jxlt hle2.1)
      obtain ⟨w₄, le4, hblt, -⟩ := MkApp_wf w₃ hmk2 halt
        (Nat.lt_of_lt_of_le jxlt (hle2.1.trans le3))
      have e_kl : heapUnfold h hwf (h.repr kl) = .dup := by
        rw [← heapUnfold_repr hwf hkllt]
        exact heapUnfold_atom hwf hn_kl
      have e_l : heapUnfold h hwf (h.repr l) =
          .app .dup (heapUnfold h hwf (h.repr kr)) := by
        rw [← heapUnfold_repr hwf hllt]
        rw [heapUnfold_app hwf hn_l, e_kl]
      have e_i : heapUnfold h hwf i =
          .app (.app .dup (heapUnfold h hwf (h.repr kr)))
            (heapUnfold h hwf (h.repr r)) := by
        rw [heapUnfold_app hwf hn_i, e_l]
      have hcd : cdBasis (heapUnfold h hwf i) =
          .app (.app (cdBasis (heapUnfold h hwf (h.repr kr)))
                (cdBasis (heapUnfold h hwf (h.repr r))))
            (cdBasis (heapUnfold h hwf (h.repr r))) := by
        rw [e_i]; rfl
      have hle23 : HLe w₂ w₃ := MkApp_hle w₂ w₃ hmk1
      have hle34 : HLe w₃ w₄ := MkApp_hle w₃ w₄ hmk2
      have jX : Join (heapUnfold h₂ w₂ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) := by
        rw [heapUnfold_repr hwf hrlt] at ihxj
        exact (hle2.2 jx jxlt).symm.trans ihxj
      have jF : Join (heapUnfold h₂ w₂ jf)
          (cdBasis (heapUnfold h hwf (h.repr kr))) := by
        have hkr : Join (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h₁ w₁ kr)) := by
          rw [← heapUnfold_repr hwf hkrlt]
          exact cdJoin_of_join (hle1.2 kr hkrlt)
        exact ihfj.trans hkr.symm
      have jF3 : Join (heapUnfold h₃ w₃ jf)
          (cdBasis (heapUnfold h hwf (h.repr kr))) :=
        (hle23.2 jf jflt).symm.trans jF
      have jX3 : Join (heapUnfold h₃ w₃ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) :=
        (hle23.2 jx (Nat.lt_of_lt_of_le jxlt hle2.1)).symm.trans jX
      have ja : Join (heapUnfold h₃ w₃ a)
          (.app (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h hwf (h.repr r)))) :=
        (MkApp_join w₂ w₃ hmk1).trans (Join_app jF3 jX3)
      have hle14 : HLe hwf w₄ :=
        hle1.trans (hle2.trans (hle23.trans hle34))
      have ja4 : Join (heapUnfold h₄ w₄ a)
          (.app (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h hwf (h.repr r)))) :=
        (hle34.2 a halt).symm.trans ja
      have jX4 : Join (heapUnfold h₄ w₄ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) :=
        (hle34.2 jx
          (Nat.lt_of_lt_of_le jxlt (hle2.1.trans le3))).symm.trans jX3
      have jb : Join (heapUnfold h₄ w₄ b)
          (cdBasis (heapUnfold h hwf i)) := by
        rw [hcd]
        exact (MkApp_join w₃ w₄ hmk2).trans (Join_app ja4 jX4)
      have hsd : Join (heapUnfold h₄ w₄ (h.repr i))
          (heapUnfold h₄ w₄ b) := by
        have h1 := (hle14.2 (h.repr i) hrilt).symm
        rw [← heapUnfold_repr hwf hi] at h1
        exact h1.trans (Join_cd_left jb)
      refine ⟨HeapWf_redirect w₄ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hblt, hle14.trans (HLe.redirect w₄ hok hsd), ?_⟩
      rw [heapUnfold_redirect_below w₄ hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2 b (Or.inl rfl)]
      exact jb
  | comp_red hn_i hn_l hn_kl hn_kll hmem hdf hdg hdx hmk1 hmk2 hok
      ihf ihg ihx =>
      rename_i D₀ h h₁ h₂ h₃ h₄ h₅ i l r kl kr kll klr jf jg jx a b
        D₁ D₂ D₃
      have hrilt : h.repr i < h.len := Heap.repr_lt hwf hi
      have hllt : l < h.len := heap_child_lt_l hwf hrilt hn_i
      have hrlt : r < h.len := heap_child_lt_r hwf hrilt hn_i
      have hrllt : h.repr l < h.len := Heap.repr_lt hwf hllt
      have hkllt : kl < h.len := heap_child_lt_l hwf hrllt hn_l
      have hkrlt : kr < h.len := heap_child_lt_r hwf hrllt hn_l
      have hrkllt : h.repr kl < h.len := Heap.repr_lt hwf hkllt
      have hklllt : kll < h.len := heap_child_lt_l hwf hrkllt hn_kl
      have hklrlt : klr < h.len := heap_child_lt_r hwf hrkllt hn_kl
      obtain ⟨w₁, jflt, hle1, ihfj⟩ := ihf hwf hklrlt
      obtain ⟨w₂, jglt, hle2, ihgj⟩ := ihg w₁
        (Nat.lt_of_lt_of_le hkrlt hle1.1)
      obtain ⟨w₃, jxlt, hle3, ihxj⟩ := ihx w₂
        (Nat.lt_of_lt_of_le hrlt (hle1.1.trans hle2.1))
      obtain ⟨w₄, le4, halt, -⟩ := MkApp_wf w₃ hmk1
        (Nat.lt_of_lt_of_le jglt hle3.1) jxlt
      obtain ⟨w₅, le5, hblt, -⟩ := MkApp_wf w₄ hmk2
        (Nat.lt_of_lt_of_le jflt
          (hle2.1.trans (hle3.1.trans le4))) halt
      have e_kll : heapUnfold h hwf (h.repr kll) = .comp := by
        rw [← heapUnfold_repr hwf hklllt]
        exact heapUnfold_atom hwf hn_kll
      have e_kl : heapUnfold h hwf (h.repr kl) =
          .app .comp (heapUnfold h hwf (h.repr klr)) := by
        rw [← heapUnfold_repr hwf hkllt]
        rw [heapUnfold_app hwf hn_kl, e_kll]
      have e_l : heapUnfold h hwf (h.repr l) =
          .app (.app .comp (heapUnfold h hwf (h.repr klr)))
            (heapUnfold h hwf (h.repr kr)) := by
        rw [← heapUnfold_repr hwf hllt]
        rw [heapUnfold_app hwf hn_l, e_kl]
      have e_i : heapUnfold h hwf i =
          .app (.app (.app .comp (heapUnfold h hwf (h.repr klr)))
              (heapUnfold h hwf (h.repr kr)))
            (heapUnfold h hwf (h.repr r)) := by
        rw [heapUnfold_app hwf hn_i, e_l]
      have hcd : cdBasis (heapUnfold h hwf i) =
          .app (cdBasis (heapUnfold h hwf (h.repr klr)))
            (.app (cdBasis (heapUnfold h hwf (h.repr kr)))
              (cdBasis (heapUnfold h hwf (h.repr r)))) := by
        rw [e_i]; rfl
      have hle34 : HLe w₃ w₄ := MkApp_hle w₃ w₄ hmk1
      have hle45 : HLe w₄ w₅ := MkApp_hle w₄ w₅ hmk2
      have jF : Join (heapUnfold h₁ w₁ jf)
          (cdBasis (heapUnfold h hwf (h.repr klr))) := by
        rw [heapUnfold_repr hwf hklrlt] at ihfj
        exact ihfj
      have jG : Join (heapUnfold h₂ w₂ jg)
          (cdBasis (heapUnfold h hwf (h.repr kr))) := by
        have hkr : Join (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h₁ w₁ kr)) := by
          rw [← heapUnfold_repr hwf hkrlt]
          exact cdJoin_of_join (hle1.2 kr hkrlt)
        exact ihgj.trans hkr.symm
      have jX : Join (heapUnfold h₃ w₃ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) := by
        have hr : Join (cdBasis (heapUnfold h hwf (h.repr r)))
            (cdBasis (heapUnfold h₂ w₂ r)) := by
          rw [← heapUnfold_repr hwf hrlt]
          exact cdJoin_of_join
            ((hle1.trans hle2).2 r hrlt)
        exact ihxj.trans hr.symm
      have jG4 : Join (heapUnfold h₄ w₄ jg)
          (cdBasis (heapUnfold h hwf (h.repr kr))) :=
        ((hle3.trans hle34).2 jg jglt).symm.trans jG
      have jX4 : Join (heapUnfold h₄ w₄ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) :=
        (hle34.2 jx jxlt).symm.trans jX
      have ja : Join (heapUnfold h₄ w₄ a)
          (.app (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h hwf (h.repr r)))) :=
        (MkApp_join w₃ w₄ hmk1).trans (Join_app jG4 jX4)
      have ja5 : Join (heapUnfold h₅ w₅ a)
          (.app (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h hwf (h.repr r)))) :=
        (hle45.2 a halt).symm.trans ja
      have jF5 : Join (heapUnfold h₅ w₅ jf)
          (cdBasis (heapUnfold h hwf (h.repr klr))) :=
        ((hle2.trans (hle3.trans (hle34.trans hle45))).2 jf jflt).symm.trans
          jF
      have jb : Join (heapUnfold h₅ w₅ b)
          (cdBasis (heapUnfold h hwf i)) := by
        rw [hcd]
        exact (MkApp_join w₄ w₅ hmk2).trans (Join_app jF5 ja5)
      have hle15 : HLe hwf w₅ :=
        hle1.trans (hle2.trans (hle3.trans (hle34.trans hle45)))
      have hsd : Join (heapUnfold h₅ w₅ (h.repr i))
          (heapUnfold h₅ w₅ b) := by
        have h1 := (hle15.2 (h.repr i) hrilt).symm
        rw [← heapUnfold_repr hwf hi] at h1
        exact h1.trans (Join_cd_left jb)
      refine ⟨HeapWf_redirect w₅ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hblt, hle15.trans (HLe.redirect w₅ hok hsd), ?_⟩
      rw [heapUnfold_redirect_below w₅ hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2 b (Or.inl rfl)]
      exact jb
  | swap_red hn_i hn_l hn_kl hn_kll hmem hdf hdx hdy hmk1 hmk2 hok
      ihf ihx ihy =>
      rename_i D₀ h h₁ h₂ h₃ h₄ h₅ i l r kl kr kll klr jf jx jy a b
        D₁ D₂ D₃
      have hrilt : h.repr i < h.len := Heap.repr_lt hwf hi
      have hllt : l < h.len := heap_child_lt_l hwf hrilt hn_i
      have hrlt : r < h.len := heap_child_lt_r hwf hrilt hn_i
      have hrllt : h.repr l < h.len := Heap.repr_lt hwf hllt
      have hkllt : kl < h.len := heap_child_lt_l hwf hrllt hn_l
      have hkrlt : kr < h.len := heap_child_lt_r hwf hrllt hn_l
      have hrkllt : h.repr kl < h.len := Heap.repr_lt hwf hkllt
      have hklllt : kll < h.len := heap_child_lt_l hwf hrkllt hn_kl
      have hklrlt : klr < h.len := heap_child_lt_r hwf hrkllt hn_kl
      obtain ⟨w₁, jflt, hle1, ihfj⟩ := ihf hwf hklrlt
      obtain ⟨w₂, jxlt, hle2, ihxj⟩ := ihx w₁
        (Nat.lt_of_lt_of_le hkrlt hle1.1)
      obtain ⟨w₃, jylt, hle3, ihyj⟩ := ihy w₂
        (Nat.lt_of_lt_of_le hrlt (hle1.1.trans hle2.1))
      obtain ⟨w₄, le4, halt, -⟩ := MkApp_wf w₃ hmk1
        (Nat.lt_of_lt_of_le jflt (hle2.1.trans hle3.1)) jylt
      obtain ⟨w₅, le5, hblt, -⟩ := MkApp_wf w₄ hmk2 halt
        (Nat.lt_of_lt_of_le jxlt (hle3.1.trans le4))
      have e_kll : heapUnfold h hwf (h.repr kll) = .swap := by
        rw [← heapUnfold_repr hwf hklllt]
        exact heapUnfold_atom hwf hn_kll
      have e_kl : heapUnfold h hwf (h.repr kl) =
          .app .swap (heapUnfold h hwf (h.repr klr)) := by
        rw [← heapUnfold_repr hwf hkllt]
        rw [heapUnfold_app hwf hn_kl, e_kll]
      have e_l : heapUnfold h hwf (h.repr l) =
          .app (.app .swap (heapUnfold h hwf (h.repr klr)))
            (heapUnfold h hwf (h.repr kr)) := by
        rw [← heapUnfold_repr hwf hllt]
        rw [heapUnfold_app hwf hn_l, e_kl]
      have e_i : heapUnfold h hwf i =
          .app (.app (.app .swap (heapUnfold h hwf (h.repr klr)))
              (heapUnfold h hwf (h.repr kr)))
            (heapUnfold h hwf (h.repr r)) := by
        rw [heapUnfold_app hwf hn_i, e_l]
      have hcd : cdBasis (heapUnfold h hwf i) =
          .app (.app (cdBasis (heapUnfold h hwf (h.repr klr)))
                (cdBasis (heapUnfold h hwf (h.repr r))))
            (cdBasis (heapUnfold h hwf (h.repr kr))) := by
        rw [e_i]; rfl
      have hle34 : HLe w₃ w₄ := MkApp_hle w₃ w₄ hmk1
      have hle45 : HLe w₄ w₅ := MkApp_hle w₄ w₅ hmk2
      have jF : Join (heapUnfold h₁ w₁ jf)
          (cdBasis (heapUnfold h hwf (h.repr klr))) := by
        rw [heapUnfold_repr hwf hklrlt] at ihfj
        exact ihfj
      have jX : Join (heapUnfold h₂ w₂ jx)
          (cdBasis (heapUnfold h hwf (h.repr kr))) := by
        have hkr : Join (cdBasis (heapUnfold h hwf (h.repr kr)))
            (cdBasis (heapUnfold h₁ w₁ kr)) := by
          rw [← heapUnfold_repr hwf hkrlt]
          exact cdJoin_of_join (hle1.2 kr hkrlt)
        exact ihxj.trans hkr.symm
      have jY : Join (heapUnfold h₃ w₃ jy)
          (cdBasis (heapUnfold h hwf (h.repr r))) := by
        have hr : Join (cdBasis (heapUnfold h hwf (h.repr r)))
            (cdBasis (heapUnfold h₂ w₂ r)) := by
          rw [← heapUnfold_repr hwf hrlt]
          exact cdJoin_of_join
            ((hle1.trans hle2).2 r hrlt)
        exact ihyj.trans hr.symm
      have jF4 : Join (heapUnfold h₄ w₄ jf)
          (cdBasis (heapUnfold h hwf (h.repr klr))) :=
        ((hle2.trans (hle3.trans hle34)).2 jf jflt).symm.trans jF
      have jY4 : Join (heapUnfold h₄ w₄ jy)
          (cdBasis (heapUnfold h hwf (h.repr r))) :=
        (hle34.2 jy jylt).symm.trans jY
      have ja : Join (heapUnfold h₄ w₄ a)
          (.app (cdBasis (heapUnfold h hwf (h.repr klr)))
            (cdBasis (heapUnfold h hwf (h.repr r)))) :=
        (MkApp_join w₃ w₄ hmk1).trans (Join_app jF4 jY4)
      have ja5 : Join (heapUnfold h₅ w₅ a)
          (.app (cdBasis (heapUnfold h hwf (h.repr klr)))
            (cdBasis (heapUnfold h hwf (h.repr r)))) :=
        (hle45.2 a halt).symm.trans ja
      have jX5 : Join (heapUnfold h₅ w₅ jx)
          (cdBasis (heapUnfold h hwf (h.repr kr))) :=
        ((hle3.trans (hle34.trans hle45)).2 jx jxlt).symm.trans jX
      have jb : Join (heapUnfold h₅ w₅ b)
          (cdBasis (heapUnfold h hwf i)) := by
        rw [hcd]
        exact (MkApp_join w₄ w₅ hmk2).trans (Join_app ja5 jX5)
      have hle15 : HLe hwf w₅ :=
        hle1.trans (hle2.trans (hle3.trans (hle34.trans hle45)))
      have hsd : Join (heapUnfold h₅ w₅ (h.repr i))
          (heapUnfold h₅ w₅ b) := by
        have h1 := (hle15.2 (h.repr i) hrilt).symm
        rw [← heapUnfold_repr hwf hi] at h1
        exact h1.trans (Join_cd_left jb)
      refine ⟨HeapWf_redirect w₅ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        hblt, hle15.trans (HLe.redirect w₅ hok hsd), ?_⟩
      rw [heapUnfold_redirect_below w₅ hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2 b (Or.inl rfl)]
      exact jb
  | app_dev hn_i hguard hmem hdl hdr hmk hok ihl ihr =>
      rename_i D₀ h h₁ h₂ h₃ i l r jf jx o D₁ D₂
      have hrilt : h.repr i < h.len := Heap.repr_lt hwf hi
      have hllt : l < h.len := heap_child_lt_l hwf hrilt hn_i
      have hrlt : r < h.len := heap_child_lt_r hwf hrilt hn_i
      have hrllt : h.repr l < h.len := Heap.repr_lt hwf hllt
      obtain ⟨w₁, jflt, hle1, ihlf⟩ := ihl hwf hllt
      obtain ⟨w₂, jxlt, hle2, ihrf⟩ := ihr w₁
        (Nat.lt_of_lt_of_le hrlt hle1.1)
      obtain ⟨w₃, le3, holt, -⟩ := MkApp_wf w₂ hmk
        (Nat.lt_of_lt_of_le jflt hle2.1) jxlt
      have e_i : heapUnfold h hwf i =
          .app (heapUnfold h hwf (h.repr l))
            (heapUnfold h hwf (h.repr r)) :=
        heapUnfold_app hwf hn_i
      have hnr : isRedexHead (heapUnfold h hwf (h.repr l)) = false :=
        hguard hwf
      have hcd : cdBasis (heapUnfold h hwf i) =
          .app (cdBasis (heapUnfold h hwf (h.repr l)))
            (cdBasis (heapUnfold h hwf (h.repr r))) := by
        rw [e_i]; exact cdBasis_app_generic hnr
      have hle23 : HLe w₂ w₃ := MkApp_hle w₂ w₃ hmk
      have jF : Join (heapUnfold h₂ w₂ jf)
          (cdBasis (heapUnfold h hwf (h.repr l))) := by
        rw [heapUnfold_repr hwf hllt] at ihlf
        exact (hle2.2 jf jflt).symm.trans ihlf
      have jX : Join (heapUnfold h₂ w₂ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) := by
        have hr : Join (cdBasis (heapUnfold h hwf (h.repr r)))
            (cdBasis (heapUnfold h₁ w₁ r)) := by
          rw [← heapUnfold_repr hwf hrlt]
          exact cdJoin_of_join (hle1.2 r hrlt)
        exact ihrf.trans hr.symm
      have jF3 : Join (heapUnfold h₃ w₃ jf)
          (cdBasis (heapUnfold h hwf (h.repr l))) :=
        (hle23.2 jf (Nat.lt_of_lt_of_le jflt hle2.1)).symm.trans jF
      have jX3 : Join (heapUnfold h₃ w₃ jx)
          (cdBasis (heapUnfold h hwf (h.repr r))) :=
        (hle23.2 jx jxlt).symm.trans jX
      have jo : Join (heapUnfold h₃ w₃ o)
          (cdBasis (heapUnfold h hwf i)) := by
        rw [hcd]
        exact (MkApp_join w₂ w₃ hmk).trans (Join_app jF3 jX3)
      have hle13 : HLe hwf w₃ := hle1.trans (hle2.trans hle23)
      have hsd : Join (heapUnfold h₃ w₃ (h.repr i))
          (heapUnfold h₃ w₃ o) := by
        have h1 := (hle13.2 (h.repr i) hrilt).symm
        rw [← heapUnfold_repr hwf hi] at h1
        exact h1.trans (Join_cd_left jo)
      refine ⟨HeapWf_redirect w₃ hok.1 hok.2.1 hok.2.2.1 hok.2.2.2,
        holt, hle13.trans (HLe.redirect w₃ hok hsd), ?_⟩
      rw [heapUnfold_redirect_below w₃ hok.1 hok.2.1 hok.2.2.1
        hok.2.2.2 o (Or.inl rfl)]
      exact jo

/-- `Join` lifts through `cdIter`. -/
theorem cdIter_join {a b : ITerm} (n : Nat) (h : Join a b) :
    Join (cdIter n a) (cdIter n b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (cdJoin_of_join h)

/-- A chain of `n` heap development rounds — the host `reduce_cd`
    loop.  Each round's input is the previous round's output node
    (`HDev` outputs are representatives, matching the host's
    `cur = repr(nxt)`). -/
inductive HDevChain : Heap → Nat → Heap → Nat → Nat → Prop where
  | nil {h : Heap} {i : Nat} : HDevChain h i h i 0
  | cons {D₀ D₁ : Finset Nat} {h h₁ h₂ : Heap} {i j k n : Nat} :
      HDev D₀ h i h₁ j D₁ → HDevChain h₁ j h₂ k n →
      HDevChain h i h₂ k (n + 1)

/-- Round parity for the shared path: `n` heap development rounds
    produce a readback that joins `cdIter n` of the input readback —
    the `rounds=` counter is formal iterated complete development. -/
theorem HDevChain_unfold {h i h' j n} (hc : HDevChain h i h' j n)
    (hwf : HeapWf h) (hi : i < h.len) :
    ∃ hwf' : HeapWf h', j < h'.len ∧
      Join (heapUnfold h' hwf' j)
        (cdIter n (heapUnfold h hwf i)) := by
  induction hc with
  | nil => exact ⟨hwf, hi, Join.refl _⟩
  | cons hd _ ih =>
      obtain ⟨w₁, -, hjlt⟩ := HDev_wf hd hwf hi
      obtain ⟨w₂, hklt, hjoin⟩ := ih w₁ hjlt
      obtain ⟨w₁', -, -, hsound⟩ := HDev_sound hwf hd hi
      refine ⟨w₂, hklt, ?_⟩
      have hs : Join (heapUnfold _ w₁ _) (cdBasis (heapUnfold _ hwf _)) :=
        hsound
      exact hjoin.trans (cdIter_join _ hs)

/-- Heap development chains stay inside basis reduction up to
    joining — the observational-equivalence statement for the shared
    executor loop. -/
theorem HDevChain_join {h i h' j n} (hc : HDevChain h i h' j n)
    (hwf : HeapWf h) (hi : i < h.len) :
    ∃ hwf' : HeapWf h', j < h'.len ∧
      Join (heapUnfold h hwf i) (heapUnfold h' hwf' j) := by
  obtain ⟨w', hj, hjoin⟩ := HDevChain_unfold hc hwf hi
  obtain ⟨u, hju, hcu⟩ := hjoin
  exact ⟨w', hj, u, (cdIter_ired n _).trans hcu, hju⟩

end ISAR
