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

/-- A heap with the same `repr` behaviour and entries. -/
structure HeapWf (h : Heap) : Prop where
  dagwf : DagWf h.ns
  fwlen : h.fw.length = h.ns.length
  fwok : FwOk h.fw

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

end ISAR
