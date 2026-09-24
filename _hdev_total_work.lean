import ISAR.HeapDev

/-!
# `HDev_total` — totality of heap-level complete development (work file)

Measure: `oldSub h₀ h i` — resolved descendants of `i` in the current
heap `h` that already existed in the outer heap `h₀`.  The derivation
exhibited uses only the fresh branch of `MkApp`; then every output's
old-descendants stay inside the input's old-descendants, which both
drives the containment for the measure drop and discharges
`RedirectOk`'s acyclicity obligation.

Once green this moves into `HeapDev.lean` before `HDevChain`.
-/

namespace ISAR

open Relation

/-- `repr` is idempotent whenever the rep is in range — no hypothesis
    on the raw index itself needed. -/
theorem Heap.repr_idem_lt {h : Heap} (hwf : HeapWf h) {i : Nat}
    (_hi : h.repr i < h.len) : h.repr (h.repr i) = h.repr i := by
  rcases Nat.lt_or_ge i h.fw.length with hlt | hge
  next =>
    exact Heap.repr_idem hwf.fwok hlt
  next =>
    have hri : h.repr i = i := Heap.repr_oob hge
    rw [hri]
    exact hri

/-- Resolved children are reps. -/
theorem RChild_isRep {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j i) : h.repr j = j := by
  obtain ⟨l, r, hns, hjl⟩ := hc
  obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hns
  obtain ⟨hli, hri⟩ := hwf.dagwf (h.repr i) hilt l r hget
  rcases hjl with hjl | hjl
  next =>
    rw [← hjl]
    apply Heap.repr_idem hwf.fwok
    rw [hwf.fwlen]; omega
  next =>
    rw [← hjl]
    apply Heap.repr_idem hwf.fwok
    rw [hwf.fwlen]; omega

/-- A resolved child of `i` is a resolved child of `repr i`. -/
theorem RChild_of_repr {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j i) : RChild h j (h.repr i) := by
  obtain ⟨l, r, hns, hjl⟩ := hc
  have hidem : h.repr (h.repr i) = h.repr i :=
    Heap.repr_idem_lt hwf (List.getElem?_eq_some_iff.mp hns).1
  exact ⟨l, r, by rwa [hidem], hjl⟩

/-- The rep of an `RChild`-parent is in range even when the parent is
    `repr i` (the raw `i` may be out of range). -/
theorem RChild_repr_parent_lt {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j (h.repr i)) : h.repr i < h.len := by
  obtain ⟨l, r, hns, -⟩ := hc
  have hlt : h.repr (h.repr i) < h.len := (List.getElem?_eq_some_iff.mp hns).1
  rcases Nat.lt_or_ge i h.fw.length with hi | hi
  next =>
    rw [← Heap.repr_idem hwf.fwok hi]; exact hlt
  next =>
    have hri : h.repr i = i := Heap.repr_oob hi
    rw [hri] at hlt; exact hlt

/-- A resolved child of `repr i` is a resolved child of `i`. -/
theorem RChild_repr_of {h : Heap} (hwf : HeapWf h) {j i : Nat}
    (hc : RChild h j (h.repr i)) : RChild h j i := by
  have hplt : h.repr i < h.len := RChild_repr_parent_lt hwf hc
  obtain ⟨l, r, hns, hjl⟩ := hc
  have hidem : h.repr (h.repr i) = h.repr i := Heap.repr_idem_lt hwf hplt
  exact ⟨l, r, by rwa [hidem] at hns, hjl⟩

/-- `RSub` only sees the resolved endpoint.  Only the last link of the
    chain mentions it, so a one-step case split suffices. -/
theorem RSub_repr {h : Heap} (hwf : HeapWf h) {j i : Nat} :
    RSub h j i ↔ RSub h j (h.repr i) := by
  constructor
  next =>
    intro hsub
    cases hsub with
    | single hc =>
        apply TransGen.single
        exact RChild_of_repr hwf hc
    | tail hsub hstep =>
        apply TransGen.tail hsub
        exact RChild_of_repr hwf hstep
  next =>
    intro hsub
    cases hsub with
    | single hc =>
        apply TransGen.single
        exact RChild_repr_of hwf hc
    | tail hsub hstep =>
        apply TransGen.tail hsub
        exact RChild_repr_of hwf hstep

/-- Old live descendants of `i`: nodes that existed in the outer heap
    `h₀`, resolve-below `i` in the current heap `h`, and whose
    representative is not sealed by the memo `D`.  This is the
    termination measure: every non-`hit` recursive premise strictly
    shrinks it. -/
noncomputable def oldSub (h₀ h : Heap) (D : Finset Nat) (i : Nat) :
    Finset Nat := by
  classical
  exact (Finset.range h₀.len).filter
    (fun k => RSub h k i ∧ h.repr k ∉ D)

/-- A derivation fragment: heaps related by allocation and guarded
    redirects — the shape of growth inside the development of `top`,
    watched on a set `W` of indices whose images must stay inside the
    developed cone.  Each redirect is annotated by three obligations,
    all discharged from the producing `HDev` constructor:

    `hb`    — descent bound: every old node below `dst` was already
              below `src` (outputs contain only parts of the input).
    `horig` — origin: the source sits at-or-below the current image
              of `top` — only the developed cone is redirected, so
              `top`'s rep is stable mid-fragment (a source equal to
              `repr top` would give `RSub src src`, killed by `Acyc`).
    `himg`  — image embedding: old nodes whose current image sits
              below `src` land at-or-below `dst` — the output retains
              the images of everything it consumed. -/
inductive HSteps (h₀ : Heap) (top : Nat) :
    Heap → Heap → Prop where
  | refl (h : Heap) : HSteps h₀ top h h
  | push {h h₁ : Heap} (n : GNode) (hs : HSteps h₀ top h h₁)
      (hn : ∀ l r, n = GNode.app l r → l < h₁.len ∧ r < h₁.len) :
      HSteps h₀ top h (h₁.push n)
  | redirect {h h₁ : Heap} {src dst : Nat}
      (hs : HSteps h₀ top h h₁)
      (hok : RedirectOk h₁ src dst)
      (hb : ∀ k < h₀.len, (k = dst ∨ RSub h₁ k dst) → RSub h₁ k src)
      (horig : RSub h₁ src (h₁.repr top) ∨ h₁.repr top = src)
      (himg : ∀ x < h₀.len, RSub h₁ (h₁.repr x) src →
        (h₁.redirect src dst).repr x = dst ∨
        RSub (h₁.redirect src dst) ((h₁.redirect src dst).repr x) dst) :
      HSteps h₀ top h (h₁.redirect src dst)

theorem HSteps.trans {h₀ : Heap} {top : Nat} {a b c : Heap}
    (h1 : HSteps h₀ top a b)
    (h2 : HSteps h₀ top b c) : HSteps h₀ top a c := by
  induction h2 with
  | refl => exact h1
  | push n hs hn ih => exact HSteps.push n ih hn
  | redirect hs hok hb horig himg ih =>
      exact HSteps.redirect ih hok hb horig himg

theorem HSteps_len {h₀ : Heap} {top : Nat} {a b : Heap}
    (hs : HSteps h₀ top a b) :
    a.len ≤ b.len := by
  induction hs with
  | refl => exact Nat.le_refl _
  | push n _ _ ih =>
      simp only [Heap.len, Heap.push, List.length_append, List.length_cons,
        List.length_nil] at ih ⊢
      omega
  | redirect _ _ _ _ _ ih => exact ih

theorem HSteps_wf {h₀ : Heap} {top : Nat} {a b : Heap}
    (hs : HSteps h₀ top a b)
    (hwf : HeapWf a) : HeapWf b := by
  induction hs with
  | refl => exact hwf
  | push n _ hn ih => exact HeapWf_push ih hn
  | redirect _ hok _ _ _ ih =>
      exact HeapWf_redirect ih hok.1 hok.2.1 hok.2.2.1 hok.2.2.2

/-- `repr` composition across a fragment: the post-fragment rep of an
    old rep equals the post-fragment rep of the raw index. -/
theorem HSteps_repr_of_repr {h₀ h h₂ : Heap} {top : Nat}
    (hwf : HeapWf h)
    (hs : HSteps h₀ top h h₂) {c : Nat} (hc : c < h.fw.length) :
    h₂.repr (h.repr c) = h₂.repr c := by
  induction hs with
  | refl => exact Heap.repr_idem hwf.fwok hc
  | push n hs hn ih =>
      rename_i h₁
      have hwf₁ : HeapWf h₁ := HSteps_wf hs hwf
      have hl := HSteps_len hs
      have hcl : c < h₁.fw.length := by
        have hc' : c < h.ns.length := by rw [← hwf.fwlen]; exact hc
        rw [hwf₁.fwlen]
        exact Nat.lt_of_lt_of_le hc' hl
      have hrcl : h.repr c < h₁.fw.length := by
        have h1 : h.repr c < h.ns.length := by
          have h2 := (h.repr_spec hwf.fwok hc).1
          rwa [hwf.fwlen] at h2
        rw [hwf₁.fwlen]
        exact Nat.lt_of_lt_of_le h1 hl
      rw [Heap.repr_push hwf₁.fwok n hrcl, Heap.repr_push hwf₁.fwok n hcl]
      exact ih
  | redirect hs hok hb horig himg ih =>
      rename_i h₁ s d
      have hwf₁ : HeapWf h₁ := HSteps_wf hs hwf
      have hl := HSteps_len hs
      have hcl : c < h₁.fw.length := by
        have hc' : c < h.ns.length := by rw [← hwf.fwlen]; exact hc
        rw [hwf₁.fwlen]
        exact Nat.lt_of_lt_of_le hc' hl
      have hrcl : h.repr c < h₁.fw.length := by
        have h1 : h.repr c < h.ns.length := by
          have h2 := (h.repr_spec hwf.fwok hc).1
          rwa [hwf.fwlen] at h2
        rw [hwf₁.fwlen]
        exact Nat.lt_of_lt_of_le h1 hl
      rw [Heap.repr_redirect hwf₁.fwok hok.1 hok.2.1 hok.2.2.1 hrcl,
          Heap.repr_redirect hwf₁.fwok hok.1 hok.2.1 hok.2.2.1 hcl, ih]

/-- Old nodes are untouched across a fragment: `push` appends,
    `redirect` keeps `ns`. -/
theorem HSteps_ns_prefix {h₀ : Heap} {top : Nat}
    {h h₂ : Heap} (hs : HSteps h₀ top h h₂)
    {i : Nat} (hi : i < h.len) : h₂.ns[i]? = h.ns[i]? := by
  induction hs with
  | refl => rfl
  | push n hs hn ih =>
      rename_i h₁
      have e : (h₁.push n).ns[i]? = h₁.ns[i]? := by
        show (h₁.ns ++ [n])[i]? = h₁.ns[i]?
        exact List.getElem?_append_left (Nat.lt_of_lt_of_le hi (HSteps_len hs))
      rw [e, ih]
  | redirect hs hok hb horig himg ih =>
      rename_i h₁ s d
      show h₁.ns[i]? = h.ns[i]?
      exact ih

/-- Ancestor lift across a fragment: a post-fragment `RSub` path into
    `j` either resolves to an `h`-child unchanged (`RSub h k j` — the
    whole last link was already an `h`-link), or lands `k` below the
    post-fragment image of some `h`-child `x` of `j` — `RSub h x j`
    for the source position, `k = h₂.repr x` or `RSub h₂ k x` for the
    descent.  Requires `j`'s rep to be stable across the fragment. -/
theorem HSteps_rsub_lift {h₀ h h₂ : Heap} {top : Nat}
    (hwf : HeapWf h) (hwf₂ : HeapWf h₂)
    (hs : HSteps h₀ top h h₂) {j k : Nat}
    (hj : j < h.len) (hstab : h₂.repr j = h.repr j)
    (hsub : RSub h₂ k j) :
    RSub h k j ∨ ∃ x, RSub h x j ∧ (k = h₂.repr x ∨ RSub h₂ k x) := by
  have hjf : j < h.fw.length := by rw [hwf.fwlen]; exact hj
  have hplt : h.repr j < h.len := by
    have h2 := (h.repr_spec hwf.fwok hjf).1
    rwa [hwf.fwlen] at h2
  cases hsub with
  | single hc =>
      obtain ⟨l, r, hns, hjl⟩ := hc
      rw [hstab, HSteps_ns_prefix hs hplt] at hns
      obtain ⟨hli, hri⟩ := hwf.dagwf _ hplt l r
        (List.getElem?_eq_some_iff.mp hns).2
      rcases hjl with hjl | hjl
      next =>
        by_cases hch : h₂.repr l = h.repr l
        next =>
          left
          exact TransGen.single ⟨l, r, hns, Or.inl (hch ▸ hjl)⟩
        next =>
          right
          refine ⟨h.repr l, TransGen.single ⟨l, r, hns, Or.inl rfl⟩, Or.inl ?_⟩
          rw [← hjl]
          exact (HSteps_repr_of_repr hwf hs (by
            rw [hwf.fwlen]; exact Nat.lt_trans hli hplt)).symm
      next =>
        by_cases hch : h₂.repr r = h.repr r
        next =>
          left
          exact TransGen.single ⟨l, r, hns, Or.inr (hch ▸ hjl)⟩
        next =>
          right
          refine ⟨h.repr r, TransGen.single ⟨l, r, hns, Or.inr rfl⟩, Or.inl ?_⟩
          rw [← hjl]
          exact (HSteps_repr_of_repr hwf hs (by
            rw [hwf.fwlen]; exact Nat.lt_trans hri hplt)).symm
  | tail hsub hstep =>
      rename_i b
      obtain ⟨l, r, hns, hjl⟩ := hstep
      rw [hstab, HSteps_ns_prefix hs hplt] at hns
      obtain ⟨hli, hri⟩ := hwf.dagwf _ hplt l r
        (List.getElem?_eq_some_iff.mp hns).2
      rcases hjl with hjl | hjl
      next =>
        right
        refine ⟨h.repr l, TransGen.single ⟨l, r, hns, Or.inl rfl⟩, Or.inr ?_⟩
        have e : h₂.repr (h.repr l) = h₂.repr l :=
          HSteps_repr_of_repr hwf hs (by
            rw [hwf.fwlen]; exact Nat.lt_trans hli hplt)
        have hsub' : RSub h₂ k (h₂.repr (h.repr l)) := by
          rw [e, hjl]; exact hsub
        exact (RSub_repr hwf₂).mpr hsub'
      next =>
        right
        refine ⟨h.repr r, TransGen.single ⟨l, r, hns, Or.inr rfl⟩, Or.inr ?_⟩
        have e : h₂.repr (h.repr r) = h₂.repr r :=
          HSteps_repr_of_repr hwf hs (by
            rw [hwf.fwlen]; exact Nat.lt_trans hri hplt)
        have hsub' : RSub h₂ k (h₂.repr (h.repr r)) := by
          rw [e, hjl]; exact hsub
        exact (RSub_repr hwf₂).mpr hsub'

/-- One redirect step preserves old-descendant containment: a path in
    the post-redirect heap decomposes (`RSub_redirect`) into an old
    path or a teleport through `dst`, and `hb` folds the teleport's
    old cone back below `src`. -/
theorem oldSub_redirect_step {h₀ h₁ : Heap} (hwf₁ : HeapWf h₁)
    {s d i k : Nat} (hok : RedirectOk h₁ s d)
    (hb : ∀ k' < h₀.len, (k' = d ∨ RSub h₁ k' d) → RSub h₁ k' s)
    (hk : k < h₀.len)
    (hsub : RSub (h₁.redirect s d) k i) :
    RSub h₁ k i := by
  obtain ⟨c, _hcrep, hcjk, hchain⟩ :=
    RSub_redirect hwf₁ hok.1 hok.2.1 hok.2.2.1 hsub
  -- Normalise a path to the post-redirect endpoint of `i` back
  -- into an `h₁`-path to `i`.
  have norm_end : ∀ {m : Nat}, m < h₀.len →
      RSub h₁ m (if h₁.repr i = s then d else h₁.repr i) →
      RSub h₁ m i := by
    intro m hm hme
    by_cases hrep : h₁.repr i = s
    next =>
      rw [if_pos hrep] at hme
      have hms := hb m hm (Or.inr hme)
      rw [← hrep] at hms
      exact (RSub_repr hwf₁).mpr hms
    next =>
      rw [if_neg hrep] at hme
      exact (RSub_repr hwf₁).mpr hme
  rcases hcjk with ⟨hck, -⟩ | ⟨hcs, hkd⟩
  next =>
    subst c
    rcases hchain with hce | ⟨hcd, hse⟩
    next =>
      exact norm_end hk hce
    next =>
      have hks := hb _ hk (Or.inr hcd)
      by_cases hrep : h₁.repr i = s
      next =>
        rw [← hrep] at hks
        exact (RSub_repr hwf₁).mpr hks
      next =>
        rw [if_neg hrep] at hse
        exact TransGen.trans hks ((RSub_repr hwf₁).mpr hse)
  next =>
    -- `c = s` and `k = d`: the endpoint normalises through the
    -- teleport; `hb` at `k = d` lands the path below `s`.
    subst c
    subst k
    have hds : RSub h₁ d s := hb _ hk (Or.inl rfl)
    rcases hchain with hce | ⟨hcd, -⟩
    next =>
      have hsi : RSub h₁ s i := by
        by_cases hrep : h₁.repr i = s
        next =>
          rw [if_pos hrep] at hce
          exact absurd (TransGen.trans hce hds) (hwf₁.acyc s)
        next =>
          rw [if_neg hrep] at hce
          exact (RSub_repr hwf₁).mpr hce
      exact TransGen.trans hds hsi
    next =>
      exact absurd (TransGen.trans hcd hds) (hwf₁.acyc s)

/-- Old-descendant containment across a fragment — the core measure
    lemma.  Every old node that sits below `i` after the fragment ran
    was already below `i` in the start heap: pushes can't introduce
    old paths (`RSub_push`), and a redirect-created path either
    existed before or teleports through `dst`, whose old cone is
    contained in `src`'s by the `hb` obligation. -/
theorem HSteps_oldSub {h₀ h h₂ : Heap} {top : Nat}
    (hwf : HeapWf h)
    (hs : HSteps h₀ top h h₂) {i k : Nat}
    (hi : i < h.len) (hk : k < h₀.len)
    (hsub : RSub h₂ k i) :
    RSub h k i := by
  induction hs generalizing i k with
  | refl => exact hsub
  | push n hs hn ih =>
      rename_i h₁
      have hwf₁ := HSteps_wf hs hwf
      have hi₁ : i < h₁.len := Nat.lt_of_lt_of_le hi (HSteps_len hs)
      exact ih hi hk ((RSub_push hwf₁ hn hi₁).mp hsub)
  | redirect hs hok hb horig himg ih =>
      rename_i h₁
      have hwf₁ := HSteps_wf hs hwf
      exact ih hi hk (oldSub_redirect_step hwf₁ hok hb hk hsub)

/-- The source of a resolved-descendant path is a rep. -/
theorem RSub_isRep {h : Heap} (hwf : HeapWf h) {k i : Nat}
    (hsub : RSub h k i) : h.repr k = k := by
  induction hsub with
  | single hc => exact RChild_isRep hwf hc
  | tail hsub _ ih => exact ih

/-- Decompose a resolved-descendant path at the endpoint's node: the
    last link resolves through one of the two children. -/
theorem RSub_decomp {h : Heap} {k i : Nat} (hsub : RSub h k i)
    {l r : Nat} (hnode : h.ns[h.repr i]? = some (GNode.app l r)) :
    k = h.repr l ∨ k = h.repr r ∨
      RSub h k (h.repr l) ∨ RSub h k (h.repr r) := by
  cases hsub with
  | single hc =>
      obtain ⟨l', r', hns, hjl⟩ := hc
      rw [hnode] at hns
      obtain ⟨hll, hrr⟩ := GNode.app.inj (Option.some.inj hns)
      subst hrr; subst hll
      rcases hjl with hjl | hjl
      next => exact Or.inl hjl.symm
      next => exact Or.inr (Or.inl hjl.symm)
  | tail hsub hstep =>
      obtain ⟨l', r', hns, hjl⟩ := hstep
      rw [hnode] at hns
      obtain ⟨hll, hrr⟩ := GNode.app.inj (Option.some.inj hns)
      subst hrr; subst hll
      rcases hjl with hjl | hjl
      next =>
        rw [← hjl] at hsub
        exact Or.inr (Or.inr (Or.inl hsub))
      next =>
        rw [← hjl] at hsub
        exact Or.inr (Or.inr (Or.inr hsub))

/-- A resolved-child link survives `redirect s d` when the child value
    is not `s` and the parent's representative is not `s`. -/
theorem RChild_lift_neq {h : Heap} (hwf : HeapWf h) {s d j p : Nat}
    (hsrc : h.fw[s]? = some none) (hdst : h.fw[d]? = some none)
    (hne : s ≠ d) (hc : RChild h j p) (hjs : j ≠ s)
    (hps : h.repr p ≠ s) :
    RChild (h.redirect s d) j p := by
  have hplt : p < h.fw.length := by
    rw [hwf.fwlen]; exact RChild_parent_lt hwf.fwlen hc
  obtain ⟨l, r, hns_node, hjl⟩ := hc
  have hpi : (h.redirect s d).repr p = h.repr p := by
    rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hplt, if_neg hps]
  have hilt : h.repr p < h.len :=
    (List.getElem?_eq_some_iff.mp hns_node).1
  refine ⟨l, r, ?_, ?_⟩
  next =>
    show (h.redirect s d).ns[(h.redirect s d).repr p]? = _
    rw [show (h.redirect s d).ns = h.ns from rfl, hpi]
    exact hns_node
  next =>
    rcases hjl with hjl | hjl
    next =>
      left
      rw [← hjl]
      have hfl : l < h.fw.length := by
        rw [hwf.fwlen]
        obtain ⟨hli, -⟩ := hwf.dagwf _ hilt l r
          (List.getElem?_eq_some_iff.mp hns_node).2
        exact Nat.lt_trans hli hilt
      rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hfl,
          if_neg (by rwa [← hjl] at hjs)]
    next =>
      right
      rw [← hjl]
      have hfr : r < h.fw.length := by
        rw [hwf.fwlen]
        obtain ⟨-, hri⟩ := hwf.dagwf _ hilt l r
          (List.getElem?_eq_some_iff.mp hns_node).2
        exact Nat.lt_trans hri hilt
      rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hfr,
          if_neg (by rwa [← hjl] at hjs)]

/-- A resolved-descendant path whose elements never hit `s` survives
    `redirect s d` verbatim: every link's parent rep and child value
    stay fixed, since a parent resolving to `s` would put `s` on the
    path (giving `RSub h a s`) and a child equal to `s` likewise. -/
theorem RSub_lift_neq {h : Heap} (hwf : HeapWf h) {s d a i : Nat}
    (hsrc : h.fw[s]? = some none) (hdst : h.fw[d]? = some none)
    (hne : s ≠ d) (has : a ≠ s) (hsub : RSub h a i)
    (hi : h.repr i ≠ s) (hns : ¬ RSub h a s) :
    RSub (h.redirect s d) a i := by
  refine TransGen.rec (motive := fun i _ =>
      h.repr i ≠ s → RSub (h.redirect s d) a i) ?_ ?_ hsub hi
  next =>
    intro i hc hi
    exact TransGen.single
      (RChild_lift_neq hwf hsrc hdst hne hc has hi)
  next =>
    intro b i hab hbc ih hi
    have hbs : h.repr b ≠ s := by
      intro e
      have e' := (RSub_repr hwf).mp hab
      rw [e] at e'
      exact hns e'
    have hbi : b ≠ s := by
      intro e; subst e; exact hns hab
    exact TransGen.tail (ih hbs)
      (RChild_lift_neq hwf hsrc hdst hne hbc hbi hi)

/-- A path out of the redirect source reroutes to start at `dst`:
    the first link's child was `s`, becomes `d`; all later links are
    unchanged since no path element can be `s` (that would cycle). -/
theorem RSub_redirect_anc {h : Heap} (hwf : HeapWf h) {s d i : Nat}
    (hsrc : h.fw[s]? = some none) (hdst : h.fw[d]? = some none)
    (hne : s ≠ d) (hsub : RSub h s i) :
    RSub (h.redirect s d) d i := by
  have hkey : ∀ {i' : Nat}, RSub h s i' → h.repr i' ≠ s := by
    intro i' hi' e
    have e' : RSub h s s := by
      have := (RSub_repr hwf).mp hi'
      rwa [e] at this
    exact hwf.acyc s e'
  refine TransGen.rec (motive := fun b _ =>
      RSub (h.redirect s d) d b) ?_ ?_ hsub
  next =>
    intro b hc
    have hsg := TransGen.single hc
    have hilt : b < h.fw.length := by
      rw [hwf.fwlen]; exact RChild_parent_lt hwf.fwlen hc
    obtain ⟨l, r, hns_node, hjl⟩ := hc
    have hpi : (h.redirect s d).repr b = h.repr b := by
      rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hilt,
          if_neg (hkey hsg)]
    have hplt : h.repr b < h.len :=
      (List.getElem?_eq_some_iff.mp hns_node).1
    refine TransGen.single ⟨l, r, ?_, ?_⟩
    next =>
      show (h.redirect s d).ns[(h.redirect s d).repr b]? = _
      rw [show (h.redirect s d).ns = h.ns from rfl, hpi]
      exact hns_node
    next =>
      rcases hjl with hjl | hjl
      next =>
        left
        have hfl : l < h.fw.length := by
          rw [hwf.fwlen]
          obtain ⟨hli, -⟩ := hwf.dagwf _ hplt l r
            (List.getElem?_eq_some_iff.mp hns_node).2
          exact Nat.lt_trans hli hplt
        rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hfl, hjl,
            if_pos rfl]
      next =>
        right
        have hfr : r < h.fw.length := by
          rw [hwf.fwlen]
          obtain ⟨-, hri⟩ := hwf.dagwf _ hplt l r
            (List.getElem?_eq_some_iff.mp hns_node).2
          exact Nat.lt_trans hri hplt
        rw [Heap.repr_redirect hwf.fwok hsrc hdst hne hfr, hjl,
            if_pos rfl]
  next =>
    intro b c hab hbc ih
    have hbm : b ≠ s := by
      intro e; subst e; exact hwf.acyc _ hab
    exact TransGen.tail ih
      (RChild_lift_neq hwf hsrc hdst hne hbc hbm
        (hkey (TransGen.tail hab hbc)))

/-- The image-map invariant: every watched node's image stays inside
    the image of `top`.  At a redirect step, either the image is the
    source itself (it becomes `dst`, which sits at-or-below `top`'s
    image by `horig` + `RSub_redirect_anc`), or the path to `top`'s
    image passes through the source (`himg` folds it into `dst`), or
    it avoids the source entirely (`RSub_lift_neq` keeps it). -/
theorem HSteps_img {h₀ : Heap} {top : Nat}
    {h h₂ : Heap} (hwf : HeapWf h) (h0l : h₀.len ≤ h.len)
    (hs : HSteps h₀ top h h₂)
    {x : Nat} (hx0 : x < h₀.len) (ht : top < h.fw.length)
    (hsub : RSub h (h.repr x) top) :
    h₂.repr x = h₂.repr top ∨ RSub h₂ (h₂.repr x) (h₂.repr top) := by
  have hxlt : x < h.fw.length := by
    rw [hwf.fwlen]; exact Nat.lt_of_lt_of_le hx0 h0l
  induction hs with
  | refl => exact Or.inr ((RSub_repr hwf).mp hsub)
  | push n hs hn ih =>
      rename_i h₁
      have hwf₁ : HeapWf h₁ := HSteps_wf hs hwf
      have hl : h.len ≤ h₁.len := HSteps_len hs
      have hx₁ : x < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact hxlt) hl
      have ht₁ : top < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact ht) hl
      have hrlt : h.repr x < h.fw.length :=
        (h.repr_spec hwf.fwok hxlt).1
      have hrlt₁ : h.repr x < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact hrlt) hl
      have hplt : h.repr top < h.fw.length :=
        (h.repr_spec hwf.fwok ht).1
      have hplt₁ : h.repr top < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact hplt) hl
      have hrlt₂ : h₁.repr x < h₁.fw.length :=
        (h₁.repr_spec hwf₁.fwok hx₁).1
      have hplt₂ : h₁.repr top < h₁.fw.length :=
        (h₁.repr_spec hwf₁.fwok ht₁).1
      have e1 : (h₁.push n).repr x = h₁.repr x :=
        Heap.repr_push hwf₁.fwok n hx₁
      have e2 : (h₁.push n).repr top = h₁.repr top :=
        Heap.repr_push hwf₁.fwok n ht₁
      rcases ih with heq | hsub₁
      next => exact Or.inl (by rw [e1, e2, heq])
      next =>
        right
        rw [e1, e2]
        exact (RSub_push hwf₁ hn (by
          rw [Heap.len_eq, ← hwf₁.fwlen]; exact hplt₂)).mpr hsub₁
  | redirect hs hok hb horig himg ih =>
      rename_i h₁ s d
      have hwf₁ : HeapWf h₁ := HSteps_wf hs hwf
      have hl : h.len ≤ h₁.len := HSteps_len hs
      have hx₁ : x < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact hxlt) hl
      have ht₁ : top < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact ht) hl
      have hrX : (h₁.redirect s d).repr x =
          if h₁.repr x = s then d else h₁.repr x :=
        Heap.repr_redirect hwf₁.fwok hok.1 hok.2.1 hok.2.2.1 hx₁
      have hrT : (h₁.redirect s d).repr top =
          if h₁.repr top = s then d else h₁.repr top :=
        Heap.repr_redirect hwf₁.fwok hok.1 hok.2.1 hok.2.2.1 ht₁
      by_cases hts : h₁.repr top = s
      next =>
        rw [hrT, if_pos hts]
        rcases ih with heq | hsub₁
        next =>
          left
          rw [hrX, if_pos (by rw [heq, hts])]
        next =>
          have hxs : RSub h₁ (h₁.repr x) s := by rwa [hts] at hsub₁
          rcases himg x hx0 hxs with hxd | hxd
          next => exact Or.inl hxd
          next => exact Or.inr hxd
      next =>
        rw [hrT, if_neg hts]
        rcases ih with heq | hsub₁
        next =>
          left
          rw [hrX, if_neg (by rw [heq]; exact hts), heq]
        next =>
          by_cases hxs : RSub h₁ (h₁.repr x) s
          next =>
            rcases himg x hx0 hxs with hxd | hxd
            next =>
              right
              rw [hxd]
              rcases horig with horig | horig
              next =>
                exact RSub_redirect_anc hwf₁ hok.1 hok.2.1
                  hok.2.2.1 horig
              next => exact absurd horig hts
            next =>
              right
              rcases horig with horig | horig
              next =>
                exact TransGen.trans hxd
                  (RSub_redirect_anc hwf₁ hok.1 hok.2.1
                    hok.2.2.1 horig)
              next => exact absurd horig hts
          next =>
            by_cases hxeq : h₁.repr x = s
            next =>
              right
              rw [hrX, if_pos hxeq]
              rcases horig with horig | horig
              next =>
                exact RSub_redirect_anc hwf₁ hok.1 hok.2.1
                  hok.2.2.1 horig
              next => exact absurd horig hts
            next =>
              right
              rw [hrX, if_neg hxeq]
              have hrep : h₁.repr (h₁.repr top) = h₁.repr top :=
                Heap.repr_idem hwf₁.fwok ht₁
              exact RSub_lift_neq hwf₁ hok.1 hok.2.1 hok.2.2.1
                hxeq hsub₁ (by rw [hrep]; exact hts) hxs

/-- A rep that is still a rep at the end of a fragment was never a
    redirect source inside it, so the resolution is unchanged. -/
theorem HSteps_repr_stay {h₀ : Heap} {top : Nat}
    {h h₂ : Heap} (hwf : HeapWf h) (hs : HSteps h₀ top h h₂)
    {i : Nat} (hi : i < h.fw.length)
    (hrep : h₂.fw[h.repr i]? = some none) :
    h₂.repr i = h.repr i := by
  induction hs with
  | refl => rfl
  | push n hs hn ih =>
      rename_i h₁
      have hwf₁ : HeapWf h₁ := HSteps_wf hs hwf
      have hl : h.len ≤ h₁.len := HSteps_len hs
      have hifw : i < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact hi) hl
      have hrfw : h.repr i < h₁.fw.length := by
        rw [hwf₁.fwlen]
        have hrlt : h.repr i < h.fw.length := (h.repr_spec hwf.fwok hi).1
        rw [hwf.fwlen] at hrlt
        exact Nat.lt_of_lt_of_le hrlt hl
      have e : (h₁.push n).fw[h.repr i]? = h₁.fw[h.repr i]? := by
        show (h₁.fw ++ [none])[h.repr i]? = _
        exact List.getElem?_append_left hrfw
      rw [e] at hrep
      rw [Heap.repr_push hwf₁.fwok n hifw]
      exact ih hrep
  | redirect hs hok hb horig himg ih =>
      rename_i h₁ s d
      have hwf₁ : HeapWf h₁ := HSteps_wf hs hwf
      have hl : h.len ≤ h₁.len := HSteps_len hs
      have hifw : i < h₁.fw.length := by
        rw [hwf₁.fwlen]; exact Nat.lt_of_lt_of_le
          (by rw [Heap.len_eq, ← hwf.fwlen]; exact hi) hl
      have hrfw : h.repr i < h₁.fw.length := by
        rw [hwf₁.fwlen]
        have hrlt : h.repr i < h.fw.length := (h.repr_spec hwf.fwok hi).1
        rw [hwf.fwlen] at hrlt
        exact Nat.lt_of_lt_of_le hrlt hl
      have hslt : s < h₁.fw.length :=
        (List.getElem?_eq_some_iff.mp hok.1).1
      have hne2 : h.repr i ≠ s := by
        intro e
        have heq : (h₁.redirect s d).fw[h.repr i]? = some (some d) := by
          show (h₁.fw.set s (some d))[h.repr i]? = some (some d)
          rw [e]; exact List.getElem?_set_self hslt
        rw [heq] at hrep; simp at hrep
      have e : (h₁.redirect s d).fw[h.repr i]? = h₁.fw[h.repr i]? := by
        show (h₁.fw.set s (some d))[h.repr i]? = _
        exact List.getElem?_set_ne (Ne.symm hne2)
      rw [e] at hrep
      have hri : h₁.repr i = h.repr i := ih hrep
      rw [Heap.repr_redirect hwf₁.fwok hok.1 hok.2.1 hok.2.2.1 hifw]
      rw [hri, if_neg hne2]

/-- Weaken the `top` marker: a fragment developing `r` is also a
    fragment developing `t` when `r`'s rep is below `t` and `r` is
    watched — the per-step `horig` obligation follows from the
    image invariant applied to the weakened prefix. -/
theorem HSteps.weaken {h₀ : Heap} {top r : Nat}
    {h h' : Heap} (hwf : HeapWf h) (h0l : h₀.len ≤ h.len)
    (hrlt0 : r < h₀.len) (htlt : top < h.fw.length)
    (hs : HSteps h₀ r h h')
    (hrt : RSub h (h.repr r) top) :
    HSteps h₀ top h h' := by
  induction hs with
  | refl => exact HSteps.refl _
  | push n hs hn ih => exact HSteps.push n ih hn
  | redirect hs hok hb horig himg ih =>
      rename_i h₁ s d
      refine HSteps.redirect ih hok hb ?_ himg
      have himg' := HSteps_img hwf h0l ih hrlt0 htlt hrt
      rcases himg' with heq | hsub
      next =>
        rcases horig with horig | horig
        next => exact Or.inl (by rw [heq] at horig; exact horig)
        next => exact Or.inr (heq ▸ horig)
      next =>
        rcases horig with horig | horig
        next => exact Or.inl (TransGen.trans horig hsub)
        next => exact Or.inl (horig ▸ hsub)

end ISAR
