import ISAR.BasisDev

/-!
# GraphDev — dag refinement of basis-level complete development

The host `graph_runtime.Graph` is a hash-consed dag with `fwd`
redirects; its `cd` pass is the executor whose `rounds=` count every
native cd routine reports.  This file proves that executor computes the
*basis-level* complete development of `BasisDev.lean`.

Model (deliberately raw — `DagWf` is a hypothesis, not a bundled field,
so growth needs no repacking):

* `GNode`/`GAtom` — node table entries (no `sₛ`: the host rejects it at
  import; the dag's image is the `sₛ`-free fragment, consistent with
  `cdBasis` treating `sₛ` as inert).
* `dagTerms`/`dagUnfold` — readback to `ITerm`.  `dagTerms` is a left
  fold over the node table (children point into the already-built
  prefix, so no well-founded recursion anywhere); `dagUnfold` is a
  `getD` lookup — total, no `Fin`, no bound proofs in terms.
* `DevRel` — inductive spec of the host `Graph.cd` pass, one constructor
  per clause, `getElem?`-premised (no bounds in the data).
* `DevRel_sound` — developments unfold to `cdBasis`; determinism free.
* `DevRel_total` — a development always exists.
* `DevChain`/`DevChain_unfold` — the host's `rounds=N` is a `cdBasis`
  iteration count, hence `IRedBasis`-reachable.

Honest bound: sharing and `fwd` redirects are quotiented away —
`unfold` sees only the term; they are an optimization layer the
semantics never notices.
-/

namespace ISAR

/-- Dag leaf atoms — the basis fragment the host heap stores. -/
inductive GAtom where
  | norm | konst | dup | swap | comp
  deriving DecidableEq, Repr

def GAtom.toTerm : GAtom → ITerm
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp

/-- Node table entry: leaf or application with child ids. -/
inductive GNode where
  | atom (a : GAtom)
  | var (n : Nat)
  | app (l r : Nat)
  deriving DecidableEq, Repr

/-- One node read against the already-built prefix.  The `getD`
    defaults are dead code under `DagWf` (children < index). -/
def stepNode (acc : List ITerm) : GNode → ITerm
  | .atom a => a.toTerm
  | .var n => .var n
  | .app l r => .app (acc.getD l (.var 0)) (acc.getD r (.var 0))

/-- Children-before-parents invariant. -/
def DagWf (ns : List GNode) : Prop :=
  ∀ (i : Nat) (hi : i < ns.length) (l r : Nat),
    ns[i] = .app l r → l < i ∧ r < i

/-- Readback list: term of node `i` is `(dagTerms ns)[i]`. -/
def dagTerms (ns : List GNode) : List ITerm :=
  ns.foldl (fun acc n => acc ++ [stepNode acc n]) []

theorem dagTerms_go_length (acc : List ITerm) (ns : List GNode) :
    (ns.foldl (fun acc n => acc ++ [stepNode acc n]) acc).length =
      acc.length + ns.length := by
  induction ns generalizing acc with
  | nil => simp
  | cons n ns ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp
      omega

theorem dagTerms_length (ns : List GNode) :
    (dagTerms ns).length = ns.length := by
  unfold dagTerms
  rw [dagTerms_go_length]
  simp

/-- Readback of node `i`: the tree it means.  Total on `Nat`; the
    default is dead code at in-range indices. -/
def dagUnfold (ns : List GNode) (i : Nat) : ITerm :=
  (dagTerms ns).getD i (.var 0)

/-- A singleton append contributes exactly its own `stepNode`. -/
theorem dagTerms_snoc (ns : List GNode) (n : GNode) :
    dagTerms (ns ++ [n]) = dagTerms ns ++ [stepNode (dagTerms ns) n] := by
  unfold dagTerms
  rw [List.foldl_append]
  simp [List.foldl_cons, List.foldl_nil]

/-- Growth preserves the prefix's terms. -/
theorem dagTerms_append (ns e : List GNode) :
    ∃ tl, dagTerms (ns ++ e) = dagTerms ns ++ tl := by
  induction e generalizing ns with
  | nil => exact ⟨[], by simp⟩
  | cons n e ih =>
      have h : ns ++ n :: e = (ns ++ [n]) ++ e := by simp
      rw [h]
      obtain ⟨tl, htl⟩ := ih (ns ++ [n])
      rw [htl, dagTerms_snoc]
      exact ⟨stepNode (dagTerms ns) n :: tl, List.append_assoc _ _ _⟩

/-- `dagTerms` decomposes at any in-range index: the term at `i` is
    `stepNode` applied to the prefix's terms. -/
theorem dagTerms_at (ns : List GNode) (i : Nat) (hi : i < ns.length) :
    ∃ tl, dagTerms ns =
      dagTerms (ns.take i) ++ stepNode (dagTerms (ns.take i)) ns[i] :: tl := by
  have hsplit : ns = ns.take i ++ ns[i] :: ns.drop (i + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have e := congrArg dagTerms hsplit
  have h : ns.take i ++ ns[i] :: ns.drop (i + 1) =
      (ns.take i ++ [ns[i]]) ++ ns.drop (i + 1) := by simp
  rw [e, h]
  obtain ⟨tl, htl⟩ := dagTerms_append (ns.take i ++ [ns[i]]) (ns.drop (i + 1))
  rw [htl, dagTerms_snoc]
  exact ⟨tl, List.append_assoc _ _ _⟩

/-- Prefix terms are the prefix of terms. -/
theorem dagTerms_take (ns : List GNode) (i : Nat) (hi : i ≤ ns.length) :
    dagTerms (ns.take i) = (dagTerms ns).take i := by
  have hlen : (dagTerms (ns.take i)).length = i := by
    rw [dagTerms_length, List.length_take]; omega
  have e := congrArg dagTerms (List.take_append_drop i ns).symm
  obtain ⟨tl, htl⟩ := dagTerms_append (ns.take i) (ns.drop i)
  have e2 : (dagTerms ns).take i = dagTerms (ns.take i) := by
    rw [e, htl, List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
        List.take_of_length_le (Nat.le_of_eq hlen)]
  exact e2.symm

/-- Readback is stable under growth (in-range indices). -/
theorem dagUnfold_stable {ns : List GNode} (e : List GNode) {i : Nat}
    (hi : i < ns.length) :
    dagUnfold (ns ++ e) i = dagUnfold ns i := by
  obtain ⟨tl, htl⟩ := dagTerms_append ns e
  unfold dagUnfold
  rw [htl]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  congr 1
  rw [List.getElem?_append_left (by rw [dagTerms_length]; exact hi)]

/-- Node `i` unfolds to its `stepNode` applied to the prefix terms. -/
theorem dagUnfold_node (ns : List GNode) (i : Nat) (hi : i < ns.length) :
    dagUnfold ns i = stepNode (dagTerms (ns.take i)) ns[i] := by
  obtain ⟨tl, htl⟩ := dagTerms_at ns i hi
  unfold dagUnfold
  rw [htl, List.getD_eq_getElem?_getD]
  have hlen : (dagTerms (ns.take i)).length = i := by
    rw [dagTerms_length, List.length_take]; omega
  rw [List.getElem?_append_right (Nat.le_of_eq hlen), hlen, Nat.sub_self]
  rfl

/-- Small-index readback agrees in a prefix and the whole. -/
theorem dagUnfold_lt (ns : List GNode) {i j : Nat}
    (hi : i ≤ ns.length) (hj : j < i) :
    dagUnfold (ns.take i) j = dagUnfold ns j := by
  unfold dagUnfold
  rw [dagTerms_take ns i hi, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD]
  congr 1
  rw [List.getElem?_take, if_pos hj]

/-- Node-shape equations — the interface `DevRel_sound` uses. -/
theorem dagUnfold_atom {ns : List GNode} {i : Nat} {a : GAtom}
    (hi : i < ns.length) (h : ns[i] = .atom a) :
    dagUnfold ns i = a.toTerm := by
  rw [dagUnfold_node ns i hi, h]
  rfl

theorem dagUnfold_var {ns : List GNode} {i n : Nat}
    (hi : i < ns.length) (h : ns[i] = .var n) :
    dagUnfold ns i = .var n := by
  rw [dagUnfold_node ns i hi, h]
  rfl

theorem dagUnfold_app {ns : List GNode} (hwf : DagWf ns)
    {i l r : Nat} (hi : i < ns.length) (h : ns[i] = .app l r) :
    dagUnfold ns i = .app (dagUnfold ns l) (dagUnfold ns r) := by
  rw [dagUnfold_node ns i hi, h]
  simp only [stepNode]
  have hl : l < i := (hwf i hi l r h).1
  have hr : r < i := (hwf i hi l r h).2
  have hle : i ≤ ns.length := Nat.le_of_lt hi
  rw [← dagUnfold_lt ns hle hl, ← dagUnfold_lt ns hle hr]
  rfl

/-- The host's redex-head check on node `i`: does node `i` sit atop a
    `norm`/`konst`/`dup`/`comp`/`swap` redex spine?  Mirrors the nested
    `fk/flk/fllk` dispatch in `Graph.cd`. -/
def isRedexNode (ns : List GNode) (i : Nat) : Bool :=
  match ns[i]? with
  | some (.app l _) =>
      match ns[l]? with
      | some (.atom .norm) => true
      | some (.app kl _) =>
          match ns[kl]? with
          | some (.atom .konst) | some (.atom .dup) => true
          | some (.app kll _) =>
              match ns[kll]? with
              | some (.atom .comp) | some (.atom .swap) => true
              | _ => false
          | _ => false
      | _ => false
  | _ => false

/-- Term-level redex head: the left child shapes that make `cdBasis`
    fire on `.app A _`. -/
def isRedexHead : ITerm → Bool
  | .norm => true
  | .app .konst _ | .app .dup _ => true
  | .app (.app .comp _) _ | .app (.app .swap _) _ => true
  | _ => false

/-- `cdBasis` at a non-redex application falls through to congruence. -/
theorem cdBasis_app_generic {A B : ITerm} (h : isRedexHead A = false) :
    cdBasis (.app A B) = .app (cdBasis A) (cdBasis B) := by
  cases A with
  | norm => simp [isRedexHead] at h
  | app a b =>
      cases a with
      | konst | dup => simp [isRedexHead] at h
      | app c d =>
          cases c with
          | comp | swap => simp [isRedexHead] at h
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- Node-level redex check unfolds to the term-level check. -/
theorem dagUnfold_isRedexHead {ns : List GNode} (hwf : DagWf ns)
    {i l r : Nat} (hi : i < ns.length) (hnode : ns[i] = .app l r) :
    isRedexHead (dagUnfold ns l) = isRedexNode ns i := by
  have hl : l < ns.length :=
    Nat.lt_trans (hwf i hi l r hnode).1 hi
  simp only [isRedexNode, List.getElem?_eq_getElem hi, hnode]
  cases hlnode : ns[l] with
  | atom a =>
      rw [dagUnfold_atom hl hlnode]
      simp only [List.getElem?_eq_getElem hl, hlnode]
      cases a <;> rfl
  | var n =>
      rw [dagUnfold_var hl hlnode]
      simp only [List.getElem?_eq_getElem hl, hlnode]
      rfl
  | app kl kr =>
      rw [dagUnfold_app hwf hl hlnode]
      simp only [List.getElem?_eq_getElem hl, hlnode]
      have hkl : kl < ns.length :=
        Nat.lt_trans (hwf l hl kl kr hlnode).1 hl
      cases hklnode : ns[kl] with
      | atom a =>
          rw [dagUnfold_atom hkl hklnode]
          simp only [List.getElem?_eq_getElem hkl, hklnode]
          cases a <;> rfl
      | var n =>
          rw [dagUnfold_var hkl hklnode]
          simp only [List.getElem?_eq_getElem hkl, hklnode]
          rfl
      | app kll klr =>
          rw [dagUnfold_app hwf hkl hklnode]
          simp only [List.getElem?_eq_getElem hkl, hklnode]
          have hkll : kll < ns.length :=
            Nat.lt_trans (hwf kl hkl kll klr hklnode).1 hkl
          cases hkllnode : ns[kll] with
          | atom a =>
              rw [dagUnfold_atom hkll hkllnode]
              simp only [List.getElem?_eq_getElem hkll, hkllnode]
              cases a <;> rfl
          | var n =>
              rw [dagUnfold_var hkll hkllnode]
              simp only [List.getElem?_eq_getElem hkll, hkllnode]
              rfl
          | app a b =>
              rw [dagUnfold_app hwf hkll hkllnode]
              simp only [List.getElem?_eq_getElem hkll, hkllnode]
              rfl

/-- Growing a dag by nodes whose children stay in-bounds preserves
    `DagWf`. -/
theorem DagWf_append {ns e : List GNode} (hwf : DagWf ns)
    (hok : ∀ (k : Nat) (hk : k < e.length) (l r : Nat),
      e[k] = .app l r → l < ns.length + k ∧ r < ns.length + k) :
    DagWf (ns ++ e) := by
  intro i hi l r hnode
  cases Nat.lt_or_ge i ns.length with
  | inl hlt =>
      rw [List.getElem_append_left hlt] at hnode
      exact hwf i hlt l r hnode
  | inr hge =>
      rw [List.getElem_append_right hge] at hnode
      have hk : i - ns.length < e.length := by
        rw [List.length_append] at hi; omega
      obtain ⟨hl', hr'⟩ := hok (i - ns.length) hk l r hnode
      omega

/-- The last node of `ns ++ [n]` unfolds to `stepNode` on the prefix. -/
theorem dagUnfold_snoc (ns : List GNode) (n : GNode) :
    dagUnfold (ns ++ [n]) ns.length = stepNode (dagTerms ns) n := by
  rw [dagUnfold_node (ns ++ [n]) ns.length (by simp)]
  congr 1
  · rw [List.take_left]
  · rw [List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self]
    exact List.getElem_cons_zero n [] (by simp)

/-- Two pushes: the second pushed node unfolds to `stepNode` on the
    once-extended prefix. -/
theorem dagUnfold_snoc2 (ns : List GNode) (a b : GNode) :
    dagUnfold (ns ++ [a, b]) (ns.length + 1) =
      stepNode (dagTerms (ns ++ [a])) b := by
  have h : ns ++ [a, b] = (ns ++ [a]) ++ [b] := by simp
  have hlen : (ns ++ [a]).length = ns.length + 1 := by simp
  rw [h, ← hlen]
  exact dagUnfold_snoc (ns ++ [a]) b

/-- Child lookup inside a `stepNode` at an in-range index is `dagUnfold`. -/
theorem stepNode_getD {ns : List GNode} {a : Nat}
    (ha : a < ns.length) :
    (dagTerms ns).getD a (.var 0) = dagUnfold ns a := by
  unfold dagUnfold
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [dagTerms_length]; exact ha),
      Option.getD_some]

/-- An appended `.app a b` node unfolds to the children's readbacks. -/
theorem dagUnfold_push_app {ns : List GNode} {a b : Nat}
    (ha : a < ns.length) (hb : b < ns.length) :
    dagUnfold (ns ++ [.app a b]) ns.length =
      .app (dagUnfold ns a) (dagUnfold ns b) := by
  rw [dagUnfold_snoc]
  simp only [stepNode]
  rw [stepNode_getD ha, stepNode_getD hb]

/-- The first of two appended nodes unfolds to its children's readbacks
    (stable under the second push). -/
theorem dagUnfold_push2_fst {ns : List GNode} {a b : Nat} (c : GNode)
    (ha : a < ns.length) (hb : b < ns.length) :
    dagUnfold (ns ++ [.app a b, c]) ns.length =
      .app (dagUnfold ns a) (dagUnfold ns b) := by
  have h : ns ++ [.app a b, c] = (ns ++ [.app a b]) ++ [c] := by simp
  rw [h, dagUnfold_stable [c] (by simp)]
  exact dagUnfold_push_app ha hb

/-- The host `Graph.cd` pass, one constructor per clause.  `DevRel ns i
    ns' j`: developing node `i` in `ns` yields node `j` in the grown dag
    `ns'` (new nodes are appended, never mutated — hash-consing and
    `fwd` redirects are quotiented out by `dagUnfold`). -/
inductive DevRel : List GNode → Nat → List GNode → Nat → Prop where
  | atom {ns : List GNode} {i : Nat} {a : GAtom} :
      ns[i]? = some (.atom a) → DevRel ns i ns i
  | var {ns : List GNode} {i n : Nat} :
      ns[i]? = some (.var n) → DevRel ns i ns i
  | norm_red {ns : List GNode} {i l r : Nat} {ns' : List GNode} {j : Nat} :
      ns[i]? = some (.app l r) → ns[l]? = some (.atom .norm) →
      DevRel ns r ns' j → DevRel ns i ns' j
  | konst_red {ns : List GNode} {i l r kl kr : Nat}
      {ns' : List GNode} {j : Nat} :
      ns[i]? = some (.app l r) → ns[l]? = some (.app kl kr) →
      ns[kl]? = some (.atom .konst) →
      DevRel ns kr ns' j → DevRel ns i ns' j
  | dup_red {ns : List GNode} {i l r kl kr : Nat}
      {ns₁ ns₂ : List GNode} {jx jf : Nat} :
      ns[i]? = some (.app l r) → ns[l]? = some (.app kl kr) →
      ns[kl]? = some (.atom .dup) →
      DevRel ns r ns₁ jx → DevRel ns₁ kr ns₂ jf →
      DevRel ns i (ns₂ ++ [.app jf jx, .app ns₂.length jx]) (ns₂.length + 1)
  | comp_red {ns : List GNode} {i l r kl kr kll klr : Nat}
      {ns₁ ns₂ ns₃ : List GNode} {jf jg jx : Nat} :
      ns[i]? = some (.app l r) → ns[l]? = some (.app kl kr) →
      ns[kl]? = some (.app kll klr) → ns[kll]? = some (.atom .comp) →
      DevRel ns klr ns₁ jf → DevRel ns₁ kr ns₂ jg → DevRel ns₂ r ns₃ jx →
      DevRel ns i (ns₃ ++ [.app jg jx, .app jf ns₃.length]) (ns₃.length + 1)
  | swap_red {ns : List GNode} {i l r kl kr kll klr : Nat}
      {ns₁ ns₂ ns₃ : List GNode} {jf jx jy : Nat} :
      ns[i]? = some (.app l r) → ns[l]? = some (.app kl kr) →
      ns[kl]? = some (.app kll klr) → ns[kll]? = some (.atom .swap) →
      DevRel ns klr ns₁ jf → DevRel ns₁ kr ns₂ jx → DevRel ns₂ r ns₃ jy →
      DevRel ns i (ns₃ ++ [.app jf jy, .app ns₃.length jx]) (ns₃.length + 1)
  | app_dev {ns : List GNode} {i l r : Nat} {ns₁ ns₂ : List GNode}
      {jf jx : Nat} :
      ns[i]? = some (.app l r) → isRedexNode ns i = false →
      DevRel ns l ns₁ jf → DevRel ns₁ r ns₂ jx →
      DevRel ns i (ns₂ ++ [.app jf jx]) ns₂.length

/-- Every development extends the dag (append-only). -/
theorem DevRel_extends {ns i ns' j} (h : DevRel ns i ns' j) :
    ∃ tl, ns' = ns ++ tl := by
  induction h with
  | atom _ | var _ => exact ⟨[], (List.append_nil _).symm⟩
  | norm_red _ _ _ ih => exact ih
  | konst_red _ _ _ _ ih => exact ih
  | dup_red a₁ a₂ a₃ hx hf ihx ihf =>
      rename_i ns i l r kl kr ns₁ ns₂ jx jf
      obtain ⟨t₁, e₁⟩ := ihx
      obtain ⟨t₂, e₂⟩ := ihf
      refine ⟨t₁ ++ t₂ ++ [.app jf jx, .app ((ns ++ t₁) ++ t₂).length jx],
        ?_⟩
      rw [e₂, e₁]
      simp only [List.append_assoc]
  | comp_red a₁ a₂ a₃ a₄ hf hg hx ihf ihg ihx =>
      rename_i ns i l r kl kr kll klr ns₁ ns₂ ns₃ jf jg jx
      obtain ⟨t₁, e₁⟩ := ihf
      obtain ⟨t₂, e₂⟩ := ihg
      obtain ⟨t₃, e₃⟩ := ihx
      refine ⟨t₁ ++ t₂ ++ t₃ ++
        [.app jg jx, .app jf (((ns ++ t₁) ++ t₂) ++ t₃).length], ?_⟩
      rw [e₃, e₂, e₁]
      simp only [List.append_assoc]
  | swap_red a₁ a₂ a₃ a₄ hf hx hy ihf ihx ihy =>
      rename_i ns i l r kl kr kll klr ns₁ ns₂ ns₃ jf jx jy
      obtain ⟨t₁, e₁⟩ := ihf
      obtain ⟨t₂, e₂⟩ := ihx
      obtain ⟨t₃, e₃⟩ := ihy
      refine ⟨t₁ ++ t₂ ++ t₃ ++
        [.app jf jy, .app (((ns ++ t₁) ++ t₂) ++ t₃).length jx], ?_⟩
      rw [e₃, e₂, e₁]
      simp only [List.append_assoc]
  | app_dev a₁ a₂ hf hx ihf ihx =>
      rename_i ns i l r ns₁ ns₂ jf jx
      obtain ⟨t₁, e₁⟩ := ihf
      obtain ⟨t₂, e₂⟩ := ihx
      refine ⟨t₁ ++ t₂ ++ [.app jf jx], ?_⟩
      rw [e₂, e₁]
      simp only [List.append_assoc]

/-- A two-node app suffix keeps `DagWf` when children point back. -/
theorem DagWf_push2 {ns : List GNode} (hwf : DagWf ns) {a b c d : Nat}
    (ha : a < ns.length) (hb : b < ns.length)
    (hc : c < ns.length + 1) (hd : d < ns.length + 1) :
    DagWf (ns ++ [.app a b, .app c d]) := by
  refine DagWf_append hwf ?_
  intro k hk l r he
  cases k with
  | zero =>
      simp at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨ha, hb⟩
  | succ k =>
      cases k with
      | zero =>
          simp at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨hc, hd⟩
      | succ k =>
          exact absurd hk (by simp)

/-- A single-node app suffix keeps `DagWf`. -/
theorem DagWf_push1 {ns : List GNode} (hwf : DagWf ns) {a b : Nat}
    (ha : a < ns.length) (hb : b < ns.length) :
    DagWf (ns ++ [.app a b]) := by
  refine DagWf_append hwf ?_
  intro k hk l r he
  cases k with
  | zero =>
      simp at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨ha, hb⟩
  | succ k =>
      exact absurd hk (by simp)

/-- Soundness: any development the executor performs unfolds to
    `cdBasis` of the input — determinism is a corollary. -/
theorem DevRel_sound {ns i ns' j} (h : DevRel ns i ns' j)
    (hwf : DagWf ns) :
    DagWf ns' ∧ j < ns'.length ∧
      dagUnfold ns' j = cdBasis (dagUnfold ns i) := by
  induction h with
  | atom hi' =>
      rename_i ns i a
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      refine ⟨hwf, hi, ?_⟩
      rw [dagUnfold_atom hi hnode]
      cases a <;> rfl
  | var hi' =>
      rename_i ns i n
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      refine ⟨hwf, hi, ?_⟩
      rw [dagUnfold_var hi hnode]
      rfl
  | norm_red hi' hl' hd ih =>
      rename_i ns i l r ns' j
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      obtain ⟨hl, hlnode⟩ := List.getElem?_eq_some_iff.mp hl'
      obtain ⟨w', hj, heq⟩ := ih hwf
      refine ⟨w', hj, ?_⟩
      rw [dagUnfold_app hwf hi hnode, dagUnfold_atom hl hlnode]
      exact heq
  | konst_red hi' hl' hkl' hd ih =>
      rename_i ns i l r kl kr ns' j
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      obtain ⟨hl, hlnode⟩ := List.getElem?_eq_some_iff.mp hl'
      obtain ⟨hkl, hklnode⟩ := List.getElem?_eq_some_iff.mp hkl'
      obtain ⟨w', hj, heq⟩ := ih hwf
      refine ⟨w', hj, ?_⟩
      rw [dagUnfold_app hwf hi hnode, dagUnfold_app hwf hl hlnode,
          dagUnfold_atom hkl hklnode]
      exact heq
  | dup_red hi' hl' hkl' hx hf ihx ihf =>
      rename_i ns i l r kl kr ns₁ ns₂ jx jf
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      obtain ⟨hl, hlnode⟩ := List.getElem?_eq_some_iff.mp hl'
      obtain ⟨hkl, hklnode⟩ := List.getElem?_eq_some_iff.mp hkl'
      obtain ⟨w₁, hjx, heqx⟩ := ihx hwf
      obtain ⟨w₂, hjf, heqf⟩ := ihf w₁
      obtain ⟨t₁, e₁⟩ := DevRel_extends hx
      obtain ⟨t₂, e₂⟩ := DevRel_extends hf
      have hkr : kr < ns.length :=
        Nat.lt_trans (hwf _ hl _ _ hlnode).2
          (Nat.lt_trans (hwf _ hi _ _ hnode).1 hi)
      have hjx₂ : jx < ns₂.length := by
        rw [e₂, List.length_append]; omega
      have hf' : dagUnfold ns₂ jf = cdBasis (dagUnfold ns kr) := by
        rw [heqf, e₁, dagUnfold_stable t₁ hkr]
      have hx' : dagUnfold ns₂ jx = cdBasis (dagUnfold ns r) := by
        rw [e₂, dagUnfold_stable t₂ hjx, heqx]
      refine ⟨DagWf_push2 w₂ hjf hjx₂ (by omega) (by omega), by simp, ?_⟩
      rw [dagUnfold_snoc2]
      simp only [stepNode]
      rw [stepNode_getD (by simp), dagUnfold_push_app hjf hjx₂]
      rw [stepNode_getD (Nat.lt_trans hjx₂ (by simp)),
        dagUnfold_stable [.app jf jx] hjx₂]
      rw [hf', hx']
      rw [dagUnfold_app hwf hi hnode, dagUnfold_app hwf hl hlnode,
          dagUnfold_atom hkl hklnode]
      simp only [GAtom.toTerm, cdBasis]
  | comp_red hi' hl' hkl' hkll' hf hg hx ihf ihg ihx =>
      rename_i ns i l r kl kr kll klr ns₁ ns₂ ns₃ jf jg jx
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      obtain ⟨hl, hlnode⟩ := List.getElem?_eq_some_iff.mp hl'
      obtain ⟨hkl, hklnode⟩ := List.getElem?_eq_some_iff.mp hkl'
      obtain ⟨hkll, hkllnode⟩ := List.getElem?_eq_some_iff.mp hkll'
      obtain ⟨w₁, hjf, heqf⟩ := ihf hwf
      obtain ⟨w₂, hjg, heqg⟩ := ihg w₁
      obtain ⟨w₃, hjx, heqx⟩ := ihx w₂
      obtain ⟨t₁, e₁⟩ := DevRel_extends hf
      obtain ⟨t₂, e₂⟩ := DevRel_extends hg
      obtain ⟨t₃, e₃⟩ := DevRel_extends hx
      have hklr : klr < ns.length :=
        Nat.lt_trans (hwf _ hkl _ _ hklnode).2
          (Nat.lt_trans (hwf _ hl _ _ hlnode).1
            (Nat.lt_trans (hwf _ hi _ _ hnode).1 hi))
      have hkr : kr < ns.length :=
        Nat.lt_trans (hwf _ hl _ _ hlnode).2
          (Nat.lt_trans (hwf _ hi _ _ hnode).1 hi)
      have hri : r < ns.length :=
        Nat.lt_trans (hwf _ hi _ _ hnode).2 hi
      have hr₁ : r < ns₁.length := by
        rw [e₁, List.length_append]; omega
      have hjf₂ : jf < ns₂.length := by
        rw [e₂, List.length_append]; omega
      have hjg₃ : jg < ns₃.length := by
        rw [e₃, List.length_append]; omega
      have hjf₃ : jf < ns₃.length := by
        rw [e₃, e₂, List.length_append, List.length_append]; omega
      have hf' : dagUnfold ns₃ jf = cdBasis (dagUnfold ns klr) := by
        rw [e₃, dagUnfold_stable t₃ hjf₂, e₂, dagUnfold_stable t₂ hjf, heqf]
      have hg' : dagUnfold ns₃ jg = cdBasis (dagUnfold ns kr) := by
        rw [e₃, dagUnfold_stable t₃ hjg, heqg, e₁,
            dagUnfold_stable t₁ hkr]
      have hx' : dagUnfold ns₃ jx = cdBasis (dagUnfold ns r) := by
        rw [heqx, e₂, dagUnfold_stable t₂ hr₁, e₁,
            dagUnfold_stable t₁ hri]
      refine ⟨DagWf_push2 w₃ hjg₃ hjx (by omega) (by omega), by simp, ?_⟩
      rw [dagUnfold_snoc2]
      simp only [stepNode]
      rw [stepNode_getD (Nat.lt_trans hjf₃ (by simp)),
        dagUnfold_stable [.app jg jx] hjf₃]
      rw [stepNode_getD (by simp), dagUnfold_push_app hjg₃ hjx]
      rw [hf', hg', hx']
      rw [dagUnfold_app hwf hi hnode, dagUnfold_app hwf hl hlnode,
          dagUnfold_app hwf hkl hklnode, dagUnfold_atom hkll hkllnode]
      simp only [GAtom.toTerm, cdBasis]
  | swap_red hi' hl' hkl' hkll' hf hx hy ihf ihx ihy =>
      rename_i ns i l r kl kr kll klr ns₁ ns₂ ns₃ jf jx jy
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      obtain ⟨hl, hlnode⟩ := List.getElem?_eq_some_iff.mp hl'
      obtain ⟨hkl, hklnode⟩ := List.getElem?_eq_some_iff.mp hkl'
      obtain ⟨hkll, hkllnode⟩ := List.getElem?_eq_some_iff.mp hkll'
      obtain ⟨w₁, hjf, heqf⟩ := ihf hwf
      obtain ⟨w₂, hjx, heqx⟩ := ihx w₁
      obtain ⟨w₃, hjy, heqy⟩ := ihy w₂
      obtain ⟨t₁, e₁⟩ := DevRel_extends hf
      obtain ⟨t₂, e₂⟩ := DevRel_extends hx
      obtain ⟨t₃, e₃⟩ := DevRel_extends hy
      have hklr : klr < ns.length :=
        Nat.lt_trans (hwf _ hkl _ _ hklnode).2
          (Nat.lt_trans (hwf _ hl _ _ hlnode).1
            (Nat.lt_trans (hwf _ hi _ _ hnode).1 hi))
      have hkr : kr < ns.length :=
        Nat.lt_trans (hwf _ hl _ _ hlnode).2
          (Nat.lt_trans (hwf _ hi _ _ hnode).1 hi)
      have hri : r < ns.length :=
        Nat.lt_trans (hwf _ hi _ _ hnode).2 hi
      have hr₁ : r < ns₁.length := by
        rw [e₁, List.length_append]; omega
      have hjf₂ : jf < ns₂.length := by
        rw [e₂, List.length_append]; omega
      have hjf₃ : jf < ns₃.length := by
        rw [e₃, e₂, List.length_append, List.length_append]; omega
      have hjx₃ : jx < ns₃.length := by
        rw [e₃, List.length_append]; omega
      have hf' : dagUnfold ns₃ jf = cdBasis (dagUnfold ns klr) := by
        rw [e₃, dagUnfold_stable t₃ hjf₂, e₂,
            dagUnfold_stable t₂ hjf, heqf]
      have hx' : dagUnfold ns₃ jx = cdBasis (dagUnfold ns kr) := by
        rw [e₃, dagUnfold_stable t₃ hjx, heqx, e₁,
            dagUnfold_stable t₁ hkr]
      have hy' : dagUnfold ns₃ jy = cdBasis (dagUnfold ns r) := by
        rw [heqy, e₂, dagUnfold_stable t₂ hr₁, e₁,
            dagUnfold_stable t₁ hri]
      refine ⟨DagWf_push2 w₃ hjf₃ hjy (by omega) (by omega), by simp, ?_⟩
      rw [dagUnfold_snoc2]
      simp only [stepNode]
      rw [stepNode_getD (by simp), dagUnfold_push_app hjf₃ hjy]
      rw [stepNode_getD (Nat.lt_trans hjx₃ (by simp)),
        dagUnfold_stable [.app jf jy] hjx₃]
      rw [hf', hx', hy']
      rw [dagUnfold_app hwf hi hnode, dagUnfold_app hwf hl hlnode,
          dagUnfold_app hwf hkl hklnode, dagUnfold_atom hkll hkllnode]
      simp only [GAtom.toTerm, cdBasis]
  | app_dev hi' hred hf hx ihf ihx =>
      rename_i ns i l r ns₁ ns₂ jf jx
      obtain ⟨hi, hnode⟩ := List.getElem?_eq_some_iff.mp hi'
      obtain ⟨w₁, hjf, heqf⟩ := ihf hwf
      obtain ⟨w₂, hjx, heqx⟩ := ihx w₁
      obtain ⟨t₁, e₁⟩ := DevRel_extends hf
      obtain ⟨t₂, e₂⟩ := DevRel_extends hx
      have hri : r < ns.length :=
        Nat.lt_trans (hwf _ hi _ _ hnode).2 hi
      have hjf₂ : jf < ns₂.length := by
        rw [e₂, List.length_append]; omega
      have hf' : dagUnfold ns₂ jf = cdBasis (dagUnfold ns l) := by
        rw [e₂, dagUnfold_stable t₂ hjf, heqf]
      have hx' : dagUnfold ns₂ jx = cdBasis (dagUnfold ns r) := by
        rw [heqx, e₁, dagUnfold_stable t₁ hri]
      have hnr : isRedexHead (dagUnfold ns l) = false := by
        rw [dagUnfold_isRedexHead hwf hi hnode]; exact hred
      refine ⟨DagWf_push1 w₂ hjf₂ hjx, by simp, ?_⟩
      rw [dagUnfold_push_app hjf₂ hjx, hf', hx']
      rw [dagUnfold_app hwf hi hnode, cdBasis_app_generic hnr]

/-- Totality: every well-formed node develops.  The dag is universally
    quantified inside the strong-recursion motive because the host
    re-develops children in the grown table. -/
theorem DevRel_total (i : Nat) (ns : List GNode) (hwf : DagWf ns)
    (hi : i < ns.length) : ∃ ns' j, DevRel ns i ns' j := by
  revert ns hwf hi
  refine Nat.strongRecOn i ?_
  intro i ih ns hwf hi
  cases hnode : ns[i] with
  | atom a =>
      exact ⟨ns, i, DevRel.atom
        (by rw [List.getElem?_eq_getElem hi, hnode])⟩
  | var n =>
      exact ⟨ns, i, DevRel.var
        (by rw [List.getElem?_eq_getElem hi, hnode])⟩
  | app l r =>
      obtain ⟨hl, hr⟩ := hwf i hi l r hnode
      have hli : l < ns.length := Nat.lt_trans hl hi
      have hri : r < ns.length := Nat.lt_trans hr hi
      have hiq : ns[i]? = some (.app l r) := by
        rw [List.getElem?_eq_getElem hi, hnode]
      have develop_generic : isRedexNode ns i = false →
          ∃ ns' j, DevRel ns i ns' j := by
        intro hred
        obtain ⟨ns₁, jf, hf⟩ := ih l hl ns hwf hli
        obtain ⟨w₁, _, _⟩ := DevRel_sound hf hwf
        obtain ⟨t₁, e₁⟩ := DevRel_extends hf
        obtain ⟨ns₂, jx, hx⟩ := ih r hr ns₁ w₁ (by
          rw [e₁, List.length_append]; omega)
        exact ⟨ns₂ ++ [.app jf jx], ns₂.length,
          DevRel.app_dev hiq hred hf hx⟩
      cases hlnode : ns[l] with
      | atom a =>
          cases a with
          | norm =>
              obtain ⟨ns', j, hd⟩ := ih r hr ns hwf hri
              exact ⟨ns', j, DevRel.norm_red hiq
                (by rw [List.getElem?_eq_getElem hli, hlnode]) hd⟩
          | _ =>
              exact develop_generic (by simp only [isRedexNode,
                List.getElem?_eq_getElem hi, hnode,
                List.getElem?_eq_getElem hli, hlnode])
      | var n =>
          exact develop_generic (by simp only [isRedexNode,
            List.getElem?_eq_getElem hi, hnode,
            List.getElem?_eq_getElem hli, hlnode])
      | app kl kr =>
          obtain ⟨hkl, hkr⟩ := hwf l hli kl kr hlnode
          have hkli : kl < ns.length := Nat.lt_trans hkl hli
          cases hklnode : ns[kl] with
          | atom a =>
              cases a with
              | konst =>
                  obtain ⟨ns', j, hd⟩ :=
                    ih kr (Nat.lt_trans hkr hl) ns hwf
                      (Nat.lt_trans hkr hli)
                  exact ⟨ns', j, DevRel.konst_red hiq
                    (by rw [List.getElem?_eq_getElem hli, hlnode])
                    (by rw [List.getElem?_eq_getElem hkli, hklnode])
                    hd⟩
              | dup =>
                  obtain ⟨ns₁, jx, hx⟩ := ih r hr ns hwf hri
                  obtain ⟨w₁, _, _⟩ := DevRel_sound hx hwf
                  obtain ⟨t₁, e₁⟩ := DevRel_extends hx
                  obtain ⟨ns₂, jf, hf⟩ :=
                    ih kr (Nat.lt_trans hkr hl) ns₁ w₁ (by
                      rw [e₁, List.length_append]; omega)
                  exact ⟨ns₂ ++ [.app jf jx, .app ns₂.length jx],
                    ns₂.length + 1, DevRel.dup_red hiq
                    (by rw [List.getElem?_eq_getElem hli, hlnode])
                    (by rw [List.getElem?_eq_getElem hkli, hklnode])
                    hx hf⟩
              | _ =>
                  exact develop_generic (by simp only [isRedexNode,
                    List.getElem?_eq_getElem hi, hnode,
                    List.getElem?_eq_getElem hli, hlnode,
                    List.getElem?_eq_getElem hkli, hklnode])
          | var n =>
              exact develop_generic (by simp only [isRedexNode,
                List.getElem?_eq_getElem hi, hnode,
                List.getElem?_eq_getElem hli, hlnode,
                List.getElem?_eq_getElem hkli, hklnode])
          | app kll klr =>
              obtain ⟨hkll, hklr⟩ := hwf kl hkli kll klr hklnode
              have hklli : kll < ns.length := Nat.lt_trans hkll hkli
              cases hkllnode : ns[kll] with
              | atom a =>
                  cases a with
                  | comp =>
                      obtain ⟨ns₁, jf, hf⟩ :=
                        ih klr (Nat.lt_trans hklr (Nat.lt_trans hkl hl))
                          ns hwf (Nat.lt_trans hklr hkli)
                      obtain ⟨w₁, _, _⟩ := DevRel_sound hf hwf
                      obtain ⟨t₁, e₁⟩ := DevRel_extends hf
                      obtain ⟨ns₂, jg, hg⟩ :=
                        ih kr (Nat.lt_trans hkr hl) ns₁ w₁ (by
                          rw [e₁, List.length_append]; omega)
                      obtain ⟨w₂, _, _⟩ := DevRel_sound hg w₁
                      obtain ⟨t₂, e₂⟩ := DevRel_extends hg
                      obtain ⟨ns₃, jx, hx⟩ := ih r hr ns₂ w₂ (by
                        rw [e₂, e₁, List.length_append,
                            List.length_append]; omega)
                      exact ⟨ns₃ ++ [.app jg jx, .app jf ns₃.length],
                        ns₃.length + 1, DevRel.comp_red hiq
                        (by rw [List.getElem?_eq_getElem hli, hlnode])
                        (by rw [List.getElem?_eq_getElem hkli, hklnode])
                        (by rw [List.getElem?_eq_getElem hklli,
                            hkllnode])
                        hf hg hx⟩
                  | swap =>
                      obtain ⟨ns₁, jf, hf⟩ :=
                        ih klr (Nat.lt_trans hklr (Nat.lt_trans hkl hl))
                          ns hwf (Nat.lt_trans hklr hkli)
                      obtain ⟨w₁, _, _⟩ := DevRel_sound hf hwf
                      obtain ⟨t₁, e₁⟩ := DevRel_extends hf
                      obtain ⟨ns₂, jx, hx⟩ :=
                        ih kr (Nat.lt_trans hkr hl) ns₁ w₁ (by
                          rw [e₁, List.length_append]; omega)
                      obtain ⟨w₂, _, _⟩ := DevRel_sound hx w₁
                      obtain ⟨t₂, e₂⟩ := DevRel_extends hx
                      obtain ⟨ns₃, jy, hy⟩ := ih r hr ns₂ w₂ (by
                        rw [e₂, e₁, List.length_append,
                            List.length_append]; omega)
                      exact ⟨ns₃ ++ [.app jf jy, .app ns₃.length jx],
                        ns₃.length + 1, DevRel.swap_red hiq
                        (by rw [List.getElem?_eq_getElem hli, hlnode])
                        (by rw [List.getElem?_eq_getElem hkli, hklnode])
                        (by rw [List.getElem?_eq_getElem hklli,
                            hkllnode])
                        hf hx hy⟩
                  | _ =>
                      exact develop_generic (by simp only [isRedexNode,
                        List.getElem?_eq_getElem hi, hnode,
                        List.getElem?_eq_getElem hli, hlnode,
                        List.getElem?_eq_getElem hkli, hklnode,
                        List.getElem?_eq_getElem hklli, hkllnode])
              | var n =>
                  exact develop_generic (by simp only [isRedexNode,
                    List.getElem?_eq_getElem hi, hnode,
                    List.getElem?_eq_getElem hli, hlnode,
                    List.getElem?_eq_getElem hkli, hklnode,
                    List.getElem?_eq_getElem hklli, hkllnode])
              | app _ _ =>
                  exact develop_generic (by simp only [isRedexNode,
                    List.getElem?_eq_getElem hi, hnode,
                    List.getElem?_eq_getElem hli, hlnode,
                    List.getElem?_eq_getElem hkli, hklnode,
                    List.getElem?_eq_getElem hklli, hkllnode])

/-- `n` rounds of complete development on terms. -/
def cdIter : Nat → ITerm → ITerm
  | 0, t => t
  | n + 1, t => cdIter n (cdBasis t)

theorem cdIter_ired (n : Nat) (t : ITerm) : IRedBasis t (cdIter n t) := by
  induction n generalizing t with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      exact Relation.ReflTransGen.trans (cdBasis_ired t) (ih _)

/-- A chain of `n` host development rounds. -/
inductive DevChain : List GNode → Nat → List GNode → Nat → Nat → Prop where
  | nil {ns : List GNode} {i : Nat} : DevChain ns i ns i 0
  | cons {ns : List GNode} {i : Nat} {ns' : List GNode} {j : Nat}
      {ns'' : List GNode} {k n : Nat} :
      DevRel ns i ns' j → DevChain ns' j ns'' k n →
      DevChain ns i ns'' k (n + 1)

/-- Round parity: a host `cd` loop that performs `n` rounds unfolds to
    exactly `cdIter n` — the `rounds=` counter the executors report is
    formal complete development. -/
theorem DevChain_unfold {ns i ns' j n} (h : DevChain ns i ns' j n)
    (hwf : DagWf ns) (hi : i < ns.length) :
    DagWf ns' ∧ j < ns'.length ∧
      dagUnfold ns' j = cdIter n (dagUnfold ns i) := by
  induction h with
  | nil => exact ⟨hwf, hi, rfl⟩
  | cons hd _ ih =>
      obtain ⟨w', hj, heq⟩ := DevRel_sound hd hwf
      obtain ⟨w'', hk, heq2⟩ := ih w' hj
      refine ⟨w'', hk, ?_⟩
      rw [heq2, heq]
      rfl

/-- Executor chains stay inside basis reduction. -/
theorem DevChain_ired {ns i ns' j n} (h : DevChain ns i ns' j n)
    (hwf : DagWf ns) (hi : i < ns.length) :
    IRedBasis (dagUnfold ns i) (dagUnfold ns' j) := by
  obtain ⟨_, _, heq⟩ := DevChain_unfold h hwf hi
  rw [heq]
  exact cdIter_ired n _

/-- Determinism up to representation: any two developments of the same
    node unfold to the same term. -/
theorem DevRel_deterministic {ns i ns₁ j₁ ns₂ j₂}
    (h₁ : DevRel ns i ns₁ j₁) (h₂ : DevRel ns i ns₂ j₂)
    (hwf : DagWf ns) :
    dagUnfold ns₁ j₁ = dagUnfold ns₂ j₂ := by
  obtain ⟨_, _, e₁⟩ := DevRel_sound h₁ hwf
  obtain ⟨_, _, e₂⟩ := DevRel_sound h₂ hwf
  rw [e₁, e₂]

end ISAR
