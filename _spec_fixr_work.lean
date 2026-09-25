import ISAR.SpecVocabulary

namespace ISAR

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

end ISAR
