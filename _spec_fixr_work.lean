import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- Batch M layer 4b: assembleOf pass-1 fold evaluation —
-- p1step EQSTR tag dispatch, label/insn acc transitions,
-- nested fragment×item fold over the program.
-- ============================================================

/-- `NIB2B4`-shaped bytes4 cell list. -/
def b4nib (n : Fin 16) : List (Fin 16 × Fin 16) :=
  [(n, 0), (0, 0), (0, 0), (0, 0)]

/-- pass-1 accumulator components: position bytes4, loc cells,
    prep cells. -/
abbrev P1St := List (Fin 16 × Fin 16) × List LTerm × List LTerm

/-- accumulator term from semantic components:
    `PAIR pos (PAIR loc prep)`. -/
def p1AccT (posT locT prepT : LTerm) : LTerm :=
  pairLit posT (pairLit locT prepT)

/-- canonical accumulator term from a semantic state. -/
def p1AccTV (st : P1St) : LTerm :=
  p1AccT (scottList (bm st.1)) (scottList st.2.1) (scottList st.2.2)

/-- label-case continuation as emitted — `.var 4` is the `rr` slot
    (bound by `λtg.λrr` in the enclosing dispatch, valid only under
    ≥ 5 outer binders). -/
def p1LabelContT (basT itT : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(.var 3),
    (aps pairSrcL [(aps conssL [(aps pairSrcL [(aps headL [(.var 4)]),
      (aps b4addL [basT, (.var 3)])]), (.var 1)]),
    (aps conssL [(aps pairSrcL [itT, (aps pairSrcL [(.var 3), klL])]),
      (.var 0)])])])))])))

/-- label-case continuation, post-substitution form — `rrT` is the
    (closed) rest-list term spliced where `.var 4` stood. -/
def p1LabelContS (basT rrT itT : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(.var 3),
    (aps pairSrcL [(aps conssL [(aps pairSrcL [(aps headL [rrT]),
      (aps b4addL [basT, (.var 3)])]), (.var 1)]),
    (aps conssL [(aps pairSrcL [itT, (aps pairSrcL [(.var 3), klL])]),
      (.var 0)])])])))])))

/-- insn-case continuation (it spliced; `.var 4` is the bound `ln4`
    slot — valid under `λenc.λln4` + four destructuring binders). -/
def p1InsnContT (itT : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL
    [(aps b4addL [(.var 3), (.var 4)]),
     (aps pairSrcL [(.var 1),
       (aps conssL [(aps pairSrcL [itT, (aps pairSrcL [(.var 3), (.var 4)])]),
         (.var 0)])])])))])))

/-- insn-case outer:
    `λenc. (λln4. acc·(λp0.λr0. r0·(λlc.λpr. …)))·(NIB2B4 (enc·KI))`
    — emitted as `(λenc. …)·(ENC it ZRV)` at the call site. -/
def p1InsnOuterT (itT accT : LTerm) : LTerm :=
  (.abs (aps (.abs (aps accT [p1InsnContT itT]))
    [aps nib2b4L [aps (.var 0) [aps klL [idL]]]]))

/-- p1step's dispatch continuation (acc/it/enc/zrv/base spliced):
    `λtg.λrr. EQSTR tg LBL (LEN tg) L I`. -/
def p1DispT (encT zrvT basT accT itT : LTerm) : LTerm :=
  (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]),
    (aps accT [p1LabelContT basT itT]),
    (aps (p1InsnOuterT itT accT) [aps encT [itT, zrvT]])])))

/-- semantic view of one assembly item. -/
structure AsmItem where
  itT : LTerm
  ns : List (Fin 16)
  rrCs : List LTerm
  ln : Fin 16
  byT : LTerm
  lnT : LTerm

/-- well-formedness for pass-1: `it` destructures to a Scott cell
    with tag `ns` and rest `rrCs`; the encoder maps it to
    `PAIR byT lnT` with `lnT →* nibLit ln`. -/
def AsmItem.V (encT zrvT : LTerm) (it : AsmItem) : Prop :=
  (∃ tgT rrT, LRed it.itT (cellLit tgT rrT) ∧
      LRed tgT (scottList (it.ns.map nibLit)) ∧
      LRed rrT (scottList it.rrCs) ∧
      closed 0 tgT = true ∧ closed 0 rrT = true) ∧
  closed 0 it.itT = true ∧
  (∀ c ∈ it.rrCs, closed 0 c = true) ∧
  closed 0 it.byT = true ∧ closed 0 it.lnT = true ∧
  LRed (aps encT [it.itT, zrvT]) (pairLit it.byT it.lnT) ∧
  LRed it.lnT (nibLit it.ln)

/-- semantic pass-1 step on `(pos, locCs, prepCs)`:
    label items cons `(name → B4ADD base pos)` onto the loc table and
    `(it, (pos, nil))` onto prep; insn items cons `(it, (pos, nib4))`
    onto prep and advance pos by `B4ADD pos nib4`. -/
def p1StepSem (basB : List (Fin 16 × Fin 16)) (it : AsmItem)
    (st : P1St) : P1St :=
  if decide (it.ns = lblNibs) then
    match it.rrCs with
    | nm :: _ =>
        (st.1,
         pairLit nm (scottList (bm (resList basB st.1 0))) :: st.2.1,
         pairLit it.itT (pairLit (scottList (bm st.1)) nilL) :: st.2.2)
    | [] => st
  else
    (resList st.1 (b4nib it.ln) 0,
     st.2.1,
     pairLit it.itT
       (pairLit (scottList (bm st.1)) (scottList (bm (b4nib it.ln))))
       :: st.2.2)

-- closedness -----------------------------------------------------

theorem closed_p1LabelContT {basT itT : LTerm} (c : Nat)
    (hb : closed 4 basT = true) (hi : closed 4 itT = true) :
    closed (c + 1) (p1LabelContT basT itT) = true := by
  simp only [p1LabelContT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono hb (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p1LabelContS {basT rrT itT : LTerm} (c : Nat)
    (hb : closed 4 basT = true) (hr : closed 4 rrT = true)
    (hi : closed 4 itT = true) :
    closed c (p1LabelContS basT rrT itT) = true := by
  simp only [p1LabelContS, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono hb (by omega)
    | exact closed_mono hr (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p1InsnContT {itT : LTerm} (c : Nat)
    (hi : closed 4 itT = true) :
    closed (c + 1) (p1InsnContT itT) = true := by
  simp only [p1InsnContT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals exact closed_mono hi (by omega)

theorem closed_p1InsnOuterT {itT accT : LTerm} (c : Nat)
    (hi : closed 4 itT = true) (ha : closed 2 accT = true) :
    closed c (p1InsnOuterT itT accT) = true := by
  simp only [p1InsnOuterT, p1InsnContT, closed, aps, List.foldl,
    Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p1DispT {encT zrvT basT accT itT : LTerm} (c : Nat)
    (he : closed 2 encT = true) (hz : closed 2 zrvT = true)
    (hb : closed 2 basT = true) (ha : closed 2 accT = true)
    (hi : closed 2 itT = true) :
    closed c (p1DispT encT zrvT basT accT itT) = true := by
  simp only [p1DispT, p1LabelContT, p1InsnOuterT, p1InsnContT,
    closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hz (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)

-- post-subst continuation defs --------------------------------------

/-- label inner continuation after p0-substitution:
    `λlc.λpr. PAIR posT (PAIR (CONS (PAIR (HEAD rr) (B4ADD base pos)) lc)
                                (CONS (PAIR it (PAIR pos K)) pr))`. -/
def p1LabelIC2 (basT rrT itT posT : LTerm) : LTerm :=
  (.abs (.abs (aps pairSrcL [posT,
    (aps pairSrcL
      [(aps conssL [(aps pairSrcL [(aps headL [rrT]),
          (aps b4addL [basT, posT])]), (.var 1)]),
       (aps conssL [(aps pairSrcL [itT, (aps pairSrcL [posT, klL])]),
         (.var 0)])])])))

/-- label produced body after lc/pr-substitution. -/
def p1LabelBody (basT rrT itT posT locT prepT : LTerm) : LTerm :=
  aps pairSrcL [posT,
    aps pairSrcL
      [aps conssL [aps pairSrcL [aps headL [rrT],
          aps b4addL [basT, posT]], locT],
       aps conssL [aps pairSrcL [itT, aps pairSrcL [posT, klL]], prepT]]]

/-- insn continuation after the enc/ln4 lets (itT/ln4V spliced):
    `λp0.λr0. r0·(λlc.λpr. PAIR (B4ADD p0 ln4V) (PAIR lc (CONS … pr)))`. -/
def p1InsnContS (itT ln4V : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL
    [(aps b4addL [(.var 3), ln4V]),
     (aps pairSrcL [(.var 1),
       (aps conssL [(aps pairSrcL [itT, (aps pairSrcL [(.var 3), ln4V])]),
         (.var 0)])])])))])))

/-- insn inner continuation after p0-substitution:
    `λlc.λpr. PAIR (B4ADD posT ln4V) (PAIR lc (CONS (PAIR it (PAIR posT ln4V)) pr))`. -/
def p1InsnIC2 (itT posT ln4V : LTerm) : LTerm :=
  (.abs (.abs (aps pairSrcL
    [(aps b4addL [posT, ln4V]),
     (aps pairSrcL [(.var 1),
       (aps conssL [(aps pairSrcL [itT, (aps pairSrcL [posT, ln4V])]),
         (.var 0)])])])))

/-- insn produced body after lc/pr-substitution. -/
def p1InsnBody (itT posT ln4V locT prepT : LTerm) : LTerm :=
  aps pairSrcL [aps b4addL [posT, ln4V],
    aps pairSrcL [locT,
      aps conssL [aps pairSrcL [itT, aps pairSrcL [posT, ln4V]], prepT]]]

-- helpers -----------------------------------------------------------

/-- pairSrc-application normalization (`conssCell_nf` analog). -/
theorem pairSrcCell_nf {h h' t t' : LTerm} (hh : LRed h h')
    (ht : LRed t t') (hh' : closed 0 h' = true)
    (ht' : closed 0 t' = true) :
    LRed (aps pairSrcL [h, t]) (pairLit h' t') :=
  (LRed_app_right ht).trans
    ((LRed_app_left (LRed_app_right hh)).trans
      (pairSrc_nf h' t' hh' ht'))

/-- `NIB2B4·nib n →* scottList (bm (b4nib n))` — bm-normalized. -/
theorem nib2b4_eval_scott (n : Fin 16) :
    LRed (.app nib2b4L (nibLit n))
      (scottList (bm (b4nib n))) := by
  have hb0 : LRed b0cT (byteLit 0 0) := by
    show LRed (aps pairSrcL [nibLit 0, nibLit 0]) _
    exact pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _)
  have hb0c : closed 0 (byteLit 0 0) = true := closed_byteLit _ _
  have c1 : LRed (.app nib2b4L (nibLit n))
      (aps conssL [aps pairSrcL [nibLit n, nibLit 0],
        aps conssL [b0cT, aps conssL [b0cT,
          aps conssL [b0cT, klL]]]]) :=
    LRed_of_hsteps (k := 1) (by
      simp [nib2b4L, aps, List.foldl, hsteps, hstep, subst,
            shift_of_closed0, subst_of_closed0,
            closed_nibLit, closed_conssL, closed_pairSrcL,
            closed_klL, closed_b0cT])
  refine c1.trans ?_
  have s3 : LRed (aps conssL [b0cT, klL])
      (cellLit (byteLit 0 0) nilL) :=
    conssCell_nf hb0 Relation.ReflTransGen.refl hb0c closed_klL
  have s2 : LRed (aps conssL [b0cT, aps conssL [b0cT, klL]])
      (cellLit (byteLit 0 0) (cellLit (byteLit 0 0) nilL)) :=
    conssCell_nf hb0 s3 hb0c (closed_cellLit hb0c closed_klL)
  have s1 : LRed (aps conssL [b0cT, aps conssL [b0cT,
      aps conssL [b0cT, klL]]])
      (cellLit (byteLit 0 0) (cellLit (byteLit 0 0)
        (cellLit (byteLit 0 0) nilL))) :=
    conssCell_nf hb0 s2 hb0c
      (closed_cellLit hb0c (closed_cellLit hb0c closed_klL))
  have hn : LRed (aps pairSrcL [nibLit n, nibLit 0])
      (byteLit n 0) :=
    pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _)
  have s0 := conssCell_nf hn s1 (closed_byteLit _ _)
    (closed_cellLit hb0c (closed_cellLit hb0c
      (closed_cellLit hb0c closed_klL)))
  show LRed _ (cellLit (byteLit n 0) (cellLit (byteLit 0 0)
    (cellLit (byteLit 0 0) (cellLit (byteLit 0 0) nilL))))
  exact s0

-- staged opens ------------------------------------------------------

/-- `p1step·acc·it →* it·K·(λtg.λrr. dispatch)` — two outer betas. -/
theorem p1Step_open (e z b accT itT : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hb : closed 0 b = true) (ha : closed 0 accT = true)
    (hi : closed 0 itT = true) :
    LRed (aps (p1StepT e z b) [accT, itT])
      (aps itT [klL, p1DispT e z b accT itT]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cz : ∀ c, closed c z = true := fun c =>
    closed_mono hz (Nat.zero_le c)
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
  have c2 : ∀ c, closed c lblL = true := fun c =>
    closed_mono closed_lblL (Nat.zero_le c)
  have c3 : ∀ c, closed c lenL = true := fun c =>
    closed_mono closed_lenL (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c6 : ∀ c, closed c headL = true := fun c =>
    closed_mono closed_headL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c9 : ∀ c, closed c nib2b4L = true := fun c =>
    closed_mono closed_nib2b4L (Nat.zero_le c)
  have c10 : ∀ c, closed c idL = true := fun c =>
    closed_mono closed_idL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1StepT, p1DispT, p1LabelContT, p1InsnOuterT, p1InsnContT,
          aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cz, cb, ca, ci, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10])

/-- `disp·tg·rr →* EQSTR tg lbl (LEN tg) L I` — tg/rr betas. -/
theorem p1Disp_open (e z b accT itT tgT rrT : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hb : closed 0 b = true) (ha : closed 0 accT = true)
    (hi : closed 0 itT = true) (ht : closed 0 tgT = true)
    (hr : closed 0 rrT = true) :
    LRed (aps (p1DispT e z b accT itT) [tgT, rrT])
      (aps eqStrL [tgT, lblL, aps lenL [tgT],
        aps accT [p1LabelContS b rrT itT],
        aps (p1InsnOuterT itT accT) [aps e [itT, z]]]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cz : ∀ c, closed c z = true := fun c =>
    closed_mono hz (Nat.zero_le c)
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have ct : ∀ c, closed c tgT = true := fun c =>
    closed_mono ht (Nat.zero_le c)
  have cr : ∀ c, closed c rrT = true := fun c =>
    closed_mono hr (Nat.zero_le c)
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
  have c2 : ∀ c, closed c lblL = true := fun c =>
    closed_mono closed_lblL (Nat.zero_le c)
  have c3 : ∀ c, closed c lenL = true := fun c =>
    closed_mono closed_lenL (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c6 : ∀ c, closed c headL = true := fun c =>
    closed_mono closed_headL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c9 : ∀ c, closed c nib2b4L = true := fun c =>
    closed_mono closed_nib2b4L (Nat.zero_le c)
  have c10 : ∀ c, closed c idL = true := fun c =>
    closed_mono closed_idL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1DispT, p1LabelContT, p1LabelContS, p1InsnOuterT, p1InsnContT,
          aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cz, cb, ca, ci, ct, cr, c1, c2, c3, c4, c5, c6, c7, c8,
          c9, c10])

/-- label continuation on the destructured acc — p0/r0 betas. -/
theorem p1LabelCont_apply (b rrT itT posT locT prepT : LTerm)
    (hb : closed 0 b = true) (hr : closed 0 rrT = true)
    (hi : closed 0 itT = true) (hp : closed 0 posT = true)
    (hl : closed 0 locT = true) (hq : closed 0 prepT = true) :
    LRed (aps (p1LabelContS b rrT itT) [posT, pairLit locT prepT])
      (aps (pairLit locT prepT) [p1LabelIC2 b rrT itT posT]) := by
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have cr : ∀ c, closed c rrT = true := fun c =>
    closed_mono hr (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have cp : ∀ c, closed c posT = true := fun c =>
    closed_mono hp (Nat.zero_le c)
  have cl : ∀ c, closed c locT = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cq : ∀ c, closed c prepT = true := fun c =>
    closed_mono hq (Nat.zero_le c)
  have cpr : ∀ c, closed c (pairLit locT prepT) = true := fun c =>
    closed_mono (closed_pairLit (cl 1) (cq 1)) (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c6 : ∀ c, closed c headL = true := fun c =>
    closed_mono closed_headL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1LabelContS, p1LabelIC2, aps, List.foldl, hsteps, hstep,
          subst, subst_of_closed, shift_of_closed,
          cb, cr, ci, cp, cpr, c4, c5, c6, c7, c8])

/-- label inner continuation — lc/pr betas to the produced body. -/
theorem p1LabelIC2_apply (b rrT itT posT locT prepT : LTerm)
    (hb : closed 0 b = true) (hr : closed 0 rrT = true)
    (hi : closed 0 itT = true) (hp : closed 0 posT = true)
    (hl : closed 0 locT = true) (hq : closed 0 prepT = true) :
    LRed (aps (p1LabelIC2 b rrT itT posT) [locT, prepT])
      (p1LabelBody b rrT itT posT locT prepT) := by
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have cr : ∀ c, closed c rrT = true := fun c =>
    closed_mono hr (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have cp : ∀ c, closed c posT = true := fun c =>
    closed_mono hp (Nat.zero_le c)
  have cl : ∀ c, closed c locT = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cq : ∀ c, closed c prepT = true := fun c =>
    closed_mono hq (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c6 : ∀ c, closed c headL = true := fun c =>
    closed_mono closed_headL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1LabelIC2, p1LabelBody, aps, List.foldl, hsteps, hstep,
          subst, subst_of_closed, shift_of_closed,
          cb, cr, ci, cp, cl, cq, c4, c5, c6, c7, c8])

/-- insn outer — enc/ln4 let-betas:
    `(λenc. (λln4. acc·cont)·ln4V)·encV →* acc·(cont[ln4V'])`. -/
theorem p1InsnOuter_apply (e z accT itT : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (ha : closed 0 accT = true) (hi : closed 0 itT = true) :
    LRed (aps (p1InsnOuterT itT accT) [aps e [itT, z]])
      (aps accT [p1InsnContS itT
        (aps nib2b4L [aps (aps e [itT, z]) [aps klL [idL]]])]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cz : ∀ c, closed c z = true := fun c =>
    closed_mono hz (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c9 : ∀ c, closed c nib2b4L = true := fun c =>
    closed_mono closed_nib2b4L (Nat.zero_le c)
  have c10 : ∀ c, closed c idL = true := fun c =>
    closed_mono closed_idL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1InsnOuterT, p1InsnContT, p1InsnContS,
          aps, List.foldl, hsteps, hstep, subst, shift,
          subst_of_closed, shift_of_closed,
          ce, cz, ca, ci, c4, c5, c7, c8, c9, c10])

/-- insn continuation on the destructured acc — p0/r0 betas. -/
theorem p1InsnContS_apply (itT posT ln4V locT prepT : LTerm)
    (hi : closed 0 itT = true) (hp : closed 0 posT = true)
    (h4 : closed 0 ln4V = true) (hl : closed 0 locT = true)
    (hq : closed 0 prepT = true) :
    LRed (aps (p1InsnContS itT ln4V) [posT, pairLit locT prepT])
      (aps (pairLit locT prepT) [p1InsnIC2 itT posT ln4V]) := by
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have cp : ∀ c, closed c posT = true := fun c =>
    closed_mono hp (Nat.zero_le c)
  have c4v : ∀ c, closed c ln4V = true := fun c =>
    closed_mono h4 (Nat.zero_le c)
  have cl : ∀ c, closed c locT = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cq : ∀ c, closed c prepT = true := fun c =>
    closed_mono hq (Nat.zero_le c)
  have cpr : ∀ c, closed c (pairLit locT prepT) = true := fun c =>
    closed_mono (closed_pairLit (cl 1) (cq 1)) (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1InsnContS, p1InsnIC2, aps, List.foldl, hsteps, hstep,
          subst, subst_of_closed, shift_of_closed,
          ci, cp, c4v, cpr, c4, c5, c7])

/-- insn inner continuation — lc/pr betas to the produced body. -/
theorem p1InsnIC2_apply (itT posT ln4V locT prepT : LTerm)
    (hi : closed 0 itT = true) (hp : closed 0 posT = true)
    (h4 : closed 0 ln4V = true) (hl : closed 0 locT = true)
    (hq : closed 0 prepT = true) :
    LRed (aps (p1InsnIC2 itT posT ln4V) [locT, prepT])
      (p1InsnBody itT posT ln4V locT prepT) := by
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have cp : ∀ c, closed c posT = true := fun c =>
    closed_mono hp (Nat.zero_le c)
  have c4v : ∀ c, closed c ln4V = true := fun c =>
    closed_mono h4 (Nat.zero_le c)
  have cl : ∀ c, closed c locT = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cq : ∀ c, closed c prepT = true := fun c =>
    closed_mono hq (Nat.zero_le c)
  have c4 : ∀ c, closed c pairSrcL = true := fun c =>
    closed_mono closed_pairSrcL (Nat.zero_le c)
  have c5 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p1InsnIC2, p1InsnBody, aps, List.foldl, hsteps, hstep,
          subst, subst_of_closed, shift_of_closed,
          ci, cp, c4v, cl, cq, c4, c5, c7])

-- semantic step evaluation -------------------------------------------

/-- label-case step evaluation: `EQSTR` true → the label continuation
    records `(HEAD rr → B4ADD base pos)` in loc and `(it,(pos,nil))` in
    prep; pos unchanged. -/
theorem p1_label_eval (encT zrvT basT accT : LTerm)
    (basB : List (Fin 16 × Fin 16)) (it : AsmItem) (st : P1St)
    (nm : LTerm) (rest : List LTerm)
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true) (ha : closed 0 accT = true)
    (hit : AsmItem.V encT zrvT it)
    (hacc : LRed accT (p1AccTV st))
    (hbas : LRed basT (scottList (bm basB)))
    (hb4 : basB.length = 4) (hpos4 : st.1.length = 4)
    (hns : it.ns = lblNibs) (hrr : it.rrCs = nm :: rest)
    (hst1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (hst2 : ∀ c ∈ st.2.2, closed 0 c = true) :
    LRed (aps (p1StepT encT zrvT basT) [accT, it.itT])
         (p1AccTV (p1StepSem basB it st)) := by
  obtain ⟨⟨tgT, rrT, hitC, htag, hrr2, htgcl, hrrcl⟩, hitcl, hrrCs,
      hbycl, hlncl, henc, hlnT⟩ := hit
  set posT := scottList (bm st.1) with hposT
  set locT := scottList st.2.1 with hlocT
  set prepT := scottList st.2.2 with hprepT
  have hbm : ∀ e ∈ bm st.1, closed 0 e = true := fun e he2 => by
    simp only [bm, List.mem_map] at he2
    obtain ⟨p, _, rfl⟩ := he2; exact closed_byteLit _ _
  have hposcl : closed 0 posT = true := closed_scottList hbm
  have hloccl : closed 0 locT = true := closed_scottList hst1
  have hprepcl : closed 0 prepT = true := closed_scottList hst2
  have hlpcl : closed 0 (pairLit locT prepT) = true :=
    closed_pairLit
      (closed_mono hloccl (Nat.zero_le 1))
      (closed_mono hprepcl (Nat.zero_le 1))
  have hnmc : closed 0 nm = true := hrrCs nm (by rw [hrr]; simp)
  have hrestc : ∀ c ∈ rest, closed 0 c = true := fun c hc =>
    hrrCs c (by rw [hrr]; simp [hc])
  have hrestcl : closed 0 (scottList rest) = true :=
    closed_scottList hrestc
  -- dispatch chain
  have s1 := p1Step_open encT zrvT basT accT it.itT he hz hb ha hitcl
  have s2 : LRed (aps it.itT [klL, p1DispT encT zrvT basT accT it.itT])
      (aps (p1DispT encT zrvT basT accT it.itT) [tgT, rrT]) :=
    (LRed_app_left (LRed_app_left hitC)).trans
      (cellLit_apply2 tgT rrT klL _ htgcl hrrcl)
  have s3 := p1Disp_open encT zrvT basT accT it.itT tgT rrT
    he hz hb ha hitcl htgcl hrrcl
  -- eqStr prefix → boolLit (decide (ns = lblNibs))
  have hnib : ∀ e ∈ it.ns.map nibLit, closed 0 e = true :=
    fun e he2 => by
      simp only [List.mem_map] at he2
      obtain ⟨p, _, rfl⟩ := he2; exact closed_nibLit _
  have hlen : LRed (aps lenL [tgT])
      (succChain kilL it.ns.length) := by
    have h1 := (LRed_app_right htag).trans
      (len_eval (it.ns.map nibLit) hnib)
    rw [List.length_map] at h1; exact h1
  have hlencl : closed 0 (aps lenL [tgT]) = true := by
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_lenL, htgcl⟩
  have heq3 := eqStr_eval it.ns lblNibs it.ns.length (Nat.le_refl _)
    tgT lblL (aps lenL [tgT]) htag lbl_nf hlen htgcl closed_lblL hlencl
  set Larg := aps accT [p1LabelContS basT rrT it.itT] with hLarg
  set Iarg := aps (p1InsnOuterT it.itT accT)
    [aps encT [it.itT, zrvT]] with hIarg
  have heq5 : LRed (aps eqStrL [tgT, lblL, aps lenL [tgT], Larg, Iarg])
      (aps (boolLit (decide (it.ns = lblNibs))) [Larg, Iarg]) :=
    LRed_app_left (LRed_app_left heq3)
  have hsel := heq5.trans (boolLit_sel _ Larg Iarg)
  have hdec : decide (it.ns = lblNibs) = true := by
    rw [hns]; decide
  rw [hdec] at hsel
  have hsel' : LRed (aps eqStrL [tgT, lblL, aps lenL [tgT], Larg, Iarg])
      Larg := hsel
  -- label continuation chain
  have s4 : LRed Larg (aps (p1AccTV st)
      [p1LabelContS basT rrT it.itT]) := LRed_app_left hacc
  have s5 : LRed (.app (p1AccTV st)
        (p1LabelContS basT rrT it.itT))
      (aps (p1LabelContS basT rrT it.itT)
        [posT, pairLit locT prepT]) :=
    pairLit_apply posT (pairLit locT prepT) _ hposcl hlpcl
  have s6 := p1LabelCont_apply basT rrT it.itT posT locT prepT
    hb hrrcl hitcl hposcl hloccl hprepcl
  have s7 : LRed (.app (pairLit locT prepT)
        (p1LabelIC2 basT rrT it.itT posT))
      (aps (p1LabelIC2 basT rrT it.itT posT) [locT, prepT]) :=
    pairLit_apply locT prepT _ hloccl hprepcl
  have s8 := p1LabelIC2_apply basT rrT it.itT posT locT prepT
    hb hrrcl hitcl hposcl hloccl hprepcl
  -- body normalization (innermost first)
  have hrr2' : LRed rrT (cellLit nm (scottList rest)) := by
    rw [hrr] at hrr2; exact hrr2
  have nA : LRed (.app headL rrT) nm :=
    (LRed_app_right hrr2').trans
      (head_cell nm (scottList rest) hnmc hrestcl)
  have nB : LRed (aps b4addL [basT, posT])
      (scottList (bm (resList basB st.1 0))) :=
    (LRed_app_left (LRed_app_right hbas)).trans
      (b4add_eval_scott basB st.1 (hb4.trans hpos4.symm))
  have hrbm : ∀ e ∈ bm (resList basB st.1 0), closed 0 e = true :=
    fun e he2 => by
      simp only [bm, List.mem_map] at he2
      obtain ⟨p, _, rfl⟩ := he2; exact closed_byteLit _ _
  have hrescl : closed 0 (scottList (bm (resList basB st.1 0))) =
      true := closed_scottList hrbm
  have nC := pairSrcCell_nf nA nB hnmc hrescl
  have hcl1 : closed 0 (pairLit nm
      (scottList (bm (resList basB st.1 0)))) = true :=
    closed_pairLit (closed_mono hnmc (Nat.zero_le 1))
      (closed_mono hrescl (Nat.zero_le 1))
  have nD := conssCell_nf nC Relation.ReflTransGen.refl hcl1 hloccl
  have pA := pairSrcCell_nf Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl hposcl closed_klL
  have hcl2 : closed 0 (pairLit posT klL) = true :=
    closed_pairLit (closed_mono hposcl (Nat.zero_le 1))
      (closed_mono closed_klL (Nat.zero_le 1))
  have pB := pairSrcCell_nf Relation.ReflTransGen.refl pA hitcl hcl2
  have hcl3 : closed 0 (pairLit it.itT (pairLit posT klL)) = true :=
    closed_pairLit (closed_mono hitcl (Nat.zero_le 1))
      (closed_mono hcl2 (Nat.zero_le 1))
  have pC := conssCell_nf pB Relation.ReflTransGen.refl hcl3 hprepcl
  have hcl4 : closed 0 (cellLit (pairLit nm
      (scottList (bm (resList basB st.1 0)))) locT) = true :=
    closed_cellLit hcl1 hloccl
  have hcl5 : closed 0 (cellLit (pairLit it.itT (pairLit posT klL))
      prepT) = true := closed_cellLit hcl3 hprepcl
  have iP := pairSrcCell_nf nD pC hcl4 hcl5
  have hcl6 : closed 0 (pairLit (cellLit (pairLit nm
      (scottList (bm (resList basB st.1 0)))) locT)
      (cellLit (pairLit it.itT (pairLit posT klL)) prepT)) = true :=
    closed_pairLit (closed_mono hcl4 (Nat.zero_le 1))
      (closed_mono hcl5 (Nat.zero_le 1))
  have oP := pairSrcCell_nf Relation.ReflTransGen.refl iP hposcl hcl6
  -- semantic unfold + finish
  have hsem : p1StepSem basB it st =
      (st.1, pairLit nm (scottList (bm (resList basB st.1 0))) ::
        st.2.1,
       pairLit it.itT (pairLit (scottList (bm st.1)) nilL) ::
        st.2.2) := by
    simp [p1StepSem, hns, hrr]
  rw [hsem]
  show LRed _ (p1AccT posT
    (cellLit (pairLit nm (scottList (bm (resList basB st.1 0))))
      locT)
    (cellLit (pairLit it.itT (pairLit posT nilL)) prepT))
  exact s1.trans (s2.trans (s3.trans (hsel'.trans
    (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans oP))))))))

/-- insn-case step evaluation: `EQSTR` false → the insn continuation
    records `(it,(pos,ln4))` in prep and advances pos by
    `B4ADD pos (NIB2B4 (enc·it·zrv)·KI)`. -/
theorem p1_insn_eval (encT zrvT basT accT : LTerm)
    (basB : List (Fin 16 × Fin 16)) (it : AsmItem) (st : P1St)
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true) (ha : closed 0 accT = true)
    (hit : AsmItem.V encT zrvT it)
    (hacc : LRed accT (p1AccTV st))
    (hpos4 : st.1.length = 4)
    (hns : it.ns ≠ lblNibs)
    (hst1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (hst2 : ∀ c ∈ st.2.2, closed 0 c = true) :
    LRed (aps (p1StepT encT zrvT basT) [accT, it.itT])
         (p1AccTV (p1StepSem basB it st)) := by
  obtain ⟨⟨tgT, rrT, hitC, htag, hrr2, htgcl, hrrcl⟩, hitcl, hrrCs,
      hbycl, hlncl, henc, hlnT⟩ := hit
  set posT := scottList (bm st.1) with hposT
  set locT := scottList st.2.1 with hlocT
  set prepT := scottList st.2.2 with hprepT
  set ln4V := aps nib2b4L
    [aps (aps encT [it.itT, zrvT]) [aps klL [idL]]] with hln4V
  have hbm : ∀ e ∈ bm st.1, closed 0 e = true := fun e he2 => by
    simp only [bm, List.mem_map] at he2
    obtain ⟨p, _, rfl⟩ := he2; exact closed_byteLit _ _
  have hposcl : closed 0 posT = true := closed_scottList hbm
  have hloccl : closed 0 locT = true := closed_scottList hst1
  have hprepcl : closed 0 prepT = true := closed_scottList hst2
  have hlpcl : closed 0 (pairLit locT prepT) = true :=
    closed_pairLit
      (closed_mono hloccl (Nat.zero_le 1))
      (closed_mono hprepcl (Nat.zero_le 1))
  -- ln4 chain: (enc·it·zrv)·KI → lnT → nibLit ln → NIB2B4 → bm
  have e1 : LRed (aps (aps encT [it.itT, zrvT]) [aps klL [idL]])
      it.lnT :=
    ((LRed_app_left henc).trans (LRed_app_right kiI_eval)).trans
      (pairLit_snd it.byT it.lnT hbycl hlncl)
  have hln4 : LRed ln4V (scottList (bm (b4nib it.ln))) :=
    (LRed_app_right (e1.trans hlnT)).trans (nib2b4_eval_scott it.ln)
  have hln4cl : closed 0 ln4V = true := by
    simp only [hln4V, aps, List.foldl, closed, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_nib2b4L
      | exact he
      | exact hitcl
      | exact hz
  have h4bm : ∀ e ∈ bm (b4nib it.ln), closed 0 e = true :=
    fun e he2 => by
      simp only [bm, List.mem_map] at he2
      obtain ⟨p, _, rfl⟩ := he2; exact closed_byteLit _ _
  have h4cl : closed 0 (scottList (bm (b4nib it.ln))) = true :=
    closed_scottList h4bm
  -- dispatch chain
  have s1 := p1Step_open encT zrvT basT accT it.itT he hz hb ha hitcl
  have s2 : LRed (aps it.itT [klL, p1DispT encT zrvT basT accT it.itT])
      (aps (p1DispT encT zrvT basT accT it.itT) [tgT, rrT]) :=
    (LRed_app_left (LRed_app_left hitC)).trans
      (cellLit_apply2 tgT rrT klL _ htgcl hrrcl)
  have s3 := p1Disp_open encT zrvT basT accT it.itT tgT rrT
    he hz hb ha hitcl htgcl hrrcl
  have hnib : ∀ e ∈ it.ns.map nibLit, closed 0 e = true :=
    fun e he2 => by
      simp only [List.mem_map] at he2
      obtain ⟨p, _, rfl⟩ := he2; exact closed_nibLit _
  have hlen : LRed (aps lenL [tgT])
      (succChain kilL it.ns.length) := by
    have h1 := (LRed_app_right htag).trans
      (len_eval (it.ns.map nibLit) hnib)
    rw [List.length_map] at h1; exact h1
  have hlencl : closed 0 (aps lenL [tgT]) = true := by
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_lenL, htgcl⟩
  have heq3 := eqStr_eval it.ns lblNibs it.ns.length (Nat.le_refl _)
    tgT lblL (aps lenL [tgT]) htag lbl_nf hlen htgcl closed_lblL hlencl
  set Larg := aps accT [p1LabelContS basT rrT it.itT] with hLarg
  set Iarg := aps (p1InsnOuterT it.itT accT)
    [aps encT [it.itT, zrvT]] with hIarg
  have heq5 : LRed (aps eqStrL [tgT, lblL, aps lenL [tgT], Larg, Iarg])
      (aps (boolLit (decide (it.ns = lblNibs))) [Larg, Iarg]) :=
    LRed_app_left (LRed_app_left heq3)
  have hsel := heq5.trans (boolLit_sel _ Larg Iarg)
  have hdec : decide (it.ns = lblNibs) = false := decide_eq_false hns
  rw [hdec] at hsel
  have hsel' : LRed (aps eqStrL [tgT, lblL, aps lenL [tgT], Larg, Iarg])
      Iarg := hsel
  -- insn outer lets → acc·contS
  have s4 : LRed Iarg (aps accT [p1InsnContS it.itT ln4V]) := by
    have h := p1InsnOuter_apply encT zrvT accT it.itT he hz ha hitcl
    rw [← hln4V] at h; exact h
  have s5 : LRed (aps accT [p1InsnContS it.itT ln4V])
      (aps (p1AccTV st) [p1InsnContS it.itT ln4V]) :=
    LRed_app_left hacc
  have s6 : LRed (.app (p1AccTV st) (p1InsnContS it.itT ln4V))
      (aps (p1InsnContS it.itT ln4V) [posT, pairLit locT prepT]) :=
    pairLit_apply posT (pairLit locT prepT) _ hposcl hlpcl
  have s7 := p1InsnContS_apply it.itT posT ln4V locT prepT
    hitcl hposcl hln4cl hloccl hprepcl
  have s8 : LRed (.app (pairLit locT prepT)
        (p1InsnIC2 it.itT posT ln4V))
      (aps (p1InsnIC2 it.itT posT ln4V) [locT, prepT]) :=
    pairLit_apply locT prepT _ hloccl hprepcl
  have s9 := p1InsnIC2_apply it.itT posT ln4V locT prepT
    hitcl hposcl hln4cl hloccl hprepcl
  -- body normalization (innermost first)
  have qA : LRed (aps b4addL [posT, ln4V])
      (scottList (bm (resList st.1 (b4nib it.ln) 0))) :=
    (LRed_app_right hln4).trans
      (b4add_eval_scott st.1 (b4nib it.ln) (by simp [b4nib, hpos4]))
  have h4res : ∀ e ∈ bm (resList st.1 (b4nib it.ln) 0),
      closed 0 e = true := fun e he2 => by
      simp only [bm, List.mem_map] at he2
      obtain ⟨p, _, rfl⟩ := he2; exact closed_byteLit _ _
  have hrescl : closed 0 (scottList (bm (resList st.1 (b4nib it.ln)
      0))) = true := closed_scottList h4res
  have qB := pairSrcCell_nf Relation.ReflTransGen.refl hln4
    hposcl h4cl
  have hcl2 : closed 0 (pairLit posT
      (scottList (bm (b4nib it.ln)))) = true :=
    closed_pairLit (closed_mono hposcl (Nat.zero_le 1))
      (closed_mono h4cl (Nat.zero_le 1))
  have qC := pairSrcCell_nf Relation.ReflTransGen.refl qB hitcl hcl2
  have hcl3 : closed 0 (pairLit it.itT (pairLit posT
      (scottList (bm (b4nib it.ln))))) = true :=
    closed_pairLit (closed_mono hitcl (Nat.zero_le 1))
      (closed_mono hcl2 (Nat.zero_le 1))
  have qD := conssCell_nf qC Relation.ReflTransGen.refl hcl3 hprepcl
  have hcl4 : closed 0 (cellLit (pairLit it.itT (pairLit posT
      (scottList (bm (b4nib it.ln))))) prepT) = true :=
    closed_cellLit hcl3 hprepcl
  have qE := pairSrcCell_nf Relation.ReflTransGen.refl qD
    hloccl hcl4
  have hcl5 : closed 0 (pairLit locT (cellLit (pairLit it.itT
      (pairLit posT (scottList (bm (b4nib it.ln))))) prepT)) = true :=
    closed_pairLit (closed_mono hloccl (Nat.zero_le 1))
      (closed_mono hcl4 (Nat.zero_le 1))
  have qF := pairSrcCell_nf qA qE hrescl hcl5
  -- semantic unfold + finish
  have hsem : p1StepSem basB it st =
      (resList st.1 (b4nib it.ln) 0, st.2.1,
       pairLit it.itT (pairLit (scottList (bm st.1))
        (scottList (bm (b4nib it.ln)))) :: st.2.2) := by
    simp [p1StepSem, hns]
  rw [hsem]
  show LRed _ (p1AccT (scottList (bm (resList st.1 (b4nib it.ln) 0)))
    locT
    (cellLit (pairLit it.itT (pairLit posT
      (scottList (bm (b4nib it.ln))))) prepT))
  exact s1.trans (s2.trans (s3.trans (hsel'.trans
    (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans
      (s9.trans qF)))))))))

-- closedness helpers ----------------------------------------------------

theorem closed_scott_bm (xs : List (Fin 16 × Fin 16)) :
    closed 0 (scottList (bm xs)) = true :=
  closed_scottList (fun _ he => closed_bm he)

theorem closed_p1AccTV (st : P1St)
    (h1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (h2 : ∀ c ∈ st.2.2, closed 0 c = true) :
    closed 0 (p1AccTV st) = true :=
  closed_pairLit (closed_mono (closed_scott_bm st.1) (Nat.zero_le 1))
    (closed_mono (closed_pairLit
      (closed_mono (closed_scottList h1) (Nat.zero_le 1))
      (closed_mono (closed_scottList h2) (Nat.zero_le 1)))
      (Nat.zero_le 1))

/-- `resList` preserves length on equal-length inputs. -/
theorem resList_len : ∀ (as bs : List (Fin 16 × Fin 16)) (c : Fin 16),
    as.length = bs.length → (resList as bs c).length = as.length := by
  intro as; induction as with
  | nil => intro bs c h; cases bs <;> simp [resList]
  | cons a as ih =>
      intro bs c h; cases bs with
      | nil => simp at h
      | cons b bs' =>
          simp only [resList, List.length_cons]
          have h' : as.length = bs'.length := by
            simpa using h
          exact congrArg Nat.succ (ih bs' _ h')

/-- pass-1 step preserves pos-length. -/
theorem p1StepSem_len (basB : List (Fin 16 × Fin 16)) (it : AsmItem)
    (st : P1St) (hl4 : st.1.length = 4) :
    (p1StepSem basB it st).1.length = 4 := by
  by_cases hns : it.ns = lblNibs
  · cases hrr : it.rrCs with
    | nil => simp [p1StepSem, hns, hrr, hl4]
    | cons nm rest => simp [p1StepSem, hns, hrr, hl4]
  · have hb4' : st.1.length = (b4nib it.ln).length := by
      simp [b4nib, hl4]
    have hlen := resList_len st.1 (b4nib it.ln) 0 hb4'
    simp [p1StepSem, hns]
    rw [hlen]; exact hl4

/-- pass-1 step preserves loc/prep closedness. -/
theorem p1StepSem_wf (encT zrvT : LTerm)
    (basB : List (Fin 16 × Fin 16)) (it : AsmItem) (st : P1St)
    (hit : AsmItem.V encT zrvT it)
    (hrrn : it.ns = lblNibs → ∃ nm rest, it.rrCs = nm :: rest)
    (h1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (h2 : ∀ c ∈ st.2.2, closed 0 c = true) :
    (∀ c ∈ (p1StepSem basB it st).2.1, closed 0 c = true) ∧
    (∀ c ∈ (p1StepSem basB it st).2.2, closed 0 c = true) := by
  obtain ⟨⟨_, _, _, _, _, _, _⟩, hitcl, hrrCs, _, _, _, _⟩ := hit
  by_cases hns : it.ns = lblNibs
  · obtain ⟨nm, rest, hrr⟩ := hrrn hns
    have hnmc : closed 0 nm = true := hrrCs nm (by rw [hrr]; simp)
    simp [p1StepSem, hns, hrr]
    refine ⟨⟨closed_pairLit (closed_mono hnmc (Nat.zero_le 1))
        (closed_mono (closed_scott_bm _) (Nat.zero_le 1)), h1⟩,
      ⟨closed_pairLit (closed_mono hitcl (Nat.zero_le 1))
        (closed_mono (closed_pairLit
          (closed_mono (closed_scott_bm _) (Nat.zero_le 1))
          (closed_mono closed_nilL (Nat.zero_le 1)))
          (Nat.zero_le 1)), h2⟩⟩
  · simp [p1StepSem, hns]
    refine ⟨h1, closed_pairLit (closed_mono hitcl (Nat.zero_le 1))
        (closed_mono (closed_pairLit
          (closed_mono (closed_scott_bm _) (Nat.zero_le 1))
          (closed_mono (closed_scott_bm _) (Nat.zero_le 1)))
          (Nat.zero_le 1)), h2⟩

/-- combined one-step pass-1 evaluation. -/
theorem p1_step_eval (encT zrvT basT accT : LTerm)
    (basB : List (Fin 16 × Fin 16)) (it : AsmItem) (st : P1St)
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true) (ha : closed 0 accT = true)
    (hit : AsmItem.V encT zrvT it)
    (hacc : LRed accT (p1AccTV st))
    (hbas : LRed basT (scottList (bm basB)))
    (hb4 : basB.length = 4) (hpos4 : st.1.length = 4)
    (hrrn : it.ns = lblNibs → ∃ nm rest, it.rrCs = nm :: rest)
    (hst1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (hst2 : ∀ c ∈ st.2.2, closed 0 c = true) :
    LRed (aps (p1StepT encT zrvT basT) [accT, it.itT])
         (p1AccTV (p1StepSem basB it st)) := by
  by_cases hns : it.ns = lblNibs
  · obtain ⟨nm, rest, hrr⟩ := hrrn hns
    exact p1_label_eval encT zrvT basT accT basB it st nm rest
      he hz hb ha hit hacc hbas hb4 hpos4 hns hrr hst1 hst2
  · exact p1_insn_eval encT zrvT basT accT basB it st
      he hz hb ha hit hacc hpos4 hns hst1 hst2

/-- fold-start congruence over `AsmItem`s. -/
theorem p1Fold_cong (st : LTerm) : ∀ (items : List AsmItem) (X a : LTerm),
    LRed X a →
    LRed (items.foldl (fun acc e => aps st [acc, e.itT]) X)
         (items.foldl (fun acc e => aps st [acc, e.itT]) a) := by
  intro items; induction items with
  | nil => intro X a h; exact h
  | cons e its ih =>
      intro X a h
      exact ih _ _ (LRed_app_left (LRed_app_right h))

/-- item-level pass-1 fold evaluation. -/
theorem p1Fold_eval (encT zrvT basT : LTerm)
    (basB : List (Fin 16 × Fin 16))
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4) :
    ∀ (items : List AsmItem),
    (∀ it ∈ items, AsmItem.V encT zrvT it) →
    (∀ it ∈ items, it.ns = lblNibs → ∃ nm rest, it.rrCs = nm :: rest) →
    ∀ (st : P1St) (accT : LTerm),
      (∀ c ∈ st.2.1, closed 0 c = true) →
      (∀ c ∈ st.2.2, closed 0 c = true) →
      st.1.length = 4 →
      LRed accT (p1AccTV st) → closed 0 accT = true →
      LRed (items.foldl (fun acc e =>
              aps (p1StepT encT zrvT basT) [acc, e.itT]) accT)
           (p1AccTV (items.foldl (fun s i => p1StepSem basB i s) st)) := by
  intro items
  induction items with
  | nil => intro _ _ st accT _ _ _ hacc _; exact hacc
  | cons it items ih =>
      intro hV hrrn st accT hw1 hw2 hl4 hacc haccl
      simp only [List.foldl_cons]
      have hVit := hV it (List.mem_cons_self)
      have hrrit := hrrn it (List.mem_cons_self)
      have hVtl : ∀ i ∈ items, AsmItem.V encT zrvT i := fun i hi =>
        hV i (List.mem_cons_of_mem _ hi)
      have hrrtl : ∀ i ∈ items, i.ns = lblNibs →
          ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
        hrrn i (List.mem_cons_of_mem _ hi)
      have hstep := p1_step_eval encT zrvT basT accT basB it st
        he hz hb haccl hVit hacc hbas hb4 hl4 hrrit hw1 hw2
      have hwf := p1StepSem_wf encT zrvT basB it st hVit hrrit hw1 hw2
      have hlen' := p1StepSem_len basB it st hl4
      have hcl' := closed_p1AccTV _ hwf.1 hwf.2
      have hcong := p1Fold_cong (p1StepT encT zrvT basT) items
        (aps (p1StepT encT zrvT basT) [accT, it.itT])
        (p1AccTV (p1StepSem basB it st)) hstep
      exact hcong.trans
        (ih hVtl hrrtl (p1StepSem basB it st)
          (p1AccTV (p1StepSem basB it st)) hwf.1 hwf.2 hlen'
          Relation.ReflTransGen.refl hcl')

/-- well-formedness preservation across an item fold. -/
theorem p1Fold_wf (encT zrvT : LTerm) (basB : List (Fin 16 × Fin 16)) :
    ∀ (items : List AsmItem),
    (∀ it ∈ items, AsmItem.V encT zrvT it) →
    (∀ it ∈ items, it.ns = lblNibs → ∃ nm rest, it.rrCs = nm :: rest) →
    ∀ (st : P1St),
      (∀ c ∈ st.2.1, closed 0 c = true) →
      (∀ c ∈ st.2.2, closed 0 c = true) →
      st.1.length = 4 →
      (∀ c ∈ (items.foldl (fun s i => p1StepSem basB i s) st).2.1,
          closed 0 c = true) ∧
      (∀ c ∈ (items.foldl (fun s i => p1StepSem basB i s) st).2.2,
          closed 0 c = true) ∧
      (items.foldl (fun s i => p1StepSem basB i s) st).1.length = 4 := by
  intro items
  induction items with
  | nil => intro _ _ st h1 h2 hl4; exact ⟨h1, h2, hl4⟩
  | cons it items ih =>
      intro hV hrrn st h1 h2 hl4
      simp only [List.foldl_cons]
      have hVit := hV it (List.mem_cons_self)
      have hrrit := hrrn it (List.mem_cons_self)
      have hVtl : ∀ i ∈ items, AsmItem.V encT zrvT i := fun i hi =>
        hV i (List.mem_cons_of_mem _ hi)
      have hrrtl : ∀ i ∈ items, i.ns = lblNibs →
          ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
        hrrn i (List.mem_cons_of_mem _ hi)
      exact ih hVtl hrrtl (p1StepSem basB it st)
        (p1StepSem_wf encT zrvT basB it st hVit hrrit h1 h2).1
        (p1StepSem_wf encT zrvT basB it st hVit hrrit h1 h2).2
        (p1StepSem_len basB it st hl4)

/-- `fragstep·acc·fr → FOLDL p1step fr acc` — two betas. -/
theorem fragStep_open (e z b aT frT : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hb : closed 0 b = true) (ha : closed 0 aT = true)
    (hf : closed 0 frT = true) :
    LRed (aps (fragStepT e z b) [aT, frT])
      (aps foldlL [p1StepT e z b, frT, aT]) := by
  have ca : ∀ c, closed c aT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have cf : ∀ c, closed c frT = true := fun c =>
    closed_mono hf (Nat.zero_le c)
  have c1 : ∀ c, closed c foldlL = true := closed_foldlL_any
  have c2 : ∀ c, closed c (p1StepT e z b) = true := fun c =>
    closed_p1StepT c he hz hb
  exact LRed_of_hsteps (k := 2) (by
    simp [fragStepT, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed, ca, cf, c1, c2])

/-- per-fragment pass-1 evaluation. -/
theorem p1Frag_eval (encT zrvT basT accT frT : LTerm)
    (basB : List (Fin 16 × Fin 16)) (its : List AsmItem) (st : P1St)
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true) (ha : closed 0 accT = true)
    (hf : closed 0 frT = true)
    (hfrT : LRed frT (scottList (its.map AsmItem.itT)))
    (hV : ∀ it ∈ its, AsmItem.V encT zrvT it)
    (hrrn : ∀ it ∈ its, it.ns = lblNibs →
        ∃ nm rest, it.rrCs = nm :: rest)
    (hacc : LRed accT (p1AccTV st))
    (hbas : LRed basT (scottList (bm basB)))
    (hb4 : basB.length = 4)
    (hw1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (hw2 : ∀ c ∈ st.2.2, closed 0 c = true)
    (hl4 : st.1.length = 4) :
    LRed (aps (fragStepT encT zrvT basT) [accT, frT])
         (p1AccTV (its.foldl (fun s i => p1StepSem basB i s) st)) := by
  have s1 := fragStep_open encT zrvT basT accT frT he hz hb ha hf
  have hcell : ∀ e ∈ its.map AsmItem.itT, closed 0 e = true :=
    fun t ht => by
      simp only [List.mem_map] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      exact (hV i hi).2.1
  have hscl : closed 0 (scottList (its.map AsmItem.itT)) = true :=
    closed_scottList hcell
  have hpscl : closed 0 (p1StepT encT zrvT basT) = true :=
    closed_p1StepT 0 he hz hb
  have s2 : LRed
      (aps foldlL [p1StepT encT zrvT basT, frT, accT])
      (aps foldlL [p1StepT encT zrvT basT,
        scottList (its.map AsmItem.itT), accT]) :=
    LRed_app_left (LRed_app_right hfrT)
  have s3 := foldl_to_ggb _ _ _ hpscl hscl ha
  have s4 := fold_run _ hpscl _ _ hcell ha
  have s5 : LRed ((its.map AsmItem.itT).foldl
        (fun acc t => .app (.app (p1StepT encT zrvT basT) acc) t) accT)
      (its.foldl (fun acc e =>
        aps (p1StepT encT zrvT basT) [acc, e.itT]) accT) := by
    rw [List.foldl_map]
    exact Relation.ReflTransGen.refl
  have s6 := p1Fold_eval encT zrvT basT basB he hz hb hbas hb4 its
    hV hrrn st accT hw1 hw2 hl4 hacc ha
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))

/-- fold-start congruence over fragment cells. -/
theorem p1FragFold_cong (st : LTerm) :
    ∀ (fcs : List LTerm) (X a : LTerm), LRed X a →
    LRed (fcs.foldl (fun acc e => aps st [acc, e]) X)
         (fcs.foldl (fun acc e => aps st [acc, e]) a) := by
  intro fcs; induction fcs with
  | nil => intro X a h; exact h
  | cons e fcs ih =>
      intro X a h
      exact ih _ _ (LRed_app_left (LRed_app_right h))

/-- semantic pass-1 over a whole program (list of fragments). -/
def p1ProgSem (basB : List (Fin 16 × Fin 16))
    (frs : List (List AsmItem)) (st : P1St) : P1St :=
  frs.foldl (fun s its => its.foldl (fun s i => p1StepSem basB i s) s) st

/-- fragment-level pass-1 fold evaluation. -/
theorem p1FoldFrag_eval (encT zrvT basT : LTerm)
    (basB : List (Fin 16 × Fin 16))
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4) :
    ∀ (fcs : List LTerm) (frs : List (List AsmItem)),
    List.Forall₂ (fun fT its =>
        LRed fT (scottList (its.map AsmItem.itT)) ∧
        closed 0 fT = true) fcs frs →
    (∀ it ∈ frs.flatten, AsmItem.V encT zrvT it) →
    (∀ it ∈ frs.flatten, it.ns = lblNibs →
        ∃ nm rest, it.rrCs = nm :: rest) →
    ∀ (st : P1St) (accT : LTerm),
      (∀ c ∈ st.2.1, closed 0 c = true) →
      (∀ c ∈ st.2.2, closed 0 c = true) →
      st.1.length = 4 →
      LRed accT (p1AccTV st) → closed 0 accT = true →
      LRed (fcs.foldl (fun acc e =>
              aps (fragStepT encT zrvT basT) [acc, e]) accT)
           (p1AccTV (p1ProgSem basB frs st)) := by
  intro fcs frs hfr
  induction hfr with
  | nil => intro _ _ st accT _ _ _ hacc _; exact hacc
  | cons hp hr ih =>
      intro hV hrrn st accT hw1 hw2 hl4 hacc haccl
      rename_i fT its fcs' frs'
      obtain ⟨hfrT, hfcl⟩ := hp
      simp only [List.foldl_cons]
      have hVh : ∀ i ∈ its, AsmItem.V encT zrvT i := fun i hi =>
        hV i (List.mem_flatten.mpr ⟨its, List.mem_cons_self, hi⟩)
      have hrrh : ∀ i ∈ its, i.ns = lblNibs →
          ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
        hrrn i (List.mem_flatten.mpr ⟨its, List.mem_cons_self, hi⟩)
      have hVr : ∀ i ∈ frs'.flatten, AsmItem.V encT zrvT i :=
        fun i hi => hV i (List.mem_flatten.mpr (by
          obtain ⟨l', hl', hmem⟩ := List.mem_flatten.mp hi
          exact ⟨l', List.mem_cons_of_mem _ hl', hmem⟩))
      have hrrr : ∀ i ∈ frs'.flatten, i.ns = lblNibs →
          ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
        hrrn i (List.mem_flatten.mpr (by
          obtain ⟨l', hl', hmem⟩ := List.mem_flatten.mp hi
          exact ⟨l', List.mem_cons_of_mem _ hl', hmem⟩))
      have hstep := p1Frag_eval encT zrvT basT accT fT basB its st
        he hz hb haccl hfcl hfrT hVh hrrh hacc hbas hb4 hw1 hw2 hl4
      have hwf' := p1Fold_wf encT zrvT basB its hVh hrrh st hw1 hw2 hl4
      have hcl' := closed_p1AccTV _ hwf'.1 hwf'.2.1
      have hcong := p1FragFold_cong (fragStepT encT zrvT basT) fcs'
        (aps (fragStepT encT zrvT basT) [accT, fT])
        (p1AccTV (its.foldl (fun s i => p1StepSem basB i s) st)) hstep
      show LRed (fcs'.foldl (fun acc e =>
            aps (fragStepT encT zrvT basT) [acc, e])
            (aps (fragStepT encT zrvT basT) [accT, fT])) _
      exact hcong.trans
        (ih hVr hrrr (its.foldl (fun s i => p1StepSem basB i s) st)
          (p1AccTV (its.foldl (fun s i => p1StepSem basB i s) st))
          hwf'.1 hwf'.2.1 hwf'.2.2
          Relation.ReflTransGen.refl hcl')

/-- pass-1 initial accumulator semantics. -/
def p1Init : P1St := (b4zeroBytes, [], [])

theorem p1Init_nf : LRed p1InitT (p1AccTV p1Init) := by
  have hin : LRed (aps pairSrcL [klL, klL]) (pairLit klL klL) :=
    pairSrc_nf _ _ closed_klL closed_klL
  have hcl : closed 0 (pairLit klL klL) = true :=
    closed_pairLit (closed_mono closed_klL (Nat.zero_le 1))
      (closed_mono closed_klL (Nat.zero_le 1))
  have hrp : ∀ e ∈ List.replicate 4 (byteLit 0 0),
      closed 0 e = true := fun e he => by
    simp only [List.mem_replicate] at he
    obtain ⟨_, rfl⟩ := he; exact closed_byteLit _ _
  have hout := pairSrcCell_nf b4z_nf hin
    (closed_scottList hrp) hcl
  show LRed p1InitT (pairLit
    (scottList (List.replicate 4 (byteLit 0 0))) (pairLit klL klL))
  exact hout

/-- pass-1 whole-program evaluation: `p1ValT` reduces to the
    semantic fold result. -/
theorem p1_eval (encT zrvT basT progT : LTerm)
    (basB : List (Fin 16 × Fin 16))
    (fcs : List LTerm) (frs : List (List AsmItem))
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4)
    (hprog : LRed progT (scottList fcs)) (_hprogcl : closed 0 progT = true)
    (hfcl : ∀ e ∈ fcs, closed 0 e = true)
    (hfr : List.Forall₂ (fun fT its =>
        LRed fT (scottList (its.map AsmItem.itT)) ∧
        closed 0 fT = true) fcs frs)
    (hV : ∀ it ∈ frs.flatten, AsmItem.V encT zrvT it)
    (hrrn : ∀ it ∈ frs.flatten, it.ns = lblNibs →
        ∃ nm rest, it.rrCs = nm :: rest) :
    LRed (p1ValT encT zrvT progT basT)
         (p1AccTV (p1ProgSem basB frs p1Init)) := by
  have hpIcl : closed 0 p1InitT = true := closed_p1InitT 0
  have hfrscl : closed 0 (fragStepT encT zrvT basT) = true :=
    closed_fragStepT 0 he hz hb
  have hsccl : closed 0 (scottList fcs) = true :=
    closed_scottList hfcl
  have s1 : LRed (p1ValT encT zrvT progT basT)
      (ggbA (fragStepT encT zrvT basT) (scottList fcs) p1InitT) :=
    (LRed_app_left (LRed_app_right hprog)).trans
      (foldl_to_ggb _ _ _ hfrscl hsccl hpIcl)
  have s2 := fold_run _ hfrscl fcs p1InitT hfcl hpIcl
  have s3 := p1FoldFrag_eval encT zrvT basT basB he hz hb hbas hb4
    fcs frs hfr hV hrrn p1Init p1InitT
    (fun c hc => nomatch hc)
    (fun c hc => nomatch hc)
    rfl p1Init_nf hpIcl
  exact s1.trans (s2.trans s3)


#print axioms p1_label_eval
#print axioms p1_insn_eval
#print axioms p1_step_eval
#print axioms p1Fold_eval
#print axioms p1Frag_eval
#print axioms p1FoldFrag_eval
#print axioms p1_eval

#print axioms nib2b4_eval_scott
#print axioms p1Step_open
#print axioms p1Disp_open
#print axioms p1LabelCont_apply
#print axioms p1LabelIC2_apply
#print axioms p1InsnOuter_apply
#print axioms p1InsnContS_apply
#print axioms p1InsnIC2_apply
#print axioms resList_len
#print axioms p1StepSem_len
#print axioms p1StepSem_wf
#print axioms p1Fold_cong
#print axioms p1Fold_wf
#print axioms fragStep_open
#print axioms p1FragFold_cong
#print axioms p1Init_nf
#print axioms pairSrcCell_nf

#print axioms eqStr_eval
#print axioms len_eval
#print axioms b4add_eval_scott
#print axioms cellLit_apply2
#print axioms pairLit_apply
#print axioms pairLit_snd
#print axioms conssCell_nf
#print axioms head_cell
#print axioms boolLit_sel
#print axioms foldl_to_ggb
#print axioms cell_unfold
#print axioms nil_unfold
#print axioms ggbA
#print axioms closed_bm
#print axioms closed_p1StepT
#print axioms closed_fragStepT
#print axioms closed_p1InitT
#print axioms closed_pairLit
#print axioms closed_scottList
#print axioms LRed_of_hsteps
#print axioms p1InitT
#print axioms fragStepT
#print axioms p1ValT

end ISAR
