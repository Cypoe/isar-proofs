import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- Batch M layer 1: assembleOf primitives —
--   nibnot/notb (byte complement), nib2b4 (nibble→bytes4 lift),
--   churchS/len (succ + list length), eqStr, alook, b4sub.
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
  -- notbL·cell → cell·(λl.λh. PAIR (NN l)(NN h)) → (λl.λh…) lo hi
  --   → PAIR (NN lo) (NN hi) → pairLit (nn lo) (nn hi) — but the
  --   args are `nibnotL·nibLit`-apps; keep them thunked: the pairLit
  --   body has the app-cells.  Instead reduce past NN too.
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
    -- pairLit (nibLit ..) (nibLit ..) defeq byteLit
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
  -- unwind the conss chain into scottList form
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

end ISAR
