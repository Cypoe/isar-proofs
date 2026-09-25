import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- Batch M layer 2: succL/succChain/lenL + b4sub ripple
-- ============================================================

/-- `_SUCC_SRC = λn.λf.λx. f (n f x)` — Church successor. -/
def succL : LTerm :=
  .abs (.abs (.abs (.app (.var 1) (aps (.var 2) [.var 1, .var 0]))))

theorem closed_succL : closed 0 succL = true := by decide

/-- `succL·t` applied `n` times around `acc` — the LEN normal form
    (a `succL`-tower, not `churchL n`: same observation behavior). -/
def succChain (acc : LTerm) : Nat → LTerm
  | 0 => acc
  | n + 1 => .app succL (succChain acc n)

theorem closed_succChain {acc : LTerm} (ha : closed 0 acc = true)
    (n : Nat) : closed 0 (succChain acc n) = true := by
  induction n with
  | zero => exact ha
  | succ n ih => exact closed_app closed_succL ih

/-- `succL·t·f·z →* f·(t·f·z)` — the successor unfold. -/
theorem succL_app3 (t f z : LTerm) (ht : closed 0 t = true)
    (hf : closed 0 f = true) (hz : closed 0 z = true) :
    LRed (aps (.app succL t) [f, z]) (.app f (aps t [f, z])) :=
  LRed_of_hsteps (k := 3) (by
    simp [succL, aps, List.foldl, hsteps, hstep, subst,
          shift_of_closed0 ht, shift_of_closed0 hf,
          shift_of_closed0 hz,
          subst_of_closed0 ht, subst_of_closed0 hf])

/-- tower iteration: `succChain acc n ·f·z →* iterL f (acc·f·z) n`. -/
theorem succChain_iter : ∀ (n : Nat) (acc f z : LTerm),
    closed 0 acc = true → closed 0 f = true →
    closed 0 z = true →
    LRed (aps (succChain acc n) [f, z])
         (iterL f (aps acc [f, z]) n) := by
  intro n
  induction n with
  | zero => intro acc f z _ _ _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro acc f z hacc hf hz
    have hcl : closed 0 (succChain acc n) = true :=
      closed_succChain hacc n
    have s1 : LRed (aps (succChain acc (n + 1)) [f, z])
        (.app f (aps (succChain acc n) [f, z])) :=
      succL_app3 _ f z hcl hf hz
    exact s1.trans (LRed_app_right (ih acc f z hacc hf hz))

/-- inner-chain congruence: reducing the seed of an iterL. -/
theorem iterL_congr (f : LTerm) (n : Nat) {a b : LTerm}
    (h : LRed a b) : LRed (iterL f a n) (iterL f b n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact LRed_app_right ih

/-- `succChain KI n` is a Church numeral: `·f·z →* f^n z`. -/
theorem succTower_iter (n : Nat) (f z : LTerm)
    (hf : closed 0 f = true) (hz : closed 0 z = true) :
    LRed (aps (succChain kilL n) [f, z]) (iterL f z n) :=
  (succChain_iter n kilL f z closed_kilL hf hz).trans
    (iterL_congr f n (kilL_apply2 f z))

/-- `_LEN` step: `λa.λc. SUCC a` (element ignored) — distinct from
    `lenStepL` (the `B4INC` variant used by `lenb4L`). -/
def lenStepCL : LTerm := .abs (.abs (.app succL (.var 1)))

theorem closed_lenStepCL : closed 0 lenStepCL = true := by decide

theorem lenStepC_eval (acc e : LTerm) (ha : closed 0 acc = true)
    (_he : closed 0 e = true) :
    LRed (.app (.app lenStepCL acc) e) (.app succL acc) ∧
    closed 0 (.app succL acc) = true :=
  ⟨LRed_of_hsteps (k := 2) (by
     simp [lenStepCL, hsteps, hstep, subst,
           shift_of_closed0 ha, subst_of_closed0 ha,
           subst_of_closed0 closed_succL]),
   closed_app closed_succL ha⟩

/-- `_LEN = λl. FOLDL (λa.λc. SUCC a) l KI`. -/
def lenL : LTerm :=
  .abs (aps foldlL [lenStepCL, .var 0, kilL])

theorem closed_lenL : closed 0 lenL = true := by decide

/-- `succChain` absorbs a leading `succL` into the count. -/
theorem succChain_base (n : Nat) (acc : LTerm) :
    succChain (.app succL acc) n = succChain acc (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show LTerm.app succL (succChain (LTerm.app succL acc) n)
       = LTerm.app succL (succChain acc (n + 1))
    rw [ih]

theorem foldl_succChain (cs : List LTerm) (acc : LTerm) :
    List.foldl (fun a _ => .app succL a) acc cs =
      succChain acc cs.length := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs' ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, succChain_base]

/-- `LEN·(scottList cs) →* succChain KI cs.length` — the Church
    numeral `cs.length` in succ-tower form. -/
theorem len_eval (cs : List LTerm)
    (hcl : ∀ e ∈ cs, closed 0 e = true) :
    LRed (.app lenL (scottList cs)) (succChain kilL cs.length) := by
  have e1 : LRed (.app lenL (scottList cs))
      (aps foldlL [lenStepCL, scottList cs, kilL]) :=
    LRed_of_hsteps (k := 1) (by
      simp [lenL, aps, List.foldl, hsteps, hstep, subst,
            shift_of_closed0, subst_of_closed0,
            closed_foldlL, closed_lenStepCL, closed_kilL,
            closed_scottList hcl])
  refine e1.trans ?_
  have h2 := fold_eval lenStepCL (fun a _ => .app succL a)
    closed_lenStepCL lenStepC_eval (scottList cs) kilL cs
    (closed_scottList hcl) closed_kilL Relation.ReflTransGen.refl hcl
  rw [foldl_succChain] at h2
  exact h2

-- b4sub ripple --------------------------------------------------------------

/-- `_B4SUB` step: `b4stepL` with `ADDBC x (NOTB hb) cy`.  Binder
    indices identical to `b4stepL`. -/
def b4subStepL : LTerm :=
  .abs (.abs
    (.app (.var 1)
      (.abs (.abs
        (.app (.var 0)
          (.abs (.abs
            (.app (.app (.var 3) klL)
              (.abs (.abs
                (.app (aps addbcL
                        [.var 6, .app notbL (.var 1), .var 3])
                  (.abs (.abs
                    (aps pairSrcL
                      [.var 2,
                       aps pairSrcL [.app b2nL (.var 0),
                                     aps conssL [.var 1,
                                     .var 4]]]))))))))))))))

theorem closed_b4subStepL : closed 0 b4subStepL = true := by decide

/-- `_B4SUB = λa.λb. (FOLDL·substep·a·(pair b (pair sel1 K)))·fin` —
    carry-in `sel1` (two's complement). -/
def b4subL : LTerm :=
  .abs (.abs (.app
    (aps foldlL [b4subStepL, .var 1,
      aps pairSrcL [.var 0, aps pairSrcL [nibLit 1, klL]]])
    b4finL))

theorem closed_b4subL : closed 0 b4subL = true := by decide

/-- carry after subtract-processing `as` against `bs` from `cn`. -/
def subCarryAfter : List (Fin 16 × Fin 16) → List (Fin 16 × Fin 16) →
    Fin 16 → Fin 16
  | [], _, cn => cn
  | a :: as, b :: bs, cn =>
      subCarryAfter as bs
        (byteStepN a (nibNot b.1, nibNot b.2) cn).2
  | _ :: _, [], cn => cn

/-- subtraction result bytes in processing order. -/
def subResList : List (Fin 16 × Fin 16) → List (Fin 16 × Fin 16) →
    Fin 16 → List (Fin 16 × Fin 16)
  | [], _, _ => []
  | a :: as, b :: bs, cn =>
      (byteStepN a (nibNot b.1, nibNot b.2) cn).1 ::
        subResList as bs (byteStepN a (nibNot b.1, nibNot b.2) cn).2
  | _ :: _, [], _ => []

/-- `b4subStepL` spine: destructures state and b-cell, lands at the
    `ADDBC x (NOTB hb) cy` call applied to the rebuild continuation. -/
theorem b4substep_spine_scott (h bh bt cn acc : LTerm)
    (hh : closed 0 h = true) (hbh : closed 0 bh = true)
    (hbt : closed 0 bt = true) (hcn : closed 0 cn = true)
    (hacc : closed 0 acc = true) :
    LRed (aps b4subStepL
           [pairLit (cellLit bh bt) (pairLit cn acc), h])
         (.app (aps addbcL [h, .app notbL bh, cn])
            (b4stepCont bt acc)) :=
  LRed_of_hsteps (k := 12) (by
    simp [b4subStepL, pairLit, cellLit, addbcL, b4stepCont, letsL, aps,
          List.foldl, hsteps, hstep, subst, shift,
          shift_of_closed0, subst_of_closed0,
          closed_klL, closed_pairSrcL, closed_b2nL, closed_conssL,
          closed_nibAddL, closed_nibCarryL, closed_orL, closed_notbL,
          hh, hbh, hbt, hcn, hacc])

/-- full sub byte-step on a cellLit-carried state. -/
theorem b4substep_eval_scott (xl xh yl yh cn : Fin 16) (bt acc : LTerm)
    (hbt : closed 0 bt = true) (hacc : closed 0 acc = true) :
    LRed (aps b4subStepL
           [pairLit (cellLit (byteLit yl yh) bt)
                    (pairLit (nibLit cn) acc),
            byteLit xl xh])
         (pairLit bt
           (pairLit
             (nibLit (byteStepN (xl, xh)
               (nibNot yl, nibNot yh) cn).2)
             (cellLit
               (byteLit (byteStepN (xl, xh)
                 (nibNot yl, nibNot yh) cn).1.1
                 (byteStepN (xl, xh)
                   (nibNot yl, nibNot yh) cn).1.2)
               acc))) := by
  have hm := b4substep_spine_scott (byteLit xl xh) (byteLit yl yh) bt
    (nibLit cn) acc
    (closed_byteLit xl xh) (closed_byteLit yl yh) hbt
    (closed_nibLit cn) hacc
  have hnb : LRed (aps addbcL [byteLit xl xh,
        .app notbL (byteLit yl yh), nibLit cn])
      (aps addbcL [byteLit xl xh,
        byteLit (nibNot yl) (nibNot yh), nibLit cn]) :=
    LRed_app (LRed_app Relation.ReflTransGen.refl
      (notb_eval yl yh)) Relation.ReflTransGen.refl
  have h1 := addbc_eval xl xh (nibNot yl) (nibNot yh) cn
  have h2 : LRed (.app (aps addbcL [byteLit xl xh,
                     byteLit (nibNot yl) (nibNot yh),
                     nibLit cn]) (b4stepCont bt acc))
      (.app (pairLit
         (byteLit ⟨(xl.val + (nibNot yl).val + cn.val) % 16,
                    Nat.mod_lt _ (by omega)⟩
                  ⟨(xh.val + (nibNot yh).val
                      + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
                         then 1 else 0)) % 16,
                    Nat.mod_lt _ (by omega)⟩)
         (boolLit (decide (16 ≤ xh.val + (nibNot yh).val
             + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
                then 1 else 0)))))
        (b4stepCont bt acc)) :=
    LRed_app_left (h1.trans (pairSrc_nf _ _
      (closed_byteLit _ _) (closed_boolLit _)))
  refine hm.trans ((LRed_app_left hnb).trans (h2.trans ?_))
  refine (pairLit_apply2 _ _ _ _
    (closed_byteLit _ _) (closed_boolLit _) hbt hacc).trans ?_
  have hb2n : LRed (.app b2nL
        (boolLit (decide (16 ≤ xh.val + (nibNot yh).val
            + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
               then 1 else 0)))))
      (nibLit (byteStepN (xl, xh) (nibNot yl, nibNot yh) cn).2) := by
    refine (b2n_correct _).trans (nibLit_eq_red ?_)
    apply Fin.ext
    simp [byteStepN, lowCarry, apply_ite, decide_eq_true_eq]
    split <;> simp_all
  have hcell : LRed (aps conssL
        [byteLit ⟨(xl.val + (nibNot yl).val + cn.val) % 16,
                   Nat.mod_lt _ (by omega)⟩
                 ⟨(xh.val + (nibNot yh).val
                     + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
                        then 1 else 0)) % 16,
                   Nat.mod_lt _ (by omega)⟩, acc])
      (cellLit (byteLit (byteStepN (xl, xh)
                        (nibNot yl, nibNot yh) cn).1.1
                        (byteStepN (xl, xh)
                          (nibNot yl, nibNot yh) cn).1.2) acc) := by
    refine (conss_nf _ _ (closed_byteLit _ _) hacc).trans ?_
    rw [show (⟨(xl.val + (nibNot yl).val + cn.val) % 16,
               Nat.mod_lt _ (by omega)⟩ : Fin 16)
          = (byteStepN (xl, xh) (nibNot yl, nibNot yh) cn).1.1
        from Fin.ext rfl,
        show (⟨(xh.val + (nibNot yh).val
                 + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
                    then 1 else 0)) % 16,
               Nat.mod_lt _ (by omega)⟩ : Fin 16)
          = (byteStepN (xl, xh) (nibNot yl, nibNot yh) cn).1.2
        from Fin.ext rfl]
  have hinner : LRed (aps pairSrcL
        [.app b2nL (boolLit (decide (16 ≤ xh.val + (nibNot yh).val
            + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
               then 1 else 0)))),
         aps conssL
           [byteLit ⟨(xl.val + (nibNot yl).val + cn.val) % 16,
                      Nat.mod_lt _ (by omega)⟩
                    ⟨(xh.val + (nibNot yh).val
                        + (if 16 ≤ xl.val + (nibNot yl).val + cn.val
                           then 1 else 0)) % 16,
                      Nat.mod_lt _ (by omega)⟩, acc]])
      (pairLit (nibLit (byteStepN (xl, xh)
                       (nibNot yl, nibNot yh) cn).2)
               (cellLit (byteLit (byteStepN (xl, xh)
                                 (nibNot yl, nibNot yh) cn).1.1
                                 (byteStepN (xl, xh)
                                   (nibNot yl, nibNot yh) cn).1.2)
                 acc)) :=
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

/-- sub fold over `cs` zipped against `bs` — mirror of
    `b4fold_run_scott`. -/
theorem b4subfold_run_scott : ∀ (cs : List (Fin 16 × Fin 16))
    (bs : List (Fin 16 × Fin 16)) (cn : Fin 16) (acc : LTerm),
    cs.length ≤ bs.length → closed 0 acc = true →
    LRed (ggbA b4subStepL
           (scottList (cs.map (fun p => byteLit p.1 p.2)))
           (pairLit (scottList (bs.map (fun p => byteLit p.1 p.2)))
             (pairLit (nibLit cn) acc)))
         (pairLit (scottList ((bs.drop cs.length).map
                    (fun p => byteLit p.1 p.2)))
           (pairLit (nibLit (subCarryAfter cs bs cn))
             ((subResList cs bs cn).reverse.foldr
               (fun p t => cellLit (byteLit p.1 p.2) t) acc))) := by
  intro cs
  induction cs with
  | nil =>
    intro bs cn acc _ hacc
    simp only [scottList, List.map_nil, List.foldr_nil,
               subCarryAfter, subResList, List.reverse_nil]
    have hcl : ∀ e ∈ bs.map (fun p => byteLit p.1 p.2),
        closed 0 e = true := fun e he => by
      simp only [List.mem_map] at he
      obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _
    exact nil_unfold b4subStepL _ closed_b4subStepL
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
          (pairLit (scottList ((b :: bs').map
            (fun p => byteLit p.1 p.2)))
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
      have hstep := b4substep_eval_scott c.1 c.2 b.1 b.2 cn
        (scottList (bs'.map (fun p => byteLit p.1 p.2))) acc
        (closed_scottList (fun e he => by
          simp only [List.mem_map] at he
          obtain ⟨q, _, rfl⟩ := he; exact closed_byteLit _ _)) hacc
      refine (cell_unfold b4subStepL _ _ _ closed_b4subStepL
        (closed_byteLit _ _) (closed_scottList htail) hstate0).trans ?_
      refine (LRed_app_right hstep).trans ?_
      have hih := ih bs'
        (byteStepN (c.1, c.2) (nibNot b.1, nibNot b.2) cn).2
        (cellLit (byteLit (byteStepN (c.1, c.2)
                          (nibNot b.1, nibNot b.2) cn).1.1
                          (byteStepN (c.1, c.2)
                            (nibNot b.1, nibNot b.2) cn).1.2) acc)
        hlen (closed_cellLit (closed_byteLit _ _) hacc)
      rw [show pairLit (scottList (((b :: bs').drop
                (c :: cs').length).map
                (fun p => byteLit p.1 p.2)))
            (pairLit (nibLit (subCarryAfter (c :: cs') (b :: bs') cn))
              ((subResList (c :: cs') (b :: bs') cn).reverse.foldr
                (fun p t => cellLit (byteLit p.1 p.2) t) acc))
          = pairLit (scottList ((bs'.drop cs'.length).map
                (fun p => byteLit p.1 p.2)))
            (pairLit (nibLit (subCarryAfter cs' bs'
                (byteStepN c (nibNot b.1, nibNot b.2) cn).2))
              ((subResList cs' bs'
                (byteStepN c (nibNot b.1, nibNot b.2) cn).2).reverse.foldr
                (fun p t => cellLit (byteLit p.1 p.2) t)
                (cellLit (byteLit (byteStepN c
                          (nibNot b.1, nibNot b.2) cn).1.1
                          (byteStepN c
                            (nibNot b.1, nibNot b.2) cn).1.2) acc)))
        from by
          simp [subCarryAfter, subResList, List.length_cons,
                List.reverse_cons, List.foldr_append]]
      exact hih

/-- `B4SUB` on scottList-carried operands: `a − b` mod 2³² via
    complement + carry-in 1. -/
theorem b4sub_eval_scott (as bs : List (Fin 16 × Fin 16))
    (h : as.length = bs.length) :
    LRed (aps b4subL [scottList (as.map (fun p => byteLit p.1 p.2)),
                      scottList (bs.map (fun p => byteLit p.1 p.2))])
         (scottList ((subResList as bs 1).map
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
      (pairLit (nibLit 1) klL)) = true :=
    closed_b4state (closed_scottList hclB) (closed_nibLit _)
      closed_klL
  have e1 : LRed (aps b4subL [scottList (as.map
        (fun p => byteLit p.1 p.2)),
                      scottList (bs.map (fun p => byteLit p.1 p.2))])
      (.app (aps foldlL [b4subStepL,
              scottList (as.map (fun p => byteLit p.1 p.2)),
              aps pairSrcL
                [scottList (bs.map (fun p => byteLit p.1 p.2)),
                 aps pairSrcL [nibLit 1, klL]]])
            b4finL) :=
    LRed_of_hsteps (k := 2) (by
      simp [b4subL, aps, List.foldl, hsteps, hstep, subst,
            shift_zero, subst_shift_succ,
            subst_of_closed0,
            closed_b4subStepL, closed_b4finL, closed_foldlL,
            closed_pairSrcL,
            closed_nibLit, closed_klL])
  have e2 : LRed (aps pairSrcL [scottList (bs.map
        (fun p => byteLit p.1 p.2)),
                    aps pairSrcL [nibLit 1, klL]])
      (pairLit (scottList (bs.map (fun p => byteLit p.1 p.2)))
        (pairLit (nibLit 1) klL)) :=
    (LRed_app_right (pairSrc_nf _ _ (closed_nibLit _)
      closed_klL)).trans
      (pairSrc_nf _ _ (closed_scottList hclB)
        (closed_pairLit (closed_mono (closed_nibLit _)
          (Nat.zero_le 1))
          (closed_mono closed_klL (Nat.zero_le 1))))
  refine e1.trans ((LRed_app_left (LRed_app_right e2)).trans ?_)
  refine (LRed_app_left (foldl_to_ggb b4subStepL
    (scottList (as.map (fun p => byteLit p.1 p.2))) _
    closed_b4subStepL (closed_scottList hclA) hstate0)).trans ?_
  refine (LRed_app_left (b4subfold_run_scott as bs 1 klL h.le
    closed_klL)).trans ?_
  have hdrop : scottList ((bs.drop as.length).map
      (fun p => byteLit p.1 p.2)) = nilL := by
    have hd : bs.drop as.length = [] := by
      rw [h]; exact List.drop_length
    rw [hd]; rfl
  rw [hdrop]
  refine (b4fin_apply nilL (nibLit (subCarryAfter as bs 1)) _
    closed_nilL
    (closed_nibLit _) (closed_accRev closed_klL)).trans ?_
  have haccEq : (subResList as bs 1).reverse.foldr
        (fun p t => cellLit (byteLit p.1 p.2) t) klL
      = scottList ((subResList as bs 1).reverse.map
          (fun p => byteLit p.1 p.2)) := by
    simp only [scottList, List.foldr_map]
    rfl
  refine (revL_eval _ ((subResList as bs 1).reverse.map
      (fun p => byteLit p.1 p.2)) (closed_accRev closed_klL)
    (fun e he => by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
      exact closed_byteLit _ _)
    (by rw [← haccEq])).trans ?_
  rw [← List.map_reverse, List.reverse_reverse]

#print axioms succL_app3
#print axioms succTower_iter
#print axioms len_eval
#print axioms b4substep_eval_scott
#print axioms b4subfold_run_scott
#print axioms b4sub_eval_scott

end ISAR
