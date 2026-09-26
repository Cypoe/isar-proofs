import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- Batch M layer 4a: assembleOf port — machine-emitted from the
-- seed's own LC parser (_emit_asm.py), combinator leaves mapped
-- to module defs, literals as standalone lblL/b4zL.
-- ============================================================

def lblL : LTerm :=
  (aps conssL [(nibLit 6), (aps conssL [(nibLit 12), (aps conssL [(nibLit 6), (aps conssL [(nibLit 1), (aps conssL [(nibLit 6), (aps conssL [(nibLit 2), (aps conssL [(nibLit 6), (aps conssL [(nibLit 5), (aps conssL [(nibLit 6), (aps conssL [(nibLit 12), klL])])])])])])])])])])

def b4zL : LTerm :=
  (aps conssL [(aps pairSrcL [(nibLit 0), (nibLit 0)]), (aps conssL [(aps pairSrcL [(nibLit 0), (nibLit 0)]), (aps conssL [(aps pairSrcL [(nibLit 0), (nibLit 0)]), (aps conssL [(aps pairSrcL [(nibLit 0), (nibLit 0)]), klL])])])])

def asmL : LTerm :=
  (.abs (.abs (.abs (.abs (.abs (aps (.abs (aps (.abs (aps (.abs (aps (.abs (aps pairSrcL [(aps revL [(.var 0)]), (.var 2)])) [(aps foldlL [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 3) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), (.var 7), (aps (.abs (aps (.abs (aps (.abs (aps foldlL [(.abs (.abs (aps conssL [(.var 0), (.var 1)]))), (aps (.var 0) [klL]), (.var 10)])) [(aps (.var 17) [(.var 7), (.var 0)])])) [(.abs (aps alookL [(.var 14), (.var 0), (aps alookL [(.var 11), (.var 0), (aps b4subL [b4zL, (.var 1)]), (.abs (aps b4subL [(.var 0), (.var 2)]))]), (.abs (aps b4subL [(.var 0), (.var 2)]))]))])) [(aps b4addL [(aps b4addL [(.var 11), (.var 3)]), (.var 2)])])])))])))])))]))), (.var 0), klL])])) [(aps revL [(aps (.var 1) [(aps klL [idL]), (aps klL [idL])])])])) [(aps (.var 0) [(aps klL [idL]), klL])])) [(aps foldlL [(.abs (.abs (aps foldlL [(.abs (.abs (aps (.var 0) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), (aps (.var 3) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(.var 3), (aps pairSrcL [(aps conssL [(aps pairSrcL [(aps headL [(.var 4)]), (aps b4addL [(.var 10), (.var 3)])]), (.var 1)]), (aps conssL [(aps pairSrcL [(.var 6), (aps pairSrcL [(.var 3), klL])]), (.var 0)])])])))])))]), (aps (.abs (aps (.abs (aps (.var 5) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(aps b4addL [(.var 3), (.var 4)]), (aps pairSrcL [(.var 1), (aps conssL [(aps pairSrcL [(.var 8), (aps pairSrcL [(.var 3), (.var 4)])]), (.var 0)])])])))])))])) [(aps nib2b4L [(aps (.var 0) [(aps klL [idL])])])])) [(aps (.var 10) [(.var 2), (.var 9)])])])))]))), (.var 0), (.var 1)]))), (.var 2), (aps pairSrcL [b4zL, (aps pairSrcL [klL, klL])])])]))))))

/-- pass-1 per-item step (enc/zrv/base spliced) -/
def p1StepT (encT zrvT basT : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), (aps (.var 3) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(.var 3), (aps pairSrcL [(aps conssL [(aps pairSrcL [(aps headL [(.var 4)]), (aps b4addL [basT, (.var 3)])]), (.var 1)]), (aps conssL [(aps pairSrcL [(.var 6), (aps pairSrcL [(.var 3), klL])]), (.var 0)])])])))])))]), (aps (.abs (aps (.abs (aps (.var 5) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(aps b4addL [(.var 3), (.var 4)]), (aps pairSrcL [(.var 1), (aps conssL [(aps pairSrcL [(.var 8), (aps pairSrcL [(.var 3), (.var 4)])]), (.var 0)])])])))])))])) [(aps nib2b4L [(aps (.var 0) [(aps klL [idL])])])])) [(aps encT [(.var 2), zrvT])])])))])))

/-- pass-2 emit step (enc/sym/loc/base spliced) -/
def emitStepT (encT symT lcT basT : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 3) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), (.var 7), (aps (.abs (aps (.abs (aps (.abs (aps foldlL [(.abs (.abs (aps conssL [(.var 0), (.var 1)]))), (aps (.var 0) [klL]), (.var 10)])) [(aps encT [(.var 7), (.var 0)])])) [(.abs (aps alookL [symT, (.var 0), (aps alookL [lcT, (.var 0), (aps b4subL [b4zL, (.var 1)]), (.abs (aps b4subL [(.var 0), (.var 2)]))]), (.abs (aps b4subL [(.var 0), (.var 2)]))]))])) [(aps b4addL [(aps b4addL [basT, (.var 3)]), (.var 2)])])])))])))])))])))

/-- let-chain body of assemble (all 5 args spliced); the four
    let-names stay bound as .var slots. -/
def asmLetsT (encT zrvT progT symT basT : LTerm) : LTerm :=
  (aps (.abs (aps (.abs (aps (.abs (aps (.abs (aps pairSrcL [(aps revL [(.var 0)]), (.var 2)])) [(aps foldlL [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 3) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), (.var 7), (aps (.abs (aps (.abs (aps (.abs (aps foldlL [(.abs (.abs (aps conssL [(.var 0), (.var 1)]))), (aps (.var 0) [klL]), (.var 10)])) [(aps encT [(.var 7), (.var 0)])])) [(.abs (aps alookL [symT, (.var 0), (aps alookL [(.var 11), (.var 0), (aps b4subL [b4zL, (.var 1)]), (.abs (aps b4subL [(.var 0), (.var 2)]))]), (.abs (aps b4subL [(.var 0), (.var 2)]))]))])) [(aps b4addL [(aps b4addL [basT, (.var 3)]), (.var 2)])])])))])))])))]))), (.var 0), klL])])) [(aps revL [(aps (.var 1) [(aps klL [idL]), (aps klL [idL])])])])) [(aps (.var 0) [(aps klL [idL]), klL])])) [(aps foldlL [(.abs (.abs (aps foldlL [(.abs (.abs (aps (.var 0) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), (aps (.var 3) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(.var 3), (aps pairSrcL [(aps conssL [(aps pairSrcL [(aps headL [(.var 4)]), (aps b4addL [basT, (.var 3)])]), (.var 1)]), (aps conssL [(aps pairSrcL [(.var 6), (aps pairSrcL [(.var 3), klL])]), (.var 0)])])])))])))]), (aps (.abs (aps (.abs (aps (.var 5) [(.abs (.abs (aps (.var 0) [(.abs (.abs (aps pairSrcL [(aps b4addL [(.var 3), (.var 4)]), (aps pairSrcL [(.var 1), (aps conssL [(aps pairSrcL [(.var 8), (aps pairSrcL [(.var 3), (.var 4)])]), (.var 0)])])])))])))])) [(aps nib2b4L [(aps (.var 0) [(aps klL [idL])])])])) [(aps encT [(.var 2), zrvT])])])))]))), (.var 0), (.var 1)]))), progT, (aps pairSrcL [b4zL, (aps pairSrcL [klL, klL])])])])

-- ---------- let-bound spine pieces (post-substitution shapes) ----------

/-- pass-1 initial accumulator `PAIR b4z (PAIR K K)`. -/
def p1InitT : LTerm := aps pairSrcL [b4zL, aps pairSrcL [klL, klL]]

/-- `λa.λfr. FOLDL p1step fr a` — the per-fragment step. -/
def fragStepT (encT zrvT basT : LTerm) : LTerm :=
  .abs (.abs (aps foldlL [p1StepT encT zrvT basT, .var 0, .var 1]))

/-- pass-1 fold value: `FOLDL fragstep prog init`. -/
def p1ValT (encT zrvT prog basT : LTerm) : LTerm :=
  aps foldlL [fragStepT encT zrvT basT, prog, p1InitT]

/-- `loc = p1·KI·K` — fst of the snd pair. -/
def asmLocV (p1V : LTerm) : LTerm := aps p1V [aps klL [idL], klL]

/-- `prep = REV (p1·KI·KI)`. -/
def asmPrepV (p1V : LTerm) : LTerm :=
  aps revL [aps p1V [aps klL [idL], aps klL [idL]]]

/-- `out = FOLDL emitstep prep K`. -/
def asmOutV (encT symT basT p1V : LTerm) : LTerm :=
  aps foldlL [emitStepT encT symT (asmLocV p1V) basT, asmPrepV p1V, klL]

-- ---------- closedness -------------------------------------------------

theorem closed_lblL : closed 0 lblL = true := by decide

theorem closed_b4zL : closed 0 b4zL = true := by decide

-- depth-generic closedness for the assemble leaves
theorem closed_idL_any (c : Nat) : closed c idL = true :=
  closed_mono closed_idL (Nat.zero_le c)
theorem closed_kilL_any (c : Nat) : closed c kilL = true :=
  closed_mono closed_kilL (Nat.zero_le c)
theorem closed_foldlL_any (c : Nat) : closed c foldlL = true :=
  closed_mono closed_foldlL (Nat.zero_le c)
theorem closed_headL_any (c : Nat) : closed c headL = true :=
  closed_mono closed_headL (Nat.zero_le c)
theorem closed_nib2b4L_any (c : Nat) : closed c nib2b4L = true :=
  closed_mono closed_nib2b4L (Nat.zero_le c)
theorem closed_lenL_any (c : Nat) : closed c lenL = true :=
  closed_mono closed_lenL (Nat.zero_le c)
theorem closed_b4subL_any (c : Nat) : closed c b4subL = true :=
  closed_mono closed_b4subL (Nat.zero_le c)
theorem closed_eqStrL_any (c : Nat) : closed c eqStrL = true :=
  closed_mono closed_eqStrL (Nat.zero_le c)
theorem closed_alookL_any (c : Nat) : closed c alookL = true :=
  closed_mono closed_alookL (Nat.zero_le c)
theorem closed_lblL_any (c : Nat) : closed c lblL = true :=
  closed_mono closed_lblL (Nat.zero_le c)
theorem closed_b4zL_any (c : Nat) : closed c b4zL = true :=
  closed_mono closed_b4zL (Nat.zero_le c)

theorem closed_p1StepT {e z b : LTerm} (c : Nat)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hb : closed 0 b = true) : closed c (p1StepT e z b) = true := by
  simp only [p1StepT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (Nat.zero_le _)
    | exact closed_mono hz (Nat.zero_le _)
    | exact closed_mono hb (Nat.zero_le _)

theorem closed_emitStepT {e s lc b : LTerm} (c : Nat)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hlc : closed 0 lc = true) (hb : closed 0 b = true) :
    closed c (emitStepT e s lc b) = true := by
  simp only [emitStepT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (Nat.zero_le _)
    | exact closed_mono hs (Nat.zero_le _)
    | exact closed_mono hlc (Nat.zero_le _)
    | exact closed_mono hb (Nat.zero_le _)

theorem closed_p1InitT (c : Nat) : closed c p1InitT = true := by
  simp only [p1InitT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor

theorem closed_fragStepT {e z b : LTerm} (c : Nat)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hb : closed 0 b = true) : closed c (fragStepT e z b) = true := by
  simp only [fragStepT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_foldlL_any _
    | exact closed_p1StepT _ he hz hb

theorem closed_app_any {f x : LTerm} {c : Nat} (hf : closed c f = true)
    (hx : closed c x = true) : closed c (.app f x) = true := by
  simp only [closed, Bool.and_eq_true]; exact ⟨hf, hx⟩

theorem closed_p1ValT {e z p b : LTerm} (c : Nat)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hp : closed 0 p = true) (hb : closed 0 b = true) :
    closed c (p1ValT e z p b) = true :=
  closed_app_any (closed_app_any (closed_app_any (closed_foldlL_any c)
    (closed_fragStepT c he hz hb)) (closed_mono hp (Nat.zero_le c)))
    (closed_p1InitT c)

-- ---------- literal normal forms ----------------------------------------

/-- `"label"` as nibble cells (hi,lo per byte of `utf8 "label"`). -/
def lblNibs : List (Fin 16) := [6, 12, 6, 1, 6, 2, 6, 5, 6, 12]

theorem lbl_nf : LRed lblL (scottList (lblNibs.map nibLit)) := by
  show LRed ((lblNibs.map nibLit).foldr
      (fun h t => aps conssL [h, t]) nilL) _
  exact conssChain_nf _ (fun e he => by
    simp only [List.mem_map] at he
    obtain ⟨i, _, rfl⟩ := he; exact closed_nibLit _)

/-- a `CONSS`-application cell whose head and tail are themselves
    reducible normalizes to a `cellLit` of the reduced parts. -/
theorem conssCell_nf {h h' t t' : LTerm} (hh : LRed h h') (ht : LRed t t')
    (hh' : closed 0 h' = true) (ht' : closed 0 t' = true) :
    LRed (aps conssL [h, t]) (cellLit h' t') :=
  (LRed_app_right ht).trans
    ((LRed_app_left (LRed_app_right hh)).trans (conss_nf h' t' hh' ht'))

theorem b4z_nf : LRed b4zL (scottList (List.replicate 4 (byteLit 0 0))) := by
  have pc : LRed (aps pairSrcL [nibLit 0, nibLit 0]) (byteLit 0 0) :=
    pairSrc_nf _ _ (closed_nibLit _) (closed_nibLit _)
  have zb : closed 0 (byteLit 0 0) = true := closed_byteLit _ _
  have s0 : closed 0 nilL = true := closed_nilL
  have h3 : LRed (aps conssL [aps pairSrcL [nibLit 0, nibLit 0], klL])
      (scottList [byteLit 0 0]) :=
    conssCell_nf pc Relation.ReflTransGen.refl zb s0
  have cl1 : closed 0 (scottList [byteLit 0 0]) = true :=
    closed_scottList (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl; exact zb)
  have h2 : LRed (aps conssL [aps pairSrcL [nibLit 0, nibLit 0],
      aps conssL [aps pairSrcL [nibLit 0, nibLit 0], klL]])
      (scottList [byteLit 0 0, byteLit 0 0]) :=
    conssCell_nf pc h3 zb cl1
  have cl2 : closed 0 (scottList [byteLit 0 0, byteLit 0 0]) = true :=
    closed_scottList (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact zb)
  have h1 : LRed (aps conssL [aps pairSrcL [nibLit 0, nibLit 0],
      aps conssL [aps pairSrcL [nibLit 0, nibLit 0],
        aps conssL [aps pairSrcL [nibLit 0, nibLit 0], klL]]])
      (scottList [byteLit 0 0, byteLit 0 0, byteLit 0 0]) :=
    conssCell_nf pc h2 zb cl2
  have cl3 : closed 0 (scottList [byteLit 0 0, byteLit 0 0,
      byteLit 0 0]) = true :=
    closed_scottList (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> exact zb)
  have h0 : LRed b4zL (scottList
      [byteLit 0 0, byteLit 0 0, byteLit 0 0, byteLit 0 0]) :=
    conssCell_nf pc h1 zb cl3
  exact h0

-- ---------- the spine open ----------------------------------------------

/-- Stage A: the 5 outer betas expose the let-chain. -/
theorem asm_open_outer (e z p s b : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hp : closed 0 p = true) (hs : closed 0 s = true)
    (hb : closed 0 b = true) :
    LRed (aps asmL [e, z, p, s, b]) (asmLetsT e z p s b) := by
  have ce : ∀ c, closed c e = true :=
    fun c => closed_mono he (Nat.zero_le c)
  have cz : ∀ c, closed c z = true :=
    fun c => closed_mono hz (Nat.zero_le c)
  have cp : ∀ c, closed c p = true :=
    fun c => closed_mono hp (Nat.zero_le c)
  have cs : ∀ c, closed c s = true :=
    fun c => closed_mono hs (Nat.zero_le c)
  have cb : ∀ c, closed c b = true :=
    fun c => closed_mono hb (Nat.zero_le c)
  exact LRed_of_hsteps (k := 5) (by
    unfold asmL asmLetsT
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed, ce, cz, cp, cs, cb,
          closed_pairSrcL_any, closed_conssL_any, closed_klL_any,
          closed_idL_any, closed_foldlL_any,
          closed_revL_any, closed_eqStrL_any, closed_lenL_any,
          closed_alookL_any, closed_headL_any, closed_b4addL_any,
          closed_b4subL_any, closed_nib2b4L_any, closed_lblL_any,
          closed_b4zL_any])

/-- Stage B: the 4 let-betas instantiate p1/loc/prep/out. -/
theorem asm_open_lets (e z p s b : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hp : closed 0 p = true) (hs : closed 0 s = true)
    (hb : closed 0 b = true) :
    LRed (asmLetsT e z p s b)
      (aps pairSrcL
        [aps revL [asmOutV e s b (p1ValT e z p b)],
         asmLocV (p1ValT e z p b)]) := by
  have ce : ∀ c, closed c e = true :=
    fun c => closed_mono he (Nat.zero_le c)
  have cz : ∀ c, closed c z = true :=
    fun c => closed_mono hz (Nat.zero_le c)
  have cp : ∀ c, closed c p = true :=
    fun c => closed_mono hp (Nat.zero_le c)
  have cs : ∀ c, closed c s = true :=
    fun c => closed_mono hs (Nat.zero_le c)
  have cb : ∀ c, closed c b = true :=
    fun c => closed_mono hb (Nat.zero_le c)
  exact LRed_of_hsteps (k := 4) (by
    unfold asmLetsT asmOutV asmLocV asmPrepV p1ValT fragStepT
      p1StepT emitStepT p1InitT
    simp [aps, List.foldl, hsteps, hstep, subst, shift,
          subst_of_closed, shift_of_closed, ce, cz, cp, cs, cb,
          closed_pairSrcL_any, closed_conssL_any, closed_klL_any,
          closed_idL_any, closed_foldlL_any,
          closed_revL_any, closed_eqStrL_any, closed_lenL_any,
          closed_alookL_any, closed_headL_any, closed_b4addL_any,
          closed_b4subL_any, closed_nib2b4L_any, closed_lblL_any,
          closed_b4zL_any])

theorem asm_open (e z p s b : LTerm)
    (he : closed 0 e = true) (hz : closed 0 z = true)
    (hp : closed 0 p = true) (hs : closed 0 s = true)
    (hb : closed 0 b = true) :
    LRed (aps asmL [e, z, p, s, b])
      (aps pairSrcL
        [aps revL [asmOutV e s b (p1ValT e z p b)],
         asmLocV (p1ValT e z p b)]) :=
  (asm_open_outer e z p s b he hz hp hs hb).trans
    (asm_open_lets e z p s b he hz hp hs hb)

-- ---------- axiom audit ---------------------------------------------------

#print axioms conssCell_nf
#print axioms lbl_nf
#print axioms b4z_nf
#print axioms asm_open_outer
#print axioms asm_open_lets
#print axioms asm_open

end ISAR
