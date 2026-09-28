import ISAR.SpecVocabulary

namespace ISAR

-- ============================================================
-- Batch M layer 4c: assembleOf pass-2 emit evaluation —
-- resv resolver (ALOOK shadow + B4SUB rel32), emitstep fold
-- over prep entries, REV-out + loc projection, asm_eval.
-- ============================================================

abbrev B4L := List (Fin 16 × Fin 16)

/-- semantic prep entry: the item, its position, its declared
    length bytes, and the bytes the encoder emits for it under
    this entry's instantiated resolver. -/
abbrev P2Item := AsmItem × B4L × B4L × B4L

/-- prep entry term `PAIR it (PAIR of4 ln4)`. -/
def p2EntryT (e : P2Item) : LTerm :=
  pairLit e.1.itT
    (pairLit (scottList (bm e.2.1)) (scottList (bm e.2.2.1)))

/-- per-item semantic pass-2 step: labels pass acc through,
    insn items prepend their emitted bytes REVERSED (the
    `FOLDL (λo.λc. CONS c o)` accumulation order). -/
def p2StepSem (e : P2Item) (acc : List LTerm) : List LTerm :=
  if decide (e.1.ns = lblNibs) then acc
  else (bm e.2.2.2).reverse ++ acc

/-- semantic pass-2 fold over prep entries in emission order. -/
def p2FoldSem (es : List P2Item) : List LTerm :=
  es.foldl (fun acc e => p2StepSem e acc) []

/-- end4 = B4ADD (B4ADD base of) ln — semantic ripple. -/
def end4Sem (basB ofB lnB : B4L) : B4L :=
  resList (resList basB ofB 0) lnB 0

/-- semantic assoc-lookup: last matching key wins. -/
def alookSem (key : List (Fin 16)) (kvs : List (List (Fin 16) × B4L)) :
    Option B4L :=
  kvs.foldl (fun acc kv => if decide (key = kv.1) then some kv.2 else acc)
    none

/-- semantic resolver: symbols shadow locals; a hit resolves to
    `B4SUB addr end4`, a miss to `B4SUB 0 end4`. -/
def resvSem (symKVs locKVs : List (List (Fin 16) × B4L))
    (nmB : List (Fin 16)) (e4 : B4L) : B4L :=
  match alookSem nmB symKVs with
  | some svB => subResList svB e4 1
  | none => match alookSem nmB locKVs with
    | some lvB => subResList lvB e4 1
    | none => subResList b4zeroBytes e4 1

-- ---------- emitted staged definitions -------------------------

/-- `λo.λc. CONS c o` — the out-fold's prepend step. -/
def consRevL : LTerm := .abs (.abs (aps conssL [.var 0, .var 1]))

/-- `λnm. (ALOOK sym nm) ((ALOOK loc nm) (B4SUB b4z ·1)
    (λlv. B4SUB lv ·2)) (λsv. B4SUB sv ·2)` — `.var 1`/`.var 2`
    is the enclosing `end4` slot (raw emitted form). -/
def p2ResvRawT (symT lcT : LTerm) : LTerm :=
  .abs (aps alookL
    [symT, .var 0,
     aps alookL
       [lcT, .var 0, aps b4subL [b4zL, .var 1],
        .abs (aps b4subL [.var 0, .var 2])],
     .abs (aps b4subL [.var 0, .var 2])])

/-- post-substitution resolver: `end4` spliced. -/
def p2ResvT (symT lcT e4T : LTerm) : LTerm :=
  .abs (aps alookL
    [symT, .var 0,
     aps alookL
       [lcT, .var 0, aps b4subL [b4zL, e4T],
        .abs (aps b4subL [.var 0, e4T])],
     .abs (aps b4subL [.var 0, e4T])])

/-- `λrsv. (λenc2. FOLDL consRev (enc2·K) acc) (ENC it rsv)`. -/
def p2RsvContT (encT accT itT : LTerm) : LTerm :=
  .abs (aps (.abs (aps foldlL
              [consRevL, aps (.var 0) [klL], accT]))
            [aps encT [itT, .var 0]])

/-- `λend4. (λrsv …) (RESV …)` — the insn let-chain body. -/
def p2E4ContT (encT symT lcT accT itT : LTerm) : LTerm :=
  .abs (aps (p2RsvContT encT accT itT) [p2ResvRawT symT lcT])

/-- `λtg.λrr. eqStr tg lbl (len tg) acc (E4CHAIN)` — the
    pass-2 dispatch; `.var 3`/`.var 2` are the enclosing
    `of`/`ln` slots. -/
def p2DispT (e s lc b accT itT : LTerm) : LTerm :=
  .abs (.abs (aps eqStrL
    [.var 1, lblL, aps lenL [.var 1], accT,
     aps (p2E4ContT e s lc accT itT)
       [aps b4addL [aps b4addL [b, .var 3], .var 2]]]))

/-- post-destructure dispatch: `of`/`ln` spliced. -/
def p2DispS (e s lc b accT itT ofT lnT : LTerm) : LTerm :=
  .abs (.abs (aps eqStrL
    [.var 1, lblL, aps lenL [.var 1], accT,
     aps (p2E4ContT e s lc accT itT)
       [aps b4addL [aps b4addL [b, ofT], lnT]]]))

/-- `λof.λln. it·K·disp` — applied to the ol pair. -/
def p2OfLnContT (e s lc b accT itT : LTerm) : LTerm :=
  .abs (.abs (aps itT [klL, p2DispT e s lc b accT itT]))

/-- `λit.λol. ol·(λof.λln. it·K·disp)` — the rec continuation
    (emitted form, inlined: `it` is `.var 3` at the K-spine and
    `.var 7` inside ENC, `of`/`ln` are `.var 3`/`.var 2` in the
    B4ADD chain, `acc` is spliced). -/
def p2RecContT (e s lc b accT : LTerm) : LTerm :=
  (.abs (.abs (aps (.var 0) [(.abs (.abs (aps (.var 3) [klL, (.abs (.abs (aps eqStrL [(.var 1), lblL, (aps lenL [(.var 1)]), accT, (aps (.abs (aps (.abs (aps (.abs (aps foldlL [(.abs (.abs (aps conssL [(.var 0), (.var 1)]))), (aps (.var 0) [klL]), accT])) [(aps e [(.var 7), (.var 0)])])) [(.abs (aps alookL [s, (.var 0), (aps alookL [lc, (.var 0), (aps b4subL [b4zL, (.var 1)]), (.abs (aps b4subL [(.var 0), (.var 2)]))]), (.abs (aps b4subL [(.var 0), (.var 2)]))]))])) [(aps b4addL [(aps b4addL [b, (.var 3)]), (.var 2)])])])))])))])))

-- ---------- closedness --------------------------------------------

theorem closed_consRevL : closed 0 consRevL = true := by decide

theorem closed_consRevL_any (c : Nat) : closed c consRevL = true :=
  closed_mono closed_consRevL (Nat.zero_le c)

theorem closed_p2ResvRawT {s lc : LTerm} (c : Nat)
    (hs : closed 1 s = true) (hl : closed 1 lc = true) :
    closed (c + 1) (p2ResvRawT s lc) = true := by
  simp only [p2ResvRawT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)

theorem closed_p2ResvT {s lc e4 : LTerm} (c : Nat)
    (hs : closed 1 s = true) (hl : closed 1 lc = true)
    (he4 : closed 1 e4 = true) :
    closed c (p2ResvT s lc e4) = true := by
  simp only [p2ResvT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono he4 (by omega)

theorem closed_p2RsvContT {e a i : LTerm} (c : Nat)
    (he : closed 1 e = true) (ha : closed 2 a = true)
    (hi : closed 1 i = true) :
    closed c (p2RsvContT e a i) = true := by
  simp only [p2RsvContT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p2E4ContT {e s lc a i : LTerm} (c : Nat)
    (he : closed 1 e = true) (hs : closed 1 s = true)
    (hl : closed 1 lc = true) (ha : closed 2 a = true)
    (hi : closed 1 i = true) :
    closed c (p2E4ContT e s lc a i) = true := by
  simp only [p2E4ContT, p2RsvContT, p2ResvRawT, closed, aps,
             List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p2DispT {e s lc b a i : LTerm} (c : Nat)
    (he : closed 4 e = true) (hs : closed 4 s = true)
    (hl : closed 4 lc = true) (hb : closed 4 b = true)
    (ha : closed 2 a = true) (hi : closed 4 i = true) :
    closed (c + 2) (p2DispT e s lc b a i) = true := by
  simp only [p2DispT, p2E4ContT, p2RsvContT, p2ResvRawT, closed, aps,
             List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p2DispS {e s lc b a i o n : LTerm} (c : Nat)
    (he : closed 2 e = true) (hs : closed 2 s = true)
    (hl : closed 2 lc = true) (hb : closed 2 b = true)
    (ha : closed 2 a = true) (hi : closed 2 i = true)
    (ho : closed 2 o = true) (hn : closed 2 n = true) :
    closed c (p2DispS e s lc b a i o n) = true := by
  simp only [p2DispS, p2E4ContT, p2RsvContT, p2ResvRawT, closed, aps,
             List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)
    | exact closed_mono ho (by omega)
    | exact closed_mono hn (by omega)

theorem closed_p2OfLnContT {e s lc b a i : LTerm} (c : Nat)
    (he : closed 2 e = true) (hs : closed 2 s = true)
    (hl : closed 2 lc = true) (hb : closed 2 b = true)
    (ha : closed 2 a = true) (hi : closed 2 i = true) :
    closed c (p2OfLnContT e s lc b a i) = true := by
  simp only [p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT, p2ResvRawT,
             closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)
    | exact closed_mono hi (by omega)

theorem closed_p2RecContT {e s lc b a : LTerm} (c : Nat)
    (he : closed 2 e = true) (hs : closed 2 s = true)
    (hl : closed 2 lc = true) (hb : closed 2 b = true)
    (ha : closed 2 a = true) :
    closed c (p2RecContT e s lc b a) = true := by
  simp only [p2RecContT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)

-- ---------- staged opens -------------------------------------------

/-- `emitstep·acc·rec →* rec·(λit.λol. ol·(λof.λln. it·K·disp))`. -/
theorem p2Step_open (e s lc b accT recT : LTerm)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hl : closed 0 lc = true) (hb : closed 0 b = true)
    (ha : closed 0 accT = true) (hr : closed 0 recT = true) :
    LRed (aps (emitStepT e s lc b) [accT, recT])
      (aps recT [p2RecContT e s lc b accT]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cs : ∀ c, closed c s = true := fun c =>
    closed_mono hs (Nat.zero_le c)
  have clc : ∀ c, closed c lc = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have cr : ∀ c, closed c recT = true := fun c =>
    closed_mono hr (Nat.zero_le c)
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
  have c2 : ∀ c, closed c lblL = true := closed_lblL_any
  have c3 : ∀ c, closed c lenL = true := fun c =>
    closed_mono closed_lenL (Nat.zero_le c)
  have c4 : ∀ c, closed c alookL = true := fun c =>
    closed_mono closed_alookL (Nat.zero_le c)
  have c5 : ∀ c, closed c b4subL = true := fun c =>
    closed_mono closed_b4subL (Nat.zero_le c)
  have c6 : ∀ c, closed c b4zL = true := closed_b4zL_any
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [emitStepT, p2RecContT, aps,
          List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, cr, c1, c2, c3, c4, c5, c6, c7, c8,
          c9, c10])

/-- the rec continuation applied to `it`/`ol`: two betas. -/
theorem p2RecCont_apply (e s lc b accT itT olT : LTerm)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hl : closed 0 lc = true) (hb : closed 0 b = true)
    (ha : closed 0 accT = true) (hi : closed 0 itT = true)
    (ho : closed 0 olT = true) :
    LRed (aps (p2RecContT e s lc b accT) [itT, olT])
      (aps olT [p2OfLnContT e s lc b accT itT]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cs : ∀ c, closed c s = true := fun c =>
    closed_mono hs (Nat.zero_le c)
  have clc : ∀ c, closed c lc = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have co : ∀ c, closed c olT = true := fun c =>
    closed_mono ho (Nat.zero_le c)
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
  have c2 : ∀ c, closed c lblL = true := closed_lblL_any
  have c3 : ∀ c, closed c lenL = true := fun c =>
    closed_mono closed_lenL (Nat.zero_le c)
  have c4 : ∀ c, closed c alookL = true := fun c =>
    closed_mono closed_alookL (Nat.zero_le c)
  have c5 : ∀ c, closed c b4subL = true := fun c =>
    closed_mono closed_b4subL (Nat.zero_le c)
  have c6 : ∀ c, closed c b4zL = true := closed_b4zL_any
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p2RecContT, p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, consRevL, aps, List.foldl, hsteps, hstep,
          subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, ci, co, c1, c2, c3, c4, c5, c6, c7,
          c8, c9, c10])

/-- `of`/`ln` betas: lands at `it·K·dispS`. -/
theorem p2OfLn_apply (e s lc b accT itT ofT lnT : LTerm)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hl : closed 0 lc = true) (hb : closed 0 b = true)
    (ha : closed 0 accT = true) (hi : closed 0 itT = true)
    (ho : closed 0 ofT = true) (hn : closed 0 lnT = true) :
    LRed (aps (p2OfLnContT e s lc b accT itT) [ofT, lnT])
      (aps itT [klL, p2DispS e s lc b accT itT ofT lnT]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cs : ∀ c, closed c s = true := fun c =>
    closed_mono hs (Nat.zero_le c)
  have clc : ∀ c, closed c lc = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have co : ∀ c, closed c ofT = true := fun c =>
    closed_mono ho (Nat.zero_le c)
  have cn : ∀ c, closed c lnT = true := fun c =>
    closed_mono hn (Nat.zero_le c)
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
  have c2 : ∀ c, closed c lblL = true := closed_lblL_any
  have c3 : ∀ c, closed c lenL = true := fun c =>
    closed_mono closed_lenL (Nat.zero_le c)
  have c4 : ∀ c, closed c alookL = true := fun c =>
    closed_mono closed_alookL (Nat.zero_le c)
  have c5 : ∀ c, closed c b4subL = true := fun c =>
    closed_mono closed_b4subL (Nat.zero_le c)
  have c6 : ∀ c, closed c b4zL = true := closed_b4zL_any
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  exact LRed_of_hsteps (k := 2) (by
    simp [p2OfLnContT, p2DispS, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, ci, co, cn, c1, c2, c3, c4, c5, c6,
          c7, c9, c10, c11])

/-- `dispS·tg·rr →* EQSTR tg lbl (LEN tg) acc (E4CHAIN of ln)`. -/
theorem p2Disp_open (e s lc b accT itT ofT lnT tgT rrT : LTerm)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hl : closed 0 lc = true) (hb : closed 0 b = true)
    (ha : closed 0 accT = true) (hi : closed 0 itT = true)
    (ho : closed 0 ofT = true) (hn : closed 0 lnT = true)
    (ht : closed 0 tgT = true) (_hr : closed 0 rrT = true) :
    LRed (aps (p2DispS e s lc b accT itT ofT lnT) [tgT, rrT])
      (aps eqStrL [tgT, lblL, aps lenL [tgT], accT,
        aps (p2E4ContT e s lc accT itT)
          [aps b4addL [aps b4addL [b, ofT], lnT]]]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cs : ∀ c, closed c s = true := fun c =>
    closed_mono hs (Nat.zero_le c)
  have clc : ∀ c, closed c lc = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have cb : ∀ c, closed c b = true := fun c =>
    closed_mono hb (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have co : ∀ c, closed c ofT = true := fun c =>
    closed_mono ho (Nat.zero_le c)
  have cn : ∀ c, closed c lnT = true := fun c =>
    closed_mono hn (Nat.zero_le c)
  have ct : ∀ c, closed c tgT = true := fun c =>
    closed_mono ht (Nat.zero_le c)
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
  have c2 : ∀ c, closed c lblL = true := closed_lblL_any
  have c3 : ∀ c, closed c lenL = true := fun c =>
    closed_mono closed_lenL (Nat.zero_le c)
  have c4 : ∀ c, closed c alookL = true := fun c =>
    closed_mono closed_alookL (Nat.zero_le c)
  have c5 : ∀ c, closed c b4subL = true := fun c =>
    closed_mono closed_b4subL (Nat.zero_le c)
  have c6 : ∀ c, closed c b4zL = true := closed_b4zL_any
  have c7 : ∀ c, closed c b4addL = true := fun c =>
    closed_mono closed_b4addL (Nat.zero_le c)
  have c8 : ∀ c, closed c conssL = true := fun c =>
    closed_mono closed_conssL (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  exact LRed_of_hsteps (k := 2) (by
    simp [p2DispS, p2E4ContT, p2RsvContT, p2ResvRawT, aps,
          List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, ci, co, cn, ct, c1, c2, c3, c4,
          c5, c6, c7, c9, c10, c11])

/-- `end4` beta: `(λe4. (λrsv…)(RESV))·e4T →* (λrsv…)(resv e4T)`. -/
theorem p2E4_apply (e s lc accT itT e4T : LTerm)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hl : closed 0 lc = true) (ha : closed 0 accT = true)
    (hi : closed 0 itT = true) (he4 : closed 0 e4T = true) :
    LRed (aps (p2E4ContT e s lc accT itT) [e4T])
      (aps (p2RsvContT e accT itT) [p2ResvT s lc e4T]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have cs : ∀ c, closed c s = true := fun c =>
    closed_mono hs (Nat.zero_le c)
  have clc : ∀ c, closed c lc = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have ce4 : ∀ c, closed c e4T = true := fun c =>
    closed_mono he4 (Nat.zero_le c)
  have c4 : ∀ c, closed c alookL = true := fun c =>
    closed_mono closed_alookL (Nat.zero_le c)
  have c5 : ∀ c, closed c b4subL = true := fun c =>
    closed_mono closed_b4subL (Nat.zero_le c)
  have c6 : ∀ c, closed c b4zL = true := closed_b4zL_any
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  exact LRed_of_hsteps (k := 1) (by
    simp [p2E4ContT, p2RsvContT, p2ResvT, p2ResvRawT, aps,
          List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, ca, ci, ce4, c4, c5, c6, c9, c10, c11])

/-- `rsv` beta: lands at `(λenc2. FOLDL consRev (enc2·K) acc)
    (ENC it rsv)`. -/
theorem p2RsvCont_apply (e accT itT rsvT : LTerm)
    (he : closed 0 e = true) (ha : closed 0 accT = true)
    (hi : closed 0 itT = true) (hr : closed 0 rsvT = true) :
    LRed (aps (p2RsvContT e accT itT) [rsvT])
      (aps (.abs (aps foldlL [consRevL, aps (.var 0) [klL], accT]))
        [aps e [itT, rsvT]]) := by
  have ce : ∀ c, closed c e = true := fun c =>
    closed_mono he (Nat.zero_le c)
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have ci : ∀ c, closed c itT = true := fun c =>
    closed_mono hi (Nat.zero_le c)
  have cr : ∀ c, closed c rsvT = true := fun c =>
    closed_mono hr (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  exact LRed_of_hsteps (k := 1) (by
    simp [p2RsvContT, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, ca, ci, cr, c9, c10, c11])

/-- `enc2` beta: `FOLDL consRev (encApp·K) acc`. -/
theorem p2Enc_apply (e accT itT rsvT : LTerm)
    (he : closed 0 e = true) (ha : closed 0 accT = true)
    (hi : closed 0 itT = true) (hr : closed 0 rsvT = true) :
    LRed (aps (.abs (aps foldlL
              [consRevL, aps (.var 0) [klL], accT]))
            [aps e [itT, rsvT]])
      (aps foldlL [consRevL, aps (aps e [itT, rsvT]) [klL],
        accT]) := by
  have ca : ∀ c, closed c accT = true := fun c =>
    closed_mono ha (Nat.zero_le c)
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  have c11 : ∀ c, closed c consRevL = true := closed_consRevL_any
  have cenc : ∀ c, closed c ((e.app itT).app rsvT) = true := fun c =>
    closed_mono (closed_app (closed_app he hi) hr) (Nat.zero_le c)
  exact LRed_of_hsteps (k := 1) (by
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ca, cenc, c9, c10, c11])

/-- `resv·nm` opens the double-ALOOK spine. -/
theorem p2Resv_apply (s lc e4 nm : LTerm)
    (hs : closed 0 s = true) (hl : closed 0 lc = true)
    (he4 : closed 0 e4 = true) (hn : closed 0 nm = true) :
    LRed (aps (p2ResvT s lc e4) [nm])
      (aps alookL
        [s, nm,
         aps alookL
           [lc, nm, aps b4subL [b4zL, e4],
            .abs (aps b4subL [.var 0, e4])],
         .abs (aps b4subL [.var 0, e4])]) := by
  have cs : ∀ c, closed c s = true := fun c =>
    closed_mono hs (Nat.zero_le c)
  have clc : ∀ c, closed c lc = true := fun c =>
    closed_mono hl (Nat.zero_le c)
  have ce4 : ∀ c, closed c e4 = true := fun c =>
    closed_mono he4 (Nat.zero_le c)
  have cn : ∀ c, closed c nm = true := fun c =>
    closed_mono hn (Nat.zero_le c)
  have c4 : ∀ c, closed c alookL = true := fun c =>
    closed_mono closed_alookL (Nat.zero_le c)
  have c5 : ∀ c, closed c b4subL = true := fun c =>
    closed_mono closed_b4subL (Nat.zero_le c)
  have c6 : ∀ c, closed c b4zL = true := closed_b4zL_any
  exact LRed_of_hsteps (k := 1) (by
    simp [p2ResvT, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          cs, clc, ce4, cn, c4, c5, c6])


-- ---------- eval helpers ---------------------------------------------------

/-- `JUST·v·n·j →* j·v` — the option-some select. -/
theorem justL_apply3 (v n j : LTerm) (hv : closed 0 v = true)
    (_hn : closed 0 n = true) (hj : closed 0 j = true) :
    LRed (aps justL [v, n, j]) (.app j v) :=
  LRed_of_hsteps (k := 3) (by
    simp [justL, aps, List.foldl, hsteps, hstep, subst,
          shift_of_closed0 hv, subst_of_closed0 hv,
          shift_of_closed0 hj])

/-- `optionLit`-maybe: `none`-cell picks the fallback, `some v`
    applies the continuation. -/
theorem optionLit_apply2 (o : Option LTerm) (n j : LTerm)
    (ho : ∀ v, o = some v → closed 0 v = true)
    (hn : closed 0 n = true) (hj : closed 0 j = true) :
    LRed (aps (optionLit o) [n, j])
      (match o with | none => n | some v => .app j v) := by
  cases o with
  | none =>
    show LRed (aps klL [n, j]) n
    exact klL_apply2 n j
  | some v =>
    show LRed (aps (.app justL v) [n, j]) (.app j v)
    exact justL_apply3 v n j (ho v rfl) hn hj

/-- option-maybe specialized per case: `none` picks the fallback,
    `some v` applies the continuation. -/
theorem optionNone_apply (n j : LTerm) :
    LRed (aps (optionLit none) [n, j]) n :=
  klL_apply2 n j

theorem optionSome_apply (v n j : LTerm) (hv : closed 0 v = true)
    (hn : closed 0 n = true) (hj : closed 0 j = true) :
    LRed (aps (optionLit (some v)) [n, j]) (.app j v) :=
  justL_apply3 v n j hv hn hj

/-- `(λsv. B4SUB sv e4)·v →* B4SUB v e4` — the resolver's
    subtraction continuation. -/
theorem p2SubCont_apply (e4 v : LTerm) (he4 : closed 0 e4 = true)
    (hv : closed 0 v = true) :
    LRed (aps (.abs (aps b4subL [.var 0, e4])) [v])
      (aps b4subL [v, e4]) :=
  LRed_of_hsteps (k := 1) (by
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed0 he4, shift_of_closed0 hv,
          subst_of_closed0 closed_b4subL])

/-- `_ALOOK` step over pairLit-form entries: `e` already reduces to
    the `PAIR kT v` cell (the pass-1 loc/prep convention) instead of
    an unreduced `pairSrc` spine. -/
theorem alookStep_eval_lit (key : List (Fin 16)) (keyT : LTerm)
    (hkeyT : LRed keyT (scottList (key.map nibLit)))
    (hkeycl : closed 0 keyT = true)
    (k2 : List (Fin 16)) (k2T v2 X : LTerm)
    (hk2T : LRed k2T (scottList (k2.map nibLit)))
    (hk2cl : closed 0 k2T = true)
    (hv2 : closed 0 v2 = true) (hXcl : closed 0 X = true)
    (e : LTerm)
    (he : LRed e (pairLit k2T v2))
    (hecl : closed 0 e = true) :
    LRed (.app (.app (alookStepK keyT) X) e)
      (if decide (key = k2) then aps justL [v2] else X) := by
  have hclkey : ∀ c ∈ key.map nibLit, closed 0 c = true := by
    intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact closed_nibLit i
  have hlen : LRed (aps lenL [keyT]) (succChain kilL key.length) :=
    (LRed_app_right hkeyT).trans
      (List.length_map (f := nibLit) ▸ len_eval _ hclkey)
  have hopen := alookStepK_open keyT X e hkeycl hXcl hecl
  have hpair : LRed (.app e (.abs (.abs (aps eqStrL
        [keyT, .var 1, aps lenL [keyT], aps justL [.var 0], X]))))
      (aps eqStrL
        [keyT, k2T, aps lenL [keyT], aps justL [v2], X]) :=
    (LRed_app_left he).trans
      ((pairLit_apply k2T v2 _ hk2cl hv2).trans
        (alookKont_eval keyT _ _ X hkeycl hk2cl hv2 hXcl))
  have hstr : LRed (aps eqStrL
        [keyT, k2T, aps lenL [keyT], aps justL [v2], X])
      (aps (boolLit (decide (key = k2))) [aps justL [v2], X]) :=
    LRed_app_left (LRed_app_left
      (eqStr_eval key k2 key.length (Nat.le_refl _)
        keyT k2T (aps lenL [keyT])
        hkeyT hk2T hlen
        hkeycl hk2cl (closed_app closed_lenL hkeycl)))
  exact hopen.trans (hpair.trans (hstr.trans (boolLit_sel _ _ _)))

/-- a table row: semantic key nibbles, semantic value bytes, and the
    value's term. -/
abbrev P2Row := List (Fin 16) × B4L × LTerm

/-- entry-cell ↔ row well-formedness: the cell is `PAIR kT vT`,
    `kT` is the row's nibble list and `vT` its bytes4 list. -/
def p2RowRel (e : LTerm) (kv : P2Row) : Prop :=
  ∃ kT, LRed e (pairLit kT kv.2.2) ∧
    LRed kT (scottList (kv.1.map nibLit)) ∧
    LRed kv.2.2 (scottList (bm kv.2.1)) ∧
    closed 0 e = true ∧ closed 0 kT = true ∧ closed 0 kv.2.2 = true

/-- the fold over pairLit-cells mirrors the row-level assoc lookup:
    last matching key wins, `none` stays `K`. -/
theorem alookFold_eval_lit (key : List (Fin 16)) (keyT : LTerm)
    (hkeyT : LRed keyT (scottList (key.map nibLit)))
    (hkeycl : closed 0 keyT = true)
    (es : List LTerm) (kvs : List P2Row)
    (h2 : List.Forall₂ p2RowRel es kvs) :
    ∀ (X : LTerm) (a : Option P2Row),
      LRed X (optionLit (Option.map (·.2.2) a)) → closed 0 X = true →
      LRed (es.foldl
            (fun acc e => .app (.app (alookStepK keyT) acc) e) X)
           (optionLit (Option.map (·.2.2) (kvs.foldl (fun acc kv =>
              if decide (key = kv.1) then some kv else acc) a))) := by
  induction h2 with
  | nil =>
    intro X a hX _
    show LRed X (optionLit (Option.map (·.2.2) a))
    exact hX
  | cons he' h2' ih =>
    intro X a hX hXcl
    rename_i e kv es' kvs'
    obtain ⟨kT, he, hkT, hvT, hecl, hkcl, hvcl⟩ := he'
    rw [List.foldl_cons, List.foldl_cons]
    have hstep := alookStep_eval_lit key keyT hkeyT hkeycl kv.1 kT
      kv.2.2 X hkT hkcl hvcl hXcl e he hecl
    have hcl : closed 0 (.app (.app (alookStepK keyT) X) e) = true :=
      closed_app (closed_app (closed_alookStepK keyT hkeycl)
        hXcl) hecl
    cases hd : decide (key = kv.1) with
    | true =>
      have hstep' : LRed (.app (.app (alookStepK keyT) X) e)
          (optionLit (Option.map (·.2.2) (some kv : Option P2Row))) := by
        rw [hd] at hstep
        exact hstep
      exact ih _ (some kv) hstep' hcl
    | false =>
      have hstep' : LRed (.app (.app (alookStepK keyT) X) e)
          (optionLit (Option.map (·.2.2) a)) := by
        rw [hd] at hstep
        exact hstep.trans hX
      exact ih _ a hstep' hcl

/-- `alook_eval` over pairLit-form entries. -/
theorem alook_eval_lit (key : List (Fin 16)) (keyT : LTerm)
    (hkeyT : LRed keyT (scottList (key.map nibLit)))
    (hkeycl : closed 0 keyT = true)
    (es : List LTerm) (kvs : List P2Row)
    (h2 : List.Forall₂ p2RowRel es kvs)
    (hcles : ∀ e ∈ es, closed 0 e = true)
    (mapT : LTerm) (hmap : LRed mapT (scottList es))
    (hmapcl : closed 0 mapT = true) :
    LRed (aps alookL [mapT, keyT])
      (optionLit (Option.map (·.2.2) (kvs.foldl (fun acc kv =>
          if decide (key = kv.1) then some kv else acc) none))) := by
  have hopen := alookL_open mapT keyT hmapcl hkeycl
  have hstep : ∀ (acc e : LTerm), closed 0 acc = true →
      closed 0 e = true →
      LRed (.app (.app (alookStepK keyT) acc) e)
           (.app (.app (alookStepK keyT) acc) e) ∧
      closed 0 (.app (.app (alookStepK keyT) acc) e) = true :=
    fun acc e hac he =>
      ⟨Relation.ReflTransGen.refl,
       closed_app (closed_app (closed_alookStepK keyT hkeycl) hac) he⟩
  have hfold := fold_eval (alookStepK keyT)
    (fun acc e => .app (.app (alookStepK keyT) acc) e)
    (closed_alookStepK keyT hkeycl) hstep mapT klL es
    hmapcl closed_klL hmap hcles
  exact hopen.trans (hfold.trans
    (alookFold_eval_lit key keyT hkeyT hkeycl es kvs h2 klL none
      Relation.ReflTransGen.refl closed_klL))

/-- fold-map correspondence: projecting each row and folding the
    projected kvs equals projecting the row-level fold result. -/
theorem alookFold_proj {α : Type} (key : List (Fin 16))
    (kvs : List P2Row) (proj : P2Row → α) (a : Option P2Row) :
    (Option.map proj (kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv else acc) a))
      = ((kvs.map (fun kv => (kv.1, proj kv))).foldl (fun acc kv =>
          if decide (key = kv.1) then some kv.2 else acc)
        (Option.map proj a)) := by
  induction kvs generalizing a with
  | nil => rfl
  | cons kv kvs ih =>
    simp only [List.foldl_cons, List.map_cons]
    cases decide (key = kv.1) <;> exact ih _

/-- `alookSem` agrees with the row-fold under `(key, valB)`
    projection. -/
theorem alookSem_proj (key : List (Fin 16)) (kvs : List P2Row) :
    (Option.map (fun kv => kv.2.1) (kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv else acc) none))
      = alookSem key (kvs.map (fun kv => (kv.1, kv.2.1))) :=
  alookFold_proj key kvs (fun kv => kv.2.1) none


/-- the last-match fold only returns rows present in the table
    (or the initial acc). -/
theorem alookFold_mem (key : List (Fin 16)) (kvs : List P2Row)
    (a : Option P2Row) (kv : P2Row)
    (h : kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv else acc) a = some kv) :
    kv ∈ kvs ∨ a = some kv := by
  induction kvs generalizing a with
  | nil =>
    simp only [List.foldl_nil] at h
    exact Or.inr h
  | cons kv' kvs ih =>
    simp only [List.foldl_cons, List.mem_cons] at h ⊢
    cases hd : decide (key = kv'.1) with
    | true =>
      have h' := ih (some kv') (by simpa [hd] using h)
      rcases h' with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inl (Or.inl (Option.some.inj h').symm)
    | false =>
      have h' := ih a (by simpa [hd] using h)
      rcases h' with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

/-- a row occurring in a `p2RowRel`-aligned table has a row-relation
    witness entry. -/
theorem p2RowRel_of_mem {es : List LTerm} {kvs : List P2Row}
    (h2 : List.Forall₂ p2RowRel es kvs) {kv : P2Row}
    (hk : kv ∈ kvs) : ∃ e ∈ es, p2RowRel e kv := by
  induction h2 with
  | nil => exact absurd hk List.not_mem_nil
  | cons hr _ ih =>
    rw [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨e, he, hr'⟩ := ih hk
      exact ⟨e, List.mem_cons_of_mem _ he, hr'⟩

/-- **`p2Resv_eval`**: the emitted resolver `λnm. (ALOOK sym nm)
    ((ALOOK loc nm) (B4SUB b4z e4) (λlv. B4SUB lv e4))
    (λsv. B4SUB sv e4)` — symbol hit shadows the local table, a hit
    subtracts `end4` (rel32), a miss falls back to zero bytes. -/
theorem p2Resv_eval (symRows locRows : List P2Row)
    (nm : List (Fin 16)) (e4B : B4L)
    (nmT e4T sT lcT : LTerm)
    (hnmT : LRed nmT (scottList (nm.map nibLit)))
    (hnmcl : closed 0 nmT = true)
    (he4T : LRed e4T (scottList (bm e4B))) (he4cl : closed 0 e4T = true)
    (he4len : e4B.length = 4)
    (symEs : List LTerm) (hsym2 : List.Forall₂ p2RowRel symEs symRows)
    (hsymes : ∀ e ∈ symEs, closed 0 e = true)
    (hsT : LRed sT (scottList symEs)) (hscl : closed 0 sT = true)
    (hsymlen : ∀ kv ∈ symRows, kv.2.1.length = 4)
    (locEs : List LTerm) (hloc2 : List.Forall₂ p2RowRel locEs locRows)
    (hloces : ∀ e ∈ locEs, closed 0 e = true)
    (hlcT : LRed lcT (scottList locEs)) (hlccl : closed 0 lcT = true)
    (hloclen : ∀ kv ∈ locRows, kv.2.1.length = 4) :
    LRed (aps (p2ResvT sT lcT e4T) [nmT])
      (scottList (bm (resvSem
        (symRows.map (fun kv => (kv.1, kv.2.1)))
        (locRows.map (fun kv => (kv.1, kv.2.1))) nm e4B))) := by
  have hJsv : closed 0 (.abs (aps b4subL [.var 0, e4T])) = true := by
    simp only [closed, aps, List.foldl, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_b4subL
      | exact closed_mono he4cl (Nat.zero_le _)
  have hZ : closed 0 (aps b4subL [b4zL, e4T]) = true := by
    simp only [closed, aps, List.foldl, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_b4subL
      | exact closed_b4zL
      | exact closed_mono he4cl (Nat.zero_le _)
  have hInner : closed 0 (aps alookL
      [lcT, nmT, aps b4subL [b4zL, e4T],
       .abs (aps b4subL [.var 0, e4T])]) = true := by
    simp only [closed, aps, List.foldl, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_alookL
      | exact hlccl
      | exact hnmcl
      | exact hZ
      | exact hJsv
  have h1 := p2Resv_apply sT lcT e4T nmT hscl hlccl he4cl hnmcl
  have h2 := alook_eval_lit nm nmT hnmT hnmcl symEs symRows hsym2
    hsymes sT hsT hscl
  have h3 : LRed (aps alookL
        [sT, nmT,
         aps alookL
           [lcT, nmT, aps b4subL [b4zL, e4T],
            .abs (aps b4subL [.var 0, e4T])],
         .abs (aps b4subL [.var 0, e4T])])
      (aps (optionLit (Option.map (·.2.2)
          (symRows.foldl (fun acc kv =>
            if decide (nm = kv.1) then some kv else acc) none)))
        [aps alookL
           [lcT, nmT, aps b4subL [b4zL, e4T],
            .abs (aps b4subL [.var 0, e4T])],
         .abs (aps b4subL [.var 0, e4T])]) :=
    LRed_app_left (LRed_app_left h2)
  have hb4z : LRed b4zL (scottList (bm b4zeroBytes)) := by
    show LRed b4zL (scottList (List.replicate 4 (byteLit 0 0)))
    exact b4z_nf
  unfold resvSem
  simp only [← alookSem_proj nm symRows]
  cases hfo : symRows.foldl (fun acc kv =>
      if decide (nm = kv.1) then some kv else acc) none with
  | some kv =>
    rw [hfo] at h3
    simp only [Option.map] at h3
    show LRed _ (scottList (bm (subResList kv.2.1 e4B 1)))
    have hmem : kv ∈ symRows :=
      (alookFold_mem nm symRows none kv hfo).elim id
        (fun h => nomatch h)
    obtain ⟨_, _, _, _, _, hvT, _, _, hvcl⟩ :=
      p2RowRel_of_mem hsym2 hmem
    have h4 := optionSome_apply kv.2.2
      (aps alookL [lcT, nmT, aps b4subL [b4zL, e4T],
        .abs (aps b4subL [.var 0, e4T])])
      (.abs (aps b4subL [.var 0, e4T])) hvcl hInner hJsv
    have hsub : LRed (aps b4subL [kv.2.2, e4T])
        (scottList (bm (subResList kv.2.1 e4B 1))) := by
      have hcong : LRed (aps b4subL [kv.2.2, e4T])
          (aps b4subL [scottList (bm kv.2.1),
                       scottList (bm e4B)]) :=
        LRed_app (LRed_app Relation.ReflTransGen.refl hvT) he4T
      exact hcong.trans (b4sub_eval_scott kv.2.1 e4B
        ((hsymlen kv hmem).trans he4len.symm))
    have hcont := p2SubCont_apply e4T kv.2.2 he4cl hvcl
    exact h1.trans (h3.trans (h4.trans (hcont.trans hsub)))
  | none =>
    rw [hfo] at h3
    simp only [Option.map] at h3
    have h4 := optionNone_apply
      (aps alookL [lcT, nmT, aps b4subL [b4zL, e4T],
        .abs (aps b4subL [.var 0, e4T])])
      (.abs (aps b4subL [.var 0, e4T]))
    have h5 := alook_eval_lit nm nmT hnmT hnmcl locEs locRows hloc2
      hloces lcT hlcT hlccl
    have h6 : LRed (aps alookL
          [lcT, nmT, aps b4subL [b4zL, e4T],
           .abs (aps b4subL [.var 0, e4T])])
        (aps (optionLit (Option.map (·.2.2)
            (locRows.foldl (fun acc kv =>
              if decide (nm = kv.1) then some kv else acc) none)))
          [aps b4subL [b4zL, e4T],
           .abs (aps b4subL [.var 0, e4T])]) :=
      LRed_app_left (LRed_app_left h5)
    simp only [← alookSem_proj nm locRows]
    cases hfo2 : locRows.foldl (fun acc kv =>
        if decide (nm = kv.1) then some kv else acc) none with
    | some kv =>
      rw [hfo2] at h6
      simp only [Option.map] at h6
      show LRed _ (scottList (bm (subResList kv.2.1 e4B 1)))
      have hmem : kv ∈ locRows :=
        (alookFold_mem nm locRows none kv hfo2).elim id
          (fun h => nomatch h)
      obtain ⟨_, _, _, _, _, hvT, _, _, hvcl⟩ :=
        p2RowRel_of_mem hloc2 hmem
      have h7 := optionSome_apply kv.2.2
        (aps b4subL [b4zL, e4T])
        (.abs (aps b4subL [.var 0, e4T])) hvcl hZ hJsv
      have hsub : LRed (aps b4subL [kv.2.2, e4T])
          (scottList (bm (subResList kv.2.1 e4B 1))) := by
        have hcong : LRed (aps b4subL [kv.2.2, e4T])
            (aps b4subL [scottList (bm kv.2.1),
                         scottList (bm e4B)]) :=
          LRed_app (LRed_app Relation.ReflTransGen.refl hvT) he4T
        exact hcong.trans (b4sub_eval_scott kv.2.1 e4B
          ((hloclen kv hmem).trans he4len.symm))
      have hcont := p2SubCont_apply e4T kv.2.2 he4cl hvcl
      exact h1.trans (h3.trans (h4.trans (h6.trans (h7.trans
        (hcont.trans hsub)))))
    | none =>
      rw [hfo2] at h6
      simp only [Option.map] at h6
      show LRed _ (scottList (bm (subResList b4zeroBytes e4B 1)))
      have h7 := optionNone_apply
        (aps b4subL [b4zL, e4T])
        (.abs (aps b4subL [.var 0, e4T]))
      have hcong : LRed (aps b4subL [b4zL, e4T])
          (aps b4subL [scottList (bm b4zeroBytes),
                       scottList (bm e4B)]) :=
        LRed_app (LRed_app Relation.ReflTransGen.refl hb4z) he4T
      have hsub := hcong.trans (b4sub_eval_scott b4zeroBytes e4B
        (by simp [b4zeroBytes, he4len]))
      exact h1.trans (h3.trans (h4.trans (h6.trans (h7.trans hsub))))


/-- `foldr cellLit` onto a Scott-list seed is `scottList` of the
    concatenated cells. -/
theorem foldr_cellLit_scott (cs acc : List LTerm) :
    cs.foldr cellLit (scottList acc) = scottList (cs ++ acc) := by
  show cs.foldr cellLit (acc.foldr cellLit nilL)
    = (cs ++ acc).foldr cellLit nilL
  rw [List.foldr_append]

/-- per-item contract for pass-2 emission: the item satisfies the
    encoder contract under ITS OWN resolver (the `end4` built from
    this entry's `of`/`ln` bytes), and its byte output normalizes to
    the declared emitted bytes. -/
def p2ItmV (encT sT lcT basT : LTerm) (e : P2Item) : Prop :=
  AsmItem.V encT (p2ResvT sT lcT
    (aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
                 scottList (bm e.2.2.1)])) e.1 ∧
  LRed e.1.byT (scottList (bm e.2.2.2))

/-- **`p2_step_eval`**: one emitted pass-2 step —
    `emitstep·acc·rec` evaluates to the semantic `p2StepSem`:
    label entries pass the accumulator through, instruction entries
    prepend the encoder's emitted bytes in reverse-cell order. -/
theorem p2_step_eval (encT sT lcT basT accT recT : LTerm)
    (basB : B4L) (e : P2Item) (acc : List LTerm)
    (he : closed 0 encT = true) (hs : closed 0 sT = true)
    (hlc : closed 0 lcT = true) (hb : closed 0 basT = true)
    (ha : closed 0 accT = true) (hr : closed 0 recT = true)
    (hbas : LRed basT (scottList (bm basB)))
    (hrec : LRed recT (p2EntryT e))
    (hit : p2ItmV encT sT lcT basT e)
    (hacc : LRed accT (scottList acc))
    (haccc : ∀ c ∈ acc, closed 0 c = true)
    (hb4 : basB.length = 4) (hof4 : e.2.1.length = 4)
    (hln4 : e.2.2.1.length = 4) :
    LRed (aps (emitStepT encT sT lcT basT) [accT, recT])
         (scottList (p2StepSem e acc)) := by
  obtain ⟨hitV, hby⟩ := hit
  obtain ⟨⟨tgT, rrT, hitC, htag, _hrr2, htgcl, hrrcl⟩, hitcl, _hrrCs,
      hbycl, hlncl, henc, _hlnT⟩ := hitV
  -- closedness of the entry components
  have hof4cl : closed 0 (scottList (bm e.2.1)) = true :=
    closed_scott_bm _
  have hln4cl : closed 0 (scottList (bm e.2.2.1)) = true :=
    closed_scott_bm _
  have holcl : closed 0 (pairLit (scottList (bm e.2.1))
      (scottList (bm e.2.2.1))) = true :=
    closed_pairLit (closed_mono hof4cl (Nat.zero_le 1))
      (closed_mono hln4cl (Nat.zero_le 1))
  have he4cl : closed 0 (aps b4addL
      [aps b4addL [basT, scottList (bm e.2.1)],
       scottList (bm e.2.2.1)]) = true := by
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    repeat' constructor
    all_goals first
      | exact closed_b4addL
      | exact hb
      | exact hof4cl
      | exact hln4cl
  have hrsv : closed 0 (p2ResvT sT lcT (aps b4addL
      [aps b4addL [basT, scottList (bm e.2.1)],
       scottList (bm e.2.2.1)])) = true :=
    closed_p2ResvT 0 (closed_mono hs (Nat.zero_le 1))
      (closed_mono hlc (Nat.zero_le 1))
      (closed_mono he4cl (Nat.zero_le 1))
  -- prefix: open + destructure + dispatch
  have s1 := p2Step_open encT sT lcT basT accT recT he hs hlc hb ha hr
  have s2 : LRed (.app recT (p2RecContT encT sT lcT basT accT))
      (aps (p2RecContT encT sT lcT basT accT) [e.1.itT,
        pairLit (scottList (bm e.2.1)) (scottList (bm e.2.2.1))]) :=
    (LRed_app_left hrec).trans
      (pairLit_apply e.1.itT _ _ hitcl holcl)
  have s3 := p2RecCont_apply encT sT lcT basT accT e.1.itT
    (pairLit (scottList (bm e.2.1)) (scottList (bm e.2.2.1)))
    he hs hlc hb ha hitcl holcl
  have s4 : LRed (.app (pairLit (scottList (bm e.2.1))
        (scottList (bm e.2.2.1)))
        (p2OfLnContT encT sT lcT basT accT e.1.itT))
      (aps (p2OfLnContT encT sT lcT basT accT e.1.itT)
        [scottList (bm e.2.1), scottList (bm e.2.2.1)]) :=
    pairLit_apply _ _ _ hof4cl hln4cl
  have s5 := p2OfLn_apply encT sT lcT basT accT e.1.itT
    (scottList (bm e.2.1)) (scottList (bm e.2.2.1))
    he hs hlc hb ha hitcl hof4cl hln4cl
  have s6 : LRed (aps e.1.itT [klL,
        p2DispS encT sT lcT basT accT e.1.itT
          (scottList (bm e.2.1)) (scottList (bm e.2.2.1))])
      (aps (p2DispS encT sT lcT basT accT e.1.itT
          (scottList (bm e.2.1)) (scottList (bm e.2.2.1)))
        [tgT, rrT]) :=
    (LRed_app_left (LRed_app_left hitC)).trans
      (cellLit_apply2 tgT rrT klL _ htgcl hrrcl)
  have s7 := p2Disp_open encT sT lcT basT accT e.1.itT
    (scottList (bm e.2.1)) (scottList (bm e.2.2.1)) tgT rrT
    he hs hlc hb ha hitcl hof4cl hln4cl htgcl hrrcl
  -- eqStr prefix → boolLit
  have hnib : ∀ x ∈ e.1.ns.map nibLit, closed 0 x = true :=
    fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx; exact closed_nibLit _
  have hlen : LRed (aps lenL [tgT])
      (succChain kilL e.1.ns.length) := by
    have h1 := (LRed_app_right htag).trans
      (len_eval (e.1.ns.map nibLit) hnib)
    rw [List.length_map] at h1; exact h1
  have hlencl : closed 0 (aps lenL [tgT]) = true := by
    simp only [aps, List.foldl, closed, Bool.and_eq_true]
    exact ⟨closed_lenL, htgcl⟩
  have heq3 := eqStr_eval e.1.ns lblNibs e.1.ns.length (Nat.le_refl _)
    tgT lblL (aps lenL [tgT]) htag lbl_nf hlen htgcl closed_lblL hlencl
  have hsel : LRed (aps eqStrL [tgT, lblL, aps lenL [tgT], accT,
        aps (p2E4ContT encT sT lcT accT e.1.itT)
          [aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
            scottList (bm e.2.2.1)]]])
      (aps (boolLit (decide (e.1.ns = lblNibs)))
        [accT, aps (p2E4ContT encT sT lcT accT e.1.itT)
          [aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
            scottList (bm e.2.2.1)]]]) :=
    LRed_app_left (LRed_app_left heq3)
  have hsel' := hsel.trans (boolLit_sel _ _ _)
  by_cases hns : e.1.ns = lblNibs
  · have hdec : decide (e.1.ns = lblNibs) = true := by
      rw [hns]; decide
    rw [hdec] at hsel'
    have hsem : p2StepSem e acc = acc := by simp [p2StepSem, hns]
    rw [hsem]
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans
      (s6.trans (s7.trans (hsel'.trans hacc)))))))
  · have hdec : decide (e.1.ns = lblNibs) = false :=
      decide_eq_false hns
    rw [hdec] at hsel'
    have hsem : p2StepSem e acc = (bm e.2.2.2).reverse ++ acc := by
      simp [p2StepSem, hns]
    rw [hsem]
    -- insn chain: end4 = B4ADD (B4ADD base of) ln
    have b1 : LRed (aps b4addL [basT, scottList (bm e.2.1)])
        (scottList (bm (resList basB e.2.1 0))) := by
      have h : LRed (aps b4addL [scottList (bm basB),
          scottList (bm e.2.1)])
          (scottList (bm (resList basB e.2.1 0))) :=
        b4add_eval_scott basB e.2.1 (hb4.trans hof4.symm)
      exact (LRed_app_left (LRed_app_right hbas)).trans h
    have b2 : LRed (aps b4addL
        [aps b4addL [basT, scottList (bm e.2.1)],
         scottList (bm e.2.2.1)])
        (scottList (bm (end4Sem basB e.2.1 e.2.2.1))) := by
      have h1 : LRed (aps b4addL
          [scottList (bm (resList basB e.2.1 0)),
           scottList (bm e.2.2.1)])
          (scottList (bm (resList (resList basB e.2.1 0)
            e.2.2.1 0))) :=
        b4add_eval_scott _ _ ((resList_len basB e.2.1 0
          (hb4.trans hof4.symm)).trans (hb4.trans hln4.symm))
      have h0 : LRed (aps b4addL
          [aps b4addL [basT, scottList (bm e.2.1)],
           scottList (bm e.2.2.1)])
          (aps b4addL [scottList (bm (resList basB e.2.1 0)),
            scottList (bm e.2.2.1)]) :=
        LRed_app_left (LRed_app_right b1)
      have h := h0.trans h1
      show LRed _ (scottList (bm (end4Sem basB e.2.1 e.2.2.1)))
      exact h
    have s8 := p2E4_apply encT sT lcT accT e.1.itT
      (aps b4addL [aps b4addL [basT, scottList (bm e.2.1)],
        scottList (bm e.2.2.1)])
      he hs hlc ha hitcl he4cl
    have s9 := p2RsvCont_apply encT accT e.1.itT
      (p2ResvT sT lcT (aps b4addL
        [aps b4addL [basT, scottList (bm e.2.1)],
         scottList (bm e.2.2.1)]))
      he ha hitcl hrsv
    have s10 := p2Enc_apply encT accT e.1.itT
      (p2ResvT sT lcT (aps b4addL
        [aps b4addL [basT, scottList (bm e.2.1)],
         scottList (bm e.2.2.1)]))
      he ha hitcl hrsv
    -- fst projection + byte-list fold
    have hbyt : LRed (.app (aps encT [e.1.itT,
          p2ResvT sT lcT (aps b4addL
            [aps b4addL [basT, scottList (bm e.2.1)],
             scottList (bm e.2.2.1)])]) klL)
        (scottList (bm e.2.2.2)) :=
      (LRed_app_left henc).trans
        ((pairLit_fst e.1.byT e.1.lnT hbycl hlncl).trans hby)
    have hfold : LRed (aps foldlL [consRevL,
          .app (aps encT [e.1.itT, p2ResvT sT lcT (aps b4addL
            [aps b4addL [basT, scottList (bm e.2.1)],
             scottList (bm e.2.2.1)])]) klL,
          accT])
        (ggbA consRevL (scottList (bm e.2.2.2)) (scottList acc)) := by
      have h0 : LRed (aps foldlL [consRevL,
          .app (aps encT [e.1.itT, p2ResvT sT lcT (aps b4addL
            [aps b4addL [basT, scottList (bm e.2.1)],
             scottList (bm e.2.2.1)])]) klL,
          accT])
          (aps foldlL [consRevL, scottList (bm e.2.2.2),
            scottList acc]) :=
        (LRed_app_left (LRed_app_right hbyt)).trans
          (LRed_app_right hacc)
      exact h0.trans (foldl_to_ggb _ _ _ closed_consRevL
        (closed_scott_bm _) (closed_scottList haccc))
    have hread : LRed (ggbA consRevL (scottList (bm e.2.2.2))
        (scottList acc))
        (scottList ((bm e.2.2.2).reverse ++ acc)) := by
      show LRed (ggbA stepConsL (scottList (bm e.2.2.2))
        (scottList acc)) _
      have h := fold_read _ _
        (fun (x : LTerm) (hx : x ∈ bm e.2.2.2) => closed_bm hx)
        (closed_scottList haccc)
      rw [foldr_cellLit_scott] at h
      exact h
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans
      (s6.trans (s7.trans (hsel'.trans (s8.trans (s9.trans
        (s10.trans (hfold.trans hread)))))))))))

/-- `p2StepSem` preserves accumulator-cell closedness. -/
theorem p2StepSem_wf (e : P2Item) (acc : List LTerm)
    (h : ∀ c ∈ acc, closed 0 c = true) :
    ∀ c ∈ p2StepSem e acc, closed 0 c = true := by
  by_cases hns : e.1.ns = lblNibs
  · simp [p2StepSem, hns]; exact h
  · have hd : decide (e.1.ns = lblNibs) = false := decide_eq_false hns
    unfold p2StepSem
    rw [hd]
    show ∀ c ∈ (bm e.2.2.2).reverse ++ acc, closed 0 c = true
    intro c hc
    simp only [List.mem_append, List.mem_reverse] at hc
    rcases hc with hc | hc
    · exact closed_bm hc
    · exact h c hc

/-- fold-start congruence over prep-entry terms. -/
theorem p2Fold_cong (st : LTerm) : ∀ (ts : List LTerm) (X a : LTerm),
    LRed X a →
    LRed (ts.foldl (fun acc t => aps st [acc, t]) X)
         (ts.foldl (fun acc t => aps st [acc, t]) a) := by
  intro ts; induction ts with
  | nil => intro X a h; exact h
  | cons t ts ih =>
    intro X a h
    exact ih _ _ (LRed_app_left (LRed_app_right h))

/-- entry-term ↔ item correspondence for the pass-2 fold. -/
def p2EntryRel (t : LTerm) (e : P2Item) : Prop :=
  LRed t (p2EntryT e) ∧ closed 0 t = true

/-- the emitted pass-2 fold over prep entries evaluates to the
    semantic `p2StepSem`-fold (accumulator threaded as a Scott-list
    of emitted cells). -/
theorem p2Fold_eval (encT sT lcT basT : LTerm) (basB : B4L)
    (he : closed 0 encT = true) (hs : closed 0 sT = true)
    (hlc : closed 0 lcT = true) (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4)
    {es : List P2Item} {ts : List LTerm}
    (h2 : List.Forall₂ p2EntryRel ts es) :
    (∀ e ∈ es, p2ItmV encT sT lcT basT e) →
    (∀ e ∈ es, e.2.1.length = 4 ∧ e.2.2.1.length = 4) →
    ∀ (acc : List LTerm) (accT : LTerm),
      (∀ c ∈ acc, closed 0 c = true) → closed 0 accT = true →
      LRed accT (scottList acc) →
      LRed (ts.foldl (fun a t =>
            aps (emitStepT encT sT lcT basT) [a, t]) accT)
           (scottList (es.foldl (fun a e => p2StepSem e a) acc)) := by
  induction h2 with
  | nil => intro _ _ acc accT _ _ hacc; exact hacc
  | cons hstep h2' ih =>
    rename_i t e ts' es'
    obtain ⟨he', htcl⟩ := hstep
    intro hV hlen acc accT haccc haccl hacc
    simp only [List.foldl_cons]
    have hVit := hV e List.mem_cons_self
    have hleni := hlen e List.mem_cons_self
    have hVtl : ∀ x ∈ es', p2ItmV encT sT lcT basT x := fun x hx =>
      hV x (List.mem_cons_of_mem _ hx)
    have hlenTl : ∀ x ∈ es', x.2.1.length = 4 ∧
        x.2.2.1.length = 4 := fun x hx =>
      hlen x (List.mem_cons_of_mem _ hx)
    have hstep' := p2_step_eval encT sT lcT basT accT t basB e acc
      he hs hlc hb haccl htcl hbas he' hVit hacc haccc hb4
      hleni.1 hleni.2
    have hwf := p2StepSem_wf e acc haccc
    have hcl' := closed_scottList hwf
    have hcong := p2Fold_cong (emitStepT encT sT lcT basT) ts'
      (aps (emitStepT encT sT lcT basT) [accT, t])
      (scottList (p2StepSem e acc)) hstep'
    exact hcong.trans (ih hVtl hlenTl (p2StepSem e acc)
      (scottList (p2StepSem e acc)) hwf hcl'
      Relation.ReflTransGen.refl)


/-- `pairLit` second-projection under the `K·I`-application form
    (`KI` as `aps klL [idL]`, the selector asmLocV/asmPrepV emit). -/
theorem pairLit_sndKI (a b : LTerm) (ha : closed 0 a = true)
    (hb : closed 0 b = true) :
    LRed (.app (pairLit a b) (aps klL [idL])) b := by
  refine (pairLit_apply a b (aps klL [idL]) ha hb).trans ?_
  show LRed (aps (aps klL [idL]) [a, b]) b
  exact kiApp_apply2 a b

/-- program-level pass-1 well-formedness: the fragment fold
    preserves loc/prep closedness and pos-length. -/
theorem p1ProgSem_wf (encT zrvT : LTerm) (basB : B4L) :
    ∀ (frs : List (List AsmItem)),
    (∀ it ∈ frs.flatten, AsmItem.V encT zrvT it) →
    (∀ it ∈ frs.flatten, it.ns = lblNibs →
        ∃ nm rest, it.rrCs = nm :: rest) →
    ∀ (st : P1St),
      (∀ c ∈ st.2.1, closed 0 c = true) →
      (∀ c ∈ st.2.2, closed 0 c = true) →
      st.1.length = 4 →
      (∀ c ∈ (p1ProgSem basB frs st).2.1, closed 0 c = true) ∧
      (∀ c ∈ (p1ProgSem basB frs st).2.2, closed 0 c = true) ∧
      (p1ProgSem basB frs st).1.length = 4 := by
  intro frs
  induction frs with
  | nil => intro _ _ st h1 h2 hl4; exact ⟨h1, h2, hl4⟩
  | cons its frs ih =>
    intro hV hrrn st h1 h2 hl4
    simp only [p1ProgSem, List.foldl_cons]
    have hVh : ∀ i ∈ its, AsmItem.V encT zrvT i := fun i hi =>
      hV i (List.mem_flatten.mpr ⟨its, List.mem_cons_self, hi⟩)
    have hrrh : ∀ i ∈ its, i.ns = lblNibs →
        ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
      hrrn i (List.mem_flatten.mpr ⟨its, List.mem_cons_self, hi⟩)
    have hVr : ∀ i ∈ frs.flatten, AsmItem.V encT zrvT i :=
      fun i hi => hV i (List.mem_flatten.mpr (by
        obtain ⟨l', hl', hmem⟩ := List.mem_flatten.mp hi
        exact ⟨l', List.mem_cons_of_mem _ hl', hmem⟩))
    have hrrr : ∀ i ∈ frs.flatten, i.ns = lblNibs →
        ∃ nm rest, i.rrCs = nm :: rest := fun i hi =>
      hrrn i (List.mem_flatten.mpr (by
        obtain ⟨l', hl', hmem⟩ := List.mem_flatten.mp hi
        exact ⟨l', List.mem_cons_of_mem _ hl', hmem⟩))
    exact ih hVr hrrr (its.foldl (fun s i => p1StepSem basB i s) st)
      (p1Fold_wf encT zrvT basB its hVh hrrh st h1 h2 hl4).1
      (p1Fold_wf encT zrvT basB its hVh hrrh st h1 h2 hl4).2.1
      (p1Fold_wf encT zrvT basB its hVh hrrh st h1 h2 hl4).2.2

/-- the pass-2 fold preserves accumulator-cell closedness. -/
theorem p2FoldSem_wf : ∀ (es : List P2Item) (acc : List LTerm),
    (∀ c ∈ acc, closed 0 c = true) →
    ∀ c ∈ es.foldl (fun a e => p2StepSem e a) acc,
      closed 0 c = true := by
  intro es; induction es with
  | nil => intro acc h c hc; exact h c hc
  | cons e es ih =>
    intro acc h c hc
    simp only [List.foldl_cons] at hc
    exact ih (p2StepSem e acc) (p2StepSem_wf e acc h) c hc

/-- **`asm_eval`**: the whole `assemble` stage reduces to
    `PAIR (REV (p2FoldSem prep)) loc` — emitted bytes in forward
    order paired with the pass-1 local table. -/
theorem asm_eval (encT zrvT progT symT basT : LTerm)
    (basB : B4L) (st : P1St) (es : List P2Item)
    (he : closed 0 encT = true) (hz : closed 0 zrvT = true)
    (hp : closed 0 progT = true) (hs : closed 0 symT = true)
    (hb : closed 0 basT = true)
    (hbas : LRed basT (scottList (bm basB))) (hb4 : basB.length = 4)
    (hp1 : LRed (p1ValT encT zrvT progT basT) (p1AccTV st))
    (hwf1 : ∀ c ∈ st.2.1, closed 0 c = true)
    (hwf2 : ∀ c ∈ st.2.2, closed 0 c = true)
    (h2 : List.Forall₂ p2EntryRel st.2.2.reverse es)
    (hV : ∀ e ∈ es, p2ItmV encT symT
        (asmLocV (p1ValT encT zrvT progT basT)) basT e)
    (hlen : ∀ e ∈ es, e.2.1.length = 4 ∧ e.2.2.1.length = 4) :
    LRed (aps asmL [encT, zrvT, progT, symT, basT])
      (pairLit (scottList (p2FoldSem es).reverse)
               (scottList st.2.1)) := by
  set p1V := p1ValT encT zrvT progT basT with hp1V
  have hp1Vc : closed 0 p1V = true :=
    closed_p1ValT 0 he hz hp hb
  have hKI : closed 0 (aps klL [idL]) = true :=
    closed_app closed_klL closed_idL
  have hinnercl : closed 0 (aps p1V [aps klL [idL],
      aps klL [idL]]) = true :=
    closed_app (closed_app hp1Vc hKI) hKI
  have hloccl' : closed 0 (asmLocV p1V) = true :=
    closed_app (closed_app hp1Vc hKI) closed_klL
  have hprepcl : closed 0 (asmPrepV p1V) = true :=
    closed_app closed_revL hinnercl
  -- p1V projections: loc = snd·fst, prep = REV (snd·snd)
  have hposcl : closed 0 (scottList (bm st.1)) = true :=
    closed_scott_bm _
  have hlocc : closed 0 (scottList st.2.1) = true :=
    closed_scottList hwf1
  have hprepc : closed 0 (scottList st.2.2) = true :=
    closed_scottList hwf2
  have hlp : closed 0 (pairLit (scottList st.2.1)
      (scottList st.2.2)) = true :=
    closed_pairLit (closed_mono hlocc (Nat.zero_le 1))
      (closed_mono hprepc (Nat.zero_le 1))
  have hloc : LRed (asmLocV p1V) (scottList st.2.1) := by
    refine (LRed_app_left (LRed_app_left hp1)).trans ?_
    unfold p1AccTV p1AccT
    exact (LRed_app_left (pairLit_sndKI _ _ hposcl hlp)).trans
      (pairLit_fst _ _ hlocc hprepc)
  have hprep : LRed (asmPrepV p1V) (scottList st.2.2.reverse) := by
    show LRed (aps revL [aps p1V [aps klL [idL], aps klL [idL]]]) _
    have h1 : LRed (aps p1V [aps klL [idL], aps klL [idL]])
        (scottList st.2.2) := by
      refine (LRed_app_left (LRed_app_left hp1)).trans ?_
      unfold p1AccTV p1AccT
      exact (LRed_app_left (pairLit_sndKI _ _ hposcl hlp)).trans
        (pairLit_sndKI _ _ hlocc hprepc)
    exact revL_eval _ _ hinnercl hwf2 h1
  -- the emit fold
  have hstepcl : closed 0 (emitStepT encT symT (asmLocV p1V) basT) =
      true := closed_emitStepT 0 he hs hloccl' hb
  have htscl : ∀ c ∈ st.2.2.reverse, closed 0 c = true :=
    fun c hc => hwf2 c (List.mem_reverse.mp hc)
  have hrevsccl : closed 0 (scottList st.2.2.reverse) = true :=
    closed_scottList htscl
  have hout : LRed (asmOutV encT symT basT p1V)
      (scottList (p2FoldSem es)) := by
    show LRed (aps foldlL
        [emitStepT encT symT (asmLocV p1V) basT,
         asmPrepV p1V, klL]) (scottList (p2FoldSem es))
    have h0 : LRed (aps foldlL
          [emitStepT encT symT (asmLocV p1V) basT,
           asmPrepV p1V, klL])
        (ggbA (emitStepT encT symT (asmLocV p1V) basT)
          (scottList st.2.2.reverse) klL) :=
      (LRed_app_left (LRed_app_right hprep)).trans
        (foldl_to_ggb _ _ _ hstepcl hrevsccl closed_klL)
    have h1 := fold_run _ hstepcl st.2.2.reverse klL htscl closed_klL
    have h2' := p2Fold_eval encT symT (asmLocV p1V) basT basB
      he hs hloccl' hb hbas hb4 h2 hV hlen [] klL
      (fun c hc => nomatch hc) closed_klL
      Relation.ReflTransGen.refl
    have h := h0.trans (h1.trans h2')
    show LRed _ (scottList (p2FoldSem es))
    exact h
  -- REV out + PAIR
  have houtcl : closed 0 (asmOutV encT symT basT p1V) = true :=
    closed_app (closed_app (closed_app closed_foldlL hstepcl)
      hprepcl) closed_klL
  have hcells : ∀ c ∈ p2FoldSem es, closed 0 c = true :=
    p2FoldSem_wf es [] (fun c hc => nomatch hc)
  have hrev : LRed (aps revL [asmOutV encT symT basT p1V])
      (scottList (p2FoldSem es).reverse) :=
    revL_eval _ _ houtcl hcells hout
  have hrevcl : closed 0 (scottList (p2FoldSem es).reverse) = true :=
    closed_scottList (fun c hc => hcells c (List.mem_reverse.mp hc))
  have hopen := asm_open encT zrvT progT symT basT he hz hp hs hb
  have hfinal : LRed (aps pairSrcL
        [aps revL [asmOutV encT symT basT p1V], asmLocV p1V])
      (pairLit (scottList (p2FoldSem es).reverse)
               (scottList st.2.1)) :=
    pairSrcCell_nf hrev hloc hrevcl hlocc
  exact hopen.trans hfinal

end ISAR
