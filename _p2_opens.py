import io
txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

# fix p2RecContT: inline the .var 3 (it) under of/ln binders —
# passing (.var 1) into p2OfLnContT would shift-misplace it.
old = '''/-- `λit.λol. ol·(λof.λln. it·K·disp)` — the rec continuation. -/
def p2RecContT (e s lc b accT : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0) [p2OfLnContT e s lc b accT (.var 1)]))'''
new = '''/-- `λit.λol. ol·(λof.λln. it·K·disp)` — the rec continuation.
    `it` stays `.var 3` inside the of/ln binders (the emitted
    index); it is NOT a p2OfLnContT application. -/
def p2RecContT (e s lc b accT : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0) [.abs (.abs (aps (.var 3)
    [klL, p2DispT e s lc b accT (.var 3)]))]))'''
assert old in txt, 'p2RecContT'
txt = txt.replace(old, new)

# its closedness: unfold p2DispT chain stays same; reword
old2 = '''theorem closed_p2RecContT {e s lc b a : LTerm} (c : Nat)
    (he : closed 2 e = true) (hs : closed 2 s = true)
    (hl : closed 2 lc = true) (hb : closed 2 b = true)
    (ha : closed 2 a = true) :
    closed c (p2RecContT e s lc b a) = true := by
  simp only [p2RecContT, p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT,
             p2ResvRawT, closed, aps, List.foldl, Bool.and_eq_true]'''
new2 = '''theorem closed_p2RecContT {e s lc b a : LTerm} (c : Nat)
    (he : closed 2 e = true) (hs : closed 2 s = true)
    (hl : closed 2 lc = true) (hb : closed 2 b = true)
    (ha : closed 2 a = true) :
    closed c (p2RecContT e s lc b a) = true := by
  simp only [p2RecContT, p2DispT, p2E4ContT, p2RsvContT,
             p2ResvRawT, closed, aps, List.foldl, Bool.and_eq_true]'''
assert old2 in txt, 'closed_p2RecContT'
txt = txt.replace(old2, new2)

opens = '''
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
    simp [emitStepT, p2RecContT, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, aps, List.foldl, hsteps, hstep, subst,
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
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  have c10 : ∀ c, closed c klL = true := fun c =>
    closed_mono closed_klL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p2RecContT, p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, ci, co, c1, c2, c3, c4, c5, c6, c7,
          c9, c10])

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
  exact LRed_of_hsteps (k := 2) (by
    simp [p2OfLnContT, p2DispS, p2E4ContT, p2RsvContT,
          p2ResvRawT, aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, ci, co, cn, c1, c2, c3, c4, c5, c6,
          c7, c9, c10])

/-- `dispS·tg·rr →* EQSTR tg lbl (LEN tg) acc (E4CHAIN of ln)`. -/
theorem p2Disp_open (e s lc b accT itT ofT lnT tgT rrT : LTerm)
    (he : closed 0 e = true) (hs : closed 0 s = true)
    (hl : closed 0 lc = true) (hb : closed 0 b = true)
    (ha : closed 0 accT = true) (hi : closed 0 itT = true)
    (ho : closed 0 ofT = true) (hn : closed 0 lnT = true)
    (ht : closed 0 tgT = true) (hr : closed 0 rrT = true) :
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
  have cr : ∀ c, closed c rrT = true := fun c =>
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
  have c9 : ∀ c, closed c foldlL = true := fun c =>
    closed_mono closed_foldlL (Nat.zero_le c)
  exact LRed_of_hsteps (k := 2) (by
    simp [p2DispS, p2E4ContT, p2RsvContT, p2ResvRawT, aps,
          List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, cs, clc, cb, ca, ci, co, cn, ct, cr, c1, c2, c3, c4,
          c5, c6, c7, c9])

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
  have c1 : ∀ c, closed c eqStrL = true := fun c =>
    closed_mono closed_eqStrL (Nat.zero_le c)
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
          ce, cs, clc, ca, ci, ce4, c1, c4, c5, c6, c9, c10, c11])

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
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed,
          ce, ca, ci, cr, c9, c10, c11])

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

end ISAR
'''
txt = txt.replace('\nend ISAR', opens)
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('opens appended')
