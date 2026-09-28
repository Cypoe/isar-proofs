import io
txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()

old = '''/-- `λit.λol. ol·(λof.λln. it·K·disp)` — the rec continuation.
    `it` stays `.var 3` inside the of/ln binders (the emitted
    index); it is NOT a p2OfLnContT application. -/
def p2RecContT (e s lc b accT : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0) [.abs (.abs (aps (.var 3)
    [klL, p2DispT e s lc b accT (.var 3)]))]))'''
new = '''/-- `λit.λol. ol·(λof.λln. it·K·disp)` — the rec continuation
    (emitted form, inlined: `it` is `.var 3` at the K-spine and
    `.var 7` inside ENC, `of`/`ln` are `.var 3`/`.var 2` in the
    B4ADD chain, `acc` is spliced). -/
def p2RecContT (e s lc b accT : LTerm) : LTerm :=
  .abs (.abs (aps (.var 0)
    [.abs (.abs (aps (.var 3)
      [klL, .abs (.abs (aps eqStrL
        [.var 1, lblL, aps lenL [.var 1], accT,
         aps (.abs (aps (.abs (aps (.abs (aps foldlL
               [consRevL, aps (.var 0) [klL], accT])
               [aps e [.var 7, .var 0]]))
              [p2ResvRawT s lc]))
           [aps b4addL [aps b4addL [b, .var 3], .var 2]]])])]))]]))'''
assert old in txt, 'p2RecContT'
txt = txt.replace(old, new)

old2 = '''  simp only [p2RecContT, p2DispT, p2E4ContT, p2RsvContT,
             p2ResvRawT, closed, aps, List.foldl, Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)'''
new2 = '''  simp only [p2RecContT, p2ResvRawT, closed, aps, List.foldl,
             Bool.and_eq_true]
  repeat' constructor
  all_goals first
    | exact closed_mono he (by omega)
    | exact closed_mono hs (by omega)
    | exact closed_mono hl (by omega)
    | exact closed_mono hb (by omega)
    | exact closed_mono ha (by omega)'''
assert old2 in txt, 'closed_p2RecContT'
txt = txt.replace(old2, new2)

# p2Step_open simp set: unfold consRevL too (emitted has inline consRev)
txt = txt.replace('''    simp [emitStepT, p2RecContT, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, aps, List.foldl, hsteps, hstep, subst,''',
'''    simp [emitStepT, p2RecContT, p2ResvRawT, consRevL, aps,
          List.foldl, hsteps, hstep, subst,''')

# p2RecCont_apply: staged defs on both sides — keep p2DispT unfold
# set but p2RecContT no longer references p2DispT/p2E4ContT/etc.
txt = txt.replace('''    simp [p2RecContT, p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, aps, List.foldl, hsteps, hstep, subst,''',
'''    simp [p2RecContT, p2OfLnContT, p2DispT, p2E4ContT, p2RsvContT,
          p2ResvRawT, consRevL, aps, List.foldl, hsteps, hstep,
          subst,''')

io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('recfix applied')
