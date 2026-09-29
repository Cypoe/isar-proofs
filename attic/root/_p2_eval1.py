import io

txt = io.open('_spec_p2_work.lean', encoding='utf-8').read()
assert txt.rstrip().endswith('end ISAR')

block = '''
-- ---------- eval helpers ---------------------------------------------------

/-- `JUST·v·n·j →* j·v` — the option-some select. -/
theorem justL_apply3 (v n j : LTerm) (hv : closed 0 v = true)
    (hn : closed 0 n = true) (hj : closed 0 j = true) :
    LRed (aps justL [v, n, j]) (.app j v) :=
  LRed_of_hsteps (k := 3) (by
    simp [justL, aps, List.foldl, hsteps, hstep, subst,
          shift_of_closed0 hv, subst_of_closed0 hv,
          shift_of_closed0 hn, subst_of_closed0 hn,
          shift_of_closed0 hj, subst_of_closed0 hj])

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

/-- `(λsv. B4SUB sv e4)·v →* B4SUB v e4` — the resolver's
    subtraction continuation. -/
theorem p2SubCont_apply (e4 v : LTerm) (he4 : closed 0 e4 = true)
    (hv : closed 0 v = true) :
    LRed (aps (.abs (aps b4subL [.var 0, e4])) [v])
      (aps b4subL [v, e4]) :=
  LRed_of_hsteps (k := 1) (by
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed0 he4, subst_of_closed0 hv,
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
      LRed X (optionLit (a.map (·.2.2))) → closed 0 X = true →
      LRed (es.foldl
            (fun acc e => .app (.app (alookStepK keyT) acc) e) X)
           (optionLit ((kvs.foldl (fun acc kv =>
              if decide (key = kv.1) then some kv else acc) a)
             .map (·.2.2))) := by
  induction h2 with
  | nil =>
    intro X a hX _
    show LRed X (optionLit (a.map (·.2.2)))
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
          (optionLit ((some kv : Option P2Row).map (·.2.2))) := by
        rw [hd] at hstep
        exact hstep
      exact ih _ (some kv) hstep' hcl
    | false =>
      have hstep' : LRed (.app (.app (alookStepK keyT) X) e)
          (optionLit (a.map (·.2.2))) := by
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
      (optionLit ((kvs.foldl (fun acc kv =>
          if decide (key = kv.1) then some kv else acc) none)
         .map (·.2.2))) := by
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
    ((kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv else acc) a).map proj)
      = ((kvs.map (fun kv => (kv.1, proj kv))).foldl (fun acc kv =>
          if decide (key = kv.1) then some kv.2 else acc)
        (a.map proj)) := by
  induction kvs generalizing a with
  | nil => rfl
  | cons kv kvs ih =>
    simp only [List.foldl_cons, List.map_cons]
    cases decide (key = kv.1) <;> exact ih _

/-- `alookSem` agrees with the row-fold under `(key, valB)`
    projection. -/
theorem alookSem_proj (key : List (Fin 16)) (kvs : List P2Row) :
    ((kvs.foldl (fun acc kv =>
        if decide (key = kv.1) then some kv else acc) none)
      .map (fun kv => kv.2.1))
      = alookSem key (kvs.map (fun kv => (kv.1, kv.2.1))) :=
  alookFold_proj key kvs (fun kv => kv.2.1) none
'''

txt = txt.replace('\nend ISAR', '\n' + block + '\nend ISAR')
io.open('_spec_p2_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('appended', len(block))
