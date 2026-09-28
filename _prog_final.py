import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# find and remove the smoke-test examples (everything from the first
# '/-- closed-0 idiom' docstring to 'end ISAR')
i0 = txt.index('/-- closed-0 idiom')
i1 = txt.index('end ISAR')

block = '''/-- discharge `closed d <literal> = true` and
    `closed 0 (subst v 1 <literal>) = true` leaves: literal atoms by
    `decide`/`closed_*_any`, parameter tokens by context (`hr`/`hc`/`hn`/
    `hv`), `.var`-slots by `decide`. -/
private macro "litLeaf" : tactic =>
  `(tactic| (simp only [closed, subst, aps, List.foldl,
      Bool.and_eq_true, shift_of_closed0, subst_of_closed0,
      subst_of_closed, closed_conssL_any, closed_klL_any,
      closed_kilL_any, closed_nilL_any, closed_pairSrcL_any,
      closed_nibLit_any]
    repeat' constructor
    all_goals first | assumption | decide))

/-- the generated segments satisfy `osegClosed` whenever the runtime
    byte terms are closed. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem closed_progSegs (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    ∀ s ∈ progSegs rbbT cbT nbT, osegClosed s := by
  intro s hs
  simp only [progSegs, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false, false_or] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
'''

# 21 bullets: frag gets psegClosed in the simp set; stS/bDS don't.
# routine order: 15 frags, st_s (stS), 4 frags, build_ds (bDS)
kinds = (['frag'] * 15 + ['stS'] + ['frag'] * 4 + ['bDS'])
for k in kinds:
    if k == 'frag':
        block += '''  · simp only [osegClosed, psegClosed, List.forall_mem_cons,
      List.forall_mem_nil, and_true]
    repeat' first | constructor | intro v hv
    all_goals litLeaf
'''
    else:
        block += '''  · simp only [osegClosed, List.forall_mem_cons,
      List.forall_mem_nil, and_true]
    repeat' first | constructor | intro v hv
    all_goals litLeaf
'''

block += '''/-- `optionLit` closedness from element closedness. -/
theorem closed_optionLit (fuel : Option LTerm)
    (hfjcl : ∀ v ∈ fuel, closed 0 v = true) :
    closed 0 (optionLit fuel) = true := by
  cases fuel with
  | none => exact closed_klL
  | some v =>
      show closed 0 (.app justL v) = true
      simp only [closed, Bool.and_eq_true]
      exact ⟨closed_justL, hfjcl v rfl⟩

/-- the five outer lambdas of `programT` apply to the open body. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem program_open (fsT fuelT rbbT cbT nbT : LTerm)
    (hfs : closed 0 fsT = true) (hfu : closed 0 fuelT = true)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    LRed (aps programT [fsT, fuelT, rbbT, cbT, nbT])
         (progBodyOpen fsT fuelT rbbT cbT nbT) := by
  have cfs : ∀ c, closed c fsT = true :=
    fun c => closed_mono hfs (Nat.zero_le c)
  have cfu : ∀ c, closed c fuelT = true :=
    fun c => closed_mono hfu (Nat.zero_le c)
  have cr : ∀ c, closed c rbbT = true :=
    fun c => closed_mono hr (Nat.zero_le c)
  have cc : ∀ c, closed c cbT = true :=
    fun c => closed_mono hc (Nat.zero_le c)
  have cn : ∀ c, closed c nbT = true :=
    fun c => closed_mono hn (Nat.zero_le c)
  exact LRed_of_hsteps (k := 5) (by
    unfold programT progBodyOpen
    simp [aps, List.foldl, hsteps, hstep, subst,
          subst_of_closed, shift_of_closed, cfs, cfu, cr, cc, cn,
          closed_conssL_any, closed_klL_any, closed_kilL_any,
          closed_nilL_any, closed_pairSrcL_any, closed_nibLit_any])

/-- `programOf` evaluation: the generated program applied to a fuse_s
    boolean, a fuel option, and the three runtime byte terms reduces to
    the Scott-list of per-routine fragment lists selected by
    `progSem`. -/
theorem program_eval (fuse : Bool) (fuel : Option LTerm)
    (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true)
    (hfjcl : ∀ v ∈ fuel, closed 0 v = true) :
    LRed (aps programT
        [boolLit fuse, optionLit fuel, rbbT, cbT, nbT])
      (scottList (progSem fuse fuel (progSegs rbbT cbT nbT))) := by
  have hopen := program_open (boolLit fuse) (optionLit fuel)
      rbbT cbT nbT (closed_boolLit fuse)
      (closed_optionLit fuel hfjcl) hr hc hn
  rw [progBody_eq] at hopen
  exact hopen.trans (osegChain_eval (boolLit fuse) (optionLit fuel)
      fuse fuel Relation.ReflTransGen.refl Relation.ReflTransGen.refl
      hfjcl (closed_boolLit fuse) (closed_optionLit fuel hfjcl)
      (progSegs rbbT cbT nbT) nilL nilL
      (closed_progSegs rbbT cbT nbT hr hc hn) closed_nilL
      Relation.ReflTransGen.refl closed_nilL)
'''

txt = txt[:i0] + block + '\n' + txt[i1:]
io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('ok — wrote concrete proof block')
