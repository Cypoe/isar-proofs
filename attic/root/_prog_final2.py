import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

i0 = txt.index('/-- discharge `closed d')
i1 = txt.index('end ISAR')

block = '''/-- discharge `closed d <literal> = true` leaves: literal atoms by
    `closed_*_any`/`decide`, parameter tokens by context
    (`hr`/`hc`/`hn`/`hv`), `.var`-slots by `decide`. -/
macro "litClosed" : tactic =>
  `(tactic| simp only [closed, aps, List.foldl,
      Bool.and_eq_true, closed_conssL_any, closed_klL_any,
      closed_kilL_any, closed_nilL_any, closed_pairSrcL_any,
      closed_nibLit_any] <;>
    repeat' constructor <;>
    first | assumption | decide)

/-- discharge `closed 0 (subst v 1 <literal>) = true` leaves (the
    fuelR subst clause): `.var 1` -> `shift 1 0 v` -> `v` via
    `shift_of_closed0 hv`; parameter/atom subtrees via
    `subst_of_closed0`/`subst_of_closed`. -/
macro "litSubst" : tactic =>
  `(tactic| simp only [subst, shift_of_closed0 hv,
      subst_of_closed0 hr, subst_of_closed0 hc, subst_of_closed0 hn,
      subst_of_closed (closed_conssL_any _),
      subst_of_closed (closed_klL_any _),
      subst_of_closed (closed_kilL_any _),
      subst_of_closed (closed_nilL_any _),
      subst_of_closed (closed_pairSrcL_any _),
      subst_of_closed (closed_nibLit_any _ _),
      closed, aps, List.foldl, Bool.and_eq_true,
      closed_conssL_any, closed_klL_any, closed_kilL_any,
      closed_nilL_any, closed_pairSrcL_any, closed_nibLit_any] <;>
    repeat' constructor <;>
    first | assumption | decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
/-- the generated segments satisfy `osegClosed` whenever the runtime
    byte terms are closed. -/
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

kinds = (['frag'] * 15 + ['stS'] + ['frag'] * 4 + ['bDS'])
for k in kinds:
    if k == 'frag':
        block += '''  · simp only [osegClosed, psegClosed, List.forall_mem_cons,
      List.forall_mem_nil, and_true]
    repeat' constructor
    all_goals first
      | litClosed
      | (intro v hv; litSubst)
'''
    else:
        block += '''  · simp only [osegClosed, List.forall_mem_cons,
      List.forall_mem_nil, and_true]
    repeat' constructor
    all_goals first
      | litClosed
      | (intro v hv; litSubst)
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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
/-- the five outer lambdas of `programT` apply to the open body. -/
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
print('ok')
