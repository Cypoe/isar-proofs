"""Splice the generated defs + proof-term into _spec_prog_work.lean:
- programT := .abs^5 progBodyVar (+ progBodyVar def)
- closed_appD + closed_progSegs := <proof-term> (replaces macros+stub)
- progBodyOpenShift + progBodyShift_eq + new program_open
"""
import re

src = open('_spec_prog_work.lean', encoding='utf-8').read()
defs = open('_prog_defs.txt', encoding='utf-8').read()
proof = open('_prog_proof.txt', encoding='utf-8').read()

# --- 1. replace programT def --------------------------------------
i = src.index('def programT : LTerm :=')
j = src.index('theorem progBody_eq', i)
# defs file contains progBodyVar+programT+progBodyOpenShift; extract
# only progBodyVar+programT here (OpenShift goes later)
dvar = defs.index('def progBodyVar')
dt = defs.index('def programT')
dsh = defs.index('set_option maxRecDepth 10000 in\nset_option '
                'maxHeartbeats 16000000 in\n/-- the open body')
block1 = (defs[:dvar] + defs[dvar:dt + defs[dt:].index('\n\n') + 2])
block1 = block1.rstrip() + '\n\n'
src = src[:i] + block1 + src[j:]

# --- 2. replace macros + closed_progSegs (772..pre-optionLit) -----
i2 = src.index('/-- discharge `closed d <literal> = true` leaves')
i3 = src.index('/-- `optionLit` closedness from element closedness.')
dsh_end = defs.index('(fsT fuelT rbbT cbT nbT : LTerm) : LTerm :=\n')
dsh_line_end = defs.index('\n', dsh_end + 20)
openshift = defs[dsh:dsh_line_end + 1]

new_mid = '''/-- `closed` under an application node (depth-parameterized). -/
theorem closed_appD {f x : LTerm} (d : Nat)
    (hf : closed d f = true) (hx : closed d x = true) :
    closed d (.app f x) = true := by
  simp only [closed, Bool.and_eq_true]; exact ⟨hf, hx⟩

''' + openshift + '''
/-- `progBodyOpenShift`'s `shift c 0 <param>` insertions collapse to
    the parameters when the parameters are closed-0. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem progBodyShift_eq (fsT fuelT rbbT cbT nbT : LTerm)
    (hfs : closed 0 fsT = true) (hfu : closed 0 fuelT = true)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    progBodyOpenShift fsT fuelT rbbT cbT nbT =
      progBodyOpen fsT fuelT rbbT cbT nbT := by
  unfold progBodyOpenShift progBodyOpen
  rw [shift_of_closed0 hfs, shift_of_closed0 hfu,
      shift_of_closed0 hr, shift_of_closed0 hc, shift_of_closed0 hn]

/-- the generated segments satisfy `osegClosed` whenever the runtime
    byte terms are closed — a generated proof term: membership chains
    (`List.forall_mem_cons`), per-`.app` `closed_appD`, depth-`decide`
    `.var` leaves, `closed_mono` for runtime tokens, and
    `shift_of_closed0` for the fuelR `subst` clause. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem closed_progSegs (rbbT cbT nbT : LTerm)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    ∀ s ∈ progSegs rbbT cbT nbT, osegClosed s :=
  ''' + proof + '''

'''
src = src[:i2] + new_mid + src[i3:]

# --- 3. replace program_open --------------------------------------
i4 = src.index('/-- the five outer lambdas of `programT` apply to '
               'the open body. -/')
i5 = src.index('/-- `programOf` evaluation:', i4)
new_open = '''/-- the five outer lambdas of `programT` apply to the open body. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem program_open (fsT fuelT rbbT cbT nbT : LTerm)
    (hfs : closed 0 fsT = true) (hfu : closed 0 fuelT = true)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    LRed (aps programT [fsT, fuelT, rbbT, cbT, nbT])
         (progBodyOpen fsT fuelT rbbT cbT nbT) :=
  have h5 : hsteps 5 (aps programT [fsT, fuelT, rbbT, cbT, nbT]) =
      subst nbT 0 (subst cbT 1 (subst rbbT 2 (subst fuelT 3
        (subst fsT 4 progBodyVar)))) := rfl
  have hu : subst nbT 0 (subst cbT 1 (subst rbbT 2 (subst fuelT 3
      (subst fsT 4 progBodyVar)))) =
      progBodyOpenShift fsT fuelT rbbT cbT nbT := rfl
  progBodyShift_eq fsT fuelT rbbT cbT nbT hfs hfu hr hc hn ▸
    (hu ▸ LRed_of_hsteps h5)

'''
src = src[:i4] + new_open + src[i5:]

open('_spec_prog_work.lean', 'w', encoding='utf-8').write(src)
print('spliced; new size', len(src))
