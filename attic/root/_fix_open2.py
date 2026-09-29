"""Insert progBodyStuck def + corrected program_open."""

src = open('_spec_prog_work.lean', encoding='utf-8').read()
defs = open('_prog_defs.txt', encoding='utf-8').read()

# extract progBodyStuck (last def in _prog_defs.txt)
di = defs.index('set_option maxRecDepth 10000 in\n'
                'set_option maxHeartbeats 16000000 in\n'
                '/-- the `hsteps`-evaluated body')
stuck = defs[di:].rstrip() + '\n\n'

# insert after programT def (before progBody_eq's set_option)
i = src.index('def programT : LTerm :=')
j = src.index('set_option maxRecDepth 10000 in\n'
              'set_option maxHeartbeats 16000000 in\n'
              'theorem progBody_eq', i)
src = src[:j] + stuck + src[j:]

# replace program_open
i = src.index('/-- the five outer lambdas of `programT` apply to '
              'the open body. -/')
j = src.index('/-- `programOf` evaluation:', i)
src = src[:i] + '''/-- the five outer lambdas of `programT` apply to the open body. -/
theorem program_open (fsT fuelT rbbT cbT nbT : LTerm)
    (hfs : closed 0 fsT = true) (hfu : closed 0 fuelT = true)
    (hr : closed 0 rbbT = true) (hc : closed 0 cbT = true)
    (hn : closed 0 nbT = true) :
    LRed (aps programT [fsT, fuelT, rbbT, cbT, nbT])
         (progBodyOpen fsT fuelT rbbT cbT nbT) := by
  have h5 : hsteps 5 (aps programT [fsT, fuelT, rbbT, cbT, nbT]) =
      subst nbT 0 (subst cbT 1 (subst rbbT 2 (subst fuelT 3
        (subst fsT 4 progBodyVar)))) := rfl
  have hu : subst nbT 0 (subst cbT 1 (subst rbbT 2 (subst fuelT 3
      (subst fsT 4 progBodyVar)))) =
      progBodyStuck fsT fuelT rbbT cbT nbT := rfl
  have hu2 : progBodyStuck fsT fuelT rbbT cbT nbT =
      progBodyOpen fsT fuelT rbbT cbT nbT := by
    unfold progBodyStuck progBodyOpen
    simp only [shift_of_closed0 hfs, shift_of_closed0 hfu,
      shift_of_closed0 hr, shift_of_closed0 hc, shift_of_closed0 hn,
      subst_of_closed0 hfs, subst_of_closed0 hfu, subst_of_closed0 hr,
      subst_of_closed0 hc, subst_of_closed0 hn]
  exact hu2 ▸ hu ▸ LRed_of_hsteps h5

''' + src[j:]

open('_spec_prog_work.lean', 'w', encoding='utf-8').write(src)
print('patched', len(src))
