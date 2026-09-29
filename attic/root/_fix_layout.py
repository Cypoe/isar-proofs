"""Fix layout: remove dead progBodyOpenShift/progBodyShift_eq block,
reorder docstring vs set_option, new program_open (hu via simp only)."""

src = open('_spec_prog_work.lean', encoding='utf-8').read()

# 1. remove progBodyOpenShift def + progBodyShift_eq (dead — hu now
#    targets progBodyOpen directly via simp only)
i = src.index('set_option maxRecDepth 10000 in\n'
              'set_option maxHeartbeats 16000000 in\n'
              '/-- the open body with `subst`')
j = src.index('/-- the generated segments satisfy `osegClosed`', i)
src = src[:i] + src[j:]

# 2. closed_progSegs: docstring then set_option -> set_option then doc
i = src.index('/-- the generated segments satisfy `osegClosed`')
j = src.index('theorem closed_progSegs', i)
seg = src[i:j]
seg = seg.replace(
    'set_option maxRecDepth 10000 in\n'
    'set_option maxHeartbeats 16000000 in\n', '')
src = (src[:i] + 'set_option maxRecDepth 10000 in\n'
       'set_option maxHeartbeats 16000000 in\n' + seg + src[j:])

# 3. program_open: dedupe/reorder + new body
i = src.index('set_option maxRecDepth 10000 in\n'
              'set_option maxHeartbeats 16000000 in\n'
              '/-- the five outer lambdas of `programT`')
j = src.index('/-- `programOf` evaluation:', i)
src = src[:i] + '''set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
/-- the five outer lambdas of `programT` apply to the open body. -/
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
      progBodyOpen fsT fuelT rbbT cbT nbT := by
    unfold progBodyOpen
    simp only [subst, aps, List.foldl, shift_of_closed0 hfs,
      shift_of_closed0 hfu, shift_of_closed0 hr, shift_of_closed0 hc,
      shift_of_closed0 hn, subst_of_closed0 hfs, subst_of_closed0 hfu,
      subst_of_closed0 hr, subst_of_closed0 hc, subst_of_closed0 hn]
  exact hu ▸ LRed_of_hsteps h5

''' + src[j:]

open('_spec_prog_work.lean', 'w', encoding='utf-8').write(src)
print('layout fixed', len(src))
