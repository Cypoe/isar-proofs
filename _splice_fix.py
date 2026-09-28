"""Repair the splice: set_option for progBody_eq, full progBodyOpenShift
body, forall_mem_nil with explicit motive arg."""
import re

src = open('_spec_prog_work.lean', encoding='utf-8').read()
defs = open('_prog_defs.txt', encoding='utf-8').read()

# 1. progBody_eq needs maxRecDepth (giant rfl)
src = src.replace(
    'theorem progBody_eq (fsT fuelT rbbT cbT nbT : LTerm) :',
    'set_option maxRecDepth 10000 in\n'
    'set_option maxHeartbeats 16000000 in\n'
    'theorem progBody_eq (fsT fuelT rbbT cbT nbT : LTerm) :', 1)

# 2. fill progBodyOpenShift's body
di = defs.index('def progBodyOpenShift')
openshift_full = defs[di:]
i = src.index('def progBodyOpenShift\n'
              '    (fsT fuelT rbbT cbT nbT : LTerm) : LTerm :=\n')
j = i + len('def progBodyOpenShift\n'
            '    (fsT fuelT rbbT cbT nbT : LTerm) : LTerm :=\n')
src = src[:i] + openshift_full + '\n' + src[j:]

# 3. forall_mem_nil takes p explicitly
src = src.replace('List.forall_mem_nil⟩', 'List.forall_mem_nil _⟩')
src = src.replace('List.forall_mem_nil\r', 'List.forall_mem_nil _\r')
src = src.replace('List.forall_mem_nil\n', 'List.forall_mem_nil _\n')
# guard: bare `List.forall_mem_nil` with no arg at end of proof term
src = re.sub(r'List\.forall_mem_nil(?![_ (])', 'List.forall_mem_nil _',
             src)
src = src.replace('List.forall_mem_nil _ _', 'List.forall_mem_nil _')

open('_spec_prog_work.lean', 'w', encoding='utf-8').write(src)
print('repaired', len(src))
