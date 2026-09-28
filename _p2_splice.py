import io

scratch = io.open('_spec_p2_work.lean', encoding='utf-8').read()
mod = io.open('src/ISAR/SpecVocabulary.lean', encoding='utf-8').read()

# scratch body: from the banner comment to before `end ISAR`
sidx = scratch.index('-- ============================================================')
eidx = scratch.rindex('end ISAR')
body = scratch[sidx:eidx].rstrip() + '\n'

# splice before the axiom-audit banner in the module
marker = '-- ---------- axiom audit ---'
aidx = mod.index(marker)
mod = mod[:aidx] + body + '\n' + mod[aidx:]

# merge audits before `end ISAR`
audits = '''
#print axioms p2Resv_eval
#print axioms p2_step_eval
#print axioms p2Fold_eval
#print axioms p1ProgSem_wf
#print axioms p2FoldSem_wf
#print axioms asm_eval
'''
mod = mod.replace('#print axioms p1_eval\n', '#print axioms p1_eval\n' + audits)

io.open('src/ISAR/SpecVocabulary.lean', 'w', encoding='utf-8', newline='\n').write(mod)
print('spliced, %d chars added' % len(body))
