import io

txt = io.open('_spec_prog_work.lean', encoding='utf-8').read()

# 1. all `(by simp only [closed]; omega)` -> `(by simp)` for symbolic decide goals
txt = txt.replace('(by simp only [closed]; omega)', '(by simp)')

# 2. `by decide` in closed_psegApp fuelR for the id-frag closedness
txt = txt.replace('refine ⟨⟨⟨hfu, by decide⟩, ?_⟩, htcl⟩',
                  'refine ⟨⟨⟨hfu, by simp⟩, ?_⟩, htcl⟩')

# 3. closed_progSem frag case `show ... at` bug
old = '''  cases s with
  | frag segs' =>
    show c ∈ [scottList (psegSem fuse fuel segs')] at hci
    simp only [List.mem_singleton] at hci
    rw [hci]
    exact closed_scottList (closed_psegSem segs' fuse fuel hsc hfv)
  | stS items =>
    cases fuse
    · show c ∈ (osegCells false fuel (.stS items)) at hci
      nomatch hci
    · show c ∈ [scottList items] at hci
      simp only [List.mem_singleton] at hci
      rw [hci]; exact closed_scottList hsc
  | bDS items =>
    cases fuse
    · show c ∈ [scottList items] at hci
      simp only [List.mem_singleton] at hci
      rw [hci]; exact closed_scottList hsc
    · show c ∈ (osegCells true fuel (.bDS items)) at hci
      nomatch hci'''
new = '''  cases s with
  | frag segs' =>
    have hci' : c ∈ [scottList (psegSem fuse fuel segs')] := hci
    simp only [List.mem_singleton] at hci'
    rw [hci']
    exact closed_scottList (closed_psegSem segs' fuse fuel hsc hfv)
  | stS items =>
    cases fuse
    · nomatch hci
    · have hci' : c ∈ [scottList items] := hci
      simp only [List.mem_singleton] at hci'
      rw [hci']; exact closed_scottList hsc
  | bDS items =>
    cases fuse
    · have hci' : c ∈ [scottList items] := hci
      simp only [List.mem_singleton] at hci'
      rw [hci']; exact closed_scottList hsc
    · nomatch hci'''
assert old in txt, "progSem"
txt = txt.replace(old, new)

io.open('_spec_prog_work.lean', 'w', encoding='utf-8', newline='\n').write(txt)
print('patched')
