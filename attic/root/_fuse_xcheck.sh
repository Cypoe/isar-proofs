#!/bin/bash
cp /mnt/c/Users/fabi0/repos/isar-proofs/_aarch64_fuse.elf /tmp/f.elf
cp /mnt/c/Users/fabi0/repos/isar-proofs/_x86_64_fuse.elf /tmp/g.elf
chmod +x /tmp/f.elf /tmp/g.elf
for inp in 'S K K @ I @' 'S B @ S K @ @ I @' 'W I @ W I @ K @ @ @' 'S I I @ K @'; do
  printf "%s" "$inp" | /tmp/f.elf >/tmp/a.out 2>/tmp/a.err; ra=$?
  printf "%s" "$inp" | /tmp/g.elf >/tmp/b.out 2>/tmp/b.err; rb=$?
  cmp -s /tmp/a.out /tmp/b.out && so=MATCH || so=DIFF
  cmp -s /tmp/a.err /tmp/b.err && se=MATCH || se=DIFF
  echo "fuse_s in='$inp' a64[$(cat /tmp/a.out)|$(cat /tmp/a.err)] x64[$(cat /tmp/b.out)|$(cat /tmp/b.err)] out:$so err:$se rc:$ra/$rb"
done
