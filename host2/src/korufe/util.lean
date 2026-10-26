/-! # korufe/util.c — allocation + growable buffer, pinned

Smallest leg on purpose: `xmalloc` (die loudly on OOM — a witness
may refuse but never corrupt), `xstrndup/xstrdup/xasprintf`, and
`Buf`/`bput`/`bputf` — the byte sink for both writers (astio's
canon JSON, lower's `[flow-eval]` s-expr).  No semantics here;
the contract is "append or die". -/
