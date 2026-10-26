/-! # korufe/main.c — the two frontend legs, pinned

    korufe FILE.k                                  -> program.ast.json
    korufe --lower FILE.ast.json CASES.json KEY    -> [flow-eval] claim

Leg 1 composes lex -> parse -> astio write.  Leg 2 composes JSON
read -> case-row lookup -> lower.  `file_read` + `base_name`
(module name from the .k stem) are the only glue.  Exit codes:
0 ok, 2 refuse — the gate reads stderr's `refuse:` prefix, not a
structured channel; refusal text names the axis. -/
