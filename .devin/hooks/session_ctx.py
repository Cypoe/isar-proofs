"""SessionStart hook — inject the repo contract pointer.

Prints hookSpecificOutput.additionalContext so the session opens
with the frag + verification discipline in view.  The norm itself
lives in AGENTS.md; the hook only points."""
import json
import sys

sys.stdout.write(json.dumps({
    "hookSpecificOutput": {
        "hookEventName": "SessionStart",
        "additionalContext": (
            "isar-proofs contract (AGENTS.md): refuse by default "
            "and name the axis; composition is declared data; "
            "docs/{GATES,CATALOG,MATRIX}.md are generated — run "
            "host/spec_project.py --write, never hand-edit; every "
            "landed feature gets a docs/frags/ frag; verify with "
            "host/battery.py --tier fast and "
            "host/gates/gates_nanopass.py before committing.")
    }
}))
