"""Stop hook — the frag flywheel.

When the turn ends with dirty engine files (host/, seed/) but no
new/modified docs/frags/ entry in the same dirty set, inject a
reminder.  Non-blocking by design (exit 0 + context): a question
or a typo fix is not a feature, and a hard block would trap
legitimate stops.  The requirement itself is normative
(AGENTS.md) — this hook makes it visible at the decision point.
"""
import json
import subprocess
import sys

ENGINE = ("host/", "seed/")
FRAGS = "docs/frags/"


def main() -> int:
    try:
        p = subprocess.run(
            ["git", "status", "--porcelain", "-uall"],
            capture_output=True, text=True, timeout=10)
    except (OSError, subprocess.SubprocessError):
        return 0
    if p.returncode != 0:
        return 0
    dirty = [ln[3:] for ln in p.stdout.splitlines() if ln.strip()]
    engine_hit = any(d.startswith(ENGINE) for d in dirty)
    frag_hit = any(d.startswith(FRAGS) for d in dirty)
    if engine_hit and not frag_hit:
        sys.stdout.write(json.dumps({
            "hookSpecificOutput": {
                "hookEventName": "Stop",
                "additionalContext": (
                    "frag reminder: engine files changed "
                    f"({', '.join(d for d in dirty if d.startswith(ENGINE))[:200]}) "
                    "without a docs/frags/ entry — if this turn "
                    "landed a feature or decision, write the frag "
                    "before wrapping up (AGENTS.md, writeup "
                    "discipline).")
            }
        }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
