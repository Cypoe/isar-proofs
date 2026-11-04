"""
flowkernel_drift — the FlowDialect mirror must not drift from its source.

src/ISAR/FlowDialect.lean is a faithful re-typed port of koru's
verify/semantics/FlowKernel.lean. Vendored by hash, not a lake dep:
the port's docstring carries `upstream-sha256:` — the LF-normalized
sha256 of the upstream file at port time. This gate recomputes that
hash over the reachable koru checkout and fails on mismatch.

Exit codes: 0 at pin; 1 drifted; 2 malformed pin; 3 NotRealized —
no koru checkout reachable (axis named, never a silent pass).

Env: KORU_SRC / ISAR_KORU_SRC override the checkout search.
"""
from __future__ import annotations

import hashlib
import os
import re
import sys

_REPO = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))
FLOWDIALECT = os.path.join(_REPO, "src", "ISAR", "FlowDialect.lean")

_KERNEL_REL = os.path.join("verify", "semantics", "FlowKernel.lean")

_CANDIDATES = (
    os.environ.get("KORU_SRC"),
    os.environ.get("ISAR_KORU_SRC"),
    "w:/src/koru",
    "/mnt/w/src/koru",
    "C:/home/cypoe/src/koru-quantity",
    "/home/cypoe/src/koru-quantity",
    os.path.join(_REPO, "..", "koru"),
)


def koru_src_dir() -> str | None:
    """First candidate holding verify/semantics/FlowKernel.lean."""
    for d in _CANDIDATES:
        if d and os.path.exists(os.path.join(d, _KERNEL_REL)):
            return os.path.normpath(d)
    return None


def sha256_lf(path: str) -> str:
    with open(path, "rb") as f:
        return hashlib.sha256(f.read().replace(b"\r\n", b"\n")).hexdigest()


def pinned_hash() -> str | None:
    with open(FLOWDIALECT, encoding="utf-8") as f:
        for line in f:
            m = re.search(r"upstream-sha256:\s*([0-9a-f]{64})", line)
            if m:
                return m.group(1)
    return None


def main() -> int:
    pin = pinned_hash()
    if pin is None:
        print("BROKEN flowkernel-drift: FlowDialect.lean carries no "
              "upstream-sha256 pin")
        return 2

    src = koru_src_dir()
    if src is None:
        print("NOT-REALIZED flowkernel-drift: no koru checkout reachable "
              "(axis: koru-src). Set KORU_SRC or land a checkout at a "
              "candidate path; the pin cannot be verified without the "
              "upstream file and we do not pass on faith.")
        return 3

    actual = sha256_lf(os.path.join(src, _KERNEL_REL))
    if actual == pin:
        print(f"flowkernel-drift: at pin — sha256={actual[:16]}… "
              f"({src})")
        return 0

    print(f"flowkernel-drift DRIFTED: upstream sha256 {actual[:16]}… "
          f"!= FlowDialect pin {pin[:16]}… ({src})")
    print("  Port the delta into FlowDialect.lean, then update the")
    print("  upstream-sha256 line in its docstring in the same commit.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
