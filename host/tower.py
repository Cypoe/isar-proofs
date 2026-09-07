"""
Pure stratification (host showcase of the composition tower).

Layer 0 — five ops (substrate presentation for this rewrite dispatch):
  norm, app, comp, dup, swap
  (Lean matrices: I, mul, and the B/W/C agents; app↔mul is Phase-4 dispatch.)

Layer 1 — derived ops (macros over L0):
  s  = derived_s  (Lean `derived_s_beta` — theorem under BCWI; correct shape)
  k  = macro K    (L1 fused β — Lean `IStep.konst_macro` / `IStepKMacro`.
                   BCWI ⊬ K forever; never derive. BCWIK was construction
                   scaffolding to prove ISAR, not definability of K.
                   `derived_k_signature` = IRAS word for the macro tag only.)

Observational NFs must keep matching. Lean exposes K as L1 `konst_macro`
(`IStepKMacro`), not as an `IStepCore` peer — same host stratification.

Layer 2 — surface / dialects (QuotientMap only):
  encode/decode onto L0+L1; observe via Graph / OperEq. No private dialect β.

Lean: `IStep.konst_macro` / `IStepKMacro` (L1); `IStepBasis = IStepCore ∪ macro`.
"""
from __future__ import annotations

from reduce import K, T, I, KK, B, S, D, C, app


# ----- Layer 0 constructors (sugar names) -----
def op_norm() -> T:
    return I


def op_comp() -> T:
    return B


def op_dup() -> T:
    return D


def op_swap() -> T:
    return C


def op_app(f: T, x: T) -> T:
    return app(f, x)


# ----- Layer 1: derived S (operational expansion) -----
def derived_s() -> T:
    """Lean `derived_s`: (B (B D)) ((C ((B B) ((B B) C))) I) — only L0 agents."""
    return app(
        app(B, app(B, D)),
        app(app(C, app(app(B, B), app(app(B, B), C))), I),
    )


_DERIVED_S = derived_s()


def derived_k_signature() -> T:
    """
    Carrier-word for K: (((I · C) · D) · S) ↔ I₁·R₁·A₁·S₁.
    Signature macro (BasisCompleteness); not an ITerm-β definition of konstβ.
    Uses derived_s so the word stays in L0+L1 without an S atom.
    """
    return app(app(app(I, C), D), _DERIVED_S)


_DERIVED_K_SIG = derived_k_signature()


def translate_to_basis(t: T) -> T:
    """
    L2 → L0+L1: expand S; keep K as macro tag (K.KONST) for fused β.
    """
    if t.k == K.S:
        return _DERIVED_S
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return app(translate_to_basis(t.l), translate_to_basis(t.r))
    return t


def quote_surface(t: T) -> T:
    """L0+L1 → L2 display: derived_s → S; K macro tag unchanged."""
    if t == _DERIVED_S:
        return S
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return app(quote_surface(t.l), quote_surface(t.r))
    return t


# backwards-compatible names
quote_s = quote_surface


def layer_summary() -> str:
    return (
        "L0 ops:  norm, app, comp, dup, swap\n"
        "L1 der:  s = derived_s (expand); k = macro (fused beta; sig IRAS)\n"
        "L2 sfc:  QuotientMap encode/decode; observe via Graph/OperEq\n"
        "Params:  host pieces + strategy (compiler uses / CoGen emits later)\n"
        "Dispatch (later): budgeted loaders CPU/SIMD/GPU - not dialect-owned"
    )


def main() -> int:
    print(layer_summary())
    print(f"derived_s:  {_DERIVED_S}")
    print(f"derived_k_signature (IRAS word):  {_DERIVED_K_SIG}")
    t = app(app(app(S, KK), KK), I)
    u = translate_to_basis(t)
    assert quote_surface(_DERIVED_S) == S
    assert u.k == K.APP
    print("OK translate S; quote S")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
