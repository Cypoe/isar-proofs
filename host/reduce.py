"""
Host-side ISAR reducer — matches Lean IStep exactly (I/K/B/S + appL/appR).
No dupβ, no swapβ.  Used by congruence golden suite.
"""
from __future__ import annotations
from dataclasses import dataclass
from enum import Enum, auto
from typing import Optional, Tuple


class K(Enum):
    VAR = auto()
    NORM = auto()    # I
    KONST = auto()   # K
    DUP = auto()     # D  (syntax only — no β rule in IStep)
    SWAP = auto()    # C  (syntax only — no β rule in IStep)
    COMP = auto()    # B
    S = auto()       # S
    APP = auto()


@dataclass(frozen=True)
class T:
    k: K
    n: int = 0
    l: Optional["T"] = None
    r: Optional["T"] = None

    def __repr__(self) -> str:
        m = {K.VAR: f"v{self.n}", K.NORM: "I", K.KONST: "K",
             K.DUP: "D", K.SWAP: "C", K.COMP: "B", K.S: "S"}
        if self.k == K.APP:
            return f"({self.l} {self.r})"
        return m.get(self.k, "?")


# Constructors
I = T(K.NORM)
KK = T(K.KONST)
B = T(K.COMP)
S = T(K.S)
D = T(K.DUP)
C = T(K.SWAP)

def app(f: T, x: T) -> T:
    return T(K.APP, l=f, r=x)


def step(t: T) -> Optional[T]:
    """LO single step matching Lean IStep (normβ, konstβ, compβ, sβ, appL, appR)."""
    if t.k != K.APP:
        return None
    f, x = t.l, t.r
    assert f is not None and x is not None

    # normβ: I x → x
    if f.k == K.NORM:
        return x

    if f.k == K.APP:
        fl, fr = f.l, f.r
        assert fl is not None and fr is not None
        # konstβ: K a b → a
        if fl.k == K.KONST:
            return fr

        if fl.k == K.APP:
            fll, flr = fl.l, fl.r
            assert fll is not None and flr is not None
            # compβ: B f g x → f (g x)
            if fll.k == K.COMP:
                return app(flr, app(fr, x))
            # sβ: S f g x → (f x)(g x)
            if fll.k == K.S:
                return app(app(flr, x), app(fr, x))

    # appL
    sf = step(f)
    if sf is not None:
        return app(sf, x)
    # appR
    sx = step(x)
    if sx is not None:
        return app(f, sx)
    return None


def reduce(t: T, fuel: int = 1000) -> Tuple[T, int]:
    """Iterate LO step until NF or fuel exhaustion."""
    cur, n = t, 0
    while n < fuel:
        nxt = step(cur)
        if nxt is None:
            break
        cur = nxt
        n += 1
    return cur, n


def cd(t: T) -> T:
    """Complete development — matches Lean `ISAR.cd` / ParStep (I/K/B/S only)."""
    if t.k != K.APP:
        return t
    f, x = t.l, t.r
    assert f is not None and x is not None
    # I x => cd x
    if f.k == K.NORM:
        return cd(x)
    if f.k == K.APP:
        fl, fr = f.l, f.r
        assert fl is not None and fr is not None
        # K a b => cd a
        if fl.k == K.KONST:
            return cd(fr)
        if fl.k == K.APP:
            fll, flr = fl.l, fl.r
            assert fll is not None and flr is not None
            # B f g x => (cd f) ((cd g) (cd x))
            if fll.k == K.COMP:
                return app(cd(flr), app(cd(fr), cd(x)))
            # S f g x => ((cd f)(cd x)) ((cd g)(cd x))
            if fll.k == K.S:
                return app(app(cd(flr), cd(x)), app(cd(fr), cd(x)))
    return app(cd(f), cd(x))


def reduce_cd(t: T, fuel: int = 1000) -> Tuple[T, int]:
    """Iterate cd until fixpoint. Round count << LO steps on I-spines."""
    cur, n = t, 0
    while n < fuel:
        nxt = cd(cur)
        if nxt == cur:
            break
        cur = nxt
        n += 1
    return cur, n


# --------------- goldens (must match Main.lean / Eval.lean) ---------------

GOLDENS = [
    ("I K -> K",                           app(I, KK),                                          KK),
    ("K S I -> S",                         app(app(KK, S), I),                                  S),
    ("S K K I -> I",                        app(app(app(S, KK), KK), I),                         I),
    ("B f g x = f(gx): B K I S -> K S",   app(app(app(app(app(S, app(KK, S)), KK), KK), I), S),
                                           app(KK, S)),
]


def main() -> int:
    ok = True
    for label, term, expected in GOLDENS:
        nf, steps = reduce(term)
        match = nf == expected
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  =>  {nf}  ({steps} steps)")
        if not match:
            print(f"  EXPECTED: {expected}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
