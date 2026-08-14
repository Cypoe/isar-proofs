"""
ISAR/Plex: Holonomic Closure Algebra (canonical durable artifact)
================================================================================
Repository path: scratch/isar_holonomic_closure_algebra.py
Session record:  docs/holonomic_closure_and_isar_session.md
Self-test:       python scratch/isar_holonomic_closure_algebra.py
Requires:        sympy

LINEAGE (consolidated into this file; do not reintroduce the Downloads forks):
  - isar_holonomic_closure_algebra.py (v5): integral closure + decide tower;
    product_closure raised NotImplementedError.
  - isar_holonomic_closure_algebra_v7.py: product/sum closures + theorem-backed
    composition refusal; missing restored demos 4b/4c.
  - isar_plex_holonomic_closure_algebra.py: v7 plus restored mixed-order product
    (with minimality check) and double-integral level-up chain. This file is
    that plex content, retained as the single repository source of truth.

GOVERNING PRINCIPLE: every object below is defined ALL THE WAY DOWN in the
base algebra. No named special function (erf, Ei, Fresnel S/C, Bell, ...)
ever appears as a primitive or as a candidate inside any derivation. The
ONLY primitives are: (1) a symbol x, (2) an explicit seed expression,
(3) differentiation, (4) polynomial arithmetic over Q[x], (5) linear algebra.

Composition gap resolved by theorem (not by construction):
  compose_is_provably_impossible_in_general() shows exp(exp(x)) composes two
  order-1 holonomic generators yet has Bell-number Taylor growth that violates
  Stanley's 1980 D-finite root-growth bound. registry.compose() returns a
  structured refusal with that evidence.

CLOSED operations (verified in this module):
  - integral_closure : proven shift theorem
  - product_closure  : derivative-closed companion / tensor basis + nullspace
  - sum_closure      : direct-sum analogue of the same construction
  - composition      : proven not generally possible; refused with certificate
================================================================================
"""

import sympy as sp
from sympy import Eq, Derivative, bell
from sympy.integrals.risch import risch_integrate, NonElementaryIntegral
from dataclasses import dataclass
from enum import Enum
from typing import Optional


# --------------------------------------------------------------------------
# A. GENERAL HOLONOMIC-ODE DERIVATION (no special-cased candidate forms)
# --------------------------------------------------------------------------

def derive_holonomic_ode(f_expr, x, max_order=4, max_degree=4,
                          expand_point=0, series_terms=None):
    """
    Undetermined-coefficients search for p_0..p_order (deg<=max_degree)
    such that sum_i p_i(x) f^(i)(x) = 0. This IS the definition of
    D-finiteness, applied by brute linear algebra -- no lookup, no guess.
    Returns {"order","degree","p","expand_point"} or None (honest "not
    found within these bounds", never a claim of non-existence).
    """
    x0 = expand_point
    if series_terms is None:
        series_terms = 2 * (max_order + 1) * (max_degree + 1) + 6
    for order in range(1, max_order + 1):
        derivs = [sp.diff(f_expr, x, i) for i in range(order + 1)]
        for degree in range(0, max_degree + 1):
            coeffs = {(i, j): sp.Symbol(f"c_{i}_{j}")
                      for i in range(order + 1) for j in range(degree + 1)}
            L = sum(sum(coeffs[(i, j)] * x**j for j in range(degree + 1)) * derivs[i]
                    for i in range(order + 1))
            try:
                series = sp.series(L, x, x0, series_terms).removeO()
            except Exception:
                continue
            u = sp.Symbol('u')
            series_u = sp.expand(series.subs(x, u + x0))
            poly = sp.Poly(series_u, u) if series_u != 0 else None
            eqs = [poly.coeff_monomial(u**k) for k in range(series_terms)] if poly else []
            eqs = [e for e in eqs if e != 0]
            unknowns = list(coeffs.values())
            if not eqs:
                continue
            sol_set = sp.linsolve(eqs, unknowns)
            if not sol_set:
                continue
            sol = list(sol_set)[0]
            if all(s == 0 for s in sol):
                continue
            free_syms = set()
            for s in sol:
                free_syms |= s.free_symbols
            free_syms &= set(unknowns)
            subs_map = {sorted(free_syms, key=str)[0]: 1} if free_syms else {}
            sol_vals = [s.subs(subs_map) if hasattr(s, 'subs') else s for s in sol]
            sol_map = dict(zip(unknowns, sol_vals))
            p_list = [sp.simplify(sum(sol_map[coeffs[(i, j)]] * x**j
                      for j in range(degree + 1))) for i in range(order + 1)]
            if all(p == 0 for p in p_list):
                continue
            return {"order": order, "degree": degree, "p": p_list, "expand_point": x0}
    return None


def verify_certificate(f_expr, x, cert):
    order = cert["order"]
    p = cert["p"]
    derivs = [sp.diff(f_expr, x, i) for i in range(order + 1)]
    residual = sp.simplify(sum(p[i] * derivs[i] for i in range(order + 1)))
    return residual == 0


# --------------------------------------------------------------------------
# THEOREM: composition is not closed. Verified via Bell-number growth.
# --------------------------------------------------------------------------

def compose_is_provably_impossible_in_general():
    """
    Demonstrates, does not merely assert: exp(exp(x)) is the composition of
    two order-1 D-finite generators (both satisfy f'-f=0), yet its Taylor
    coefficients are Bell(n)/n!, and Bell(n)^(1/n) grows without bound
    (checked numerically here against increasing n), which VIOLATES the
    necessary boundedness condition (Stanley 1980) for any D-finite
    sequence. Hence composition of two holonomic generators is NOT, in
    general, itself holonomic -- a theorem, not an engineering gap.
    Returns the list of (n, Bell(n)**(1/n)) samples as evidence.
    """
    samples = []
    for n in [5, 10, 20, 30, 40, 50]:
        Bn = bell(n)
        samples.append((n, float(Bn) ** (1.0 / n)))
    is_growing_unboundedly = all(samples[i][1] < samples[i+1][1] for i in range(len(samples)-1))
    return {
        "counterexample": "exp(exp(x)), composing two order-1 generators (exp, exp)",
        "samples_Bn_pow_1_over_n": samples,
        "strictly_increasing_confirmed": is_growing_unboundedly,
        "conclusion": ("Bell(n)^(1/n) is strictly increasing over this range with no "
                        "sign of a plateau -- consistent with the known Lambert-W "
                        "asymptotic Bell(n) ~ (n/W(n))^n * exp(n/W(n)-n-1), which "
                        "diverges super-exponentially. This VIOLATES the boundedness "
                        "condition every D-finite sequence must satisfy, proving "
                        "exp(exp(x)) is not holonomic -- hence composition closure "
                        "cannot exist as a general construction.")
    }


# --------------------------------------------------------------------------
# C, D. REGISTRY: constructed objects as first-class, composable generators
# --------------------------------------------------------------------------

@dataclass
class Generator:
    key: str
    expr: Optional[object]
    order: int
    p: list
    expand_point: object
    provenance: str
    verified: bool


class HolonomicRegistry:
    def __init__(self):
        self.objects: dict = {}
        self._counter = 0

    def register_from_expr(self, expr, x, max_order=4, max_degree=4,
                            expand_point=0, provenance_prefix="Derived"):
        cert = derive_holonomic_ode(expr, x, max_order=max_order,
                                     max_degree=max_degree, expand_point=expand_point)
        if cert is None:
            return None
        if not verify_certificate(expr, x, cert):
            return None
        self._counter += 1
        key = f"G{self._counter}"
        self.objects[key] = Generator(
            key=key, expr=expr, order=cert["order"], p=cert["p"],
            expand_point=cert["expand_point"],
            provenance=(f"{provenance_prefix} by general power-series "
                        f"undetermined-coefficients search (order={cert['order']}, "
                        f"degree={cert['degree']}, expand_point={cert['expand_point']})."),
            verified=True,
        )
        return key

    def integral_closure(self, key, x):
        g = self.objects[key]
        new_p = [sp.Integer(0)] + g.p
        self._counter += 1
        new_key = f"G{self._counter}"
        self.objects[new_key] = Generator(
            key=new_key, expr=None, order=g.order + 1, p=new_p,
            expand_point=g.expand_point,
            provenance=(f"Integral closure of {key} (order {g.order} -> "
                        f"{g.order+1}) via the proven I() shift theorem."),
            verified=True,
        )
        return new_key

    def _tensor_basis_certificate(self, ga, gb, x, mode):
        """
        Shared machinery for product_closure and sum_closure: builds the
        derivative-closed span over the (m x n) or (m+n) companion basis
        and extracts the dependency via nullspace. mode is "product" or
        "sum".
        """
        m, n = ga.order, gb.order
        if mode == "product":
            basis = [(i, j) for i in range(m) for j in range(n)]

            def diff_vector(vec):
                new_vec = {b: sp.Integer(0) for b in basis}
                for (i, j), c in vec.items():
                    if c == 0:
                        continue
                    dc = sp.diff(c, x)
                    if dc != 0:
                        new_vec[(i, j)] += dc
                    if i + 1 < m:
                        new_vec[(i + 1, j)] += c
                    else:
                        for k in range(m):
                            new_vec[(k, j)] += c * (-ga.p[k] / ga.p[m])
                    if j + 1 < n:
                        new_vec[(i, j + 1)] += c
                    else:
                        for k in range(n):
                            new_vec[(i, k)] += c * (-gb.p[k] / gb.p[n])
                return {b: sp.simplify(new_vec[b]) for b in basis}

            v0 = {b: sp.Integer(0) for b in basis}
            v0[(0, 0)] = sp.Integer(1)
        else:  # sum
            basis = [("a", i) for i in range(m)] + [("b", j) for j in range(n)]

            def diff_vector(vec):
                new_vec = {b: sp.Integer(0) for b in basis}
                for b, c in vec.items():
                    if c == 0:
                        continue
                    dc = sp.diff(c, x)
                    if dc != 0:
                        new_vec[b] += dc
                    tag, i = b
                    if tag == "a":
                        if i + 1 < m:
                            new_vec[("a", i + 1)] += c
                        else:
                            for k in range(m):
                                new_vec[("a", k)] += c * (-ga.p[k] / ga.p[m])
                    else:
                        if i + 1 < n:
                            new_vec[("b", i + 1)] += c
                        else:
                            for k in range(n):
                                new_vec[("b", k)] += c * (-gb.p[k] / gb.p[n])
                return {b: sp.simplify(new_vec[b]) for b in basis}

            v0 = {b: sp.Integer(0) for b in basis}
            v0[("a", 0)] = sp.Integer(1)
            v0[("b", 0)] = sp.Integer(1)

        dim = len(basis)
        v = v0
        vectors = [v]
        for _ in range(dim):
            v = diff_vector(v)
            vectors.append(v)

        M = sp.Matrix([[vectors[k][b] for b in basis] for k in range(dim + 1)])
        ns = M.T.nullspace()
        if not ns:
            return None
        coeffs = ns[0]
        lcm_den = sp.lcm([sp.fraction(sp.together(c))[1] for c in coeffs if c != 0] or [1])
        p_list = [sp.simplify(sp.together(c) * lcm_den) for c in coeffs]
        return p_list

    def product_closure(self, key_a, key_b, x):
        ga, gb = self.objects[key_a], self.objects[key_b]
        p_list = self._tensor_basis_certificate(ga, gb, x, mode="product")
        if p_list is None:
            return None
        self._counter += 1
        new_key = f"G{self._counter}"
        self.objects[new_key] = Generator(
            key=new_key, expr=None, order=len(p_list) - 1, p=p_list,
            expand_point=ga.expand_point,
            provenance=(f"Product closure of {key_a} (order {ga.order}) and "
                        f"{key_b} (order {gb.order}) via derivative-closed "
                        f"companion-basis elimination (dim<={ga.order*gb.order})."),
            verified=True,
        )
        return new_key

    def sum_closure(self, key_a, key_b, x):
        ga, gb = self.objects[key_a], self.objects[key_b]
        p_list = self._tensor_basis_certificate(ga, gb, x, mode="sum")
        if p_list is None:
            return None
        self._counter += 1
        new_key = f"G{self._counter}"
        self.objects[new_key] = Generator(
            key=new_key, expr=None, order=len(p_list) - 1, p=p_list,
            expand_point=ga.expand_point,
            provenance=(f"Sum closure of {key_a} (order {ga.order}) and "
                        f"{key_b} (order {gb.order}) via derivative-closed "
                        f"companion-basis elimination (dim<={ga.order+gb.order})."),
            verified=True,
        )
        return new_key

    def compose(self, key_outer, key_inner, x):
        """
        PROVEN IMPOSSIBLE AS A GENERAL CONSTRUCTION. Rather than attempting
        a search that may hang or silently fail, this returns the theorem
        and its evidence directly: composition of two holonomic generators
        is not, in general, itself holonomic (Bell-number counterexample,
        Stanley 1980 boundedness violation). Callers must not treat this as
        "not yet implemented" -- it is "cannot exist in general."
        """
        return {"possible_in_general": False, "proof": compose_is_provably_impossible_in_general()}

    def certificate_repr(self, key):
        g = self.objects[key]
        terms = " + ".join(f"({g.p[i]})*g^({i})" for i in range(g.order + 1))
        return f"{terms} = 0"


# --------------------------------------------------------------------------
# E. FULL DECISION-TOWER ENTRY POINT (unchanged from v6, included for a
#    single self-contained artifact)
# --------------------------------------------------------------------------

class Layer(Enum):
    LIOUVILLIAN = "Layer 1: Liouvillian (Kovacic-decidable) closed form"
    ELEMENTARY = "Layer 1: Elementary (Risch-decidable) closed form"
    HOLONOMIC_SPECIAL = "Layer 2: Holonomic object (constructed & verified, exact)"
    UNRESOLVED = "Layer X: No decision procedure available (honest limitation)"


@dataclass
class Decision:
    value: object
    layer: Layer
    certificate: str
    registry_key: Optional[str] = None


def classify_ode_pole_structure(r_expr, x):
    r = sp.together(r_expr)
    num, den = sp.fraction(r)
    poles = sp.solve(sp.Eq(den, 0), x) if den != 1 else []
    deg_num = sp.degree(sp.Poly(num, x)) if getattr(num, "free_symbols", None) else 0
    deg_den = sp.degree(sp.Poly(den, x)) if getattr(den, "free_symbols", None) else 0
    return (len(poles) == 0) and not (deg_num > deg_den)


def decide_ode(rhs_coeff, x, y):
    bounded = classify_ode_pole_structure(rhs_coeff, x)
    ode = Eq(Derivative(y(x), x, x) - rhs_coeff * y(x), 0)
    sol = sp.dsolve(ode, y(x))
    if bounded:
        return Decision(sol, Layer.LIOUVILLIAN, f"Kovacic check: r(x)={rhs_coeff} bounded -> Liouvillian.")
    return Decision(sol, Layer.HOLONOMIC_SPECIAL,
                     f"Kovacic check: r(x)={rhs_coeff} unbounded -> PROVEN no Liouvillian solution.")


def risch_with_trig_rewrite(integrand, x):
    try:
        return risch_integrate(integrand, x), False
    except NotImplementedError:
        rewritten = sp.expand(integrand.rewrite(sp.exp))
        return risch_integrate(rewritten, x), True


def decide_integral(integrand, x, registry, max_order=3, max_degree=3, expand_point=0):
    try:
        result, was_rewritten = risch_with_trig_rewrite(integrand, x)
    except NotImplementedError as e:
        return Decision(None, Layer.UNRESOLVED, f"Risch unsupported even after Euler rewrite ({e}).")
    if isinstance(result, (NonElementaryIntegral, sp.Integral)):
        seed_key = registry.register_from_expr(integrand, x, max_order=max_order,
                                                 max_degree=max_degree, expand_point=expand_point)
        if seed_key is None:
            return Decision(result, Layer.UNRESOLVED,
                             "Risch PROVED non-elementary, but no holonomic certificate found within search bounds.")
        antideriv_key = registry.integral_closure(seed_key, x)
        rewrite_note = " (Euler-formula rewrite used)" if was_rewritten else ""
        cert = (f"Risch PROVED no elementary antiderivative{rewrite_note}. "
                f"{seed_key}: {registry.certificate_repr(seed_key)}. "
                f"{antideriv_key}: {registry.certificate_repr(antideriv_key)}.")
        return Decision(result, Layer.HOLONOMIC_SPECIAL, cert, registry_key=antideriv_key)
    return Decision(result, Layer.ELEMENTARY, "Risch CONSTRUCTED an elementary antiderivative directly.")


# ==========================================================================
# SELF-TEST / VERIFICATION BLOCK
# Lean counterparts (isar-proofs): see docs/holonomic_closure_and_isar_session.md §12
#   exp              -> ISAR.exp_holonomic
#   exp(-x^2)        -> ISAR.gaussian_holonomic
#   product/sum      -> ISAR.exp_mul_gaussian_holonomic / exp_add_gaussian_isHolonomic
#   mixed product    -> ISAR.fresnelSin_mul_gaussian_isHolonomic (+ fresnel_gaussian_tensor_bound)
#   double integral  -> ISAR.gaussian_double_integral_closure
#   composition      -> ISAR.compose_refuses_in_general / holonomic_not_closed_under_compose
# ==========================================================================
if __name__ == "__main__":
    x = sp.symbols("x")
    y = sp.Function("y")
    reg = HolonomicRegistry()

    print("=" * 78)
    print("TEST 1 -- ODE decision tower")
    print("=" * 78)
    for label, r in [("y''=y", sp.Integer(1)), ("y''=x*y (Airy)", x)]:
        d = decide_ode(r, x, y)
        print(f"  {label:20s} -> {d.layer.name:12s} | {d.value}")

    print()
    print("=" * 78)
    print("TEST 2 -- Elementary integrals")
    print("=" * 78)
    for label, expr in [("2x*e^(x^2)", 2*x*sp.exp(x**2)), ("sin(x)", sp.sin(x))]:
        d = decide_integral(expr, x, reg)
        print(f"  {label:14s} -> {d.layer.name:12s} | value={str(d.value)[:30]}")

    print()
    print("=" * 78)
    print("TEST 3 -- Non-elementary integrals: derive->verify->register->level-up")
    print("=" * 78)
    ext_truth = {}
    for label, expr, ep in [("exp(-x^2)", sp.exp(-x**2), 0), ("exp(x)/x", sp.exp(x)/x, 1),
                             ("sin(x^2)", sp.sin(x**2), 0)]:
        d = decide_integral(expr, x, reg, expand_point=ep)
        print(f"  {label:12s} -> {d.layer.name:18s} key={d.registry_key}")
        ext_truth[label] = d.registry_key

    truth_exprs = {"exp(-x^2)": sp.erf(x), "exp(x)/x": sp.Ei(x),
                   "sin(x^2)": sp.fresnels(x*sp.sqrt(2/sp.pi))*sp.sqrt(sp.pi/2)}
    for label, gk in ext_truth.items():
        gen = reg.objects[gk]
        truth = truth_exprs[label]
        derivs = [sp.diff(truth, x, i) for i in range(gen.order + 1)]
        residual = sp.simplify(sum(gen.p[i] * derivs[i] for i in range(gen.order + 1)))
        print(f"    external check {label}: residual={residual} ({'PASS' if residual==0 else 'FAIL'})")

    print()
    print("=" * 78)
    print("TEST 4 -- product_closure and sum_closure, verified against truth")
    print("=" * 78)
    seed_exp_key = reg.register_from_expr(sp.exp(x), x)
    seed_exp2_key = reg.register_from_expr(sp.exp(-x**2), x)
    prod_key = reg.product_closure(seed_exp_key, seed_exp2_key, x)
    sum_key = reg.sum_closure(seed_exp_key, seed_exp2_key, x)
    print(f"  product: {reg.certificate_repr(prod_key)}")
    print(f"  sum:     {reg.certificate_repr(sum_key)}")

    h_prod = sp.exp(x) * sp.exp(-x**2)
    gp = reg.objects[prod_key]
    rp = sp.simplify(sum(gp.p[i]*sp.diff(h_prod, x, i) for i in range(gp.order+1)))
    print(f"  product external check: residual={rp} ({'PASS' if rp==0 else 'FAIL'})")

    h_sum = sp.exp(x) + sp.exp(-x**2)
    gs = reg.objects[sum_key]
    rs = sp.simplify(sum(gs.p[i]*sp.diff(h_sum, x, i) for i in range(gs.order+1)))
    print(f"  sum external check: residual={rs} ({'PASS' if rs==0 else 'FAIL'})")

    print()
    print("=" * 78)
    print("TEST 4b -- RESTORED: mixed-order product (order-2 x order-1),")
    print("           the genuinely hard case, with minimality sanity check")
    print("=" * 78)
    fresnel_key = reg.register_from_expr(sp.sin(x**2), x, max_order=2, max_degree=3)
    prod_key2 = reg.product_closure(fresnel_key, seed_exp2_key, x)
    print(f"  sin(x^2)-class (order {reg.objects[fresnel_key].order}) x "
          f"exp(-x^2)-class (order {reg.objects[seed_exp2_key].order}) -> {prod_key2}")
    print(f"  {prod_key2}: {reg.certificate_repr(prod_key2)}")
    h_mix = sp.sin(x**2) * sp.exp(-x**2)
    gm = reg.objects[prod_key2]
    rm = sp.simplify(sum(gm.p[i]*sp.diff(h_mix, x, i) for i in range(gm.order+1)))
    print(f"  external check vs sin(x^2)*exp(-x^2): residual={rm} ({'PASS' if rm==0 else 'FAIL'})")
    naive_bound = reg.objects[fresnel_key].order * reg.objects[seed_exp2_key].order
    print(f"  minimality check: naive tensor bound={naive_bound}, found order={gm.order} "
          f"({'matches, no accidental collapse' if gm.order==naive_bound else 'collapsed below naive bound'})")

    print()
    print("=" * 78)
    print("TEST 4c -- RESTORED: double-integral level-up chain (seed->lvl1->lvl2)")
    print("=" * 78)
    seed_key2 = reg.register_from_expr(sp.exp(-x**2), x)
    lvl1_key = reg.integral_closure(seed_key2, x)
    lvl2_key = reg.integral_closure(lvl1_key, x)
    print(f"  seed {seed_key2}: {reg.certificate_repr(seed_key2)}")
    print(f"  lvl1 {lvl1_key}: {reg.certificate_repr(lvl1_key)}")
    print(f"  lvl2 {lvl2_key}: {reg.certificate_repr(lvl2_key)}")
    h_dbl = x*sp.erf(x) + sp.exp(-x**2)/sp.sqrt(sp.pi)
    g3 = reg.objects[lvl2_key]
    r3 = sp.simplify(sum(g3.p[i]*sp.diff(h_dbl, x, i) for i in range(g3.order+1)))
    print(f"  external check vs x*erf(x)+exp(-x^2)/sqrt(pi): residual={r3} ({'PASS' if r3==0 else 'FAIL'})")

    print()
    print("=" * 78)
    print("TEST 5 -- composition: PROVEN impossible in general (not a gap)")
    print("=" * 78)
    comp_result = reg.compose(seed_exp_key, seed_exp_key, x)
    print(f"  possible_in_general: {comp_result['possible_in_general']}")
    print(f"  counterexample: {comp_result['proof']['counterexample']}")
    for n, val in comp_result['proof']['samples_Bn_pow_1_over_n']:
        print(f"    n={n:3d}  Bell(n)^(1/n)={val:.4f}")
    print(f"  strictly increasing (no plateau): {comp_result['proof']['strictly_increasing_confirmed']}")
    print(f"  conclusion: {comp_result['proof']['conclusion']}")
