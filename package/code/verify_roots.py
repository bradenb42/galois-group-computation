"""
verify_roots.py — root verification in the three approximation rings.

Given a resolvent R = R_{U,V,F} and a recognized value v, certify
  (a) v is a simple root of R,
  (b) the complete list of roots of R in the ring (so that "no other root" and
      the negative verdict are decided),
as computations modulo the precision k_prf, recording k_prf, the factorization
data used, and the root-simplicity check.

  Z       (complete integer-root lists over Z)  auxiliary prime ℓ with R̄ squarefree; distinct-degree
                  factorization of R̄ (the factorization data); Hensel/Newton lift
                  of the *linear* factors only, to ℓ^k with ℓ^k > 2^{B+1};
                  symmetric remainders, filter |v_i| ≤ 2^B, exact test; and the
                  same test modulo ℓ^{k_prf} (valid by |R(v_i)| ≤ 2^{N(B+1)}).
  O_K     (root verification over a local field)  Newton polygon of R(y+v) over O_K at coefficient precision m:
                  c_0 ≡ 0, v(c_1) < m, λ_2 exact from the polygon right of j=1,
                  m > v(c_1) + λ_2, and k_eff > e' λ_2.  Other roots in K are
                  decided per coset by the image check.
  F_q[t]  (root verification over F_q[t])  exact in the ring; the u-adic formulation is R(v) ≡ 0 mod
                  u^{NB+1} and R'(v) ≢ 0 mod u^{(N-1)B+1}; the complete root list
                  comes from a point t_1 with R(t_1, x) squarefree, lifting its
                  linear factors u_1-adically to u_1^{B+1}, re-expanding in t and
                  applying the Frobenius test to the t-polynomial.

Conventions: polynomials are lists low -> high; F_q[t] elements are lists of
ints mod p (q = p prime here); the size bound B is the one of the three approximation rings — for F_q[t]
the root bound is δ = max_j deg(a_j)/(n - j), a_j the coefficient of x^j
(this is the correct index convention for the Newton polygon at infinity).
"""

from __future__ import annotations

import math
from typing import Dict, List, Optional, Sequence, Tuple

import hensel_frobenius as hf
from hensel_frobenius import Zmod, PolyQuot, _peval, _pderiv, _pextgcd_field, _pdivmod_field, _strip, newton_root

INF = 10 ** 9


# ----------------------------------------------------------------------------
# shared: finite-field polynomial helpers
# ----------------------------------------------------------------------------

def _pmod(R, a, m):
    return _pdivmod_field(R, a, m)[1]

def _powmod(R, base, e, m):
    """base^e mod m in R[x], R a field."""
    result = [R.one()]
    base = _pmod(R, base, m)
    while e:
        if e & 1:
            result = _pmod(R, hf._pmul(R, result, base), m)
        base = _pmod(R, hf._pmul(R, base, base), m)
        e >>= 1
    return result

def distinct_degree_factorization(R, poly, q: int) -> List[Tuple[int, int]]:
    """[(degree d, number of irreducible factors of degree d)] of a squarefree
    polynomial over F_q (R the field object, q its size)."""
    f = _strip(R, poly)
    lc_inv = R.inv(f[-1]); f = [R.mul(c, lc_inv) for c in f]
    out = []
    x = [R.zero(), R.one()]
    h = x
    d = 0
    while len(f) - 1 >= 2 * (d + 1):
        d += 1
        h = _powmod(R, h, q, f)                               # x^{q^d} mod f
        g, _, _ = _pextgcd_field(R, _strip(R, hf._padd(R, h, hf._pneg(R, x))), f)
        if len(g) > 1:
            out.append((d, (len(g) - 1) // d))
            f, _ = _pdivmod_field(R, f, g)
            f = _strip(R, f); lc_inv = R.inv(f[-1]); f = [R.mul(c, lc_inv) for c in f]
            h = _pmod(R, h, f)
    if len(f) > 1:
        out.append((len(f) - 1, 1))
    return out

def _is_squarefree(R, poly) -> bool:
    g, _, _ = _pextgcd_field(R, _strip(R, poly), _strip(R, _pderiv(R, poly)))
    return len(g) == 1


# ----------------------------------------------------------------------------
# case 1: Z
# ----------------------------------------------------------------------------

def _ev_int(poly: Sequence[int], x: int) -> int:
    acc = 0
    for c in reversed(poly):
        acc = acc * x + c
    return acc

def _vp(x: int, p: int) -> int:
    if x == 0:
        return INF
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

def _gcd_Q(a: List[int], b: List[int]) -> List[int]:
    """monic gcd over Q of integer polynomials (Gauss: in Z[x] when inputs are monic)."""
    from fractions import Fraction
    class _Q:
        def zero(self): return Fraction(0)
        def one(self): return Fraction(1)
        def add(self, x, y): return x + y
        def sub(self, x, y): return x - y
        def neg(self, x): return -x
        def mul(self, x, y): return x * y
        def is_zero(self, x): return x == 0
        def inv(self, x): return 1 / x
        def eq(self, x, y): return x == y
        def from_int(self, k): return Fraction(k)
    Q = _Q()
    g, _, _ = _pextgcd_field(Q, [Fraction(c) for c in a], [Fraction(c) for c in b])
    assert all(c.denominator == 1 for c in g)
    return [int(c) for c in g]

def squarefree_part(R: List[int]) -> Tuple[List[int], List[int]]:
    """(R / gcd(R, R'), gcd) for monic R ∈ Z[x]; the quotient is monic in Z[x] with the same root set."""
    dR = [i * R[i] for i in range(1, len(R))]
    g = _gcd_Q(R, dR)
    if len(g) == 1:
        return list(R), g
    from fractions import Fraction
    q, r = hf._pdivmod_monic(_QRing(), [Fraction(c) for c in R], [Fraction(c) for c in g])
    assert all(c == 0 for c in r) and all(c.denominator == 1 for c in q)
    return [int(c) for c in q], g

class _QRing:
    from fractions import Fraction as _F
    def zero(self): return self._F(0)
    def one(self): return self._F(1)
    def add(self, x, y): return x + y
    def sub(self, x, y): return x - y
    def neg(self, x): return -x
    def mul(self, x, y): return x * y
    def is_zero(self, x): return x == 0
    def eq(self, x, y): return x == y
    def from_int(self, k): return self._F(k)

def verify_Z(R: List[int], v: int, B: float, ell: Optional[int] = None, max_ell: int = 10 ** 6) -> Dict:
    """R ∈ Z[x] monic (exact), v ∈ Z, B ≥ log2 of a bound on the roots of R.
    Linear factors are lifted for the squarefree part of R (same root set);
    simplicity of v is an exact test on R itself."""
    N = len(R) - 1
    R_full = list(R)
    R, gcd_RRp = squarefree_part(R)
    # auxiliary prime with squarefree reduction of the squarefree part (ℓ ∤ disc R_sf)
    if ell is None:
        ell = 3
        while not (hf.is_prime(ell) and _is_squarefree(Zmod(ell), [c % ell for c in R])):
            ell += 1
            if ell > max_ell:
                raise ArithmeticError("no auxiliary prime with squarefree reduction found below max_ell")
    Fl = Zmod(ell)
    Rbar = [c % ell for c in R]
    assert _is_squarefree(Fl, Rbar), "R_sf must be squarefree mod ell"
    ddf = distinct_degree_factorization(Fl, Rbar, ell)
    roots_mod = [x for x in range(ell) if _peval(Fl, Rbar, x) == 0]
    # Hensel/Newton lift of the linear factors only
    k = int(math.floor((B + 1) / math.log2(ell))) + 1             # ell^k > 2^{B+1}
    k_prf = int(math.floor(N * (B + 1) / math.log2(ell))) + 1     # ell^{k_prf} > 2^{N(B+1)}
    Zk = Zmod(ell ** k)
    Rk = [c % ell ** k for c in R]
    lifted, candidates, integer_roots = [], [], []
    for r in roots_mod:
        a, it = newton_root(Zk, Rk, r)
        lifted.append((r, a, it))
        sr = a - ell ** k if a > ell ** k // 2 else a
        if abs(sr) > 2 ** B:                                       # spurious lift (termination fix): cannot be a root
            candidates.append((sr, "discarded: |candidate| > 2^B"))
            continue
        exact = _ev_int(R, sr) == 0
        modular = _ev_int(R, sr) % ell ** k_prf == 0             # valid because |R(sr)| <= 2^{N(B+1)} < ell^{k_prf}
        assert exact == modular
        candidates.append((sr, "root" if exact else "not a root"))
        if exact:
            integer_roots.append(sr)
    dR = [i * R_full[i] for i in range(1, len(R_full))]
    v_is_root = _ev_int(R_full, v) == 0
    Rp_v = _ev_int(dR, v)
    return {
        "ring": "Z", "N": N, "ell": ell, "k_lift": k, "k_prf": k_prf, "B": B,
        "squarefree": len(gcd_RRp) == 1, "gcd_R_Rprime": gcd_RRp, "squarefree_part_degree": len(R) - 1,
        "factorization_mod_ell": {"squarefree": True, "distinct_degree": ddf, "linear_roots": roots_mod},
        "lifted_linear_factors": [{"root_mod_ell": r, "lift": a, "newton_iterations": it} for r, a, it in lifted],
        "candidates": candidates, "integer_roots": sorted(integer_roots),
        "v_is_root": v_is_root, "v_simple": v_is_root and Rp_v != 0, "R_prime_at_v": Rp_v,
        "v_p_of_R_prime_at_v": (_vp(Rp_v, ell) if Rp_v else INF),
        "no_other_integer_root": integer_roots == [v] if v_is_root else len(integer_roots) == 0,
        "bound_consistent": (v in integer_roots) if v_is_root else True,   # False would mean B is not a valid root bound
    }


# ----------------------------------------------------------------------------
# case 2: O_K  (here K = Q_p, coefficients of R in Z_p known mod p^m)
# ----------------------------------------------------------------------------

def taylor_shift(R: List[int], v: int, mod: int) -> List[int]:
    """coefficients of R(y + v) modulo `mod`."""
    n = len(R) - 1
    c = [x % mod for x in R]
    # repeated synthetic division by (y - v)
    out = []
    for _ in range(n + 1):
        rem = 0
        for i in range(len(c) - 1, -1, -1):
            rem = (rem * v + c[i]) % mod
        out.append(rem)
        # divide c by (y - v): c = q (y - v) + rem
        q = [0] * (len(c) - 1)
        acc = 0
        for i in range(len(c) - 1, 0, -1):
            acc = (acc * v + c[i]) % mod
            q[i - 1] = acc
        c = q
        if not c:
            break
    return out

def newton_polygon_lower_hull(points: List[Tuple[int, float]]) -> List[Tuple[int, float]]:
    pts = sorted(points)
    hull: List[Tuple[int, float]] = []
    for pnt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            x3, y3 = pnt
            if (y2 - y1) * (x3 - x1) >= (y3 - y1) * (x2 - x1):  # middle point not strictly below the chord
                hull.pop()
            else:
                break
        hull.append(pnt)
    return hull

def verify_OK(R_mod: List[int], v: int, p: int, m: int, e_prime: int, k_eff: int) -> Dict:
    """R_mod: coefficients of R in O_K = Z_p modulo p^m; v ∈ Z_p (as an integer
    mod p^m); e_prime = e(K'/K); k_eff = certified π'-adic precision of the roots."""
    mod = p ** m
    c = taylor_shift(R_mod, v % mod, mod)
    vals = [(_vp(cj % mod, p) if cj % mod else INF) for cj in c]     # exact when < m, else "≥ m"
    known = [(j, vals[j]) for j in range(1, len(c)) if vals[j] < m]
    rec: Dict = {"ring": "O_K", "p": p, "m": m, "e_prime": e_prime, "k_eff": k_eff,
                 "valuations": [("≥%d" % m if vv >= m else vv) for vv in vals],
                 "lambda2": None, "condition_(*)_m>v(c1)+lambda2": None, "condition_k_eff>e'lambda2": None}
    c0_ok = vals[0] >= m
    c1_known = vals[1] < m
    rec["c0_vanishes_mod_p^m"] = c0_ok
    rec["v(c1)"] = vals[1] if c1_known else None
    if not c0_ok:
        rec["verdict"] = "v is not a root to precision m"
        rec["simple_root_certified"] = False
        return rec
    if not c1_known:
        rec["verdict"] = "inconclusive: v(c1) >= m, raise precision (or R has a multiple root near v)"
        rec["simple_root_certified"] = False
        return rec
    # polygon to the right of j = 1: all vertices have valuation <= v(c1) < m, hence known exactly
    hull = newton_polygon_lower_hull([(j, float(vv)) for j, vv in known])
    # λ2 = max over j>=2 of (v(c1) - v(cj))/(j-1)  (second slope magnitude)
    lam2 = max(((vals[1] - vv) / (j - 1)) for j, vv in known if j >= 2) if any(j >= 2 for j, _ in known) else 0.0
    rec["lambda2"] = lam2
    rec["polygon_right_of_1"] = hull
    cond_vertex = m > vals[1] + lam2                   # (*)
    cond_id = k_eff > e_prime * lam2                    # identification of the coset
    rec["condition_(*)_m>v(c1)+lambda2"] = cond_vertex
    rec["condition_k_eff>e'lambda2"] = cond_id
    rec["simple_root_certified"] = cond_vertex and cond_id
    rec["closest_root_distance_lower_bound_v_pi"] = f">= {m} - {vals[1]} = {m - vals[1]}"
    rec["verdict"] = "simple root in K certified near v" if rec["simple_root_certified"] else "conditions failed: raise precision"
    return rec


# ----------------------------------------------------------------------------
# case 3: F_q[t]  (q = p prime; elements of F_p[t] are lists of ints mod p)
# ----------------------------------------------------------------------------

class Fpt:
    def __init__(self, p: int): self.p = p; self.Fp = Zmod(p)
    def norm(self, a): return _strip(self.Fp, [c % self.p for c in a])
    def add(self, a, b): return self.norm(hf._padd(self.Fp, a, b))
    def sub(self, a, b): return self.norm(hf._padd(self.Fp, a, hf._pneg(self.Fp, b)))
    def mul(self, a, b): return self.norm(hf._pmul(self.Fp, a, b))
    def is_zero(self, a): return not self.norm(a)
    def deg(self, a): a = self.norm(a); return len(a) - 1 if a else -1
    def eval_poly_in_x(self, Rx, vt):
        """R(vt) for R with coefficients in F_p[t] (list of lists), vt ∈ F_p[t]."""
        acc = []
        for c in reversed(Rx):
            acc = self.add(self.mul(acc, vt), c)
        return acc
    def deriv_in_x(self, Rx):
        return [self.norm([(i * c) % self.p for c in Rx[i]]) for i in range(1, len(Rx))]

def verify_Fqt(Rx: List[List[int]], v: List[int], p: int, B: float, t1: Optional[int] = None, seed: int = 0) -> Dict:
    """Rx: monic in x with coefficients in F_p[t] (exact); v ∈ F_p[t]; B ≥ degree bound on the roots of R."""
    K = Fpt(p)
    N = len(Rx) - 1
    Bi = int(math.floor(B))                 # ring roots have degree <= floor(B)
    NB = int(math.floor(N * B))             # coefficients of R have degree <= floor(N*B)
    k_prf = NB + 1
    Rv = K.eval_poly_in_x(Rx, v)
    dRx = K.deriv_in_x(Rx)
    Rpv = K.eval_poly_in_x(dRx, v)
    # u-adic formulation at the approximation point: R(v) == 0 iff R(v) ≡ 0 mod u^{NB+1}
    v_is_root = K.is_zero(Rv)
    # u-adic formulation (root verification over F_q[t]): deg R(v) <= floor(N B) < k_prf, so R(v) ≡ 0 mod u^{k_prf} iff R(v) = 0
    assert K.deg(Rv) <= NB, "degree bound violated: B is not a valid bound"
    u_adic_root_check = v_is_root
    v_simple = v_is_root and not K.is_zero(Rpv)
    # complete root list via a point t1 with R(t1, x) squarefree over F_p
    Fp = Zmod(p)
    if t1 is None:
        for cand in range(p):
            R_t1 = [_peval(Fp, c, cand) if c else 0 for c in Rx]
            if _is_squarefree(Fp, R_t1):
                t1 = cand; break
        assert t1 is not None, "no point in F_p with squarefree specialization (take an extension point)"
    R_t1 = [_peval(Fp, c, t1) if c else 0 for c in Rx]
    ddf = distinct_degree_factorization(Fp, R_t1, p)
    # roots of R(t1, x): linear factors over F_p (roots in F_p[t] specialize into F_p)
    roots_mod = [x for x in range(p) if _peval(Fp, R_t1, x) == 0]
    # lift u1-adically to u1^{B+1}: S1 = F_p[[u1]]/u1^{B+1}, coefficients of R shifted to u1 = t - t1
    F1 = PolyQuot(Fp, [0, 1], "field")                       # F_p itself as a degree-1 quotient
    S1 = PolyQuot(F1, [F1.zero()] * (Bi + 1) + [F1.one()], "constant")
    R_S1 = [S1.from_list([F1.from_int(cc) for cc in hf._shift_poly_t(p, c, t1)]) if c else S1.zero() for c in Rx]
    candidates, ring_roots = [], []
    for r in roots_mod:
        a, it = newton_root(S1, R_S1, S1.from_base(F1.from_int(r)))
        # read as polynomial in u1 of degree <= B, re-expand in t
        coeffs_u1 = [cc[0] for cc in a]                            # F1 elements are 1-tuples of ints
        vt = []
        for k, ck in enumerate(coeffs_u1):
            # (t - t1)^k
            term = [1]
            for _ in range(k):
                term = K.mul(term, [(-t1) % p, 1])
            vt = K.add(vt, [(ck * x) % p for x in term])
        exact = K.is_zero(K.eval_poly_in_x(Rx, vt))
        candidates.append({"root_mod_(t-t1)": r, "newton_iterations": it, "candidate": vt, "root": exact})
        if exact:
            ring_roots.append(vt)
    return {
        "ring": "F_p[t]", "p": p, "N": N, "B": B, "k_prf": k_prf, "t1": t1,
        "factorization_at_t1": {"squarefree": True, "distinct_degree": ddf, "linear_roots": roots_mod},
        "R(v)": Rv, "R'(v)": Rpv, "v_is_root": v_is_root, "u_adic_root_check": u_adic_root_check,
        "v_simple": v_simple, "candidates": candidates, "ring_roots": ring_roots,
        "no_other_ring_root": (ring_roots == [K.norm(v)]) if v_is_root else (len(ring_roots) == 0),
    }


# ----------------------------------------------------------------------------
# demo: build resolvents in each ring and run the verification
# ----------------------------------------------------------------------------

if __name__ == "__main__":
    import json
    import descent as ds
    import invariants as inv

    print("=" * 90); print("case 1 (Z): resolvents from the descent of x^5-5x+12 (D_5) and x^5-2 (F_20)")
    for f in ([12, -5, 0, 0, 0, 1], [-2, 0, 0, 0, 0, 1]):
        st = ds.DescentState(f, 120, table_path="tables/invariants_descent.json")
        U = inv.closure(inv.S_n(5), 5)
        res = ds.descend(st, U, verbose=False)
        R, v, B = res["R"], res["v"], res["B"]
        rep = verify_Z(R, v, B)
        print(f"  f={f}: R of degree {rep['N']}, v={v} (Tschirnhaus T={res['T']}); ell={rep['ell']}, k_lift={rep['k_lift']}, k_prf={rep['k_prf']}")
        print(f"     factorization of R mod ell: {rep['factorization_mod_ell']}")
        print(f"     candidates: {rep['candidates']}")
        print(f"     v is root: {rep['v_is_root']}, simple: {rep['v_simple']} (R'(v)={rep['R_prime_at_v']}, v_ell={rep['v_p_of_R_prime_at_v']}), "
              f"integer roots {rep['integer_roots']}, no other: {rep['no_other_integer_root']}")
        # negative resolvent: (S_5, A_5) for x^5-2 has no integer root
    st = ds.DescentState([-2, 0, 0, 0, 0, 1], 120, table_path="tables/invariants_descent.json")
    U = inv.closure(inv.S_n(5), 5); V = inv.closure(inv.A_n(5), 5)
    F = st.ic.invariant(inv.S_n(5), inv.A_n(5), 5)["F"]
    B = st.bound_B(F); st.ensure_precision(st.k_prf(B, 2) + 2)
    vals = [st.evaluate(inv.act(s, F)) for s in ds.coset_reps(U, V)]
    R = [st.symmetric_remainder(c, st.K) for c in hf.poly_from_roots(st.A, vals)]
    rep = verify_Z(R, 0, B)
    print(f"  (S5,A5) for x^5-2: R={R}; factorization mod {rep['ell']}: {rep['factorization_mod_ell']['distinct_degree']}, "
          f"integer roots {rep['integer_roots']} -> negative verdict")

    print("=" * 90); print("case 2 (O_K): x^4-3 over Q_3, U = S_4, V = G = <iota, phi~> (order 8)")
    ob = hf.case2([-3, 0, 0, 0, 1], p=3, K=16, return_objects=True)
    A, Bq, roots, n, K, p = ob["A"], ob["B"], ob["roots"], ob["n"], ob["K"], ob["p"]
    # the untransformed resolvent is y^3 (all coset values vanish): apply T(x) = x + x^2 (termination, Tschirnhaus)
    roots = [Bq.add(r, Bq.mul(r, r)) for r in roots]
    print("  roots replaced by T(alpha) = alpha + alpha^2 (the untransformed resolvent is y^3)")
    G = inv.closure([tuple(ob["tau_iota"]), tuple(ob["tau_phi"])], n)
    U = inv.closure(inv.S_n(n), n)
    ic = inv.InvariantConstructor("tables/invariants_descent.json")
    recF = ic.invariant(inv.S_n(n), inv.generating_set(G, n), n)
    F = recF["F"]
    def evalB(F):
        acc = Bq.zero()
        for e, c in F.items():
            term = Bq.from_int(c)
            for i, ei in enumerate(e):
                for _ in range(ei):
                    term = Bq.mul(term, roots[i])
            acc = Bq.add(acc, term)
        return acc
    cos = ds.coset_reps(U, G)
    vals = [evalB(inv.act(s, F)) for s in cos]
    R_B = hf.poly_from_roots(Bq, vals)
    def in_Zp(x):  # B element with only the constant-of-constant coordinate
        return all(A.is_zero(c) for c in x[1:]) and all(A.base.is_zero(c) for c in x[0][1:])
    assert all(in_Zp(c) for c in R_B), "resolvent coefficients must lie in Z_p"
    R_mod = [c[0][0] % p ** K for c in R_B]
    m, e_prime, k_eff = K, n, n * K
    for s_, val in zip(cos, vals):
        if in_Zp(val):
            v = val[0][0] % p ** K
            rep = verify_OK(R_mod, v, p, m, e_prime, k_eff)
            print(f"  coset {s_}: image check passes, v ≡ {v} mod {p}^{m}; valuations of R(y+v): {rep['valuations']}")
            cid = rep["condition_k_eff>e'lambda2"]
            print(f"     v(c1)={rep['v(c1)']}, lambda2={rep['lambda2']}, (*) {rep['condition_(*)_m>v(c1)+lambda2']}, "
                  f"k_eff>e'lambda2 {cid} -> {rep['verdict']}")
        else:
            print(f"  coset {s_}: image check fails -> rho not in K (unconditional negative)")

    print("=" * 90); print("case 3 (F_7[t]): x^3 - t^2, U = S_3, V = A_3 (G = C_3 since -27 is a square mod 7)")
    f_t = [[0, 0, -1 % 7], [0], [0], [1]]
    ob = hf.case3(f_t, p=7, t0=1, K=30, return_objects=True)
    S, roots, p = ob["S"], ob["roots"], ob["p"]
    n = 3
    U = inv.closure(inv.S_n(3), 3); V = inv.closure(inv.A_n(3), 3)
    F = ic.invariant(inv.S_n(3), inv.A_n(3), 3)["F"]
    d = max(sum(e) for e in F)
    delta = max((len(_strip(Zmod(7), a)) - 1) / (n - j) for j, a in enumerate(f_t[:-1]) if _strip(Zmod(7), a))
    B = d * delta
    def evalS(F):
        acc = S.zero()
        for e, c in F.items():
            term = S.from_int(c)
            for i, ei in enumerate(e):
                for _ in range(ei):
                    term = S.mul(term, roots[i])
            acc = S.add(acc, term)
        return acc
    cos = ds.coset_reps(U, V)
    vals = [evalS(inv.act(s, F)) for s in cos]
    R_S = hf.poly_from_roots(S, vals)
    K3 = Fpt(7)
    def series_to_t(ser, degbound):
        # truncate at degree <= degbound in u = t - t0, re-expand in t (t0 = 1); coefficients must be in F_p
        vt = []
        for k, ck in enumerate(ser[: degbound + 1]):
            assert all(x == 0 for x in ck[1:]), "coefficient not in F_p"
            term = [1]
            for _ in range(k):
                term = K3.mul(term, [(-ob["t0"]) % 7, 1])
            vt = K3.add(vt, [(ck[0] * x) % 7 for x in term])
        assert all(all(x == 0 for x in ck) for ck in ser[degbound + 1:]), "series not a polynomial of the expected degree"
        return vt
    N = len(cos)
    Rx = [series_to_t(c, int(N * B)) for c in R_S]
    print(f"  B = d*delta = {d}*{delta:.3f} = {B:.3f}; R(x) over F_7[t] = {Rx} (coefficients low->high, each a polynomial in t)")
    for s_, val in zip(cos, vals):
        v = series_to_t(val, int(B))
        rep = verify_Fqt(Rx, v, 7, B)
        rpv = rep["R'(v)"]
        print(f"  coset {s_}: v = {v}; R(v)={rep['R(v)']}, R'(v)={rpv}, simple={rep['v_simple']}, k_prf={rep['k_prf']}, "
              f"t1={rep['t1']}, factorization at t1: {rep['factorization_at_t1']['distinct_degree']}, ring roots {rep['ring_roots']}, no other: {rep['no_other_ring_root']}")