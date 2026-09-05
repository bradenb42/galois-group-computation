"""
hensel_frobenius.py — Hensel lifting in the three approximation rings (p-adic,
local, power-series), the certified Frobenius and inertia elements, and the
certification that such an element lies in G by checking that it fixes the coefficients of f
reconstructed from the roots.

Rings implemented (all with exact arithmetic on coordinates, truncated at a
fixed precision so that truncation is a ring homomorphism):

  case 1   A  = (Z/p^K)[z]/(m(z)),  m irreducible mod p of degree s   ≅ O_q / p^K
  case 2   B  = A[x]/(f(x)),        f Eisenstein over Q_p, tame (p ∤ n) ≅ O_{K'}/p^K,  K' = Q_{p^s}(α)
  case 3   S  = F_{p^s}[[u]]/(u^K), u = t - t0                         ≅ F_{q^s}[[u]]/u^K   (q = p)

Hensel lifting is one function, `newton_root`, used everywhere with a *unit*
derivative.  In case 2 the roots of f are obtained without any precision loss
(effective precision after Hensel lifting) by the change of variables y = x/α:  g(y) := f(αy)/α^n ≡ y^n - 1 (mod π'),
whose roots ζ^j are simple modulo π' when p ∤ n.  The unit-derivative Hensel
step therefore certifies the roots of f to the full coordinate precision p^K,
i.e. π'^{nK}.  (The wild case needs the explicit splitting-field construction
and is not implemented here.)

Elements of G obtained (certified Frobenius and inertia elements):
  case 1: τ_φ from the Frobenius φ of A, itself obtained by Hensel-lifting z^p
          to the root of m congruent to it mod p;
  case 2: τ_ι from the inertia generator ι : α ↦ α_1 (the root lifted from ζ·α),
          and τ_φ̃ from the canonical Frobenius lift φ̃ (coefficientwise φ, α fixed;
          an automorphism because f has coefficients in Q_p);
  case 3: τ_φ from φ : Σ c_j u^j ↦ Σ c_j^p u^j.

Certification (`certify_element`): (i) Π_j (x - α̂_j) reconstructs f exactly at
the working precision; (ii) ψ fixes every reconstructed coefficient; (iii) ψ maps
the root list bijectively onto itself, giving the permutation; (iv) roots are
pairwise separated at the working precision, so the matching is unambiguous.
"""

from __future__ import annotations

import itertools
import json
import math
import random
from typing import Callable, List, Sequence, Tuple

INF = float("inf")


# ----------------------------------------------------------------------------
# Base ring Z/N
# ----------------------------------------------------------------------------

class Zmod:
    def __init__(self, N: int):
        self.N = N

    def zero(self): return 0
    def one(self): return 1
    def from_int(self, k): return k % self.N
    def add(self, a, b): return (a + b) % self.N
    def sub(self, a, b): return (a - b) % self.N
    def neg(self, a): return (-a) % self.N
    def mul(self, a, b): return (a * b) % self.N
    def eq(self, a, b): return (a - b) % self.N == 0
    def is_zero(self, a): return a % self.N == 0
    def is_unit(self, a): return math.gcd(a, self.N) == 1
    def inv(self, a): return pow(a, -1, self.N)
    def elements(self): return range(self.N)


# ----------------------------------------------------------------------------
# Polynomial helpers over an arbitrary base ring (lists low -> high)
# ----------------------------------------------------------------------------

def _strip(R, a):
    a = list(a)
    while a and R.is_zero(a[-1]):
        a.pop()
    return a

def _padd(R, a, b):
    n = max(len(a), len(b))
    return [R.add(a[i] if i < len(a) else R.zero(), b[i] if i < len(b) else R.zero()) for i in range(n)]

def _pneg(R, a):
    return [R.neg(c) for c in a]

def _pmul(R, a, b):
    if not a or not b:
        return []
    out = [R.zero()] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if R.is_zero(x):
            continue
        for j, y in enumerate(b):
            out[i + j] = R.add(out[i + j], R.mul(x, y))
    return out

def _pscale(R, a, c):
    return [R.mul(x, c) for x in a]

def _pdivmod_monic(R, a, m):
    """divide a by monic m; returns (q, r) with deg r < deg m."""
    a = list(a)
    d = len(m) - 1
    q = [R.zero()] * max(0, len(a) - d)
    for i in range(len(a) - 1, d - 1, -1):
        c = a[i]
        if R.is_zero(c):
            continue
        q[i - d] = c
        for j in range(d + 1):
            a[i - d + j] = R.sub(a[i - d + j], R.mul(c, m[j]))
    return q, a[:d] if d > 0 else []

def _pdivmod_field(R, a, b):
    """division in F[z] for a field F (b arbitrary nonzero)."""
    b = _strip(R, b)
    lc_inv = R.inv(b[-1])
    a = _strip(R, a)
    if len(a) < len(b):
        return [], a
    q = [R.zero()] * (len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        c = R.mul(a[-1], lc_inv)
        k = len(a) - len(b)
        q[k] = c
        for j, y in enumerate(b):
            a[k + j] = R.sub(a[k + j], R.mul(c, y))
        a = _strip(R, a)
    return q, a

def _pextgcd_field(R, a, b):
    """returns (g, s, t) with s a + t b = g, g monic, over a field R."""
    r0, r1 = _strip(R, a), _strip(R, b)
    s0, s1 = [R.one()], []
    t0, t1 = [], [R.one()]
    while r1:
        q, r = _pdivmod_field(R, r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, _strip(R, _padd(R, s0, _pneg(R, _pmul(R, q, s1))))
        t0, t1 = t1, _strip(R, _padd(R, t0, _pneg(R, _pmul(R, q, t1))))
    lc_inv = R.inv(r0[-1])
    return _pscale(R, r0, lc_inv), _pscale(R, s0, lc_inv), _pscale(R, t0, lc_inv)

def _peval(R, coeffs, a):
    """Horner evaluation of a polynomial with coefficients in R at a ∈ R."""
    acc = R.zero()
    for c in reversed(coeffs):
        acc = R.add(R.mul(acc, a), c)
    return acc

def _pderiv(R, coeffs):
    out = []
    for i in range(1, len(coeffs)):
        k = R.from_int(i)
        out.append(R.mul(k, coeffs[i]))
    return out


# ----------------------------------------------------------------------------
# Quotient ring base[X]/(modulus)
# ----------------------------------------------------------------------------

class PolyQuot:
    """Elements are tuples of length d = deg(modulus) of base elements, reduced.

    inverse_mode:
      'field'     base is a field and modulus is irreducible: extended Euclid.
      'constant'  the constant term of a unit is a unit of base and X is
                  topologically nilpotent (Eisenstein tower, power series):
                  Newton from y0 = base.inv(a[0]).
      'residue'   base = Z/p^K, modulus irreducible mod p: invert in the residue
                  field and Newton-lift.  `residue` = (field_ring, project, lift).
    """

    def __init__(self, base, modulus: Sequence, inverse_mode: str, residue=None, name="X"):
        self.base = base
        self.mod = list(modulus)
        assert base.eq(self.mod[-1], base.one()), "modulus must be monic"
        self.d = len(self.mod) - 1
        assert self.d >= 1
        self.inverse_mode = inverse_mode
        self.residue = residue
        self.name = name

    # -- constructors ---------------------------------------------------------
    def zero(self): return tuple([self.base.zero()] * self.d)
    def one(self): return self.from_base(self.base.one())
    def from_base(self, c): return tuple([c] + [self.base.zero()] * (self.d - 1))
    def from_int(self, k): return self.from_base(self.base.from_int(k))
    def from_list(self, coeffs): return tuple(self.reduce([c for c in coeffs]))
    def gen(self):
        return self.from_list([self.base.zero(), self.base.one()])

    def reduce(self, coeffs):
        coeffs = list(coeffs)
        if len(coeffs) > self.d:
            _, r = _pdivmod_monic(self.base, coeffs, self.mod)
            coeffs = r
        coeffs = coeffs + [self.base.zero()] * (self.d - len(coeffs))
        return coeffs[: self.d]

    # -- arithmetic -----------------------------------------------------------
    def add(self, a, b): return tuple(self.base.add(x, y) for x, y in zip(a, b))
    def sub(self, a, b): return tuple(self.base.sub(x, y) for x, y in zip(a, b))
    def neg(self, a): return tuple(self.base.neg(x) for x in a)
    def mul(self, a, b): return tuple(self.reduce(_pmul(self.base, list(a), list(b))))
    def eq(self, a, b): return all(self.base.eq(x, y) for x, y in zip(a, b))
    def is_zero(self, a): return all(self.base.is_zero(x) for x in a)
    def pow(self, a, e):
        r, b = self.one(), a
        while e:
            if e & 1:
                r = self.mul(r, b)
            b = self.mul(b, b)
            e >>= 1
        return r

    def is_unit(self, a):
        if self.inverse_mode == "field":
            return not self.is_zero(a)
        if self.inverse_mode == "constant":
            return self.base.is_unit(a[0])
        F, project, _ = self.residue
        return not F.is_zero(project(a))

    def inv(self, a):
        if self.inverse_mode == "field":
            g, s, _ = _pextgcd_field(self.base, list(a), self.mod)
            if len(g) != 1:
                raise ZeroDivisionError("not a unit")
            return tuple(self.reduce(s))
        if self.inverse_mode == "constant":
            y = self.from_base(self.base.inv(a[0]))
        else:
            F, project, lift = self.residue
            y = lift(F.inv(project(a)))
        # Newton: y <- y (2 - a y); error 1 - a y has positive valuation and squares each step
        for _ in range(200):
            e = self.sub(self.one(), self.mul(a, y))
            if self.is_zero(e):
                return y
            y = self.mul(y, self.add(self.one(), e))
        raise ArithmeticError("Newton inversion did not converge")

    def elements(self):
        for tup in itertools.product(list(self.base.elements()), repeat=self.d):
            yield tuple(tup)


# ----------------------------------------------------------------------------
# Hensel / Newton root lifting with a unit derivative
# ----------------------------------------------------------------------------

def newton_root(R, coeffs: Sequence, a0, max_iter: int = 200):
    """Lift a0 to a root of the polynomial with coefficients `coeffs` (in R),
    assuming f'(a0) is a unit of R and f(a0) is topologically nilpotent.
    Returns (root, iterations).  Raises if the derivative is not a unit."""
    dcoeffs = _pderiv(R, list(coeffs))
    a = a0
    for it in range(max_iter):
        fa = _peval(R, coeffs, a)
        if R.is_zero(fa):
            return a, it
        da = _peval(R, dcoeffs, a)
        if not R.is_unit(da):
            raise ArithmeticError("derivative is not a unit at the current approximation")
        a = R.sub(a, R.mul(fa, R.inv(da)))
    raise ArithmeticError("Newton did not converge")


# ----------------------------------------------------------------------------
# Finite-field utilities
# ----------------------------------------------------------------------------

def is_prime(m: int) -> bool:
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True

def _is_irreducible_mod_p(p: int, m: List[int]) -> bool:
    """m monic over F_p, via gcd(x^{p^i} - x, m) = 1 for i <= deg/2."""
    Fp = Zmod(p)
    s = len(m) - 1
    if s == 1:
        return True
    Fq = PolyQuot(Fp, m, "field")  # used only for arithmetic mod m
    x = Fq.gen()
    xp = x
    for i in range(1, s // 2 + 1):
        xp = Fq.pow(xp, p)
        g, _, _ = _pextgcd_field(Fp, _strip(Fp, list(Fq.sub(xp, x))), m)
        if len(g) != 1:
            return False
    return True

def irreducible_poly(p: int, s: int, seed: int = 0) -> List[int]:
    """a monic irreducible of degree s over F_p (deterministic search)."""
    if s == 1:
        return [0, 1]
    rng = random.Random(seed)
    while True:
        m = [rng.randrange(p) for _ in range(s)] + [1]
        if m[0] != 0 and _is_irreducible_mod_p(p, m):
            return m

def prime_factors(n: int) -> List[int]:
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out

def primitive_root_of_unity(F: PolyQuot, order: int, field_size: int):
    """an element of exact multiplicative order `order` in the finite field F."""
    assert (field_size - 1) % order == 0
    cof = (field_size - 1) // order
    for x in F.elements():
        if F.is_zero(x):
            continue
        y = F.pow(x, cof)
        if all(not F.eq(F.pow(y, order // l), F.one()) for l in prime_factors(order)):
            return y
    raise ArithmeticError("no primitive root found")


# ----------------------------------------------------------------------------
# Certification of an element of G
# ----------------------------------------------------------------------------

def poly_from_roots(R, roots):
    poly = [R.one()]
    for r in roots:
        poly = _pmul(R, poly, [R.neg(r), R.one()])
    return poly

def certify_element(R, f_in_R: Sequence, roots: Sequence, psi: Callable, separated: Callable[[object, object], bool]):
    """Return the permutation τ with ψ(α_i) = α_{τ(i)}, after verifying:
       (i)  Π (x - α_i) == f in R        (roots are the roots of f, complete),
       (ii) ψ fixes every coefficient of the reconstructed polynomial,
       (iii) ψ permutes the root list bijectively,
       (iv) all pairs of roots are separated, so (iii) is unambiguous."""
    recon = poly_from_roots(R, roots)
    if len(recon) != len(f_in_R) or not all(R.eq(a, b) for a, b in zip(recon, f_in_R)):
        raise AssertionError("(i) reconstructed polynomial differs from f")
    for c in recon:
        if not R.eq(psi(c), c):
            raise AssertionError("(ii) ψ does not fix a coefficient of f")
    n = len(roots)
    for i in range(n):
        for j in range(i + 1, n):
            if not separated(roots[i], roots[j]):
                raise AssertionError("(iv) roots not separated at working precision")
    tau = []
    for r in roots:
        img = psi(r)
        matches = [j for j, s in enumerate(roots) if R.eq(img, s)]
        if len(matches) != 1:
            raise AssertionError("(iii) ψ(root) is not exactly one root")
        tau.append(matches[0])
    if sorted(tau) != list(range(n)):
        raise AssertionError("(iii) ψ is not a bijection on the roots")
    return tau


def cycle_type(tau: Sequence[int]) -> List[int]:
    seen, ct = set(), []
    for i in range(len(tau)):
        if i in seen:
            continue
        l, j = 0, i
        while j not in seen:
            seen.add(j); j = tau[j]; l += 1
        ct.append(l)
    return sorted(ct, reverse=True)

def group_closure(gens: List[Tuple[int, ...]], cap: int = 100000) -> int:
    """order of the permutation group generated (small groups only)."""
    n = len(gens[0])
    ident = tuple(range(n))
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                gh = tuple(h[g[i]] for i in range(n))
                if gh not in seen:
                    seen.add(gh); nxt.append(gh)
                    if len(seen) > cap:
                        raise ArithmeticError("group too large for closure")
        frontier = nxt
    return len(seen)


# ----------------------------------------------------------------------------
# Case 1:  Z,  A = (Z/p^K)[z]/(m)
# ----------------------------------------------------------------------------

def case1(f: List[int], p: int, K: int, seed: int = 0):
    """f monic integer polynomial (low->high, last coefficient 1), p ∤ disc f."""
    n = len(f) - 1
    Fp = Zmod(p)
    fbar = [c % p for c in f]
    # roots of f mod p in F_{p^s}: s = lcm of the degrees of the irreducible factors,
    # found by increasing s until n distinct roots appear.
    for s in range(1, n + 1):
        m = irreducible_poly(p, s, seed)
        F = PolyQuot(Fp, m, "field", name="z")
        fbar_F = [F.from_int(c) for c in fbar]
        rts = [x for x in F.elements() if F.is_zero(_peval(F, fbar_F, x))]
        if len(rts) == n:
            break
    else:
        raise ArithmeticError("f mod p is not squarefree or has no root in F_{p^s}, s<=n")
    # A = (Z/p^K)[z]/(m), residue map to F
    ZpK = Zmod(p ** K)
    project = lambda a: tuple(c % p for c in a)
    lift = lambda x: tuple(int(c) for c in x)
    A = PolyQuot(ZpK, [c % (p ** K) for c in m], "residue", residue=(F, project, lift), name="z")
    f_A = [A.from_int(c) for c in f]
    # check squarefreeness mod p via distinct roots (n of them) -> f'(root) unit
    roots, its = [], []
    for r in rts:
        a, it = newton_root(A, f_A, lift(r))
        roots.append(a); its.append(it)
    # Frobenius of A: φ(z) = root of m congruent to z^p
    m_A = [A.from_int(c) for c in m]
    phi_z, _ = newton_root(A, m_A, A.pow(A.gen(), p))
    def phi(a):
        return _peval(A, [A.from_base(c) for c in a], phi_z)
    separated = lambda x, y: not F.eq(project(x), project(y))   # distinct mod p suffices
    tau = certify_element(A, f_A, roots, phi, separated)
    # independent check from the residue field: ᾱ^p
    tau_res = [rts.index(F.pow(r, p)) for r in rts]
    assert tau == tau_res, "Frobenius permutation disagrees with residue computation"
    return {
        "case": 1, "p": p, "s": s, "precision": f"p^{K}", "certified_root_precision_k": K,
        "newton_iterations": its, "tau_frobenius": tau, "cycle_type": cycle_type(tau),
        "group_order_generated": group_closure([tuple(tau)]),
    }


# ----------------------------------------------------------------------------
# Case 2:  Q_p, f Eisenstein and tame;  B = A[x]/(f),  A = (Z/p^K)[z]/(m)
# ----------------------------------------------------------------------------

def case2(f: List[int], p: int, K: int, seed: int = 0, return_objects: bool = False):
    n = len(f) - 1
    assert f[-1] == 1 and all(c % p == 0 for c in f[:-1]) and f[0] % (p * p) != 0, "f must be Eisenstein at p"
    assert n % p != 0, "only the tame case (p ∤ n) is implemented"
    # s = order of p modulo n, so that μ_n ⊂ F_{p^s} ⊂ K_0 = Q_{p^s}
    s, pw = 1, p % n
    while pw != 1 % n:
        pw = (pw * p) % n; s += 1
    Fp = Zmod(p)
    m = irreducible_poly(p, s, seed)
    F = PolyQuot(Fp, m, "field", name="z")
    ZpK = Zmod(p ** K)
    project = lambda a: tuple(c % p for c in a)
    lift = lambda x: tuple(int(c) for c in x)
    A = PolyQuot(ZpK, [c % (p ** K) for c in m], "residue", residue=(F, project, lift), name="z")
    # ζ_n in A by Hensel from F
    zeta_F = primitive_root_of_unity(F, n, p ** s)
    unity = [A.from_int(-1)] + [A.zero()] * (n - 1) + [A.one()]
    zeta, _ = newton_root(A, unity, lift(zeta_F))
    # B = A[x]/(f): O_{K'} / p^K,  π'^{nK} = p^K
    f_A = [A.from_int(c) for c in f]
    B = PolyQuot(A, f_A, "constant", name="alpha")
    alpha = B.gen()
    f_B = [B.from_base(c) for c in f_A]
    # g(y) = f(α y)/α^n, computed without dividing by α:
    #   a_i = p b_i (i<n), c = b_0 unit,  p/α^n = -c^{-1} (1 + Σ_{i≥1} (b_i/c) α^i)^{-1}
    b = [c // p for c in f[:-1]]
    c0 = b[0]
    c0_inv = A.inv(A.from_int(c0))
    one_plus = B.one()
    for i in range(1, n):
        one_plus = B.add(one_plus, B.mul(B.from_base(A.mul(A.from_int(b[i]), c0_inv)), B.pow(alpha, i)))
    w = B.neg(B.mul(B.from_base(c0_inv), B.inv(one_plus)))          # = p / α^n
    g = []
    for i in range(n):
        g.append(B.mul(B.mul(B.from_int(b[i]), B.pow(alpha, i)), w))  # = a_i α^{i-n}
    g.append(B.one())
    # sanity: α^n · g(y) evaluated at y=1 must vanish, i.e. g(1)=0
    assert B.is_zero(_peval(B, g, B.one())), "g(1) != 0: construction of g failed"
    # roots y_j of g by unit-derivative Hensel from ζ^j; α_j = α y_j
    roots, its = [], []
    for j in range(n):
        y0 = B.from_base(A.pow(zeta, j))
        yj, it = newton_root(B, g, y0)
        roots.append(B.mul(alpha, yj)); its.append(it)
    for r in roots:
        assert B.is_zero(_peval(B, f_B, r)), "lifted element is not a root of f"
    # valuations
    def vp(c):
        if c == 0:
            return K
        v = 0
        while c % p == 0:
            c //= p; v += 1
        return v
    def vA(a): return min(vp(c) for c in a)
    def vB(bb): return min(n * vA(bb[i]) + i for i in range(n))   # π'-adic, capped at nK
    # inertia generator ι : α ↦ α_1 ; Frobenius lift φ̃ : coefficientwise φ, α fixed
    m_A = [A.from_int(c) for c in m]
    phi_z, _ = newton_root(A, m_A, A.pow(A.gen(), p))
    def phi_A(a): return _peval(A, [A.from_base(c) for c in a], phi_z)
    def iota(bb): return _peval(B, [B.from_base(c) for c in bb], roots[1])
    def phi_B(bb): return tuple(phi_A(c) for c in bb)
    separated = lambda x, y: vB(B.sub(x, y)) < n * K
    tau_iota = certify_element(B, f_B, roots, iota, separated)
    tau_phi = certify_element(B, f_B, roots, phi_B, separated)
    seps = sorted({vB(B.sub(roots[i], roots[j])) for i in range(n) for j in range(i + 1, n)})
    if return_objects:
        return {"A": A, "B": B, "F": F, "roots": roots, "iota": iota, "phi_B": phi_B, "tau_iota": tau_iota,
                "tau_phi": tau_phi, "vB": vB, "vA": vA, "K": K, "n": n, "p": p, "s": s}
    return {
        "case": 2, "p": p, "n": n, "s": s, "e_prime": n, "precision": f"p^{K} = pi'^{n*K}",
        "certified_root_precision_k_eff": n * K,  # no loss: lifted via g with unit derivative
        "root_separation_valuations_pi_prime": seps,
        "newton_iterations": its,
        "tau_inertia": tau_iota, "inertia_cycle_type": cycle_type(tau_iota),
        "tau_frobenius_lift": tau_phi, "frobenius_cycle_type": cycle_type(tau_phi),
        "group_order_generated": group_closure([tuple(tau_iota), tuple(tau_phi)]),
    }


# ----------------------------------------------------------------------------
# Case 3:  F_p[t],  S = F_{p^s}[[u]]/(u^K),  u = t - t0
# ----------------------------------------------------------------------------

def _shift_poly_t(p: int, a: List[int], t0: int) -> List[int]:
    """a(t) ∈ F_p[t] (low->high) as a polynomial in u = t - t0: a(t0 + u)."""
    Fp = Zmod(p)
    out = []
    for k in range(len(a)):
        # coefficient of u^k: Σ_j a_j C(j,k) t0^{j-k}
        c = 0
        for j in range(k, len(a)):
            c += a[j] * math.comb(j, k) * pow(t0, j - k, p)
        out.append(c % p)
    return out if out else [0]

def case3(f_t: List[List[int]], p: int, t0: int, K: int, seed: int = 0, return_objects: bool = False):
    """f_t: list of coefficients a_i(t) ∈ F_p[t], each a list low->high; leading a_n = [1]."""
    n = len(f_t) - 1
    assert f_t[-1] == [1], "f must be monic in x"
    Fp = Zmod(p)
    # f(t0, x) over F_p and its roots in F_{p^s}
    f0 = [_peval(Fp, a, t0 % p) for a in f_t]
    from subfields import _fpoly_strip, _roots_in_F           # lazy: avoids circular import
    import verify_roots as _vr
    if not _vr._is_squarefree(Fp, f0):
        raise ArithmeticError("f(t0,x) not squarefree")
    ddf = _vr.distinct_degree_factorization(Fp, f0, p)
    s = 1
    for d_, _cnt in ddf:
        s = s * d_ // math.gcd(s, d_)
    m = irreducible_poly(p, s, seed)
    F = PolyQuot(Fp, m, "field", name="z")
    f0_F = [F.from_int(c) for c in f0]
    q_ = p ** s
    if q_ <= 20000:
        rts = [x for x in F.elements() if F.is_zero(_peval(F, f0_F, x))]
    else:
        if p % 2 == 0:
            raise ArithmeticError("root finding in a large field of characteristic 2 not implemented (needs trace splitting)")
        rts = sorted(_roots_in_F(F, f0_F, q_, random.Random(seed + 1)))
    if len(rts) != n:
        raise ArithmeticError("could not split f(t0,x) in F_{p^s}")
    # S = F_{p^s}[[u]]/u^K
    S = PolyQuot(F, [F.zero()] * K + [F.one()], "constant", name="u")
    f_S = []
    for a in f_t:
        au = _shift_poly_t(p, a, t0)
        f_S.append(S.from_list([F.from_int(c) for c in au]))
    roots, its = [], []
    for r in rts:
        a, it = newton_root(S, f_S, S.from_base(r))
        roots.append(a); its.append(it)
    # Frobenius: coefficientwise c ↦ c^p on F_{p^s}
    def phi(ser): return tuple(F.pow(c, p) for c in ser)
    separated = lambda x, y: not F.eq(x[0], y[0])     # distinct mod u suffices
    tau = certify_element(S, f_S, roots, phi, separated)
    tau_res = [rts.index(F.pow(r, p)) for r in rts]
    assert tau == tau_res
    if return_objects:
        return {"S": S, "F": F, "roots": roots, "phi": phi, "tau": tau, "K": K, "p": p, "s": s, "t0": t0, "m": m}
    return {
        "case": 3, "p": p, "t0": t0, "s": s, "precision": f"u^{K}", "certified_root_precision_k": K,
        "newton_iterations": its, "tau_frobenius": tau, "cycle_type": cycle_type(tau),
        "group_order_generated": group_closure([tuple(tau)]),
    }


# ----------------------------------------------------------------------------
if __name__ == "__main__":
    out = {}
    # case 1: x^3 - 2 at p = 7 (irreducible mod 7 -> 3-cycle); x^4 + 1 at p = 3 (two 2-cycles)
    out["case1_x3-2_p7"] = case1([-2, 0, 0, 1], p=7, K=40)
    out["case1_x4+1_p3"] = case1([1, 0, 0, 0, 1], p=3, K=40)
    # case 2 (Eisenstein, tame): x^3 - 5 over Q_5 (S_3); x^3 + 5x + 5 over Q_5 (non-binomial, S_3);
    #                            x^4 - 3 over Q_3 (D_4, order 8); x^2 - 3 over Q_3 (C_2)
    out["case2_x3-5_Q5"] = case2([-5, 0, 0, 1], p=5, K=12)
    out["case2_x3+5x+5_Q5"] = case2([5, 5, 0, 1], p=5, K=12)
    out["case2_x4-3_Q3"] = case2([-3, 0, 0, 0, 1], p=3, K=12)
    out["case2_x2-3_Q3"] = case2([-3, 0, 1], p=3, K=12)
    # case 3: x^3 + t x + 1 over F_5 at t0 = 1 (irreducible -> 3-cycle); x^2 - t at t0 = 2 (2 non-square mod 5)
    out["case3_x3+tx+1_F5_t0=1"] = case3([[1], [0, 1], [0], [1]], p=5, t0=1, K=30)
    out["case3_x2-t_F5_t0=2"] = case3([[0, -1], [0], [1]], p=5, t0=2, K=30)
    # negative test: a map that is not an automorphism must be rejected by certify_element
    Fp = Zmod(7); m = irreducible_poly(7, 3); F = PolyQuot(Fp, m, "field")
    A = PolyQuot(Zmod(7 ** 10), m, "residue", residue=(F, lambda a: tuple(c % 7 for c in a), lambda x: tuple(x)))
    fA = [A.from_int(c) for c in [-2, 0, 0, 1]]
    rts = [x for x in F.elements() if F.is_zero(_peval(F, [F.from_int(c % 7) for c in [-2, 0, 0, 1]], x))]
    roots = [newton_root(A, fA, tuple(r))[0] for r in rts]
    try:
        certify_element(A, fA, roots, lambda a: A.add(a, A.one()), lambda x, y: True)
        out["negative_test"] = "FAILED: non-automorphism accepted"
    except AssertionError as e:
        out["negative_test"] = f"rejected as expected: {e}"
    print(json.dumps(out, indent=2))