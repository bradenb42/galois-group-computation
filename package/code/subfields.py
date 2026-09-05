"""
subfields.py — the subfield lattice and starting group over Z, on top of
hensel_frobenius.py.

Pipeline for an irreducible monic f ∈ Z[x] of degree n:

  1. choose a prime p with f̄ squarefree *and* having a root in F_p (degree-one
     embedding, choice of a degree-one prime); Hensel-lift all roots into A = (Z/p^K)[z]/(m); compute the
     Frobenius φ of A and its permutation τ (certified Frobenius and inertia elements), relabelled so that τ(0)=0 and
     α_0 ∈ Z_p, whence K_f = Q(α_0) ⊂ Q_p is fixed pointwise by φ;
  2. factor f over K_f: the root set of each factor is a union of τ-cycles; for a
     candidate union S the coefficients of g_S = Π_{m∈S}(y - α_m) are recognized
     as elements of K_f from the single embedding by a closest-vector computation
     in the coset of the kernel lattice Λ_0(a) (Lemma 6.3 + LLL/Babai), and the
     candidate is accepted only after the *exact* test g_S | f in K_f[y];
  3. principal subfields L_i = ker(g ↦ (g(y) - g(α)) mod f_i) by exact linear
     algebra (Lemma 6.1), lattice by intersection closure (Theorem 6.2);
  4. for each subfield: an integral primitive element, its minimal polynomial h,
     the block system by grouping b(α̂_j) in A at precision K > v_p(disc h)/2
     (Lemma 6.4), and the starting group W = ∩ Stab(B_L) (here by brute force
     over S_n for small n, plus the chain wreath product and the type bound of
     block systems from subfields with all n points);
  5. verification: φ fixes every subfield pointwise (under the embedding at α_0)
     and acts equivariantly on the conjugate embeddings; τ preserves every block
     system; τ ∈ W and τ ∈ the chain wreath product.

All exact arithmetic uses Fractions; all p-adic arithmetic is the truncated
ring A of hensel_frobenius.py.
"""

from __future__ import annotations

import itertools
import json
import math
import random
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from hensel_frobenius import (PolyQuot, Zmod, _peval, _pmul, _strip, _pextgcd_field, _pderiv,
                              irreducible_poly, is_prime, newton_root, poly_from_roots, cycle_type)


# ----------------------------------------------------------------------------
# exact helpers over Q
# ----------------------------------------------------------------------------

def det_fraction(M: List[List[Fraction]]) -> Fraction:
    M = [row[:] for row in M]
    n = len(M)
    det = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
            det = -det
        det *= M[i][i]
        inv = 1 / M[i][i]
        for r in range(i + 1, n):
            if M[r][i] != 0:
                fac = M[r][i] * inv
                for c in range(i, n):
                    M[r][c] -= fac * M[i][c]
    return det

def resultant(a: List[Fraction], b: List[Fraction]) -> Fraction:
    """Sylvester resultant, polynomials low->high."""
    a = [Fraction(x) for x in a]; b = [Fraction(x) for x in b]
    da, db = len(a) - 1, len(b) - 1
    N = da + db
    M = []
    for i in range(db):
        row = [Fraction(0)] * N
        for j, c in enumerate(reversed(a)):
            row[i + j] = c
        M.append(row)
    for i in range(da):
        row = [Fraction(0)] * N
        for j, c in enumerate(reversed(b)):
            row[i + j] = c
        M.append(row)
    return det_fraction(M)

def discriminant(h: List[Fraction]) -> Fraction:
    d = len(h) - 1
    dh = [i * h[i] for i in range(1, len(h))]
    lc = Fraction(h[-1])
    sign = -1 if (d * (d - 1) // 2) % 2 else 1
    return sign * resultant(h, dh) / lc

def rref(rows: List[List[Fraction]]) -> List[List[Fraction]]:
    M = [[Fraction(x) for x in r] for r in rows]
    if not M:
        return []
    ncols = len(M[0]); r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                fac = M[i][c]
                M[i] = [x - fac * y for x, y in zip(M[i], M[r])]
        r += 1
        if r == len(M):
            break
    return [row for row in M if any(x != 0 for x in row)]

def nullspace(rows: List[List[Fraction]], ncols: int) -> List[List[Fraction]]:
    R = rref(rows) if rows else []
    pivots = []
    for row in R:
        pivots.append(next(c for c in range(ncols) if row[c] != 0))
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncols
        v[fc] = Fraction(1)
        for row, pc in zip(R, pivots):
            v[pc] = -row[fc]
        basis.append(v)
    return basis

def intersect_subspaces(U: List[List[Fraction]], V: List[List[Fraction]], ncols: int) -> List[List[Fraction]]:
    """basis of span(U) ∩ span(V)."""
    if not U or not V:
        return []
    # find (x, y) with x U - y V = 0  <=>  [U^T | -V^T] (x;y)^T = 0
    rows = []
    for c in range(ncols):
        rows.append([u[c] for u in U] + [-v[c] for v in V])
    ns = nullspace(rows, len(U) + len(V))
    out = []
    for vec in ns:
        x = vec[: len(U)]
        out.append([sum(x[i] * U[i][c] for i in range(len(U))) for c in range(ncols)])
    return rref(out)

def lll(basis: List[List[int]], delta=Fraction(3, 4)) -> List[List[int]]:
    B = [[Fraction(x) for x in row] for row in basis]
    n = len(B)
    def gso(B):
        Bs, mu = [], [[Fraction(0)] * n for _ in range(n)]
        for i in range(n):
            v = B[i][:]
            for j in range(i):
                mu[i][j] = sum(B[i][k] * Bs[j][k] for k in range(len(v))) / sum(x * x for x in Bs[j])
                v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
            Bs.append(v)
        return Bs, mu
    Bs, mu = gso(B)
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [a - q * b for a, b in zip(B[k], B[j])]
                Bs, mu = gso(B)
        nk = sum(x * x for x in Bs[k]); nk1 = sum(x * x for x in Bs[k - 1])
        if nk >= (delta - mu[k][k - 1] ** 2) * nk1:
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bs, mu = gso(B)
            k = max(k - 1, 1)
    return [[int(x) for x in row] for row in B]

def babai_closest(basis: List[List[int]], target: List[int]) -> List[int]:
    B = [[Fraction(x) for x in row] for row in basis]
    n = len(B)
    Bs = []
    for i in range(n):
        v = B[i][:]
        for j in range(i):
            m = sum(B[i][k] * Bs[j][k] for k in range(len(v))) / sum(x * x for x in Bs[j])
            v = [a - m * b for a, b in zip(v, Bs[j])]
        Bs.append(v)
    t = [Fraction(x) for x in target]
    v = [Fraction(0)] * len(t)
    for i in range(n - 1, -1, -1):
        c = round(sum(t[k] * Bs[i][k] for k in range(len(t))) / sum(x * x for x in Bs[i]))
        t = [a - c * b for a, b in zip(t, B[i])]
        v = [a + c * b for a, b in zip(v, B[i])]
    return [int(x) for x in v]


# ----------------------------------------------------------------------------
# exact arithmetic in K_f = Q[x]/(f)
# ----------------------------------------------------------------------------

class Kf:
    def __init__(self, f: List[int]):
        self.f = [Fraction(c) for c in f]
        self.n = len(f) - 1
    def zero(self): return [Fraction(0)] * self.n
    def one(self): return [Fraction(1)] + [Fraction(0)] * (self.n - 1)
    def from_vec(self, v): return [Fraction(x) for x in v]
    def add(self, a, b): return [x + y for x, y in zip(a, b)]
    def sub(self, a, b): return [x - y for x, y in zip(a, b)]
    def neg(self, a): return [-x for x in a]
    def scal(self, a, c): return [x * c for x in a]
    def is_zero(self, a): return all(x == 0 for x in a)
    def eq(self, a, b): return all(x == y for x, y in zip(a, b))
    def mul(self, a, b):
        prod = [Fraction(0)] * (2 * self.n - 1)
        for i, x in enumerate(a):
            if x == 0: continue
            for j, y in enumerate(b):
                prod[i + j] += x * y
        for i in range(len(prod) - 1, self.n - 1, -1):
            c = prod[i]
            if c == 0: continue
            for j in range(self.n + 1):
                prod[i - self.n + j] -= c * self.f[j]
        return prod[: self.n]
    def pow(self, a, e):
        r = self.one()
        for _ in range(e):
            r = self.mul(r, a)
        return r
    def inv(self, a):
        # solve a * x = 1 by linear algebra on the multiplication matrix
        cols = [self.mul(a, [Fraction(int(i == k)) for i in range(self.n)]) for k in range(self.n)]
        rows = [[cols[k][i] for k in range(self.n)] + [Fraction(int(i == 0))] for i in range(self.n)]
        R = rref(rows)
        x = [Fraction(0)] * self.n
        for row in R:
            pc = next(c for c in range(self.n) if row[c] != 0)
            x[pc] = row[self.n]
        assert self.eq(self.mul(a, x), self.one())
        return x

def kpoly_mod(K: Kf, a: List[List[Fraction]], b: List[List[Fraction]]) -> List[List[Fraction]]:
    """a mod b in K_f[y], b monic (lists of K_f elements, low->high)."""
    a = [x[:] for x in a]
    db = len(b) - 1
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if K.is_zero(c): continue
        for j in range(db + 1):
            a[i - db + j] = K.sub(a[i - db + j], K.mul(c, b[j]))
    r = a[:db]
    return r

def kpoly_mul(K: Kf, a, b):
    out = [K.zero() for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = K.add(out[i + j], K.mul(x, y))
    return out


# ----------------------------------------------------------------------------
# step 1: degree-one prime, roots, Frobenius
# ----------------------------------------------------------------------------

def choose_prime(f: List[int], start: int = 3) -> int:
    """smallest p >= start with f̄ squarefree and having a root in F_p."""
    n = len(f) - 1
    p = start
    while True:
        if is_prime(p):
            Fp = Zmod(p)
            fb = [c % p for c in f]
            rts = [x for x in range(p) if _peval(Fp, fb, x) == 0]
            # squarefree mod p: gcd(f̄, f̄') = 1
            g, _, _ = _pextgcd_field(Fp, _strip(Fp, fb), _strip(Fp, _pderiv(Fp, fb)))
            if rts and len(g) == 1:
                return p
        p += 1

def _fpoly_strip(F, a):
    a = list(a)
    while a and F.is_zero(a[-1]):
        a.pop()
    return a

def _fpoly_divmod(F, a, b):
    a = _fpoly_strip(F, a); b = _fpoly_strip(F, b)
    inv = F.inv(b[-1])
    q = [F.zero()] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        c = F.mul(a[-1], inv); k = len(a) - len(b); q[k] = c
        for j in range(len(b)):
            a[k + j] = F.sub(a[k + j], F.mul(c, b[j]))
        a = _fpoly_strip(F, a)
    return q, a

def _fpoly_gcd(F, a, b):
    a, b = _fpoly_strip(F, a), _fpoly_strip(F, b)
    while b:
        a, b = b, _fpoly_divmod(F, a, b)[1]
    if a:
        inv = F.inv(a[-1]); a = [F.mul(c, inv) for c in a]
    return a

def _fpoly_powmod(F, base, e, m):
    r = [F.one()]
    base = _fpoly_divmod(F, base, m)[1]
    while e:
        if e & 1:
            r = _fpoly_divmod(F, _pmul(F, r, base), m)[1]
        base = _fpoly_divmod(F, _pmul(F, base, base), m)[1]
        e >>= 1
    return r

def _roots_in_F(F, poly, q: int, rng) -> list:
    """all roots in F (odd finite field of size q) of a squarefree polynomial
    splitting completely over F: Cantor-Zassenhaus splitting with random
    elements of the full field (elements of the prime field cannot separate
    conjugate roots)."""
    poly = _fpoly_strip(F, poly)
    if len(poly) == 1:
        return []
    if len(poly) == 2:
        return [F.neg(F.mul(poly[0], F.inv(poly[1])))]
    one = F.one()
    for _attempt in range(400):
        a = F.from_list([F.base.from_int(rng.randrange(F.base.N)) for _ in range(F.d)])
        t = _fpoly_powmod(F, [a, one], (q - 1) // 2, poly)          # (x + a)^{(q-1)/2} mod poly
        t = list(t) + [F.zero()] * (1 - len(t))
        t[0] = F.sub(t[0], one)
        g = _fpoly_gcd(F, _fpoly_strip(F, t), poly)
        if 0 < len(g) - 1 < len(poly) - 1:
            h, r = _fpoly_divmod(F, poly, g)
            assert not r
            return _roots_in_F(F, g, q, rng) + _roots_in_F(F, h, q, rng)
    raise ArithmeticError("Cantor-Zassenhaus did not split: input polynomial does not split over F?")

def roots_and_frobenius(f: List[int], p: int, K: int, seed: int = 0):
    n = len(f) - 1
    assert p % 2 == 1, "odd p required (Cantor-Zassenhaus splitting)"
    Fp = Zmod(p)
    fbar = [c % p for c in f]
    # residue degree s = lcm of the irreducible factor degrees (distinct-degree factorization)
    import verify_roots as _vr
    ddf = _vr.distinct_degree_factorization(Fp, fbar, p)
    s = 1
    for d, _cnt in ddf:
        s = s * d // math.gcd(s, d)
    m = irreducible_poly(p, s, seed)
    F = PolyQuot(Fp, m, "field")
    fbar_F = [F.from_int(c) for c in fbar]
    q = p ** s
    if q <= 20000:                                            # tiny field: enumeration
        rts = [x for x in F.elements() if F.is_zero(_peval(F, fbar_F, x))]
    else:
        rts = sorted(_roots_in_F(F, fbar_F, q, random.Random(seed + 1)))
    if len(rts) != n:
        raise ArithmeticError("could not split f mod p in F_{p^s}")
    ZpK = Zmod(p ** K)
    project = lambda a: tuple(c % p for c in a)
    lift = lambda x: tuple(int(c) for c in x)
    A = PolyQuot(ZpK, [c % (p ** K) for c in m], "residue", residue=(F, project, lift))
    f_A = [A.from_int(c) for c in f]
    roots = [newton_root(A, f_A, lift(r))[0] for r in rts]
    # put a Z_p-root first (degree-one embedding)
    zp_idx = [i for i, r in enumerate(roots) if all(A.base.is_zero(c) for c in r[1:])]
    assert zp_idx, "no root in Z_p although f has a root mod p"
    i0 = zp_idx[0]
    roots = [roots[i0]] + roots[:i0] + roots[i0 + 1:]
    m_A = [A.from_int(c) for c in m]
    phi_z, _ = newton_root(A, m_A, A.pow(A.gen(), p))
    def phi(a): return _peval(A, [A.from_base(c) for c in a], phi_z)
    tau = []
    for r in roots:
        img = phi(r)
        j = [k for k, s_ in enumerate(roots) if A.eq(img, s_)]
        assert len(j) == 1
        tau.append(j[0])
    assert tau[0] == 0
    return A, F, project, roots, phi, tau, s


# ----------------------------------------------------------------------------
# step 2: recognition in K_f and factorization over K_f
# ----------------------------------------------------------------------------

class KfRecognizer:
    """Recognition of elements of K_f ⊂ Q_p from the single embedding α ↦ α_0
    (Lemma 6.3): the kernel lattice Λ_0 = {c ∈ Z^n : c(α_0) ≡ 0 mod p^K} is
    LLL-reduced once; each value is then a single Babai closest-vector step."""

    def __init__(self, A: PolyQuot, alpha0, D: int, p: int, K: int, n: int):
        self.A, self.D, self.N, self.n = A, D, p ** K, n
        a0 = alpha0[0] % self.N
        basis = [[self.N] + [0] * (n - 1)]
        pw = 1
        for k in range(1, n):
            pw = (pw * a0) % self.N
            row = [0] * n
            row[0] = (-pw) % self.N
            row[k] = 1
            basis.append(row)
        self.reduced = lll(basis)

    def recognize(self, gamma):
        """coefficient vector of γ in the power basis, or None if γ ∉ Z_p (image check)."""
        if not all(self.A.base.is_zero(c) for c in gamma[1:]):
            return None
        target = [(gamma[0] * self.D) % self.N] + [0] * (self.n - 1)
        v = babai_closest(self.reduced, target)
        return [Fraction(t - w, self.D) for t, w in zip(target, v)]


def recognize_in_Kf(A: PolyQuot, gamma, alpha0, D: int, p: int, K: int, n: int):
    return KfRecognizer(A, alpha0, D, p, K, n).recognize(gamma)


def factor_over_Kf(f: List[int], A: PolyQuot, roots, tau, p: int, K: int):
    n = len(f) - 1
    Kfield = Kf(f)
    D = abs(int(discriminant([Fraction(c) for c in f])))
    # τ-cycles
    seen, cycles = set(), []
    for i in range(n):
        if i in seen: continue
        cyc, j = [], i
        while j not in seen:
            seen.add(j); cyc.append(j); j = tau[j]
        cycles.append(cyc)
    f_K = [[Fraction(c)] + [Fraction(0)] * (n - 1) for c in f]
    rec = KfRecognizer(A, roots[0], D, p, K, n)
    factors: List[Dict] = []
    covered = set()
    for j in range(n):
        if j in covered: continue
        cj = next(c for c in cycles if j in c)
        others = [c for c in cycles if c is not cj]
        found = None
        for size in range(0, len(others) + 1):
            for combo in itertools.combinations(others, size):
                S = sorted(cj + [x for c in combo for x in c])
                gS_A = poly_from_roots(A, [roots[i] for i in S])
                coeffs = []
                ok = True
                for gamma in gS_A[:-1]:
                    vec = rec.recognize(gamma)
                    if vec is None:
                        ok = False; break
                    coeffs.append(Kfield.from_vec(vec))
                if not ok: continue
                coeffs.append(Kfield.one())
                if all(Kfield.is_zero(c) for c in kpoly_mod(Kfield, f_K, coeffs)):
                    found = (S, coeffs); break
            if found: break
        assert found is not None, "no K_f-factor found containing root %d" % j
        S, coeffs = found
        # Soundness of the labelling: the exact g_S is ≡ Π_{m∈S}(y - α̂_m) mod p^K and is
        # squarefree mod p, so its roots in O_q are exactly the α_m, m ∈ S (Hensel uniqueness).
        covered |= set(S)
        factors.append({"support": S, "coeffs": coeffs})
    # consistency: product of factors equals f in K_f[y]
    prod = [Kfield.one()]
    for fac in factors:
        prod = kpoly_mul(Kfield, prod, fac["coeffs"])
    assert len(prod) == n + 1 and all(Kfield.eq(a, b) for a, b in zip(prod, f_K))
    return Kfield, factors


# ----------------------------------------------------------------------------
# step 3: principal subfields and the lattice
# ----------------------------------------------------------------------------

def principal_subfield(Kfield: Kf, fi: List[List[Fraction]]) -> List[List[Fraction]]:
    """L_i = { g(α) : f_i | g(y) - g(α) }, as an rref basis of a subspace of Q^n
    (coefficients in the power basis).  For each k the remainder of y^k - α^k
    modulo f_i is a vector in K_f[y]_{<d} ≅ Q^{n d}; the condition is linear in g."""
    n = Kfield.n
    d = len(fi) - 1
    alpha = Kfield.from_vec([0, 1] + [0] * (n - 2))
    yk = [Kfield.one()]                         # y^k reduced mod f_i, as a list of K_f elements
    cols = []
    for k in range(n):
        rem = yk + [Kfield.zero()] * (d - len(yk))   # pad to length d
        rem = [x[:] for x in rem]
        rem[0] = Kfield.sub(rem[0], Kfield.pow(alpha, k))
        cols.append([x for coeff in rem for x in coeff])
        yk = kpoly_mod(Kfield, [Kfield.zero()] + yk, fi) if len(yk) + 1 > d else [Kfield.zero()] + yk
    rows = [[cols[k][i] for k in range(n)] for i in range(n * d)]
    return rref(nullspace(rows, n))


def subfield_lattice(Kfield: Kf, principal: List[List[List[Fraction]]]) -> List[List[List[Fraction]]]:
    n = Kfield.n
    key = lambda B: tuple(tuple(x for x in row) for row in B)
    lat = {key(B): B for B in principal}
    changed = True
    while changed:
        changed = False
        items = list(lat.values())
        for U in items:
            for V in items:
                W = intersect_subspaces(U, V, n)
                if W and key(W) not in lat:
                    lat[key(W)] = W; changed = True
    return sorted(lat.values(), key=lambda B: -len(B))


# ----------------------------------------------------------------------------
# step 4: primitive elements, block systems, starting group
# ----------------------------------------------------------------------------

def integral_basis_vectors(B: List[List[Fraction]]) -> List[List[int]]:
    out = []
    for row in B:
        l = 1
        for x in row:
            l = l * x.denominator // math.gcd(l, x.denominator)
        out.append([int(x * l) for x in row])
    return out

def minimal_polynomial(Kfield: Kf, beta) -> List[Fraction]:
    n = Kfield.n
    pows = [Kfield.one()]
    for k in range(1, n + 1):
        pows.append(Kfield.mul(pows[-1], beta))
        rows = [[pows[i][c] for i in range(k + 1)] for c in range(n)]
        ns = nullspace(rows, k + 1)
        if ns:
            v = ns[0]
            v = [x / v[k] for x in v]
            return v
    raise ArithmeticError

def block_system(A: PolyQuot, roots, b_int: List[int], K: int, p: int, h: List[Fraction]):
    """partition of root indices by b(α̂_j), certified by K > v_p(disc h)/2."""
    disc = discriminant(h)
    assert disc.denominator == 1 and disc != 0
    dval, v = int(disc), 0
    while dval % p == 0:
        dval //= p; v += 1
    assert K > v / 2, "precision insufficient for Lemma 6.4"
    vals = [_peval(A, [A.from_int(c) for c in b_int], r) for r in roots]
    classes: List[List[int]] = []
    for j, val in enumerate(vals):
        for cl in classes:
            if A.eq(vals[cl[0]], val):
                cl.append(j); break
        else:
            classes.append([j])
    return classes, v

def perm_preserves(perm: Sequence[int], blocks: List[List[int]]) -> bool:
    bset = {frozenset(b) for b in blocks}
    return all(frozenset(perm[i] for i in b) in bset for b in blocks)

def starting_group_bruteforce(n: int, systems: List[List[List[int]]]) -> List[Tuple[int, ...]]:
    return [perm for perm in itertools.permutations(range(n)) if all(perm_preserves(perm, B) for B in systems)]

def maximal_chain(n: int, systems: List[List[List[int]]]) -> List[List[List[int]]]:
    """a maximal chain of block systems under refinement, from points to Ω."""
    def refines(B1, B2):  # B1 finer than B2
        return all(any(set(b1) <= set(b2) for b2 in B2) for b1 in B1)
    allsys = [[[i] for i in range(n)]] + [B for B in systems if 1 < len(B) < n] + [[list(range(n))]]
    # remove duplicates
    uniq = []
    for B in allsys:
        if not any({frozenset(b) for b in B} == {frozenset(b) for b in C} for C in uniq):
            uniq.append(B)
    chain = [uniq[0]]
    while len(chain[-1]) > 1:
        cands = [B for B in uniq if len(B) < len(chain[-1]) and refines(chain[-1], B)]
        nxt = max(cands, key=lambda B: len(B))   # finest coarser system
        chain.append(nxt)
    return chain

def chain_wreath_order(chain) -> int:
    n = len(chain[0]); order = 1; prev = n
    # chain[i] has n/(m_1...m_i) blocks; m_i = (#blocks of chain[i-1]) / (#blocks of chain[i])
    for i in range(1, len(chain)):
        m = len(chain[i - 1]) // len(chain[i])
        order *= math.factorial(m) ** len(chain[i])
    return order

def type_bound(n: int, systems: List[List[List[int]]]) -> int:
    """Π_{i=1}^{n} |T_i| with types relative to all previous points (block systems from subfields)."""
    allsys = [[[i] for i in range(n)]] + systems
    def finest_common(x, y):
        best = None
        for idx, B in enumerate(allsys):
            if any(x in b and y in b for b in B):
                if best is None or len(B) > len(allsys[best]):
                    best = idx
        return best
    bound = 1
    for i in range(n):
        ty = tuple(finest_common(i, s) for s in range(i))
        T = [y for y in range(i, n) if tuple(finest_common(y, s) for s in range(i)) == ty]
        bound *= len(T)
    return bound


# ----------------------------------------------------------------------------
# driver
# ----------------------------------------------------------------------------

def run_A6(f: List[int], K: int = 120, p: int | None = None, max_precision_doublings: int = 3):
    n = len(f) - 1
    p = p or choose_prime(f)
    for attempt in range(max_precision_doublings + 1):
        A, F, project, roots, phi, tau, s = roots_and_frobenius(f, p, K)
        try:
            Kfield, factors = factor_over_Kf(f, A, roots, tau, p, K)
            break
        except AssertionError:
            if attempt == max_precision_doublings:
                raise
            K *= 2               # recognition precision insufficient (large disc f): retry; labelling is K-independent
    principal = [principal_subfield(Kfield, fac["coeffs"]) for fac in factors]
    lattice = subfield_lattice(Kfield, principal)
    report = {"f": f, "n": n, "p": p, "s": s, "precision": f"p^{K}", "tau": tau, "tau_cycle_type": cycle_type(tau),
              "factor_supports": [fac["support"] for fac in factors],
              "factor_degrees": [len(fac["support"]) for fac in factors], "subfields": []}
    systems = []
    rng = random.Random(1)
    for B in lattice:
        d = len(B)
        Bint = integral_basis_vectors(B)
        # integral primitive element
        for _ in range(50):
            coeffs = [rng.randint(-3, 3) for _ in Bint]
            b_int = [sum(c * row[k] for c, row in zip(coeffs, Bint)) for k in range(n)]
            beta = Kfield.from_vec(b_int)
            h = minimal_polynomial(Kfield, beta)
            if len(h) - 1 == d:
                break
        else:
            raise ArithmeticError("no primitive element found")
        assert all(x.denominator == 1 for x in h), "primitive element must be integral"
        blocks, vdisc = block_system(A, roots, b_int, K, p, h)
        assert len(blocks) == d and all(len(bl) == n // d for bl in blocks), "block sizes inconsistent"
        # --- verification against the Frobenius ---
        # (a) φ fixes the subfield pointwise under the embedding at α_0 (τ(0)=0)
        for row in Bint:
            val0 = _peval(A, [A.from_int(c) for c in row], roots[0])
            assert A.eq(phi(val0), val0), "Frobenius does not fix a subfield element"
            # (b) equivariance on all conjugate embeddings
            vals = [_peval(A, [A.from_int(c) for c in row], r) for r in roots]
            assert all(A.eq(phi(vals[j]), vals[tau[j]]) for j in range(n)), "Frobenius not equivariant"
        # (c) τ preserves the block system
        assert perm_preserves(tau, blocks), "Frobenius does not preserve the block system"
        systems.append(blocks)
        report["subfields"].append({"degree_over_Q": d, "primitive_element": b_int, "min_poly": [int(x) for x in h],
                                    "blocks": blocks, "v_p(disc h)": vdisc,
                                    "frobenius_fixes_pointwise": True, "frobenius_preserves_blocks": True})
    proper = [B for B in systems if 1 < len(B) < n]
    W = starting_group_bruteforce(n, proper) if n <= 8 else None
    chain = maximal_chain(n, proper)
    report["starting_group"] = {
        "num_proper_block_systems": len(proper),
        "W_order_bruteforce": len(W) if W is not None else None,
        "chain_block_counts": [len(B) for B in chain],
        "chain_wreath_order": chain_wreath_order(chain),
        "type_bound": type_bound(n, proper),
        "tau_in_W": (tuple(tau) in set(W)) if W is not None else None,
        "tau_in_chain_wreath": all(perm_preserves(tau, B) for B in chain),
    }
    assert report["starting_group"]["tau_in_chain_wreath"]
    if W is not None:
        assert report["starting_group"]["tau_in_W"]
    return report


if __name__ == "__main__":
    out = {}
    out["x4+1"] = run_A6([1, 0, 0, 0, 1])                       # V_4: three quadratic subfields, W = V_4
    out["x4-2"] = run_A6([-2, 0, 0, 0, 1])                      # D_4: one quadratic subfield, W = D_4
    out["x6+2x4+x2-2"] = run_A6([-2, 0, 1, 0, 2, 0, 1])         # (x^3+x)^2 - 2: cubic and quadratic subfields, W = S_3 x S_2
    out["x5-2"] = run_A6([-2, 0, 0, 0, 0, 1])                   # no proper subfields, W = S_5
    print(json.dumps(out, indent=2, default=str))