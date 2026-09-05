#!/usr/bin/env python3
"""
checker.py — the independent certificate checker (case 1, coefficient ring Z).

    python3 checker.py certificate.json [-v]        exit 0 = ACCEPT, 1 = REJECT

This program shares NO code with the prover except permgroup.py (the
permutation-group library). Everything else — arithmetic in O_q / p^K,
Frobenius from the residue field, exact linear algebra over Q, resolvent
recovery, integer-root search — is implemented here from scratch, so an error
in the prover's routines cannot be mirrored by the checker.

Checks (the checker conditions C0-C6), each named in the rejection message:
  C0  p prime; f squarefree mod p; m irreducible of degree s over F_p; the n
      supplied roots satisfy f(α̂) ≡ 0 mod p^K and are distinct mod p; α̂_0 ∈ Z_p;
      Frobenius τ read off the residue field is a permutation.
  C1  for every subfield record (b, h, blocks): h(b(α)) = 0 exactly in Q[x]/(f),
      deg h = #blocks, 1..b^{d-1} independent (h minimal), disc h ≠ 0,
      K > v_p(disc h)/2, blocks recomputed from b(α̂_j) agree; U_0 preserves all
      block systems, |U_0| equals the type bound with all n points, τ ∈ U_0.
  C2  Stab_{U_i}(F_i) = σ_i^{-1} U_{i+1} σ_i by orbit counting over Z, mod 2, mod 3.
  C3  σ_i F_i(T_i(α̂)) ≡ v_i mod p^{k_i}.
  C4  k_i ≥ k_prf recomputed from F_i, f, T_i; k_i ≤ K.
  C5  R_i recovered exactly from the U_i-orbit of F_i at precision k_i and equal
      to the supplied one; R_i(v_i) = 0 and R_i'(v_i) ≠ 0 exactly; v_p(R_i'(v_i)) < k_i.
  C6  every class of maximal subgroups of U_ell (the checker's own list) is
      covered by a terminal record, re-verified: dismissal ⇒ τ in no conjugate;
      negative ⇒ stabilizer verified, resolvent recovered, no integer root
      (linear-factor lifting of the squarefree part at an auxiliary prime).
"""

from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

import permgroup as pg


class Reject(Exception):
    pass

def need(cond: bool, msg: str):
    if not cond:
        raise Reject(msg)


# ----------------------------------------------------------------------------
# small-integer and modular helpers (own implementation)
# ----------------------------------------------------------------------------

def is_prime(n: int) -> bool:
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0: return False
        d += 2
    return True

def vp(x: int, p: int) -> int:
    if x == 0: return 10 ** 9
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

def poly_eval_int(poly: Sequence[int], x: int) -> int:
    acc = 0
    for c in reversed(poly):
        acc = acc * x + c
    return acc

# polynomials over F_p: lists low->high of ints mod p
def fp_strip(a, p):
    a = [c % p for c in a]
    while a and a[-1] == 0: a.pop()
    return a

def fp_mul(a, b, p):
    if not a or not b: return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return fp_strip(out, p)

def fp_divmod(a, b, p):
    a = fp_strip(a, p); b = fp_strip(b, p)
    inv = pow(b[-1], -1, p)
    q = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        c = (a[-1] * inv) % p; k = len(a) - len(b); q[k] = c
        for j in range(len(b)):
            a[k + j] = (a[k + j] - c * b[j]) % p
        a = fp_strip(a, p)
    return q, a

def fp_gcd(a, b, p):
    a, b = fp_strip(a, p), fp_strip(b, p)
    while b:
        a, b = b, fp_divmod(a, b, p)[1]
    if a:
        inv = pow(a[-1], -1, p); a = [(c * inv) % p for c in a]
    return a

def fp_deriv(a, p):
    return fp_strip([(i * a[i]) % p for i in range(1, len(a))], p)

def fp_powmod(base, e, m, p):
    r = [1]; base = fp_divmod(base, m, p)[1]
    while e:
        if e & 1: r = fp_divmod(fp_mul(r, base, p), m, p)[1]
        base = fp_divmod(fp_mul(base, base, p), m, p)[1]; e >>= 1
    return r

def fp_irreducible(m, p) -> bool:
    """m monic over F_p irreducible iff gcd(x^{p^i} - x, m) = 1 for i <= deg m / 2."""
    m = fp_strip(m, p); d = len(m) - 1
    if d < 1: return False
    h = [0, 1]
    for i in range(1, d // 2 + 1):
        h = fp_powmod(h, p, m, p)
        g = fp_gcd(fp_strip([(h[k] if k < len(h) else 0) - (1 if k == 1 else 0) for k in range(max(len(h), 2))], p), m, p)
        if len(g) > 1: return False
    return True

def fp_squarefree(a, p) -> bool:
    return len(fp_gcd(a, fp_deriv(a, p), p)) == 1


# ----------------------------------------------------------------------------
# the ring A = (Z/p^K)[z]/(m): elements are tuples of length s; own implementation
# ----------------------------------------------------------------------------

class RingA:
    def __init__(self, p: int, K: int, m: List[int]):
        self.p, self.K, self.N = p, K, p ** K
        self.m = [c % self.N for c in m]
        self.s = len(m) - 1
        assert self.m[-1] == 1
    def zero(self): return tuple([0] * self.s)
    def one(self): return tuple([1] + [0] * (self.s - 1))
    def from_int(self, k): return tuple([k % self.N] + [0] * (self.s - 1))
    def add(self, a, b): return tuple((x + y) % self.N for x, y in zip(a, b))
    def sub(self, a, b): return tuple((x - y) % self.N for x, y in zip(a, b))
    def mul(self, a, b):
        prod = [0] * (2 * self.s - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] = (prod[i + j] + x * y) % self.N
        for i in range(len(prod) - 1, self.s - 1, -1):
            c = prod[i]
            if c:
                for j in range(self.s + 1):
                    prod[i - self.s + j] = (prod[i - self.s + j] - c * self.m[j]) % self.N
        return tuple(prod[: self.s])
    def is_zero(self, a): return all(x % self.N == 0 for x in a)
    def eq(self, a, b): return self.is_zero(self.sub(a, b))
    def residue(self, a): return tuple(x % self.p for x in a)
    def in_Zp(self, a): return all(x % self.N == 0 for x in a[1:])
    def symrem(self, a, k: int) -> int:
        Nk = self.p ** k; x = a[0] % Nk
        return x - Nk if x > Nk // 2 else x
    def eval_poly(self, coeffs_int: Sequence[int], x):
        acc = self.zero()
        for c in reversed(coeffs_int):
            acc = self.add(self.mul(acc, x), self.from_int(c))
        return acc
    def eval_sparse(self, F: pg.Poly, roots):
        acc = self.zero()
        pw = [[self.one()] for _ in roots]
        for e, c in F.items():
            term = self.from_int(c)
            for i, ei in enumerate(e):
                while len(pw[i]) <= ei:
                    pw[i].append(self.mul(pw[i][-1], roots[i]))
                if ei: term = self.mul(term, pw[i][ei])
            acc = self.add(acc, term)
        return acc
    def poly_from_roots(self, rts):
        poly = [self.one()]
        for r in rts:
            new = [self.zero()] * (len(poly) + 1)
            for i, c in enumerate(poly):
                new[i + 1] = self.add(new[i + 1], c)
                new[i] = self.sub(new[i], self.mul(c, r))
            poly = new
        return poly

# residue field F_{p^s} = F_p[z]/(m): elements tuples of length s
class FieldFq:
    def __init__(self, p, m):
        self.p, self.m, self.s = p, [c % p for c in m], len(m) - 1
    def mul(self, a, b):
        prod = [0] * (2 * self.s - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                prod[i + j] = (prod[i + j] + x * y) % self.p
        for i in range(len(prod) - 1, self.s - 1, -1):
            c = prod[i]
            if c:
                for j in range(self.s + 1):
                    prod[i - self.s + j] = (prod[i - self.s + j] - c * self.m[j]) % self.p
        return tuple(prod[: self.s])
    def pow(self, a, e):
        r = tuple([1] + [0] * (self.s - 1))
        for _ in range(e): r = self.mul(r, a)
        return r


# ----------------------------------------------------------------------------
# exact linear algebra over Q and arithmetic in Q[x]/(f) (own implementation)
# ----------------------------------------------------------------------------

def q_rank(rows: List[List[Fraction]]) -> int:
    M = [r[:] for r in rows]; rank = 0
    ncols = len(M[0]) if M else 0
    for c in range(ncols):
        piv = next((i for i in range(rank, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = 1 / M[rank][c]; M[rank] = [x * inv for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][c] != 0:
                fac = M[i][c]; M[i] = [x - fac * y for x, y in zip(M[i], M[rank])]
        rank += 1
    return rank

def q_det(M: List[List[Fraction]]) -> Fraction:
    M = [r[:] for r in M]; n = len(M); det = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None: return Fraction(0)
        if piv != i: M[i], M[piv] = M[piv], M[i]; det = -det
        det *= M[i][i]; inv = 1 / M[i][i]
        for r in range(i + 1, n):
            if M[r][i] != 0:
                fac = M[r][i] * inv
                for c in range(i, n): M[r][c] -= fac * M[i][c]
    return det

def q_resultant(a: List[Fraction], b: List[Fraction]) -> Fraction:
    da, db = len(a) - 1, len(b) - 1; N = da + db; M = []
    for i in range(db):
        row = [Fraction(0)] * N
        for j, c in enumerate(reversed(a)): row[i + j] = c
        M.append(row)
    for i in range(da):
        row = [Fraction(0)] * N
        for j, c in enumerate(reversed(b)): row[i + j] = c
        M.append(row)
    return q_det(M)

def q_discriminant(h: List[Fraction]) -> Fraction:
    d = len(h) - 1
    if d == 1: return Fraction(1)
    dh = [i * h[i] for i in range(1, len(h))]
    sign = -1 if (d * (d - 1) // 2) % 2 else 1
    return sign * q_resultant(h, dh) / h[-1]

class QuotientField:
    """Q[x]/(f), elements are lists of n Fractions."""
    def __init__(self, f: List[int]):
        self.f = [Fraction(c) for c in f]; self.n = len(f) - 1
    def from_vec(self, v): return [Fraction(x) for x in v] + [Fraction(0)] * (self.n - len(v))
    def mul(self, a, b):
        prod = [Fraction(0)] * (2 * self.n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b): prod[i + j] += x * y
        for i in range(len(prod) - 1, self.n - 1, -1):
            c = prod[i]
            if c:
                for j in range(self.n + 1): prod[i - self.n + j] -= c * self.f[j]
        return prod[: self.n]
    def add(self, a, b): return [x + y for x, y in zip(a, b)]
    def is_zero(self, a): return all(x == 0 for x in a)


# ----------------------------------------------------------------------------
# integer roots of a monic integer polynomial (own implementation)
# ----------------------------------------------------------------------------

def z_poly_gcd_monic(a: List[int], b: List[int]) -> List[int]:
    A = [Fraction(c) for c in a]; B = [Fraction(c) for c in b]
    def strip(x):
        x = x[:]
        while x and x[-1] == 0: x.pop()
        return x
    A, B = strip(A), strip(B)
    while B:
        # A mod B
        A = A[:]
        while len(A) >= len(B) and A:
            c = A[-1] / B[-1]; k = len(A) - len(B)
            for j in range(len(B)): A[k + j] -= c * B[j]
            A = strip(A)
        A, B = B, A
    lc = A[-1]; A = [c / lc for c in A]
    assert all(c.denominator == 1 for c in A)
    return [int(c) for c in A]

def z_poly_div_exact(a: List[int], b: List[int]) -> List[int]:
    A = [Fraction(c) for c in a]; q = [Fraction(0)] * (len(a) - len(b) + 1)
    for k in range(len(a) - len(b), -1, -1):
        c = A[k + len(b) - 1] / Fraction(b[-1]); q[k] = c
        for j in range(len(b)): A[k + j] -= c * b[j]
    assert all(c == 0 for c in A) and all(c.denominator == 1 for c in q)
    return [int(c) for c in q]

def integer_roots(R: List[int], B: float, max_ell: int = 10 ** 6) -> Tuple[List[int], Dict]:
    """all integer roots of monic R given |root| <= 2^B: lift the linear factors
    of the squarefree part at an auxiliary prime ell to ell^k > 2^{B+1}."""
    dR = [i * R[i] for i in range(1, len(R))]
    g = z_poly_gcd_monic(R, dR)
    Rs = z_poly_div_exact(R, g) if len(g) > 1 else list(R)
    ell = 3
    while not (is_prime(ell) and fp_squarefree([c % ell for c in Rs], ell)):
        ell += 1
        need(ell <= max_ell, "integer-root search: no auxiliary prime found")
    k = int(math.floor((B + 1) / math.log2(ell))) + 1
    Nk = ell ** k
    Rk = [c % Nk for c in Rs]; dRk = [(i * Rs[i]) % Nk for i in range(1, len(Rs))]
    roots = []
    for r0 in [x for x in range(ell) if poly_eval_int([c % ell for c in Rs], x) % ell == 0]:
        a = r0
        for _ in range(k.bit_length() + 2):           # Newton iteration with unit derivative
            fa = poly_eval_int(Rk, a) % Nk; da = poly_eval_int(dRk, a) % Nk
            a = (a - fa * pow(da, -1, Nk)) % Nk
        need(poly_eval_int(Rk, a) % Nk == 0, "integer-root search: Newton lift failed")
        sr = a - Nk if a > Nk // 2 else a
        if abs(sr) <= 2 ** B and poly_eval_int(R, sr) == 0:
            roots.append(sr)
    return sorted(roots), {"ell": ell, "k": k, "squarefree_part_degree": len(Rs) - 1}


# ----------------------------------------------------------------------------
# the checker
# ----------------------------------------------------------------------------

def load_poly(L) -> pg.Poly:
    return {tuple(e): c for e, c in L}

def check(cert: Dict, verbose: bool = False) -> Dict:
    log: List[str] = []
    def ok(msg):
        log.append(msg)
        if verbose: print("  " + msg)
    H = cert["header"]
    need(H.get("case") == 1, "only case 1 certificates are checked by this program")
    f, p, s, m, K = H["f"], H["p"], H["s"], H["m"], H["K"]
    n = len(f) - 1
    need(isinstance(f, list) and all(isinstance(c, int) for c in f) and f[-1] == 1 and n >= 2, "C0: f is not a monic integer polynomial")
    need(isinstance(p, int) and is_prime(p), "C0: p is not prime")
    need(isinstance(K, int) and K >= 1 and isinstance(s, int) and s >= 1, "C0: bad precision or residue degree")
    need(fp_squarefree([c % p for c in f], p), "C0: f is not squarefree mod p")
    need(isinstance(m, list) and len(m) - 1 == s and m[-1] == 1 and fp_irreducible(m, p), "C0: modulus of O_q is not irreducible of degree s")
    A = RingA(p, K, m)
    Fq = FieldFq(p, m)
    roots = H["roots"]
    need(isinstance(roots, list) and len(roots) == n and all(isinstance(r, list) and len(r) == s and all(isinstance(x, int) and 0 <= x < A.N for x in r) for r in roots),
         "C0: roots have the wrong shape or are not reduced mod p^K")
    roots = [tuple(r) for r in roots]
    need(all(A.is_zero(A.eval_poly(f, r)) for r in roots), "C0: f(alpha^) != 0 mod p^K")
    res = [A.residue(r) for r in roots]
    need(len(set(res)) == n, "C0: roots are not distinct mod p")
    need(A.in_Zp(roots[0]), "C0: alpha_0 not in Z_p")
    tau = []
    for r in res:
        img = Fq.pow(r, p)
        need(img in res, "C0: Frobenius image is not a root")
        tau.append(res.index(img))
    tau = tuple(tau)
    need(sorted(tau) == list(range(n)), "C0: Frobenius is not a permutation")
    ok(f"C0: roots certified in O_q/p^{K} (q = {p}^{s}); tau = {tau}")

    # ---- C1 ----
    QF = QuotientField(f)
    systems = []
    for L in cert["lattice"]["subfields"]:
        b, h, blocks = L["b"], L["h"], L["blocks"]
        need(isinstance(b, list) and len(b) == n and all(isinstance(x, int) for x in b), "C1: primitive element malformed")
        need(isinstance(h, list) and all(isinstance(x, int) for x in h) and h[-1] == 1, "C1: minimal polynomial malformed")
        d = len(h) - 1
        need(d == L["degree"] and isinstance(blocks, list) and len(blocks) == d and sorted(x for bl in blocks for x in bl) == list(range(n)),
             "C1: degree / blocks inconsistent")
        beta = QF.from_vec(b)
        val = QF.from_vec([0])
        for c in reversed(h):
            val = QF.add(QF.mul(val, beta), QF.from_vec([c]))
        need(QF.is_zero(val), "C1: h(b(alpha)) != 0")
        pows = [QF.from_vec([1])]
        for _ in range(d - 1): pows.append(QF.mul(pows[-1], beta))
        need(q_rank([[pows[i][c] for i in range(d)] for c in range(n)]) == d, "C1: h is not the minimal polynomial of b(alpha)")
        disc = q_discriminant([Fraction(c) for c in h])
        need(disc != 0, "C1: disc h = 0")
        need(K > vp(int(disc), p) / 2, "C1: precision K too small to certify the block system")
        vals = [A.eval_poly(b, r) for r in roots]
        classes: List[List[int]] = []
        for j, x in enumerate(vals):
            for cl in classes:
                if A.eq(vals[cl[0]], x): cl.append(j); break
            else:
                classes.append([j])
        need(sorted(sorted(c) for c in classes) == sorted(sorted(bl) for bl in blocks), "C1: block system does not match the recomputed one")
        if 1 < d < n: systems.append([sorted(bl) for bl in blocks])
    U0g = [tuple(g) for g in cert["lattice"]["U0_gens"]]
    need(all(sorted(g) == list(range(n)) for g in U0g), "C1: U_0 generator is not a permutation")
    U0 = pg.closure(U0g, n)
    def preserves(g, blocks):
        bs = {frozenset(bl) for bl in blocks}
        return all(frozenset(g[i] for i in bl) in bs for bl in blocks)
    need(all(preserves(g, Bl) for g in U0 for Bl in systems), "C1: U_0 does not preserve every block system")
    # type bound with all n points
    allsys = [[[i] for i in range(n)]] + systems
    def finest_common(x, y):
        best = None
        for idx, Bl in enumerate(allsys):
            if any(x in bl and y in bl for bl in Bl):
                if best is None or len(Bl) > len(allsys[best]): best = idx
        return best
    tb = 1
    for i in range(n):
        ty = tuple(finest_common(i, t) for t in range(i))
        tb *= sum(1 for y in range(i, n) if tuple(finest_common(y, t) for t in range(i)) == ty)
    need(len(U0) == tb, f"C1: |U_0| = {len(U0)} is not the type bound {tb}; U_0 = W not certified")
    need(tau in U0, "C1: tau not in U_0")
    ok(f"C1: {len(systems)} proper block systems; U_0 = W of order {tb}; tau in U_0")

    # ---- steps ----
    log2p = math.log2(p)
    M = 1 + max(abs(c) for c in f[:-1])
    U = U0
    def roots_for(T):
        if T is None: return roots, math.log2(M)
        need(isinstance(T, list) and all(isinstance(c, int) for c in T) and len(T) <= n and any(c != 0 for c in T[1:]), "Tschirnhaus transformation malformed")
        return [A.eval_poly(T, r) for r in roots], math.log2(sum(abs(c) * M ** j for j, c in enumerate(T)))
    def orbit_of(F, Ugens, cap):
        orb = {pg.canon(F): F}; frontier = [F]
        while frontier:
            nxt = []
            for P in frontier:
                for g in Ugens:
                    Q = pg.act(g, P); kq = pg.canon(Q)
                    if kq not in orb:
                        need(len(orb) < cap, "orbit larger than the index")
                        orb[kq] = Q; nxt.append(Q)
            frontier = nxt
        return list(orb.values())
    def recover_resolvent(F, Ugens, Ni, rts, k):
        orb = orbit_of(F, Ugens, Ni)
        need(len(orb) == Ni, "orbit size differs from the index")
        R_A = A.poly_from_roots([A.eval_sparse(P, rts) for P in orb])
        need(all(A.in_Zp(c) for c in R_A), "resolvent coefficient not in Z_p")
        return [A.symrem(c, k) for c in R_A]
    def bound_B(F, logM):
        need(all(isinstance(c, int) and c != 0 for c in F.values()) and all(len(e) == n and all(isinstance(x, int) and x >= 0 for x in e) for e in F), "invariant malformed")
        return math.log2(sum(abs(c) for c in F.values())) + max(sum(e) for e in F) * logM

    for i, S in enumerate(cert["steps"]):
        Ug = [tuple(g) for g in S["U_gens"]]; Ung = [tuple(g) for g in S["U_next_gens"]]; sigma = tuple(S["sigma"])
        need(all(sorted(g) == list(range(n)) for g in Ug + Ung + [sigma]), f"step {i}: non-permutation entry")
        Ui = pg.closure(Ug, n)
        need(Ui == U, f"step {i}: U_i differs from the group reached so far")
        Un = pg.closure(Ung, n)
        need(Un < Ui and sigma in Ui, f"step {i}: U_{i+1} not a proper subgroup of U_i, or sigma not in U_i")
        F = load_poly(S["F"]); v = S["v"]; k = S["k"]; T = S.get("T"); R = S["R"]
        need(isinstance(v, int) and isinstance(k, int) and isinstance(R, list) and all(isinstance(c, int) for c in R), f"step {i}: malformed scalars")
        Vp = pg.conjugate(Un, pg.inverse(sigma))
        Ni = len(Ui) // len(Un)
        ver = pg.verify_stabilizer(pg.generating_set(Ui, n), len(Ui), pg.generating_set(Vp, n), len(Vp), F, n)
        need(ver["ok"], f"step {i}: C2 Stab_U(F) != sigma^-1 U_next sigma")
        rts, logM = roots_for(T)
        B = bound_B(F, logM)
        k_prf = int(math.floor(Ni * (B + 1) / log2p)) + 1
        need(k_prf <= k <= K, f"step {i}: C4 precision k = {k} outside [k_prf = {k_prf}, K = {K}]")
        g = A.eval_sparse(pg.act(sigma, F), rts)
        need(A.in_Zp(g) and (g[0] - v) % p ** k == 0, f"step {i}: C3 sigma F(alpha^) is not congruent to v mod p^k")
        need(len(R) == Ni + 1 and R[-1] == 1 and recover_resolvent(F, pg.generating_set(Ui, n), Ni, rts, k) == R, f"step {i}: C5 resolvent does not match the recomputed one")
        need(abs(v) <= 2 ** B, f"step {i}: C5 |v| exceeds the root bound")
        need(poly_eval_int(R, v) == 0, f"step {i}: C5 R(v) != 0")
        Rp = poly_eval_int([j * R[j] for j in range(1, len(R))], v)
        need(Rp != 0, f"step {i}: C5 v is a multiple root of R")
        need(vp(Rp, p) < k, f"step {i}: C5 identification threshold k > v_p(R'(v)) fails")
        ok(f"step {i}: C2-C5 ok (index {Ni}, k = {k} >= k_prf = {k_prf}, v = {v})")
        U = Un

    # ---- C6 ----
    Tm = cert["terminal"]
    need(Tm.get("kind") == "negative_resolvents", "C6: unsupported terminal kind")
    Ulg = [tuple(g) for g in Tm["U_gens"]]
    need(all(sorted(g) == list(range(n)) for g in Ulg) and pg.closure(Ulg, n) == U, "C6: terminal group differs from the last group of the chain")
    my_classes = pg.maximal_subgroup_classes(U, n)
    supplied = []
    for c in Tm["classes"]:
        Vg = [tuple(g) for g in c["V_gens"]]
        need(all(sorted(g) == list(range(n)) for g in Vg), "C6: non-permutation in a terminal record")
        supplied.append((c, pg.closure(Vg, n)))
    Ulgens = pg.generating_set(U, n)
    for V in my_classes:
        match = next((c for c, Vc in supplied if any(pg.conjugate(Vc, u) == V for u in U)), None)
        need(match is not None, f"C6: no terminal record for a class of maximal subgroups of order {len(V)}")
        if match["kind"] == "dismissed_by_pruning":
            need(not any(pg.compose(pg.inverse(u), pg.compose(tau, u)) in V for u in U), "C6: dismissal invalid: tau lies in a conjugate of V")
            ok(f"C6: class of order {len(V)}: dismissed, tau in no conjugate")
            continue
        need(match["kind"] == "negative_resolvent", "C6: unknown terminal record kind")
        Vc = pg.closure([tuple(g) for g in match["V_gens"]], n)
        F = load_poly(match["F"]); T = match.get("T"); k = match["K"]; R = match["R"]
        need(isinstance(k, int) and isinstance(R, list) and all(isinstance(c, int) for c in R), "C6: malformed terminal record")
        ver = pg.verify_stabilizer(Ulgens, len(U), pg.generating_set(Vc, n), len(Vc), F, n)
        need(ver["ok"], "C6: terminal invariant stabilizer check failed")
        rts, logM = roots_for(T)
        Ni = len(U) // len(Vc)
        B = bound_B(F, logM)
        k_prf = int(math.floor(Ni * (B + 1) / log2p)) + 1
        need(k_prf <= k <= K, "C6: terminal precision outside [k_prf, K]")
        need(len(R) == Ni + 1 and R[-1] == 1 and recover_resolvent(F, Ulgens, Ni, rts, k) == R, "C6: terminal resolvent does not match the recomputed one")
        rts_int, info = integer_roots(R, B)
        need(rts_int == [], "C6: terminal resolvent has an integer root: G = U_ell NOT certified")
        ok(f"C6: class of order {len(V)}: negative, resolvent of degree {Ni} has no integer root (ell = {info['ell']})")
    need(cert.get("claimed_group_order") == len(U), "claimed group order differs from the certified one")
    return {"verdict": "ACCEPT", "G_order": len(U), "G_gens": [list(g) for g in pg.generating_set(U, n)], "log": log}


def main(argv):
    if len(argv) < 2:
        print(__doc__); return 2
    verbose = "-v" in argv
    with open(argv[1]) as fh:
        cert = json.load(fh)
    try:
        res = check(cert, verbose)
    except Reject as e:
        print(f"REJECT: {e}"); return 1
    except (KeyError, TypeError, ValueError, IndexError, AssertionError) as e:
        print(f"REJECT: malformed certificate ({type(e).__name__}: {e})"); return 1
    print(f"ACCEPT: Gal(f) has order {res['G_order']}, generators {res['G_gens']}")
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
