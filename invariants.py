"""
invariants.py — U-relative V-invariants valid over every coefficient ring, with a stored table for pairs already encountered,
on-the-fly construction otherwise, and a permutation-group verification of the
stabilizer for every invariant that is used.

Invariants are sparse integer polynomials {exponent tuple: coefficient}.  The
three constructions of the three invariant constructions:

  Type I   (block action drops)  F = G(s_1, …, s_d), s_j = Σ_{x∈B_j} x, G a
           π(U)-relative π(V)-invariant built recursively on the d blocks
           (Principle (B): stabilizer pulls back through the disjoint-variable
           substitution in every characteristic);
  Type II  (local group drops)   F = Σ_j v_j·H, H a U_1-relative W_1-invariant on
           the block B_1 for a maximal W_1 with V_1 ≤ W_1 < U_1, transported by
           elements v_j ∈ V; a 0–1 polynomial, union of disjoint supports;
  Type III (otherwise)           F = Σ_{v∈V} v·m_C, the V-orbit sum of the
           separating monomial m_C of a maximal chain C of block systems of U
           (Lemma 3.1: trivial stabilizer, degree δ(C)); a 0–1 polynomial.

The stabilizer property Stab_U(F) = V is *verified*, never assumed, by the
orbit count of the checker conditions C0-C6 C2: the generators of V fix F and |U·F| = [U:V].  The same
count is run on F mod 2 and F mod 3, which is the "valid over every ring" claim
in checkable form.  Verification results are stored with the invariant.

Permutation groups are handled by brute force (closure by breadth-first search),
which is adequate for the group orders that arise in the tests (≤ a few
thousand); Schreier–Sims would replace `closure` at scale without changing
anything else.
"""

from __future__ import annotations

import itertools
import json
import os
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

Perm = Tuple[int, ...]
Poly = Dict[Tuple[int, ...], int]

from permgroup import (identity, compose, inverse, closure, generating_set, is_transitive,
                       is_maximal_bruteforce, maximal_overgroup, act, reduce_mod, degree, canon, verify_stabilizer)

# ----------------------------------------------------------------------------
# block systems
# ----------------------------------------------------------------------------

Partition = Tuple[FrozenSet[int], ...]

def _canon(blocks) -> Partition:
    return tuple(sorted((frozenset(b) for b in blocks), key=lambda b: min(b)))

def join_partition(P: Partition, Q: Partition, n: int) -> Partition:
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for part in (P, Q):
        for b in part:
            b = sorted(b)
            for x in b[1:]:
                parent[find(x)] = find(b[0])
    cls: Dict[int, set] = {}
    for x in range(n):
        cls.setdefault(find(x), set()).add(x)
    return _canon(cls.values())

def minimal_block_system(gens: Sequence[Perm], n: int, i: int, j: int) -> Partition:
    """finest block system of ⟨gens⟩ with i and j in one block (transitive group)."""
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb; return True
        return False
    union(i, j)
    changed = True
    while changed:
        changed = False
        for g in gens:
            for x in range(n):
                for y in range(x + 1, n):
                    if find(x) == find(y) and union(g[x], g[y]):
                        changed = True
    cls: Dict[int, set] = {}
    for x in range(n):
        cls.setdefault(find(x), set()).add(x)
    return _canon(cls.values())

def all_block_systems(gens: Sequence[Perm], n: int) -> List[Partition]:
    points = _canon([{x} for x in range(n)])
    systems = {points}
    minimal = {minimal_block_system(gens, n, 0, j) for j in range(1, n)}
    systems |= minimal
    changed = True
    while changed:
        changed = False
        cur = list(systems)
        for P in cur:
            for Q in cur:
                J = join_partition(P, Q, n)
                if J not in systems:
                    systems.add(J); changed = True
    return sorted(systems, key=lambda P: -len(P))       # finest first

def refines(P: Partition, Q: Partition) -> bool:
    return all(any(b <= c for c in Q) for b in P)

def maximal_chain(systems: List[Partition]) -> List[Partition]:
    chain = [systems[0]]                                  # points
    while len(chain[-1]) > 1:
        cands = [Q for Q in systems if len(Q) < len(chain[-1]) and refines(chain[-1], Q)]
        chain.append(max(cands, key=len))
    return chain

def induced_action(g: Perm, blocks: Partition) -> Perm:
    rep = [min(b) for b in blocks]
    idx = {b: k for k, b in enumerate(blocks)}
    out = []
    for r in rep:
        img = g[r]
        k = next(k for k, b in enumerate(blocks) if img in b)
        out.append(k)
    return tuple(out)

def local_group(elems: FrozenSet[Perm], block: FrozenSet[int]) -> Tuple[FrozenSet[Perm], List[int]]:
    pts = sorted(block)
    pos = {x: k for k, x in enumerate(pts)}
    loc = set()
    for g in elems:
        if all(g[x] in block for x in pts):
            loc.add(tuple(pos[g[x]] for x in pts))
    return frozenset(loc), pts

# ----------------------------------------------------------------------------
# polynomials
# ----------------------------------------------------------------------------

def padd(F: Poly, G: Poly) -> Poly:
    out = dict(F)
    for e, c in G.items():
        out[e] = out.get(e, 0) + c
        if out[e] == 0:
            del out[e]
    return out

def pmul(F: Poly, G: Poly) -> Poly:
    out: Poly = {}
    for e1, c1 in F.items():
        for e2, c2 in G.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}

def ppow(F: Poly, k: int, n: int) -> Poly:
    out = {tuple([0] * n): 1}
    for _ in range(k):
        out = pmul(out, F)
    return out

# ----------------------------------------------------------------------------
# separating monomial and δ
# ----------------------------------------------------------------------------

def separating_monomial(chain: List[Partition], n: int) -> Tuple[Tuple[int, ...], int, List[int]]:
    """exponent vector of m_C for the chain C_0 ≺ … ≺ C_r, δ(C), and the branching (m_1..m_r)."""
    r = len(chain) - 1
    # address a_l(x) ∈ {1..m_l}: position of x's level-(l-1) block among the children of its level-l block
    branching = []
    addr = {x: [] for x in range(n)}
    for l in range(1, r + 1):
        parent_sys, child_sys = chain[l], chain[l - 1]
        m_l = len(child_sys) // len(parent_sys)
        branching.append(m_l)
        for P in parent_sys:
            children = sorted((c for c in child_sys if c <= P), key=min)
            assert len(children) == m_l
            for k, c in enumerate(children):
                for x in c:
                    addr[x].append(k + 1)
    e = []
    for x in range(n):
        a = addr[x]
        ex = (a[0] - 1) if r >= 1 else 0
        for l in range(2, r + 1):
            if all(a[t - 1] == branching[t - 1] for t in range(1, l)):
                ex += a[l - 1] - 1
        e.append(ex)
    delta = 0
    prod = 1
    for l, m_l in enumerate(branching, start=1):
        prod *= m_l
        delta += (n // prod) * (m_l * (m_l - 1) // 2)
    return tuple(e), delta, branching

# ----------------------------------------------------------------------------
# construction
# ----------------------------------------------------------------------------

class InvariantConstructor:
    def __init__(self, table_path: str = "tables/invariants.json", conjugacy_search_max_n: int = 6):
        self.table_path = table_path
        self.conjugacy_search_max_n = conjugacy_search_max_n
        self.table: List[Dict] = []
        self.stats = {"table_hits": 0, "conjugate_hits": 0, "constructed": 0}
        if os.path.exists(table_path):
            with open(table_path) as fh:
                self.table = json.load(fh)

    # ---- table -----------------------------------------------------------
    def _save(self):
        os.makedirs(os.path.dirname(self.table_path) or ".", exist_ok=True)
        with open(self.table_path, "w") as fh:
            json.dump(self.table, fh)

    @staticmethod
    def _poly_to_json(F: Poly): return [[list(e), c] for e, c in sorted(F.items())]
    @staticmethod
    def _poly_from_json(L): return {tuple(e): c for e, c in L}

    def _lookup(self, U: FrozenSet[Perm], V: FrozenSet[Perm], n: int):
        for entry in self.table:
            if entry["n"] != n or entry["U_order"] != len(U) or entry["V_order"] != len(V):
                continue
            Ue = frozenset(tuple(g) for g in entry["U"]); Ve = frozenset(tuple(g) for g in entry["V"])
            if Ue == U and Ve == V:
                self.stats["table_hits"] += 1
                return self._poly_from_json(entry["F"]), entry["type"], "table"
            if n <= self.conjugacy_search_max_n:
                # conjugate pair: π U_e π^{-1} = U, π V_e π^{-1} = V  ⇒  invariant is π·F
                Ug, Vg = generating_set(Ue, n), generating_set(Ve, n)
                for pi in itertools.permutations(range(n)):
                    pinv = inverse(pi)
                    if all(compose(pi, compose(g, pinv)) in U for g in Ug) and all(compose(pi, compose(g, pinv)) in V for g in Vg):
                        self.stats["conjugate_hits"] += 1
                        return act(pi, self._poly_from_json(entry["F"])), entry["type"], "table(conjugate)"
        return None

    # ---- main entry --------------------------------------------------------
    def invariant(self, U_gens: Sequence[Perm], V_gens: Sequence[Perm], n: int, verify: bool = True, store: bool = True,
                  variant: int = 0) -> Dict:
        """variant = 0: table lookup, then the primary construction. variant >= 1:
        an ALTERNATIVE invariant for the same pair (never from the table): the
        V-orbit sum of the separating monomial with exponents scaled by
        (variant + 1) — Lemma 3.1's stabilizer argument only uses distinctness of
        the exponent patterns, which scaling preserves; verification is run as
        always. Used by the rejection-localization procedure (B4)."""
        U = closure(U_gens, n); V = closure(V_gens, n)
        assert V < U, "need V a proper subgroup of U"
        assert all(g in U for g in V_gens)
        if variant > 0:
            F, typ = self._construct_alternative(U, V, n, variant)
            source = f"alternative(variant={variant})"
        else:
            hit = self._lookup(U, V, n)
            if hit is not None:
                F, typ, source = hit
            else:
                F, typ = self._construct(U, V, n)
                source = "constructed"
                self.stats["constructed"] += 1
        systems = all_block_systems(generating_set(U, n), n) if is_transitive(U, n) else None
        chain = maximal_chain(systems) if systems else None
        _, delta, branching = separating_monomial(chain, n) if chain else (None, n * (n - 1) // 2, [n])
        result = {"n": n, "type": typ, "source": source, "F": F, "terms": len(F), "degree": degree(F), "delta": delta,
                  "branching": branching, "U_order": len(U), "V_order": len(V), "index": len(U) // len(V)}
        if verify:
            result["verification"] = verify_stabilizer(generating_set(U, n), len(U), generating_set(V, n), len(V), F, n)
            assert result["verification"]["ok"], "stabilizer verification failed"
        if store and source == "constructed" and variant == 0:
            self.table.append({"n": n, "U": [list(g) for g in sorted(U)], "V": [list(g) for g in sorted(V)],
                               "U_order": len(U), "V_order": len(V), "type": typ, "F": self._poly_to_json(F),
                               "degree": degree(F), "delta": delta,
                               "verification": result.get("verification")})
            self._save()
        return result

    def _construct_alternative(self, U: FrozenSet[Perm], V: FrozenSet[Perm], n: int, variant: int) -> Tuple[Poly, str]:
        assert is_transitive(U, n)
        systems = all_block_systems(generating_set(U, n), n)
        chain = maximal_chain(systems)
        e, _, _ = separating_monomial(chain, n)
        e = tuple((variant + 1) * x for x in e)
        F: Poly = {}
        for v in V:
            key = tuple(act(v, {e: 1}).keys())[0]
            assert key not in F, "scaled separating monomial has nontrivial stabilizer"
            F[key] = 1
        return F, "III-alt"

    # ---- the trichotomy ---------------------------------------------------
    def _construct(self, U: FrozenSet[Perm], V: FrozenSet[Perm], n: int) -> Tuple[Poly, str]:
        assert is_transitive(U, n), "construction assumes U transitive (true for every group met in the descent)"
        # Principle (A) support invariants first: if V is a point stabilizer, F = x_i
        # (degree 1, 0-1 support, valid over every ring; the resolvent is then a
        # Tschirnhaus-transform of f itself). Without this, metacyclic pairs like
        # (C_p x| C_{p-1}, point stabilizer) get the degree-C(n,2) generic invariant,
        # whose structured values on Kummer-type roots force costly transformations.
        for i in range(n):
            if V == frozenset(u for u in U if u[i] == i):
                return {tuple(1 if j == i else 0 for j in range(n)): 1}, "A-support"
        Ug = generating_set(U, n)
        systems = all_block_systems(Ug, n)
        proper = [P for P in systems if 1 < len(P) < n]
        # walk from coarsest to finest (proper systems are sorted finest-first, so reverse)
        for P in reversed(proper):
            d = len(P)
            piU = frozenset(induced_action(g, P) for g in U)
            piV = frozenset(induced_action(g, P) for g in V)
            if len(piV) < len(piU):                                   # Type I
                G, _ = self._construct(piU, piV, d)
                s = [{tuple(1 if x == i else 0 for i in range(n)): 1 for x in b} for b in P]
                F: Poly = {}
                for e, c in G.items():
                    term = {tuple([0] * n): c}
                    for j, ej in enumerate(e):
                        if ej:
                            term = pmul(term, ppow(s[j], ej, n))
                    F = padd(F, term)
                return F, "I"
        for P in reversed(proper):
            B1 = P[0]
            U1, pts = local_group(U, B1)
            V1, _ = local_group(V, B1)
            if len(V1) < len(U1):                                      # Type II
                W1 = maximal_overgroup(U1, V1, len(pts))
                H, _ = self._construct(U1, W1, len(pts))
                assert all(sum(e) > 0 for e in H), "H must have zero constant term"
                # orbit of B1 under V and transporting elements
                F: Poly = {}
                covered = set()
                for v in sorted(V):
                    Bj = frozenset(v[x] for x in pts)
                    if Bj in covered:
                        continue
                    covered.add(Bj)
                    for e, c in H.items():
                        e2 = [0] * n
                        for k, x in enumerate(pts):
                            e2[v[x]] = e[k]
                        key = tuple(e2)
                        assert key not in F
                        F[key] = c
                return F, "II"
        chain = maximal_chain(systems)                                 # Type III
        e, delta, _ = separating_monomial(chain, n)
        F: Poly = {}
        for v in V:
            key = tuple(act(v, {e: 1}).keys())[0]
            assert key not in F, "separating monomial has nontrivial stabilizer"
            F[key] = 1
        return F, "III"


# ----------------------------------------------------------------------------
# demo
# ----------------------------------------------------------------------------

def S_n(n): return [tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])]

def A_n(n):
    def sign(p):
        s, seen = 1, set()
        for i in range(len(p)):
            if i in seen: continue
            l, j = 0, i
            while j not in seen:
                seen.add(j); j = p[j]; l += 1
            s *= (-1) ** (l - 1)
        return s
    return generating_set(frozenset(g for g in closure(S_n(n), n) if sign(g) == 1), n)

def cyc(n, *cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)

if __name__ == "__main__":
    import shutil, sys, time
    path = sys.argv[1] if len(sys.argv) > 1 else "tables/invariants_demo.json"
    if os.path.exists(path):
        os.remove(path)
    ic = InvariantConstructor(path)
    pairs = {
        "S4 > A4":               (4, S_n(4), A_n(4)),
        "A4 > V4":               (4, A_n(4), [cyc(4, (0, 1), (2, 3)), cyc(4, (0, 2), (1, 3))]),
        "D4=S2wrS2 > S2xS2":     (4, [cyc(4, (0, 2)), cyc(4, (1, 3)), cyc(4, (0, 1), (2, 3))], [cyc(4, (0, 2)), cyc(4, (1, 3))]),
        "D4 (blocks 01|23) > K": (4, [cyc(4, (0, 1)), cyc(4, (2, 3)), cyc(4, (0, 2), (1, 3))], [cyc(4, (0, 1)), cyc(4, (2, 3))]),  # conjugate of the previous pair
        "S3xS2 (x^6-2) > A3xS2": (6, [cyc(6, (0, 1), (2, 3), (4, 5)), cyc(6, (0, 2, 4), (1, 3, 5)), cyc(6, (0, 2), (1, 3))],
                                     [cyc(6, (0, 1), (2, 3), (4, 5)), cyc(6, (0, 2, 4), (1, 3, 5))]),
        "S3wrS2 > sign-product": (6, [cyc(6, (0, 1)), cyc(6, (0, 1, 2)), cyc(6, (0, 3), (1, 4), (2, 5))],
                                     [cyc(6, (0, 1), (3, 4)), cyc(6, (0, 1, 2)), cyc(6, (3, 4, 5)), cyc(6, (0, 3), (1, 4), (2, 5))]),
        "S4wrS2 > (D4xD4):C2":   (8, [cyc(8, (0, 1)), cyc(8, (0, 1, 2, 3)), cyc(8, (0, 4), (1, 5), (2, 6), (3, 7))],
                                     [cyc(8, (0, 1)), cyc(8, (2, 3)), cyc(8, (0, 2), (1, 3)), cyc(8, (4, 5)), cyc(8, (6, 7)), cyc(8, (4, 6), (5, 7)),
                                      cyc(8, (0, 4), (1, 5), (2, 6), (3, 7))]),
        "S5 > A5":               (5, S_n(5), A_n(5)),
        "S5 > S4 (point stab)":  (5, S_n(5), [cyc(5, (0, 1)), cyc(5, (0, 1, 2, 3))]),
    }
    for name, (n, Ug, Vg) in pairs.items():
        t0 = time.time()
        U, V = closure(Ug, n), closure(Vg, n)
        maximal = is_maximal_bruteforce(U, V, n) if len(U) <= 2000 else None
        r = ic.invariant(Ug, Vg, n)
        ver = r["verification"]
        print(f"{name:24s} n={n} |U|={r['U_order']:5d} |V|={r['V_order']:4d} idx={r['index']:3d} maximal={maximal} "
              f"type={r['type']:3s} source={r['source']:16s} terms={r['terms']:3d} deg={r['degree']:2d} delta={r['delta']:2d} "
              f"branching={r['branching']} verify: Z={ver['Z']['ok']} mod2={ver['mod2']['ok']} mod3={ver['mod3']['ok']}  ({time.time()-t0:.1f}s)")
    # second pass: everything comes from the table
    ic2 = InvariantConstructor(path)
    for name, (n, Ug, Vg) in pairs.items():
        r = ic2.invariant(Ug, Vg, n)
        assert r["source"].startswith("table"), name
    print("second pass:", ic2.stats)
