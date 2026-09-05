"""
family_compositions.py — validation family 1: compositions f = g∘h over Q.

What is proven, and therefore tested:
  (P1) the fibres of h, B_i = {α : h(α) = β_i}, form a block system of G that
       appears in the subfield lattice of A6 (Q(β) = Q(h(α)) is a subfield);
  (P2) the action of G on the blocks is Gal(g) (as a permutation group of the
       roots of g, here compared up to conjugacy in S_d);
  (P3) the local group L = Stab_G(B_1)|_{B_1} is Gal(h(x) - β / Q(β)), hence
       G ≤ L ≀ π(G) and |G| = |π(G)| · |G ∩ Ker|, G ∩ Ker ≤ L^d.
What is NOT true in general and is recorded for comparison:
  (X)  the literal claim G ≤ Gal(h) ≀ Gal(g), i.e. L ≤ Gal(h) up to conjugacy.

Scope: brute-force groups restrict the run to deg f = deg g · deg h ≤ 8 with
starting groups of order ≤ 600 (the subgroup-enumeration cap); larger cases
are reported as skipped. "deg g, deg h ≤ 8" in full is out of reach of the
brute-force group layer (deg f up to 64).
"""

from __future__ import annotations

import itertools
import json
import math
import sys
import time
from typing import Dict, List, Optional, Tuple

import descent as ds
import invariants as inv
import hensel_frobenius as hf
import permgroup as pg
import subfields as sf
import verify_roots as vr
from hensel_frobenius import Zmod


# ----------------------------------------------------------------------------
# integer polynomial helpers
# ----------------------------------------------------------------------------

def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out

def padd(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] += x
    for i, x in enumerate(b): out[i] += x
    return out

def compose(g, h):
    """g(h(x)) for integer polynomials low->high."""
    out = [0]
    for c in reversed(g):
        out = padd(pmul(out, h), [c])
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out

def _fp_factor(fb: List[int], p: int) -> List[List[int]]:
    """monic irreducible factors of a squarefree monic polynomial over F_p, by
    trial division against all monic polynomials of degree <= deg/2 (small p:
    when degree d is reached, every factor of smaller degree has been removed,
    so any degree-d divisor is irreducible)."""
    Fp = Zmod(p)
    rem = hf._strip(Fp, [c % p for c in fb])
    out = []
    d = 1
    while len(rem) - 1 >= 2 * d:
        for tup in itertools.product(range(p), repeat=d):
            cand = list(tup) + [1]
            q, r = vr._pdivmod_field(Fp, rem, cand)
            if not hf._strip(Fp, r):
                out.append(cand)
                rem = hf._strip(Fp, q)
                if len(rem) - 1 < 2 * d:
                    break
        d += 1
    if len(rem) > 1:
        out.append(rem)
    return out

def _hensel_bifactor(f: List[int], g: List[int], h: List[int], p: int, k: int) -> List[int]:
    """lift the monic bifactorization f ≡ g h (mod p), gcd(g, h) = 1 mod p, to
    modulus p^k by linear Hensel steps; returns the lift of g."""
    Fp = Zmod(p)
    _, a, b = hf._pextgcd_field(Fp, [c % p for c in g], [c % p for c in h])   # a g + b h ≡ 1 (mod p)
    mod = p
    g, h = [c % p for c in g], [c % p for c in h]
    while mod < p ** k:
        prev = mod
        mod *= p
        prod = pmul(g, h)
        e = [((fc - pc) // prev) % p for fc, pc in zip(f, prod)]
        be = hf._pmul(Fp, [c % p for c in b], e); _, dg = vr._pdivmod_field(Fp, be, [c % p for c in g])
        ae = hf._pmul(Fp, [c % p for c in a], e); _, dh = vr._pdivmod_field(Fp, ae, [c % p for c in h])
        g = [(gc + prev * (dg[i] if i < len(dg) else 0)) % mod for i, gc in enumerate(g)]
        h = [(hc + prev * (dh[i] if i < len(dh) else 0)) % mod for i, hc in enumerate(h)]
    return g

def _divides_exact(g: List[int], f: List[int]) -> bool:
    """does monic g divide f over Z (synthetic division)?"""
    rem = list(f)
    for kk in range(len(f) - len(g), -1, -1):
        c = rem[kk + len(g) - 1]
        if c:
            for j in range(len(g)):
                rem[kk + j] -= c * g[j]
    return all(x == 0 for x in rem)

def is_irreducible_Z(f: List[int]) -> bool:
    """complete irreducibility test for monic squarefree f ∈ Z[x] of small degree:
    factorization mod a good prime, Hensel lifting past a factor-coefficient
    bound, subset recombination with exact division (van Hoeij's ancestor;
    exponential in the number of modular factors, fine for n <= 10)."""
    n = len(f) - 1
    if n <= 1:
        return True
    dF = [i * f[i] for i in range(1, len(f))]
    if len(vr._gcd_Q(f, dF)) > 1:
        return False                                          # not squarefree over Q => reducible (n >= 2)
    p = 3
    while not (hf.is_prime(p) and vr._is_squarefree(Zmod(p), [c % p for c in f])):
        p += 2
    facs = _fp_factor(f, p)
    if len(facs) == 1:
        return True
    norm2 = math.isqrt(sum(c * c for c in f)) + 1
    bound = 2 ** n * norm2                                   # Mignotte-type bound on factor coefficients
    k = 1
    while p ** k <= 2 * bound:
        k += 1
    lifted = []
    for i, fac in enumerate(facs):
        other = [1]
        for j, of in enumerate(facs):
            if j != i:
                other = [c % p for c in pmul(other, of)]
        lifted.append(_hensel_bifactor(f, fac, other, p, k))
    Nk = p ** k
    for r in range(1, len(lifted)):
        for Ssub in itertools.combinations(range(len(lifted)), r):
            prod = [1]
            for i in Ssub:
                prod = [c % Nk for c in pmul(prod, lifted[i])]
            cand = [c - Nk if c > Nk // 2 else c for c in prod]
            if any(abs(c) > bound for c in cand):
                continue
            if _divides_exact(cand, f):
                return False
    return True

# ----------------------------------------------------------------------------
# one composition
# ----------------------------------------------------------------------------

def conjugate_in_Sd(H: frozenset, Kgrp: frozenset, d: int) -> bool:
    if len(H) != len(Kgrp):
        return False
    Hg = pg.generating_set(H, d)
    return any(all(pg.compose(pi, pg.compose(g, pg.inverse(pi))) in Kgrp for g in Hg) for pi in itertools.permutations(range(d)))

def conjugate_contained(H: frozenset, Kgrp: frozenset, d: int) -> bool:
    Hg = pg.generating_set(H, d)
    return any(all(pg.compose(pi, pg.compose(g, pg.inverse(pi))) in Kgrp for g in Hg) for pi in itertools.permutations(range(d)))

def check_composition(g: List[int], h: List[int], verbose: bool = False) -> Dict:
    f = compose(g, h)
    n, d, m = len(f) - 1, len(g) - 1, len(h) - 1
    rec: Dict = {"g": g, "h": h, "f": f, "n": n, "deg_g": d, "deg_h": m}
    if not is_irreducible_Z(f):
        rec["status"] = "skipped: f reducible"
        return rec
    try:
        r = ds.run_descent(f, verbose=False)
    except ArithmeticError as e:
        rec["status"] = f"skipped: {e}"
        return rec
    st = r["state"]
    G = pg.closure([tuple(x) for x in r["G_gens"]], n)
    rec["G_order"], rec["W_order"] = len(G), r["W_order"]
    # (P1) fibres of h as a partition of the roots, compared with the lattice
    A = st.A
    hA = [A.from_int(c) for c in h]
    vals = [hf._peval(A, hA, root) for root in st.roots_raw]
    blocks: List[List[int]] = []
    for j, x in enumerate(vals):
        for bl in blocks:
            if A.eq(vals[bl[0]], x):
                bl.append(j); break
        else:
            blocks.append([j])
    blocks = sorted(sorted(b) for b in blocks)
    lattice_systems = [sorted(sorted(b) for b in s_["blocks"]) for s_ in r["A6"]["subfields"]]
    rec["fibre_blocks"] = blocks
    rec["P1_fibres_in_lattice"] = blocks in lattice_systems and len(blocks) == d and all(len(b) == m for b in blocks)
    # (P2) block quotient vs Gal(g)
    P = inv._canon(blocks)
    piG = frozenset(inv.induced_action(x, P) for x in G)
    rec["block_quotient_order"] = len(piG)
    if is_irreducible_Z(g):
        rg = ds.run_descent(g, verbose=False)
        Gg = pg.closure([tuple(x) for x in rg["G_gens"]], d)
        rec["Gal_g_order"] = len(Gg)
        rec["P2_block_quotient_is_Gal_g"] = conjugate_in_Sd(piG, Gg, d)
    else:
        rec["Gal_g_order"] = None; rec["P2_block_quotient_is_Gal_g"] = None
    # (P3) local group, kernel, proven bound
    L, _ = inv.local_group(G, P[0])
    ker = frozenset(x for x in G if inv.induced_action(x, P) == pg.identity(d))
    rec["local_group_order"] = len(L)
    rec["kernel_order"] = len(ker)
    rec["P3_order_factorization"] = (len(G) == len(piG) * len(ker)) and ((len(L) ** d) % len(ker) == 0)
    rec["P3_G_in_L_wr_piG"] = len(G) <= len(L) ** d * len(piG)
    # (X) literal wreath claim L <= Gal(h) (up to conjugacy), only meaningful when h is irreducible
    if m >= 2 and is_irreducible_Z(h):
        rh = ds.run_descent(h, verbose=False)
        Gh = pg.closure([tuple(x) for x in rh["G_gens"]], m)
        rec["Gal_h_order"] = len(Gh)
        rec["X_local_group_in_Gal_h"] = conjugate_contained(L, Gh, m)
    else:
        rec["Gal_h_order"] = None
        rec["X_local_group_in_Gal_h"] = None if m >= 2 else True
    rec["status"] = "ok"
    return rec


# ----------------------------------------------------------------------------
# the run
# ----------------------------------------------------------------------------

CATALOGUE = {
    2: [[-2, 0, 1], [1, 0, 1], [1, 1, 1], [-3, 0, 1], [2, 0, 1], [-1, 1, 1]],
    3: [[-2, 0, 0, 1], [1, 1, 0, 1], [1, -3, 0, 1], [0, 1, 0, 1], [0, -3, 0, 1], [2, 0, 1, 1]],
    4: [[1, 0, 0, 0, 1], [-2, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 0, 1, 0, 1]],
}

# classical compositions with proven groups, for the direct comparison
KNOWN = {
    ((-2, 0, 1), (0, 0, 1)): 8,          # (x^2)^2 - 2 = x^4 - 2: D_4
    ((-2, 0, 1), (0, 1, 0, 1)): 12,      # (x^3 + x)^2 - 2: S_3 x C_2
    ((-2, 0, 0, 1), (0, 0, 1)): 12,      # (x^2)^3 - 2 = x^6 - 2: S_3 x C_2
    ((1, 0, 1), (0, 0, 1)): 4,           # x^4 + 1: V_4
    ((-2, 0, 1), (1, 0, 1)): 8,          # (x^2+1)^2 - 2 = x^4 + 2x^2 - 1: D_4
    ((2, 0, 1), (0, 0, 1)): 8,           # x^4 + 2: D_4
    ((1, 1, 1), (0, 0, 1)): 4,           # x^4 + x^2 + 1 is reducible; (skipped by the irreducibility test)
}

def main(max_degree: int = 8, verbose: bool = True, budget_s: Optional[float] = None,
         results_path: str = "family_compositions_results.json") -> List[Dict]:
    import os
    pg.load_subgroup_cache()
    results = json.load(open(results_path)) if os.path.exists(results_path) else []
    done = {(tuple(r["g"]), tuple(r["h"])) for r in results}
    pairs = [(g, h) for dg, gs in CATALOGUE.items() for dh, hs in CATALOGUE.items() if dg * dh <= max_degree
             for g in gs for h in hs]
    # include the pure powers h = x^m as well (the classical x^n - a family)
    pairs += [(g, [0] * m + [1]) for dg, gs in CATALOGUE.items() for m in (2, 3, 4) if dg * m <= max_degree for g in gs]
    seen = set()
    t_all = time.time()
    for g, h in pairs:
        key = (tuple(g), tuple(h))
        if key in seen or key in done: continue
        if budget_s is not None and time.time() - t_all > budget_s:
            print(f"[budget reached: {len(done) + len(seen)} of {len(pairs)} pairs recorded]")
            break
        seen.add(key)
        t0 = time.time()
        rec = check_composition(g, h)
        rec["time_s"] = round(time.time() - t0, 1)
        rec["known_order"] = KNOWN.get(key)
        if rec["status"] == "ok" and rec["known_order"] is not None:
            rec["matches_known"] = (rec["G_order"] == rec["known_order"])
        results.append(rec)
        pg.save_subgroup_cache()
        with open(results_path, "w") as fh:
            json.dump(results, fh, indent=1, default=str)
        if verbose:
            if rec["status"] != "ok":
                print(f"g={g} h={h} n={rec['n']}: {rec['status']}")
            else:
                print(f"g={g} h={h} n={rec['n']:2d} |W|={rec['W_order']:4d} |G|={rec['G_order']:4d} "
                      f"pi(G)={rec['block_quotient_order']:3d} Gal(g)={rec['Gal_g_order']} L={rec['local_group_order']:2d} Gal(h)={rec['Gal_h_order']} "
                      f"| P1 {rec['P1_fibres_in_lattice']} P2 {rec['P2_block_quotient_is_Gal_g']} P3 {rec['P3_order_factorization'] and rec['P3_G_in_L_wr_piG']} "
                      f"| X(L<=Gal h) {rec['X_local_group_in_Gal_h']}"
                      + (f" | known {rec['known_order']} {'OK' if rec['matches_known'] else 'MISMATCH'}" if rec["known_order"] else "")
                      + f" ({rec['time_s']}s)")
    if verbose:
        oks = [r for r in results if r["status"] == "ok"]
        print(f"\n{len(oks)} compositions checked, {len(results) - len(oks)} skipped, {time.time() - t_all:.0f}s total")
        print("P1 (fibres in lattice):      ", all(r["P1_fibres_in_lattice"] for r in oks))
        print("P2 (block quotient = Gal g): ", all(r["P2_block_quotient_is_Gal_g"] for r in oks if r["P2_block_quotient_is_Gal_g"] is not None))
        print("P3 (order factorization, G <= L wr pi(G)):", all(r["P3_order_factorization"] and r["P3_G_in_L_wr_piG"] for r in oks))
        xs = [r for r in oks if r["X_local_group_in_Gal_h"] is not None]
        print(f"X  (literal L <= Gal(h)): holds in {sum(1 for r in xs if r['X_local_group_in_Gal_h'])}/{len(xs)} cases; counterexamples:",
              [(r["g"], r["h"]) for r in xs if not r["X_local_group_in_Gal_h"]])
        print("known groups:", all(r.get("matches_known", True) for r in oks))
    return results


if __name__ == "__main__":
    maxdeg = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else None
    main(maxdeg, budget_s=budget)