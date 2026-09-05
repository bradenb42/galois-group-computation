"""
family_eisenstein.py — validation family 2: Eisenstein polynomials of degree
n ≤ 12 over Q_2, Q_3, Q_5, checked against their explicit splitting fields.

Scope. The implemented case-2 machinery is the tame case (p ∤ n). For tame,
totally ramified extensions the classification underlying the tables of local
fields (Jones–Roberts) is explicit: the isomorphism classes of totally tamely
ramified degree-n extensions of Q_p are

        L_j = Q_p((g^j p)^{1/n}),   j = 0, …, gcd(n, p-1) - 1,

g a primitive root mod p; the splitting field is K' = Q_{p^{s0}}((g^j p)^{1/n})
with s0 = ord of p in (Z/n)^×, so

        e' = n,  f' = s0,  Gal(K'/Q_p) = C_n ⋊_p C_{s0}
        (inertia sigma of order n; Frobenius phi with phi sigma phi^{-1} = sigma^p),

independently of j. Wild degrees (p | n) are reported as out of implemented
scope; hensel_frobenius.case2 implements the tame case.

Run. For every prime p in {2, 3, 5} and every tame n ≤ 12: all pure class
representatives x^n - g^j p, plus `extras` random Eisenstein polynomials of the
same degree (their fields are isomorphic to pure ones by Krasner, so the same
prediction applies). For each polynomial, from the certified elements
(tau_iota, tau_phi) of case2:

  E1  inertia element is an n-cycle and v_{pi'}(alpha) = 1 (e' = n);
  E2  s reported by case2 equals s0 = ord_n(p) (f' = s0);
  E3  |<tau_iota, tau_phi>| = n * s0;
  E4  explicit splitting-field comparison: relabel the roots along the
      tau_iota-orbit (so tau_iota becomes k -> k+1 on Z/n); then the group,
      as a permutation group of Z/n, must EQUAL <k -> k+1, k -> p k>
      — the Galois group of Q_{p^{s0}}((g^j p)^{1/n}) in its natural labelling
      (the Frobenius lift acts on the roots zeta^k alpha by zeta -> zeta^p,
      and a translation twist is absorbed by the cyclic factor);
  E5  metacyclic relation tau_phi tau_iota tau_phi^{-1} = tau_iota^p;
  E6  ramification polygon in root form: v_{pi'}(alpha_j - alpha_0) = 1 for all
      j != 0 (all slopes 0 after normalization — the tame polygon), the
      multiset {v(alpha_j - alpha_0) - v(alpha_0)} = {0,...,0};
  E7  v_p(disc f) = n - 1 (exact integer discriminant), which equals the
      different identity Sigma_{i>=0} (|G_i| - 1) = |G_0| - 1 = n - 1 for the
      tame filtration G_0 = C_n, G_1 = 1.
"""

from __future__ import annotations

import json
import math
import random
import sys
import time
from fractions import Fraction
from typing import Dict, List

import hensel_frobenius as hf
import permgroup as pg
import subfields as sf


PRIMITIVE_ROOT = {2: 1, 3: 2, 5: 2}

def ord_mod(p: int, n: int) -> int:
    s, x = 1, p % n
    while x != 1:
        x = (x * p) % n; s += 1
    return s

def tame_degrees(p: int, nmax: int = 12) -> List[int]:
    return [n for n in range(2, nmax + 1) if n % p != 0]

def wild_degrees(p: int, nmax: int = 12) -> List[int]:
    return [n for n in range(2, nmax + 1) if n % p == 0]

def pure_representatives(p: int, n: int) -> List[List[int]]:
    """the class representatives x^n - g^j p, j < gcd(n, p-1)."""
    g = PRIMITIVE_ROOT[p]
    out = []
    for j in range(math.gcd(n, p - 1)):
        c = pow(g, j) * p
        out.append([-c] + [0] * (n - 1) + [1])
    return out

def random_eisenstein(p: int, n: int, rng) -> List[int]:
    """monic Eisenstein: a_0 = p*unit (not divisible by p^2), a_i in p*Z small."""
    a0 = -p * rng.choice([u for u in range(1, 3 * p) if u % p])
    mids = [p * rng.randint(-2, 2) for _ in range(n - 1)]
    return [a0] + mids + [1]


def theory_group(p: int, n: int) -> frozenset:
    """<k -> k+1, k -> p k> on Z/n: Gal of the explicit splitting field."""
    shift = tuple((k + 1) % n for k in range(n))
    mult = tuple((p * k) % n for k in range(n))
    return pg.closure([shift, mult], n)


def check_one(f: List[int], p: int, K: int = 14) -> Dict:
    n = len(f) - 1
    rec: Dict = {"f": f, "p": p, "n": n}
    s0 = ord_mod(p, n)
    rec["s0_theory"], rec["expected_order"] = s0, n * s0
    ob = hf.case2(f, p, K, return_objects=True)
    B, roots, vB = ob["B"], ob["roots"], ob["vB"]
    ti, tp = tuple(ob["tau_iota"]), tuple(ob["tau_phi"])
    G = pg.closure([ti, tp], n)
    # E1: inertia n-cycle, e' = n
    rec["E1_inertia_n_cycle"] = (hf.cycle_type(ti) == [n]) and vB(roots[0]) == 1
    # E2: residue degree
    rec["E2_s_equals_ord"] = (ob["s"] == s0)
    # E3: order
    rec["G_order"] = len(G)
    rec["E3_order"] = (len(G) == n * s0)
    # E4: relabel along the tau_iota-orbit and compare with the explicit group
    lab = [0] * n
    pos = 0
    for step in range(n):
        lab[pos] = step
        pos = ti[pos]
    inv_lab = [0] * n
    for i, l in enumerate(lab):
        inv_lab[l] = i
    def relabel(perm):
        return tuple(lab[perm[inv_lab[k]]] for k in range(n))
    G_l = frozenset(relabel(x) for x in G)
    rec["E4_equals_explicit_splitting_group"] = (G_l == theory_group(p, n))
    # E5: metacyclic relation
    conj = pg.compose(tp, pg.compose(ti, pg.inverse(tp)))
    ti_p = pg.identity(n)
    for _ in range(p % n):
        ti_p = pg.compose(ti, ti_p)
    rec["E5_phi_iota_phi_inv_is_iota_p"] = (conj == ti_p)
    # E6: ramification polygon in root form (tame: all normalized slopes 0)
    diffs = [vB(B.sub(roots[j], roots[0])) - vB(roots[0]) for j in range(1, n)]
    rec["E6_polygon_multiset"] = sorted(diffs)
    rec["E6_tame_polygon"] = all(d == 0 for d in diffs)
    # E7: discriminant valuation = n-1 = different identity
    disc = sf.discriminant([Fraction(c) for c in f])
    v, dd = 0, abs(int(disc))
    while dd % p == 0:
        dd //= p; v += 1
    rec["v_p_disc"] = v
    rec["E7_disc_valuation_n_minus_1"] = (v == n - 1)
    rec["different_identity_sum"] = n - 1                      # Sigma (|G_i|-1) for G_0=C_n, G_i=1 (i>=1)
    rec["ok"] = all(rec[k] for k in ("E1_inertia_n_cycle", "E2_s_equals_ord", "E3_order",
                                     "E4_equals_explicit_splitting_group", "E5_phi_iota_phi_inv_is_iota_p",
                                     "E6_tame_polygon", "E7_disc_valuation_n_minus_1"))
    return rec


def main(extras: int = 2, verbose: bool = True) -> List[Dict]:
    rng = random.Random(20260823)
    results: List[Dict] = []
    t_all = time.time()
    for p in (2, 3, 5):
        for n in wild_degrees(p):
            results.append({"f": None, "p": p, "n": n, "status": "skipped: wild (p | n) — case-2 machinery is tame-only"})
        for n in tame_degrees(p):
            reps = pure_representatives(p, n)
            polys = [(f, "pure class j=%d" % j) for j, f in enumerate(reps)]
            for _ in range(extras):
                polys.append((random_eisenstein(p, n, rng), "random Eisenstein"))
            for f, kind in polys:
                t0 = time.time()
                rec = check_one(f, p)
                rec["kind"], rec["status"], rec["time_s"] = kind, "ok", round(time.time() - t0, 1)
                results.append(rec)
                if verbose:
                    print(f"Q_{p} n={n:2d} {kind:16s} f={f}: |G|={rec['G_order']:3d} (= n*s0 = {rec['expected_order']:3d}) "
                          f"{'all ok' if rec['ok'] else 'FAILURE ' + str({k: v for k, v in rec.items() if str(k).startswith('E') and v is False})} ({rec['time_s']}s)")
    if verbose:
        oks = [r for r in results if r.get("status") == "ok"]
        sk = [r for r in results if str(r.get("status", "")).startswith("skipped")]
        print(f"\n{len(oks)} Eisenstein polynomials checked, {len(sk)} wild degrees out of scope, {time.time() - t_all:.0f}s")
        print("all E1-E7 pass:", all(r["ok"] for r in oks))
        print("class counts per (p, n) = gcd(n, p-1):",
              all(len(pure_representatives(p, n)) == math.gcd(n, p - 1) for p in (2, 3, 5) for n in tame_degrees(p)))
    return results


def global_cross_check(nmax: int = 5, verbose: bool = True) -> List[Dict]:
    """G^aut vs G^desc: the pure representatives x^n - g^j p are Eisenstein hence
    irreducible over Q; for n <= nmax run the global case-1 descent and verify
    that the local group embeds into the global one up to conjugacy in S_n
    (decomposition subgroup at p), recording when they are equal."""
    import itertools
    import descent as ds
    out = []
    for p in (2, 3, 5):
        for n in [n for n in tame_degrees(p, nmax)]:
            for j, f in enumerate(pure_representatives(p, n)):
                ob = hf.case2(f, p, 14, return_objects=True)
                Gl = pg.closure([tuple(ob["tau_iota"]), tuple(ob["tau_phi"])], n)
                r = ds.run_descent(f, verbose=False)
                Gg = pg.closure([tuple(x) for x in r["G_gens"]], n)
                Glg = pg.generating_set(Gl, n)
                embeds = any(all(pg.compose(pi, pg.compose(g, pg.inverse(pi))) in Gg for g in Glg)
                             for pi in itertools.permutations(range(n)))
                rec = {"f": f, "p": p, "n": n, "class": j, "local_order": len(Gl), "global_order": len(Gg),
                       "local_embeds_in_global": embeds, "equal_orders": len(Gl) == len(Gg)}
                out.append(rec)
                if verbose:
                    print(f"Q_{p} n={n} j={j}: |G_loc| = {len(Gl):2d}, |G_glob| = {len(Gg):2d}, "
                          f"local <= global (conj): {embeds}" + ("  [local = global]" if rec["equal_orders"] and embeds else ""))
    assert all(r["local_embeds_in_global"] for r in out)
    return out


if __name__ == "__main__":
    res = main(extras=int(sys.argv[1]) if len(sys.argv) > 1 else 2)
    print("\nglobal cross-check (G^aut embeds in G^desc of the same polynomial over Q):")
    cross = global_cross_check()
    with open("family_eisenstein_results.json", "w") as fh:
        json.dump({"local": res, "global_cross_check": cross}, fh, indent=1, default=str)