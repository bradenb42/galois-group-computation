"""
descent.py — the Stauduhar step descend(U) over Z (case 1), assembled from
hensel_frobenius.py (roots, Frobenius), subfields.py (degree-one prime, W) and
invariants.py (U-relative V-invariants, group utilities).

descend(U) returns None (no maximal subgroup of U contains G: G = U) or a record
    (V, sigma, v, k_rec, ...)
meaning Stab_U(F) = V, G ≤ sigma V sigma^{-1}, and v = sigma·F(alpha) ∈ Z.

Per (U, V) the step does, in the order:
  * pruning: only cosets sigma N_U(V) with tau ∈ sigma V sigma^{-1} are
    candidates, tau the certified Frobenius element; the count c_tau is reported
    against [U : N_U(V)];
  * recognition: sigma·F(alpha^) is evaluated in A, image-checked, and
    lifted by the symmetric remainder at precision k_rec; the lift is repeated at
    a second precision k_2 > k_rec and the two results must coincide
    (the "same element of R at two precisions" check);
  * proof: the full resolvent R = Π_{U/V}(x - sigma'·F(alpha^)) is recovered
    exactly at precision ≥ k_prf, and R(v) = 0, R'(v) ≠ 0, v_p(R'(v)) < K are
    checked exactly, identifying the coset (Hensel uniqueness);
  * verdicts: positive if an integer simple root belongs to a surviving coset;
    negative if R has no integer root (complete, since every integer root is
    some rho_sigma' and its symmetric remainder is among the candidates);
    inconclusive (multiple integer root) triggers a Tschirnhaus transformation.

Group computations are brute force (closures), adequate for |U| ≤ a few
thousand; maximal subgroups are enumerated among 2-generated subgroups and each
class representative is re-checked with is_maximal_bruteforce.
"""

from __future__ import annotations

import json
import math
import random
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

import hensel_frobenius as hf
import invariants as inv
import subfields as sf
from fractions import Fraction

Perm = Tuple[int, ...]


# ----------------------------------------------------------------------------
# group utilities on top of invariants.py
# ----------------------------------------------------------------------------

from permgroup import conjugate, all_subgroups, maximal_subgroup_classes, normalizer, coset_reps, _SUBGROUP_CACHE

# ----------------------------------------------------------------------------
# the descent state: roots, Frobenius, precision management
# ----------------------------------------------------------------------------

class DescentState:
    def __init__(self, f: List[int], K: int = 120, p: Optional[int] = None, table_path: str = "tables/invariants_descent.json"):
        self.f = f
        self.n = len(f) - 1
        self.p = p or sf.choose_prime(f)
        self.K = 0
        self.ic = inv.InvariantConstructor(table_path)
        self.roots = None
        self.tschirnhaus_T: Optional[List[int]] = None   # current transformation T (None = identity)
        self.last_classes: List[Dict] = []
        self.last_pair_record: Optional[Dict] = None
        self.ensure_precision(K)
        self.log2p = math.log2(self.p)

    def ensure_precision(self, K: int):
        if K <= self.K:
            return
        A, F, project, roots, phi, tau, s = sf.roots_and_frobenius(self.f, self.p, K)
        if self.roots is not None:
            # consistency with the previous labelling: new roots reduce to the old ones
            for old, new in zip(self.roots_raw, roots):
                assert all((a - b) % (self.p ** self.K) == 0 for a, b in zip(old, new))
            assert tau == self.tau
        self.A, self.F, self.project, self.roots_raw, self.phi, self.tau, self.s, self.K = A, F, project, roots, phi, tau, s, K
        self._apply_tschirnhaus()

    def _apply_tschirnhaus(self):
        if self.tschirnhaus_T is None:
            self.roots = list(self.roots_raw)
        else:
            T = [self.A.from_int(c) for c in self.tschirnhaus_T]
            self.roots = [hf._peval(self.A, T, r) for r in self.roots_raw]

    def root_bound_log2(self) -> float:
        """log2 of a bound on |T(alpha_j)| (Cauchy bound for f, then the norm of T)."""
        M = 1 + max(abs(c) for c in self.f[:-1])
        if self.tschirnhaus_T is None:
            return math.log2(M)
        T = self.tschirnhaus_T
        return math.log2(sum(abs(c) * M ** k for k, c in enumerate(T)))

    # -- evaluation and lifting ---------------------------------------------
    def evaluate(self, F: Dict[Tuple[int, ...], int]):
        A = self.A
        pw = [[A.one()] for _ in self.roots]
        acc = A.zero()
        for e, c in F.items():
            term = A.from_int(c)
            for i, ei in enumerate(e):
                while len(pw[i]) <= ei:
                    pw[i].append(A.mul(pw[i][-1], self.roots[i]))
                if ei:
                    term = A.mul(term, pw[i][ei])
            acc = A.add(acc, term)
        return acc

    def image_check(self, gamma) -> bool:
        return all(self.A.base.is_zero(c) for c in gamma[1:])

    def symmetric_remainder(self, gamma, k: int) -> int:
        N = self.p ** k
        v = gamma[0] % N
        return v - N if v > N // 2 else v

    # -- precision formulas of recognition and proof precisions -------------------------------------------
    def bound_B(self, F) -> float:
        l1 = sum(abs(c) for c in F.values())
        d = max(sum(e) for e in F)
        return math.log2(l1) + d * self.root_bound_log2()

    def k_rec(self, B: float) -> int:
        return int(math.floor((B + 1) / self.log2p)) + 1

    def k_prf(self, B: float, N: int) -> int:
        return int(math.floor(N * (B + 1) / self.log2p)) + 1


# ----------------------------------------------------------------------------
# descend(U)
# ----------------------------------------------------------------------------

def _vp(x: int, p: int) -> int:
    if x == 0:
        return 10 ** 9
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

def descend(state: DescentState, U: FrozenSet[Perm], verbose: bool = True, max_tschirnhaus: int = 8,
            use_pruning: bool = True, proof: str = "resolvent") -> Optional[Dict]:
    """One Stauduhar step. Returns a positive record, or None if every class of
    maximal subgroups is certified negative (so G = U). Raises if some class
    stays inconclusive (a multiple rational root that Tschirnhaus could not
    remove), since then G = U is NOT certified."""
    n, p = state.n, state.p
    reps = maximal_subgroup_classes(U, n)
    if verbose:
        print(f"  U of order {len(U)}: {len(reps)} classes of maximal subgroups, orders {[len(V) for V in reps]}")
    rng = random.Random(12345)
    state.last_classes = []
    for V in reps:
        state.tschirnhaus_T = None
        state._apply_tschirnhaus()
        verdict = "inconclusive"
        for attempt in range(max_tschirnhaus + 1):
            state.last_pair_record = None
            res = _test_pair(state, U, V, verbose, use_pruning=use_pruning, proof=proof)
            if res == "tschirnhaus":
                # random T of degree < n with small coefficients in every degree (Lemma 9.2 / Schwartz-Zippel)
                state.tschirnhaus_T = [rng.randint(-3, 3) for _ in range(n)]      # degree <= n-1
                if all(c == 0 for c in state.tschirnhaus_T[1:]):
                    state.tschirnhaus_T[-1] = 1                                      # never constant
                state._apply_tschirnhaus()
                if verbose:
                    print(f"    multiple rational root -> Tschirnhaus T = {state.tschirnhaus_T}")
                continue
            if res is not None:
                res["T"] = state.tschirnhaus_T            # the (R, v, B) of the record refer to T(alpha)
                state.tschirnhaus_T = None; state._apply_tschirnhaus()
                return res
            verdict = "negative"
            state.last_classes.append(state.last_pair_record)
            break
        state.tschirnhaus_T = None
        state._apply_tschirnhaus()
        if verdict != "negative":
            raise ArithmeticError(f"class of maximal subgroups of order {len(V)} remained inconclusive: G = U is not certified")
    return None

def _test_pair(state: DescentState, U: FrozenSet[Perm], V: FrozenSet[Perm], verbose: bool,
               use_pruning: bool = True, invariant_variant: int = 0, k_multiplier: int = 1,
               proof: str = "resolvent"):
    """Diagnosis knobs (defaults = production behavior):
    use_pruning=False disables the the coset filter and dismissal (B2 probe);
    invariant_variant>=1 replaces the invariant by an alternative (B4 probe);
    k_multiplier=2 doubles the working precision (B5 probe)."""
    n, p = state.n, state.p
    tau = getattr(state, "pruning_tau", None) or state.tau
    Ug, Vg = inv.generating_set(U, n), inv.generating_set(V, n)
    N_idx = len(U) // len(V)
    # invariant with verified stabilizer (A3)
    rec = state.ic.invariant(Ug, Vg, n, variant=invariant_variant)
    F = rec["F"]
    # pruning (coset filter by the certified element)
    Nrm = normalizer(U, V, n)
    reps = coset_reps(U, Nrm)
    surviving = [s for s in reps if inv.compose(inv.inverse(s), inv.compose(tau, s)) in V] if use_pruning else list(reps)
    if not surviving:                       # A2: tau ∈ G lies in no conjugate of V, so neither does G
        if verbose:
            print(f"    V order {len(V):4d} idx {N_idx:3d} | dismissed by pruning: tau in no conjugate (0/{len(reps)})")
        state.last_pair_record = {"kind": "dismissed_by_pruning", "V_gens": Vg}
        return None
    # precisions (recognition and proof precisions)
    B = state.bound_B(F)
    k_rec, k_prf = state.k_rec(B), state.k_prf(B, N_idx)
    k2 = k_rec + max(4, k_rec // 2)
    if proof == "probabilistic":
        # recognition-only mode (recognition and proof precisions ablation): work at k2, no exact resolvent, no proof.
        # Positive = some surviving coset recognizes the same integer at two precisions;
        # negative = none does. The negative verdict is HEURISTIC (no completeness), and
        # the emitted step carries no R: the independent checker cannot accept it.
        state.ensure_precision(k_multiplier * k2 + 2)
        K = state.K
        Ncos = coset_reps(U, V)
        allowed = [s for s in Ncos if any(inv.compose(inv.inverse(r), s) in Nrm for r in surviving)]
        for s in allowed:
            g = state.evaluate(inv.act(s, F))
            if not state.image_check(g):
                continue
            v1, v2 = state.symmetric_remainder(g, k_rec), state.symmetric_remainder(g, k2)
            if v1 == v2:
                if verbose:
                    print(f"    V order {len(V):4d} idx {N_idx:3d} [probabilistic] recognized v={v1} at k_rec={k_rec}, k2={k2}")
                return {"V": V, "V_gens": Vg, "sigma": s, "v": v1, "k_rec": k_rec, "k2": k2, "k_prf": k_prf, "K": K,
                        "B": B, "F": F, "index": N_idx, "type": rec["type"], "pruned": (len(surviving), len(reps)),
                        "R": None, "R_prime_at_v": None, "invariant_verification": rec.get("verification", {}).get("ok"),
                        "proof": "probabilistic"}
        state.last_pair_record = {"kind": "negative_probabilistic", "V_gens": Vg, "K": K, "k_rec": k_rec, "k2": k2}
        if verbose:
            print(f"    V order {len(V):4d} idx {N_idx:3d} [probabilistic] no recognition | pruning {len(surviving)}/{len(reps)}")
        return None
    state.ensure_precision(k_multiplier * max(k_prf, k2) + 2)
    K = state.K
    # all coset values at full precision (for the exact resolvent) — cosets of V, not of N_U(V)
    all_cosets = coset_reps(U, V)
    values = {s: state.evaluate(inv.act(s, F)) for s in all_cosets}
    # exact resolvent
    R_A = hf.poly_from_roots(state.A, [values[s] for s in all_cosets])
    assert all(state.image_check(c) for c in R_A), "resolvent coefficient not in Z_p: G not contained in U?"
    R = [state.symmetric_remainder(c, K) for c in R_A]
    dR = [i * R[i] for i in range(1, len(R))]
    def ev(poly, x):
        acc = 0
        for c in reversed(poly):
            acc = acc * x + c
        return acc
    # candidates from every coset (completeness of the integer-root list), with the two-precision check
    integer_roots = {}
    for s in all_cosets:
        g = values[s]
        if not state.image_check(g):
            continue
        v1, v2 = state.symmetric_remainder(g, k_rec), state.symmetric_remainder(g, k2)
        if v1 != v2:
            continue                      # not an integer of size <= 2^B: not a value in Z
        if ev(R, v1) == 0:
            integer_roots.setdefault(v1, []).append(s)
    if verbose:
        print(f"    V order {len(V):4d} idx {N_idx:3d} type {rec['type']:3s} deg {rec['degree']:2d} terms {rec['terms']:3d} "
              f"| pruning {len(surviving)}/{len(reps)} conjugates | k_rec={k_rec} k2={k2} k_prf={k_prf} K={K} "
              f"| integer roots of R: {sorted(integer_roots)}")
    if not integer_roots:
        state.last_pair_record = {"kind": "negative_resolvent", "V_gens": Vg, "F": F, "T": state.tschirnhaus_T, "B": B,
                                  "K": K, "k_prf": k_prf, "R": R}
        return None                       # negative verdict for this class
    simple = [(v, cs) for v, cs in integer_roots.items() if ev(dR, v) != 0]
    if not simple:
        if getattr(state, "accept_multiple_roots", False):        # B6 demo: the historical unsound behavior
            v, cosets = next(iter(integer_roots.items()))
            s = cosets[0]
            return {"V": V, "V_gens": Vg, "sigma": s, "v": v, "k_rec": k_rec, "k2": k2, "k_prf": k_prf, "K": K, "B": B,
                    "F": F, "index": N_idx, "type": rec["type"], "pruned": (len(surviving), len(reps)), "R": R,
                    "R_prime_at_v": 0, "invariant_verification": rec.get("verification", {}).get("ok"),
                    "integer_roots_of_R": sorted(integer_roots)}
        return "tschirnhaus"              # every integer root is multiple: inconclusive
    v, cosets = simple[0]
    # identification: unique coset with value ≡ v needs K > v_p(R'(v)) (Hensel uniqueness); raise precision if not
    need = _vp(ev(dR, v), p) + 1
    if need > K:
        state.ensure_precision(need + 2)
        return _test_pair(state, U, V, verbose, use_pruning, invariant_variant, k_multiplier)
    assert len(cosets) == 1, "identification failed although K > v_p(R'(v))"
    s = cosets[0]
    # the coset of N_U(V) containing s must survive the filter (pruning safety, Lemma 9.3)
    s_class = next(r for r in reps if inv.compose(inv.inverse(r), s) in Nrm)
    assert s_class in surviving, "pruning discarded a coset containing G: tau is not in G?!"
    return {"V": V, "V_gens": Vg, "sigma": s, "v": v, "k_rec": k_rec, "k2": k2, "k_prf": k_prf, "K": K, "B": B, "F": F,
            "index": N_idx, "type": rec["type"], "pruned": (len(surviving), len(reps)),
            "R": R, "R_prime_at_v": ev(dR, v), "invariant_verification": rec.get("verification", {}).get("ok"),
            "integer_roots_of_R": sorted(integer_roots)}


# ----------------------------------------------------------------------------
# driver: W -> G
# ----------------------------------------------------------------------------

def validate_input(f: List[int]) -> None:
    """clean errors for violated preconditions (previously: an infinite prime
    search on non-squarefree f, an opaque A6 assert on reducible f)."""
    n = len(f) - 1
    if n < 2 or f[-1] != 1:
        raise ValueError("f must be monic of degree >= 2 (coefficients low -> high)")
    from fractions import Fraction
    import verify_roots as vr
    if len(vr._gcd_Q([Fraction(c) for c in f], [Fraction(j * f[j]) for j in range(1, n + 1)])) > 1:
        raise ValueError("f is not squarefree (disc f = 0): no prime is admissible")
    import family_compositions as fc                      # lazy: fc imports this module
    if not fc.is_irreducible_Z(f):
        raise ValueError("f is reducible over Q: the subfield lattice machinery assumes K_f is a field")


def run_descent(f: List[int], K: int = 120, verbose: bool = True, use_pruning: bool = True,
                start: str = "subfield", proof: str = "resolvent") -> Dict:
    n = len(f) - 1
    validate_input(f)
    state = DescentState(f, K)
    if start == "Sn":
        report_A6 = {"subfields": []}
        W = inv.closure(inv.S_n(n), n)
    else:
        # starting group W from A6, in the same labelling (same prime, same roots)
        report_A6 = sf.run_A6(f, K=max(state.K, 120), p=state.p)   # the lattice needs healthy precision; labelling is K-independent
        systems = [sf_["blocks"] for sf_ in report_A6["subfields"] if 1 < len(sf_["blocks"]) < n]
        W = frozenset(sf.starting_group_bruteforce(n, systems))
    assert tuple(state.tau) in W
    if verbose:
        print(f"f = {f}, p = {state.p}, tau = {state.tau} (cycle type {inv_cycle(state.tau)}), |W| = {len(W)}")
    U = W
    steps = []
    while True:
        U_gens_before = inv.generating_set(U, n)
        res = descend(state, U, verbose, use_pruning=use_pruning, proof=proof)
        if res is None:
            break
        V, s = res["V"], res["sigma"]
        U = conjugate(V, s)
        steps.append({k: res[k] for k in ("v", "k_rec", "k2", "k_prf", "K", "index", "type", "pruned", "R_prime_at_v", "F", "R", "B", "T")}
                     | {"sigma": s, "new_order": len(U), "U_gens": U_gens_before, "U_next_gens": inv.generating_set(U, n)})
        if verbose:
            print(f"  -> G <= sigma V sigma^-1 of order {len(U)}: sigma={s}, v={res['v']}, k_rec={res['k_rec']}, k2={res['k2']} (agree), type {res['type']}")
    if verbose:
        print(f"  G = U of order {len(U)} (no maximal subgroup contains G)")
    return {"f": f, "p": state.p, "tau": state.tau, "W_order": len(W), "G_order": len(U), "G_gens": inv.generating_set(U, n), "steps": steps,
            "terminal_classes": state.last_classes, "invariant_table": state.ic.stats, "state": state, "A6": report_A6, "W": W}

def inv_cycle(t):
    return hf.cycle_type(t)


if __name__ == "__main__":
    examples = {
        "x^3-3x+1 (C3)":                 ([1, -3, 0, 1], 3),
        "x^4-x^3+x^2-x+1 (C4)":          ([1, -1, 1, -1, 1], 4),
        "x^4-2 (D4)":                    ([-2, 0, 0, 0, 1], 8),
        "x^5-2 (F20)":                   ([-2, 0, 0, 0, 0, 1], 20),
        "x^5-5x+12 (D5)":                ([12, -5, 0, 0, 0, 1], 10),
        "x^5-x-1 (S5)":                  ([-1, -1, 0, 0, 0, 1], 120),
    }
    results = {}
    for name, (f, expected) in examples.items():
        print("=" * 100)
        print(name)
        r = run_descent(f)
        ok = r["G_order"] == expected
        print(f"  expected |G| = {expected}: {'OK' if ok else 'MISMATCH'}")
        results[name] = (r["G_order"], expected, ok)
    print("=" * 100)
    print(json.dumps({k: {"computed": a, "expected": b, "ok": c} for k, (a, b, c) in results.items()}, indent=2))
