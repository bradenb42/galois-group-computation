"""
diagnose.py — rejection localization for case-1 certificates, a companion to checker.py.

When checker.check rejects a certificate, `diagnose(cert)` re-runs the rejected
step prover-side under four controlled variations, one knob at a time:

    B6  proof       fresh Tschirnhaus transformation (new resolvent)
    B5  precision   doubled working precision
    B2  pruning     the coset filter disabled
    B4  invariant   invariant replaced by a verified alternative (variant = 1)

plus a baseline re-run with no variation. For each variant the certificate is
REBUILT from the rejected point on — the varied step, then the remaining
descent and the terminal records under default settings — and handed to the
independent checker again. The report lists which variations produce ACCEPT:

    baseline accepts             -> the record was corrupted (serialization /
                                    tampering); the algorithm is not implicated
    only fresh Tschirnhaus       -> B6 (proof: degenerate resolvent / multiple root)
    only doubled precision       -> B5 (precision: bound or k too small)
    only pruning disabled        -> B2 (pruning: the certified element / filter)
    only alternative invariant   -> B4 (invariant construction)
    none                         -> not localized by these knobs (deeper fault)

Rejections in the header or lattice (C0/C1) are not step-local and are reported
as such; rejections at C6 are treated as a rejection of the "terminal step" and
the same four variations are applied to the terminal enumeration.

The procedure needs the polynomial f (from the certificate header) and re-runs
the prover with the same prime, so the labelling matches the certificate's; the
prefix of accepted steps is kept verbatim.
"""

from __future__ import annotations

import copy
import json
import random
import re
from typing import Dict, List, Optional, Tuple

import checker
import descent as ds
import invariants as inv
import permgroup as pg
import run_config as rc
from artifact import _poly_json, _poly_load


# ----------------------------------------------------------------------------
# locating the rejection
# ----------------------------------------------------------------------------

def locate(reject_msg: str) -> Tuple[str, Optional[int]]:
    """('step', i) | ('terminal', None) | ('global', None)"""
    m = re.match(r"step (\d+):", reject_msg)
    if m:
        return "step", int(m.group(1))
    if reject_msg.startswith("C6") or "terminal" in reject_msg:
        return "terminal", None
    return "global", None


# ----------------------------------------------------------------------------
# prover-side re-run of one step / the terminal, with one knob turned
# ----------------------------------------------------------------------------

VARIATIONS = {
    "baseline":        dict(),
    "fresh_tschirnhaus": dict(fresh_T=True),
    "doubled_precision": dict(k_multiplier=2),
    "pruning_disabled":  dict(use_pruning=False),
    "alternative_invariant": dict(invariant_variant=1),
}
LOCALIZATION = {"fresh_tschirnhaus": "B6 (proof)", "doubled_precision": "B5 (precision)",
                "pruning_disabled": "B2 (pruning)", "alternative_invariant": "B4 (invariant)"}


def _prepare_state(cert: Dict, state_hook=None) -> ds.DescentState:
    H = cert["header"]
    f = H["f"]
    state = ds.DescentState(f, K=H["K"], p=H["p"], table_path="tables/invariants_descent.json")
    # same labelling as the certificate (deterministic in (f, p)); tolerate a
    # higher current precision by comparing modulo the smaller modulus
    Kc = min(state.K, H["K"])
    mod = H["p"] ** Kc
    for ours, theirs in zip(state.roots_raw, H["roots"]):
        assert all((a - b) % mod == 0 for a, b in zip(ours, theirs)), "labelling differs from the certificate"
    if state_hook:
        state_hook(state)                 # a persistent prover fault stays active during diagnosis
    return state

def _run_step(state: ds.DescentState, U, V, variation: Dict, seed: int):
    tries = 5 if variation.get("fresh_T") else 1
    res = "tschirnhaus"
    for a in range(tries):
        if variation.get("fresh_T"):
            rng = random.Random(seed + a)
            state.tschirnhaus_T = [rng.randint(-3, 3) for _ in range(state.n)]
            if all(c == 0 for c in state.tschirnhaus_T[1:]):
                state.tschirnhaus_T[-1] = 1
        else:
            state.tschirnhaus_T = None
        state._apply_tschirnhaus()
        res = ds._test_pair(state, U, V, verbose=False,
                            use_pruning=variation.get("use_pruning", True),
                            invariant_variant=variation.get("invariant_variant", 0),
                            k_multiplier=variation.get("k_multiplier", 1))
        T_used = state.tschirnhaus_T
        state.tschirnhaus_T = None
        state._apply_tschirnhaus()
        if isinstance(res, dict):
            res["T"] = T_used
            return res
        if res is None:
            return None
    return res

def _finish_descent(state: ds.DescentState, U, variation_for_terminal: Optional[Dict] = None):
    """default-descend from U to G, collecting step records and terminal classes;
    if variation_for_terminal is given, its knobs apply to the terminal classes."""
    steps = []
    while True:
        U_gens_before = inv.generating_set(U, state.n)
        if variation_for_terminal is None:
            res = ds.descend(state, U, verbose=False)
        else:
            res = _descend_with_knobs(state, U, variation_for_terminal)
        if res is None:
            break
        Un = ds.conjugate(res["V"], res["sigma"])
        steps.append(dict(res) | {"U_gens": U_gens_before, "U_next_gens": inv.generating_set(Un, state.n)})
        U = Un
    return U, steps, state.last_classes

def _descend_with_knobs(state: ds.DescentState, U, variation: Dict):
    """ds.descend with the variation's knobs applied to every pair (used for the
    terminal localization)."""
    n = state.n
    reps = pg.maximal_subgroup_classes(U, n)
    rng = random.Random(999)
    state.last_classes = []
    for V in reps:
        state.tschirnhaus_T = None
        state._apply_tschirnhaus()
        verdict = "inconclusive"
        for attempt in range(9):
            state.last_pair_record = None
            if variation.get("fresh_T") and attempt == 0:
                state.tschirnhaus_T = [rng.randint(-3, 3) for _ in range(n)]
                if all(c == 0 for c in state.tschirnhaus_T[1:]):
                    state.tschirnhaus_T[-1] = 1
                state._apply_tschirnhaus()
            res = ds._test_pair(state, U, V, verbose=False,
                                use_pruning=variation.get("use_pruning", True),
                                invariant_variant=variation.get("invariant_variant", 0),
                                k_multiplier=variation.get("k_multiplier", 1))
            if res == "tschirnhaus":
                state.tschirnhaus_T = [rng.randint(-3, 3) for _ in range(n)]
                if all(c == 0 for c in state.tschirnhaus_T[1:]):
                    state.tschirnhaus_T[-1] = 1
                state._apply_tschirnhaus()
                continue
            if res is not None:
                res["T"] = state.tschirnhaus_T
                state.tschirnhaus_T = None; state._apply_tschirnhaus()
                return res
            verdict = "negative"
            state.last_classes.append(state.last_pair_record)
            break
        state.tschirnhaus_T = None; state._apply_tschirnhaus()
        if verdict != "negative":
            raise ArithmeticError("inconclusive class under the variation")
    return None


# ----------------------------------------------------------------------------
# certificate reassembly
# ----------------------------------------------------------------------------

def _step_json(s_: Dict, n: int) -> Dict:
    return {"U_gens": [list(g) for g in s_["U_gens"]], "U_next_gens": [list(g) for g in s_["U_next_gens"]],
            "F": _poly_json(s_["F"]), "sigma": list(s_["sigma"]), "v": s_["v"], "k": s_["K"], "T": s_["T"],
            "R": s_["R"], "type": s_["type"]}

def _terminal_json(classes: List[Dict], U_gens, n: int) -> Dict:
    return {"kind": "negative_resolvents", "U_gens": [list(g) for g in U_gens],
            "classes": [({"kind": c["kind"], "V_gens": [list(g) for g in c["V_gens"]]} if c["kind"] == "dismissed_by_pruning" else
                         {"kind": c["kind"], "V_gens": [list(g) for g in c["V_gens"]], "F": _poly_json(c["F"]), "T": c["T"],
                          "K": c["K"], "R": c["R"]}) for c in classes]}

def _rebuild(cert: Dict, locus: str, i: Optional[int], variation: Dict, seed: int = 1234, state_hook=None) -> Dict:
    """certificate with the varied step / terminal and a default-rebuilt suffix."""
    state = _prepare_state(cert, state_hook)
    n = state.n
    new = copy.deepcopy(cert)
    if locus == "step":
        U = pg.closure([tuple(g) for g in cert["steps"][i]["U_gens"]], n)
        V_cert = pg.closure([tuple(g) for g in cert["steps"][i]["U_next_gens"]], n)
        sigma_c = tuple(cert["steps"][i]["sigma"])
        V = ds.conjugate(V_cert, pg.inverse(sigma_c))
        res = _run_step(state, U, V, variation, seed)
        if res == "tschirnhaus":
            raise checker.Reject("variation stayed inconclusive on the pair")
        if res is None:
            # the variation shows the pair is NEGATIVE: the rejected step should never
            # have been positive; continue the descent from U with the variation active
            G, suffix, terminal = _finish_descent(state, U, variation_for_terminal=variation)
            new["steps"] = cert["steps"][:i] + [_step_json(s_, n) for s_ in suffix]
        else:
            Un = ds.conjugate(res["V"], res["sigma"])
            step_rec = dict(res) | {"U_gens": inv.generating_set(U, n), "U_next_gens": inv.generating_set(Un, n)}
            # the variation is applied SYSTEMICALLY (suffix and terminal too): a
            # persistent prover fault breaks the rebuilt suffix as well, and only a
            # knob that repairs the whole chain counts as the localization
            G, suffix, terminal = _finish_descent(state, Un, variation_for_terminal=variation)
            new["steps"] = cert["steps"][:i] + [_step_json(step_rec, n)] + [_step_json(s_, n) for s_ in suffix]
    else:  # terminal
        U = pg.closure([tuple(g) for g in cert["terminal"]["U_gens"]], n)
        G, suffix, terminal = _finish_descent(state, U, variation_for_terminal=variation)
        new["steps"] = cert["steps"] + [_step_json(s_, n) for s_ in suffix]
    new["terminal"] = _terminal_json(terminal, inv.generating_set(G, n), n)
    new["claimed_group_order"] = len(G)
    # the header must carry the final precision and matching roots
    new["header"]["K"] = state.K
    new["header"]["roots"] = [list(map(int, r)) for r in state.roots_raw]
    return new


# ----------------------------------------------------------------------------
# the procedure
# ----------------------------------------------------------------------------

def diagnose(cert: Dict, verbose: bool = True, state_hook=None) -> Dict:
    try:
        checker.check(cert)
        if verbose:
            print("certificate accepted; nothing to diagnose")
        return {"verdict": "ACCEPT", "note": "certificate accepted; nothing to diagnose"}
    except checker.Reject as e:
        msg = str(e)
    locus, i = locate(msg)
    report: Dict = {"rejection": msg, "locus": locus if i is None else f"step {i}", "results": {}, "localization": []}
    if verbose:
        print(f"rejected: {msg}\n  locus: {report['locus']}")
    if locus == "global":
        report["note"] = "rejection is in the header/lattice (C0/C1): not step-local; the four variations do not apply"
        return report
    for name, variation in VARIATIONS.items():
        try:
            patched = _rebuild(cert, locus, i, variation, state_hook=state_hook)
            try:
                res = checker.check(patched)
                report["results"][name] = "ACCEPT"
            except checker.Reject as e2:
                report["results"][name] = f"REJECT: {e2}"
        except (checker.Reject, ArithmeticError, AssertionError) as e2:
            report["results"][name] = f"rebuild failed: {e2}"
        if verbose:
            print(f"  {name:24s} -> {report['results'][name][:100]}")
    if report["results"].get("baseline") == "ACCEPT":
        report["localization"] = ["record corruption (baseline re-run accepts): not B2/B4/B5/B6"]
    else:
        report["localization"] = [LOCALIZATION[k] for k in LOCALIZATION if report["results"].get(k) == "ACCEPT"]
        if not report["localization"]:
            report["localization"] = ["not localized by these variations"]
    if verbose:
        print("  localization:", report["localization"])
    return report


# ----------------------------------------------------------------------------
# demonstrations: four injected prover faults, one per B-code
# ----------------------------------------------------------------------------

def _make_cert(f: List[int], sabotage=None, K: int = 120) -> Dict:
    """run the prover (optionally sabotaged) and return the certificate dict."""
    ds.validate_input(f)
    state = ds.DescentState(f, K, table_path="tables/invariants_descent.json")
    if sabotage:
        sabotage(state)
    import subfields as sf
    report_A6 = sf.run_A6(f, K=max(state.K, 120), p=state.p)   # the lattice needs healthy precision; labelling is K-independent
    n = state.n
    systems = [s_["blocks"] for s_ in report_A6["subfields"] if 1 < len(s_["blocks"]) < n]
    W = frozenset(sf.starting_group_bruteforce(n, systems))
    G, steps, terminal = _finish_descent(state, W)
    proper_subfields = report_A6["subfields"]
    cert = {"derivation_version": rc.DERIVATION_VERSION, "run_id": "diag-demo", "config_hash": "diag-demo",
            "header": {"case": 1, "f": f, "p": state.p, "s": state.s, "m": list(state.A.mod), "K": state.K,
                       "roots": [list(map(int, r)) for r in state.roots_raw]},
            "lattice": {"subfields": [{"degree": s_["degree_over_Q"], "b": s_["primitive_element"], "h": s_["min_poly"],
                                       "blocks": s_["blocks"]} for s_ in proper_subfields],
                        "U0_gens": [list(g) for g in inv.generating_set(W, n)], "U0_certificate": "type_bound"},
            "steps": [_step_json(s_, n) for s_ in steps],
            "terminal": _terminal_json(terminal, inv.generating_set(G, n), n),
            "claimed_group_order": len(G)}
    return cert


if __name__ == "__main__":
    f = [1, -1, 1, -1, 1]                                            # Phi_10: one step D_4 -> C_4
    print("=" * 100)
    print("fault B5 (precision): the bound B is underestimated by 12 bits (initial K too small to mask it)")
    def bad_bound(state):
        orig = state.bound_B
        state.bound_B = lambda F: max(orig(F) - 12.0, 0.5)
    cert = _make_cert([12, -5, 0, 0, 0, 1], bad_bound, K=6)          # x^5-5x+12: large resolvent coefficients
    diagnose(cert, state_hook=bad_bound)
    print("=" * 100)
    print("fault B4 (invariant): the primary invariant construction drops an orbit term (variant 0 only)")
    def bad_invariant(state):
        orig = state.ic.invariant
        def patched(Ug, Vg, n, verify=True, store=True, variant=0):
            if variant != 0:
                return orig(Ug, Vg, n, verify=verify, store=store, variant=variant)
            r = orig(Ug, Vg, n, verify=False, store=False, variant=0)
            if len(r["F"]) > 1:
                F = dict(r["F"]); F.pop(next(iter(F)))
                r = dict(r) | {"F": F}
            r.setdefault("verification", {"ok": False})
            return r
        state.ic.invariant = patched
    cert = _make_cert(f, bad_invariant)
    diagnose(cert, state_hook=bad_invariant)
    print("=" * 100)
    print("fault B2 (pruning): the element used for pruning is not the certified Frobenius")
    def bad_pruning(state):
        t = list(state.tau)
        t[0], t[1] = t[1], t[0]                                       # a non-Galois permutation, pruning-side only
        state.pruning_tau = tuple(t)
    cert = _make_cert(f, bad_pruning)
    diagnose(cert, state_hook=bad_pruning)
    print("=" * 100)
    print("fault B6 (proof): multiple resolvent roots accepted as if simple (the pre-audit bug)")
    def bad_proof(state):
        state.accept_multiple_roots = True
    fired = None
    for f6 in ([2, 0, 4, 0, 1], [2, 0, -4, 0, 1], [2, 0, 2, 0, 1], [2, 0, -2, 0, 1], [-2, 0, 0, 0, 0, 0, 0, 0, 1]):
        try:
            c = _make_cert(f6, bad_proof)
            try:
                checker.check(c)
            except checker.Reject:
                fired = (f6, c); break
        except (AssertionError, ArithmeticError) as e:
            print(f"  f = {f6}: the buggy prover SELF-DESTRUCTS before emitting ({str(e)[:60]})")
    if fired is None:
        print("  finding: on every tested input the degenerate positive step claims G inside a group where the")
        print("  next level's own structural checks (transitivity of U, Z_p-rationality of resolvent coefficients)")
        print("  fail — this fault class cannot reach a certificate here. The fresh-Tschirnhaus column of the")
        print("  procedure remains the localizer for proof-level degeneracy when such a certificate does arise")
        print("  (e.g. via record corruption, where the baseline column identifies it instead).")
    else:
        diagnose(fired[1], state_hook=bad_proof)