"""
ablation.py — the ablation matrix

    {pruning on, off} x {subfield start, S_n start} x {proof by resolvent,
    probabilistic only} x {ring: Z, F_q(t)}

against the columns: steps, surviving cosets per step, k_rec and k_prf per
step, certificate size, checker time, prover wall-clock.  Each ablation is
confirmed to change exactly the quantity the derivations predict:

  P1 pruning off      -> surviving cosets rise from c_tau to c_0 (coset pruning by a certified element); terminal
                         dismissals become negative resolvents, so the CERTIFICATE
                         GROWS; the group and the k-columns are unchanged.
  P2 S_n start        -> MORE STEPS (the chain termination is longer from S_n than from W)
                         and a larger total k_prf (top-level invariants have higher
                         degree); the group is unchanged.
  P3 probabilistic    -> per-step working precision drops from ~k_prf to ~k2 (recognition and proof precisions),
                         the certificate shrinks (no R) and the independent checker
                         REJECTS it (the certificate and its checker: no proof, nothing to verify); the computed
                         group is unchanged on these inputs (correct whp, not certified).
  P4 ring             -> the precision formulas themselves change (approximation rings and precision/recognition and proof precisions): over Z,
                         k_prf = floor(N(B+1)/log2 p)+1 (archimedean defect eps = 1,
                         log p scaling); over F_q(t), k_prf = floor(N B)+1 exactly
                         (ultrametric, eps = 0).  Confirmed against the records.

O_K row: no descent is implemented for case 2 (tame certification only), reported
as out of scope.
"""

from __future__ import annotations

import itertools
import json
import math
import time
from typing import Dict, List

import checker
import constant_field as cf
import descent as ds
import family_sparse as fs
import invariants as inv
import permgroup as pg
from diagnose import _step_json, _make_cert
from artifact import _poly_json


def _terminal_json(classes, U_gens, n):
    out = []
    for c in classes:
        e = {"kind": c["kind"], "V_gens": [list(g) for g in c["V_gens"]]}
        if c["kind"] == "negative_resolvent":
            e |= {"F": _poly_json(c["F"]), "T": c["T"], "K": c["K"], "R": c["R"]}
        out.append(e)
    return {"kind": "negative_resolvents", "U_gens": [list(g) for g in U_gens], "classes": out}


def run_cell_Z(f: List[int], use_pruning: bool, start: str, proof: str) -> Dict:
    t0 = time.perf_counter()
    r = ds.run_descent(f, K=6, verbose=False, use_pruning=use_pruning, start=start, proof=proof)
    wall = time.perf_counter() - t0
    st = r["state"]
    n = len(f) - 1
    cert = {"derivation_version": "ablation", "run_id": "ablation", "config_hash": "ablation",
            "header": {"case": 1, "f": f, "p": st.p, "s": st.s, "m": list(st.A.mod), "K": st.K,
                       "roots": [list(map(int, x)) for x in st.roots_raw]},
            "lattice": {"subfields": [{"degree": s_["degree_over_Q"], "b": s_["primitive_element"], "h": s_["min_poly"],
                                       "blocks": s_["blocks"]} for s_ in r["A6"]["subfields"]],
                        "U0_gens": [list(g) for g in inv.generating_set(r["W"], n)], "U0_certificate": "type_bound"},
            "steps": [_step_json(s_, n) for s_ in r["steps"]],
            "terminal": _terminal_json(r["terminal_classes"], [tuple(x) for x in r["G_gens"]], n),
            "claimed_group_order": r["G_order"]}
    blob = json.dumps(cert)
    t1 = time.perf_counter()
    try:
        checker.check(cert)
        verdict = "ACCEPT"
    except checker.Reject as e:
        verdict = f"REJECT ({str(e)[:34]}…)"
    t_check = time.perf_counter() - t1
    return {"G": r["G_order"], "steps": len(r["steps"]),
            "surviving": [s_["pruned"] for s_ in r["steps"]],
            "k_rec": [s_["k_rec"] for s_ in r["steps"]], "k_prf": [s_["k_prf"] for s_ in r["steps"]],
            "k_used": [s_["K"] for s_ in r["steps"]], "B": [s_["B"] for s_ in r["steps"]],
            "terminal_dismissed": sum(1 for c in r["terminal_classes"] if c["kind"] == "dismissed_by_pruning"),
            "terminal_kinds": sorted({c["kind"] for c in r["terminal_classes"]}),
            "cert_bytes": len(blob), "checker": verdict, "checker_s": round(t_check, 3), "wall_s": round(wall, 2)}


def run_cell_Fqt(use_pruning: bool, start: str, proof: str) -> Dict:
    f_t = [[0, 6], [0], [0], [0], [1]]                      # x^4 - t over F_7
    t0 = time.perf_counter()
    state = cf.FqtState(f_t, 7, 1, 12)
    if start == "subfield":                                  # the proven fibration bound (A_cl)
        labels, _ = fs.fibration_labels(state, 4)
        _, U0 = fs.classification_groups(labels, 4, 1, 7)
    else:
        U0 = pg.closure(inv.S_n(4), 4)
    try:
        G, steps = cf.galois_group_Fqt(state, e=1, verbose=False, U0=U0, use_pruning=use_pruning, proof=proof)
    except (ArithmeticError, AssertionError) as e:
        # the predicted failure mode of recognition-only proof over F_q(t): a degenerate
        # coincidence (e.g. the block sum x_0 + x_2 = 0 in F_7[t]) is accepted as a positive,
        # the descent derails, and the structural asserts stop it. Over F_q(t) the k_rec
        # window is exactly the truncation, so the two-precision check is vacuous there —
        # the exact-resolvent proof carries all the soundness.
        return {"G": "-", "steps": "-", "surviving": "-", "k_rec": "-", "k_prf": "-", "k_used": "-", "B": "-",
                "terminal_dismissed": "-", "terminal_kinds": "-", "cert_bytes": "n/a",
                "checker": "DERAILED (wrong positive; assert)", "checker_s": "-",
                "wall_s": round(time.perf_counter() - t0, 2), "derailed": True}
    wall = time.perf_counter() - t0
    return {"G": len(G), "steps": len(steps), "derailed": False,
            "surviving": [s_["pruned"] for s_ in steps],
            "k_rec": [s_["k_rec"] for s_ in steps], "k_prf": [s_["k_prf"] for s_ in steps],
            "k_used": ["-"] * len(steps), "B": [s_["B"] for s_ in steps], "index": [s_["index"] for s_ in steps],
            "terminal_dismissed": "-", "terminal_kinds": "-",
            "cert_bytes": "n/a", "checker": "n/a (no case-3 emitter/checker)", "checker_s": "-", "wall_s": round(wall, 2)}


def main():
    cells: Dict = {}
    print("=" * 132)
    print("ring Z — Phi_10 = x^4-x^3+x^2-x+1 (W = D_4 < S_4, tau = id) and x^5-2 (W = S_5, tau a 4-cycle)")
    print("-" * 132)
    hdr = f"{'f':8s} {'prune':5s} {'start':8s} {'proof':13s} | {'G':>3s} {'st':>2s} {'surviving':16s} {'k_rec':10s} {'k_prf':10s} {'k_used':10s} {'cert B':>7s} {'checker':28s} {'chk s':>6s} {'wall s':>6s}"
    print(hdr)
    for name, f in (("Phi_10", [1, -1, 1, -1, 1]), ("x^5-2", [-2, 0, 0, 0, 0, 1])):
        for pr, stt, prf in itertools.product((True, False), ("subfield", "Sn"), ("resolvent", "probabilistic")):
            c = run_cell_Z(f, pr, stt, prf)
            cells[("Z", name, pr, stt, prf)] = c
            print(f"{name:8s} {str(pr):5s} {stt:8s} {prf:13s} | {c['G']:3d} {c['steps']:2d} {str(c['surviving']):16s} "
                  f"{str(c['k_rec']):10s} {str(c['k_prf']):10s} {str(c['k_used']):10s} {c['cert_bytes']:7d} {c['checker']:28s} "
                  f"{c['checker_s']:6} {c['wall_s']:6}")
    print("-" * 132)
    print("ring F_q(t) — x^4 - t over F_7 (arithmetic group D_4 of order 8; 'subfield start' = the proven fibration bound A_cl)")
    for pr, stt, prf in itertools.product((True, False), ("subfield", "Sn"), ("resolvent", "probabilistic")):
        c = run_cell_Fqt(pr, stt, prf)
        cells[("Fqt", "x^4-t", pr, stt, prf)] = c
        print(f"{'x^4-t':8s} {str(pr):5s} {stt:8s} {prf:13s} | {str(c['G']):>3s} {str(c['steps']):>2s} {str(c['surviving']):16s} "
              f"{str(c['k_rec']):10s} {str(c['k_prf']):10s} {str(c['k_used']):10s} {str(c['cert_bytes']):>7s} {c['checker']:28s} "
              f"{str(c['checker_s']):>6s} {c['wall_s']:6}")
    print("-" * 132)
    print("ring O_K: no descent implemented (case 2 provides tame certification only) — out of scope for the matrix")
    print("=" * 132)

    # ---- confirmations -------------------------------------------------------
    ok = []
    g = lambda ring, name, pr, stt, prf: cells[(ring, name, pr, stt, prf)]
    # P1 pruning (x^5-2, resolvent, subfield): surviving per step c_tau -> c_0; terminal dismissals -> 0; cert grows; G, k unchanged
    a, b = g("Z", "x^5-2", True, "subfield", "resolvent"), g("Z", "x^5-2", False, "subfield", "resolvent")
    ok.append(("P1 pruning: surviving cosets rise (c_tau -> c_0) and only there",
               all(x[0] < x[1] or x[0] == x[1] for x in a["surviving"]) and
               all(x[0] == x[1] for x in b["surviving"]) and
               any(x[0] < x[1] for x in a["surviving"]) and
               a["terminal_dismissed"] > 0 and b["terminal_dismissed"] == 0 and
               b["cert_bytes"] > a["cert_bytes"] and a["G"] == b["G"] and a["k_prf"] == b["k_prf"]))
    # P2 start (Phi_10, pruning on, resolvent): more steps and larger total k_prf from S_n; G unchanged
    a, b = g("Z", "Phi_10", True, "subfield", "resolvent"), g("Z", "Phi_10", True, "Sn", "resolvent")
    ok.append(("P2 start: S_n start lengthens the chain and its total k_prf",
               b["steps"] > a["steps"] and sum(b["k_prf"]) > sum(a["k_prf"]) and b["cert_bytes"] > a["cert_bytes"] and a["G"] == b["G"]))
    # P3 proof (x^5-2, pruning on, subfield): k_used drops to ~k2 << k_prf, cert shrinks, checker rejects, G unchanged
    a, b = g("Z", "x^5-2", True, "subfield", "resolvent"), g("Z", "x^5-2", True, "subfield", "probabilistic")
    ok.append(("P3 proof: probabilistic mode works at k2 << k_prf, shrinks the certificate, and is NOT checkable",
               all(ku < kp for ku, kp in zip(b["k_used"], b["k_prf"])) and
               all(ku >= kp for ku, kp in zip(a["k_used"], a["k_prf"])) and
               b["cert_bytes"] < a["cert_bytes"] and a["checker"] == "ACCEPT" and b["checker"].startswith("REJECT") and
               a["G"] == b["G"] and b["wall_s"] <= a["wall_s"] + 0.5))
    # P4 ring: the k_prf formulas differ as derived (recomputed from the recorded B)
    az = g("Z", "x^5-2", True, "subfield", "resolvent")
    st = ds.DescentState([-2, 0, 0, 0, 0, 1], 6)
    z_formula = all(kp == int(math.floor(6 * (B + 1) / math.log2(st.p))) + 1 for kp, B in zip(az["k_prf"], az["B"]))
    aq = g("Fqt", "x^4-t", True, "Sn", "resolvent")     # S_n start has actual steps to inspect
    from fractions import Fraction
    q_formula = (aq["steps"] != "-" and aq["steps"] > 0 and
                 all(kp == math.floor(Fraction(B).limit_denominator(10 ** 4) * idx) + 1
                     for kp, idx, B in zip(aq["k_prf"], aq["index"], aq["B"])))
    # k_prf = floor(N * B) + 1 with eps = 0, N the recorded index, B exact (Fraction) in the prover
    ok.append(("P4 ring: k_prf = floor(N(B+1)/log2 p)+1 over Z but floor(N B)+1 over F_q(t) (eps = 1 vs 0)",
               z_formula and q_formula))
    # P5: probabilistic over F_q(t) derails and is caught (the vacuous k_rec window)
    ok.append(("P5 ring x proof: recognition-only over F_q(t) accepts a degenerate coincidence and DERAILS (caught by asserts)",
               cells[("Fqt", "x^4-t", True, "subfield", "probabilistic")]["derailed"]))
    print()
    for name, passed in ok:
        print(("CONFIRMED  " if passed else "FAILED     ") + name)
    assert all(p for _, p in ok)
    # sanity: the group is identical in every cell of each polynomial
    for nm in ("Phi_10", "x^5-2"):
        assert len({c["G"] for k, c in cells.items() if k[1] == nm}) == 1
    assert len({c["G"] for k, c in cells.items() if k[0] == "Fqt" and not c.get("derailed")}) == 1
    print("group identical across every cell of each row")
    return cells


if __name__ == "__main__":
    main()