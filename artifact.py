"""
artifact.py — the case-1 artifact: configuration -> run -> certificate -> independent check.

run(config, run_dir):
    writes config.json (run_config.start_run), runs the subfield computation and the descent, and
    writes certificate.json with the structure of the certificate format:
      header   f, p, s, m (the irreducible modulus of O_q), K, approximate roots
      lattice  subfields (integral primitive element, minimal polynomial, blocks)
               and the starting group U_0 with its type-bound certificate
      steps    (U_i gens, U_{i+1} gens, F_i, sigma_i, v_i, k_i, T_i, R_i)
      terminal negative resolvents / pruning dismissals for every class of
               maximal subgroups of U_ell (the prover's list)

check_certificate(cert):
    wrapper around checker.py, the independent checker of the checker conditions C0-C6 (a separate
    executable sharing only permgroup.py with the prover), which recomputes
    everything from witnesses:
      C0 roots (squarefree reduction, distinct residues, f(alpha^)=0), Frobenius tau
      C1 subfields (h_L(b_L)=0 exactly, deg h_L = #blocks, disc h_L != 0,
         blocks recomputed at precision K > v_p(disc h_L)/2), U_0 <= W by
         generators and |U_0| = type bound with all n points (block systems from subfields (b))
      C2 Stab_{U_i}(F_i) = sigma_i^{-1} U_{i+1} sigma_i by orbit counting (Z, mod 2, mod 3)
      C3 sigma_i F_i(T_i(alpha^)) ≡ v_i mod p^{k_i}
      C4 k_i >= k_prf(N_i, B_i) with B_i recomputed from F_i, f and T_i
      C5 R_i recovered exactly, R_i(v_i) = 0, R_i'(v_i) != 0, v_p(R_i'(v_i)) < k_i
      C6 the checker's own list of maximal-subgroup classes of U_ell must be
         covered by the supplied terminal records; each record is re-verified
         (dismissal: tau in no conjugate; negative: resolvent recomputed, no
         integer root by verify_Z)
    Nothing supplied by the prover is trusted except as a witness.
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction
from typing import Dict, List

import descent as ds
import hensel_frobenius as hf
import invariants as inv
import run_config as rc
import subfields as sf
import verify_roots as vr


# ----------------------------------------------------------------------------
# prover side
# ----------------------------------------------------------------------------

def _poly_json(F): return [[list(e), c] for e, c in sorted(F.items())]
def _poly_load(L): return {tuple(e): c for e, c in L}

def run(config: rc.RunConfig, run_dir: str, verbose: bool = False) -> str:
    assert config.coefficient_ring.kind == "Z", "artifact.run implements case 1 (Z); cases 2 and 3 are covered by hensel_frobenius/verify_roots only"
    ctx = rc.start_run(config, run_dir)
    f = [int(c) for c in config.polynomial.coefficients] + [1]
    K0 = config.precision_policy.fixed_k or 120
    r = ds.run_descent(f, K=K0, verbose=verbose)
    st, A6 = r["state"], r["A6"]
    n = len(f) - 1
    proper = [s_["blocks"] for s_ in A6["subfields"] if 1 < len(s_["blocks"]) < n]
    cert = {
        "derivation_version": rc.DERIVATION_VERSION, "run_id": ctx["run_id"], "config_hash": ctx["config_hash"],
        "header": {"case": 1, "f": f, "p": st.p, "s": st.s, "m": list(st.A.mod), "K": st.K,
                   "roots": [list(map(int, root)) for root in st.roots_raw]},
        "lattice": {"subfields": [{"degree": s_["degree_over_Q"], "b": s_["primitive_element"], "h": s_["min_poly"], "blocks": s_["blocks"]}
                                  for s_ in A6["subfields"]],
                    "U0_gens": [list(g) for g in inv.generating_set(r["W"], n)],
                    "U0_certificate": "type_bound"},
        "steps": [{"U_gens": [list(g) for g in s_["U_gens"]], "U_next_gens": [list(g) for g in s_["U_next_gens"]],
                   "F": _poly_json(s_["F"]), "sigma": list(s_["sigma"]), "v": s_["v"], "k": s_["K"], "T": s_["T"], "R": s_["R"],
                   "type": s_["type"]} for s_ in r["steps"]],
        "terminal": {"kind": "negative_resolvents", "U_gens": [list(g) for g in r["G_gens"]],
                     "classes": [({"kind": c["kind"], "V_gens": [list(g) for g in c["V_gens"]]} if c["kind"] == "dismissed_by_pruning" else
                                  {"kind": c["kind"], "V_gens": [list(g) for g in c["V_gens"]], "F": _poly_json(c["F"]), "T": c["T"], "K": c["K"], "R": c["R"]})
                                 for c in r["terminal_classes"]]},
        "claimed_group_order": r["G_order"],
    }
    path = os.path.join(run_dir, "certificate.json")
    with open(path, "w") as fh:
        json.dump(cert, fh)
    return path


# ----------------------------------------------------------------------------
# checker side: the independent executable checker.py (shares only permgroup.py)
# ----------------------------------------------------------------------------

import checker as _checker

Reject = _checker.Reject

def check_certificate(cert: Dict, verbose: bool = False) -> Dict:
    """delegates to checker.check — the standalone program `python3 checker.py certificate.json`."""
    return _checker.check(cert, verbose)


if __name__ == "__main__":
    import copy, sys, tempfile
    base = rc.example_case1()
    examples = {"x^5-5x+12 (D5)": [12, -5, 0, 0, 0], "x^5-2 (F20)": [-2, 0, 0, 0, 0], "Phi_10 (C4)": [1, -1, 1, -1], "x^4-2 (D4)": [-2, 0, 0, 0]}
    for name, coeffs in examples.items():
        import dataclasses
        cfg = dataclasses.replace(base, polynomial=rc.Polynomial(degree=len(coeffs), coefficients=[str(c) for c in coeffs]),
                                  family_check=rc.FamilyCheck(), invariant_table_path="tables/invariants_descent.json", notes=name)
        with tempfile.TemporaryDirectory() as d:
            path = run(cfg, d)
            cert = json.load(open(path))
            size = os.path.getsize(path)
            try:
                res = check_certificate(cert)
                print(f"{name:20s} |G| = {res['G_order']:3d}  certificate {size/1024:.1f} kB  -> {res['verdict']}")
            except Reject as e:
                print(f"{name:20s} REJECTED: {e}")
            # tampering: a wrong v, and a dropped terminal class, must be rejected
            if cert["steps"]:
                bad = copy.deepcopy(cert); bad["steps"][0]["v"] += 1
                try:
                    check_certificate(bad); print("   tampered v ACCEPTED (BUG)")
                except Reject as e:
                    print(f"   tampered v rejected: {e}")
            if cert["terminal"]["classes"]:
                bad = copy.deepcopy(cert); bad["terminal"]["classes"].pop()
                try:
                    check_certificate(bad); print("   dropped terminal class ACCEPTED (BUG)")
                except Reject as e:
                    print(f"   dropped terminal class rejected: {e}")
