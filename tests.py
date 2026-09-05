"""tests.py — regression tests for run_config.py, hensel_frobenius.py, subfields.py.

Run:  python3 tests.py
"""

from __future__ import annotations

import copy
import dataclasses
import json
import os
import sys
import tempfile
import time
from fractions import Fraction

import hensel_frobenius as hf
import run_config as rc
import subfields as sf

FAILS = []

def check(name, cond, info=""):
    status = "ok  " if cond else "FAIL"
    print(f"[{status}] {name} {info}")
    if not cond:
        FAILS.append(name)

def expect_raise(name, fn, exc=Exception):
    try:
        fn()
    except exc as e:
        print(f"[ok  ] {name}: raised {type(e).__name__}: {str(e)[:60]}")
        return
    print(f"[FAIL] {name}: no exception")
    FAILS.append(name)


# ----------------------------------------------------------------------------
# run_config
# ----------------------------------------------------------------------------
print("== run_config")
with tempfile.TemporaryDirectory() as d:
    for cfg in (rc.example_case1(), rc.example_case2(), rc.example_case3()):
        ctx = rc.start_run(cfg, os.path.join(d, f"case{cfg.coefficient_ring.case}"))
        back = rc.read_run_config(ctx["run_dir"])
        check(f"config roundtrip case {cfg.coefficient_ring.case}", back.content_hash() == cfg.content_hash())
        check("history copy written", os.path.exists(os.path.join(ctx["run_dir"], "config_history", f"{cfg.run_id}.json")))
    # a second run in the same directory must not clobber history
    cfg = rc.example_case1()
    rc.start_run(cfg, os.path.join(d, "case1"))
    check("two history entries after second run", len(os.listdir(os.path.join(d, "case1", "config_history"))) == 2)
expect_raise("case2 rejects frobenius_local", lambda: dataclasses.replace(rc.example_case2(), pruning_sources=["frobenius_local"]).validate(), ValueError)
expect_raise("case2 rejects T2", lambda: dataclasses.replace(rc.example_case2(), terminal_preference=["T2"]).validate(), ValueError)
expect_raise("case1 rejects inertia_tame", lambda: dataclasses.replace(rc.example_case1(), pruning_sources=["inertia_tame"]).validate(), ValueError)
expect_raise("non-monic coefficient count", lambda: rc.Polynomial(degree=3, coefficients=["1", "2"]).validate(rc.CoefficientRing(kind="Z")), ValueError)
expect_raise("composite p rejected", lambda: rc.ApproximationDatum(kind="prime", p=9, residue_degree_s=1).validate(rc.CoefficientRing(kind="Z")), ValueError)

# ----------------------------------------------------------------------------
# hensel_frobenius: ring arithmetic invariants
# ----------------------------------------------------------------------------
print("== hensel_frobenius: rings")
p, K = 7, 20
F = hf.PolyQuot(hf.Zmod(p), hf.irreducible_poly(p, 3), "field")
A = hf.PolyQuot(hf.Zmod(p ** K), hf.irreducible_poly(p, 3), "residue",
                residue=(F, lambda a: tuple(c % p for c in a), lambda x: tuple(x)))
import random
rng = random.Random(5)
ok = True
for _ in range(50):
    a = tuple(rng.randrange(p ** K) for _ in range(3))
    if A.is_unit(a):
        ok &= A.eq(A.mul(a, A.inv(a)), A.one())
    b = tuple(rng.randrange(p ** K) for _ in range(3))
    c = tuple(rng.randrange(p ** K) for _ in range(3))
    ok &= A.eq(A.mul(a, A.add(b, c)), A.add(A.mul(a, b), A.mul(a, c)))   # distributivity
    ok &= A.eq(A.mul(a, b), A.mul(b, a))
check("A: inverses, distributivity, commutativity", ok)
# Frobenius of A is a ring automorphism of order s = 3
m_A = [A.from_int(c) for c in A.mod]
phi_z, _ = hf.newton_root(A, m_A, A.pow(A.gen(), p))
phi = lambda x: hf._peval(A, [A.from_base(c) for c in x], phi_z)
a = tuple(rng.randrange(p ** K) for _ in range(3)); b = tuple(rng.randrange(p ** K) for _ in range(3))
check("phi multiplicative", A.eq(phi(A.mul(a, b)), A.mul(phi(a), phi(b))))
check("phi^3 = id on A", A.eq(phi(phi(phi(a))), a))
check("phi != id on A", not A.eq(phi(A.gen()), A.gen()))
# power series ring: Newton inversion and a unit-derivative lift
S = hf.PolyQuot(F, [F.zero()] * 15 + [F.one()], "constant")
u = S.gen()
one_plus_u = S.add(S.one(), u)
inv = S.inv(one_plus_u)
check("series inverse of 1+u", S.eq(S.mul(inv, one_plus_u), S.one()))
# sqrt(1+u) in F_{7^3}[[u]]: root of y^2 - (1+u) from y0 = 1
rt, it = hf.newton_root(S, [S.neg(one_plus_u), S.zero(), S.one()], S.one())
check("series sqrt(1+u)", S.eq(S.mul(rt, rt), one_plus_u), f"(iterations={it})")

print("== hensel_frobenius: cases")
r = hf.case1([-2, 0, 0, 1], p=7, K=30)
check("case1 x^3-2 @7: 3-cycle", r["cycle_type"] == [3])
r = hf.case1([-2, 0, 1], p=7, K=30)
check("case1 x^2-2 @7 (s=1): trivial", r["tau_frobenius"] == [0, 1] and r["s"] == 1)
expect_raise("case1 rejects p | disc (x^2-2 @2)", lambda: hf.case1([-2, 0, 1], p=2, K=10), ArithmeticError)
r = hf.case2([-5, 0, 0, 1], p=5, K=10)
check("case2 x^3-5 /Q5: S_3, inertia 3-cycle", r["group_order_generated"] == 6 and r["inertia_cycle_type"] == [3])
r = hf.case2([5, 5, 0, 1], p=5, K=10)
check("case2 x^3+5x+5 /Q5: S_3, Newton actually iterates", r["group_order_generated"] == 6 and max(r["newton_iterations"]) > 0)
r = hf.case2([-3, 0, 0, 0, 1], p=3, K=10)
check("case2 x^4-3 /Q3: D_4", r["group_order_generated"] == 8 and r["inertia_cycle_type"] == [4])
expect_raise("case2 rejects non-Eisenstein (x^3-2 @5)", lambda: hf.case2([-2, 0, 0, 1], p=5, K=8), AssertionError)
expect_raise("case2 rejects wild (x^2-2 @2)", lambda: hf.case2([-2, 0, 1], p=2, K=8), AssertionError)
r = hf.case3([[1], [0, 1], [0], [1]], p=5, t0=1, K=20)
check("case3 x^3+tx+1 /F5 @1: 3-cycle", r["cycle_type"] == [3])
r = hf.case3([[0, -1], [0], [1]], p=5, t0=4, K=20)
check("case3 x^2-t @4 (square): trivial, s=1", r["tau_frobenius"] == [0, 1] and r["s"] == 1)
expect_raise("case3 rejects disc f(t0)=0 (x^2-t @0)", lambda: hf.case3([[0, -1], [0], [1]], p=5, t0=0, K=10), ArithmeticError)
# shift polynomial: a(t0+u) agrees with direct evaluation at a few points
a = [3, 1, 4, 1]
au = hf._shift_poly_t(7, a, 2)
Fp = hf.Zmod(7)
check("_shift_poly_t consistent", all(hf._peval(Fp, au, (x - 2) % 7) == hf._peval(Fp, a, x) for x in range(7)))

# ----------------------------------------------------------------------------
# subfields
# ----------------------------------------------------------------------------
print("== subfields: exact helpers")
check("disc(x^2-2) = 8", sf.discriminant([Fraction(-2), Fraction(0), Fraction(1)]) == 8)
check("disc(x^3-2) = -108", sf.discriminant([Fraction(-2), Fraction(0), Fraction(0), Fraction(1)]) == -108)
Kf = sf.Kf([-2, 0, 0, 1])
al = Kf.from_vec([0, 1, 0])
check("K_f: alpha^3 = 2", Kf.eq(Kf.pow(al, 3), Kf.from_vec([2, 0, 0])))
check("K_f: inverse", Kf.eq(Kf.mul(al, Kf.inv(al)), Kf.one()))
U = [[Fraction(1), Fraction(0), Fraction(0)], [Fraction(0), Fraction(1), Fraction(0)]]
V = [[Fraction(0), Fraction(1), Fraction(0)], [Fraction(0), Fraction(0), Fraction(1)]]
check("subspace intersection", sf.intersect_subspaces(U, V, 3) == [[Fraction(0), Fraction(1), Fraction(0)]])
B = sf.lll([[7 ** 12, 0, 0], [-5, 1, 0], [-25 % 7 ** 12, 0, 1]])
check("lll preserves lattice determinant", abs(sf.det_fraction([[Fraction(x) for x in r] for r in B])) == 7 ** 12)

print("== subfields: recognition and full runs")
A, F, proj, roots, phi, tau, s = sf.roots_and_frobenius([-2, 0, 0, 0, 0, 1], p=3, K=120)
rec = sf.KfRecognizer(A, roots[0], 1, 3, 120, 5)
gamma = A.add(A.mul(roots[0], roots[0]), A.from_int(3))
check("recognize alpha^2+3 with D=1", rec.recognize(gamma) == [Fraction(3), 0, Fraction(1), 0, 0])
check("image check rejects conjugate root", rec.recognize(roots[1]) is None)
t0 = time.time()
expected = {
    "x4+1":       ([1, 0, 0, 0, 1],       3, 4),     # (proper systems, |W|)
    "x4-2":       ([-2, 0, 0, 0, 1],      1, 8),
    "x6+2x4+x2-2": ([-2, 0, 1, 0, 2, 0, 1], 2, 12),
    "x5-2":       ([-2, 0, 0, 0, 0, 1],   0, 120),
    "x6-2":       ([-2, 0, 0, 0, 0, 0, 1], 2, 12),   # Q(2^{1/6}): subfields Q(2^{1/2}), Q(2^{1/3}); W = S_3 x S_2 = Gal(f)
}
for name, (f, nsys, worder) in expected.items():
    rep = sf.run_A6(f)
    sg = rep["starting_group"]
    check(f"run_A6 {name}: #systems={sg['num_proper_block_systems']} |W|={sg['W_order_bruteforce']} tau in W",
          sg["num_proper_block_systems"] == nsys and sg["W_order_bruteforce"] == worder and sg["tau_in_W"] and sg["tau_in_chain_wreath"],
          f"(p={rep['p']}, tau cycle type {rep['tau_cycle_type']}, factor degrees {rep['factor_degrees']})")
    # every block system is preserved by tau and the subfield degrees multiply to n per block
    n = rep["n"]
    check(f"run_A6 {name}: block sizes", all(len(b) * sf_["degree_over_Q"] == n for sf_ in rep["subfields"] for b in sf_["blocks"]))
print(f"   (full runs took {time.time() - t0:.1f}s)")


# ----------------------------------------------------------------------------
# invariants (A3)
# ----------------------------------------------------------------------------
print("== invariants")
import invariants as inv
with tempfile.TemporaryDirectory() as d:
    ic = inv.InvariantConstructor(os.path.join(d, "inv.json"))
    r = ic.invariant(inv.S_n(4), inv.A_n(4), 4)
    check("S4>A4: type III, 12 terms, verified incl. mod 2", r["type"] == "III" and r["terms"] == 12 and r["verification"]["ok"])
    r = ic.invariant([inv.cyc(4, (0, 2)), inv.cyc(4, (1, 3)), inv.cyc(4, (0, 1), (2, 3))], [inv.cyc(4, (0, 2)), inv.cyc(4, (1, 3))], 4)
    check("D4>K: type I block sum", r["type"] == "I" and r["F"] in ({(1, 0, 0, 0): 1, (0, 0, 1, 0): 1}, {(0, 1, 0, 0): 1, (0, 0, 0, 1): 1}))
    r = ic.invariant([inv.cyc(8, (0, 1)), inv.cyc(8, (0, 1, 2, 3)), inv.cyc(8, (0, 4), (1, 5), (2, 6), (3, 7))],
                     [inv.cyc(8, (0, 1)), inv.cyc(8, (2, 3)), inv.cyc(8, (0, 2), (1, 3)), inv.cyc(8, (4, 5)), inv.cyc(8, (6, 7)),
                      inv.cyc(8, (4, 6), (5, 7)), inv.cyc(8, (0, 4), (1, 5), (2, 6), (3, 7))], 8)
    check("S4wrS2>(D4xD4):C2: type II, index 9, deg <= delta", r["type"] == "II" and r["index"] == 9 and r["degree"] <= r["delta"])
    ic2 = inv.InvariantConstructor(os.path.join(d, "inv.json"))
    r2 = ic2.invariant(inv.S_n(4), inv.A_n(4), 4)
    check("table hit on second constructor", r2["source"] == "table" and r2["F"] == r["F"] or r2["source"] == "table")
    # the sign-based invariant Π(x_i - x_j) separates A_4 over Z but NOT mod 2 (ring-independent invariants motivation)
    n = 4
    vand = {tuple([0] * n): 1}
    for i in range(n):
        for j in range(i + 1, n):
            lin = {tuple(1 if k == i else 0 for k in range(n)): 1, tuple(1 if k == j else 0 for k in range(n)): -1}
            vand = inv.pmul(vand, lin)
    rep = inv.verify_stabilizer(inv.S_n(4), 24, inv.A_n(4), 12, vand, 4)
    check("Vandermonde: stabilizer A4 over Z but fails mod 2", rep["Z"]["ok"] and not rep["mod2"]["ok"])
    # a symmetric polynomial is not a U-relative V-invariant
    sym = {tuple(1 if k == i else 0 for k in range(n)): 1 for i in range(n)}
    check("symmetric polynomial rejected", not inv.verify_stabilizer(inv.S_n(4), 24, inv.A_n(4), 12, sym, 4)["ok"])
    # separating monomial: trivial stabilizer in the chain wreath product S2 wr S2 wr S2 on 8 points
    chain = [inv._canon([{i} for i in range(8)]), inv._canon([{0,1},{2,3},{4,5},{6,7}]), inv._canon([{0,1,2,3},{4,5,6,7}]), inv._canon([set(range(8))])]
    e, delta, br = inv.separating_monomial(chain, 8)
    W = inv.closure([inv.cyc(8,(0,1)), inv.cyc(8,(2,3)), inv.cyc(8,(4,5)), inv.cyc(8,(6,7)), inv.cyc(8,(0,2),(1,3)), inv.cyc(8,(4,6),(5,7)), inv.cyc(8,(0,4),(1,5),(2,6),(3,7))], 8)
    stab = sum(1 for g in W if tuple(inv.act(g, {e: 1}).keys())[0] == e)
    check("separating monomial: trivial stabilizer in S2wrS2wrS2, degree = delta", stab == 1 and sum(e) == delta == 4*1 + 2*1 + 1 and br == [2, 2, 2])


# ----------------------------------------------------------------------------
# descent (descend(U) with pruning and the two-precision check)
# ----------------------------------------------------------------------------
print("== descent")
import descent as ds
t0 = time.time()
for name, f, expected in [("x^3-3x+1 C3", [1, -3, 0, 1], 3), ("Phi_10 C4", [1, -1, 1, -1, 1], 4), ("x^4-2 D4", [-2, 0, 0, 0, 1], 8),
                          ("x^5-2 F20", [-2, 0, 0, 0, 0, 1], 20), ("x^5-5x+12 D5", [12, -5, 0, 0, 0, 1], 10)]:
    r = ds.run_descent(f, verbose=False)
    check(f"descent {name}: |G| = {r['G_order']}", r["G_order"] == expected,
          f"(steps {[(s['index'], s['type'], s['pruned']) for s in r['steps']]})")
    check(f"descent {name}: every step recognized v at two precisions", all(s["k2"] > s["k_rec"] for s in r["steps"]))
print(f"   (descents took {time.time() - t0:.1f}s)")
# pruning safety: with a wrong 'Frobenius' the step must not silently succeed
st = ds.DescentState([-2, 0, 0, 0, 0, 1], 120)
W = inv.closure(inv.S_n(5), 5)
st.tau = (1, 0, 2, 3, 4)     # a transposition, not in F20 = Gal(x^5-2): must be caught
def bad():
    ds.descend(st, W, verbose=False)
expect_raise("descent with a wrong tau is caught (pruning safety / inconclusive)", bad, (AssertionError, ArithmeticError))


# ----------------------------------------------------------------------------
# verify_roots (A5 in the three rings)
# ----------------------------------------------------------------------------
print("== verify_roots")
import verify_roots as vr
# Z: R = (x-3)(x+5)(x^2+1) = x^4 + 2x^3 - 14x^2 + 2x - 15 ; roots bounded by 2^4
R = [-15, 2, -14, 2, 1]
rep = vr.verify_Z(R, 3, 4.0)
check("Z: integer roots found by linear-factor lifting only", rep["integer_roots"] == [-5, 3] and rep["v_simple"] and not rep["no_other_integer_root"],
      f"(ell={rep['ell']}, ddf={rep['factorization_mod_ell']['distinct_degree']})")
rep = vr.verify_Z([1, 0, 1], 0, 1.0)            # x^2+1: no integer root
check("Z: negative verdict for x^2+1", rep["integer_roots"] == [] and rep["no_other_integer_root"] and not rep["v_is_root"])
rep = vr.verify_Z([-3, 0, 1], 0, 0.8)           # x^2-3 with B so small that 2^B < sqrt(3): candidates must be discarded, none accepted
check("Z: spurious lifts discarded by the size filter", rep["integer_roots"] == [] and all("discarded" in c[1] or c[1] == "not a root" for c in rep["candidates"]))
rep = vr.verify_Z([-4, 0, 1], 2, 2.0)           # x^2-4: ell must avoid 2 (R mod 2 = x^2 not squarefree)
check("Z: auxiliary prime avoids non-squarefree reduction", rep["ell"] != 2 and rep["integer_roots"] == [-2, 2])
# O_K: synthetic R(y) = (y - 9)(y - 10)(y - 1) over Z_3, v = 9: v(R'(9)) = v(-1*8) = 0, lambda2 = 0 -> certified at any m >= 1
R_OK = [-90, 9 * 10 + 9 * 1 + 10 * 1, -(9 + 10 + 1), 1]
rep = vr.verify_OK(R_OK, 9, 3, 5, 1, 5)
check("O_K: simple root certified by the Newton polygon", rep["simple_root_certified"] and rep["v(c1)"] == 0)
# R(y) = (y-9)(y-18)(y-1): roots 9,18 congruent mod 9: lambda2 = v(18-9) = 2, v(c1)=v((9-18)(9-1))=2 -> need m > 4
R_OK2 = [-(9 * 18 * 1), 9 * 18 + 9 + 18, -(9 + 18 + 1), 1]
rep_lo = vr.verify_OK(R_OK2, 9, 3, 4, 1, 4); rep_hi = vr.verify_OK(R_OK2, 9, 3, 6, 1, 6)
check("O_K: precision threshold m > v(c1)+lambda2 is sharp", (not rep_lo["simple_root_certified"]) and rep_hi["simple_root_certified"] and rep_hi["lambda2"] == 2.0)
# F_p[t]: R = (x - t^2)(x + t)(x^2 + t x + 1) over F_5  (monic in x)
Fpt = vr.Fpt(5)
fac = [[[0, 0, 4], [1]], [[0, 1], [1]], [[1], [0, 1], [1]]]     # x - t^2, x + t, x^2 + t x + 1
Rx = [[1]]
for g in fac:
    new = [[] for _ in range(len(Rx) + len(g) - 1)]
    for i, a in enumerate(Rx):
        for j, b in enumerate(g):
            new[i + j] = Fpt.add(new[i + j], Fpt.mul(a, b))
    Rx = new
rep = vr.verify_Fqt(Rx, [0, 0, 1], 5, 2.0)
check("F_p[t]: ring roots via point lifting, v = t^2 simple", rep["v_is_root"] and rep["v_simple"] and sorted(rep["ring_roots"]) == sorted([[0, 0, 1], [0, 4]]),
      f"(t1={rep['t1']}, ddf={rep['factorization_at_t1']['distinct_degree']}, k_prf={rep['k_prf']})")
rep = vr.verify_Fqt(Rx, [0, 1], 5, 2.0)
check("F_p[t]: non-root reported", not rep["v_is_root"])


# ----------------------------------------------------------------------------
# artifact: certificate + independent checker (case 1)
# ----------------------------------------------------------------------------
print("== artifact")
import artifact, copy, dataclasses
base = rc.example_case1()
for name, coeffs, expected in [("Phi_10", [1, -1, 1, -1], 4), ("x^5-5x+12", [12, -5, 0, 0, 0], 10)]:
    cfg = dataclasses.replace(base, polynomial=rc.Polynomial(degree=len(coeffs), coefficients=[str(c) for c in coeffs]),
                              family_check=rc.FamilyCheck(), invariant_table_path="tables/invariants_descent.json")
    with tempfile.TemporaryDirectory() as d:
        path = artifact.run(cfg, d); cert = json.load(open(path))
        res = artifact.check_certificate(cert)
        check(f"artifact {name}: checker accepts, |G| = {res['G_order']}", res["verdict"] == "ACCEPT" and res["G_order"] == expected)
        bad = copy.deepcopy(cert); bad["steps"][0]["v"] += 1
        expect_raise(f"artifact {name}: tampered v rejected", lambda: artifact.check_certificate(bad), artifact.Reject)
        bad = copy.deepcopy(cert); bad["terminal"]["classes"].pop()
        expect_raise(f"artifact {name}: dropped terminal class rejected", lambda: artifact.check_certificate(bad), artifact.Reject)
        bad = copy.deepcopy(cert); bad["claimed_group_order"] += 1
        expect_raise(f"artifact {name}: wrong claimed order rejected", lambda: artifact.check_certificate(bad), artifact.Reject)
# non-squarefree resolvent handled by verify_Z
R = [45, -21, -1, 1]           # (x-3)^2 (x+5)
rep = vr.verify_Z(R, -5, 3.0)
check("verify_Z: non-squarefree R, roots via squarefree part, simplicity exact", not rep["squarefree"] and rep["integer_roots"] == [-5, 3] and rep["v_simple"] and not vr.verify_Z(R, 3, 3.0)["v_simple"])
# complete maximal-subgroup enumeration: C2^4 (non-2-generated maximal subgroups)
U = inv.closure([inv.cyc(8, (0, 1)), inv.cyc(8, (2, 3)), inv.cyc(8, (4, 5)), inv.cyc(8, (6, 7))], 8)
check("maximal_subgroup_classes: C2^4 has 15 maximal subgroups of order 8", [len(S) for S in ds.maximal_subgroup_classes(U, 8)] == [8] * 15)


# ----------------------------------------------------------------------------
# standalone checker + exhaustive single-entry mutation test
# ----------------------------------------------------------------------------
print("== checker / mutations")
import subprocess, checker, mutate
src = open("checker.py").read()
check("checker.py imports only permgroup from the project", all(l.split()[1] in ("json", "math", "sys", "permgroup") for l in src.splitlines() if l.startswith("import ")) and "from fractions" in src and "from typing" in src and all(("from " + m) not in src for m in ("descent", "invariants", "subfields", "hensel_frobenius", "verify_roots", "artifact", "run_config")))
for name in ("phi10", "x4m2"):
    path = f"certs/{name}/certificate.json"
    r = subprocess.run([sys.executable, "checker.py", path], capture_output=True, text=True)
    check(f"checker executable accepts {name}", r.returncode == 0 and r.stdout.startswith("ACCEPT"))
    cert = json.load(open(path))
    total = rejected = 0; wrong = []
    for pth, val in list(mutate.leaves(cert)):
        if isinstance(val, bool) or not isinstance(val, (int, str)) and val is not None:
            continue
        nv = (val + 1) if isinstance(val, int) else (val + "x" if isinstance(val, str) else 0)
        m = copy.deepcopy(cert); mutate.set_path(m, pth, nv); total += 1
        try:
            checker.check(m); acc = True
        except Exception:
            acc = False
        if not acc: rejected += 1
        elif not mutate.benign(pth, val, m): wrong.append(pth)
    check(f"mutations {name}: {rejected}/{total} rejected, rest benign", not wrong, f"(wrongly accepted: {wrong})")
r = subprocess.run([sys.executable, "checker.py", "/dev/null"], capture_output=True, text=True)
check("checker executable rejects a non-certificate", r.returncode == 1)


# ----------------------------------------------------------------------------
# A7: constant field degree over F_q(t)
# ----------------------------------------------------------------------------
print("== constant field (A7)")
import constant_field as cf
t0 = time.time()
for name, f_t, p, pt, exp in [("x^3-t^2/F_5", [[0, 0, 4], [0], [0], [1]], 5, 1, (6, 3, 2)),
                              ("x^3-t^2/F_7", [[0, 0, 6], [0], [0], [1]], 7, 1, (3, 3, 1)),
                              ("x^2-2/F_5 (constant)", [[3], [0], [1]], 5, 0, (2, 1, 2)),
                              ("x^4-t/F_7", [[0, 6], [0], [0], [0], [1]], 7, 1, (8, 4, 2)),
                              ("x^4-t/F_5", [[0, 4], [0], [0], [0], [1]], 5, 1, (4, 4, 1))]:
    r = cf.run_A7(f_t, p, pt, verbose=False)
    got = (r["G_order"], r["G_geom_order"], r["constant_field_degree_c"])
    check(f"A7 {name}: (|G|, |G_geom|, c) = {got}", got == exp and r["all_checks_pass"], f"(s = {r['s']}, tau {r['tau_cycle_type']})")
print(f"   (A7 runs took {time.time() - t0:.1f}s)")


# ----------------------------------------------------------------------------
# A10 check 1: compositions (fast smoke subset; the full run is family_compositions_results.json)
# ----------------------------------------------------------------------------
print("== compositions (A10 check 1)")
import family_compositions as fc
check("compose strips leading zeros", fc.compose([-2, 0, 1], [0, 0, 1]) == [-2, 0, 0, 0, 1])
irr_cases = [([1, 0, 0, 0, 1], True), ([1, 2, 1], False), ([1, 0, 1, 0, 1], False), ([4, 4, 1], False), ([1, 1, 0, 0, 0, 0, 1], True)]
check("is_irreducible_Z unit cases", all(fc.is_irreducible_Z(f) == e for f, e in irr_cases))
r = fc.check_composition([-2, 0, 1], [1, 0, 1])       # (x^2+1)^2 - 2: D_4
check("composition (x^2+1)^2-2: P1-P3, |G| = 8", r["status"] == "ok" and r["G_order"] == 8 and r["P1_fibres_in_lattice"]
      and r["P2_block_quotient_is_Gal_g"] and r["P3_order_factorization"] and r["P3_G_in_L_wr_piG"])
res = json.load(open("family_compositions_results.json"))
oks = [x for x in res if x["status"] == "ok"]
check(f"full family run: {len(oks)} checked / {len(res)} recorded, P1-P3 universal",
      len(res) == 184 and len(oks) == 143
      and all(x["P1_fibres_in_lattice"] for x in oks)
      and all(x["P2_block_quotient_is_Gal_g"] for x in oks if x["P2_block_quotient_is_Gal_g"] is not None)
      and all(x["P3_order_factorization"] and x["P3_G_in_L_wr_piG"] for x in oks)
      and all(x.get("matches_known", True) for x in oks))
xs = [x for x in oks if x["X_local_group_in_Gal_h"] is not None]
check("literal wreath claim fails exactly on the h = x^3-3x+1 and h = x^4+1 families",
      sorted({tuple(x["h"]) for x in xs if not x["X_local_group_in_Gal_h"]}) == [(1, -3, 0, 1), (1, 0, 0, 0, 1)])
# subgroup cache conjugacy transport
U1 = inv.closure([inv.cyc(6, (0, 1)), inv.cyc(6, (0, 1, 2)), inv.cyc(6, (3, 4)), inv.cyc(6, (4, 5))], 6)
subs1 = ds.all_subgroups(U1, 6)
U2 = ds.conjugate(U1, (3, 4, 5, 0, 1, 2))
subs2 = ds.all_subgroups(U2, 6)
check("subgroup cache: conjugate transport", len(subs1) == len(subs2) and all(S <= U2 for S in subs2))


# ----------------------------------------------------------------------------
# A10 check 2: Eisenstein polynomials over Q_2, Q_3, Q_5 (fast smoke subset)
# ----------------------------------------------------------------------------
print("== Eisenstein (A10 check 2)")
import family_eisenstein as fe
check("tame/wild degree split", fe.tame_degrees(2) == [3, 5, 7, 9, 11] and fe.wild_degrees(3) == [3, 6, 9, 12]
      and len(fe.pure_representatives(5, 4)) == 4 and len(fe.pure_representatives(2, 9)) == 1)
r = fe.check_one([-3, 0, 0, 0, 1], 3)      # x^4 - 3 over Q_3: C_4 x_3 C_2 = D_4, order 8
check("x^4-3 over Q_3: |G| = 8 = n*s0, E1-E7", r["ok"] and r["G_order"] == 8 and r["s0_theory"] == 2)
r = fe.check_one([-10, 0, 0, 0, 0, 0, 0, 0, 1], 5)   # x^8 - 10 over Q_5: order 16
check("x^8-10 over Q_5: |G| = 16, tame polygon", r["ok"] and r["G_order"] == 16 and r["E6_polygon_multiset"] == [0] * 7)
r = fe.check_one([-2, 2, -2, 1], 2)        # random-shape Eisenstein cubic over Q_2: S_3
check("Eisenstein cubic over Q_2: |G| = 6", r["ok"] and r["G_order"] == 6)
res = json.load(open("family_eisenstein_results.json"))
loc, cross = res["local"], res["global_cross_check"]
oks = [x for x in loc if x.get("status") == "ok"]
check(f"full Eisenstein run: {len(oks)} checked, 12 wild out of scope, all E1-E7",
      len(oks) == 78 and sum(1 for x in loc if str(x.get('status','')).startswith('skipped')) == 12 and all(x["ok"] for x in oks))
check("global cross-check: local embeds in global everywhere; proper at Q_5 n=4",
      all(x["local_embeds_in_global"] for x in cross)
      and all((x["local_order"] == x["global_order"]) == (not (x["p"] == 5 and x["n"] == 4)) for x in cross))


# ----------------------------------------------------------------------------
# rejection localization (diagnose)
# ----------------------------------------------------------------------------
print("== diagnose")
import diagnose as dg
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
cert = dg._make_cert([1, -1, 1, -1, 1], bad_invariant)
rep = dg.diagnose(cert, verbose=False, state_hook=bad_invariant)
check("diagnose localizes a broken invariant to B4", rep["localization"] == ["B4 (invariant)"],
      f"(results: { {k: v[:20] for k, v in rep['results'].items()} })")
def bad_pruning(state):
    t = list(state.tau); t[0], t[1] = t[1], t[0]
    state.pruning_tau = tuple(t)
cert = dg._make_cert([1, -1, 1, -1, 1], bad_pruning)
rep = dg.diagnose(cert, verbose=False, state_hook=bad_pruning)
check("diagnose localizes a broken pruning element to B2", rep["localization"] == ["B2 (pruning)"])
# a tampered record must be identified as record corruption (baseline accepts)
cert = dg._make_cert([1, -1, 1, -1, 1])
cert["steps"][0]["v"] += 1
rep = dg.diagnose(cert, verbose=False)
check("diagnose identifies record corruption via the baseline column", rep["localization"][0].startswith("record corruption"))
# an intact certificate needs no diagnosis
rep = dg.diagnose(dg._make_cert([1, -1, 1, -1, 1]), verbose=False)
check("diagnose accepts an intact certificate", rep["verdict"] == "ACCEPT")


# ----------------------------------------------------------------------------
# ablation matrix (runs its own confirmation asserts)
# ----------------------------------------------------------------------------
print("== ablation matrix")
import contextlib, io
import ablation
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    cells = ablation.main()
out = buf.getvalue()
check("ablation matrix: all predictions confirmed", out.count("CONFIRMED") == 5 and "FAILED" not in out,
      f"({out.count('CONFIRMED')} confirmed)")
check("ablation matrix: 24 cells recorded", len(cells) == 24)


# ----------------------------------------------------------------------------
# package integrity
# ----------------------------------------------------------------------------
print("== package")
import os
need_files = ["package/README.md", "package/reproduce_figures.py", "package/config/configuration.json",
              "package/account/part1_derivations.md", "package/account/part2_guarantees_and_validation.md",
              "package/account/part3_measurements.md", "package/measurements/measurements.json",
              "package/certificates/phi10/certificate.json", "package/code/checker.py"] + \
             [f"package/figures/fig{i}_" for i in range(1, 6)]
have = all(os.path.exists(p) if not p.endswith("_") else
           any(x.startswith(os.path.basename(p)) for x in os.listdir("package/figures")) for p in need_files)
check("package: account, config, results, certificates, figures, measurements, reproduce script present", have)
m = json.load(open("package/measurements/measurements.json"))
import math as _m
check("measurements: every harvested step satisfies the k_prf formula",
      all(s["k_prf"] == _m.floor(s["index"] * (s["B"] + 1) / _m.log2(s["p"])) + 1 for s in m["index_harvest"]))
check("measurements: height sweep is monotone in k_prf and constant in G",
      all(a["max_k_prf"] < b["max_k_prf"] for a, b in zip(m["height_sweep"], m["height_sweep"][1:]))
      and len({h["G"] for h in m["height_sweep"]}) == 1)

print()
print("ALL PASSED" if not FAILS else f"FAILURES: {FAILS}")