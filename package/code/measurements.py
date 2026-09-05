"""
measurements.py — how the three checks depend on the degree, the height or
discriminant valuation, and the index of the largest step.

Datasets (written to measurements.json):

  check1_by_degree   from family_compositions_results.json: (n, height(f), time_s)
  check2_by_degree   from family_eisenstein_results.json: (n, p, v_p(disc), time_s)
  check3_by_degree   from family_sparse_results.json: (MV, |A_cl|, s, time_s)
  height_sweep       fresh controlled runs: f = x^5 - c over growing c;
                     per-run max k_prf and wall-clock (K = 6 so precision is driven
                     by the bounds, not the initial value)
  index_harvest      per-step records (index N, B, k_prf, p) across a fixed set of
                     descents (subfield and S_n starts), for the collapse
                     k_prf = floor(N (B + 1) / log2 p) + 1

Figures (PNG):
  fig1_check1_degree.png     check 1 wall-clock vs composed degree
  fig2_check2_degree.png     check 2 wall-clock vs n, and v_p(disc f) = n - 1
  fig3_check3_degree.png     check 3 wall-clock vs MV, annotated with |A_cl|
  fig4_height_sweep.png      max k_prf and wall-clock vs log2 height
  fig5_index_collapse.png    k_prf vs N(B+1)/log2 p across all harvested steps

The predictions being tested:
  degree: cost grows with the group sizes met (subgroup enumeration, coset counts),
          not with n alone — check 3 makes this visible (|A_cl| = d phi(d) drives it);
  height: B is affine in log2 H (root bound), so k_prf and hence cost grow linearly
          in log2 H at fixed shape (recognition and proof precisions);
  index:  k_prf is EXACTLY floor(N(B+1)/log2 p) + 1 (recognition and proof precisions over Z): all steps collapse
          onto the line y = x (+1 from the floor) — the largest-index step dictates
          the precision of the whole run.
"""

from __future__ import annotations

import json
import math
import time
from typing import Dict, List

MEASUREMENT_CONFIG = {
    "height_sweep": {"shape": "x^5 - c", "cs": [2, 7, 101, 10007, 1000003, 1000000007, 1000000000039], "K": 6},
    "index_examples": [
        {"f": [1, -1, 1, -1, 1], "start": "subfield"}, {"f": [1, -1, 1, -1, 1], "start": "Sn"},
        {"f": [-2, 0, 0, 0, 0, 1], "start": "subfield"},
        {"f": [12, -5, 0, 0, 0, 1], "start": "subfield"},
        {"f": [1, 0, 0, 1, 0, 0, 1], "start": "subfield"},          # Phi_9 = x^6+x^3+1: 12 -> 6
        {"f": [-2, 0, 0, 0, 1], "start": "Sn"},                     # x^4-2 from S_4
    ],
    "K": 6,
    "sources": {"check1": "family_compositions_results.json",
                "check2": "family_eisenstein_results.json",
                "check3": "family_sparse_results.json"},
}


def height(f: List[int]) -> int:
    return max(abs(c) for c in f)


def build(config: Dict = MEASUREMENT_CONFIG, verbose: bool = True) -> Dict:
    import descent as ds
    out: Dict = {"config": config}
    # ---- recorded outcomes ---------------------------------------------------
    c1 = json.load(open(config["sources"]["check1"]))
    out["check1_by_degree"] = [{"n": r["n"], "height": height(r["f"]), "time_s": r["time_s"]}
                               for r in c1 if r["status"] == "ok"]
    c2 = json.load(open(config["sources"]["check2"]))
    out["check2_by_degree"] = [{"n": r["n"], "p": r["p"], "v_p_disc": r["v_p_disc"], "time_s": r["time_s"],
                               "G_order": r["G_order"]} for r in c2["local"] if r.get("status") == "ok"]
    c3 = json.load(open(config["sources"]["check3"]))
    out["check3_by_degree"] = [{"MV": r["MV"], "A_cl_order": r["A_cl_order"], "s": r["s"], "time_s": r["time_s"],
                               "family": r["family"]} for r in c3 if r.get("status") == "ok"]
    # ---- height sweep --------------------------------------------------------
    hs = []
    for c in config["height_sweep"]["cs"]:
        f = [-c, 0, 0, 0, 0, 1]
        t0 = time.perf_counter()
        r = ds.run_descent(f, K=config["height_sweep"]["K"], verbose=False)
        wall = time.perf_counter() - t0
        hs.append({"c": c, "log2H": math.log2(c), "G": r["G_order"],
                   "max_k_prf": max((s_["k_prf"] for s_ in r["steps"]), default=0),
                   "sum_k_prf": sum(s_["k_prf"] for s_ in r["steps"]),
                   "steps": len(r["steps"]), "p": r["state"].p, "time_s": round(wall, 2)})
        if verbose:
            print(f"height sweep c={c:>13d}: |G|={hs[-1]['G']:3d} max k_prf={hs[-1]['max_k_prf']:4d} {wall:6.2f}s")
    out["height_sweep"] = hs
    # ---- index harvest -------------------------------------------------------
    ih = []
    for ex in config["index_examples"]:
        r = ds.run_descent(ex["f"], K=config["K"], verbose=False, start=ex["start"])
        for s_ in r["steps"]:
            ih.append({"f": ex["f"], "start": ex["start"], "index": s_["index"], "B": s_["B"],
                       "k_prf": s_["k_prf"], "p": r["state"].p})
        if verbose:
            print(f"index harvest {ex['f']} ({ex['start']}): {[(s_['index'], s_['k_prf']) for s_ in r['steps']]}")
    out["index_harvest"] = ih
    # the exact recognition and proof precisions formula, checked here as well
    for s_ in ih:
        assert s_["k_prf"] == math.floor(s_["index"] * (s_["B"] + 1) / math.log2(s_["p"])) + 1
    return out


def figures(meas: Dict, outdir: str = "figures", verbose: bool = True) -> List[str]:
    import os
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    os.makedirs(outdir, exist_ok=True)
    paths = []

    def save(fig, name):
        p = os.path.join(outdir, name)
        fig.tight_layout(); fig.savefig(p, dpi=150); plt.close(fig); paths.append(p)
        if verbose:
            print("wrote", p)

    # fig 1: check 1 vs degree
    fig, ax = plt.subplots(figsize=(6, 4))
    d1 = meas["check1_by_degree"]
    import random as _r
    rj = _r.Random(0)
    for r in d1:
        ax.plot(r["n"] + rj.uniform(-0.15, 0.15), r["time_s"], "o", color="tab:blue", alpha=0.35, ms=4)
    for n in sorted({r["n"] for r in d1}):
        ts = sorted(r["time_s"] for r in d1 if r["n"] == n)
        ax.plot(n, ts[len(ts) // 2], "k_", ms=22, mew=2)
    ax.set_yscale("log"); ax.set_xlabel("composed degree n"); ax.set_ylabel("wall-clock (s)")
    ax.set_title("check 1 (compositions): time vs degree (medians marked)")
    save(fig, "fig1_check1_degree.png")

    # fig 2: check 2 vs degree + the different identity
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(9, 4))
    d2 = meas["check2_by_degree"]
    for p, m in ((2, "o"), (3, "s"), (5, "^")):
        xs = [r["n"] for r in d2 if r["p"] == p]; ys = [max(r["time_s"], 0.01) for r in d2 if r["p"] == p]
        ax.plot(xs, ys, m, alpha=0.5, label=f"p = {p}")
    ax.set_yscale("log"); ax.set_xlabel("degree n"); ax.set_ylabel("wall-clock (s)"); ax.legend()
    ax.set_title("check 2 (Eisenstein): time vs degree")
    ax2.plot([r["n"] for r in d2], [r["v_p_disc"] for r in d2], "o", alpha=0.4)
    ns = sorted({r["n"] for r in d2}); ax2.plot(ns, [n - 1 for n in ns], "k-", lw=1, label="v_p(disc) = n - 1")
    ax2.set_xlabel("degree n"); ax2.set_ylabel("v_p(disc f)"); ax2.legend()
    ax2.set_title("the tame different identity")
    save(fig, "fig2_check2_degree.png")

    # fig 3: check 3 vs MV
    fig, ax = plt.subplots(figsize=(6, 4))
    d3 = meas["check3_by_degree"]
    ax.plot([r["MV"] for r in d3], [r["time_s"] for r in d3], "o", color="tab:green")
    for r in d3:
        ax.annotate(f"|A_cl|={r['A_cl_order']}, s={r['s']}", (r["MV"], r["time_s"]),
                    textcoords="offset points", xytext=(4, 3), fontsize=6)
    ax.set_yscale("log"); ax.set_xlabel("MV (= degree of the pencil)"); ax.set_ylabel("wall-clock (s)")
    ax.set_title("check 3 (sparse pencils): |A_cl| = d phi(d) and s drive the cost, not MV alone")
    save(fig, "fig3_check3_degree.png")

    # fig 4: height sweep
    hs = meas["height_sweep"]
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(9, 4))
    ax.plot([h["log2H"] for h in hs], [h["max_k_prf"] for h in hs], "o-")
    ax.set_xlabel("log2 height(f)"); ax.set_ylabel("max k_prf over the run")
    ax.set_title("x^5 - c: k_prf is affine in log2 H")
    ax2.plot([h["log2H"] for h in hs], [h["time_s"] for h in hs], "o-", color="tab:red")
    ax2.set_xlabel("log2 height(f)"); ax2.set_ylabel("wall-clock (s)")
    ax2.set_title("and so is the cost, up to arithmetic overhead")
    save(fig, "fig4_height_sweep.png")

    # fig 5: index collapse
    ih = meas["index_harvest"]
    fig, ax = plt.subplots(figsize=(6, 4))
    xs = [s["index"] * (s["B"] + 1) / math.log2(s["p"]) for s in ih]
    ys = [s["k_prf"] for s in ih]
    ax.plot(xs, ys, "o", alpha=0.6)
    lim = [0, max(xs) * 1.05]
    ax.plot(lim, [x + 1 for x in lim], "k-", lw=1, label="k_prf = floor(x) + 1")
    ax.set_xlabel("N (B + 1) / log2 p   (N = step index)"); ax.set_ylabel("k_prf")
    ax.legend(); ax.set_title("every step collapses onto k_prf = floor(N(B+1)/log2 p) + 1")
    save(fig, "fig5_index_collapse.png")
    return paths


if __name__ == "__main__":
    meas = build()
    with open("measurements.json", "w") as fh:
        json.dump(meas, fh, indent=1)
    figures(meas)