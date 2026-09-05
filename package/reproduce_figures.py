#!/usr/bin/env python3
"""Reproduce every figure of the package from the configuration.

    python3 reproduce_figures.py               # regenerate figures from measurements/measurements.json
    python3 reproduce_figures.py --remeasure   # re-run the measurements from config/configuration.json
                                               # (fresh height sweep + index harvest; the three family
                                               # results are read as recorded and can be extended with
                                               # code/family_*.py), then regenerate the figures
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "code"))

if "--remeasure" in sys.argv:
    import measurements as M
    cfg = json.load(open(os.path.join(HERE, "config", "configuration.json")))["measurements"]
    cfg["sources"] = {k: os.path.join(HERE, "results", os.path.basename(v)) for k, v in cfg["sources"].items()}
    os.chdir(os.path.join(HERE, "code"))                       # the prover reads tables/ relative paths
    os.makedirs("tables", exist_ok=True)
    for t in ("invariants.json", "invariants_descent.json"):
        src = os.path.join(HERE, "tables", t)
        if os.path.exists(src) and not os.path.exists(os.path.join("tables", t)):
            import shutil
            shutil.copy(src, os.path.join("tables", t))
    meas = M.build(cfg)
    json.dump(meas, open(os.path.join(HERE, "measurements", "measurements.json"), "w"), indent=1)
    print("re-measured")
    os.chdir(HERE)

import measurements as M
meas = json.load(open(os.path.join(HERE, "measurements", "measurements.json")))
M.figures(meas, outdir=os.path.join(HERE, "figures"))
print("all figures reproduced in figures/")
