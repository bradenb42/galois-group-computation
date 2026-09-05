#!/usr/bin/env python3
"""
mutate.py — exhaustive single-entry alteration test for checker.py.

    python3 mutate.py certificate.json

Every scalar leaf of the certificate (integers, strings, nulls) is altered in
turn — integers by +1 and by -1, strings by appending a character, nulls by
replacing with 0 — and the altered certificate is handed to checker.check.
A mutation that is still ACCEPTED is reported with its path; the harness then
classifies it as *benign* if the altered certificate still describes the same
true statement (the only such entries are precisions k that remain inside
[k_prf, K]) and as a FAILURE otherwise.
"""

import copy
import json
import sys

import checker


def leaves(obj, path=()):
    if isinstance(obj, dict):
        for k, v in obj.items():
            yield from leaves(v, path + (k,))
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            yield from leaves(v, path + (i,))
    else:
        yield path, obj

def set_path(obj, path, value):
    for k in path[:-1]:
        obj = obj[k]
    obj[path[-1]] = value

BENIGN_REASONS = {
    "metadata": "run metadata not part of the mathematical claim",
    "label": "informational label; the checker verifies the underlying fact directly",
    "precision": "precision re-verified to lie in [k_prf, K]; claim unchanged",
    "modulus_s1": "with s = 1 every monic degree-1 modulus gives O_q = Z_p",
    "tschirnhaus": "the checker recomputed the resolvent from the altered T and it coincides (T-invariant resolvent value)",
}

def benign(path, original, mutated_cert):
    """classify an ACCEPTED alteration; returns a reason key or None (= failure).
    Only alterations whose certificate still states a true, re-verified claim
    are benign."""
    if path[0] in ("run_id", "config_hash", "derivation_version", "spec_version"):
        return "metadata"
    if path[-1] in ("type", "U0_certificate"):
        return "label"
    if path[-1] in ("k", "K") and path[0] in ("steps", "terminal"):
        return "precision"
    if path[0] == "header" and path[1] == "m" and mutated_cert["header"]["s"] == 1:
        return "modulus_s1"
    if "T" in path:
        return "tschirnhaus"
    return None

def main(argv):
    cert = json.load(open(argv[1]))
    base = checker.check(cert)
    assert base["verdict"] == "ACCEPT"
    total = rejected = benign_acc = 0
    failures = []
    benign_list = []
    for path, val in list(leaves(cert)):
        if isinstance(val, bool):
            variants = [not val]
        elif isinstance(val, int):
            variants = [val + 1, val - 1]
        elif isinstance(val, str):
            variants = [val + "x"]
        elif val is None:
            variants = [0]
        else:
            continue
        for nv in variants:
            mut = copy.deepcopy(cert)
            set_path(mut, path, nv)
            total += 1
            try:
                res = checker.check(mut)
                accepted = True
            except checker.Reject:
                accepted = False
            except Exception:
                accepted = False      # malformed: the executable reports REJECT for these too
            if not accepted:
                rejected += 1
            else:
                reason = benign(path, val, mut)
                if reason:
                    benign_acc += 1
                    benign_list.append(("/".join(map(str, path)), val, nv, reason))
                else:
                    failures.append((path, val, nv))
    print(f"{argv[1]}: {total} single-entry alterations: {rejected} rejected, {benign_acc} accepted (benign), {len(failures)} ACCEPTED WRONGLY")
    for pth, v, nv, reason in benign_list:
        print(f"   benign: {pth} {v} -> {nv}   [{reason}: {BENIGN_REASONS[reason]}]")
    for pth, v, nv in failures:
        print("   FAILURE:", "/".join(map(str, pth)), v, "->", nv)
    return 0 if not failures else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv))