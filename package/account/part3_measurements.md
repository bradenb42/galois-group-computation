# Measurements

How the three checks depend on the degree, the height or discriminant
valuation, and the index of the largest step. All data is in
`measurements/measurements.json`; every figure is regenerated from the
configuration by `python3 reproduce_figures.py` (`--remeasure` re-runs the
sweeps).

## 1. Degree

**Check 1, compositions** (`figures/fig1_check1_degree.png`). Wall-clock over the 143
checked compositions, by composed degree: medians 0.3 s (n = 4, 39 runs),
3.2 s (n = 6, 63 runs), 18.2 s (n = 8, 41 runs). The growth is driven not by
n itself but by the group sizes n forces: the starting group W from the subfield lattice, its
subgroup enumeration (memoised and conjugacy-transported after the first
representative of each class), and the coset counts of the descent. The wide
spread within n = 8 (0.4 s to ~300 s before caching) is exactly the spread of
|W| from 16 to 384.

**Check 2, Eisenstein polynomials** (`figures/fig2_check2_degree.png`, left panel). Wall-clock over
the 78 Eisenstein polynomials by degree, marked by prime. Two regimes are
visible: the pure classes x^n − g^j p are near-instant at every degree (the
roots ζ^k α are exact, no Newton iteration), while the random Eisenstein
representatives grow with n and with s_0 = ord_n(p) ,  the arithmetic runs in
F_{p^{s_0}}-modules, so Q_2 at n = 11 (s_0 = 10, |G| = 110) is the most
expensive cell (~8 s), and the overall maximum is 17.6 s. Degree enters
through n·s_0 = |G| and the module rank, not on its own.

**Check 3, sparse pencils** (`figures/fig3_check3_degree.png`). Wall-clock versus MV for the
recorded sparse pencils, annotated with the starting-group order
|A_cl| = d·ord_d(q) and the splitting degree s at the chosen point. The
annotation is the finding: d = 13 (16 s) runs an order of magnitude faster
than d = 11 (122 s) despite the larger degree. The two starting groups are
almost the same size (|A_cl| = 52 against 55), so the separation comes from
s, which is 4 against 5: every root coordinate is an s-tuple, and the
subgroup lattice and chain length follow the multiplier order c = ord_d(q).
MV enters only through the evaluation width. This is why the proven classification bound
A_cl, replacing the S_n start, is what makes MV = 40 reachable at all.

## 2. Height and discriminant valuation

**Height sweep** (`figures/fig4_height_sweep.png`). For the fixed shape
f = x^5 − c with c from 2 to 10^12 + 39 (all runs choosing p = 3, so the
slope is not confounded by the prime), the maximum k_prf over the run grows
affinely in log₂ H:

    log₂H :   1.0    2.8    6.7   13.3   19.9   29.9   39.9
    k_prf :    81    134    273    524    775   1152   1530

with empirical slope 37.3 digits per bit of height. This is what the bound
k_prf = ⌊N(B+1)/log₂p⌋+1 predicts: B is affine in log₂ of the root bound,
which is affine in log₂ H, and N, the index of the step, is fixed along the
sweep. The behaviour is observed over nine decades of height at a constant
group (every run certifies |G| = 20). Wall-clock grows
from 1 s to 20 s: linear in k_prf times the quasi-quadratic cost of p-adic
arithmetic at that precision.

**Discriminant valuation** (`figures/fig2_check2_degree.png`, right panel).
Across all 78 tame Eisenstein polynomials, the computed v_p(disc f) lies
exactly on the line n − 1: the different identity Σ(|G_i| − 1) = |G_0| − 1
for the tame filtration, verified by exact integer discriminants (E7). In the
tame stratum the discriminant valuation is thus a function of the degree
alone, and its "dependence" is this identity; In the wild stratum the valuation grows and drives
precision; the implemented case-2 machinery covers the tame stratum.

## 3. The index of the largest step

**Index collapse** (`figures/fig5_index_collapse.png`). Every step from a
mixed set of descents (subfield and S_n starts, indices N = 2, 3, 6) plotted
as k_prf against N(B+1)/log₂p: all points lie on y = ⌊x⌋+1 ,  asserted
exactly, not fitted. Consequences read off the harvest: the largest-index
step dictates the precision of the entire run (x^5−5x+12: the index-6 step
needs k_prf = 157 while its index-2 companion needs 56; the run's precision
and cost are set by the former), and moving the start from W to S_n raises
the largest index and thus the whole budget (Φ_10: max k_prf 4 → 9). Since B carries the invariant
degree, the point-stabilizer invariants act on this axis: replacing a
degree-C(n,2) invariant by one of degree 1 at point-stabilizer pairs
collapses N(B+1) for exactly the pairs that would otherwise dominate.

## 4. Reproduction

`config/configuration.json` freezes the family definitions, the sweep
(shape, coefficient list, K = 6), the harvest examples, and the seeds.
`reproduce_figures.py` regenerates every figure from the recorded
measurements; `--remeasure` re-runs the height sweep and index harvest from
the configuration and re-reads the three results files (which
`code/family_*.py` can extend, resumably, at any time).