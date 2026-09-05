# Guarantees and Validation

This document states what the artifact guarantees, on what trust base, and
records the validation performed. The derivations with proofs are in
`derivations.md`; the measurements in `measurements.md`.

## 1. The guarantee

**Certificate soundness.** Let `cert` be a case-1 certificate for a monic
squarefree `f ∈ Z[x]` of degree n, and suppose the independent checker accepts
(`checker.check(cert)` returns, exit code 0). Then:

1. the header data reconstructs a labelling `α_1, …, α_n` of the roots of f in
   an unramified extension of Z_p at the stated precision, together with the
   Frobenius permutation τ, all re-derived by the checker's own arithmetic
   (check C0);
2. the lattice section exhibits proper subfields with exact minimal-polynomial
   witnesses, re-verified by exact rational arithmetic, whose block systems
   give a starting group `U_0` with `|U_0|` equal to the type bound computed from the block systems, and
   `τ ∈ U_0` (check C1);
3. every step `i` descends `U_i → U_{i+1}` by a resolvent argument the checker
   replays in full: the invariant's stabilizer is recomputed (C2), the claimed
   value satisfies the congruence at the claimed precision (C3), the precision
   lies in the window `[k_prf, K]` recomputed by the checker from its own
   bound `B` (C4), and the resolvent recovered by the checker from the roots
   has the claimed simple integer root identifying the unique coset (C5);
4. the terminal section covers the checker's OWN list of maximal subgroup
   classes of the final group: each class is either dismissed because τ lies in
   no conjugate (re-verified), or refuted by a recomputed resolvent with no
   integer root (C6).

Consequently `Gal(f/Q)`, in the certificate's labelling, is the closure of the
claimed generators: the descent chain pins G from above (each step is a proven
containment) and the terminal from below (no proper maximal subgroup of the
final group contains G, by soundness of the pruning and completeness of the
integer-root list). The unique-lift lemma makes the p-adic identification
exact rather than heuristic: `p^k > 2^{B+1}` turns a congruence into an
equality of integers.

**Scope of the guarantee.** The certified statement covers case-1
certificates end to end: prover, certificate, and independent checker. The
checker accepts only resolvent-proved steps, so recognition-only output is
rejected by design. Case 2 certifies tame Eisenstein data, namely the inertia
and Frobenius elements and the seven structural checks against the explicit
splitting field. Case 3 computes arithmetic and geometric groups by the same
descent logic from proven starting bounds, validated against classification
predictions.

## 2. The trust base

The checker is a standalone executable sharing exactly one module with the
prover: `permgroup.py` (finite permutation-group operations, auditable in
isolation). It re-implements modular arithmetic, `F_{p^s}` arithmetic, exact
rational linear algebra, resultants, discriminants, and integer root finding.
It never reads prover state: everything is recomputed from the certificate
bytes. Accepting a wrong certificate therefore requires a correlated error in
(a) the checker's independent arithmetic, (b) `permgroup.py`, or (c) the
soundness argument itself.

## 3. Validation record

**Mutation testing.** For five certificates (Φ_10 → C_4, x^4−2 → D_4,
x^5−5x+12 → D_5, x^5−2 → F_20, x^8−3 → a group of order 32), every scalar in
the certificate was altered one at a time (289, 232, 1246, 651, and 3412
alterations, 5830 in total). No altered
certificate that changes a load-bearing quantity is accepted; the accepted
alterations are exactly the classified benign ones (metadata, labels,
in-range precision values, the modulus polynomial at s = 1, and
Tschirnhaus-invariant resolvent data). Zero wrong acceptances.

**Check 1: compositions over Q.** All 184 catalogue pairs g∘h of
composed degree ≤ 8: 143 fully checked, 35 skipped with a proof of
reducibility, 6 skipped at the stated group-size cap. In all 143: the fibres of h appear in the computed subfield lattice, the
block quotient equals Gal(g) computed by an independent descent, and
G ≤ L wr Gal(g) with |G| = |block quotient| · |kernel|, where L is the
relative local group. The naive
claim G ≤ Gal(h) wr Gal(g) fails in exactly 11 cases ,  the families
h = x^3−3x+1 (local group S_3 over the cyclic C_3; provable via
disc(h−√2) = 27(1+2√2) of negative norm) and h = x^4+1 ,  extending the known reducible
counterexample to irreducible h. All classically known groups matched.

**Check 2: Eisenstein polynomials over Q_2, Q_3, Q_5.** All 78 tame
polynomials (every isomorphism class x^n − g^j p of every tame degree ≤ 12,
class counts gcd(n, p−1) verified, plus random Eisenstein representatives)
pass all seven checks against the explicit splitting fields
Q_{p^{s_0}}((g^j p)^{1/n}): the relabelled group EQUALS ⟨k↦k+1, k↦pk⟩, the
metacyclic relation holds as permutations, e′ = n, f′ = s_0 = ord_n(p),
|G| = n s_0, the ramification polygon is the tame one in root form, and
v_p(disc f) = n−1 = Σ(|G_i|−1) by exact integer discriminants. The seven
checks are: inertia is an n-cycle with v(α) = 1; residue degree s_0; group
order n·s_0; equality of the relabelled group with the expected metacyclic
group; the metacyclic relation as permutations; the tame ramification polygon
in root form; and the different identity for the discriminant valuation. The
12 wild degrees are recorded as outside the implemented tame case. Global cross-check: for n ≤ 5 the same polynomials over Q have the
local group embedded in the global one up to conjugacy in all 14 cases, with
equality except the four theoretically forced Q_5 quartics (i ∈ Q_5 forces
the local C_4 inside the global D_4).

**Check 3: sparse pencils over F_q(t).** Lacunary and triangular
pencils with MV ≤ 40; descent from the PROVEN bounds
W_cl = C_d wr S_m, A_cl = W_cl ⋊ ⟨q mod d⟩ (the fibration and the μ_d-torsor
structure are defined over F_q(t), and the cyclotomic character lands in
⟨q⟩), which is what makes MV = 40 feasible: at m = 1 the bound has order
d·ord_d(q), so 160 for d = 40 over F_3, against |S_40|. Every pencil checked
so far passes: G_geom = W_cl exactly, G ≤ A_cl with equality of orders,
geometric multipliers trivial, arithmetic multipliers in ⟨q⟩, the certified
Frobenius affine with multiplier exactly q, and c = [G : G_geom] = ord_d(q);
the triangular pencils additionally verify the block quotient against the
independently computed geometric monodromy of the base and the relative
wreath bound. The run is resumable (`code/family_sparse.py <budget_s>`);
`results/family_sparse_results.json` records the current coverage.

**Rejection localization.** `code/diagnose.py`: on a checker rejection at
step i (or terminal), the step is re-run under baseline, fresh Tschirnhaus,
doubled precision, pruning disabled, and an alternative verified invariant , 
applied systemically to the rebuilt suffix ,  and each rebuilt certificate is
re-checked. Injected persistent faults localize to a single accepting column:
an under-estimated bound to the precision column, a corrupted invariant
construction to the invariant column, a wrong pruning element to the pruning
column; tampered records are identified by the baseline column. One finding
is worth recording: the historical multiple-root fault never reaches a
certificate at all, because the bogus step lands in a group where the
prover's own transitivity or rationality checks refuse to continue.

**Ablation matrix.** {pruning} × {start} × {proof} × {ring}, 24 cells; all
five predictions confirmed programmatically: pruning changes only the
surviving-coset counts (c_τ → c_0) and the certificate size; the S_n start
lengthens the chain and its total k_prf; probabilistic proof works at
k_2 ≪ k_prf, shrinks the certificate, and is rejected by the checker; the
precision formulas are ring-dependent exactly as derived
(k_prf = ⌊N(B+1)/log₂p⌋+1 over Z, ⌊NB⌋+1 over F_q(t)); and recognition-only
proof over F_q(t) derails on a degenerate coincidence and is caught by the
structural checks: the two-precision filter does no work over a function
field, so the resolvent proof carries all the soundness there.

## 4. Regression coverage

The regression suite (`tests.py`, about 110 checks) pins every result quoted
above: the certificate soundness conditions, the three family records, the
mutation totals, the localization columns, the ablation predictions, and the
measurement formulas.