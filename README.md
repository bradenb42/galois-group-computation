# Certified Galois group computation

Computes the Galois group of a monic separable polynomial by relative resolvent
descent (Stauduhar's method) and emits a certificate that a separate program
verifies from scratch.

Three coefficient rings are covered by one set of derivations:

| case | ring `R` | approximation ring | status |
|---|---|---|---|
| 1 | `Z` | `A = (Z/p^K)[z]/(m)`, that is `O_q / p^K` | full pipeline: descent, certificate, checker |
| 2 | `O_K`, `K/Q_p` local | `B = A[x]/(f)`, that is `O_{K'}/p^K` | tame Eisenstein only: certified elements, no descent |
| 3 | `F_q[t]` | `S = F_{q^s}[[u]]/u^K`, `u = t - t_0` | descent and constant field degree, no certificate emitter |

Only case 1 produces certificates. Cases 2 and 3 have working root lifting,
Frobenius and inertia elements, and (case 3) a descent, but no serialized
certificate and no checker.

## Requirements

Python 3.9 or later, standard library only. `matplotlib` is needed for the
figures in `measurements.py` and for nothing else.

## Layout

| file | contents |
|---|---|
| `permgroup.py` | permutations, closures, subgroup enumeration, maximal-subgroup classes, normalizers, coset representatives, action on polynomials, stabilizer verification. The only module shared between prover and checker. |
| `hensel_frobenius.py` | base rings (`Zmod`, `PolyQuot`), Newton root lifting with unit derivative, the three cases' root sets, Frobenius and inertia elements, `certify_element` |
| `subfields.py` | degree-one prime choice, roots and Frobenius in a fixed labelling, recognition in `K_f` by LLL and Babai rounding, factorization over `K_f`, principal subfields, subfield lattice, block systems, starting group `W` |
| `invariants.py` | `U`-relative `V`-invariants: A-support, Type I, Type II, Type III (separating monomial), plus the alternative variant used by diagnosis; a JSON table with conjugacy-aware lookup |
| `descent.py` | the Stauduhar step over `Z`: pruning, recognition at two precisions, exact resolvent, verdicts, Tschirnhaus retries; `run_descent` drives `W` down to `G` |
| `verify_roots.py` | simple-root and complete-root-list certification in all three rings: integer roots by linear-factor lifting, Newton polygon over `O_K`, point lifting over `F_q[t]` |
| `constant_field.py` | the case-3 descent, run twice (arithmetic and geometric) to obtain `G`, `G_geom` and the constant field degree `c` |
| `run_config.py` | the configuration object recorded at the start of every run, with per-case validation |
| `artifact.py` | case-1 driver: config, descent, `certificate.json`; thin wrapper over the checker |
| `checker.py` | standalone checker, `python3 checker.py cert.json`, exit 0 accept and 1 reject |
| `mutate.py` | alters every scalar of a certificate one at a time and reports any alteration the checker still accepts |
| `diagnose.py` | on a rejection, re-runs the failing step under four one-knob variations and reports which one repairs the chain |
| `ablation.py` | the 24-cell matrix over {pruning} x {start} x {proof mode} x {ring}, with programmatic confirmation of the predicted effects |
| `measurements.py` | cost data by degree, height and step index, plus figures |
| `family_compositions.py` | check 1: `f = g(h(x))` over `Q` |
| `family_eisenstein.py` | check 2: tame Eisenstein polynomials over `Q_2`, `Q_3`, `Q_5` |
| `family_sparse.py` | check 3: lacunary and triangular pencils over `F_q(t)` |
| `tests.py` | regression suite over all of the above |

Conventions: polynomials are lists of integers from low degree to high and
monic, so `x^5 - 2` is `[-2, 0, 0, 0, 0, 1]`. Permutations are tuples of the
images of `0..n-1`, with `compose(a, b)(i) = a(b(i))`. Invariants are sparse
dicts mapping exponent tuples to integer coefficients. Over `F_q[t]` a
coefficient is itself a list of ints modulo `p`, so `f_t` is a list of lists.

## Quick start

```bash
python3 descent.py                 # six examples with their expected group orders
python3 artifact.py                # build and check certificates for four polynomials
python3 checker.py certs/phi10/certificate.json -v
python3 tests.py                   # full regression suite
```

Computing one group directly:

```python
import descent as ds
r = ds.run_descent([-2, 0, 0, 0, 0, 1])   # x^5 - 2
r["G_order"]                              # 20
r["G_gens"]                               # generators as permutation tuples
```

Producing a certificate:

```python
import artifact, run_config as rc, dataclasses, json
cfg = dataclasses.replace(
    rc.example_case1(),
    polynomial=rc.Polynomial(degree=5, coefficients=["-2", "0", "0", "0", "0"]),
    invariant_table_path="tables/invariants_descent.json",
)
path = artifact.run(cfg, "runs/x5m2")
artifact.check_certificate(json.load(open(path)))
```

## Prover pipeline (case 1)

1. Choose a prime `p` with `f mod p` squarefree and having a root in `F_p`,
   lift all roots into `A`, compute the Frobenius `phi` and its permutation
   `tau`, relabelled so that `tau(0) = 0` and `alpha_0` lies in `Z_p`
   (`subfields.roots_and_frobenius`).
2. Factor `f` over `K_f` by recognizing coefficients from the single embedding,
   then form the principal subfields and close under intersection
   (`subfields.factor_over_Kf`, `principal_subfield`, `subfield_lattice`).
3. Turn each subfield into a block system and intersect the block stabilizers to
   get the starting group `W`, with the type bound as its certificate
   (`subfields.starting_group_bruteforce`, `type_bound`).
4. Descend. For each class of maximal subgroups `V < U`: build a `U`-relative
   `V`-invariant with verified stabilizer, prune the cosets using `tau`,
   evaluate, recognize the value at two precisions, recover the exact resolvent,
   and inspect its integer roots. A simple integer root in a surviving coset
   gives `G <= sigma V sigma^{-1}`; no integer root closes the class; a multiple
   root triggers a Tschirnhaus transformation (`descent.descend`, `_test_pair`).
5. Stop when every class is negative, then serialize (`artifact.run`).

Precisions follow the derived formulas. Over `Z`,
`k_rec = floor((B+1)/log2 p) + 1` and `k_prf = floor(N(B+1)/log2 p) + 1`, with
`B = log2|F|_1 + deg(F) * log2(root bound)` and `N` the index. Over `F_q[t]`
the same quantities are `k_rec = B + 1` and `k_prf = NB + 1`, computed with
exact `Fraction` arithmetic because float rounding breaks the degree bounds.

## Certificate format

`certificate.json` has four parts.

- `header`: case, `f`, `p`, residue degree `s`, the modulus `m` of `O_q`, the
  precision `K`, and the `n` approximate roots as coordinate lists.
- `lattice`: each subfield as an integral primitive element `b`, its minimal
  polynomial `h`, and its blocks; plus generators of `U_0` and the string
  `"type_bound"` naming the justification for it.
- `steps`: per step, generators of `U_i` and `U_{i+1}`, the invariant `F_i`,
  `sigma_i`, the value `v_i`, the precision `k_i`, the Tschirnhaus
  transformation `T_i` or null, and the exact resolvent `R_i`.
- `terminal`: generators of `U_ell` and one record per class of maximal
  subgroups, either `dismissed_by_pruning` or `negative_resolvent` with its
  invariant, `T`, precision and resolvent.
- `claimed_group_order`.

## Checker

`checker.py` re-implements modular arithmetic, `F_{p^s}` arithmetic, exact
linear algebra over `Q`, resultants, discriminants and integer root finding. It
imports `permgroup` and nothing else from the project, so a fault in a prover
routine is not mirrored on the checking side; `tests.py` asserts this import
restriction. Each condition is named in the rejection message.

- **C0** `p` prime, `f` squarefree mod `p`, `m` irreducible of degree `s`, the
  supplied roots satisfy `f(alpha) = 0 mod p^K` and are distinct mod `p`,
  `alpha_0` in `Z_p`, and the Frobenius read off the residue field is a
  permutation.
- **C1** per subfield: `h(b(alpha)) = 0` exactly in `Q[x]/(f)`, `deg h` equals
  the number of blocks, the powers of `b` are independent, `disc h != 0`,
  `K > v_p(disc h)/2`, and the blocks recomputed from the approximate roots
  agree. Then `U_0` preserves every block system and `|U_0|` equals the type
  bound over all `n` points, so `U_0 = W`; and `tau` lies in `U_0`.
- **C2** `Stab_{U_i}(F_i) = sigma_i^{-1} U_{i+1} sigma_i` by orbit counting over
  `Z` and again modulo 2 and 3, with the orbit search cut off at the index.
- **C3** `sigma_i F_i(T_i(alpha)) = v_i mod p^{k_i}`.
- **C4** `k_prf` recomputed from `F_i`, `f` and `T_i`, with `k_prf <= k_i <= K`.
- **C5** the resolvent recovered from the orbit and compared with the supplied
  one, then `R_i(v_i) = 0`, `R_i'(v_i) != 0` and `v_p(R_i'(v_i)) < k_i`, all
  exact.
- **C6** the checker's own list of maximal-subgroup classes of `U_ell` must be
  covered by the terminal records. A dismissal is re-verified by showing `tau`
  lies in no conjugate of `V`; a negative record is re-verified by recomputing
  the resolvent and finding no integer root, by linear-factor lifting of the
  squarefree part at an auxiliary prime.

Three prover-side quantities are absent from the certificate: completeness of
the subfield lattice, maximality of the pairs, and the pruning decisions. A
defect in any of these lengthens a chain or produces a rejection; none can turn
a false statement into an acceptance.

## Validation tools

```bash
python3 mutate.py certs/phi10/certificate.json    # exhaustive single-entry alteration
python3 diagnose.py                               # four injected faults, localized
python3 ablation.py                               # 24 cells with confirmations
python3 measurements.py                           # data and figures
```

`mutate.py` classifies an accepted alteration as benign only when the altered
certificate still states a re-verified true claim: run metadata, informational
labels, precisions that remain inside `[k_prf, K]`, a degree-one modulus, and
Tschirnhaus data whose resolvent recomputes to the same value. Anything else
accepted is reported as a failure.

`diagnose.py` maps a rejection to one of four knobs by rebuilding the
certificate from the failing step onward with that knob turned, then
re-checking: fresh Tschirnhaus (proof), doubled precision (precision), pruning
disabled (pruning), alternative invariant (invariant). The variation applies to
the whole rebuilt suffix, so a persistent fault is localized only by a knob that
repairs the entire chain. If the baseline re-run accepts, the record was
corrupted rather than the algorithm being at fault.

## Family checks

```bash
python3 family_compositions.py 8            # optional second argument: time budget in seconds
python3 family_eisenstein.py 2              # argument: random representatives per (p, n)
python3 family_sparse.py 3600               # argument: time budget in seconds
```

All three are resumable: results accumulate in
`family_compositions_results.json`, `family_eisenstein_results.json` and
`family_sparse_results.json`, and completed keys are skipped on a rerun.

Compositions check that the fibres of `h` appear in the subfield lattice, that
the block quotient equals `Gal(g)` computed by an independent descent, and that
the order factors as `|pi(G)| * |G ∩ ker|`. The literal containment
`G <= Gal(h) wr Gal(g)` is recorded separately, since it fails in general; the
run reports which pairs violate it.

Eisenstein runs compare the certified inertia and Frobenius elements against the
explicit splitting field `Q_{p^{s_0}}((g^j p)^{1/n})` in its natural labelling,
together with the metacyclic relation, the tame ramification polygon, and
`v_p(disc f) = n - 1`.

Sparse pencils compare `G_geom` and `G` against `C_d wr S_m` and its extension
by `<q mod d>`, as literal set containments in the fibration labelling, with no
conjugacy search.

## Generated files

`tables/invariants_*.json` (the invariant table, appended to as new pairs are
met), `tables/subgroup_cache.pkl` (memoized subgroup lattices),
`family_*_results.json`, `measurements.json`, `figures/fig*.png`, and per run
`config.json`, `config.sha256`, `config_history/<run_id>.json` and
`certificate.json`.

## Scope

The group layer is brute force throughout: closures by breadth-first search,
complete subgroup enumeration by one-generator extensions with a cap of 800
elements, and maximal-subgroup classes taken from the full subgroup list. This
is adequate for `|U|` up to a few thousand and is the part that would be
replaced by Schreier-Sims at scale. Nothing else depends on how the group layer
is implemented. The cap is what limits compositions to composed degree at most 8
with starting groups of order at most 600, and triangular pencils to `n <= 7`.

The case-2 machinery is tame, meaning `p` does not divide `n`. Wild degrees are
reported as out of scope rather than attempted, since automorphisms of a wild
extension require the explicit splitting-field construction.

Case 3 has no certificate emitter and no checker, so `ablation.py` records its
cells with `n/a` in the checker columns. Its recognition-only mode fails in a
specific way: over `F_q(t)` the two-precision window coincides with the
truncation, so a degenerate coincidence such as `x_0 + x_2 = 0` is accepted as a
positive step, the descent enters an intransitive group, and the structural
assertions stop it. Soundness in case 3 therefore rests on the exact resolvent
rather than on the recognition step.

Root finding over `F_{p^s}` with `p = 2` and a large field is not implemented
and raises rather than returning a wrong answer.

## License

MIT

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). The preferred paper citation is:

Braden Bost, *A uniform certified algorithm for Galois groups over Q, p-adic fields, and F_q(t)* (2026).
