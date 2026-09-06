# Repository structure

The repository is organized around four roles: core computation, certification/diagnostics, validation/measurement, and reproducibility artifacts.

## Core computation

These modules implement the mathematical and group-theoretic pipeline:

- `permgroup.py` — permutation/group primitives and subgroup operations.
- `hensel_frobenius.py` — coefficient rings, root lifting, Frobenius, and inertia.
- `subfields.py` — subfield recognition, block systems, and starting groups.
- `invariants.py` — relative invariants and stabilizer verification.
- `descent.py` — Stauduhar descent over `Z`.
- `constant_field.py` — function-field descent and constant-field degree.
- `verify_roots.py` — root-list certification in the supported coefficient rings.
- `run_config.py` — validated, serializable run configuration.

## Certification and diagnostics

- `artifact.py` — certificate-producing driver for case 1.
- `checker.py` — standalone certificate checker.
- `mutate.py` — mutation testing for certificate robustness.
- `diagnose.py` — rejection diagnosis via controlled reruns.

## Validation and measurement

- `tests.py` — regression suite.
- `ablation.py` — ablation matrix across pruning/start/proof/ring choices.
- `family_compositions.py` — composition-family validation.
- `family_eisenstein.py` — tame Eisenstein-family validation.
- `family_sparse.py` — sparse/function-field family validation.
- `measurements.py` — measurement harvesting and figure generation.

The corresponding committed JSON datasets are evidence used by the repository and reproducibility artifact. Keep their filenames stable unless all readers and documentation are updated together.

## Data, fixtures, and generated outputs

- `certs/` — committed certificate fixtures.
- `tables/` — invariant tables and subgroup caches; regenerated as needed.
- `figures/` — generated plots.
- `family_*_results.json` — committed family-validation outputs.
- `measurements.json` — committed measurement dataset.
- `runs/` — local per-run output; not committed.

## Reproducibility package

`package/` is a self-contained snapshot used to reproduce the artifact independently of the development layout. It intentionally duplicates selected top-level source/data files.

Treat the top level as the development source of truth and `package/` as a snapshot. When a development change is meant to alter the reproducibility artifact, update the corresponding file under `package/` in the same pull request and preserve byte identity for copied files whenever possible.
