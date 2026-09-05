# Reproducibility package

This directory is a self-contained snapshot of the code, recorded data, certificates, measurements, figures, and certificate specification used by the artifact.

## Requirements

Python 3.9 or later. The prover and checker use the standard library; `matplotlib` is needed only to regenerate figures. The packaged dependency declaration is in `requirements.txt`.

## Reproduce the figures

From this directory:

```bash
python3 reproduce_figures.py
```

This regenerates all five figures from `measurements/measurements.json`.

To rerun the controlled height sweep and index harvest before regenerating the figures:

```bash
python3 reproduce_figures.py --remeasure
```

The three family result files are read from `results/` as recorded data. The family scripts in `code/` can be run separately to extend those resumable datasets.

## Verify a certificate

```bash
cd code
python3 checker.py ../certificates/phi10/certificate.json -v
```

The packaged certificates identify `galois_certificate_spec.md@final`; the exact specification is included at `galois_certificate_spec.md`.

## Layout

- `account/` — derivations, guarantees and validation, and measurement discussion.
- `config/configuration.json` — frozen family, measurement, and ablation configuration.
- `measurements/measurements.json` — recorded measurement dataset.
- `results/` — recorded composition, Eisenstein, and sparse-family results.
- `figures/` — the five published measurement figures.
- `certificates/` — certificate fixtures used by the artifact.
- `code/` — source snapshot needed for checking, figure reproduction, and remeasurement.
- `tables/` — recorded invariant tables used by descent.
- `galois_certificate_spec.md` — certificate format, derivations, soundness, and checker specification.
- `requirements.txt` — figure-generation dependency declaration.
- `LICENSE` — MIT license copied from the repository root.

Files copied into this package are Git-identical to their corresponding top-level repository artifacts unless the package path itself is configuration or documentation specific to this bundle.
