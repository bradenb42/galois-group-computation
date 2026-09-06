# Contributing

This repository mixes algorithmic source code, validation scripts, committed experiment outputs, and a frozen reproducibility package. Keep changes narrowly scoped so those roles stay clear.

## Repository conventions

- Treat the top-level Python modules as the primary development source.
- Treat `package/` as a reproducibility snapshot. Update it deliberately when a change is intended to affect the archived artifact, and keep copied source/data files byte-identical to their top-level counterparts whenever the package layout allows it.
- Keep algorithmic modules, validation scripts, committed outputs, and generated caches distinct. See `docs/REPOSITORY_STRUCTURE.md` for the current grouping.
- Use lowercase `snake_case` for Python modules, functions, and generated JSON filenames.
- Use four spaces in Python, UTF-8 text, LF line endings, a final newline, and no trailing whitespace. The repository-level `.editorconfig` and `.gitattributes` encode these defaults.
- Prefer standard-library imports first, then project-local imports. Avoid unrelated reformatting in mathematical or certification changes; small diffs are easier to audit.

## Generated and committed artifacts

Some generated files are intentionally tracked because the regression suite and reproducibility package depend on them. In particular, the family result JSON files, `measurements.json`, and certificate fixtures under `certs/` are part of the checked-in evidence.

By contrast, local caches and regenerated plotting/table outputs are ignored where appropriate. Do not commit temporary run directories, editor state, Python caches, or scratch files.

When changing an experiment or certificate format, update the corresponding committed outputs only when the change is intentional and reproducible.

## Validation

Run the narrowest checks that cover your change, then the full regression suite when practical:

```bash
python3 tests.py
python3 checker.py certs/phi10/certificate.json -v
```

For changes to a validation family, also run the relevant family script. For changes to measurement collection or plotting, run `python3 measurements.py` and inspect the regenerated data/figures before committing intended output changes.

## Pull requests

Keep pull requests focused. Describe:

1. what changed;
2. why the change is needed;
3. which validation commands were run; and
4. whether any committed artifact or `package/` snapshot changed.

Avoid combining organization-only cleanup with algorithmic behavior changes unless the behavior change depends on the reorganization.
