# Rust comparison tools

`sp1-comparison/` compares pinned SP1 inventories and exercises Clean's built-in Rust backend.
`witgen-interp/` is the transitional [JSON witness comparison](../docs/witgen-wire-format.md).
Retire its interpreter and fixtures when the direct export path replaces their instruction
coverage; see [export and integration](../docs/export.md).

Run the fresh comparisons:

```sh
scripts/check_ensemble_export.sh
python3 scripts/check_witgen_export.py
```

Both run locked Cargo checks in CI. The witness driver builds the full Lean closure, exports
twice under `.lake/witgen-export/`, verifies deterministic bytes and all 25 chips against
independent SP1 dumps, then runs the interpreter's unit, ensemble and row tests. Its printed
output directory contains logs and source/artifact fingerprints. For a focused diagnostic:

```sh
WITGEN_EXPORT_DIR=/path/printed/by/the/driver cargo run --locked --release \
  --manifest-path rust/witgen-interp/Cargo.toml -- check --chip Add --verbose
```

Every SP1-anchored row is reconstructed cell-for-cell and its exported assertions are checked.
These comparisons test serialization and evaluation; they do not prove lowering correct.

The optional live prover check uses the extraction revision from `scripts/provenance.json`:

```sh
python3 scripts/run_sp1_conformance.py --sp1-dir /path/to/pinned/sp1 \
  --export-dir /path/printed/by/the/driver
```

The driver rejects changed source/artifact fingerprints, then stages the pinned checker and
fresh exports under `.lake` without editing SP1. The pinned checker still depends on its
vendored interpreter; that duplication ends when direct export replaces the legacy comparison.
