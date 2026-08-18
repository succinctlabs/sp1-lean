# rust/ — Rust-side artifacts of the witness-generation export

This directory holds Rust code that **consumes** the Lean-verified witness-generation export.
It is deliberately self-contained: nothing here depends on SP1's crates, on the extraction
overlay, or on the Lean toolchain — only on the wire format documented in
`docs/witgen-wire-format.md`. That is what makes it shippable as-is to the SP1 team.

## Crates

- **`witgen-interp/`** — the reference interpreter for the exported witness IR. Reads a
  circuit's `export/witgen/<Chip>.witgen.json` (the serialized witness programs plus the
  constraint/interaction list), the chip's symbolic row map (`<Chip>.rowmap.json`), and a
  trace fixture (`export/testdata/<Chip>.trace.json` — SP1-anchored event rows plus
  synthetic rows, written by the fail-closed generation-time gate). For every row it
  re-runs the witness programs on the input prefix and checks the witness cells; for every
  SP1-anchored row it additionally reconstructs the **full Rust trace row** through the row
  map, matches it against SP1's real `generate_trace` output verbatim, and checks that
  every extracted AIR constraint evaluates to zero on it. A wrong interpreter, a wrong row
  map, or a wrong exported program all fail the differential run loudly.

## Relationship to the trust story

Witness generation is completeness-side: a wrong witness generator makes a prover fail, it
can never make a false proof verify. The interpreter is therefore a *conformance oracle*,
not a trusted component — its value is demonstrating that the exported artifact is
sufficient to reproduce SP1's real traces, which is the load-bearing step toward SP1
consuming the verified witness generators directly (see `docs/rust-integration-memo.md`).

## Building and running

Plain cargo, no workspace. The full battery (unit tests for every documented semantics
trap + the differential over all committed fixtures):

```
cd rust/witgen-interp && cargo test
```

Or from the repo root, the differential alone (~857 fixture rows across all 25 chips, 706
of them SP1-anchored):

```
scripts/run_interp_diff.sh                    # against the committed export/
scripts/run_interp_diff.sh --regen            # re-verify the export first (needs lake build SP1CleanTest)
scripts/run_interp_diff.sh --chip Add --verbose   # one chip, per-op cell values
```

A mismatch fails loudly with the chip, fixture row, cell index, and the witness
operation that produced the cell. Cargo is deliberately **not** part of the Lean CI;
run the script manually after regenerating exports or fixtures.
