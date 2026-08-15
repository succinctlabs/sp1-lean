# rust/ — Rust-side artifacts of the witness-generation export

This directory holds Rust code that **consumes** the Lean-verified witness-generation export.
It is deliberately self-contained: nothing here depends on SP1's crates, on the extraction
overlay, or on the Lean toolchain — only on the wire format documented in
`docs/witgen-wire-format.md`. That is what makes it shippable as-is to the SP1 team.

## Crates

- **`witgen-interp/`** — the reference interpreter for the exported witness IR. Reads a
  circuit's `export/witgen/<Chip>.witgen.json` (the serialized witness programs plus the
  constraint/interaction list), the chip's manifest (`<Chip>.manifest.json` — input layout,
  hint schema, pad-row policy), and a trace fixture (`export/testdata/<Chip>.trace.json` —
  real events and golden rows dumped from SP1's own `generate_trace`), and checks that
  evaluating the witness programs on each row's input prefix reproduces the golden witness
  cells. A wrong interpreter, a wrong manifest, or a wrong exported program all fail the
  differential run loudly.

## Relationship to the trust story

Witness generation is completeness-side: a wrong witness generator makes a prover fail, it
can never make a false proof verify. The interpreter is therefore a *conformance oracle*,
not a trusted component — its value is demonstrating that the exported artifact is
sufficient to reproduce SP1's real traces, which is the load-bearing step toward SP1
consuming the verified witness generators directly (see `docs/rust-integration-memo.md`).

## Building

Plain cargo, no workspace:

```
cd rust/witgen-interp && cargo test
```

`scripts/run_interp_diff.sh` wraps the differential run against the checked-in exports and
fixtures. Cargo is deliberately **not** part of the Lean CI; run the script manually after
regenerating exports or fixtures.
