# Integrating the verified witness generators with SP1 — a memo for the Rust side

*Audience: SP1 maintainers evaluating what this project's witness-generation export is, how it is
checked against the real prover today, and what a tighter integration would look like. Everything
cited here is committed and reproducible; file paths are relative to `sp1-lean` unless prefixed
with `sp1/`.*

## 1. What exists: two independent implementations, one comparison chain

There are two implementations of "fill in a chip row":

- **SP1's prover**: per chip, `populate` methods write witness columns and emit byte-lookup
  events, e.g. `sp1/crates/core/machine/src/operations/add.rs` (`AddOperation::populate` — the
  4-limb u16 carry chain) called from `alu/add_sub/add.rs`'s `generate_trace`.
- **The Lean circuits**: witness generation is part of the circuit language itself. `AddChip`'s
  `main` creates its four witness cells with `witnessVectorIR 4 (AddOperation.populateIR b c)` —
  a first-class expression IR, not an opaque closure — and that same term is what the chip's
  kernel-checked completeness proof witnesses. Nothing is translated between the two sides;
  they are compared.

Because the IR is data, it serializes. Per chip we export three JSON artifacts
(`export/witgen/`):

| artifact | content |
|---|---|
| `<Chip>.witgen.json` | the wire-format v1 program: witness ops (with shared let-steps), the ordered `assert` list, the interaction list |
| `<Chip>.rowmap.json` | the **symbolic Rust row**: `rustWidth` expressions over the input+witness cells, produced by applying the audited native→Rust layout map (`ChipFaithful`'s `reconfigure`) at the expression level |
| `<Chip>.manifest.json` | what the wire format deliberately omits: `inputWidth`, `localLength`, the hint-table schema, the field modulus |

The format is specified in `docs/witgen-wire-format.md`; the serializer is Clean's (the Lean
circuit DSL), and the sharing pass that makes production-scale programs small (DivRem:
1.22 GB → 1.04 MB) carries a kernel-checked evaluation-preservation proof. Total export for all
25 chips: ~2.5 MB, byte-stable (no timestamps or revisions embedded; regeneration at the same
pins is byte-identical, CI-diffed).

## 2. How it is checked against the real prover today (Rust → Lean)

1. **Ground truth in**: `chip_traces` (a committed binary at the pinned extraction branch,
   `sp1/crates/core/compiler/src/bin/chip_traces.rs`) runs SP1's real `generate_trace` over
   deterministic per-chip event batteries and dumps events + the full padded matrices into
   `export/sp1dump/` (byte-reproducible at the pin; sole writer `scripts/update_sp1_dumps.sh`).
2. **The generation-time gate**: `scripts/witgenExport.lean --testdata` recovers each event row's
   native inputs *from the dumped row itself* through the row map (every input cell is a bare
   `var` column, except `is_real` on the six flag-hinted chips), derives the hint tables from the
   event's opcode, re-runs the witness programs, evaluates the row map, and **fails closed unless
   the reconstructed row equals SP1's row cell-for-cell** — for every event row of all 25 chips.
   Only then are the differential fixtures (`export/testdata/`) written. This gate re-runs in CI.
3. **Independent re-execution**: `rust/witgen-interp` (self-contained: one dependency, no SP1
   types, no Lean) re-runs the witness programs from the wire bytes alone over ~857 fixture rows,
   reconstructs every anchored full row, and checks every extracted AIR constraint evaluates to
   zero on it (`scripts/run_interp_diff.sh`).

The gate has teeth: on its first full run it caught that SP1 populates the `op_a` link word only
when `rd ≠ x0` (`jal`/`jalr`/`utype`) while the Lean circuits witnessed it unconditionally — the
Lean side was fixed to match SP1's bytes exactly.

## 3. Why witness generation is the safe thing to share

Witness generation is completeness-side: a wrong generator makes a prover fail; it can never make
a false proof verify. The verified artifact is therefore a *conformance and correctness* asset
with no soundness exposure. On the Lean side, the exported program is provably the same object
the completeness theorems reason about (`populateIR_eval` ties the IR to the value-level
`populate`, which `spec_populate` ties to the chip's semantic spec; `Circuit.witgen` provably
builds the environment the proofs quantify over).

## 4. The proposal: invert the comparison — check the artifacts against the prover, in Rust

Today's flow pulls SP1 data into `sp1-lean`. The better long-term shape is the reverse: the
exported artifacts are vendored into the SP1 tree, and a Rust check **inside the SP1 tree**
runs them against the live prover:

```
per chip:
  record  = synthetic event battery (the chip_traces builders, reused as a library)
  trace   = RiscvAir::machine().chip(name).generate_trace(record)   // the real prover path
  inputs  = derive_inputs(rowmap, trace_row, is_real)               // bare-var gather
  hints   = one-hots from the real events (match on Opcode; Branch's taken bit from operands)
  check   = check_row(program, rowmap, inputs, hints)               // the shared witgen-interp core
  assert  check.rust_row == trace_row  (cell-for-cell)
  assert  check.constraint_failures.is_empty()
```

`witgen-interp` provides `check_row` and `derive_inputs` as pure library functions
(`rust/witgen-interp/src/check.rs`) — the SP1-side check and `sp1-lean`'s own differential share
one implementation.

This check **exists today** on the pinned extraction branch, deliberately staged with **zero CI
footprint**: `crates/core/compiler/conformance-check/` is a standalone opt-in package (its own
cargo workspace, excluded from SP1's, alongside the vendored interpreter and the ~2.5 MB of
artifacts), so nothing in SP1's `cargo build` or `cargo test --workspace` builds or runs it. It
runs only when invoked —

```
cargo run --release --manifest-path crates/core/compiler/conformance-check/Cargo.toml
```

— or via `sp1-lean`'s driver `scripts/run_sp1_conformance.sh` (which fences the pin and the
artifact byte-identity first). All 25 chips pass in ~11 s; exit code 1 on any mismatch keeps it
script- and CI-ready.

Promoting the check into SP1's CI is a deliberate **later hardening step** — the artifact-sync
protocol (who refreshes on which side of a chip change, and how staleness is surfaced without
blocking unrelated PRs) should be agreed first. Once promoted, what each side gains:

- **SP1** gains a CI check that its trace generation matches a formally verified generator —
  drift in a `populate`, a column layout, or an AIR constraint is caught on the PR that
  introduces it, with a named chip/row/column.
- **sp1-lean** retires the committed-dump machinery and its refresh ritual; the claim upgrades
  from "SP1-at-pin-X matched when we last dumped" to "SP1's HEAD matches, checked continuously."
- The artifacts crossing the boundary are small, versioned, and deterministic; a provenance
  sidecar stamped at vendoring time records the producing `sp1-lean` commit and Clean revision.

## 5. Versioning contract

- The wire format carries `version: 1`; evaluation semantics are total (`0⁻¹ = 0`, wrapping u64
  ops, zero-default hint reads — the zero-default *is* the padding-row semantics).
- Artifacts are byte-stable by construction; the vendored copy carries a `provenance.json`
  sidecar `{sp1-lean commit, Clean rev, wireVersion}` written by the sync script, so the vendored
  tree is attributable and refresh is one command.
- A red SP1-side test means one of exactly three things: SP1's trace generation changed (the
  common case — refresh or reconcile), the artifacts are stale, or a wire-format regression.
  The failure message names the chip, row, and column.

## 6. Beyond conformance: the end state

If SP1's local witness cells were *generated from* the verified IR (interpreted, or compiled —
the wire format is a sufficient codegen source; the reference interpreter measures ~2M Add
rows/s single-threaded, conformance-class rather than prover-class), the comparison collapses
into an identity plus a small wiring smoke test. The clean split already exists: SP1's adapter/
state populate fills the input block from events; the verified programs fill the witness block;
the byte-lookup events a `populate` emits are exactly the exported interaction list, which the
interpreter already evaluates per row. That is a separate, larger conversation — the inversion
above is the self-contained first step and requires no change to any shipping SP1 component.
