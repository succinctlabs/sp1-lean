# Standalone Clean backend conformance

This campaign compiles three existing public native gadgets through the pinned Clean
Circom backend over the BN254 scalar field. It checks backend conformance; it does not
prove that backend correct, implement final-ensemble export, or add Rust operation
faithfulness anchors.

Prepare the repository's pinned Lean dependencies, install Node **22.16.0**, then explicitly
install the locked checker:

```sh
npm ci --prefix tools/backend-gadgets
scripts/check_backend_gadgets.sh
```

The runner also works by absolute path from another directory. It checks prerequisites
and pins before building, and never installs tools or updates dependencies. No `circom`
executable is needed. It uses the package-local **snarkjs 0.7.6**, not a global installation.
The first native build can compile many C objects even when Lean oleans are cached.

The exporter is a native executable with a Sail-free import closure:

```sh
LEAN_NUM_THREADS=2 lake --no-cache build --wfail --iofail backendGadgets
.lake/build/bin/backendGadgets export/backend-gadgets
```

`scripts/backendGadgets.lean` is the sole writer of `export/backend-gadgets/`. The checker
regenerates into an ignored scratch directory and compares the complete inventory and
every byte against the committed artifacts before running any external checks. Regenerate
the committed tree only when intentionally changing the fixture or pinned backend.

| Public circuit | Inputs | Lean witness cells | Lean assertions | Full R1CS constraints | Total signals |
|---|---:|---:|---:|---:|---:|
| `IsZeroOperation.circuit` | 1 | 2 | 3 | 6 | 7 |
| `IsZeroWordOperation.circuit` | 4 | 11 | 17 | 33 | 32 |
| `WordRangeCheck.circuit` | 4 | 64 | 68 | 132 | 133 |

These are measured costs of the unchanged circuits and the pinned lowering, including
the constant signal at index zero and all backend auxiliary signals. They are not optimized R1CS
cost claims. The zero gadgets' thin adapters allocate their existing `populateFE`
columns and invoke the public assertion with gate `1`; the range adapter invokes the
existing public bit-decomposition circuit. No constraints, lookups, or interactions
are removed to make compilation succeed.

Each gadget directory contains WASM, binary and JSON R1CS, explicit `layout.json`,
individual input JSON files, and `cases.json`. Field elements use exact decimal strings.
The layout comes from Clean's actual `signalOfVar`, including its outputs-first order.
For each input, the exporter evaluates the same program with Lean's prover environment
and records every original input and witness cell. The checker runs:

```sh
node tools/backend-gadgets/node_modules/snarkjs/build/cli.cjs wtns calculate CIRCUIT.wasm INPUT.json WITNESS.wtns
node tools/backend-gadgets/node_modules/snarkjs/build/cli.cjs wtns check CIRCUIT.r1cs WITNESS.wtns
```

It compares all mapped original cells with Lean, then checks the **entire R1CS**, including
auxiliaries. Clean's WASM accepts the Circom sanity-check flag but does not check assertions;
successful witness calculation alone never counts as circuit acceptance here. The checker
requires an explicit snarkjs witness verdict, so process failure cannot impersonate a
negative test. It also corrupts one backend auxiliary per gadget to verify rejection.

The 29 input cases cover zero, nonzero, field limits, values above 64/128 bits, each word
limb, maximum 16-bit limbs, and out-of-range limbs. The 26 mutations include altered
results, nonzero-input inverses, Boolean/reconstruction bits, and backend auxiliaries.
Five valid mutations preserve the zero gadgets' deliberate freedom: on a zero operand,
the inverse is unconstrained by the original contract. They must remain R1CS-satisfying,
even though they differ from the canonical `populateFE` witness. Mutations use the same
explicit original-cell signal map; the Lean assertion evaluator independently checks
their expected acceptance before export.

The exporter checks every flattened operation and uses Clean's witness-IR compiler for
eligibility. Its executable rejection tests cover lookup, interaction, native closure,
`dataGet`, `hintGet`, and an unbound loop index. These are capability failures, not a
reason to strip constraints or replace the IR. Static-table replacements, Plonky3, and
generated Rust remain separate roadmap work.
