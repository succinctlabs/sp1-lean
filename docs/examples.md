# Library examples

From a [prepared checkout](contributing.md), run all examples or select one:

```sh
python3 scripts/check_examples.py
python3 scripts/check_examples.py branch --json
```

The shared runner builds the selected test modules, checks every expected case and writes
results.json, commands.log and provenance.json under .lake/build/examples. It verifies prepared
dependency checkouts and records revision, dirty state, pins and CI identifiers. Invalid output,
diagnostics after a zero exit, mismatched expectations and changing sources fail. Reports are
executable evidence, not proof certificates; the central trust scan covers theorem dependencies.

## ADD and a complete Memory boundary

[AddEnsemble](../SP1CleanTest/Alignment/Examples/AddEnsemble.lean) checks ADD x1,x2,x3 with
x2=100, x3=23 and x1=123, PC 65536→65540 and clock 9→17. It starts at an arbitrary local
boundary. The [shared fixture](../SP1CleanTest/Alignment/Support/HostFinalMemoryFixture.lean)
checks the public verifier, actual physical rows, fixed lookups and all registered balances.

The active and empty witnesses accept. Missing/duplicated RAM authentication, wrong final
clock, missing untouched-register authentication, changed untouched x31/RAM and a missing bank
terminal reject. These cases exercise complete change coverage, not just locally valid arithmetic.

## A compiler-derived branch

[BranchEnsembleRoundTrip](../SP1CleanTest/Alignment/Audit/BranchEnsembleRoundTrip.lean) joins
an official Sail step to canonical projection, event compilation and raw acceptance of the
actual HostFinalMemory assembly. BEQ x1,x2,+4092 has PC 65536→69628 and clock 1→9.

The fixture retains every installed component and all 32 verifier-fixed source-register rows,
including unused rows at count zero. The JSON report records physical rows, complete interactions
and the separate public verifier. Full RawChannel membership equivalence permits deduplicating
the registry while retaining every interaction occurrence and each assertion-check channel.

Original/empty witnesses accept. Wrong next PC, missing/duplicate authentication, a changed
untouched target register and malformed seed indices/lengths reject. The runner computes the
compiler and physical witness; the official Sail step is theorem evidence, not execution of a
noncomputable full Sail state. This closes one concrete construction, not general totality.

## Verified LoadByte replacement

[LoadByteStaticChip](../SP1Clean/Proofs/Chips/LoadByteStaticChip/Transport.lean) replaces one
paired U8Range request with two upstream fixed ByteTable lookups. Gating the lookup inputs
preserves inactive-row freedom. Semantic assumptions, arithmetic assertions and generated witness
cells agree with the original circuit. The proof retains arbitrary residual providers, including
reader demand with the same key as the removed occurrence. Generation and evaluation data are
independent. The constraint transport fixes one evaluation environment; applying it after changing
canonical inventory still requires residual-lookup agreement. The executable cases check both
assemblies at their own derived data.

The 69 cases cover LB/LBU, every byte offset, boundary byte values, inactive byte 300, repeated
keys and three malformed rows. On the 64-active-plus-one-inactive workload:

| Metric | Original | Replacement |
|---|---:|---:|
| Dedicated / residual provider rows | 65 / 800 | 0 / 800 |
| Assembly cells | 18,594 | 17,359 |
| Assertions | 16,786 | 15,616 |
| Raw interactions | 2,360 | 2,230 |
| Fixed lookup occurrences | 0 | 130 |

The fixed table has 256 rows. These are counts for the dedicated-provider assembly, not backend
timings, R1CS costs or a whole-machine speedup. Executable tests close Byte balance; State,
Memory and Program remain visible demand. The universal assembly transport theorem carries its
own full balance premises.

## A small complete machine

[Counter](../SP1Clean/Soundness/Examples/Counter.lean) proves both directions for an actual Clean
ensemble over ZMod 97: natural endpoints in 0..15 and at most 15 increments. The transition
checks its predecessor in 0..14 and successor = predecessor + 1. The separate verifier enforces
each endpoint's 0..15 range through polynomial assertions and supplies the State endpoints.
Only transition rows enter the physical inventory and derived prover data. Ranked ledger recovery
orders all rows. Its data-only compiler is proved sound and complete without readiness premises.

[Counter tests](../SP1CleanTest/Alignment/Examples/Counter.lean) cover empty/maximal traces,
shuffled rows, missing/duplicate rows, bad endpoints/event counts and field wraparound:
(96,0) satisfies field addition but fails the actual fixed lookup. State balance alone accepts
an empty 16-to-16 trace; the verifier's public checks reject it. A trace of `n` increments has
`2*n + 2` State occurrences and four additional public-check occurrences, including for `n = 0`.

```sh
lake build --wfail --iofail SP1CleanTest.Alignment.Examples.Counter
lake env lean scripts/counterExample.lean
```

[StateBalance](../SP1Clean/Soundness/Examples/StateBalance.lean) separately shows why balance
alone is insufficient: a disconnected cycle can balance without an exhaustive ranked trail.
It is a graph counterexample, not a full SP1 AIR exploit. The
[independent backend gadgets](../tools/backend-gadgets/README.md) exercise another boundary,
including alternate valid witnesses and R1CS mutations.
