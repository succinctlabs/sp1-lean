<div align="center">

![SP1 Lean](./.github/assets/header.png)

Formal verification of SP1 Core instruction AIRs and native AIR-to-execution refinement

</div>

## What this repository proves

This is a Clean-native Lean 4 verification of SP1's Core RISC-V instruction chips and native
53-table AIR-to-execution layer, anchored to the unmodified Rust source at
`f66b4bff51d0ccff51d152e0f7f66b2ffedf3529`
(`v6.4.0`).

The current closed capstone is:

```lean
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model)
```

It proves that a valid, balanced witness for the 25-chip native Clean machine, with an explicit
program/provider binding, yields a genuine shard-local execution of the generated RISC-V Sail model
between the public PC and clock endpoints.

All 25 supported instruction chips have:

- native Clean soundness and completeness proofs;
- Sail instruction-step bridges;
- whole-chip equivalence with the complete extracted Rust assertion system on the canonical
  native physical row reconstructed from each extracted Rust row; and
- on extracted Rust rows satisfying the complete assertion system, whole-chip equality of active
  interaction multisets.

The proof-bearing coverage certificate is tied to the exact upstream 25-table instruction profile.
The main library has no `sorry`, `stop`, project `axiom`, `sorryAx`, `skipKernelTC`, or
`native_decide`.

A converse-shaped **native witness-assembly** theorem is proved too:
`supported_core_native_complete` constructs a native ensemble witness satisfying
`SupportedCoreNativeRelation` — all 53 tables plus the
verifier row, every physical row computed by the circuits' own generators — from a supplied trace
whose obligations are explicit: `WellFormed`; `ProviderMultiplicitiesFit` (`2 * m ≤ p`, making each
aggregate provider count the canonical nonnegative centered representative); exact centered-integer
per-key `BalancedOn` plus the separate interaction-count bound `< p`; public-value equality; and
`SemanticBoundaryBinding`. This is not yet machine-level semantic completeness: no theorem turns an
arbitrary supported Sail execution into that trace.

`SP1CleanTest/Audit/ActiveTraceNonVacuity.lean` nevertheless exercises the implemented assembly path
with a hand-assembled semantic trace record for `JAL x0, 0`. Its instruction-event count and decoded
physical instruction-row count are both one; the matching native provider occurrences close all four
buses, completeness circuit-generates the AIR rows, and soundness yields the official-Sail local
execution for any supplied `SP1MachineModel` satisfying `UsesOrdinarySchedule`. This is an active
non-vacuity anchor, not a verified or full trace generator. See the
verification report, §7.4.

## What is not yet proved

The repository also contains a complete list-level model of the pinned upstream Core AIR:

- the exact 34-table execution cluster;
- the separate 6-table memory-boundary cluster;
- every table's complete assertion and interaction lists;
- the 160-cell public-value block; and
- a preprocessed-commitment and exact natural interaction-balance relation.

That exact upstream relation has not yet been connected all the way to Sail, though the two theorem
families are no longer disconnected. `SP1Clean/Composition/` turns each chip's whole-chip
`ChipFaithful` anchor into a table-level transport — a valid extracted table becomes a native Clean
table satisfying the whole native circuit's constraints — and proves the twenty-five transported
tables *are* the ensemble's instruction tables. The separate generic `transportTable_spec` reaches a
chip's semantic contract only when its native `Assumptions` and channel `Guarantees` are also supplied;
the exact assembly theorem itself claims local constraints, not row semantics.

The transport now covers the whole *local* native artifact. Given valid exact execution and
memory-boundary witnesses **plus a caller-supplied `CanonicalPreprocessedInventory` and the named
preprocessing, memory-boundary, and public-limb transport contracts**, the construction produces all
25 instruction tables and all 28 redistributed provider/system tables; `CoreEnsemble.lean` assembles
those 53 tables plus the verifier row and
proves their complete local constraints. The provider tail has six Byte-op tables, one Range table
for every width `0..16`, Program, MemoryInit, MemoryFinalize, MemoryBump, and StateBump. Supporting
all 17 Range widths is load-bearing: honest shift rows request widths outside the former
`8/13/14/16` subset and can now balance without an impossible provider key.

Exact Byte/Range/Program multiplicities are deliberately recounted from the constructed native
consumer skeleton: the verifier, 25 transported instruction tables, MemoryInit/MemoryFinalize, and
both bump tables, after projecting their actual Clean interactions. They are not copied from the full
34-table exact cluster, whose counts include consumers absent from the native 53-table slice.
The raw exact Byte/Range/Program assertion lists are empty. `CoreAIR.PreprocessedBinding` only
records the named matrix/PCS-opening premise, to be discharged by ArkLib; it proves no row-local
meaning or provider selection. That meaning is the explicit caller premise
`PreprocessedProviderContract`; exact
main multiplicities are not reused, and raw projected keys are not claimed duplicate-free. The
caller-supplied `CanonicalPreprocessedInventory` selects demand-oriented carriers
partitioned by native provider. Every selected carrier must be backed by the matching exact source
matrix (and, for Range, the matching width block), while projected-key `Nodup` is a field of the
selected inventory itself. Raw keys with zero native demand may be omitted. The recount contract then
requires coverage of every nonzero Byte/Program consumer key, consumer nonpositivity, and canonical
count capacity. PCS/program identity, State and Memory balance, and semantic boundary binding remain
separate explicit contracts. `freshRowsByKey` is only a declarative/small-regression
canonicalization, not the construction path.
`ExactBalance.lean` and the access-permutation theorems provide reusable
exact-payload/native-key transport lemmas. `CoreArtifact.lean` exposes the remaining
`ExactNativeGlobalContract` explicitly:
all-channel interaction-count bounds, exact centered-integer balance for State and Memory, and
semantic program/boundary binding combine with the explicit provider-recount contract to imply
`SupportedCoreNativeRelation` and hence an official-Sail local execution for any supplied model
satisfying `UsesOrdinarySchedule`. Byte (including Range) and Program integer balance are derived by
the recount. No theorem yet jointly witnesses those contracts with valid exact clusters.

What remains is assembling those explicit contracts from two auditable sources: exact-Core / ArkLib
extraction must supply the recount preconditions, all-channel interaction-count bounds, and exact
State/Memory balance, while PCS authentication must justify the caller-supplied source-backed
inventory and program identity. Loader, platform, code-memory, program, and memory-boundary contracts
supply the remaining semantic binding.
The named non-literal seams are the upstream public-value Range13 quotient versus the native Range16
boundary lookup, raw `Global` versus typed native Memory, preprocessing/program authentication,
memory-boundary semantics, and syscall facts. The exact system/public-value
artifacts also contain constants encoded canonically for SP1's KoalaBear field, so the final closed
exact-v6.4.0 capstone must be stated at that concrete field (or consume a proved literal-
interpretation contract); native chip and grounding theorems remain field-generic.

The available exact-AIR declarations are deliberately conditional:

```lean
sp1_air_refinement_of_obligations
sp1_air_sound_of_obligations
```

Their `CoreAIRRefinementObligations` argument is not currently instantiated. The unqualified
`sp1_air_refinement` and `sp1_air_sound` names are reserved for the future closed theorem.

Boot-to-halt shard composition and ArkLib verifier knowledge soundness are separate downstream
theorems. This repository does not claim that verifier acceptance deterministically implies an
execution without cryptographic assumptions and an error bound.

## Architecture

The stable verification boundary is a whole SP1 chip:

```text
native Clean circuit
  ├─→ semantic chip contract
  ├─→ official Sail instruction behavior
  └─→ complete extracted Rust AIR row relation
```

Rust helper operations and Lean proof gadgets may be decomposed differently. Extraction emits only row
shapes and ordered assertion/interaction lists; it does not generate Clean circuits.

At machine level, State, Program, Memory, and Byte are ordinary structural Clean channels. Global
execution meaning is derived by deterministic typed decoding, ranked State ordering, Program
commitment, and timed per-location Memory grounding. It is not smuggled into channel guarantees.

COMMIT-row correctness and row existence are also kept separate. The AIR layer's obligations
bundle requires that every canonical row that exists carries the correct digest word (stated as
the `publicCommitOperand` obligation, not yet discharged). Complete eight-row coverage is an
optional program-level contract of the verification-key-bound standard halt wrapper; output-byte
and hashing semantics are not yet modeled.

## Repository layout

- `SP1Clean/Math/` — generic word, carry, bit-vector, and arithmetic lemmas.
- `SP1Clean/Model/` — SP1 buses, Sail state/execution, schedules, and syscall interfaces.
- `SP1Clean/Extracted/` — generated Rust row/list oracles, manifest, and provenance.
- `SP1Clean/FormalModel/` — semantic contracts and public witness relations.
- `SP1Clean/Native/` — independent native Clean circuits.
- `SP1Clean/Proofs/` — circuit soundness/completeness and Sail bridges.
- `SP1Clean/Faithful/` — extracted-Rust-row → canonical-native-row whole-chip comparison.
- `SP1Clean/Soundness/` — registry, typed grounding, and machine capstones.
- `SP1CleanTest/` — isolated compiler-trusted witness/trace conformance tests.

## Build and audit

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

The audit regenerates the released-declaration `#print axioms` census and checks source deferrals,
project axioms, forbidden kernel bypasses, main-library `native_decide`, and performance-budget
drift. The sole numeric count is maintained and mechanically checked in the
[`axiom ledger`](docs/snapshots/axiom-ledger.md).
Sail-model platform hooks, selected generated `bv_decide` proof constants, and the trusted extraction
toolchain are disclosed in the report.

## Documentation

Each document has one role; start with the one that matches yours:

1. [`docs/overview.md`](docs/overview.md) — the ten-minute orientation: current theorem, coverage,
   and limitations.
2. [`docs/verification-report.md`](docs/verification-report.md) — the self-contained technical
   report that argues and evidences each claim, for external reviewers.
3. [`docs/architecture.md`](docs/architecture.md) — proof and module structure, design rules, and
   the deliberate layering exceptions.
4. [`docs/release-audit.md`](docs/release-audit.md) — machine-checked source pins, trust boundary,
   and audit result.
5. [`docs/roadmap.md`](docs/roadmap.md) — the dependency-ordered path to full Core soundness.
6. [`docs/goal-overview.md`](docs/goal-overview.md) — completed-state verifier and completeness
   goals (a contract, not current status).

Clean's upstream proof and performance documentation is authoritative for circuit proof style. See
[`AGENTS.md`](AGENTS.md) and [`docs/agents/proof-patterns.md`](docs/agents/proof-patterns.md) before
changing nontrivial proofs.

## License

Dual-licensed under either of [Apache License 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT),
at your option. Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this repository by you shall be dual-licensed as above, without any additional
terms or conditions.

## Toolchain note

Lean and mathlib are on **v4.32.2**, and every dependency is an immutable git pin, so a clean clone
builds this project. The generated Sail model (`sail-riscv-lean`) is pinned to a snapshot
regenerated from pinned sources plus a checked-in SP1 platform configuration
(`scripts/sail-config/`) — see
[`docs/agents/sail-model-provenance.md`](docs/agents/sail-model-provenance.md) for what the config
sets and why stock upstream is not usable. Do not run a bare `lake update`; update one
`[[require]]` at a time.
