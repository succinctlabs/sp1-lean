<div align="center">

![SP1 Lean](./.github/assets/header.png)

Formal verification of SP1 Hypercube zkVM arithmetization

</div>

## What this repository proves

This is a Clean-native Lean 4 verification of SP1's Core RISC-V AIR, anchored to the unmodified Rust
source at `a630089d9ff484ec6f2feade8d0afbb1447eed11`
(`v6.3.1-8-ga630089d9`).

The current closed capstone is:

```lean
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound SupportedCoreNativeRelation
      (SupportedCoreLocalExecutionRelation model)
```

It proves that a valid, balanced witness for the 25-chip native Clean machine, with explicit
program/provider and timestamp bindings, yields a genuine shard-local execution of the generated
RISC-V Sail model between the public PC and clock endpoints.

All 25 supported instruction chips have:

- native Clean soundness and completeness proofs;
- Sail instruction-step bridges;
- whole-chip equivalence with the complete extracted Rust assertion system; and
- whole-chip equality of active interaction multisets.

The proof-bearing coverage certificate is tied to the exact upstream 25-table instruction profile.
The main library has no `sorry`, `stop`, project `axiom`, `sorryAx`, `skipKernelTC`, or
`native_decide`.

## What is not yet proved

The repository also contains a complete list-level model of the pinned upstream Core AIR:

- the exact 34-table execution cluster;
- the separate 6-table memory-boundary cluster;
- every table's complete assertion and interaction lists;
- the 160-cell public-value block; and
- a preprocessed-commitment and exact natural interaction-balance relation.

That exact upstream relation has not yet been connected all the way to Sail. The remaining work is to
derive the native theorem's program/provider, memory-uniqueness, timestamp, and syscall facts from the
six Core system tables.

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

COMMIT-row correctness and row existence are also kept separate. AIR proves that every canonical row
that exists carries the correct digest word. Complete eight-row coverage is an optional program-level
contract of the verification-key-bound standard halt wrapper; output-byte and hashing semantics are not
yet modeled.

## Repository layout

- `SP1Clean/Math/` — generic word, carry, bit-vector, and arithmetic lemmas.
- `SP1Clean/Model/` — SP1 buses, Sail state/execution, schedules, and syscall interfaces.
- `SP1Clean/Extracted/` — generated Rust row/list oracles, manifest, and provenance.
- `SP1Clean/FormalModel/` — semantic contracts and public witness relations.
- `SP1Clean/Native/` — independent native Clean circuits.
- `SP1Clean/Proofs/` — circuit soundness/completeness and Sail bridges.
- `SP1Clean/Faithful/` — whole-chip native ↔ Rust AIR equivalence.
- `SP1Clean/Soundness/` — registry, typed grounding, and machine capstones.
- `SP1CleanTest/` — isolated compiler-trusted witness/trace conformance tests.

## Build and audit

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

The audit regenerates a 513-declaration `#print axioms` census and checks source deferrals, project
axioms, forbidden kernel bypasses, main-library `native_decide`, and performance-budget drift.
Sail-model platform hooks, selected generated `bv_decide` proof constants, and the trusted extraction
toolchain are disclosed in the report.

## Documentation

Start with:

1. [`docs/overview.md`](docs/overview.md) — current theorem, coverage, and limitations.
2. [`docs/architecture.md`](docs/architecture.md) — proof and module structure.
3. [`docs/release-audit.md`](docs/release-audit.md) — source pins, trust boundary, and audit result.
4. [`docs/roadmap.md`](docs/roadmap.md) — the dependency-ordered path to full Core soundness.
5. [`docs/goal-overview.md`](docs/goal-overview.md) — completed-state verifier and completeness goals.

Clean's upstream proof and performance documentation is authoritative for circuit proof style. See
[`AGENTS.md`](AGENTS.md) and [`docs/agents/proof-patterns.md`](docs/agents/proof-patterns.md) before
changing nontrivial proofs.

## Toolchain note

Lean and mathlib are on 4.31. Clean, LeanRV64D, RISCV, and lean-sail are temporarily local path
dependencies during migration. Restore immutable published git pins before a release, and do not run a
bare `lake update`.
