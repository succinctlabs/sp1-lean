# Roadmap

The native 25-chip soundness theorem, every registered chip contract, and every whole-chip
faithfulness proof are closed. The critical path is no longer chip remediation. It is the semantic
interpretation of the exact upstream Core system tables.

## Current checkpoint

Completed:

- 25 native instruction circuits with soundness and completeness;
- 25 Sail bridges and `ChipKind.advance` registrations;
- 25 whole-chip `ChipFaithful` proofs;
- deterministic typed row decoding and exhaustive ranked State ordering;
- Program and Memory timed grounding for the native 36-table ensemble;
- `supported_core_native_sound`;
- exact list-level 34-table execution and 6-table memory-boundary relations;
- honest COMMIT-row versus wrapper-coverage separation; and
- zero main-library proof deferrals or project axioms.

Not completed:

- a closed `CoreAIRRefinementObligations` value;
- exact upstream system-table grounding;
- cross-shard boot-to-halt soundness;
- concrete syscall-handler refinements beyond the abstract relation;
- ArkLib verifier knowledge soundness; and
- whole-machine witness-generation completeness.

## P0: close exact Core AIR soundness

### 1. Transport all instruction tables

Build one registry-driven adapter from exact Rust instruction traces to the native instruction slice.
For each physical upstream row:

- use the chip's bijective row codec;
- use `ChipFaithful.constraints` to transport local validity;
- use `ChipFaithful.interactions` to transport the active interaction multiset; and
- preserve exact natural multiplicity counts when rows are concatenated.

The adapter must consume `supportedChipFaithfulness`, so adding or removing a Core instruction table
creates an explicit coverage failure. Do not write 25 unrelated top-level dispatch lists.

Deliverable: a theorem that projects the exact 25 instruction tables into the instruction part of a
valid native witness, with assertion and bus-balance transport proved once at the registry layer.

### 2. Ground preprocessed and system tables

Prove the semantic facts currently supplied to `SupportedCoreNativeRelation` from the exact upstream
tables:

- Program: the committed ROM and decoded Program-provider messages;
- Byte and Range: lookup-provider coverage;
- MemoryLocal and MemoryBump: per-location access order and timestamp differences;
- StateBump: State ordering across sparse clock ranges;
- Global: the public boundary and cumulative interaction facts;
- MemoryGlobalInit/Finalize: initial/final memory values and per-location uniqueness; and
- SyscallCore/SyscallInstrs: raw syscall transcript consistency.

This work should target the existing `InitialBoundaryFacts`,
`SupportedCoreMemoryTimestampRangeRelation`, and event structures. Extend those contracts only when the
exact upstream AIR proves a materially stronger fact that is needed by correctness.

The main correctness risks to audit are:

- no modular-wrap inference where natural ordering is required;
- no inference of provider uniqueness from ordinary channel balance alone;
- no inference that equal PC/timestamp endpoints imply equal complete Sail states;
- no silent use of the memory-boundary cluster as an execution cluster; and
- no transition constraint omitted by the list extractor on a future Rust pin.

### 3. Assemble ordinary and syscall events

The final shard decoder must preserve physical execution order and the mixed schedule:

- ordinary supported rows: one real Sail step and 8 ticks;
- raw ECALL rows: one `CoreSyscallEvent` and 264 ticks;
- boundary shards: no execution trace and unchanged PC/timestamp.

Keep `SyscallHandler` as the narrow host-semantics interface. Initially model only the syscall behavior
required for baseline Core soundness and the standard halt path. Add precompile handlers only with the
corresponding complete table clusters and semantic refinements.

Do not derive COMMIT-row existence from `SyscallInstrs` or a rolling public flag. AIR proves only the
operand of a row that exists.

### 4. Construct the exact refinement bundle

Instantiate every field of `CoreAIRRefinementObligations` from the preceding theorems and narrowly
stated external contracts. Then publish:

```lean
sp1_air_refinement
sp1_air_sound
```

At that point the `_of_obligations` declarations may remain as internal composition helpers.

Acceptance criteria:

- source is exactly `CoreAIR.Current.Relation binds .execution`;
- target is `SP1CoreShardExecutionRelation`;
- the map is a total deterministic function of statement and AIR witness;
- no field simply restates the final target as an assumption;
- the proof consumes all 34 execution-cluster tables;
- the memory-boundary cluster is used only where its own relation is authenticated; and
- the audit remains `sorryAx`-free.

## P1: compose shards from boot to HALT

Prove a separate `sp1_execution_sound` against `SP1ExecutionRelation`.

Required inputs:

- the authenticated public-values ledger;
- verification-key/program consistency;
- full Sail-state continuity between consecutive execution shards;
- valid non-execution boundary shards;
- global cumulative-sum balance;
- deferred-proof digest authentication;
- boot reachability of the first execution state; and
- a final HALT with the public exit code.

PC and timestamp continuity are necessary but insufficient; the composition proof must carry the
complete machine state.

Public-output coverage remains an optional strengthening:

1. prove `UsesStandardHaltWrapper` for the exact committed standard guest, or
   `OutputSafeVerifyingKey` for the verification key;
2. derive all-eight `CompleteCommitCoverage`; and
3. add output-byte and hashing semantics before calling the result full public-output authentication.

Add deferred-COMMIT coverage only if a downstream theorem needs it.

## P2: ArkLib verifier integration

Pin the Core verifier target and prove:

- executable Lean/Rust verifier agreement on structured proofs;
- transcript and Fiat--Shamir refinement;
- LogUp/GKR knowledge soundness;
- zero-check and PCS knowledge soundness;
- commitment and preprocessed-trace binding;
- extraction of exact natural interaction multiplicities with bounds; and
- a composed probabilistic `sp1_verifier_sound` with an explicit failure probability.

Compressed, Plonk, and Groth16 are separate targets. Do not broaden the Core theorem implicitly.

## P3: extractable witness generation and completeness

Use Clean's witness-generation IR to replace sampled conformance with proved construction:

- generate every native instruction and provider row from supported execution events;
- prove row constraints and all channel balances;
- reconfigure the native trace to the exact upstream trace;
- connect the construction to SP1's Rust `generate_trace`; and
- prove proof-system completeness separately.

The source relation must express supported, trace-generatable executions and concrete syscall handler
behavior. Existing `SP1CleanTest` batteries remain regression tests during this work but are not a
substitute for the theorem.

## Maintenance gates

Every phase ends with:

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

On an SP1 pin change:

- compare the unmodified Rust machine source first;
- regenerate the runtime table/width/public-value manifest;
- re-audit first/last/transition selector use;
- regenerate every list anchor and conformance vector;
- update both semantic and extractor provenance;
- prove the 25-table coverage permutation again; and
- treat a cluster, width, interaction-kind, or schedule change as an architecture change, not a
  mechanical version bump.
