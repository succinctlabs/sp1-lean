# Completion target

This document describes the intended finished verification stack. It is a completion contract, not a
claim about the current repository. For current status, read [`overview.md`](overview.md).

## The final claim is a composition of three proofs

The project should end with three independently auditable layers:

```text
structured Core proof accepted by verifyCore
  │
  │ ArkLib knowledge soundness, with an explicit error bound
  ▼
exact full Core AIR witness
  │
  │ deterministic SP1 AIR soundness
  ▼
authenticated shard execution in the official Sail model
  │
  │ ledger continuity, full-state stitching, and final-halt reasoning
  ▼
boot-to-halt execution of the verification-key-bound guest program
```

The layers must not be collapsed into an unconditional theorem of the form
`verifyCore proof = true → ∃ valid execution`. A polynomial-commitment proof system provides
probabilistic knowledge soundness, so the final theorem must retain its extractor, assumptions, and
failure probability.

## Layer 1: executable Core verifier

An executable Lean `verifyCore` should agree with the pinned Rust Core verifier on a structured proof
representation. Parsing may initially be delegated to a canonical Rust exporter, provided the exported
structure and its refinement boundary are explicit.

Completion requires:

- a pinned Core verifier configuration;
- agreement on transcript order, domain sizes, commitments, and public values;
- no conflation with Compressed, Plonk, or Groth16 verifier targets; and
- a separate completeness theorem for honestly generated proofs.

## Layer 2: ArkLib knowledge soundness

ArkLib should prove that verifier acceptance yields, except with an explicit bounded probability, an
extractable witness satisfying the exact relation in `Faithful/CoreAIR.lean`.

The extracted fact must cover:

- the complete 34-table execution cluster;
- the separate 6-table memory-boundary cluster when required by recursion;
- every row's generated `assertZero` list;
- the complete public-value block;
- the preprocessed-trace commitment;
- exact natural interaction multiplicities, not only a field-valued sum;
- transcript, LogUp/GKR, zero-check, PCS, commitment, and Fiat--Shamir assumptions; and
- all trace-size and multiplicity bounds used to rule out modular wraparound.

The deterministic postprocessor should be the closed future declaration:

```lean
sp1_air_refinement
```

It should map the extracted witness without making proof-dependent choices. Its existential corollary
should be:

```lean
sp1_air_sound
```

The current `_of_obligations` declarations become internal assembly lemmas once
`CoreAIRRefinementObligations` has a closed construction.

## Layer 3: SP1 AIR to execution

`sp1_air_sound` should establish one honest eventful shard:

- the verification-key-bound program and entry point;
- a canonical boundary shard when `is_execution_shard = 0`;
- an execution shard whose decoded ordinary rows are exact Sail steps;
- 8 ticks for ordinary instructions and 264 ticks for raw syscall events;
- ordered State and Memory behavior derived from the system AIR;
- correct public-value endpoints;
- correctness of every COMMIT/COMMIT_DEFERRED row that exists, including the one-way fact that such
  a row sets its shard's rolling flag; and
- the exact public-values transition laws that freeze a digest after its rolling flag is set.

The proof should reuse:

- the 25 whole-chip `ChipFaithful` anchors;
- `supported_core_native_sound` and its timed-grounding lemmas;
- the exact system-table list anchors; and
- explicit syscall-handler contracts.

It should not add a second instruction semantics or a bespoke operation-level faithfulness layer.

## Whole-execution composition

Shard soundness is not a halting theorem. A separate `sp1_execution_sound` should consume:

- the authenticated public-values ledger;
- complete Sail-state equality between consecutive execution shards;
- program and verification-key consistency;
- global cumulative-sum validity;
- authenticated deferred-proof digests;
- boot reachability of the first execution state; and
- a final successful HALT with the committed exit code.

The base execution theorem should remain independent of public-output wrapper behavior. If an
application wants all eight COMMIT indices, it should additionally prove
`CommitCoveringVerifyingKey` or `UsesStandardHaltWrapper` for the exact committed program. Combined
with ledger continuity, `completeCommitDigestMatches_of_coveredExecution` then ties all eight rows to
the terminal committed digest. A later, stronger output theorem must also model output bytes and the
wrapper's hashing behavior.

## Final verifier theorem

The final theorem should have the shape:

```text
verifier acceptance
  + cryptographic assumptions
  + application/program contracts
  ⇒ extractor succeeds and returns a boot-to-halt execution
    except with probability ε
```

Its trusted and assumed inputs must remain visible:

- the Lean kernel and disclosed logical axioms;
- the generated Sail model and its platform hooks;
- the canonical Rust/Lean verifier-refinement boundary;
- cryptographic assumptions and security parameters;
- the SP1 semantic pin and extraction-tool provenance; and
- any program-specific syscall or public-output contracts.

## Completeness follows as a separate project

Soundness does not prove that honest executions can be witnessed. The next project should use Clean's
exportable witness-generation machinery to prove:

1. a supported semantic execution produces native chip rows;
2. the rows satisfy every chip constraint and all channel balances;
3. the native rows reconfigure to valid exact upstream rows;
4. the Rust/Lean witness generators agree on the supported input domain; and
5. the proof system accepts the constructed AIR witness.

The semantic source relation must be restricted to trace-generatable, supported executions. Claiming
completeness for every Sail execution would be false because the current Core profile and syscall
handler do not implement every behavior in the full Sail model.

## Done criteria

The AIR-to-execution workstream is complete when all of the following hold:

- `CoreAIRRefinementObligations` has a closed construction from the exact extracted relation and
  narrowly stated external contracts;
- unqualified `sp1_air_refinement` and `sp1_air_sound` are declared;
- the six Core system tables and required memory-boundary tables are semantically grounded;
- syscall handler behavior claimed by the theorem has a concrete refinement proof;
- boot-to-halt shard composition is proved separately;
- no proof deferrals or project axioms appear in the released theorem graph;
- every generated pin, table, width, and axiom census guard passes; and
- the human-facing report states the cryptographic, Sail, extraction, and program-level trust
  boundaries without folding them into “AIR soundness.”
