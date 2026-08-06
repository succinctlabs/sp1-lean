# Verification overview

*Snapshot: 2026-08, branch `dtumad/v1.0-release`. Lean and mathlib v4.32.2; generated Sail model
paired with lean-sail v5; SP1 semantic pin `v6.3.1-8-ga630089d9`. Recorded pins are
machine-cross-checked by `scripts/check_pins.sh`; see `release-audit.md` for the full table.*

This repository proves a substantial SP1 AIR-to-execution result, but it does not yet prove full
upstream Core AIR soundness.

The closed capstone is `supported_core_native_sound`. It says that a satisfying, balanced witness for
the 25-chip native Clean machine, together with explicit program/boundary and memory-timestamp
relations, determines a genuine shard-local execution of the generated RISC-V Sail model. The exact
v6.3.1 upstream AIR is separately represented by complete extracted assertion and interaction lists.
All 25 native instruction chips are now proved faithful to their corresponding upstream tables. The
remaining top-level work is to derive the native theorem's semantic boundary facts from the upstream
Core system tables and then instantiate the exact-AIR refinement bundle.

No Lean proof in `SP1Clean/` is deferred: the audit finds no `sorry`, `stop`, project `axiom`, or
`sorryAx`. That fact should not be confused with completion of every desired theorem. Open work is
represented by theorem premises or by theorem names that are intentionally not declared.

## The theorem that is fully proved

The current semantic capstone is:

```lean
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model)
```

Its source relation has three visible parts:

1. `SupportedCoreEnsembleRelation`
   - the witness public input equals the statement;
   - every native Clean table constraint holds; and
   - all four Clean channels balance.
2. `SP1SemanticBoundaryRelation`
   - the program is well formed and bound to the shared prover data;
   - a concrete initial Sail state has the public PC and clock;
   - ROM is loaded, the Sail configuration is valid, and code memory is compatible;
   - Program-provider rows describe that program; and
   - Memory-init and Memory-finalize provider rows have the required meaning and per-location
     uniqueness.
3. `SupportedCoreMemoryTimestampRangeRelation`
   - the high component of each pulled memory timestamp is below the 24-bit physical bound needed by
     SP1's timestamp-difference argument.

From those facts the proof deterministically decodes the physical rows, obtains an exhaustive
State-bus order, grounds Program and Memory accesses at every position, applies the registered chip
contract, and constructs a successful Sail chain. The resulting local segment:

- uses the statement's program;
- starts and ends at the public PC and clock boundaries; and
- consists of exactly the active physical instruction rows.

It does not say that the initial state is reachable from boot, that the final row halts, that shards
compose, or that a cryptographic verifier accepted a proof. Those are deliberately separate claims.

Two time views coexist under this statement by design. The general
`Machine.SP1MachineModel.schedule` event model covers both the ordinary 8-tick and syscall 264-tick
windows; the fixed eight-tick micro-time layer (`ordinaryClkInc`/`ramEffectOffset`/
`regEffectOffset`, named for the Rust `CLK_INC` and `MemoryAccessPosition` constants they track) is
the proved register/RAM interpretation the ordinary-row grounding engine consumes. The theorem's
`UsesOrdinarySchedule` hypothesis is the explicit bridge; unifying the two models is roadmap work
(`architecture.md` § deliberate layering exceptions).

## Current coverage

| Layer | Current coverage | Status |
|---|---:|---|
| Native instruction circuits | 25 / 25 supported tables | soundness and completeness proved |
| Sail instruction bridges | 25 / 25 supported tables | proved |
| Whole-chip Rust AIR faithfulness | 25 / 25 supported instruction tables | proved |
| Grounding contracts used by the native capstone | 25 / 25 descriptors | proved |
| Exact upstream execution cluster | 34 tables | complete list-level relation present |
| Exact upstream memory-boundary cluster | 6 tables | complete list-level relation present |
| Whole-chip Rust trace conformance | 10 chips | executable test evidence, not a theorem premise |
| Exact upstream AIR to Sail | 34-table execution cluster | open bundle; conditional combinator only |
| Cross-shard boot-to-halt execution | full shard ledger | relation specified; theorem not yet declared |
| Cross-shard ledger predicate layer | `Contracts/PublicValues.lean` | reserved API, declared ahead of its consumer |
| ArkLib verifier knowledge soundness | Core verifier | out of this workstream's current proof |

The 25 instruction tables are Add, Addi, Addw, Sub, Subw, Bitwise, Lt, ShiftLeft, ShiftRight, Jal,
Jalr, Branch, UType, five load tables, four store tables, Mul, DivRem, and AluX0. The theorem
`supportedChipFaithfulness_upstream` proves that the proof-bearing faithfulness index is a permutation
of the exact `CoreProfile.instructionTables` list. It also tracks the physical order of the native
`supportedChips` registry.

`ChipFaithful` is a whole-row statement. For every adversarial Rust row it proves equivalence between:

- the complete upstream `assertZero` list; and
- the native Clean component's complete constraint predicate.

On accepted rows it also proves equality, up to permutation and removal of zero-multiplicity entries,
of the complete active interaction multiset. Rust helper operations and Lean proof gadgets may be
factored differently; they are not separate public proof boundaries.

## The exact upstream AIR boundary

The semantic Rust source is pinned to:

```text
a630089d9ff484ec6f2feade8d0afbb1447eed11
v6.3.1-8-ga630089d9
```

The list-only extractor uses a separately pinned descendant. Its machine-source delta from the
semantic revision consists only of reflection derives/imports; exporter changes are hash-checked
outside the AIR definitions. The generated manifest fixes table membership, row widths, preprocessed
widths, and the 160-cell public-values width.

`CoreAIR.Current.Relation` contains:

- exact heterogeneous row types for every table;
- the complete generated assertion and interaction list for every row;
- the complete public-value assertion and interaction block;
- exact cluster membership and nonempty active traces;
- a verifying-key/preprocessed-trace binding; and
- equality of canonical natural send/receive multiplicities.

The final item is intentionally stronger than a modular field equality. An ArkLib LogUp/GKR
knowledge-soundness theorem must justify extraction of that natural multiset fact, with the appropriate
bounds and error probability.

At this pin, the Core machine AIR sources do not call first-row, last-row, or transition-window
selectors. The exported row lists therefore do not omit a separate next-row constraint family.
Changing the Rust pin requires rechecking this fact as well as regenerating the manifest and lists.

## Why full `sp1_air_sound` is not yet declared

`CoreAIRRefinementObligations` names the remaining deterministic proofs from the exact execution
cluster to an eventful Sail shard:

- public-value and program well-formedness;
- verification-key/program binding and entry point;
- first-execution-shard facts;
- syscall transcript decoding and per-existing-row digest operands;
- the non-execution boundary case; and
- the execution case, including system-table grounding into an exact event trace.

The last field is the main semantic theorem, not bookkeeping. No closed value of this structure exists
today. The available declarations are therefore deliberately named:

```lean
sp1_air_refinement_of_obligations
sp1_air_sound_of_obligations
```

They are useful, proved composition lemmas, but they are not evidence that the obligations have been
discharged. The unqualified names `sp1_air_refinement` and `sp1_air_sound` are reserved for the closed
construction.

The missing bridge is concentrated in the six non-preprocessed Core system tables:
`SyscallCore`, `SyscallInstrs`, `MemoryBump`, `StateBump`, `MemoryLocal`, and `Global`. It must derive
the native boundary/provider/timestamp facts, handle the 8-tick ordinary and 264-tick syscall schedule,
and connect syscall rows to an explicit host-handler contract. It must reuse the 25 chip-faithfulness
proofs rather than restating instruction semantics.

## COMMIT rows and public output

The AIR constrains each canonical COMMIT or COMMIT_DEFERRED row that exists. It does not prove the
converse that a rolling flag implies such a row exists.

Accordingly:

- `CommitRowsMatch` is an AIR-level, per-existing-row property;
- `CompleteCommitCoverage` means that all eight public digest indices occur across the whole
  execution;
- `UsesStandardHaltWrapper` is the program-level condition that supplies that coverage; and
- `OutputSafeVerifyingKey` packages the condition for every program admitted by a verification key.

The base execution relation does not assume wrapper use. The optional
`SP1CommitCoveredExecutionRelation` adds coverage only when one of those program contracts is supplied.
The model does not yet connect output bytes to the wrapper's hash computation, so complete COMMIT-event
coverage is not full guest-public-output authentication.

## Trust and assumptions

The audit separates proof incompleteness from external trust:

- Lean checks the main proof library; standard logical dependencies are `propext`,
  `Classical.choice`, and `Quot.sound`.
- Selected bit-vector lemmas use `bv_decide` and disclose their generated proof constants.
- The official generated Sail target contains platform hooks for reservation, floating-point, random,
  and termination behavior. A theorem stated over that target inherits those hooks even when the
  supported RV64IM path does not execute them.
- The SP1 constraint compiler and extraction overlay are trusted, pin-checked source-to-list tools.
  Generated outputs are not treated as self-authenticating; whole-chip `ChipFaithful` proofs compare
  them with the native circuits.
- `native_decide` is forbidden in `SP1Clean/`. It appears only in `SP1CleanTest/` for executable witness
  and trace conformance, where compiler trust is explicitly accepted.
- Cryptographic commitments, PCS opening, LogUp/GKR, Fiat--Shamir, and verifier extraction remain the
  responsibility of the later ArkLib layer.

The semantic boundary and timestamp relations in `SupportedCoreNativeRelation` are theorem premises,
not hidden axioms. Full upstream soundness requires deriving them from the exact system AIR and
cryptographic binding relations.

Three named link predicates (`TraceStateLink`, `TraceByteLink`, `TraceMemClkValid`) appear in the
standalone per-bus consistency modules as their honestly-stated premises. They are **not** premises
of `supported_core_native_sound`: the capstone's premise surface is exactly the three relation
conjuncts above plus the `UsesOrdinarySchedule` schedule hypothesis, and no module on its proof
path references the link predicates.

## Reproduce the current checkpoint

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

The audit regenerates the declaration list and raw `#print axioms` census and compares it against
the committed snapshot (drift fails; `--update` rewrites deliberately). It also cross-checks every
recorded pin and doc-cited count against the build graph.

Where to go next: [`release-audit.md`](release-audit.md) for the machine-derived pins and census;
[`verification-report.md`](verification-report.md) for the argued long-form report;
[`architecture.md`](architecture.md) for module ownership and the deliberate layering exceptions;
[`roadmap.md`](roadmap.md) for the remaining dependency order; [`README.md`](README.md) for the
one-role-per-document map.
