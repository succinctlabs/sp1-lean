# Verification overview

*Snapshot: 2026-08, repository tree at this document's commit. Lean and mathlib v4.32.2; generated Sail model
paired with lean-sail v5; SP1 semantic pin `v6.4.0`. Recorded pins are
machine-cross-checked by `scripts/check_pins.sh`; see `release-audit.md` for the full table.*

This repository proves a substantial SP1 AIR-to-execution result, but it does not yet prove full
upstream Core AIR soundness.

The closed capstone is `supported_core_native_sound`. It says that a satisfying, balanced witness for
the 25-chip native Clean machine, together with an explicit program/provider boundary relation,
determines a genuine shard-local execution of the generated RISC-V Sail model. The required pulled
memory-timestamp bound is derived inside the theorem from Memory balance; it is not a separate
premise. The exact
v6.4.0 upstream AIR is separately represented by complete extracted assertion and interaction lists.
All 25 native instruction chips are proved faithful to their corresponding upstream tables. The two
exact clusters, **when paired with a caller-supplied `CanonicalPreprocessedInventory` and the named
preprocessing, memory-boundary, and public-limb transport contracts**, now construct the complete
local 53-table native artifact and verifier
row, with every local constraint proved. The remaining top-level work is global: derive the
provider-recount preconditions, all-channel count bounds, and State/Memory balance from
exact-Core/ArkLib extraction; authenticate the caller-supplied source-backed inventory and its program
identity through PCS; combine those facts with explicit loader, platform, code-memory, program,
memory-boundary, and handler contracts for `SemanticBoundaryBinding`; prove that combined contract jointly inhabitable
with valid exact clusters; then
instantiate the exact-AIR refinement bundle.

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

Its source relation has two visible parts:

1. `SupportedCoreEnsembleRelation`
   - the witness public input equals the statement;
   - every native Clean table constraint holds — the ensemble has 53 tables: the 25 instruction
     chips plus 28 provider/boundary tables (six Byte-op providers, 17 Range providers for every
     width `0..16`, the Program-ROM provider, the two Memory init/finalize boundary tables, and the
     two SP1 system tables MemoryBump and StateBump); and
   - all four Clean channels balance.
2. `SP1SemanticBoundaryRelation`
   - the program is well formed and bound to the shared prover data;
   - a concrete initial Sail state has the public PC, and the committed prover data carries the
     public initial clock;
   - ROM is loaded, the Sail configuration is valid, and code memory is compatible;
   - Program-provider rows describe that program; and
   - Memory-init and Memory-finalize provider rows have the required meaning and per-location
     uniqueness.

Those two conjuncts are the whole hypothesis. In particular the 24-bit range fact on each pulled
memory timestamp — needed by SP1's timestamp-difference argument, and formerly a third companion
relation — is now *derived* inside the proof from the per-location Memory balance: every record on
the produced side of that balance carries the bound (the boundary provider pins both init clock
limbs to zero, instruction rows inherit it from the range-checked public shard-time ceiling, and
MemoryBump rows range-check it in-circuit), so every pulled record does too.

From those facts the proof deterministically decodes the physical rows, obtains an exhaustive
State-bus order, grounds Program and Memory accesses at every position, applies the registered chip
contract, and constructs a successful Sail chain. The resulting local segment:

- uses the statement's program;
- starts and ends at the public PC and clock boundaries; and
- is constructed by the proof from exactly the active physical instruction rows (the exported
  relation states the endpoint facts; row exactness lives in the intermediate grounding
  theorem).

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
| Native instruction circuits | 25 / 25 supported tables | soundness and completeness proved (completeness-witness scope disclosed below) |
| Sail instruction bridges | 25 / 25 supported tables | proved |
| Whole-chip Rust AIR faithfulness | 25 / 25 supported instruction tables | proved |
| Grounding contracts used by the native capstone | 25 / 25 descriptors | proved |
| Exact upstream Core shard | paired 34-table execution + 6-table Memory-boundary clusters | complete list-level source relation present |
| Exact clusters + named transport contracts → local native ensemble artifact | 53 tables + verifier | constructed; all local constraints proved |
| Active hand-assembled semantic trace → circuit-generated native AIR → Sail anchor | 1 JAL-x0 row | one event and one decoded physical instruction row; four-bus balance, native relation, and local execution proved for any supplied ordinary-schedule model |
| Whole-chip Rust trace conformance (dump-anchored gate) | 25 chips | executable test evidence, not a theorem premise |
| Exact upstream AIR to Sail | paired 34+6-table shard witness | open 12-field AIR bundle plus explicit external context; conditional combinator only |
| Cross-shard boot-to-halt execution | full shard ledger | relation specified; theorem not yet declared |
| Cross-shard ledger predicate layer | `Contracts/PublicValues.lean` | reserved API, declared ahead of its consumer |
| ArkLib verifier knowledge soundness | Core verifier | out of this workstream's current proof |

The 25 instruction tables are Add, Addi, Addw, Sub, Subw, Bitwise, Lt, ShiftLeft, ShiftRight, Jal,
Jalr, Branch, UType, five load tables, four store tables, Mul, DivRem, and AluX0. The theorem
`supportedChipFaithfulness_upstream` proves that the proof-bearing faithfulness index is a permutation
of the exact `CoreProfile.instructionTables` list. It also tracks the physical order of the native
`supportedChips` registry.

The native completeness layer now has a proof-independent compiler for all 25 instruction tables.
It folds the `EventExecutionTrace` deterministically evaluated from the common
`CoreShardSemanticWitness`, inserts the required State/Memory refreshes,
constructs both Memory boundaries, and closes Byte/Range/Program demand from the trace's own Clean
ledger. Provider balance is proved directly in the field, so the old `2 * multiplicity ≤ p`
restriction is gone; only the actual interaction-list footprint `< p` remains.

`supported_core_native_functionalCompleteness` proves the resulting 53-table witness satisfies the
same native relation consumed by soundness on `SupportedCoreNativeAdmissibleShardRelation`.
That source restricts the common bounded shard relation by named residual semantic readiness facts
and the physical `< p` footprint for the deterministic compiler output. Both
directions use the same `CoreProfile.WithinOrdinaryRowLimit` policy, and
`supported_core_native_shard_sound` targets that same bounded semantic relation. The remaining
scope gap is exactly `NativeShardTraceTotal`, not missing tables, bump placement, provider
closure, a second execution carrier, or an existential trace generator.

`ChipFaithful` is a whole-row statement. For every adversarial Rust row it proves equivalence between:

- the complete upstream `assertZero` list; and
- the native Clean component's complete constraint predicate.

On accepted rows it also proves equality, up to permutation and removal of zero-multiplicity entries,
of the complete active interaction multiset. Rust helper operations and Lean proof gadgets may be
factored differently; they are not separate public proof boundaries.

## The exact upstream AIR boundary

The semantic Rust source is pinned to:

```text
f66b4bff51d0ccff51d152e0f7f66b2ffedf3529
v6.4.0
```

The list-only extractor uses a separately pinned descendant branch (every extraction change an
ordinary commit on it). Its machine-source delta from the semantic revision consists only of
reflection derives/imports. Shape projection, symbolic IR, compiler, and trace-tool changes live on
a separate explicit trusted-tooling surface at the exact extraction pin; their allowlisting is not
a semantic-inertness proof. The generated manifest fixes table membership, row widths,
preprocessed widths, and the 160-cell public-values width.

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

Two exact system/public-value artifacts use constants canonically encoded for SP1's KoalaBear field
(`Global`/`SyscallInstrs`, plus public-value curve seeds). Therefore a closed exact-v6.4.0 capstone
must be concrete at KoalaBear unless it first proves an explicit literal-interpretation contract.
The native instruction and grounding results remain field-generic; that scope does not automatically
extend to the full exact system relation.

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
- the one-way row-to-flag implications and the public-values COMMIT transition laws;
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

The local bridge is now constructive under its exact hypotheses: valid exact instruction and
memory-boundary clusters, a caller-supplied `CanonicalPreprocessedInventory`, and named
preprocessing, memory-boundary, and public-limb transport contracts assemble the native instruction,
provider, bump, and verifier rows and prove
their local constraints. Its Byte/Range/Program multiplicities are recounted from the actual Clean
interaction ledger of the verifier, 25 instruction tables, MemoryInit/MemoryFinalize, and both bumps,
not copied from the full exact cluster: the latter includes consumers that the native 53-table slice
intentionally omits. The raw exact Byte/Range/Program assertion lists are empty.
`CoreAIR.PreprocessedBinding` only records the named matrix/PCS-opening premise, to be discharged by
ArkLib; it proves neither row-local meaning nor provider selection. `PreprocessedProviderContract`
is the explicit caller premise for that meaning.
Source main multiplicities are not reused, and neither premise implies projected-key uniqueness. The caller supplies a
demand-oriented `CanonicalPreprocessedInventory`: its carriers are source-backed by the matching
Byte/Program matrix or Range-width block, and the selected projected keys are explicitly `Nodup`.
Zero-demand raw keys may be omitted. The recount contract separately states nonzero-demand
Byte/Program-key coverage, consumer nonpositivity, and canonical capacity. `freshRowsByKey` is only a
declarative/regression helper. PCS/program identity, State and Memory balance, and the semantic
boundary remain separate and explicit. The
missing bridge is the global interpretation concentrated in
`SyscallCore`, `SyscallInstrs`, `MemoryLocal`, `Global`, and the authenticated preprocessing/public
blocks. It must derive the artifact's named Range13-quotient→Range16 and raw-Global→typed-Memory
transformations, the native boundary/program meaning, the 8-tick ordinary and 264-tick syscall
schedule facts, and an explicit host-handler contract. The exact/native table access-permutation
lemmas are reusable ingredients; the unused full-exact-payload key-balance closure was retired.
`CoreArtifact` consumes an explicit recount contract to derive Byte
(including Range) and Program integer balance; `ExactNativeGlobalContract` retains all-channel count
bounds, State/Memory integer balance, and semantic binding. No joint inhabitance anchor for those
contracts and valid exact clusters exists. The bridge reuses the 25
chip-faithfulness proofs rather than restating instruction semantics.

## COMMIT rows and public output

The AIR constrains each canonical COMMIT or COMMIT_DEFERRED row that exists. It does not prove the
converse that a rolling flag implies such a row exists.

Accordingly:

- `CommitRowsMatch` is an AIR-level, per-existing-row property;
- `CommitRowsSetFlags` records the AIR-forced direction from an existing row to its shard flag
  (an obligations-bundle field — stated, not yet discharged from the exact tables);
- `CommitTransitionValid` records the public-values AIR laws that preserve a digest once the rolling
  flag is set;
- `CompleteCommitCoverage` means that all eight public digest indices occur across the whole
  execution;
- `UsesStandardHaltWrapper` is the program-level condition that supplies that coverage; and
- `CommitCoveringVerifyingKey` packages that coverage condition for every program admitted by a
  verification key.

The base execution relation does not assume wrapper use. The optional
`SP1CommitCoveredExecutionRelation` adds coverage only when one of those program contracts is
supplied. `completeCommitDigestMatches_of_coveredExecution` combines coverage with row-to-flag,
intra-shard digest freezing, and cross-shard ledger continuity, proving that every one of the eight
rows carries its word of the terminal committed digest. The model does not yet connect output bytes
to the wrapper's hash computation, so this is still not full guest-public-output authentication.

## Trust and assumptions

The audit separates proof incompleteness from external trust:

- Lean checks the main proof library; standard logical dependencies are `propext`,
  `Classical.choice`, and `Quot.sound`.
- Selected bit-vector lemmas use `bv_decide` and disclose their generated proof constants.
- The official generated Sail target contains platform hooks for reservation, floating-point, random,
  and termination behavior. A theorem stated over that target inherits those hooks even when the
  supported RV64IM path does not execute them.
- The SP1 constraint compiler and trace dumper are trusted, pin-checked source-to-artifact tools
  (one committed extraction branch). Generated outputs are not treated as self-authenticating;
  whole-chip `ChipFaithful` proofs compare the AIR lists with the native circuits, and the
  dump-anchored generation-time gate recomputes every dumped trace row cell-for-cell.
- `native_decide` is forbidden in `SP1Clean/`. It appears only in `SP1CleanTest/`, where compiler
  trust is explicitly accepted: the exportability battery and the satisfiability anchors,
  including the real-row battery (`SP1CleanTest/NonVacuityReal.lean`, a concrete satisfying
  `is_real = 1` row for every instruction chip's complete constraint system).
- Cryptographic commitments, PCS opening, LogUp/GKR, Fiat--Shamir, and verifier extraction remain the
  responsibility of the later ArkLib layer.

The semantic boundary relation in `SupportedCoreNativeRelation` is a theorem premise, not a hidden
axiom. Full upstream soundness requires deriving its authenticated provider-content/program portion
from the exact-system and cryptographic binding relations, while loader, platform, code-memory,
memory-boundary, and handler contracts remain explicit application premises. The single most
load-bearing such premise deserves naming here:
`SailCodeMemoryCompatible` — every store on the run preserves the program's ROM bytes. SP1 fetches
instructions from an immutable program table while unmodified Sail fetches from the same mutable
memory that stores write to; for a guest that overwrites its own code the two genuinely diverge, and
the theorem simply does not apply. Self-modifying programs are excluded by assumption, not proved
impossible.

The former standalone per-bus `Trace*Link` predicates and integer `*Lookups` shadows have been
retired. The capstone reads typed Clean interactions directly through `TypedState`, `TypedProgram`,
and `TypedMemory`; its premise surface remains the two relation conjuncts above plus the
`UsesOrdinarySchedule` schedule hypothesis.

## Reproduce the current checkpoint

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

The audit regenerates the declaration list and raw `#print axioms` census and compares it against
the committed snapshots (drift fails; `--update` rewrites deliberately). The current main/test split
and total live only in the mechanically checked [`axiom ledger`](snapshots/axiom-ledger.md), so this
reader document cannot carry a stale duplicate count. The audit also cross-checks every recorded pin
against the build graph.

Where to go next: [`release-audit.md`](release-audit.md) for the machine-derived pins and census;
[`verification-report.md`](verification-report.md) for the argued long-form report;
[`architecture.md`](architecture.md) for module ownership and the deliberate layering exceptions;
[`roadmap.md`](roadmap.md) for the remaining dependency order; [`README.md`](README.md) for the
one-role-per-document map.
