# SP1Clean verification report

Snapshot date: 2026-07-27. The generated records in `docs/snapshots/` are authoritative for exact
declaration dependencies; rerun the commands below before citing this report for another commit.

## Executive assessment

The repository has a closed, nontrivial native AIR-to-Sail theorem for all 25 supported Core
instruction tables. Every registered chip has:

- native Clean soundness and completeness;
- a bridge to the generated RISC-V Sail semantics;
- a whole-chip proof against the complete extracted Rust assertion system; and
- a whole-chip proof against the complete active Rust interaction multiset.

The repository does not yet have a closed theorem from the exact 34-table upstream Core relation to
Sail. The remaining gap is system-table semantics and exact-to-native assembly, represented by the
uninstantiated `CoreAIRRefinementObligations` structure. The available
`sp1_air_*_of_obligations` declarations are conditional composition lemmas.

No main-library proof is deferred. This audit found no `sorry`, `stop`, project `axiom`, or `sorryAx`.

## Audited sources

| Component | Audited value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.31.0` |
| SP1 semantic source | `a630089d9ff484ec6f2feade8d0afbb1447eed11` |
| SP1 description | `v6.3.1-8-ga630089d9` |
| SP1 extractor overlay | `69a8377c6e5550451f40c81fca17459687cd0a8f` |
| Extractor patch digest | `a2c43cfab00280f5331a15ec251a8341a26ecf3baedcda22fec182915fbcf108` |
| Clean checkout | `8e6ce748743fbce2a56e42d346e7054863c665da` |
| LeanRV64D checkout | `793034f378c19c4374ab93755b785b9929db8ec1` |
| RISCV checkout | `e65c352acd9e5a530fe80653d35073daa0994926` |
| lean-sail checkout | `79b4d08505af29d88b3918f32d29840fae1fa191` |
| PolyFun checkout | `502582b4bf51cddac166d3faed9ee2bfa5a2b7cc` |

The local path dependencies are migration checkouts. Reproducible immutable dependency pins remain a
release requirement.

The extractor overlay is a descendant of the semantic source with that source as its merge base. The
diff under `crates/core/machine/src` changes only reflection imports/derives needed to expose row
shapes; it does not change an AIR equation or trace-population function. Exporter changes and dirty
patches are separately hash-checked before generation.

## Verification stack and status

| Layer | Main artifact | Result |
|---|---|---|
| Native chip semantics | 25 `GeneralFormalCircuit`s | closed soundness and completeness |
| ISA refinement | 25 `ChipKind.advance` bridges | closed for the supported RV64IM routes |
| Whole-chip AIR faithfulness | `supportedChipFaithfulness` | exact 25-table coverage |
| Native machine grounding | `supported_core_witness_grounding` | closed |
| Native AIR-to-Sail | `supported_core_native_sound` | closed, shard-local, explicit boundary premises |
| Exact Rust AIR relation | `CoreAIR.Current.Relation` | complete 34/6-table list-level relation |
| Exact Rust AIR-to-Sail | `sp1_air_sound_of_obligations` | conditional; bundle not instantiated |
| Cross-shard execution | `SP1ExecutionRelation` | target relation specified; no soundness theorem yet |
| Core verifier | `VerifierKnowledgeSound` composition API | cryptographic proof not implemented here |
| Whole-machine completeness | intended Clean witness generation | not yet declared |

## Closed capstone statement

`supported_core_native_sound` consumes:

```text
native public-input equality
+ all native Clean constraints
+ four-channel balance
+ committed Program and provider/boundary semantics
+ Memory provider uniqueness
+ pulled high-timestamp range
+ an ordinary 8-tick machine schedule
```

and produces:

```text
a successful shard-local Sail execution
of the statement's program
between the public PC and clock endpoints
using exactly the active decoded rows
```

The theorem does not consume boot or halt hypotheses and does not conclude either fact. It also does
not derive its provider/boundary premises from the exact upstream system tables. Those scope
restrictions are in the relation definitions, rather than prose assumptions.

## Faithfulness audit

The exact instruction profile contains 25 tables. `Faithful/SupportedMachine.lean` stores 25 actual
`ChipFaithful` propositions and their proofs. It proves:

- the certificate length equals the native registry length;
- its table-name order equals the native registry's physical order; and
- its table tags are a permutation of `CoreProfile.instructionTables`.

Each `ChipFaithful` proposition is bidirectional for local assertions. It is not merely a claim that
the two systems agree on traces produced by the honest witness generator. Interaction equality is
proved on every locally accepted row, modulo permutation and zero-multiplicity entries.

The system tables are handled differently: their complete generated lists are used directly in the
exact relation. They do not yet have native semantic-table faithfulness theorems, because the native
ensemble uses a smaller proof-oriented provider interface. Connecting those two interfaces is the
remaining exact Core refinement task.

## Exact AIR coverage

The generated runtime manifest and hand-readable profile agree on:

- 34 execution-cluster tables and every main/preprocessed width;
- 6 memory-boundary-cluster tables and every width; and
- 160 base-field public-value cells.

The exact execution cluster contains:

- Program, Byte, and Range preprocessed tables;
- 25 instruction tables; and
- SyscallCore, SyscallInstrs, MemoryBump, StateBump, MemoryLocal, and Global.

The separate memory-boundary cluster contains Program, Byte, Range, MemoryGlobalInit,
MemoryGlobalFinalize, and Global.

The current Rust Core machine sources do not use `is_first_row`, `is_last_row`, or transition-window
selectors. Consequently the list-only row extraction does not omit a separate transition family at
this pin. This is a source-review fact and must be repeated on every pin change.

`CoreAIR.Current.Balance.Valid` requires equality of natural send/receive multiplicities. This is
stronger than a bare field-sum equality and is the correct source for execution soundness. The future
ArkLib theorem must show why verifier acceptance extracts that stronger relation.

## COMMIT provenance

The report distinguishes three statements:

1. the program executed and halted;
2. every COMMIT row that occurs contains the correct digest word; and
3. all eight COMMIT rows occur.

AIR provides the second statement. Program correctness of the standard halt wrapper provides the
third. The verification key prevents program substitution only after its program binding is proved.

The base shard and execution relations therefore require no wrapper assumption.
`SP1CommitCoveredExecutionRelation` is an optional strengthening derived from
`UsesStandardHaltWrapper` or `OutputSafeVerifyingKey`. Neither condition currently proves that the
digest hashes a modeled output byte stream.

## Proof and axiom audit

`scripts/run_audit.sh` performs:

- dependency and SP1 pin reporting;
- a zero-tolerance source proof-deferral scan;
- a zero-tolerance project-axiom scan;
- `skipKernelTC` and main-library `native_decide` guards;
- a heartbeat-override ratchet; and
- a generated `#print axioms` census over the released theorem surface.

Current classes in the census are:

| Class | Interpretation |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | accepted Lean/mathlib logical baseline |
| generated `bv_decide` constants | kernel-checked bit-vector proof artifacts used by selected lemmas |
| Sail platform hooks | external operations present in the generated official model |
| generated `native_decide` constants | compiler-trusted tests, confined to `SP1CleanTest/` |
| `sorryAx` | forbidden; current count is zero |

The Sail model's hooks include reservation, floating-point, randomness, and platform termination
operations. The supported ordinary instruction path does not intend to execute most of them, but a
theorem whose target is the complete generated interpreter inherits dependencies from that target and
its reduction lemmas. The raw census discloses this boundary instead of describing the headline theorem
as depending only on three logical axioms.

There are 51 textual `native_decide` occurrences in the test library (the conformance batteries plus the `NonVacuity.lean` chip-assumptions witnesses) and none in the main library.
They check witness and complete-trace conformance and are not imported by the soundness theorem.

## Trusted or externally assumed components

| Boundary | Why it is present | Closure plan |
|---|---|---|
| SP1 constraint compiler/exporter | translates Rust AIR expressions to Lean lists | pin/diff/hash checks plus independent `ChipFaithful` proofs |
| Generated Sail platform hooks | official model leaves platform operations external | narrow the model interface or prove concrete platform refinements |
| Native semantic boundary relation | native provider tables must mean the selected program/state | derive from exact Program/Memory/Global system tables |
| Timestamp high bound | prevents wrap in MemoryAccess ordering | derive from exact public timestamp/range and memory permutation |
| `SyscallHandler` | Sail does not implement SP1 host syscalls | prove concrete handlers for claimed syscalls |
| Preprocessed commitment | verifying key must bind the Program/provider trace | discharge in PCS/ArkLib layer |
| Exact natural balance | execution needs a real multiset, not modular equality | extract with LogUp/GKR soundness and bounds |
| Shard ledger cryptography | cumulative sums and deferred proofs are recursive-proof facts | prove in recursion/verifier layer |
| Standard halt wrapper | needed only for all-eight COMMIT coverage | prove from exact committed ROM |

These are theorem inputs or tool/model trust boundaries, not undisclosed Lean axioms.

## Open correctness work

The critical remaining proof is not another instruction chip. It is:

```text
exact instruction tables
  + exact system tables
  + exact public/preprocessed data
  → eventful Sail shard relation
```

Specifically:

- transport all 25 exact instruction traces through the coverage certificate;
- derive native provider, memory uniqueness, and timestamp facts from the system tables;
- prove the mixed ordinary/syscall schedule and exact syscall transcript;
- instantiate `CoreAIRRefinementObligations`;
- compose authenticated shards from boot to HALT; and
- integrate ArkLib with a probabilistic knowledge-soundness theorem.

See [`roadmap.md`](roadmap.md) for the dependency order.

## Reproduction

Run from the repository root:

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

The final command regenerates:

- `scripts/axiom_probe.lean`; and
- `docs/snapshots/axiom-census.txt`.

An unknown declaration makes the probe fail. A new proof deferral, project axiom, forbidden kernel
bypass, main-library `native_decide`, unexpected heartbeat-site increase, or `sorryAx` carrier makes the
audit fail.
