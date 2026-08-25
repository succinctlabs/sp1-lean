# SP1 v1.0 release audit

Snapshot date: 2026-08-06, re-audited on the Lean v4.31 -> v4.32.2 + Sail v4 -> v5 migration. The
generated records in `docs/snapshots/` are authoritative for exact declaration dependencies; rerun the
commands below before citing this report for another commit.

## Executive assessment

The repository has a closed, nontrivial native AIR-to-Sail theorem for all 25 supported Core
instruction tables. Every registered chip has:

- native Clean soundness and completeness;
- a bridge to the generated RISC-V Sail semantics;
- a whole-chip proof against the complete extracted Rust assertion system; and
- a whole-chip proof against the complete active Rust interaction multiset on every locally
  accepted reconstructed row in the codec image, modulo permutation and zero-multiplicity entries.

The repository does not yet have a closed theorem from the exact 34-table upstream Core relation to
Sail. Local exact-to-native assembly is now proved. The remaining gap is deriving the explicit
global balance/count, preprocessing and program authentication, memory-boundary semantics, and
application-level semantic binding needed to instantiate the unclosed
`CoreAIRRefinementObligations` structure. The available
`sp1_air_*_of_obligations` declarations are conditional composition lemmas.

No main-library proof is deferred. This audit found no `sorry`, `stop`, project `axiom`, or `sorryAx`.

## Audited sources

| Component | Audited value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.32.2` |
| SP1 semantic source | `f66b4bff51d0ccff51d152e0f7f66b2ffedf3529` |
| SP1 description | `v6.4.0` |
| SP1 extraction branch | `b5616f908c393d6050970630871f69afe233a21c` (`dtumad/lean-extraction`, `v6.4.0-10-gb5616f908`) |
| mathlib pin | `905b95818eb32af7874a58b427f50c1711a5e96c` (tag `v4.32.2`) |
| Clean pin | `2dad7788d58b09eabeb3898506e4cb896e5d3e9d` (**fork** — see below) |
| Lean_RV64D pin | `befc6976ef53c592b637dc897f61b4e71467c239` |
| Sail compiler source | `41694abd58b27b687af5db275810dfeb8a88cfc0` (rems-project/sail, `sail2`) |
| sail-riscv model source | `61266bd4dede6c7dd6e903e52dc80bcbf644b1b8` (riscv/sail-riscv, `master`) |
| SP1 Sail config | sha256 `41311181e4cad458c21b01a0160a0087b407ee15e616243013169d52d3c1a854` (`scripts/sail-config/sp1_rv64d_cfg.json`) |
| RISCV pin | `d1d678c67f3039b5fb8a9c5aba76904c5793756b` |
| lean-sail pin | `079463134b9c50450b8393e1566a09fc492a34d9` (tag `v5`) |
| PolyFun pin | `d062ba2cbb3a50ba5b9f3ba349ca003e6c79630a` (upstream `main`) |

Every dependency is an immutable git pin — `lake-manifest.json` records no `path` entries, so a clean
clone reproduces this graph. `Lean_RV64D` is pinned to a **generated** snapshot on
`succinctlabs/sail-riscv-lean` (branch `sp1/config-generated-4.32.2`; the `sp1-rv64d-v1.0` tag marks
the earlier four-key snapshot and deliberately was not moved): the
pinned Sail compiler + sail-riscv sources above run against the schema-shaped SP1 platform config,
reproducible via `scripts/sail-config/generate_lean_rv64d.sh` (`docs/agents/sail-model-provenance.md`).
It equals the opencompl base `11d8fa21` except the four platform-value sites the two-key config sets
(PMP-off moved to a Lean-side hypothesis, 2026-08); the
snapshot's commit message carries the full provenance record. `RISCV` is pinned to the head of the
open opencompl PR #59; repoint it to opencompl once that merges.

**`Clean` is pinned to a fork, and that is a change to the trust base.** The DSL every circuit in
this project is built on is no longer upstream `Verified-zkEVM/clean` but `dtumad/clean`, branch
`sp1-integration`. The base is upstream `0e53b9f2` (the previous pin); the delta is two changes,
one branch per upstream PR:

| Commit | Branch | What it changes |
|---|---|---|
| `f5ae8e17` | `agreesbelow-data-hint` | `ProverEnvironment.AgreesBelow` gains `∧ env.data = env'.data ∧ env.hint = env'.hint`, plus three accessors and `agreesBelow_rfl` |
| `8301b77a` | `agreesbelow-data-hint` | Adds `Clean/Examples/DataWitness.lean` — a worked example, no change to any existing declaration |
| `410ffba8` | `witgen-share` | Adds `Clean/Circuit/WitnessShare.lean` (`WitgenIR.share`, subterm sharing into let-steps) and the `Operations.witgenJsonShared?` serializer entry — pure additions plus one refactor of `witgenJson?` through a shared `witgenJsonList?` with identical output |
| `4a9c2c7b` | `witgen-share` | Proves `WitgenIR.eval_share` (`ir.share.eval env = ir.eval env`, axiom-clean) — the sharing pass is a proven transformation |

The `witgen-share` change exists because the wire format serializes expression *trees*: without
sharing, this repo's DivRem witness programs serialize to 1.22 GB (two single programs at 552 MB);
with the pass applied at serialization the committed payload is 1.04 MB, and an external
interpreter's evaluation cost drops proportionally.

`AgreesBelow` sits in *hypothesis* position everywhere except one discharge site, so the change
weakens every obligation that mentions it and strengthens the two theorems that conclude with it
(`Circuit.proverEnvironment_usesLocalWitnesses`, `Circuit.witgen_usesLocalWitnesses`); no Clean
conclusion is weakened. The reason it cannot live in this repo's additive `ToClean` library is that
Clean's own `witgen_usesLocalWitnesses` refers to Clean's `AgreesBelow`, not ours — a local copy with
the stronger hypothesis yields a *weaker* obligation and would not feed it.

The change is a bug fix rather than an ergonomics request: `not_computable_from_cells_alone` in the
example file proves that the previous obligation was **false** for any witness program reading
`FExpr.dataGet`, not merely hard to discharge.

**Exit condition: re-pin to upstream as soon as the PR merges.** Until then this fork is the one
dependency in the table that is not upstream, and the axiom census is unaffected by it (verified: the
census is unchanged across the re-pin). Fork state, the PR queue, and the standing rule for what may
go in the fork versus `ToClean/` are recorded in `docs/agents/clean-upstream.md`.

The extraction branch is a descendant of the semantic source with that source as its merge base, and
every extraction change is an ordinary commit on it — there is no uncommitted-patch mechanism. The
diff under `crates/core/machine/src` changes only reflection imports/derives needed to expose row
shapes; it does not change an AIR equation or trace-population function. The generator verifies the
merge base, the changed-file allowlist, the derive-only machine diff, and a clean worktree before it
writes any artifact. Changes to `IntoShape`, the constraint compiler, and the symbolic IR are a
separate pinned trusted-extractor surface: their paths are fail-closed by the allowlist and their
bytes by the exact commit, but the gate does not label them semantically inert.

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
| Core verifier | `VerifierBoundary.PerfectExtraction` composition API | cryptographic proof not implemented here |
| Native ensemble completeness | `supported_core_native_functionalCompleteness` | closed for the deterministic all-25 compiler on its explicit admissible semantic image |
| Broader semantic-language completeness | shared capacity-bounded semantic relation | open two-sided relation alignment plus residual semantic/footprint implications; no language equality claimed |

`supported_core_native_complete` is the existential projection of a proof-independent functional
compiler. It computes all native physical rows, refreshes, Memory boundaries, and canonical
Byte/Range/Program providers from the supplied semantic execution; constraints and all four channel
balances are proved. Its explicit admissible source still requires the named event-validity,
provider-semantic, and actual-footprint facts. Proving those on an intended bounded source is not
by itself enough to combine this theorem with exact soundness: the current soundness target is
unbounded and does not record the Core row cap or physical capacity. Public-language equality first
requires a shared capacity-bounded semantic relation (or equivalent two-sided refinement).

## Closed capstone statement

`supported_core_native_sound` consumes:

```text
native public-input equality
+ all native Clean constraints
+ four-channel balance
+ committed Program and provider/boundary semantics
+ Memory provider uniqueness
+ an ordinary 8-tick machine schedule
```

It does **not** consume a pulled-timestamp range premise: the `< 2^24` bound on every pulled
Memory record's high clock limb is derived inside the capstone from the per-location Memory
balance (`pushGood`/`pullGood` in `SP1Clean/Soundness/AIR.lean`), so `SupportedCoreNativeRelation`
is exactly the ensemble relation plus the semantic boundary binding.

and produces:

```text
a successful shard-local Sail execution
of the statement's program
between the public PC and clock endpoints
(constructed by the proof from exactly the active decoded rows)
```

The exported target relation states only the program/endpoint facts; the row-exactness fact lives
in the intermediate `supported_core_witness_grounding` theorem and is discarded by the final
existential. The theorem does not consume boot or halt hypotheses and does not conclude either
fact. It also does not derive its provider/boundary premises from the exact upstream system
tables. The endpoint/program scope restrictions are in the relation definitions, rather than
prose assumptions.

## Faithfulness audit

The exact instruction profile contains 25 tables. `Faithful/SupportedMachine.lean` stores 25 actual
`ChipFaithful` propositions and their proofs. It proves:

- the certificate length equals the native registry length;
- its table-name order equals the native registry's physical order; and
- its table tags are a permutation of `CoreProfile.instructionTables`.

Each `ChipFaithful` proposition is bidirectional for local assertions **after** an arbitrary
extracted Rust row is decoded and reconstructed as its canonical native physical row. It is not
merely a claim about rows produced by the honest witness generator, but it also does not quantify
over every possible physical native assignment outside that codec image. Interaction equality is
proved on every locally accepted reconstructed row, modulo permutation and zero-multiplicity
entries.

The system tables are handled differently: their complete generated lists are used directly in the
exact relation. StateBump and MemoryBump retain native chips and whole-table faithfulness anchors.
The rest do not acquire artificial row-wise native counterparts, because the native ensemble uses a
proof-oriented provider interface (28 provider/boundary tables alongside the 25 instruction chips —
a 53-table Clean ensemble). The provider family contains six Byte-op tables, all 17 Range widths
`0..16`, Program, MemoryInit, MemoryFinalize, MemoryBump, and StateBump; the complete Range family
closes the provider side of honest shift-row lookups. `SP1Clean/Composition/{PreprocessedProviders,
MemoryBoundary,SystemTables,ProviderSegment,CoreEnsemble}.lean` now constructively connects the two
local interfaces under a caller-supplied `CanonicalPreprocessedInventory` and proves all 53 native
tables plus the verifier row satisfy their constraints.
Byte/Range/Program counts are recounted from the actual Clean interaction ledger of the verifier,
25 transported instruction tables, MemoryInit/MemoryFinalize, and both bumps rather than copied from
the larger exact cluster. The raw exact Byte/Range/Program assertion lists are empty.
`CoreAIR.PreprocessedBinding` only records the named matrix/PCS-opening premise, to be discharged by
ArkLib; it proves neither row-local meaning nor provider selection. `PreprocessedProviderContract`
is the explicit caller premise for row-local semantics. Source main
multiplicities are not reused and raw projected keys are not assumed unique. The caller-supplied
`CanonicalPreprocessedInventory` selects carriers backed by the matching source matrix/Range-width
block and explicitly carries projected-key `Nodup`; zero-demand raw keys may be omitted. The recount
contract separately states nonzero Byte/Program-key coverage, skeleton nonpositivity, and canonical
capacity. `freshRowsByKey` is only declarative/regression support. PCS/program identity,
State/Memory balance, and semantic binding remain separate and explicit. The recount derives Byte
(including Range) and Program
integer balance; the global contract retains all-channel count bounds and State/Memory integer
balance. The remaining exact Core refinement task is global across those contracts and the named
public-range and Global→Memory transformations.

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

The AIR layer is responsible for the second statement (the obligations bundle's
`publicCommitOperand`/`deferredCommitOperand` fields — stated, not yet discharged). It also supplies
the one-way row-to-flag implications and the public-values transition laws (all three, like the
operand fields, are stated obligations — not yet discharged from the exact tables). Together with recursion's
ledger continuity, `finalCommitRowsMatch_of_execution` proves that every existing row is tied to the
terminal digest; it never infers row existence from a flag. Program correctness of the standard halt
wrapper provides the third statement. The verification key prevents program substitution only after
its program binding is proved.

The base shard and execution relations therefore require no wrapper assumption.
`SP1CommitCoveredExecutionRelation` is an optional strengthening derived from
`UsesStandardHaltWrapper` or `CommitCoveringVerifyingKey`.
`completeCommitDigestMatches_of_coveredExecution` proves all eight covered rows match the terminal
digest. Neither program condition currently proves that the digest hashes a modeled output byte
stream.

## Proof and axiom audit

`scripts/run_audit.sh` performs:

- manifest-resolved pin reporting, gating any present `.lake` checkout against the manifest;
- recorded-value cross-checks (`scripts/check_pins.sh`: lakefile ↔ manifest ↔ this report's pin
  table ↔ `CoreProfile.sp1SemanticRevision` ↔ the authoritative census ledger and raw snapshots);
- root-index completeness (`scripts/check_root_index.sh`) and doc-citation resolution
  (`scripts/check_report_citations.sh`);
- a zero-tolerance source proof-deferral scan;
- a zero-tolerance project-axiom scan;
- `skipKernelTC` and main-library `native_decide` guards;
- an elaboration-budget escape-hatch prohibition (allowlist-gated); and
- a generated `#print axioms` census over the released theorem surface, split by library and
  diffed against the committed `docs/snapshots/axiom-census.txt` (main) and
  `docs/snapshots/axiom-census-test.txt` (test anchors) — drift fails; only `--update` rewrites
  the snapshots, so a passing run leaves the tree clean. The mechanically checked main/test counts
  and total live only in `docs/snapshots/axiom-ledger.md`.

CI runs the three cross-check gates in its fast `guards` job, the harness's main scope
(`--main-only`) in a dedicated `audit` job on the built `SP1Clean` oleans, and the test-scope
census (`--test-only`) in the `test` job right after `lake test` produces the `SP1CleanTest`
oleans that probe needs.

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

The test library's `native_decide` occurrences (the exportability battery's prime instance, the
`NonVacuity.lean` chip-assumptions witnesses, the `NonVacuityReal.lean` real-row satisfiability
battery, and the independent-audit joint-premise regression) are confined there; none are in the
main library, and none are imported by the soundness theorem. Trace conformance against SP1's
real prover no longer uses `native_decide` at all: it is the dump-anchored pipeline — committed
`chip_traces` dumps at the extraction pin (`export/sp1dump/`, byte-reproducible), the fail-closed
generation-time gate in `scripts/witgenExport.lean --testdata` (every event row of all 25 chips
recomputed and matched cell-for-cell), and the independent Rust interpreter differential.

## Trusted or externally assumed components

| Boundary | Why it is present | Closure plan |
|---|---|---|
| SP1 constraint compiler/exporter | translates Rust AIR expressions to Lean lists | pin/diff/hash checks plus independent `ChipFaithful` proofs |
| Generated Sail platform hooks | official model leaves platform operations external | narrow the model interface or prove concrete platform refinements |
| Two-key generated Sail config | `clint`/`simple_interrupt_generator` disabled at four generated value sites — devices SP1 does not implement, whose stock defaults make the memory-bridge lemmas false as stated | stays config-generated; the generation pins and config hash are gated by `check_pins.sh` |
| `SailConfigured` platform state | the theorems' initial-state hypotheses select SP1's platform on the Lean side: machine mode, no enabled interrupts, `MPRV`/`mseccfg`/PMM off, no HTIF, PMP all-OFF (`h_pmp_off`), and the single RWX PMA region `[2^16, 2^48)` | discharge per-field from SP1's boot/ELF-load contract; the PMA window and PMP-off are the platform selection itself (verification-report §3.2) |
| Native semantic boundary relation | native provider tables must mean the selected program/state | derive from exact Program/Memory/Global system tables |
| `SyscallHandler` | Sail does not implement SP1 host syscalls | prove concrete handlers for claimed syscalls |
| Preprocessed commitment | verifying key must bind the Program/provider trace | discharge in PCS/ArkLib layer |
| Exact natural balance | execution needs a real multiset, not modular equality | extract with LogUp/GKR soundness and bounds |
| Shard ledger cryptography | cumulative sums and deferred proofs are recursive-proof facts | prove in recursion/verifier layer |
| Standard halt wrapper | needed only for all-eight COMMIT coverage | prove from exact committed ROM |
| Opcode enum and routing source mirror | `SP1Clean/Model/Opcode.lean`'s 53 names/discriminants are kernel-checked against the generated, pin-checked `Extracted/OpcodeTable.lean` artifact by `opcodeTable_matchesExtracted`; the single `supportedChips` descriptor still mirrors `tracing.rs`'s opcode→chip dispatch by hand, while the coverage proofs tie that descriptor to the 25-chip registry and exhaust the extracted opcode alphabet | extract the routing dispatch itself on a future SP1 pin; until then review the one descriptor against `tracing.rs` |

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

- discharge `ExactNativeGlobalContract` from the exact interaction argument: all-channel count
  bounds, State/Memory integer balance, and the semantic program/boundary binding;
- authenticate and construct the source-backed preprocessing inventory, and close the named
  Range13→Range16 and raw-Global→typed-Memory transformations (the 25 instruction tables and
  complete 28-table provider/system tail are already constructed under those explicit contracts);
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

The final command regenerates the two probe sources and validates their output against the committed
census snapshots:

- `scripts/axiom_probe.lean` and `scripts/axiom_probe_test.lean` are always regenerated;
- `docs/snapshots/axiom-census.txt` and `docs/snapshots/axiom-census-test.txt` are read-only in the
  normal audit and are rewritten only by `scripts/run_audit.sh --update` from a clean committed tree.

An unknown declaration makes the probe fail. A new proof deferral, project axiom, forbidden kernel
bypass, main-library `native_decide`, non-allowlisted elaboration-budget directive, or `sorryAx` carrier
makes the audit fail.
