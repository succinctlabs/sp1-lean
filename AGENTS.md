# AGENTS.md

Guidance for AI agents working in this repository (`sp1-clean-native`).
`CLAUDE.md` is a one-line pointer to this file so Claude Code auto-loads it.

## What this repo is

A **Clean-native, semantically-specified** formal verification of SP1's RISC-V chips, built on the
**public** Clean DSL. The stable verification boundary is the **whole chip**:

1. proof-oriented Lean gadgets (`Native/Operations/` + local `Proofs/Operations/` lemmas) implement
   semantic arithmetic and are composed as true Clean subcircuits;
2. a native `GeneralFormalCircuit` chip has its own row type and semantic contract on the
   `FormalModel/Contracts/` audit surface;
3. a native Sail bridge proves that chip contract reaches the RISC-V Sail spec;
4. extraction supplies the complete Rust chip row, `assertZero` list, interaction list, and whole-chip
   populate traces; `Faithful/ChipOracle.lean` maps the native row to the Rust row and `ChipFaithful`
   compares the two complete assertion systems and interaction multisets.

Rust operations and Lean gadgets are complementary, not corresponding proof objects. They may use
different structs and decompositions. Do not add new operation-level faithfulness anchors,
Rust-generated circuits, or operation witness batteries. The direct-to-circuit generator and
`Extracted/Circuit/` have been removed; native circuit definitions are hand-maintained under `Native/`.
**The whole-chip oracle migration is complete (2026-07): all 25 supported instruction chips have
native rows, `Extracted/ChipOracle/<Chip>.lean` oracles, and native-row `ChipFaithful` proofs**;
`Faithful/SupportedMachine.lean` ties that proof-bearing index to the exact upstream
instruction-table profile. The remaining flat `Extracted/<Op>.lean` modules and per-op/reader
`Faithful/` anchors are deliberate **shared substrate** — canonical statement targets that multiple
chip oracles reference through one-line namespace bridges — not migration debt.

This project is **independent** of `sp1-lean`. It does **not** import `SP1Foundations`/`SP1Operations`/
`SP1Chips`/`SP1Clean` (those are 4.29 oleans — cross-toolchain), and does **not** use the legacy structural `correct_*` / `SailBridge` /
`fromMain`/`toMain` pattern. Needed foundations are re-created here (`Math/` + `Model/`). Every released
theorem must be proof-complete: no `sorryAx`. Pure chip/AIR proofs should normally show only
`[propext, Classical.choice, Quot.sound]`; selected `bv_decide` lemmas and the generated Sail target's
platform hooks are separately disclosed by the axiom census.
`update_extracted.py` does invoke SP1's constraint compiler and witness-dump tooling as a trusted,
pin-checked Rust oracle; generated outputs are never treated as self-authenticating.

The unmodified SP1 Rust semantic source lives in a sibling `sp1` checkout. Regeneration points `SP1_DIR`
at the separately hash-checked extraction overlay described in `docs/agents/extraction.md`; do not modify
the semantic checkout merely to run the exporter. The 4.29 `sp1-lean` repo is a read-only reference for porting (a sibling
`sp1-lean` checkout); its arithmetic/Sail proofs are the thing we re-derive natively here, not import.

### Larger verified-verifier program

This repository is presently the **AIR-to-execution** workstream, not yet an implementation of SP1's
cryptographic proof verifier. Keep the eventual claim split into three independently auditable layers:

1. an executable Lean `verifyCore` that agrees with the pinned Rust verifier on structured real proofs;
2. ArkLib knowledge soundness for the transcript, LogUp GKR, zero-check, PCS, commitments, and
   Fiat--Shamir transformation, yielding an extracted full AIR witness with an explicit error bound; and
3. `sp1_air_sound`, turning that faithful full AIR witness into the official Sail execution relation.

The final `sp1_verifier_sound` must be probabilistic/knowledge-soundness-shaped; do not claim the
unconditional deterministic implication `verifyCore = true -> exists valid execution` without the
cryptographic assumptions and error term. Completeness is a separate companion theorem.

These layers are parallel workstreams and may be owned by different developers. Core, Compressed,
Plonk, and Groth16 are separate verifier targets; pin **Core** first. Parsing may initially be delegated
to a canonical Rust exporter so it does not obscure the verifier/refinement boundary.

**This workstream's current priority:** instantiate the exact v6.3.1 Core AIR refinement bundle. Native
timed grounding, every one of the 25 chip contracts, and `supported_core_native_sound` are closed. The
34-table execution and 6-table memory-boundary relations exist, but full upstream soundness remains open
until the six Core system tables derive the native boundary/timestamp facts and
`CoreAIRRefinementObligations` has a closed construction. Until then only
`sp1_air_refinement_of_obligations`/`sp1_air_sound_of_obligations` are declared; the unqualified names
remain reserved. See `docs/roadmap.md` and `docs/architecture.md`.

## Build

- Full build: `lake build SP1Clean` (the default target). Passing = **0 errors AND 0 warnings**, and
  **no stray `info:` notes** — leave the build output clean (see the `ring` note below). This builds
  **only the main library** — it carries no `native_decide` (gated by `scripts/check_no_native_decide.sh`).
- Tests: `lake test` (the `SP1CleanTest` `testDriver`). Builds/elaborates the witness- and trace-conformance
  anchors — the project's **only** `native_decide` — checked against batteries dumped from SP1's real Rust
  prover. Runs on top of the cached main-library oleans (the test lib imports `SP1Clean`, never vice-versa).
- Single file: `lake env lean SP1Clean/Proofs/Chips/AddChip/Formal.lean` (elaborates against the
  **already-built** oleans). ⚠ `lake env` only sets the environment — **it does not build anything**.
  If you have edited a dependency, its olean is stale and this command silently checks against the
  *old* one. Run `lake build <Dep.Module>` first, or finish with `lake build SP1Clean`.
  ⚠️ `lake env lean <file>` **exits 0 even on a Lean stack overflow**, and a stale cached olean can make
  downstream checks pass falsely — **always finish a phase with `lake build SP1Clean`**.
- **Build concurrency.** Elaboration is heavy (full build is ~1800+ jobs across Clean + mathlib + Sail; the
  `toBitVec64`/carry proofs are the slowest). Before starting a new build, **let the running one
  finish or kill it** (`pkill -f "lake build"` / `pkill -f "lake env lean"`). Cap at **2–3 builds at once**.
  A `run_in_background` build can outlive its shell — check with `ps -ef | grep -E "lake|lean" | grep -v lsp`
  before spawning another. The lean LSP server (`uvx lean-lsp-mcp`) also keeps several GB warm.
  **There is no `-j` option** in Lake here (only `-J/--json`; re-verified at v4.32.2) — serialise by not
  running anything else.
- **Process hygiene.** *LSP file workers* (`lean --worker …`, children of `lean --server`) leak and hold GB
  after an agent exits; `pkill -f "lean --worker"` is the correct reaper. **Never kill `lean --server` /
  `lake serve`** — that is the `lean-lsp` MCP server, and killing it drops the MCP connection for the whole
  session. *Build workers* carry no `--worker` token, so use `ps -ef | grep tstack` for build liveness, and
  `sample <pid>` (not RSS — a healthy run also plateaus at ~3.2 GB) to tell a hang from progress.
- **Toolchain:** `lean-toolchain` and mathlib are `v4.32.2`, and **every dependency is an immutable git
  pin** — there are no path dependencies, so a clean clone builds. `Lean_RV64D` points at
  `succinctlabs/sail-riscv-lean`, a **generated** snapshot: pinned Sail sources run against the
  checked-in SP1 platform config, regenerable via `scripts/sail-config/generate_lean_rv64d.sh`
  (`docs/agents/sail-model-provenance.md`). **Do not run bare `lake update`** (it may advance
  dependencies/toolchains) — update one `[[require]]` at a time.
  ⚠ **The generated Sail model and the `lean-sail` runtime must move together.** A v4-generated
  `LeanRV64D` snapshot against `lean-sail` v5 fails with `unknown namespace Sail.ConcurrencyInterfaceV2`;
  pin both from the same pairing (`opencompl/riscv-lean` PR #59 is the reference).
  Read `docs/agents/lean-sail-notes.md` before touching any dependency.
- Lake options already set in `lakefile.toml`: `--tstack=400000`, `synthInstance.maxHeartbeats = 1000000`.
- There are no conventional unit tests in the main library; correctness lives in kernel-checked
  soundness/faithfulness/bridge theorems. `lake test` is the separate executable conformance layer.

## Architecture

Mirror-rust layout under `SP1Clean/`:

- **`Math/`** — general math, no SP1/Sail deps: `Word.lean` (`Word`, `toBitVec64`, `isU64`, `val_65536_*`,
  `limb_lift`), `Bitwise.lean` (`byteOp`, `reassemble_byteOp`, …), `Misc.lean`, `MulCarryChain.lean`,
  `HWord.lean`, `GetElemFastPath.lean` (the upstreaming candidate).
- **`Model/`** — the SP1 substrate (Sail + buses): `Register.lean`, `SailWrap.lean`, `SailMemory.lean`,
  `BusMessages.lean` (the State/Memory/Program message structs + their structural per-row predicates —
  incl. `MemoryMsg.ClkBound` and the reader-level `Readers.ClkDiscipline`, the memory-clock discipline),
  `Channels.lean` (plain Clean channels: State `True`, Program `RowSpec`, Memory `isU64 ∧ ClkBound`,
  Byte `ByteRowSpec`),
  `InteractionBus/Projection/Recovery.lean`, `ChipAir.lean`, `SP1Constraint.lean`, `ByteTable.lean`, and
  the **semantic-execution substrate** `Semantics/` — `GuestProgram.lean` (the `GuestProgram` +
  `IsInitialState`/`SailStep`/`SailChain`/`SP1Halted` Sail execution model), `ProgramCommitment.lean`
  (`progOf : ProverData → GuestProgram`, the committed program), `MicroTime.lean` (bus-clock ↔ step
  correspondence, `MemLoc`, `chainState`, `microValue`), and `Truth.lean` (`StateTruth`/`MemTruth`/
  `ProgTruth`, the global execution predicates derived by grounding, not channel payloads). (`Math` +
  `Model` are the former `Foundations/`, split by SP1-dependence.) `Model/Machine/{Schedule,Syscall,
  EventExecution}.lean` gives the row-dependent 8/264-tick event semantics and explicit SP1 host-handler
  boundary.
- **`Extracted/`** — the "extracted from Rust" pillar, **auto-generated, do not hand-edit**. The
  inventory: 25 whole-chip oracles (`ChipOracle/<Chip>.lean` — the chip-namespaced Rust row +
  complete `asserts`/`interactions`), 12 system tables (`SystemOracle/<Table>.lean`), the shared
  flat modules (canonical readers, the `MemoryAccess` struct carrier, shared operations that
  multiple chips' bridge lemmas cite), and the fail-closed Core manifest/provenance. No legacy
  `<Chip>Chip.lean` files remain. Extraction never emits a Clean circuit. All generated files are
  regenerated by `update_extracted.py` (kept at the repo root deliberately — it is the pipeline's
  single entry point and the path every generated header and doc cites).
- **`FormalModel/`** — the central audit surface (the "middle ground" between `Extracted` and the proofs):
  `Contracts/` holds the per-reader/operation/chip `Inputs` + semantic `Spec`s (`Readers.lean`,
  `Operations.lean`, `Chips.lean`, plus focused rich contracts such as `DivRem.lean`) and the lifted chip `Assumptions`/`ProverAssumptions`
  (`ChipAssumptions.lean` — Add/Addi/Addw/Sub/Subw/UType; the two-reason keep-list taxonomy for the
  other chips is stated in that file's module docstring). `ProverSpec` is uniformly
  `fun _ _ _ => True` (inline in each `circuit` bundle). `Trace/Witness.lean` holds the witness-table
  scaffolding; the guest-program execution model (`GuestProgram`, `IsInitialState`, `SailStep`/`SailChain`,
  `SP1Halted`, `exitOf`) lives in `Model/Semantics/GuestProgram.lean`. Relation-level AIR/verifier
  contracts live in `Relations.lean`, `CoreProfile.lean`, `CoreAIRRelation.lean`, `Execution.lean`, and
  `Verifier.lean`; `ChipRow`-dependent decode,
  routing, and grounding arguments remain naturally in `Soundness/`.
- **`Native/`** — the "implemented native in Lean" pillar (circuit construction): `Native/Chips/<Op>Chip/Defs.lean`
  (each chip's `main` + `ElaboratedCircuit`), `Native/Operations/<Op>/{Populate,RawSpec}.lean` (witness +
  native arithmetic core) + flat ops (`BitwiseU16Operation.lean`, `AddressOperation.lean`, …), and
  `Native/Readers/*.lean` (the register/state reader circuits — their `Spec`s are in
  `FormalModel/Contracts/Readers.lean`; the readers' local `SpecD`/`AssumptionsD`/`ProverAssumptionsD`
  are the **`D`-suffix convention**: the `ProverData`-threading lifts of the plain contract
  predicates, e.g. `SpecD input _ data := Spec input`, wrapping a Contracts-layer predicate into the
  `GeneralFormalCircuit` signature). Operation circuit definitions are hand-maintained in
  `Native/Operations/<Op>/Defs.lean` when they are not flat single-file operations.
- **`Proofs/`** — the "proven sound/complete" pillar: `Proofs/Chips/<Op>Chip/{Formal,Bridge,…}.lean`
  (soundness/completeness/`circuit` + the Sail bridge; the `Spec` is in `FormalModel/Contracts/Chips.lean`,
  the ALU chips' `Assumptions`/`ProverAssumptions` in `Contracts/ChipAssumptions.lean`),
  `Proofs/Operations/<Op>/Formal.lean` (the `FormalAssertion` soundness/completeness). Flat receiver
  infra (`ByteChip`/`ProgramChip`/`MemoryProvider`) sits in
  `Proofs/Chips/`. Complex chips may decompose proofs without changing their public chip boundary.
  DivRem is the reference: `FormalModel/Contracts/DivRem.lean` defines four semantic families,
  `Proofs/Chips/DivRemChip/Cases.lean` proves circuit-independent evidence-to-ISA lemmas, and the sole
  heavy arithmetic seam is the whole-chip `evidenceSoundness` theorem in `Formal.lean`.
- **`Faithful/`** — the "proven faithful" pillar: `ChipOracle.lean` plus the 25 whole-chip
  native↔Rust anchors (reconfigure-based oracles; the whole-trace conformance anchors audit the
  reconfigure maps cell-for-cell). The per-operation/reader anchor files that remain are shared
  substrate: their lemmas are the canonical statements the chip anchors cite via namespace
  bridges (each has ≥2 live importers — verified in the 2026-07 retirement sweep).
- **`SP1CleanTest/`** (top-level, **not** under `SP1Clean/`) — the **test library**, the sole home of
  `native_decide` and the `lake test` target (`testDriver`). It imports the main `SP1Clean` library and
  is never imported by it, so the default `lake build SP1Clean` stays `native_decide`-free (enforced by
  `scripts/check_no_native_decide.sh`; `native_decide` trusts the whole compiler — at v4.32.2 the census
  shows this as generated `._native.native_decide.ax_*` constants, the successors of the named
  `Lean.ofReduceBool`/`Lean.trustCompiler` axioms). Two layers, namespaces preserved (`SP1Clean.WitnessTests` /
  `SP1Clean.TraceGenTests`, decoupled from the new module paths):
  - `WitnessTests/` — the `<Op>Witness.lean` witness-generation conformance anchors +
    `WitnessConformance.lean` scaffold; auto-gen vectors under `WitnessTests/Vectors/`.
  - `TraceGenTests/` — the **circuit-as-trace-generator** full-trace layer (`TraceGenerator.lean` +
    `EventPopulate.lean` + `Conformance.lean` + `<Chip>ChipTrace{Vectors,Witness}.lean`): whole chip
    traces derived from the chips' own `main` witness closures + output struct, `native_decide`-checked
    against SP1's real `generate_trace`. 10 chips, **all unmasked**: Add/Sub/Subw/Addw fixed-witness;
    Mul/DivRem/Bitwise/Lt/ShiftLeft/ShiftRight hint-driven flags (per-event `ProverHint` from the dumped
    executor opcode).
  Both vector batteries are regenerated by `update_extracted.py` (the `WITNESS_DIR`/`TRACEGEN_DIR` writers).
- **`Soundness/`** — the whole-machine layer: per-bus `{State,Byte,Program,Memory}Consistency.lean`;
  `ChipRow.lean` (the `ChipKind` structure-of-functions — each chip registers one `kind`, carrying a
  `name` = its SP1 `MachineAir::name`) + `ChipRegistry.lean` (`allChipKinds`); the gated execution capstone
  `GatedVm/` (the legacy-but-proved Eulerian-trail machinery) + `SP1Ensemble.lean` (`sp1Ensemble` — a
  plain Clean `Ensemble`, 25 chips + 11 boundary/provider tables); the timed/ranked grounding engine;
  `WitnessDecode.lean` (the deterministic typed row decoder), `LocalExecution.lean` (grounded ordered
  rows → a genuine shard-local Sail chain), and `AIR.lean` (the honest native witness relation plus
  proved `supported_core_witness_grounding` and `supported_core_native_sound`); the
  grounding-adapter/contract stack that proves `supportedCore_orderedRows_dynamic` from per-chip
  obligations — `GroundingAdapter.lean` (the `advance`→timed-engine-record adapter: `RowWiring`,
  `stepFact_of_advance`/`frameFact_of_advance`, `rowWiring_rtype`), `ChipContracts.lean`
  (the `ChipGroundingContracts` bundle + registry-wide proved instances),
  `AlignedCarrier.lean` (+ `AlignsWith` in `TimedGrounding.lean`, the ordinary↔aligned `RowFacts`
  carrier transports), and `TimeExtraction.lean` (the `pull_lt_push` payoff from the memory-channel
  `ClkBound`); and the typed interaction/Memory bridge (`TypedInteractions.lean`, `TypedMemory.lean`;
  exact evaluated chip pulls → timed facts/live operands); and the
  auditable instruction-coverage layer — `Coverage.lean` (+ the opcode enum itself at
  `Model/Opcode.lean`, namespace `SP1Clean.Soundness` per the decoupling rule) (the `Opcode → chip → Sail`
  routing table mirroring SP1's `tracing.rs`/`RiscvAir`). The former `InstructionTrace.lean` name-only
  row-routing shadow and `Completeness.lean` routing scaffold were retired in favor of witness decoding,
  timed grounding, and the relation-level completeness boundary in `AIR.lean`. The bespoke
  `MachineSoundness`/`MachineConsistency` `TraceValid` capstone was retired 2026-06-05.
  `Soundness/CoreAIR.lean` is the exact v6.3.1 deterministic boundary: its `_of_obligations`
  combinators consume the `.execution` cluster only and expose the unclosed field-by-field proof bundle.
  `TargetVm.lean` retains the proved conditional trail-to-Sail walk; it is an intermediate lemma, not
  the headline zkVM theorem. Audit harness: `scripts/run_audit.sh`
  (pins + sorry gates + the `#print axioms` census via `scripts/gen_axiom_probe.py`).
- `Soundness/RowView.lean` (the reader-agnostic `RowView`/`AdapterView` row-view infra the bus layer reads —
  formerly the top-level `Trace.lean`). The design rationale for the whole-chip semantic boundary is in
  `docs/architecture.md`. The root index is `SP1Clean.lean` — **wire every new module's import there**.

**Namespaces are decoupled from directory paths** — a file's `namespace` (e.g. `SP1Clean.AddChip`,
`SP1Clean.Word`) does **not** track its directory, so files can be moved between pillars without changing
any fully-qualified name (only `import` lines and tooling path-globs follow the move). Keep it that way.

**Lake libraries** (`lakefile.toml`): the umbrella `SP1Clean` (the default target — its root index imports
the whole **main** library, so `lake build` builds all of it) plus per-pillar build-targets `SP1Math` /
`SP1Model` / `SP1Extracted` / `SP1FormalModel` / `SP1Native` / `SP1Proofs` (selected by submodule globs, e.g.
`"SP1Clean.Math.+"`; `SP1Proofs` groups `Proofs` + `Faithful` + `Soundness`). `lake build SP1Extracted`
builds just that layer. Separately, the top-level **test** library `SP1CleanTest` (glob `"SP1CleanTest.+"`,
the `testDriver` → `lake test`) holds the witness/trace conformance anchors; it imports `SP1Clean` but is
**not** part of the umbrella, so `lake build SP1Clean` never compiles it (keeping the main build
`native_decide`-free). Isolation is **by convention** — Lake does not forbid cross-layer
imports within one package; the auto-gen guard is the `Extracted/` + `SP1CleanTest/**/Vectors`/`*TraceVectors`
"do not hand-edit" headers + the sole writer `update_extracted.py`.

**Restructure status (updated 2026-07-27; whole-chip oracle migration completed the same day).**
Landed in the 2026-07 release-readiness campaign: the full 25-chip `Extracted/ChipOracle/`
migration (native rows everywhere, zero legacy chip files, the `MemoryAccess` struct carrier, the
reader-family oracle config), the release-readiness audit (zero BLOCKERs across the 25-chip spec
review, substrate, relation level, Rust-faithfulness spot checks, and Clean-idiom sweep — the
full findings log lived at `docs/audits/2026-07-release-readiness.md` through commit `14c926bd`
and is retrievable from git history; its durable disclosures are inline in the verification
report and `docs/agents/extraction.md`), the docs pruning, and the external verification report
(`docs/verification-report.md`). Previously landed: the `Math`/`Model` split, list-only `Extracted/`
consolidation (including system tables, manifest, and provenance), the `FormalModel/Contracts/` audit surface (all `Spec`s +
the ALU chips' `Assumptions`/`ProverAssumptions`), the `Native/`+`Proofs/` five-pillar re-bucket of
`Chips`/`Operations`/`Readers`/`WitnessTests`, and all six per-pillar layer libraries. Every registered
chip soundness/completeness theorem, DivRem evidence theorem, structural circuit law, grounding
contract, and whole-chip faithfulness proof is closed. `scripts/run_audit.sh` gates zero proof
deferrals. The exact v6.3.1 Core relation and conditional `_of_obligations` combinators are landed;
their explicit refinement bundle is not yet instantiated. The obsolete nine DivRem per-op soundness files and
their shared tail were retired in favor of the four-family evidence contract. A large proof-cleanup
campaign (2026-06-22 / 06-23) golfed ~109
hand-written files (−591 lines) while preserving axiom-cleanliness, plus substrate-hoist refactors
(`Word.isU64_four`, Faithful `val_16`/`bool_iff` dedup → `ChipTactics`). Upstream `main` was merged in
2026-06-23 (#100 hard-gates `skipKernelTC` and removes overrides; #101 fleshes out the immediate-type Sail
bridges; #102 makes the jalr/jal/branch specs explicit about divisibility / LSB-clearing). The 2026-08
release-audit pass closed the recorded `Assumptions`-lift plan at its true extent: UType joined the five
ALU chips on `Contracts/ChipAssumptions.lean`, and the rest are a **stated keep-list**, not pending work —
the hint/helper-dependent chips (Mul/Bitwise/Lt/Branch/Jal/Jalr/DivRem/ShiftLeft/ShiftRight) reference
`Defs`-layer witness plumbing, and the memory/x0 chips' whole contract blocks (`Inputs` + `Spec`) are
Native-resident pending the "Spec homing" backlog item (see the ChipAssumptions module docstring and
`docs/architecture.md` § deliberate layering exceptions). The same pass renamed the ten suffix-less
`Faithful/` anchors to `<X>Chip.lean`, named the micro-time window constants with their Rust provenance,
and completed the root index (now gated by `scripts/check_root_index.sh`). The trace *arguments*
(TargetObligations / target theorem / routing / Emits) are `ChipRow`-dependent
and so remain in `Soundness/` — their natural layer — rather than being forced below it.
The bespoke `Soundness/GatedVm/` → Clean `VmTables` migration (roadmap W11) was investigated and **deferred**
— Clean's VM engine yields verifier-guarantees with no explicit execution walk, while SP1's spec is a
balance-derived `GatedExecution` with an Eulerian trail, so re-basing adds obligations without removing the
SP1-specific trail machinery (see roadmap W11).

**Structural-bus grounding program (closed for the native slice, 2026-07).** Channels communicate the field tuples and
multiplicities that SP1 actually constrains; they do not assert reachability. `VmChannel` and the earlier
semantic-channel spike were retired. State has local guarantee `True`, Program carries `RowSpec`, Memory
carries `isU64 ∧ ClkBound` (value + a bounded 24-bit access timestamp), and Byte carries `ByteRowSpec`.
`StateTruth`/`ProgTruth` are conclusions of the timed
grounding engine from bus balance, boundary/provider facts, program commitment, strict schedule rank, and
the 25 chip `advance` lemmas. No chip `ProverAssumptions` threads either global truth. The current capstone
layers distinguish native supported-machine refinement, extracted AIR faithfulness, full SP1 AIR
soundness, and the eventual ArkLib verifier theorem; see `docs/roadmap.md` W12.
The memory-bus closed forms, `GroundingAdapter`, all 25 `ChipGroundingContracts`, aligned-carrier
transports, RAM/same-location grounding, and per-position assumptions/readiness are proved. Remaining
work is to derive this native relation's semantic boundary and timestamp premises from the exact
upstream system tables.

Everything is **field-generic** over a prime field — the standard variable block is:
```lean
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
```

## Clean-native principles (non-negotiable)

**Read Clean's own docs — they are the upstream authority for this whole project.** Our proof-style notes
below are SP1-specific *instances* of principles Clean already documents generally; when a technique here
feels ad-hoc, the general rule is in Clean's docs.

*Where to find them.* Browse upstream at **<https://github.com/Verified-zkEVM/clean>** (the `doc/` folder +
`Clean/Air/README.md` + the repo-root `AGENTS.md`), or read the copy Lake installs in-tree under
**`.lake/packages/Clean/`** (e.g. `.lake/packages/Clean/doc/performance-problems.md`). Prefer these over any
local checkout: Clean is a pinned **git** dependency (`0e53b9f2`, v4.32.2), and a local sibling path must
never be baked into permanent docs or into `lakefile.toml`. (The pin can still lag upstream `main`; if a doc
named below is missing from `.lake/packages/Clean`, read it on GitHub.)

Read, in priority order (paths relative to the Clean repo root — i.e. `.lake/packages/Clean/<path>` in-tree,
or `<path>` on GitHub):
- `doc/performance-problems.md` — the `whnf`-into-expensive-values doctrine (make dangerous values opaque;
  cross spellings by syntactic rewriting, not unification), the 9 fix patterns, the kernel-size-cliff
  completeness recipe (`circuit_proof_start_core`), and the **"keep hypothesis types folded"** section (our
  "pass the `Spec` folded" fix). Read this **before any nontrivial proof work**, and first when you hit a
  `whnf`/heartbeat/`(kernel) deep recursion` blowup.
- `doc/proving-guide.md` — opening/middle/closing tactic moves; the "what (not) to unfold" list.
- `AGENTS.md` (Clean's own) — subcircuit-boundary discipline (bundle a proof boundary, inline a non-boundary,
  never leave an unbundled `Circuit` parent proofs treat abstractly), helper-lemma discipline (helpers are
  for real math, not for unpacking `ConstraintsHold`), spec-states-meaning discipline, and the
  `ElaboratedCircuit` explicit-`elaborated`-field performance rule.
- `Clean/Air/README.md` — the flat-AIR channel/ensemble/`Balance.lean` model our grounding engine builds on
  (incl. the "guarantees-to-requirements-reversal" theorem — the general form of our currency circularities).
- Secondary: `doc/witgen-authoring.md` (the exportable witness IR), `doc/conventions.md` (local style that
  differs from Mathlib).

These are the keepers from sp1-lean's "faithful sub-circuit composition" discipline; violations are bugs.

1. **Compose true Clean subcircuits, not inline constraints.** A chip's `main` invokes each
   sub-operation through its bundled `circuit` — `let _ ← <SubOp>.circuit ⟨…⟩` (the
   `GeneralFormalCircuit` `CoeFun` application) or `assertion <SubOp>.circuit ⟨…⟩` — both of which
   compose it as a genuine subcircuit boundary (Clean's `subcircuit` combinator is the underlying
   mechanism). A gadget that uses another gadget composes it the same way. Never inline a
   sub-operation's constraints.
2. **One `main`, one `Spec` per file.** Each `Native/Operations/<Op>` and `Native/Chips/<Op>Chip/Defs.lean`
   exposes exactly one `main`, with one `Spec` (in `FormalModel/Contracts/`) plus the `circuit` glue (in
   `Proofs/`), and references sub-operation Specs *by direct field
   application*, never by re-wrapping low-level constraints.
3. **Specs are semantic, not structural.** The `Spec` states what the row *means* (a `toBitVec64` equation,
   `is_real`-gated), not a restatement of the constraint list. No `InlinedSpec` / `inlinedSpec_iff_spec`
   bridging helpers — they only exist when `main` and `Spec` were defined in mismatched forms; the fix is to
   align them.
4. **Axiom-clean target.** After each artifact, check `#print axioms <decl>` (or the `lean_verify` MCP tool) is
   only `[propext, Classical.choice, Quot.sound]` (bv_decide may add generated
   `._native.bv_decide.ax_*` constants — the v4.32.2 form of the former
   `Lean.ofReduceBool`/`trustCompiler`) — and
   **no `sorryAx`**.

## Proof-style quick notes

- `circuit_proof_start` (from `Clean.Utils.Tactics`) is the **first** tactic in soundness/completeness proofs;
  any `haveI`/`set_option` must come after it, or it errors "can only be used on Soundness/Completeness".
- Imports MUST precede the module doc-comment (a `-D linter.*` flag can't be validated against a header that
  opens with a doc-comment before its imports — the linter's registration module isn't in scope yet; same
  "Step 0" reason the package `[leanOptions]` carries no Mathlib linter flags, see `lakefile.toml`).
- **Linters — two kinds.** *Syntactic* linters run during `lake build` (option-gated); *environment*
  linters run as a separate `lake lint` pass over the built environment.
  - **Syntactic.** Every hand-written **core** pillar lake library enables the same eight `-D linter.*` flags
    (via its `moreLeanArgs`): `SP1Math`, `SP1Model`, `SP1FormalModel`, `SP1Native`, and `SP1Proofs`
    (`Proofs/`+`Faithful/`+`Soundness/`). The flags: `style.lambdaSyntax`/`style.dollarSyntax`, the four
    deprecated-tactic guards `style.refine`/`style.cases`/`style.induction`/`style.admit`, and
    `oldObtain`/`style.cdot` — all at **zero** violations. They apply during the normal `lake build SP1Clean`.
    `linter.style.longLine` is the remaining candidate (real fallout, concentrated in Native/FormalModel; see
    `docs/roadmap.md` § "Cleanup / polish backlog"). The flags are scoped **per-lib** rather than at package level so the
    auto-gen `SP1Extracted` library stays out of the set (it carries per-file `set_option linter.all false`);
    keep the five identical `moreLeanArgs` copies in `lakefile.toml` in sync. (Every hand-written pillar
    transitively imports Mathlib — Native via Clean — so the `-D linter.*` options register fine; the older
    "Clean-only Math/Model lack the registration" note was stale. Still true: a file's imports must precede
    its module doc-comment, or the `-D` flag can't be validated — see the Step 0 bullet above.)
  - **Environment (`lake lint`).** Run `lake lint` (after a build — it imports the oleans) for the Batteries
    `#lint` checks. The driver is `scripts/sp1Lint.lean` (package `lintDriver = "sp1Lint"`), a thin wrapper over
    `getChecks`/`lintCore`. We use a **custom driver, not the stock `runLinter` exe**, because `runLinter`
    scopes by namespace *root* (`getDeclsInPackage module.getRoot`) — it would lint all `SP1Clean.*` incl.
    `SP1Clean.Extracted.*`, and the per-file `set_option linter.all false` headers do **nothing** against
    environment linters (those run post-import; only `nolints.json`/`@[nolint]` suppress them). `sp1Lint`
    instead filters decls by full module path (drops `Extracted/`+`*Vectors`) and runs a **curated** set of 13
    low-noise linters (incl. the Mathlib `structureInType`/`deprecatedNoSince` hygiene checks, both at zero
    violations). Residue lives in `scripts/nolints.json` (20 stable entries — 2 `defLemma`
    obligation-bundle defs + 4 `simpComm` + 14 `simpNF` Math/Model/Sail simp lemmas); `lake exe sp1Lint --update`
    regenerates it; CI runs `lake lint` in the build job. Deliberately **dropped**: `docBlame`/`tacticDocs`
    (doc-coverage noise) and `unusedArguments` (flags only the uniform field-generic / `ProverData` signature
    args — all structural, and a fresh false-positive per new chip).
  - The next-candidate linter (`longLine`) is tracked in `docs/roadmap.md` § "Cleanup / polish backlog"; the
    non-negotiable suppressions — `unusedSectionVars`/`unusedSimpArgs` (structurally necessary in circuit
    proofs) and the auto-gen `linter.all false` — must stay.
- **This repo does not raise elaboration budgets.** Hand-written Lean carries **zero**
  `set_option maxHeartbeats`, matching upstream Clean (none in 44,603 lines), and two measured structural
  `maxRecDepth` sites; every other site is on a generated definition.
  `scripts/check_option_escapes.sh` (the CI `guards` job + `run_audit.sh`) **prohibits** both options: any
  site not named in `scripts/option_escapes_allowlist.txt` fails the build. It is not a ratchet and not a
  budget — a ratchet permits a new hatch as long as an old one leaves; this does not. When a proof blows
  up (heavy `toBitVec64`/carry rw chains are the usual suspects), **fold it** — `docs/agents/perf-findings.md`
  §1 "The rule". The allowlist is a last resort with a four-part bar (§7), not an allowance.
- **Never write the phrases `set_option maxHeartbeats` or `set_option maxRecDepth` into a Lean comment or
  docstring under `SP1Clean/` / `SP1CleanTest/`.** The guard greps for the **full `set_option …` phrase** and
  does not parse Lean, so a comment quoting a whole directive scores as a live site and fails the build.
  (The bare option name in prose is harmless — "the depth bump", or even "maxRecDepth" alone, is fine.)
  Record a measured ladder without the directive: "the former 8M ceiling was ~200× over".
- **Dropping `by exact` on a `def`'s Prop-valued field can be load-bearing *opacity*.** A tactic block becomes
  an opaque auxiliary proof constant; the bare term inlines and `isDefEqDelta` unfolds it into every consumer.
  One such −1-line golf took a downstream module from **260s to >1230s**. A/B-time the *downstream* consumers,
  not the edited file (`docs/agents/proof-patterns.md`).
- **Never `set_option (debug.)skipKernelTC`.** It bypasses the kernel's type-check re-run — the trust anchor
  for an axiom-clean proof — so it is **CI-gated** (`scripts/check_no_skipkerneltc.sh`, run by the audit and a
  standalone CI `guards` job; any hit in `SP1Clean/**/*.lean` fails the build). If a goal blocks on a kernel
  deep-recursion / `2^64`-unfold error, the fix is to factor the expensive compute into an **abstract-`BitVec`
  helper** proved once over variables (the `srl_toNat`/`sra_toNat` pattern), then apply it symbolically — never
  silence the kernel. See `docs/agents/proof-patterns.md` §"Bit-shift chip soundness" (the `2^64` bullet) for
  the worked fix.
- **Never `native_decide` in the main `SP1Clean/` library.** It discharges goals by running compiled code,
  trusting the **whole compiler** (surfaced in the census as generated
  `._native.native_decide.ax_*` constants — formerly the named `Lean.ofReduceBool`/
  `Lean.trustCompiler` axioms) — so headline soundness
  theorems would no longer be `[propext, Classical.choice, Quot.sound]`-clean. It is **CI-gated**
  (`scripts/check_no_native_decide.sh`, run by the audit + the `guards` job; any hit in `SP1Clean/**/*.lean`
  fails the build). Conformance checks that genuinely need it live in the separate top-level `SP1CleanTest`
  library (`lake test`); to disclose a new one, put the anchor there, not in `SP1Clean/`.
- `mul_eq_zero` won't fire on `ZMod p` (a `Nat.rec` Mul-instance quirk) — derive booleanness via
  `inv_mul_cancel₀` / a `bool_of_mul_pred`-style lemma instead.
- `Word` is an `abbrev` for `Vector` — `w.toBitVec64` dot-notation fails; write `Word.toBitVec64 w`.
- **The Sail `-i` token — space your negations.** Sail declares GLOBAL `infixl:65 " +i "/" -i "/" *i "/" ^i "`
  (`Sail/Sail.lean`, integer ops, used 1300+× in the generated LeanRV64D model so they can't be scoped). Now
  that `Model/Channels.lean` imports Sail-carrying `Truth` (the semantic-channels flip), all four tokens are
  active in **every** circuit-proof file, and the lexer greedily tokenizes `<op>i` inside `-input_is_real` /
  `i₀+i` as the operator → `unexpected token '-i'; expected term`. So keep a space (or parens) whenever an
  operator is immediately followed by an `i`: **`- input_is_real`** / `-(input_is_real)` (never `-input_is_real`),
  **`i₀ + i`** (never `i₀+i`), `2 ^ i`, `x * input`. (The space *before* the operator is untouched and still
  distinguishes binary-op from unary/application, so this is semantically null. The spaced Sail operator
  ` +i ` — the `i` followed by a space — is the one form you must NOT break.)
- Prefer targeted `simp [...] at h` over `simp_all` (it leaks into unrelated hypotheses).
- **Don't leave `ring`'s `info:` note in the build.** On some goals `ring` runs its `ring1` pass, which
  *fails* and emits `Try this: ring_nf` / "ring works primarily in commutative rings …", then closes via
  the `ring_nf` fallback — so the proof passes but leaks an `info:` note that clutters the build output.
  Close those goals with the tactic that actually works, no note: `simp` for the `is_real` binary gate
  (`is_real * (is_real - 1) === 0`) and `interval_cases`-carry goals, `ring_nf` where it closes, or the
  explicit lemma (`sub_eq_add_neg`, `zero_mul`/`mul_zero`). A clean build has zero `info:` notes too.
- **`ElaboratedCircuit` field obligations should almost never have a hand-written proof — make the default
  tactics close them.** `localLength_eq`/`output_eq`/`subcircuitsConsistent`/`channelsLawful` each have a
  Clean default tactic (`simp only [circuit_norm, seval]`); the goal is always to let it succeed by adding
  the right `circuit_norm` lemmas, then **omit** the field — not to override it. Recipe: every circuit
  exposes its `channelsWithGuarantees`/`channelsWithRequirements`/`localLength` as `@[circuit_norm]`
  `rfl`-lemmas (`channelsWith*_eq`/`localLength_eq`, each behind `set_option linter.unusedSectionVars
  false in`) right after its `elaborated` instance; the generic list/prop closers are tagged `circuit_norm`
  once in `Model/Channels.lean`. A missing default-tactic close means a missing `circuit_norm` lemma,
  not a reason to hand-write the field. These lemmas also tidy `circuit_proof_start`; mind the soundness
  requirement-tail caveat. Full recipe: `docs/agents/proof-patterns.md` "ElaboratedCircuit field obligations".
- **When a proof is slow, extract over *opaque* arguments — and check what the extraction can still see.**
  This is the single highest-yield move (`docs/agents/perf-findings.md` §1 "The rule"). The cost hides in
  places the goal text does not show: in the local *context* rather than the goal, in a `have`'s *type*
  rather than its proof, in the *order* of two tactic steps, in a struct *literal* where `fromElements`
  belonged, in rewrites that each renormalise a large context. The fix is to interpose an opaque variable,
  never to make the expensive step cheaper. Corollary: extracting a block into a `have` **inside the same
  proof** buys nothing, because it keeps the whole context — so "extraction moved nothing" is not evidence
  of irreducibility unless the extraction actually took the context away.
- **Ladder before you believe a cause you found by reading code.** A structural hypothesis promoted on a
  code-read predicts nothing until a measured ladder confirms it: a mechanism can be genuine, verifiable,
  and irrelevant — including one that is upstream Clean's own documented performance rule (measured delta:
  0.008%). Measure first. Details: `docs/agents/perf-findings.md` §1 "The rule".
- Full landmine list + the witnessed-`FormalCircuit` recipe: `docs/agents/proof-patterns.md`.

## MCP servers

`.mcp.json` declares `lean-lsp` (live goal/diagnostic state from the Lean LSP); it is deliberately
committed so any checkout gets the server without setup. It launches via `uvx`, so `uv`
must be on `PATH` — install with `curl -LsSf https://astral.sh/uv/install.sh | sh` if missing. Local
enable/permissions are in `.claude/settings.local.json` (`enableAllProjectMcpServers: true`). Restart the agent
after installing or toggling.

## docs/

- **Clean's own docs (the upstream authority; read first)** — upstream at
  <https://github.com/Verified-zkEVM/clean>, or in-tree under `.lake/packages/Clean/`: `doc/performance-problems.md`
  + `doc/proving-guide.md` (proofs/perf), `AGENTS.md` (subcircuit/spec/`ElaboratedCircuit` discipline),
  `Clean/Air/README.md` (channels/ensembles/balance). See the "Read Clean's own docs" callout under
  "Clean-native principles" (incl. the path-dependency-is-temporary note).
- `docs/README.md` — index + "what to read first" + the one-role-per-doc split.
- `docs/overview.md` — the ten-minute reader-facing orientation: current theorem, coverage table,
  trust base, limitations.
- `docs/verification-report.md` — the self-contained external technical report (the only doc
  allowed to be long); its citations are machine-checked by `scripts/check_report_citations.sh`.
- `docs/architecture.md` — the chip-centered native/Sail/Rust-oracle/trace chain and theorem layering,
  including the deliberate layering exceptions.
- `docs/roadmap.md` — the dependency order from exact system-table grounding through ArkLib and
  completeness.
- `docs/goal-overview.md` — the completed-state contract (verifier + completeness targets). Not
  current status; never cite it as such.
- `docs/chip-standardization.md` — the completed 25/25 `ChipKind.advance` interface record.
- `docs/bus-model.md` — HISTORICAL (pre-consolidation bus model); kept only because source
  doc-comments cite its section numbers. Read its banner before citing.
- `docs/proposals/consolidation-progress.md` — the consolidation checkpoint board.
- `docs/release-audit.md` — the honest-claim / trust-boundary report (axiom census and zero-deferral gate;
  regenerate with `scripts/run_audit.sh`). The census is **split by library**: the main scope diffs
  `docs/snapshots/axiom-census.txt` (needs the `SP1Clean` oleans; CI `audit` job runs
  `--main-only`), the test scope diffs `docs/snapshots/axiom-census-test.txt` (needs `lake test`
  first; CI `test` job runs `--test-only`); the no-flag default runs both. The harness leaves the
  tree **clean on a pass**: it diffs each fresh census against its committed snapshot and fails on
  drift; only an explicit `scripts/run_audit.sh --update` rewrites the snapshot(s) for the scope(s)
  run (inspect and commit the delta — a moved auto-generated `bv_decide` `ax_N_M✝` index is
  hygienic). It also runs `check_pins.sh`, `check_root_index.sh`, and `check_report_citations.sh`
  as gates, so none need a separate invocation.
- `docs/agents/lean-sail-notes.md` — the v4.32.2 environment, the git dependency pins, the Sail
  code-generation workaround, and the `lake update` trap.
- `docs/agents/sail-model-provenance.md` — the generated `Lean_RV64D` snapshot's provenance: the
  four-key SP1 config and its six generated sites, why stock upstream makes the memory-bridge
  lemmas false, the regeneration pipeline, and the re-pinning procedure.
- `docs/agents/proof-patterns.md` — the witnessed-`FormalCircuit` soundness/completeness recipe + concrete
  landmines + the **Golf & cleanup discipline** section (how to golf/clean proofs safely).
- `docs/agents/cleanup-profile.md` — **binding house rules for `/cleanup` and `/cleanup-all`.** The
  `mathlib-quality` plugin is written for mathlib and several of its hard gates would break this build or
  corrupt the audit surface (it unsqueezes `simp only`, splits `∧` statements,
  privatises single-file decls, rewrites `≥`→`≤`, and deletes "wrapper" lemmas). Read this file first; it
  overrides the plugin where they conflict.
- `docs/agents/perf-findings.md` — **how to avoid an elaboration budget.** §1 is the rule (extract over
  opaque arguments; check what the extraction can still see), then the folded-vs-unfolded predictor, the
  cause classes with worked fixes, the diagnostic instrument, the measurement traps, and §7's bar for the
  rare site that may be allowlisted. Read it before diagnosing any slow or blowing-up declaration.
- `docs/agents/cleanup-deferred.md` — the owner-decision queue: every duplication found
  and deliberately not fixed, grouped by blocker (shallow-file hoist · statement change · deletion ·
  `Faithful/**` conservative-only · cross-module round), with measured sizes; the "deliberately NOT taken"
  decisions; and the 40-entry rename queue, which is **queued, never applied**.
- `docs/agents/porting-recipe.md` — step-by-step checklist to port a new chip from the Add/Bitwise template.
- `docs/agents/extraction.md` — the constraint-extraction pipeline (compiler → Python → Lean DSL).
- `docs/agents/mul-operation-learnings.md` — Mul-specific soundness/completeness pitfalls.
- `docs/snapshots/compile-profile.md` — per-module wall-clock compile profile + worst offenders + common threads
  (point-in-time snapshot); re-run with `scripts/profile_compile.sh`.
- `docs/snapshots/axiom-ledger.md` — machine-checked `#print axioms` inventory per theorem (point-in-time
  snapshot; re-generate before release).
