# AGENTS.md

Guidance for AI agents working in this repository (`sp1-clean-native`).
`CLAUDE.md` is a one-line pointer to this file so Claude Code auto-loads it.

## What this repo is

A **Clean-native, semantically-specified** formal verification of SP1's RISC-V chips, built fresh in
Lean 4.28 on the **public** Clean DSL. For each operation we build a chain of four artifacts:

1. a **witnessed `FormalCircuit` gadget** (`Native/Operations/<Op>/{Populate,RawSpec}.lean` — or a flat
   `Native/Operations/<Op>.lean` — plus `Proofs/Operations/<Op>/Formal.lean`) with a *semantic* spec
   (e.g. `Word.toBitVec64 value = Word.toBitVec64 a + Word.toBitVec64 b`), whose arithmetic is
   **re-derived natively** in-project;
2. a **`GeneralFormalCircuit` chip** (`Native/Chips/<Op>Chip/Defs.lean` = `main` + `ElaboratedCircuit`,
   `Proofs/Chips/<Op>Chip/Formal.lean` = soundness/completeness/`circuit`; the `Spec`/`Assumptions` live on
   the audit surface `FormalModel/Contracts/`) that composes the gadget as a true Clean `subcircuit` plus an
   `is_real` selector gate, exposing one semantic, gated `Spec`;
3. a **native Sail bridge** (`Proofs/Chips/<Op>Chip/Bridge.lean`) proving the chip's `Spec` reaches the RISC-V Sail
   spec (`correct_<op>_native`);
4. a **faithfulness anchor** (`Faithful/<Op>.lean`) proving SP1's operation constraint list is exactly the
   gadget's `RawSpec`. The *asserts* half is structural; the *interactions* half is mid-conversion from the
   semantic `Interaction.toProp` interpreter to a **syntactic** `LookupAccess`-list comparison (the circuit's
   *emitted* interactions = SP1's extracted oracle, all four buses, no semantics) — see the "Interaction half"
   note in `docs/architecture.md` §"four-artifact chain". Done for all leaf/composed/witnessed ops,
   CPUState/RTypeReader/ALUTypeReader, and **all four buses + combined** of AddChip/SubChip/AddwChip/SubwChip;
   the rest (Lt/Bitwise/Shift/AluX0/Mul/I-J/load-store chips, remaining readers) is a tracked longer-term goal.

This project is **independent** of `sp1-lean`. It does **not** import `SP1Foundations`/`SP1Operations`/
`SP1Chips`/`SP1Clean` (those are 4.29 oleans — cross-toolchain), does **not** use `update_constraints.py` or
the constraint compiler, and does **not** use the legacy structural `correct_*` / `SailBridge` /
`fromMain`/`toMain` pattern. Needed foundations are re-created here (`Math/` + `Model/`). The goal: every headline
theorem is **axiom-clean** — `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

The SP1 Rust source (the extraction/spec oracle, read-only reference) lives in a sibling `sp1` checkout
(`$SP1_DIR`, by default `../sp1`). The 4.29 `sp1-lean` repo is a read-only reference for porting (a sibling
`sp1-lean` checkout); its arithmetic/Sail proofs are the thing we re-derive natively here, not import.

## Build

- Full build: `lake build SP1Clean` (the default target). Passing = **0 errors AND 0 warnings**, and
  **no stray `info:` notes** — leave the build output clean (see the `ring` note below). This builds
  **only the main library** — it carries no `native_decide` (gated by `scripts/check_no_native_decide.sh`).
- Tests: `lake test` (the `SP1CleanTest` `testDriver`). Builds/elaborates the witness- and trace-conformance
  anchors — the project's **only** `native_decide` — checked against batteries dumped from SP1's real Rust
  prover. Runs on top of the cached main-library oleans (the test lib imports `SP1Clean`, never vice-versa).
- Single file: `lake env lean SP1Clean/Proofs/Chips/AddChip/Formal.lean` (builds deps from cache, then elaborates).
  ⚠️ `lake env lean <file>` **exits 0 even on a Lean stack overflow**, and a stale cached olean can make
  downstream checks pass falsely — **always finish a phase with `lake build SP1Clean`**.
- **Build concurrency.** Elaboration is heavy (full build is ~1800+ jobs across Clean + mathlib + Sail; the
  `toBitVec64`/carry proofs run at high `maxHeartbeats`). Before starting a new build, **let the running one
  finish or kill it** (`pkill -f "lake build"` / `pkill -f "lake env lean"`). Cap at **2–3 builds at once**.
  A `run_in_background` build can outlive its shell — check with `ps -ef | grep -E "lake|lean" | grep -v lsp`
  before spawning another. The lean LSP server (`uvx lean-lsp-mcp`) also keeps several GB warm.
- **Toolchain (pinned, do not bump):** `lean-toolchain` = `leanprover/lean4:v4.28.0`; mathlib `v4.28.0`;
  Clean pinned to merged `main` (`2c20f7f0`, the #398 merge commit — the native gated-channel API; see
  `lakefile.toml`, roadmap W9, and `docs/agents/clean-main-migration.md`). Bump with the **scoped**
  `lake update Clean` (NEVER bare `lake update` — it jumps to the max dep toolchain → 4.29). Sail comes from two `github.com/succinctlabs/*` deps
  pinned to the `dtumad/clean-native` branch — `LeanRV64D` (`sail-riscv-lean`, the generated RV64 model) and
  `RISCV` (`riscv-lean`, the lightweight ISA fns) — which transitively pull the `rems-project/lean-sail @ v4`
  runtime; each carries a 4.28 `lean-toolchain`. All deps are fetched by `lake build`; nothing is a local
  sibling checkout. **Do not run `lake update`** — it bumps the project to the **max** dep toolchain, which
  is what would push it to 4.29. See `docs/agents/lean-sail-notes.md` before touching deps.
- Lake options already set in `lakefile.toml`: `--tstack=400000`, `synthInstance.maxHeartbeats = 1000000`.
- There are no unit tests; correctness lives in the soundness/completeness theorems and the
  `correct_<op>_native` bridges. "Test" = it elaborates and is axiom-clean.

## Architecture

Mirror-rust layout under `SP1Clean/`:

- **`Math/`** — general math, no SP1/Sail deps: `Word.lean` (`Word`, `toBitVec64`, `isU64`, `val_65536_*`,
  `limb_lift`), `Bitwise.lean` (`byteOp`, `reassemble_byteOp`, …), `Misc.lean`, `MulCarryChain.lean`,
  `HWord.lean`, `GetElemFastPath.lean` (the upstreaming candidate).
- **`Model/`** — the SP1 substrate (Sail + buses): `Register.lean`, `SailWrap.lean`, `SailMemory.lean`,
  `BusMessages.lean` (the State/Memory/Program message structs + their structural per-row predicates),
  `Channels.lean` (the channel definitions — `VmChannel`s carrying the semantic guarantees),
  `VmChannel.lean` (the decoupled-`Guarantees`/`Owed` veneer over Clean's `RawChannel`),
  `InteractionBus/Projection/Recovery.lean`, `ChipAir.lean`, `SP1Constraint.lean`, `ByteTable.lean`, and
  the **semantic-execution substrate** `Semantics/` — `GuestProgram.lean` (the `GuestProgram` +
  `IsInitialState`/`SailStep`/`SailChain`/`SP1Halted` Sail execution model), `ProgramCommitment.lean`
  (`progOf : ProverData → GuestProgram`, the committed program), `MicroTime.lean` (bus-clock ↔ step
  correspondence, `MemLoc`, `chainState`, `microValue`), and `Truth.lean` (`StateTruth`/`MemTruth`/
  `ProgTruth`, the semantic channel payloads). `Semantics/` sits **below** `Channels.lean` so the channel
  `Guarantees` can be `StateTruth`/`ProgTruth` directly. (`Math` + `Model` are the former `Foundations/`,
  split by SP1-dependence.)
- **`Extracted/`** — the "extracted from Rust" pillar, **auto-generated, do not hand-edit**: the column
  structs + `asserts`/`interactions` lists (`<Op>.lean`/`<Chip>Chip.lean`), the operation circuit forms
  `Circuit/<Op>.lean` (SP1's `eval` as a Clean circuit), and the witness-conformance vectors
  `WitnessVectors/<Op>.lean`. All regenerated by `update_extracted.py`.
- **`FormalModel/`** — the central audit surface (the "middle ground" between `Extracted` and the proofs):
  `Contracts/` holds the per-reader/operation/chip `Inputs` + semantic `Spec`s (`Readers.lean`,
  `Operations.lean`, `Chips.lean` — the former `Specs/`) and the lifted chip `Assumptions`/`ProverAssumptions`
  (`ChipAssumptions.lean`, currently the ALU chips Add/Addi/Addw/Sub/Subw). `ProverSpec` is uniformly
  `fun _ _ _ => True` (inline in each `circuit` bundle). `Trace/Witness.lean` holds the witness-table
  scaffolding; the guest-program execution model (`GuestProgram`, `IsInitialState`, `SailStep`/`SailChain`,
  `SP1Halted`, `exitOf`) was relocated **down to `Model/Semantics/GuestProgram.lean`** (so the semantic
  channel guarantees can reference it). The trace *arguments* that consume it (`TargetObligations`, the
  `sp1_target_execution` theorem, the `Opcode→chip` routing, `Emits`) reference `ChipRow` (a Soundness-layer
  type), so they cannot move below `Soundness/` and stay there.
- **`Native/`** — the "implemented native in Lean" pillar (circuit construction): `Native/Chips/<Op>Chip/Defs.lean`
  (each chip's `main` + `ElaboratedCircuit`), `Native/Operations/<Op>/{Populate,RawSpec}.lean` (witness +
  native arithmetic core) + flat ops (`BitwiseU16Operation.lean`, `AddressOperation.lean`, …), and
  `Native/Readers/*.lean` (the register/state reader circuits — their `Spec`s are in
  `FormalModel/Contracts/Readers.lean`). The auto-gen op circuit form lives in `Extracted/Circuit/`.
- **`Proofs/`** — the "proven sound/complete" pillar: `Proofs/Chips/<Op>Chip/{Formal,Bridge,…}.lean`
  (soundness/completeness/`circuit` + the Sail bridge; the `Spec` is in `FormalModel/Contracts/Chips.lean`,
  the ALU chips' `Assumptions`/`ProverAssumptions` in `Contracts/ChipAssumptions.lean`),
  `Proofs/Operations/<Op>/Formal.lean` (the `FormalAssertion` soundness/completeness). Flat receiver
  infra (`ByteChip`/`ProgramChip`/`MemoryProvider`) sits in
  `Proofs/Chips/`. The 3 entangled complex chips (DivRem/ShiftLeft/ShiftRight) stay **whole** in
  `Proofs/Chips/` — their `Defs` import sibling proof files, so they are not split into `Native/`.
- **`Faithful/`** — the "proven faithful" pillar: the per-operation/chip constraint anchors (`<Op>.lean`).
- **`SP1CleanTest/`** (top-level, **not** under `SP1Clean/`) — the **test library**, the sole home of
  `native_decide` and the `lake test` target (`testDriver`). It imports the main `SP1Clean` library and
  is never imported by it, so the default `lake build SP1Clean` stays `native_decide`-free (enforced by
  `scripts/check_no_native_decide.sh`; `native_decide` trusts the whole compiler, adding
  `Lean.ofReduceBool`/`Lean.trustCompiler`). Two layers, namespaces preserved (`SP1Clean.WitnessTests` /
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
  `GatedVm/` (the Eulerian-trail machinery) + `SP1Ensemble.lean` (`sp1Ensemble` — a plain Clean
  `Ensemble`, 25 chips + 11 boundary/provider tables — and `sp1_machine_soundness`, the final Clean
  `FormalEnsemble`; W11 Phase 5 re-base, the bespoke `GatedVm` data layer retired); and the
  auditable instruction-coverage layer — `Opcode.lean` + `Coverage.lean` (the `Opcode → chip → Sail`
  routing table mirroring SP1's `tracing.rs`/`RiscvAir`), `InstructionTrace.lean` (instruction-sequence →
  `ChipRow`-sequence map, mirroring `ExecutionRecord`/`generate_trace`), and `Completeness.lean`
  (partial-VM-completeness scaffold). The bespoke `MachineSoundness`/`MachineConsistency` `TraceValid`
  capstone was retired 2026-06-05 — the gated path is the sole capstone. `TargetVm.lean` is the
  **target machine-level theorem** (`Target.sp1_target_execution`: trail → real `try_step` Sail chain
  from a loaded `GuestProgram` to the halting ECALL, walk induction proved; the open gaps are the
  named `TargetObligations` seams, mapped to roadmap W-items). Audit harness: `scripts/run_audit.sh`
  (pins + sorry gates + the `#print axioms` census via `scripts/gen_axiom_probe.py`).
- `Soundness/RowView.lean` (the reader-agnostic `RowView`/`AdapterView` row-view infra the bus layer reads —
  formerly the top-level `Trace.lean`) and top-level `Comparison.lean` (the worked-example findings doc — read
  it for the full design rationale). The root index is `SP1Clean.lean` — **wire every new module's import there**.

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

**Restructure status (updated 2026-06-23).** Landed & green: the `Math`/`Model` split, `Extracted/` auto-gen
consolidation (`Circuit/` + `WitnessVectors/`), the `FormalModel/Contracts/` audit surface (all `Spec`s +
the ALU chips' `Assumptions`/`ProverAssumptions`), the `Native/`+`Proofs/` five-pillar re-bucket of
`Chips`/`Operations`/`Readers`/`WitnessTests`, and all six per-pillar layer libraries — build green
(3676 jobs), audit clean (366 probes, `sorryAx` confined to the known debt). **DivRem/ShiftLeft/ShiftRight/Mul
completeness are all closed** (2026-06-12 / 06-18), leaving **one** remaining `sorry` — `sp1_witness_decode`
(the capstone W1b/W1c decode seam). A large proof-cleanup campaign (2026-06-22 / 06-23) golfed ~109
hand-written files (−591 lines) while preserving axiom-cleanliness, plus substrate-hoist refactors
(`Word.isU64_four`, Faithful `val_16`/`bool_iff` dedup → `ChipTactics`). Upstream `main` was merged in
2026-06-23 (#100 hard-gates `skipKernelTC` and removes overrides; #101 fleshes out the immediate-type Sail
bridges; #102 makes the jalr/jal/branch specs explicit about divisibility / LSB-clearing). Planned (approved
plan, not yet done): lifting the remaining chips' `Assumptions` onto the audit surface (helper-dependent
chips Jal/Jalr/Branch/DivRem/ShiftLeft/ShiftRight + split-`Spec` Lt/Bitwise keep theirs in their proof
files). The trace *arguments* (TargetObligations / target theorem / routing / Emits) are `ChipRow`-dependent
and so remain in `Soundness/` — their natural layer — rather than being forced below it.
The bespoke `Soundness/GatedVm/` → Clean `VmTables` migration (roadmap W11) was investigated and **deferred**
— Clean's VM engine yields verifier-guarantees with no explicit execution walk, while SP1's spec is a
balance-derived `GatedExecution` with an Eulerian trail, so re-basing adds obligations without removing the
SP1-specific trail machinery (see roadmap W11).

**Semantic-channels program (in progress, 2026-07).** The approved direction (`docs/` roadmap + the
`semantic_channels_program` memory) inverts the architecture so the **channels carry the execution
semantics**: the prover commits the guest program in `ProverData`, the State channel's guarantee becomes
`StateTruth` ("the deterministic Sail execution of the committed program is at this pc at this clk"), the
Program channel's becomes `ProgTruth` (fetch-decode correspondence), and **memory stays structural
`isU64`** (pure coherence bookkeeping — never carries execution truth, never in the final theorem). Landed:
the `VmChannel` veneer (decoupled `Guarantees`/`Owed`), the semantic foundation (`progOf`/`MicroTime`/
`Truth`), the Phase-1 end-to-end spike (`Spike/`, axiom-clean), the full reader/chip `FormalAssertion →
GeneralFormalCircuit` sweep, the **relocation of the execution substrate down to `Model/Semantics/`**, and
the **State-channel flip (Phase 2c, 2026-07-05)**: `stateChannel` is now a `VmChannel` carrying
`Guarantees := StateTruth` (Owed `True`) — CPUState → GFC supplying the pull's `StateTruth`, all 25 chips
threading it, the boundary verifier carrying the final-state truth, the parked `StateVm` VmTables spike
retired. **Consequence (disclosed): `sp1_machine_soundness` now inherits the Sail platform trust base**
(`riscv_f*`/`plat_*`/`*_reservation`/…) — the capstone is tied to the Sail execution model via the state
channel; `StateTruth` is not yet grounded in the soundness *conclusion* (that is the engine phase). Next:
the program flip (`ProgTruth` — needs the decode maps relocated to `Model`), then the per-chip `advance`
lemmas + the timed-channel grounding engine.

Everything is **field-generic** over a prime field — the standard variable block is:
```lean
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
```

## Clean-native principles (non-negotiable)

These are the keepers from sp1-lean's "faithful sub-circuit composition" discipline; violations are bugs.

1. **Compose true Clean subcircuits, not inline constraints.** A chip's `main` calls
   `subcircuit <SubOp>.circuit ⟨…⟩`; a gadget that uses another gadget composes it the same way. Never inline a
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
   only `[propext, Classical.choice, Quot.sound]` (bv_decide may add `Lean.ofReduceBool`/`trustCompiler`) — and
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
    violations). Residue lives in `scripts/nolints.json` (21 stable entries — 3 `defLemma`
    obligation-bundle defs + 18 `simpComm`/`simpNF` Math/Model/Sail simp lemmas); `lake exe sp1Lint --update`
    regenerates it; CI runs `lake lint` in the build job. Deliberately **dropped**: `docBlame`/`tacticDocs`
    (doc-coverage noise) and `unusedArguments` (flags only the uniform field-generic / `ProverData` signature
    args — all structural, and a fresh false-positive per new chip).
  - The next-candidate linter (`longLine`) is tracked in `docs/roadmap.md` § "Cleanup / polish backlog"; the
    non-negotiable suppressions — `unusedSectionVars`/`unusedSimpArgs` (structurally necessary in circuit
    proofs) and the auto-gen `linter.all false` — must stay.
- Heavy `toBitVec64` rw chains are whnf-expensive — `set_option maxHeartbeats 2000000 in` (carry lemmas need up
  to `16000000`).
- **Never `set_option (debug.)skipKernelTC`.** It bypasses the kernel's type-check re-run — the trust anchor
  for an axiom-clean proof — so it is **CI-gated** (`scripts/check_no_skipkerneltc.sh`, run by the audit and a
  standalone CI `guards` job; any hit in `SP1Clean/**/*.lean` fails the build). If a goal blocks on a kernel
  deep-recursion / `2^64`-unfold error, the fix is to factor the expensive compute into an **abstract-`BitVec`
  helper** proved once over variables (the `srl_toNat`/`sra_toNat` pattern), then apply it symbolically — never
  silence the kernel. See `docs/agents/proof-patterns.md` §"Bit-shift chip soundness" (the `2^64` bullet) for
  the worked fix.
- **Never `native_decide` in the main `SP1Clean/` library.** It discharges goals by running compiled code,
  trusting the **whole compiler** (adds `Lean.ofReduceBool`/`Lean.trustCompiler`) — so headline soundness
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
- Full landmine list + the witnessed-`FormalCircuit` recipe: `docs/agents/proof-patterns.md`.

## MCP servers

`.mcp.json` declares `lean-lsp` (live goal/diagnostic state from the Lean LSP). It launches via `uvx`, so `uv`
must be on `PATH` — install with `curl -LsSf https://astral.sh/uv/install.sh | sh` if missing. Local
enable/permissions are in `.claude/settings.local.json` (`enableAllProjectMcpServers: true`). Restart the agent
after installing or toggling.

## docs/

- `docs/README.md` — index + "what to read first".
- `docs/architecture.md` — the four-artifact chain, layout, design verdict, what's deferred.
- `docs/roadmap.md` — the W-graph dependency chart, open work, debt status.
- `docs/bus-model.md` — the cross-chip interaction-bus model (channels, consistency).
- `docs/release-audit.md` — the honest-claim / trust-boundary report (axiom census + sorry inventory;
  regenerate with `scripts/run_audit.sh`).
- `docs/agents/lean-sail-notes.md` — the 4.28 environment: toolchain pins, why public Clean `main`, the local Sail
  setup + `lake update` trap, the Clean-main ↔ Batteries import collision and its fix.
- `docs/agents/proof-patterns.md` — the witnessed-`FormalCircuit` soundness/completeness recipe + concrete
  landmines + the **Golf & cleanup discipline** section (how to golf/clean proofs safely).
- `docs/agents/porting-recipe.md` — step-by-step checklist to port a new chip from the Add/Bitwise template.
- `docs/agents/extraction.md` — the constraint-extraction pipeline (compiler → Python → Lean DSL).
- `docs/agents/mul-operation-learnings.md` — Mul-specific soundness/completeness pitfalls.
- `docs/snapshots/compile-profile.md` — per-module wall-clock compile profile + worst offenders + common threads
  (point-in-time snapshot); re-run with `scripts/profile_compile.sh`.
- `docs/snapshots/axiom-ledger.md` — machine-checked `#print axioms` inventory per theorem (point-in-time
  snapshot; re-generate before release).
