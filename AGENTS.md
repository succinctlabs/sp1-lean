# AGENTS.md

Guidance for AI agents working in this repository (`sp1-clean-native`).
`CLAUDE.md` is a one-line pointer to this file so Claude Code auto-loads it.

## What this repo is

A **Clean-native, semantically-specified** formal verification of SP1's RISC-V chips, built fresh in
Lean 4.28 on the **public** Clean DSL. For each operation we build a chain of four artifacts:

1. a **witnessed `FormalCircuit` gadget** (`Operations/<Op>.lean`) with a *semantic* spec
   (e.g. `Word.toBitVec64 value = Word.toBitVec64 a + Word.toBitVec64 b`), whose arithmetic is
   **re-derived natively** in-project;
2. a **`GeneralFormalCircuit` chip** (`Chips/<Op>Chip/`, split `Defs.lean` (`main` + `ElaboratedCircuit`)
   + `Formal.lean` (`Assumptions`/`Spec`/soundness/completeness/`circuit`)) that composes the gadget as a
   true Clean `subcircuit` plus an `is_real` selector gate, exposing one semantic, gated `Spec`;
3. a **native Sail bridge** (`Chips/<Op>Chip/Bridge.lean`) proving the chip's `Spec` reaches the RISC-V Sail
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
`fromMain`/`toMain` pattern. Needed foundations are re-created here (`Foundations/`). The goal: every headline
theorem is **axiom-clean** — `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

The SP1 Rust source (the extraction/spec oracle, read-only reference) lives in a sibling `sp1` checkout
(`$SP1_DIR`, by default `../sp1`). The 4.29 `sp1-lean` repo is a read-only reference for porting (a sibling
`sp1-lean` checkout); its arithmetic/Sail proofs are the thing we re-derive natively here, not import.

## Build

- Full build: `lake build SP1Clean` (the default target). Passing = **0 errors AND 0 warnings**, and
  **no stray `info:` notes** — leave the build output clean (see the `ring` note below).
- Single file: `lake env lean SP1Clean/Chips/AddChip.lean` (builds deps from cache, then elaborates).
  ⚠️ `lake env lean <file>` **exits 0 even on a Lean stack overflow**, and a stale cached olean can make
  downstream checks pass falsely — **always finish a phase with `lake build SP1Clean`**.
- **Build concurrency.** Elaboration is heavy (full build is ~1800+ jobs across Clean + mathlib + Sail; the
  `toBitVec64`/carry proofs run at high `maxHeartbeats`). Before starting a new build, **let the running one
  finish or kill it** (`pkill -f "lake build"` / `pkill -f "lake env lean"`). Cap at **2–3 builds at once**.
  A `run_in_background` build can outlive its shell — check with `ps -ef | grep -E "lake|lean" | grep -v lsp`
  before spawning another. The lean LSP server (`uvx lean-lsp-mcp`) also keeps several GB warm.
- **Toolchain (pinned, do not bump):** `lean-toolchain` = `leanprover/lean4:v4.28.0`; mathlib `v4.28.0`;
  Clean from `github.com/Verified-zkEVM/clean @ main`. Sail comes from two `github.com/succinctlabs/*` deps
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

- **`Foundations/`** — re-created core: `Word.lean` (`Word`, `toBitVec64`, `isU64`, `val_65536_*`,
  `limb_lift`), `Bitwise.lean` (`byteOp`, `reassemble_byteOp`, …), `Misc.lean`, `Register.lean`,
  `SailWrap.lean` (trimmed Sail RTYPE/register wrappers).
- **`Operations/`** — the witnessed gadgets (`AddOperation.lean`, `BitwiseU16Operation.lean`, …).
- **`Chips/`** — per-chip directories `<Op>Chip/` each split into `Defs.lean` (`main` + `ElaboratedCircuit`),
  `Formal.lean` (`Assumptions`/`Spec`/soundness/completeness/`circuit`), and (where present) `Bridge.lean`
  (the Sail bridge). `ByteChip.lean`/`ProgramChip.lean` are flat pure-lemma "receiver" infra files.
- **`Faithful/`** — the per-operation constraint anchors (`<Op>.lean`).
- **`WitnessTests/`** — the witness-generation conformance layer: auto-generated `<Op>WitnessVectors.lean`
  vectors (dumped from SP1's real `populate`) paired with hand-written `<Op>Witness.lean` `native_decide`
  anchors, plus the shared `WitnessConformance.lean` scaffold. All in namespace `SP1Clean.WitnessTests`;
  vectors regenerated by `update_extracted.py`.
- **`Soundness/`** — the whole-machine layer: per-bus `{State,Byte,Program,Memory}Consistency.lean`;
  `ChipRow.lean` (the `ChipKind` structure-of-functions — each chip registers one `kind`, carrying a
  `name` = its SP1 `MachineAir::name`) + `ChipRegistry.lean` (`allChipKinds`); the gated execution capstone
  `GatedVm/` + `SP1GatedVm.lean` (`sp1_machine_soundness`, the final Clean `FormalEnsemble`); and the
  auditable instruction-coverage layer — `Opcode.lean` + `Coverage.lean` (the `Opcode → chip → Sail`
  routing table mirroring SP1's `tracing.rs`/`RiscvAir`), `InstructionTrace.lean` (instruction-sequence →
  `ChipRow`-sequence map, mirroring `ExecutionRecord`/`generate_trace`), and `Completeness.lean`
  (partial-VM-completeness scaffold). The bespoke `MachineSoundness`/`MachineConsistency` `TraceValid`
  capstone was retired 2026-06-05 — the gated path is the sole capstone.
- Top-level `Trace.lean` (the reader-agnostic `RowView`/`AdapterView` row-view infra the bus layer reads),
  `Comparison.lean` (the worked-example findings doc — read it for the full design rationale),
  `Step0Smoke.lean`. Lake auto-globs subdir modules; the root index is `SP1Clean.lean` — **wire every
  new module's import in there**.

Everything is **field-generic** over a prime field — the standard variable block is:
```lean
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
```

## Clean-native principles (non-negotiable)

These are the keepers from sp1-lean's "faithful sub-circuit composition" discipline; violations are bugs.

1. **Compose true Clean subcircuits, not inline constraints.** A chip's `main` calls
   `subcircuit <SubOp>.circuit ⟨…⟩`; a gadget that uses another gadget composes it the same way. Never inline a
   sub-operation's constraints.
2. **One `main`, one `Spec` per file.** Each `Operations/<Op>.lean` and `Chips/<Op>Chip/` exposes exactly
   one `main` and one `Spec` (plus the `circuit` glue), and references sub-operation Specs *by direct field
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
- Imports MUST precede the module doc-comment (the package `-D linter.flexible` flag is rejected on a
  zero-imports header).
- Heavy `toBitVec64` rw chains are whnf-expensive — `set_option maxHeartbeats 2000000 in` (carry lemmas need up
  to `16000000`).
- `mul_eq_zero` won't fire on `ZMod p` (a `Nat.rec` Mul-instance quirk) — derive booleanness via
  `inv_mul_cancel₀` / a `bool_of_mul_pred`-style lemma instead.
- `Word` is an `abbrev` for `Vector` — `w.toBitVec64` dot-notation fails; write `Word.toBitVec64 w`.
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
  once in `Foundations/Channels.lean`. A missing default-tactic close means a missing `circuit_norm` lemma,
  not a reason to hand-write the field. These lemmas also tidy `circuit_proof_start`; mind the soundness
  requirement-tail caveat. Full recipe: `docs/agents/proof-patterns.md` "ElaboratedCircuit field obligations".
- Full landmine list + the witnessed-`FormalCircuit` recipe: `docs/agents/proof-patterns.md`.

## MCP servers

`.mcp.json` declares `lean-lsp` (live goal/diagnostic state from the Lean LSP). It launches via `uvx`, so `uv`
must be on `PATH` — install with `curl -LsSf https://astral.sh/uv/install.sh | sh` if missing. Local
enable/permissions are in `.claude/settings.local.json` (`enableAllProjectMcpServers: true`). Restart the agent
after installing or toggling.

## docs/

- `docs/architecture.md` — the four-artifact chain, layout, design verdict, what's deferred.
- `docs/agents/lean-sail-notes.md` — the 4.28 environment: toolchain pins, why public Clean `main`, the local Sail
  setup + `lake update` trap, the Clean-main ↔ Batteries import collision and its fix.
- `docs/agents/proof-patterns.md` — the witnessed-`FormalCircuit` soundness/completeness recipe + concrete landmines.
- `docs/agents/porting-recipe.md` — step-by-step checklist to port a new chip from the Add/Bitwise template.
- `docs/snapshots/compile-profile.md` — per-module wall-clock compile profile + worst offenders + common threads
  (point-in-time snapshot); re-run with `scripts/profile_compile.sh`.
- `docs/snapshots/axiom-ledger.md` — machine-checked `#print axioms` inventory per theorem (point-in-time
  snapshot; re-generate before release).
