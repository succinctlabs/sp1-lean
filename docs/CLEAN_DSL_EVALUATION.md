# Clean DSL evaluation — alternative extraction target / parallel constraint rep

Initial assessment, dated 2026-05-18. Reviews [Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean) (local clone at `../clean`, git rev as of 2026-05-18) against the SP1-lean constraint architecture for two roles:

- **A.** Alternative extraction target — have `update_constraints.py` emit Clean circuits instead of (or alongside) `SP1ConstraintList`.
- **B.** Parallel constraint representation — keep `SP1ConstraintList` as the source of truth, but mirror each chip in Clean and prove an equivalence, gaining Clean's soundness/completeness pairing and Plonky3 export for free.

Not in scope: replacing the Sail/`SailM` ISA bridge with Clean primitives. The current `spec_<op>` proofs route through `LeanRV64D.execute_*` and are out of scope to restructure here.

---

## TL;DR

- **Use case A (extraction target) — not recommended now.** Clean's `Circuit F α` is a monadic writer (`clean/Clean/Circuit/Basic.lean:28`), structurally different from SP1's flat `SP1ConstraintList`. Migration is ~25 chips × (rewrite constraints + restate soundness + reprove), and most existing `SP1Operations/` helpers (`AddOperation`, `RTypeReader`, `CPUState`) don't transfer.
- **Use case B (parallel rep) — defensible as a single-chip spike, but the cost/benefit is poor at scale.** A `cleanConstraints : Vector (ZMod KB) N → Circuit (ZMod KB) Unit` + an equivalence theorem buys access to Clean's `FormalCircuit` machinery and the Plonky3 backend without touching existing proofs. Costs: extra surface to keep in sync after `update_constraints.py` regenerations, a KoalaBear `Field` instance Clean has never been exercised on, and ~1 new file per chip.
- **Two upstream signals worth tracking before committing.** zkSecurity's blog post lists "a formally verified minimal VM for a subset of RISC-V" as planned work (https://blog.zksecurity.xyz/posts/clean), and Plonky3 backend polish is on the roadmap (`clean/README.md:63-64`). Both are directly relevant; both are currently early-stage.
- **Headline risks:** no KoalaBear field in upstream Clean (grep returns zero hits across `../clean`); Plonky3 backend is a self-described POC (`clean/backends/plonky3/readme.md:3`); no existing CPU/ISA template under `clean/Clean/Tables/`; Clean's `circuit_norm` simp set is untested against the chip-sized goal states this repo routinely hits.
- **Recommendation:** if anyone has appetite, run a one-week spike on `AddChip` for use case B (parallel rep + equivalence), with the explicit success criteria in §8. Defer use case A pending the upstream RISC-V VM and Plonky3 maturation.

---

## 1. What Clean is

**Core monad** (`clean/Clean/Circuit/Basic.lean:28`):

```lean
def Circuit (F : Type) [Field F] (α : Type) := ℕ → α × List (Operation F)
```

A writer-state monad that accumulates operations while threading the local-variable offset. Four operation kinds (`clean/Clean/Circuit/Operations.lean:16-20`):

```lean
inductive FlatOperation (F : Type) where
  | witness : (m : ℕ) → (ProverEnvironment F → Vector F m) → FlatOperation F
  | assert  : Expression F → FlatOperation F
  | lookup  : Lookup F → FlatOperation F
  | interact : AbstractInteraction F → FlatOperation F
```

**Witnesses are first-class.** Each `witness` operation carries the prover's compute function (`compute : ProverEnvironment F → Vector F m`). Clean's `Circuit.proverEnvironment` (`Basic.lean:643`) reduces a circuit to a concrete prover-side env by chaining those generators — i.e. Clean's circuits can both *prove* their own constraints and *generate the trace*. SP1's `SP1Constraint` is purely declarative; trace generation lives in the SP1 Rust prover.

**Channels** (`Basic.lean:131-146`) — `Channel.emit / push / pull` — are the analogue of `send`/`receive` interactions, but typed (`Message : TypeMap`) and validated by a `ChannelsLawful` predicate (`Basic.lean:196-203`).

**Soundness and completeness as paired statements** (`Basic.lean:259-283`):

```lean
def Soundness   ... Assumptions Spec      -- ∀ env, Assumptions → ConstraintsHold → Spec
def Completeness ... Assumptions          -- ∀ env, UsesLocalWitnesses → Assumptions → ConstraintsHold
```

A `FormalCircuit` (`Basic.lean:298-303`) bundles a circuit with both proofs. Variants `FormalAssertion` (`:356-366`), `GeneralFormalCircuit` (`:415-428`), and `GeneralFormalCircuit.WithHint` (`:470-484`) cover assertion-only and hint-aware cases. The pairing is the central design claim: a proven `FormalCircuit` behaves "similar to a function" (`Basic.lean:295`).

**Structured circuit values** via `ProvableType` (`clean/Clean/Circuit/Provable.lean:12-37`):

```lean
class ProvableType (M : TypeMap) where
  size : ℕ
  toElements {F} : M F → Vector F size
  fromElements {F} : Vector F size → M F
```

Any type that flattens to a field vector can flow through a circuit (`U32`, `U64`, vectors, custom structs via `deriving ProvableStruct`). This is how Clean writes circuits over RISC-V-shaped data without exploding into raw field expressions.

**AIR tables.** `clean/Clean/Tables/Fibonacci32Inductive.lean` is the canonical small example — 46 lines including `Spec`, `soundness`, and `completeness` — and uses `InductiveTable` to lift a per-row `step` (which itself invokes `Addition32.circuit`) into a multi-row claim. `clean/Clean/Tables/KeccakInductive.lean` is the closest analog to a complex SP1 chip: 25-element `KeccakState` of `U64`s, multi-block absorption. There is **no `Cpu` / `Risc` / `Instruction` table.**

**Backend.** `clean/backends/plonky3/` (Rust + Cargo) consumes Clean's `Operation` list and produces a Plonky3 AIR. The integration test (`backends/plonky3/tests/clean_air.rs`) proves the Fibonacci circuit end-to-end in ~2 s. The readme labels itself "NOT-PRODUCTION-READY POC" (`backends/plonky3/readme.md:3`).

**Field abstraction.** Every core definition is parametric in `[Field F]`. No concrete field is committed. KoalaBear (`KB = 2130706433`) is **not present** anywhere in the upstream repo (`grep -rn "KoalaBear\|2130706433\|RISC\|riscv" ../clean` returns no hits).

---

## 2. What sp1-lean has today

**Constraint datatype** (`SP1Foundations/Constraint.lean:9-34`):

```lean
inductive AirInteraction (F : Type*) where
  | byte    (op : ByteOpcode) (a b c : F)
  | memory  (clk_high clk_low addr0 addr1 addr2 limb0 limb1 limb2 limb3 : F)
  | state   (clk_high clk_low pc0 pc1 pc2 : F)
  | program (pc0 pc1 pc2 : F) (opcode : Opcode) (op_a op_b_0 ... imm_c : F)

inductive SP1Constraint (F : Type*) where
  | assertZero (x : F)
  | send       (interaction : AirInteraction F) (mult : F)
  | receive    (interaction : AirInteraction F) (mult : F)
```

Flat list of three variants. The interaction families (byte/memory/state/program) are baked into the inductive — Clean's `AbstractInteraction` is more open-ended (any `Message : TypeMap` with a `ProvableType` instance).

**Two semantic projections** of a constraint list:

- `toProp_poly` (`Constraint.lean:41-67`) → `Prop`. `assertZero` becomes field equality; `send (.program …)` becomes opcode-validity (`trusted_instr_poly`) plus `op_a < 32` plus per-limb `< 65536` plus boolean-flag conditions.
- `toStateProp_poly` (`Constraint.lean:86-104`) → state-bridging facts. `send (.memory …)` becomes register-read agreement (`s.get_reg? … = some (Word.toBitVec64_poly …)`) when address is register-shaped, or byte-level memory agreement otherwise. `receive (.state … pc …)` becomes `s.regs.get? Register.PC = some …`.

Aggregated into `allHold_poly` / `initialState_poly` (`Constraint.lean:115-121`).

**Per-chip proof structure** (`SP1Chips/AddChip.lean:17-95`, paired with the generated `SP1Chips/Add/Constraints.lean:7-24`):

```lean
-- spec: Sail-side reference
noncomputable def spec_add (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

-- sp1: SP1-side implementation, reading row columns
def sp1_add : SailM Unit := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

theorem correct_add
  (cstrs       : (constraints Main).allHold_poly)
  (h_is_real   : Main[32] = 1)
  (state_cstrs : (constraints Main).initialState_poly s) :
  (spec_add ...).run s = (sp1_add Main).run s
```

The theorem shape is **SailM equality under three hypotheses**: propositional constraints hold, the trace row's `is_real` column is 1, and the row's state-interaction columns agree with the actual `SailState s`. The proof body (60+ lines) destructures `cstrs`, specializes `CPUState.allHold_constraints_iff_is_real_poly` and `RTypeReader.allHold_constraints_iff_is_real_poly`, extracts initial-state facts, then rewrites the monadic forms via `run_readReg`/`exec_RTYPE_pure_bv_to_w_poly` etc. (`AddChip.lean:44-94`).

The generated block (`Add/Constraints.lean:7-24`) is auto-emitted by `cargo run -p sp1-constraint-compiler` between the `section constraints` / `end constraints` markers. **Never hand-edit** that block — see `CLAUDE.md` and `docs/CONSTRAINT_REGEN.md`.

**Field.** `KB = 2130706433` (`SP1Foundations/Field.lean`), but chip proofs are stated generically: `{p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]` (`AddChip.lean:12-13`). Multiple recent docs cover field genericization (`docs/FIELD_GENERIC.md`).

**Aggregator.** `SP1Chips/Soundness.lean` (812 lines) collects per-chip `correct_*` theorems and dispatches multi-opcode chips. No whole-VM theorem yet.

---

## 3. Side-by-side architectural diff

| Axis | sp1-lean (current) | Clean | Implication |
|---|---|---|---|
| **Constraint datatype** | Flat `inductive SP1Constraint` (3 variants) over a *closed* inductive `AirInteraction` (byte/memory/state/program). | `Circuit F α` monad over `FlatOperation` (4 variants: witness, assert, lookup, interact). | Different shapes. Translation is structural, not syntactic. |
| **Witness model** | None. Trace generation lives in Rust. | First-class: every `witness` op carries a `ProverEnvironment F → Vector F m` generator (`Basic.lean:92-115`). | Clean circuits can self-host the prover — a feature SP1 didn't try to capture. Irrelevant if we only want SP1's verifier guarantee. |
| **Field** | `ZMod p` with `[Fact (2^17 < p)]`, concretized to KoalaBear. | `[Field F]` generic; no KoalaBear instance. | We'd have to add and exercise a KB instance against Clean's `circuit_norm` simp set — untested territory. |
| **Lookups / interactions** | `send` / `receive` with fixed `AirInteraction` payload; balance enforced separately. | Typed `Channel`s (`Basic.lean:131-146`) carrying any `[ProvableType Message]`, with `ChannelsLawful` (`Basic.lean:196-203`). | Clean's model is strictly more expressive; mapping SP1's byte/memory/state/program families to typed channels is mechanical. |
| **Structured types** | None on the constraint side. The `spec_*`/`sp1_*` layer uses `BitVec 64`, `Word`, `regidx` via Sail. | `ProvableType` / `ProvableStruct` (`Provable.lean:12-37`). | Clean would let constraint code talk about `U64`/`Register` directly instead of `Main[k] : F` slots. |
| **Soundness statement** | `(spec_*).run s = (sp1_*).run s` under `allHold_poly`, `initialState_poly`, `Main[last] = 1`. SailM-equality. | `Assumptions input → ConstraintsHold → Spec input output` (`Basic.lean:259-271`). Pure-Lean predicate. | **The two shapes don't unify.** The SailM bridge is structural to the SP1 statement — translating an SP1 chip into a `FormalCircuit` would still need a separate "Spec ↔ SailM" theorem on top. |
| **Completeness** | Not stated. Implicit in "the SP1 prover produces a satisfying trace." | Required as a peer of soundness (`Basic.lean:274-283`). | Free win in Clean — modulo the work of writing the witness generators. |
| **Codegen seam** | `update_constraints.py` → Rust `sp1-constraint-compiler` → Lean text inside `section constraints` markers. | None (circuits hand-written in Lean monad notation). | Clean as an extraction target ⇒ rewrite the constraint compiler. Big. |
| **Backend** | None in this repo. SP1 prover is separate. | `backends/plonky3/` POC, ~2 s for Fibonacci, no KoalaBear support and explicit "NOT-PRODUCTION-READY POC". | Even if we ported, the downstream path is not production yet. |
| **Existing gadget library** | `SP1Operations/Operation/*` and `SP1Operations/Compare/*` — purpose-built around `AirInteraction` byte ops. | ~50 gadgets including `Addition8/32`, `Bits`, `IsZero`, `IsEqual`, `ByteDecomposition`, plus `BLAKE3` and `Keccak` suites. No `MulOperation`, no `DivRem`, no RISC-V instruction decoders. | Significant per-chip rewriting either way. Clean's gadgets are more generic but cover less of the RISC-V surface. |

---

## 4. Use case A — alternative extraction target

**Mechanics.** Today, `update_constraints.py` shells to `cargo run -p sp1-constraint-compiler` (in an external SP1 checkout under `$SP1_DIR`) and splices its Lean output between `section constraints ... end constraints` markers as a flat list of `SP1Constraint` values. To make Clean the target instead, we'd need:

1. **Rust-side rewrite.** `sp1-constraint-compiler` currently emits SP1 ADT literals (`(.assertZero E1)`, `AddOperation.constraints #v[…]`, etc., per `Add/Constraints.lean:13-22`). Clean wants `do`-notation in the `Circuit F Unit` monad with explicit `assertZero e`, `lookup table entry`, and `Channel.emit/pull/push` calls (`Basic.lean:117-146`). Offset threading is implicit in the monad — the emitter doesn't have to track it, but it does have to maintain stable variable identity across calls. Mechanical but invasive.
2. **Lean-side rewrite of every chip's hand-written half.** The `spec_<op>` / `sp1_<op>` / `correct_<op>` triple (`AddChip.lean:17-95`) becomes a `FormalCircuit.Spec input output` predicate + a `FormalCircuit.soundness` proof. The SailM bridge does **not** disappear — Sail still defines the reference `execute_*` — so we'd additionally keep a theorem of the form `Spec input output → (spec_<op> ...).run s = (sp1_equiv input output).run s` to recover the current SailM-equality guarantee.
3. **Operations library rewrite.** `SP1Operations/Operation/AddOperation`, `SP1Operations/Reader/CPUState`, `SP1Operations/Reader/RTypeReader`, and their `_poly` siblings are written against `SP1ConstraintList`. They don't transfer — Clean's analog is `Gadgets/Addition32`, plus presumably-new `RegisterFile`/`InstructionDecoder` gadgets that don't exist upstream yet.
4. **Field plumbing.** Add a KoalaBear `Field (ZMod 2130706433)` instance (mostly inherited from Mathlib), then port the high-priority arithmetic instances that this repo uses to keep typeclass synthesis tractable (`SP1Foundations/Field.lean:101-110`). Whether Clean's `circuit_norm` simp set behaves well over KB at the goal sizes this repo hits is **unknown** — none of Clean's existing gadgets stress-test that.

**Cost.** ~25 chips × (rewrite generated constraints + rewrite hand-written triple + reprove) + Rust compiler rewrite + 8–15 supporting `SP1Operations/*` ports + KoalaBear plumbing. Conservatively a multi-month effort, with significant risk that the prover-environment / witness-generator obligations Clean expects (`Basic.lean:643-644`) don't map cleanly onto SP1's external Rust prover (which never sees the Lean witness functions).

**Gain.** Free completeness proofs per chip. Composable `FormalCircuit`s (the same gadget can be reused across chips with a `CoeFun` call). A path to Plonky3 export. Structured types in the constraint layer (Register/U64/Word instead of `Main[k]`).

**Verdict.** Not recommended now. Reconsider when (a) the upstream `clean` RISC-V VM lands, signaling that the gadget library and patterns are right-sized for an ISA, and (b) the Plonky3 backend is production-grade with KoalaBear support.

---

## 5. Use case B — parallel constraint representation

**Mechanics.** Keep `constraints : Vector (ZMod p) N → SP1ConstraintList (ZMod p)` and the entire existing proof stack. Add, per chip:

```lean
-- New file: SP1Chips/Add/CleanCircuit.lean
def cleanConstraints (Main : Vector (ZMod KB) 33) : Circuit (ZMod KB) Unit := do
  -- Mirror Add/Constraints.lean line-for-line:
  -- AddOperation.constraints  →  Addition32.circuit (after wrapping Main slices as U32)
  -- CPUState.constraints      →  hand-written cpuState gadget (does not exist yet)
  -- RTypeReader.constraints   →  hand-written rTypeReader gadget (does not exist yet)
  -- (.assertZero E1)          →  assertZero (Main[32] * (Main[32] - 1))
  -- (.assertZero Main[13])    →  assertZero Main[13]
  ...

-- Equivalence theorem
theorem clean_iff (Main : Vector (ZMod KB) 33) (env : Environment (ZMod KB)) :
  (Add.constraints Main).allHold_poly ↔
    ConstraintsHold.Soundness env ((cleanConstraints Main) 0).2 := ...
```

Once we have the equivalence, anything provable in Clean's `FormalCircuit` framework (soundness, completeness, Plonky3 export) is automatically available for that chip's existing constraints.

**Cost per chip.** Roughly:

- Hand-write the Clean mirror (~50–150 lines per chip; chip-shape dependent).
- Prove `clean_iff` (this is the load-bearing step — `simp [constraints, cleanConstraints, ConstraintsHold]` may discharge most of it, but the `Channel.emit`/`send` correspondence will need a mapping lemma).
- New gadgets we'd need to write because Clean doesn't have them: `CpuState`, `RTypeReader`, `ITypeReader`, `JTypeReader`, `ALUTypeReader`, byte-opcode lookup gadgets matching SP1's `ByteOpcode` (`SP1Foundations/ByteOpcode.lean`).

**Cost system-wide.**

- A KoalaBear `Field` instance — same plumbing as use case A, but the blast radius is bounded to the new mirror files.
- A drift-prevention plan: when `update_constraints.py` regenerates `Add/Constraints.lean:13-22` (shifting `Main[k]` indices or adding/removing rows), the mirror must regenerate too, or `clean_iff` breaks silently. Two options:
  - **(b1)** Extend `sp1-constraint-compiler` to additionally emit the Clean mirror — keeps codegen single-source. Smaller scope than use case A's full rewrite because the source-of-truth proofs still live on the SP1 side.
  - **(b2)** Hand-mirror, and add a CI check that `clean_iff` builds after every regeneration. Cheaper to start, more painful to maintain at 25-chip scale.

**Gain.**

- For each chip with `clean_iff` proven: a `FormalCircuit` instance, hence a free completeness statement and an extraction path to Plonky3 (once KoalaBear lands there).
- A second, independently-typed view of every constraint. If Clean's view disagrees with `SP1Constraint`'s, that's an immediate red flag — useful as a sanity check on the generator output. (This is the "more reasoned foundations" angle the user asked about.)
- Decouples downstream Clean upgrades from the SailM bridge.

**Risk-adjusted recommendation.** Spike on `AddChip` first. The 33-column shape is small enough to prove `clean_iff` by hand without (b1), and lets us calibrate: how big is the gadget gap (CpuState/RTypeReader), how does `circuit_norm` interact with KB literals, how invasive is the eventual codegen extension.

---

## 6. Headline risks

1. **KoalaBear has zero presence in Clean.** Grep across `../clean` for `KoalaBear|2130706433|RISC|riscv` returns nothing. We'd be the first to exercise Clean's gadget set against this field. The existing Fibonacci/Addition gadgets typically require `[Fact (p > 512)]` or larger (`clean/Clean/Tables/Fibonacci32Inductive.lean:7` requires `[Fact (p > 512)]`); KB ≫ that, so no soundness blocker, but the simp/arithmetic tactics may misbehave under KB-shaped literals.
2. **No CPU/ISA template upstream.** `clean/Clean/Tables/` has `Fibonacci8`, `Fibonacci32`, `Fibonacci32Inductive`, `KeccakInductive`, `BLAKE3/`, `Addition8`. The largest non-crypto example tops out at 25-state Keccak. SP1 chips are at 33–247 columns with cross-chip interactions; nothing in Clean exercises that scale yet.
3. **Plonky3 backend is POC.** `backends/plonky3/readme.md:3`: "NOT-PRODUCTION-READY POC!". Production export — the headline downstream gain — is on the roadmap (`README.md:63-64`) but not landed.
4. **`circuit_norm` vs this repo's elaboration pressure.** This repo already runs with `--tstack=400000`, `synthInstance.maxHeartbeats = 1000000` (per `CLAUDE.md`), and per-file `maxHeartbeats` overrides on the heavy chips. Clean's proofs lean on `simp_all only [circuit_norm]` (per `clean/AGENTS.md`); the `circuit_norm` simp set itself spans `Basic.lean:705-773` and is non-trivial. Compounding the two sets in one file may produce surprising performance.
5. **Witness-generator obligation mismatch.** Clean's completeness proofs require the witness generators (`ProverEnvironment.UsesLocalWitnessesCompleteness`, `Basic.lean:175-181`). For chips whose witnesses are computed by the SP1 Rust prover, encoding equivalent generators in Lean is either trivial (most ALU ops) or non-trivial (anything that consumes a memory hint). Worth scoping before committing.
6. **Drift cost.** The `update_constraints.py` cycle is part of routine work in this repo (see `docs/CONSTRAINT_REGEN.md`). Every parallel-rep file is one more thing to keep in sync. Without (b1) codegen extension, a single regeneration breaks every Clean mirror at once.

---

## 7. Adjacent considerations

- **`FormalAssertion` and `GeneralFormalCircuit`** (`Basic.lean:356-366`, `:415-428`, `:470-484`) give us soundness/completeness variants for assertion-only and hint-aware circuits respectively. SP1's `assertZero`-only sub-fragments map naturally to `FormalAssertion`; chips that consume prover hints would need `GeneralFormalCircuit.WithHint`.
- **Subcircuit composition.** Clean's `CoeFun` instance for `FormalCircuit` (`clean/AGENTS.md:103-107`) means a proven gadget is callable like a function inside a parent circuit. SP1's analog — `AddOperation.spec_poly` consumed by `Add.correct_add` — is currently done via lemma application. Clean's composition is type-driven and more ergonomic *if* you've committed to the framework.
- **The blog post (`https://blog.zksecurity.xyz/posts/clean`) explicitly lists** "a formally verified minimal VM for a subset of RISC-V" as planned work alongside hash-function verification and a reusable gadget library. zkSecurity also has an active grant via Verified-zkEVM (`README.md:14`) and an open Telegram channel. Worth opening a conversation before any spike — they may already have prototype code or be open to coordinating.

---

## 8. Recommendation

**Defer use case A.** Cost is high, blockers are real (KoalaBear, Plonky3 maturity, missing gadgets). Revisit when both upstream RISC-V VM work and Plonky3 production support land.

**Conditionally pursue a use case B spike on `AddChip`** if there's appetite to invest ~1 person-week. Success criteria, in order:

1. A `Field (ZMod 2130706433)` instance + the two or three `circuit_norm` interactions needed to keep elaboration tractable.
2. A `Gadgets/CpuState.lean` and `Gadgets/RTypeReader.lean` mirroring `SP1Operations/Reader/CPUState.lean` and `SP1Operations/Reader/RTypeReader.lean` — proven as `FormalCircuit`s.
3. A `Gadgets/Addition64.lean` (extending Clean's existing `Addition32`) or wrapper around it for KB.
4. A file `SP1Chips/Add/CleanCircuit.lean` containing `cleanConstraints` + `clean_iff : (constraints Main).allHold_poly ↔ ConstraintsHold env ((cleanConstraints Main) 0).2`.
5. The `clean_iff` build time is within 2× of the existing `correct_add` build time (per-chip wall-clock budget; see `docs/memory/feedback_build_concurrency.md`).
6. A short writeup of what would change for `BitwiseChip` and `MulChip` — chips at extreme ends of the complexity range.

If 1–5 land, we have evidence the approach scales. If (6) shows the gadget gap is bounded, we can plan a multi-chip rollout. If any of 1–5 stalls beyond budget, we drop the approach and revisit only when upstream Clean changes the cost calculus.

---

## 9. Open questions for upstream / community

1. Is KoalaBear (`p = 2130706433`) on the roadmap for Clean's gadget library and Plonky3 backend?
2. What's the current state of the "minimal RISC-V VM" listed in the blog post? Any prototype branches, design docs, or interested contributors?
3. Does Clean's `Air` (flat) layer (`clean/Clean/Air/`) fit a one-row-per-instruction-chip pattern (matching SP1's chip-per-row convention), or is the `InductiveTable` style preferred?
4. Has anyone exercised Clean's `circuit_norm` on goal states the size of SP1 chips (30+ columns, multi-hundred-line constraint definitions)? Any known performance traps?
5. Would zkSecurity be open to extending `sp1-constraint-compiler` to emit Clean circuits alongside `SP1Constraint` (use case A path) or to a parallel-rep collaboration (use case B path)?

---

## File and section index (for quick re-checking)

Clean references:
- Circuit monad and core ops: `clean/Clean/Circuit/Basic.lean:28-146`
- Soundness / Completeness / FormalCircuit: `clean/Clean/Circuit/Basic.lean:259-303`
- FormalAssertion / GeneralFormalCircuit / WithHint: `clean/Clean/Circuit/Basic.lean:356-484`
- FlatOperation inductive: `clean/Clean/Circuit/Operations.lean:16-20`
- ProvableType class: `clean/Clean/Circuit/Provable.lean:12-37`
- Small AIR example: `clean/Clean/Tables/Fibonacci32Inductive.lean` (46 lines)
- Complex AIR example: `clean/Clean/Tables/KeccakInductive.lean`
- Plonky3 backend status: `clean/backends/plonky3/readme.md`
- Roadmap (RISC-V VM mentioned in §5 implicitly via README + blog post): `clean/README.md:54-90`, https://blog.zksecurity.xyz/posts/clean

SP1-lean references:
- AirInteraction / SP1Constraint: `SP1Foundations/Constraint.lean:9-34`
- toProp_poly / toStateProp_poly / allHold_poly: `SP1Foundations/Constraint.lean:41-121`
- AddChip anchor: `SP1Chips/AddChip.lean:17-95`
- Generated constraints block: `SP1Chips/Add/Constraints.lean:7-24`
- Constraint-compiler workflow: `update_constraints.py`, `docs/CONSTRAINT_REGEN.md`
- Field genericization: `docs/FIELD_GENERIC.md`
- Soundness aggregator: `SP1Chips/Soundness.lean` (812 lines)
