# SP1Clean — Overview & current state

Friendly tour of what `SP1Clean/` is, why it exists alongside `SP1Chips/` and `SP1Operations/`, what's built today, and how the pieces compose. The companion `docs/CLEAN_FUTURE.md` covers open work and forward roadmap.

## What SP1Clean is

`SP1Clean/` is a parallel formalization of every SP1 instruction chip, written in the **Clean DSL** ([Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean), cloned at `../clean`). It does not replace anything in `SP1Chips/` or `SP1Operations/` — both libraries build, both pass, and SP1's `correct_*` Sail-equivalence theorems still flow through the original constraint-compiler output. SP1Clean sits next to them, exporting the same chip as a Clean `FormalAssertion` bundle and bridging back to SP1 via per-chip `iff_sp1` lemmas.

The pilot exists to give the constraint layer a better long-term home — catching soundness/completeness bugs, exporting to a real prover (Plonky3), and separating "the spec of what this chip does" from "the column layout SP1 happens to emit."

`lake build SP1Clean` is green: 0 errors, 0 warnings, 0 active `sorry`s in the core promotion path (two outstanding sorries documented in `MULTIPLICITY_BUS.md` for the multiplicity-bus refactor only).

## What "existing formalization" means in this repo

Every SP1 instruction follows the same three-step recipe:

```
SP1Chips/<Chip>/Constraints.lean    -- auto-generated constraint list
  ↓
SP1Chips/<Chip>Chip.lean            -- spec_<op> / sp1_<op> / correct_<op>
  ↑                                    (calls into Sail via SailM)
SP1Operations/Operation/<Op>.lean   -- reusable arithmetic fragments
SP1Operations/Reader/<Reader>.lean  -- decoder fragments (R-type, I-type, …)
```

The chip's `constraints` function is a `Vector (Fin KB) N → SP1ConstraintList`. It's a flat list of `assertZero` / `send` / `receive` items, one per logical AIR constraint. The compiler emits it; we don't hand-edit between the markers; `correct_*` proves that when those constraints hold, the chip behaves identically to the Sail RISC-V semantics. Every chip has a `correct_*` theorem. The proofs are sometimes hard — DivRem and ShiftLeft needed weeks of `_poly` restructuring — but the pattern is mechanical and the scaffolding is well understood. **Nothing in the Clean pilot changes any of this.**

## What SP1Clean adds

Three ingredients matter:

**1. Structured columns instead of flat indices.** SP1's `Main[k]` indexing is a flat 33-element vector for `AddChip`. SP1Clean defines an `AddCols` record with named fields — `op_a`, `op_b_memory_prev_value`, `pc : Vector _ 3`, etc. — and writes the chip's `Spec` over that record. A `fromMain : Vector (ZMod p) 33 → AddCols (ZMod p)` projects raw indices into the structured view exactly once, at the bridge layer. After that, no proof ever mentions `Main[28]` again.

**2. A pair of theorems instead of one.** SP1's `correct_*` says "if the constraints hold, the chip matches Sail" — soundness only. Clean's `FormalAssertion` bundles soundness *and completeness* — a proof that for every input satisfying the chip's `Spec`, you can write witnesses such that the constraints hold. Without completeness, a chip could be vacuous (over-constrained, never satisfiable) and `correct_*` would still pass. SP1's existing approach doesn't surface completeness as a separate lemma; Clean makes it a first-class theorem with its own proof obligation.

**3. A composable interaction layer.** SP1 has four interaction kinds (`byte`, `state`, `memory`, `program`) modeled as `AirInteraction` constructors with multiplicities tracked declaratively. SP1Clean uses `lookup`-against-`Table` (stateless lookups for byte/state/program) and a multiplicity-aware bus (`SP1Clean/SP1Lookup.lean`, `SP1Clean/Multiplicity.lean`) that mirrors SP1's `InteractionKind`-tagged model. Memory interactions are aggregated *trace-level* through `Clean.Utils.OfflineMemory`, which handles the timestamp-ordering discipline that SP1's per-row sends can't enforce locally. Per-row soundness says nothing about cross-row consistency; the Clean side gives a machine-checked aggregator that turns per-row claims into a trace-level "every memory access is consistent" property, discharged once at the library level.

## The three proof layers

| Layer | What it proves | Where |
|---|---|---|
| **Dirty** `correct_*` | AIR constraints `allHold` + Sail state link ⇒ `spec_X.run s = sp1_X.run s` (per-row Sail equivalence) | `SP1Chips/<Chip>Chip.lean` |
| **Clean** `FormalAssertion` | constraints ↔ chip-row `Spec` (soundness `⇒` and completeness `⇐`) | `SP1Clean/<Chip>Chip.lean` |
| **Trace** | aggregator over `ChipRow` + trace-shape bundles ⇒ offline memory consistency + state-bus PC chain | `SP1Clean/Soundness/*` |

The dirty layer is the original repo's deliverable. The Clean layer reformulates that proof inside the Clean DSL, giving an `iff`-shaped chip-row predicate ready for compositional trace-level reasoning. The trace layer wires per-chip predicates into a single trace-level soundness statement via the upstream `Clean.Utils.OfflineMemory` consistency theorem and a PC-chain aggregator.

## Per-chip status (24 chips)

Counts here are reproducible:
```
grep -c "^theorem correct_\|^theorem correct\b" SP1Chips/<Chip>Chip.lean
grep -c "def assertion : FormalAssertion" SP1Clean/<Chip>Chip.lean
grep -nE "^\s+| <Chip> " SP1Clean/Soundness/MemoryConsistency.lean
```

| Chip | Dirty `correct_*` | Clean FormalAssertion (S+C) | `ChipRow` registered |
|---|---|---|---|
| Add | ✅ 1 thm | ✅ | ✅ |
| Addi | ✅ 1 | ✅ | ✅ |
| Addw | ✅ 2 | ✅ | ✅ |
| Bitwise | ✅ 6 | ✅ | ✅ |
| Branch | ✅ 6 | ✅ | ✅ |
| DivRem | ✅ 8 | ✅ | ✅ |
| Jal | ✅ 1 | ✅ | ✅ |
| Jalr | ✅ 1 | ✅ | ✅ |
| LoadByte | ✅ 2 | ✅ | ✅ |
| LoadDouble | ✅ 1 | ✅ | ✅ |
| LoadHalf | ✅ 2 | ✅ | ✅ |
| LoadWord | ✅ 2 | ✅ | ✅ |
| LoadX0 | ✅ 7 | ✅ | ✅ |
| Lt | ✅ 4 | ✅ | ✅ |
| Mul | ✅ 5 | ✅ | ✅ |
| ShiftLeft | ✅ 4 | ✅ | ✅ |
| ShiftRight | ✅ 8 | ✅ | ✅ |
| StoreByte | ✅ 1 | ✅ | ✅ |
| StoreDouble | ✅ 1 | ✅ | ✅ |
| StoreHalf | ✅ 1 | ✅ | ✅ |
| StoreWord | ✅ 1 | ✅ | ✅ |
| Sub | ✅ 1 | ✅ | ✅ |
| Subw | ✅ 1 | ✅ | ✅ |
| UType | ✅ 2 | ✅ | ✅ |

**Aggregate counts:**
- Dirty `correct_*`: **24 / 24** proven (zero active sorries; inert `sorry`-mentioning comments at `SP1Chips/ShiftRight/Sra.lean:31` and `SP1Chips/DivRem/DivRem.lean:814` only).
- Clean `FormalAssertion` (S+C, sorry-free in the core path): **24 / 24** — every chip carries a top-level `FormalAssertion` with `theorem soundness` and `theorem completeness`. The five originally "heavy-operation" chips (Branch, DivRem, Mul, ShiftLeft, ShiftRight) landed via Path-2 against their `main`'s surface gates — operation-specific content stays in legacy `Spec` and is consumed via the chip pipeline. ShiftLeft drops 10 Vector-indexed `bit_shift`/`byte_shift` gates from its `FormalSpec` for the `Expression.eval` indexed-access reason documented in `MULTIPLICITY_BUS.md`.
- `ChipRow` registered (in trace aggregator): **24 / 24** — wired in `SP1Clean/Soundness/MemoryConsistency.lean` (constructors + `memoryAccesses` / `clockComponents` / `Spec` / `offsets` cases) and `SP1Clean/Soundness/StateConsistency.lean` (`stateAccess` cases).

## Trace-level scaffolding

These modules build clean (`lake build SP1Clean.Soundness` = 8616 jobs, 0/0 errors/warnings) and the end-to-end statement's axiom audit shows only `propext`, `Classical.choice`, `Quot.sound`:

| Module | Purpose | Key exports |
|---|---|---|
| `SP1Clean/Soundness/MemoryConsistency.lean` | Memory bus aggregator + offline bridge | `aggregateMemoryAccesses`, `ChipRow.rowAccessTuples`, `chip_specs_admit_offline_bridge` |
| `SP1Clean/Soundness/MemoryConsistencyClock.lean` | Timestamp-sort + nodup derivations | `TraceClkValid`, `aggregateMemoryAccesses_isTimestampSorted`, `aggregateMemoryAccesses_Notimestampdup` |
| `SP1Clean/Soundness/StateConsistency.lean` | State-bus (PC chain) aggregator | `ChipRow.stateAccess`, `aggregateStateAccesses`, `pcChainProp`, `TraceStateValid` |
| `SP1Clean/Soundness/IsRealBinary.lean` | `is_real ∈ {0,1}` surfacing | `binary_of_assertZero`, `TraceIsRealBinary` |
| `SP1Clean/Multiplicity.lean` | Multiplicity-gating lemmas | `ByteOpcode_send_iff_constrain`, `Program_send_iff_clause`, `Memory_send_iff_isU64` |
| `SP1Clean/Soundness/TraceSoundness.lean` | End-to-end statement | `trace_soundness_aggregateMemory`, `trace_soundness_with_boundary` |
| `SP1Clean/Soundness.lean` | Umbrella re-export | — |

Boundary chips (`MemoryGlobalChip.lean`) ship two `ChipRow` constructors (`.memInit`, `.memFinalize`) with placeholder `memoryAccesses = []`; full bus closure is the Phase 4.5 follow-up documented in `CLEAN_FUTURE.md`.

Upstream `Clean.Utils.OfflineMemory` required 3 Lean 4.29 simp regressions patched in the sibling repo (added `Decidable (timestamp_ordering …)` instance; tightened two examples; added `split_ifs <;> rfl` on the `filterAddress_cons` lemma).

## The bridge: how SP1Clean and SP1Chips stay in sync

SP1Clean isn't a fork. It imports the SP1 side directly and reuses its lemmas. Every promoted chip's bridge follows the same pattern:

```lean
-- SP1Clean/AddChip.lean (Layer 2, ~50 lines)
theorem iff_sp1 (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold ↔ Spec (fromMain Main) := by
  simp only [fromMain, Spec, ...]
  rw [...]   -- unpack the constraint list
  rw [AddOperation.allHold_constraints_iff a b cols]   -- ← SP1 lemma reused
  rw [cpuStateSpec_iff_sp1, rtypeReaderSpec_iff_sp1]   -- ← subbridges
  -- close arithmetic
```

`AddOperation.allHold_constraints_iff` is **the SP1-side lemma** — proved once in `SP1Operations/Operation/AddOperation.lean`, never re-proved in SP1Clean. The Clean side just re-expresses the same statement in terms of a record-valued `Spec` and calls back into the existing proof. This is the "three-layer bridging" discipline:

- **Layer 0** — SP1's `_poly` lemmas (the genuinely hard arithmetic proofs for DivRem, ShiftLeft, Mul). **Never duplicated.** Clean reuses them.
- **Layer 1** — operation-level `iff_sp1` in SP1Clean. Thin re-exports; usually 5–15 lines.
- **Layer 2** — chip-level `iff_sp1`. Composes Layer 1 + readers.
- **Layer 3** — `FormalAssertion.soundness` / `completeness`. Wraps the bridge into Clean's standard interface.

The DivRem 5-layer helper architecture, the ShiftLeft bit-decomposition tower, the MulOperation 16-limb carry chain — all of those live in SP1 and are reused as-is. Clean only adds the structural plumbing around them.

## Faithful sub-circuit composition

A first-class invariant: SP1Clean files must structurally mirror the SP1 constraint composition graph. The full statement lives in the repo-root `CLAUDE.md` §"Faithful sub-circuit composition". One-line summary:

> Each `SP1Clean/Operations/<Op>.lean` and `SP1Clean/<Chip>Chip/Circuit.lean` exposes exactly one `main` and one `Spec`, composes sub-operations as `FormalAssertion` subcircuits (never inlining sub-constraints), and references sub-Specs by direct field application (never via `List.Forall SP1Constraint.toProp ...` envelopes).

Concretely:
- ✅ `SP1Clean.AddwOp.main` calls `SP1Clean.U16MSBOp.assertion` as a subcircuit; `AddwOp.Spec` composes `U16MSBOp.Assertion.Spec` directly.
- ✅ `SP1Clean.AddChip.main` composes `RTypeReader.assertion`; `AddwChip.main` composes `ALUTypeReader.assertion`.
- ❌ Avoid: chip-level `main` that inlines byte lookups when a reader-level `OperandAccess.assertion` exists.
- ❌ Avoid: `Spec` defined with `List.Forall SP1Constraint.toProp (<Sub>.constraints …)` when a `<Sub>.Assertion.Spec` is available.
- ❌ Avoid: `InlinedSpec` / `inlinedSpec_iff_spec` bridging helpers. They exist only when `main` and `Spec` were defined in mismatched forms; the fix is to align them, not paper over the mismatch.

The canonical ALU-chip Layer-0/Layer-2 shape is the one used in `SP1Clean/AddChip/Common.lean` — both sides of the iff in `.allHold` form (not `List.Forall SP1Constraint.toProp`), so the matching SP1Clean Layer-2 `allHold_iff_structural` (see `SP1Clean/AddChip/Lemmas.lean`) collapses to a flat `rw` chain. Existing chip Commons that still use the older `List.Forall` form are migrated opportunistically.

## Canonical pattern reference

The reference baseline for every SP1Clean chip is `AddChip` + `AddOp`, anchored at commits `b82c79e` + `a8e50fb`. Read these end-to-end alongside `SP1Chips/AddChip.lean` and `SP1Chips/Add/Constraints.lean` — that's the smallest non-trivial side-by-side that shows every layer:

- `SP1Clean/AddChip/Cols.lean` — `AddCols` record + `FormalSpec` (the canonical Spec semantic-purity shape: `... ∧ (is_real = 1 → isU64 result ∧ RV64.<op>-equation)`).
- `SP1Clean/AddChip/Circuit.lean` — `main : Var Inputs → Circuit Unit` composing `CPUState.Gated.assertion` + `RTypeReader.Gated.assertion`.
- `SP1Clean/AddChip/Lemmas.lean` — Layer-2 `allHold_iff_structural` flat-`rw` bridge to SP1's `allHold`.
- `SP1Clean/AddChip/SailBridge.lean` — axiom-clean `sail_correct_of_formalSpec` (single declaration; `{propext, Classical.choice, Quot.sound}`).
- `SP1Clean/Operations/AddOperation.lean` — operation-level `main` / `Spec` / `iff_sp1`.

The full **operation contract template** (multiplicity gating + reader composition + `Gated.assertion` wrappers) lives in `MULTIPLICITY_BUS.md#operation-contract-template-canonical-pattern-from-commit-b82c79e--this-pr`.

## Where to dig deeper

- **`docs/MULTIPLICITY_BUS.md`** — the multiplicity-aware lookup bus (`SP1Clean/SP1Lookup.lean`). Mirrors SP1's `AirInteraction<E>` from `sp1/crates/core/machine/src/air/memory.rs` (`InteractionKind`-tagged buses, `lookupGated` primitive with hint-witness completeness, parallel `LookupAccessList` aggregator). Phase 1+2 foundation landed and verified axiom-clean. Hand-off doc for the two remaining `sorry`s at `SP1Clean/AddwChip/Circuit.lean:152` and `SP1Clean/Soundness/MemoryConsistency.lean:1067`.
- **`docs/STRUCT_DIVERGENCE.md`** — field-level snapshot of how SP1Clean column structs and SP1Operations structs have drifted from upstream Rust (`../sp1`). Per-chip constraint-usage tables, macro divergences, coverage gaps (privilege/trap, paging, syscalls, lookup tables).
- **`docs/CLEAN_FUTURE.md`** — open work: per-chip sorry register, phased roadmap (Phase-A gating combinator, Phase-B heavy ops, Phase-C reader promotion, Phase-D write-back tooling), durable lessons from iter retros.
- **The SP1Clean files themselves** — `SP1Clean/AddChip/` is the canonical full Path-1 example. `SP1Clean/AddwChip.lean` is the canonical Path-2 example. `SP1Clean/Operations/AddOperation.lean` is the deepest operation promotion.

## Axiom audit

End-to-end statement (`trace_soundness_aggregateMemory` and `trace_soundness_with_boundary` in `SP1Clean/Soundness/TraceSoundness.lean`) shows only the three classical axioms `propext`, `Classical.choice`, `Quot.sound` — same as the chip-level FormalAssertions and their Sail bridges. No `sorryAx`, no Sail axiomatization beyond `LeanRV64D`'s baseline.
