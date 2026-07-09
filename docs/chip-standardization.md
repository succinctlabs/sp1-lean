# Chip standardization — one uniform per-chip contract

**Status (branch `dtumad/clean-upgrade`, 2026-07-08): 21 of 25 instruction chips migrated to the uniform
`ChipKind.advance` obligation; the generic dispatcher and the capstone lift-wiring are landed; full
`sailEquiv`/`reaches_sail` retirement is blocked only on the four decoder-seam chips.**

This doc records the *chip-standardization* effort: the campaign to give every RISC-V chip **one uniform,
semantically-meaningful contract** with the machine-level soundness proof, replacing the per-chip bespoke
Sail-correctness predicates that came before. It was spurred by the semantic-channels program (the state
channel needs each chip to advance a real Sail execution), but it generalized well past that into a single
chip-authoring interface, a faithful per-row effect model, and a generic capstone dispatcher.

Read `architecture.md` first (the four-artifact chain and the layout); this doc is about the *fifth* artifact
that the semantic-channels work added — the per-row **Sail-step** obligation — and how it got standardized.

## 1. The problem it solves

Before this campaign, each chip proved its RISC-V correctness as a **bespoke `sailEquiv`/`reaches_sail`
pair** (`Soundness/ChipRow.lean`): an op-specific statement "the SP1 emulation of this row equals the real
Sail `execute_<op>` run," quantifying that chip's own register/PC/decode preconditions internally. Twenty-five
chips meant twenty-five differently-shaped predicates, and the whole-machine capstone (`Soundness/TargetVm.lean`,
`TargetObligations.lift` — the "one real Sail `try_step` per committed row" seam, roadmap **W7**) had no
uniform way to consume them. `lift` sat as a monolithic black-box hypothesis threaded through the capstone.

The standardization replaces that with **one obligation, the same shape for every chip**:

> In a Sail state `s` that refines this committed row, one real `try_step` produces the row's committed
> `RowEffect` (its PC transition, its ≤1 register write, its ≤1 memory write, and ROM/config preservation).

Every chip discharges *that* — no more per-chip predicate shapes — and a single generic lemma
(`chipRows_advance_sound`) assembles the per-chip proofs into the whole-trace `lift`. Adding or migrating a
chip never touches the capstone.

## 2. Where it came from: the semantic-channels program

The [`semantic_channels_program`](../AGENTS.md#semantic-channels-program) inverted the architecture so the
**interaction-bus channels carry the execution semantics** instead of pure coherence bookkeeping. The pivotal
step (SC Phase 2c, commit `628e7417`) flipped the **State channel** to carry `StateTruth` as its guarantee:
"the deterministic Sail execution of the committed guest program is at this pc at this clk." For that guarantee
to be *maintained* across a trace, every chip row must prove it **advances that Sail execution by exactly one
real step**. That per-chip Sail-step obligation is the thing this campaign standardized and then discharged
chip by chip (SC Phase 3a built the `try_step` reduction machinery; SC Phase 4 is the fan-out).

It generalized past the channel motivation in three ways:

- **A faithful effect model** (§4) — not just "the state advances," but the *three orthogonal axes* of the
  Sail `SequentialState` (regs / mem / PC), which is a reusable RISC-V mental model, not a channel artifact.
- **A uniform chip-authoring interface** (§3) — the `ChipKind` structure-of-functions is now the single place
  a chip registers *everything* the machine layer needs, decoupled from directory/namespace.
- **A generic capstone dispatcher** (§5) — `chipRows_advance_sound` + the `_via_advance` lift-wiring decompose
  the black-box `lift` seam into `advance` (per chip) ∘ three named residuals, independent of the channels.

## 3. The standardized interface: `ChipKind`

`Soundness/ChipRow.lean` defines the structure-of-functions each chip registers exactly once (in
`Chips/<Op>Chip/Bridge.lean`), collected in `Soundness/ChipRegistry.lean` (`allChipKinds`):

| field | meaning |
|---|---|
| `name` | the SP1 `MachineAir::name()` string — the chip's auditable identity (coverage table / registry) |
| `Inputs`, `Cols` | the chip's input + committed-column type maps |
| `view` | the chip-agnostic **bus view** (`Trace.RowView`): shared reader blocks, `is_real`, the rd write value, the opcode, and the committed **`CommitEffect`** (§4) |
| `chipSpec` | the per-row in-circuit contract (the chip's verified `Spec`) |
| `sailEquiv` / `reaches_sail` | the op-specific Sail ≡ SP1-emulation statement + its discharge (the *legacy* per-chip predicate — retained during migration) |
| `advanceReady` | the chip-specific "row is ready to advance" bundle (defaults `True`; each chip overrides with exactly what its `advance` consumes) |
| **`advance`** | **the uniform obligation** — `Option (PLift …)`, `none` until the chip proves it; the one shape §1 describes |

`advance` is `Option`-valued so chips migrate **incrementally**: a `none` chip still works through the legacy
`reaches_sail` path; a `some` chip is covered by the generic dispatcher. `advanceReady` is the honest home for
the trace-well-formedness facts a chip needs beyond refinement + `Spec` — reader pass-through
(`cols = main inp`), the routing invariant (`op_a ≠ 0` for register-writers, `op_a = 0` for the x0 chip, the
active-op flag for multi-op chips), pc-limb bounds, byte-alignment for wide stores, and the ROM/data
disjointness a store introduces. It is the direct analogue of how `sailEquiv` folds a chip's own preconditions
internally — the capstone stays agnostic to a row's arity.

## 4. The two-axis effect model

`advance`'s conclusion is a `RowEffect` (`Soundness/RowEffectDefs.lean`): the committed row transitions the PC
and performs **≤1 register write ⊕ ≤1 contiguous memory write** — the three orthogonal axes of the Sail
`SequentialState` (`regs` / `mem` / PC). The descriptor is `RowView.commit : CommitEffect`
(`Soundness/RowView.lean`):

```
structure MemWrite    where addr : Vector F 3; value : Word F; width : Nat   -- one contiguous store
structure CommitEffect where writesReg : Bool; memWrite : Option (MemWrite F)
  .regWrite  = ⟨true,  none⟩    -- ALU / jump / normal load
  .noWrite   = ⟨false, none⟩    -- Branch / AluX0 / LoadX0
  .store mw  = ⟨false, some mw⟩ -- Store
```

**Why two axes, not one unified content.** Sail genuinely splits `regs` (64-bit atomic) from `mem`
(byte-addressed), and a sub-word store mutates one byte of an 8-byte word — byte-addressed replay
(`memReplayVal`, the byte twin of `replayVal`) maps one-to-one onto Sail's `writeBytes`, whereas a unified
64-bit `MemLoc` fold would fight sub-word stores. Registers-are-addresses stays in the *bus* layer (where SP1
is unified); the *refinement* layer bridges down to Sail's split state. Chosen for long-term viability — a
hypothetical reg+mem AMO falls out for free — and it aligns with the bus vocabulary (`writesReg` is exactly
the `opAEvent.is_write` the Memory bus already wanted).

**The mechanism that kept the 14 already-proven chips byte-identical:** the gated clauses
(`RowEffect.regs = if commit.writesReg then … else all-frame`, `RowEffect.mem = match commit.memWrite …`)
whnf-reduce definitionally for the `.regWrite`/`.noWrite`/`.store` literals, and the shared cores gained the
new gate facts as **`:= by rfl` auto-params** — so no register-writing chip's adapter changed when the memory
axis landed.

## 5. The generic machinery

Three layers, all in `Proofs/Sail/Advance.lean`, `Model/Semantics/Decode.lean`, and `Soundness/`:

- **Shared `advance` cores** — the reusable ladder proofs each chip family plugs into: `advance_write_core`
  (straight-line register write), `advance_jump_core` (computed next_pc + write), `advance_of_ctrl` (no-write
  computed next_pc — Branch), `advance_load_core` (memory-read register-write), `advance_of_store`
  (width-general memory write), `advance_alu_x0_core` (no-write straight-line ALU into x0). Each is proved
  once over the ladder (`sailStep_of_ladder` / `tail_effect`) and applied symbolically; the per-chip adapter
  is a thin call.
- **The decode layer** — `decodedInROM` *supplies* the `ext_decode w = i` fact as the Program-bus assumption
  (`ProgTruth`), and per-family producers (`decodesRType`/`decodesIType`/`decodesLoad`/`decodesStore`/… ,
  each mirroring `decodesDiv`) invert `instrToProgramRow` by `split` + `opcodeCast_inj` to pin the
  instruction — **never unfolding the ~29K-line `encdec_backwards`** (that's the key discipline; see §6).
  `execute_<op>_reaches` lemmas re-express each Sail `execute` as the ladder's `hexec` shape.
- **The dispatcher + capstone wiring** — `chipRows_advance_sound` (`Soundness/AdvanceDispatch.lean`) routes
  each walk position to its chip's `advance` by multiset membership (no per-chip `cases`), and
  `targetObligations_full{,_of_balance}_via_advance` (`Soundness/ValueBound.lean`) wire it in as the
  `TargetObligations.lift` provider. The monolithic W7 black box is now **`advance` (per chip) ∘ three
  clearly-named residuals**: `h_migrated` (coverage — every real row's chip has `advance.isSome`), `h_decode`
  (the ProgTruth fetch truth), `h_ready` (`advanceReady` routing).

## 6. Progress

**Migrated (21 / 25 instruction chips), all axiom-clean** (`[propext, Classical.choice, Quot.sound]` + the
accepted Sail platform base; `bv_decide` adds `ofReduceBool`/`trustCompiler` on the store/byte-extraction
decls; no `sorryAx`, no `native_decide`):

Add, Addi, Addw, Sub, Subw, Bitwise, Lt, UType, Jal, Jalr, ShiftLeft, ShiftRight, DivRem (8-way), Branch,
LoadByte/Half/Word, StoreByte/Half/Word, AluX0 (27 of its 29 dispatched opcodes).

**The arc** (SC Phase 0 → 4, ~70 commits): the pilot (Add, over `advance_write_core`) → the R-type / I-type /
multi-op / W-op / U-type / jump / shift / DivRem fan-out (Phase 1–2) → the two-axis effect model and the
memory axis (Phase 3a register gate + Branch; Phase 3b loads then stores) → AluX0 → the endgame lift-wiring.

**The endgame is structurally done.** `lift` is no longer a black box — it is the per-chip `advance`
(proved and axiom-clean, per chip) composed with the three named residuals. What remains for *full*
`sailEquiv`/`reaches_sail` retirement is universal `h_migrated` coverage, i.e. the last four chips.

## 7. The deferred boundary — one root cause

Four instruction chips stay `advance = none`, plus two AluX0 opcodes, **all for the same reason: the
committed opcode does not injectively pin the decoded instruction, and pinning it would require an
`ext_decode` output-determinism fact that only follows from the intractable ~29K-line `encdec_backwards`
symbolic trace** (documented "not pursued" in the Sail decode notes; `decodedInROM` stays a trusted
assumption at that boundary):

- **Mul (register)** — `MULHSU`'s `mul_op` is genuinely ambiguous (two records map to the opcode), so the
  register value can't be pinned. See [`agents/mul-operation-learnings.md`](agents/mul-operation-learnings.md).
- **LoadDouble / LoadX0 / StoreDouble** — the width-8 `load`/`store` opcode is the non-injective `else` of
  `loadOpcode`/`storeOpcode`; a width-pin hypothesis is provably false without the width fact from
  `encdec_backwards`.
- **MUL(11) & MULHSU(14) into x0 (AluX0 27/29)** — `mulOpToOpcode` maps `.Low, _, _ => .MUL` (four preimages)
  and MULHSU 2-to-1, so those two opcodes can't pin the `mul_op` uniformly across the ladder's states without
  output-determinism. The value is *discarded* at x0, but `advance_alu_x0_core` still needs a **fixed** decoded
  instruction `I` with `∀ sc, ext_decode w = I`. MULH/MULHU (injective) and MULW (no op) close cleanly; these
  two don't. The generic `advance_of_alu_x0_mul` / `decodesMul` are parameterized over `op` + a pin
  hypothesis, so both close *immediately* once a determinism lemma exists.

This is a deliberate, honest deferral — not a gap to be papered over. It is the same boundary the trusted
`decodedInROM` assumption already sits behind.

## Cross-references

- `SP1Clean/Soundness/ChipRow.lean` — the `ChipKind` interface (the standardization target).
- `SP1Clean/Soundness/RowView.lean`, `RowEffectDefs.lean` — the two-axis effect model.
- `SP1Clean/Proofs/Sail/Advance.lean` — the shared `advance` cores + `execute_<op>_reaches`.
- `SP1Clean/Model/Semantics/Decode.lean` — `decodedInROM` + the `decodes<Op>` producers.
- `SP1Clean/Soundness/AdvanceDispatch.lean` — `chipRows_advance_sound` (the generic dispatcher).
- `SP1Clean/Soundness/ValueBound.lean` — `targetObligations_full{,_of_balance}_via_advance` (the lift-wiring).
- `SP1Clean/Soundness/TargetVm.lean` — `TargetObligations` / `lift` (the W7 seam this discharges).
- `docs/roadmap.md` (W7 / the semantic-channels section), `docs/bus-model.md`, `AGENTS.md`
  ("semantic-channels program").
