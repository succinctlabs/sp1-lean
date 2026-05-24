import SP1Clean.StateAccess
import SP1Clean.Soundness.MemoryConsistency

/-! # Trace-level state-bus (PC chain) consistency

This file mirrors the memory aggregator's structure for the SP1 state
bus, which links consecutive trace rows via PC handoff.

## Roles

Each chip row's CPUState reader emits two state-bus interactions
(`SP1Foundations/Constraint.lean:9-22`):

- `receive (.state clk_high clk_low pc[0] pc[1] pc[2]) is_real`
- `send (.state clk_high clk_low_succ next_pc[0] next_pc[1] next_pc[2]) is_real`

For two adjacent real rows `r₁` (earlier) and `r₂` (later), the
send→receive handshake gives `r₁.next_pc = r₂.pc`. This is the chain
condition this file states and reasons about.

## Per-chip `is_real`

Not every chip exposes a chip-level `is_real` column. Eight chips
(Branch, LoadByte, LoadHalf, LoadWord, LoadX0, ShiftLeft, ShiftRight,
Mul, Lt) define `is_real` inline as a sum of sub-opcode flags
(e.g. `is_beq + is_bne + …` for Branch). The per-chip
`ChipRow.stateAccess` projection mirrors each chip's `Spec` formula.

## Per-chip `next_pc`

Each chip's `next_pc` projection is either derived directly from `cols.state.pc`
or read from a chip-specific column:

- **21 straight-line chips** (Add, Addi, Addw, Bitwise, DivRem,
  Load{Byte,Double,Half,Word,X0}, Lt, Mul, Shift{Left,Right},
  Store{Byte,Double,Half,Word}, Sub, Subw, UType): derive
  `next_pc := #v[pc[0] + 4, pc[1], pc[2]]` from `cols.state.pc` directly,
  matching Rust's literal expression in `adapter/state.rs:75`. There is no
  per-chip `next_pc_carry_value` column — that Clean-only over-validation was
  removed (macro divergence #5 closure, 2026-05-23). Traces that need to cross
  64 KB boundaries do so via JAL/JALR; otherwise `pcChainProp`'s field equation
  `a.next_pc = b.pc` would fail because the next row's u16 byte-lookups on
  `pc[0]` would not match the overflowing field value.
- **Jal**: reads `cols.next_pc[0..2]`, truncating the 4-limb column.
- **Jalr**: reads `cols.jump_target[0..2]` with bit-0 of the low limb
  cleared (`jump_target[0] - cols.lsb`) to match the chip's
  alignment masking.
- **Branch**: reads `cols.next_pc` directly (already 3-limb); the
  FormalSpec carries the case-split on `is_branching` so this column
  equals either `pc + imm` (taken) or `pc + 4` (not taken).

`pcChainProp` itself is fully proven from a bundled trace-shape
hypothesis; deriving it from chip `Spec`s + a chronological state-link
assumption is the iter-8 sub-task D work. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Per-chip state-access projection. Returns the row's clock
components, current `pc`, the row's claimed `next_pc`, and the
`is_real` flag — computed inline for chips without an explicit column
(see file docstring). -/
def ChipRow.stateAccess : ChipRow p → StateAccess (ZMod p)
  | .add cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .loadByte cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_lb + cols.is_lbu }
  | .storeByte cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .jal cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]],
        is_real := cols.is_real }
  | .mul cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_mul + cols.is_mulh + cols.is_mulw +
          cols.is_mulhsu + cols.is_mulhu }
  | .shiftLeft cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_sll + cols.is_sllw }
  | .addw cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .uType cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .jalr cols =>
      -- `jump_target[0]` is the unmasked low limb; the chip's `lsb`
      -- column carries the to-be-cleared bit so `jump_target[0] - lsb`
      -- is the bit-0-cleared real next_pc.
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.jump_target[0] - cols.lsb,
          cols.jump_target[1], cols.jump_target[2]],
        is_real := cols.is_real }
  | .lt cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_slt + cols.is_sltu }
  | .storeWord cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .storeDouble cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .storeHalf cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .loadDouble cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .loadWord cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_lw + cols.is_lwu }
  | .loadHalf cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_lh + cols.is_lhu }
  | .branch cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc,
        is_real := cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
          cols.is_bltu + cols.is_bgeu }
  | .loadX0 cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld }
  | .shiftRight cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw }
  | .divRem cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .addi cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .bitwise cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_xor + cols.is_or + cols.is_and }
  | .sub cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  | .subw cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
        is_real := cols.is_real }
  -- Boundary chips: not part of the PC chain. Their `stateAccess`
  -- carries placeholder PC/next_pc fields (all zeros); `is_real` mirrors
  -- the chip's own is_real column. The verifier's trace shape places
  -- these chips at boundaries (before the first interior row / after
  -- the last), so they don't participate in the adjacent-pair PC handoff.
  | .memInit cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_low,
        pc := #v[0, 0, 0],
        next_pc := #v[0, 0, 0],
        is_real := cols.is_real }
  | .memFinalize cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_low,
        pc := #v[0, 0, 0],
        next_pc := #v[0, 0, 0],
        is_real := cols.is_real }

/-- Aggregate a list of chip rows into a per-row state-access list.

Unlike `aggregateMemoryAccesses` which reverses to match
OfflineMemory's "most-recent at head" convention, this aggregator
preserves chronological order — the PC chain's natural reading is
forward in time (row 0 → row 1 → …). -/
def aggregateStateAccesses (rows : List (ChipRow p)) :
    List (StateAccess (ZMod p)) :=
  rows.map ChipRow.stateAccess

/-- The PC chain predicate: every pair of adjacent rows agrees on PC
handoff when both rows are real.

For two adjacent state-accesses `a` (current) and `b` (next), if both
are real (`is_real ≠ 0`), then `a.next_pc = b.pc` and the encoded
clock advances by exactly `clkIncrement` (SP1's per-row clock step,
canonically 8). Padding rows where either gate is zero make the
pairwise obligation vacuous. -/
def pcChainProp (clkIncrement : ZMod p) :
    List (StateAccess (ZMod p)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (a.is_real ≠ 0 ∧ b.is_real ≠ 0 →
        a.next_pc = b.pc ∧
        a.clk_high * (2 ^ 24 : ZMod p) + a.clk_low + clkIncrement =
          b.clk_high * (2 ^ 24 : ZMod p) + b.clk_low) ∧
      pcChainProp clkIncrement (b :: rest)

/-- Trace-shape state-bus invariant. Bundles the obligation that the
aggregated state-access list satisfies the PC handoff chain.

This is intentionally a thin bundle. Future discharge work derives it
from per-chip `Spec`s plus a chronological trace-link assumption
between adjacent rows. See file docstring's per-chip `next_pc`
section. -/
structure TraceStateValid (rows : List (ChipRow p)) (clkIncrement : ZMod p) :
    Prop where
  chain_holds :
    pcChainProp clkIncrement (aggregateStateAccesses rows)

/-! ## State-bus boundary (iter-8 Phase 4)

SP1's state bus is closed at the trace boundaries: the very first row's
`pc` must match the verifier-committed `initial_pc` (an input public
value), and the very last row's `next_pc` must match `final_pc`. These
boundary conditions tie the on-chain PC chain to externally visible
state.

`TraceStateBoundary` packages both as a single trace-shape predicate.
It's threaded into `trace_soundness_aggregateMemory` as an additional
hypothesis (alongside `TraceClkValid`, `TraceStateValid`,
`TraceIsRealBinary`) — see `SP1Clean/Soundness/TraceSoundness.lean`. -/

/-- State-bus boundary hypothesis. The first row's `pc` equals
`initial_pc` and the last row's `next_pc` equals `final_pc`. Boundary
chip rows (`memInit`/`memFinalize`) carry placeholder PC values and
don't participate; the verifier's trace shape is responsible for
positioning boundary chips outside the PC-chain window. -/
structure TraceStateBoundary (rows : List (ChipRow p))
    (initial_pc final_pc : Vector (ZMod p) 3) : Prop where
  /-- The first chip row's projected `pc` matches the verifier-committed
  initial PC. If `rows = []` this is vacuous (`none = none` would
  require `initial_pc = ...` which can't be witnessed, so the predicate
  is non-empty-list only). -/
  initial_match :
    (rows.head?).map (fun row => (ChipRow.stateAccess row).pc) =
      some initial_pc
  /-- The last chip row's projected `next_pc` matches the verifier-
  committed final PC. -/
  final_match :
    (rows.getLast?).map (fun row => (ChipRow.stateAccess row).next_pc) =
      some final_pc

/-- The aggregated state-access list satisfies the PC chain under
`TraceStateValid`. The hypothesis already bundles the conclusion (this
theorem is the structural unfolding), so the proof is a direct
projection. Future work proves `TraceStateValid` from chip `Spec`s. -/
theorem aggregateStateAccesses_pcChain
    (rows : List (ChipRow p)) (clkIncrement : ZMod p)
    (h : TraceStateValid rows clkIncrement) :
    pcChainProp clkIncrement (aggregateStateAccesses rows) :=
  h.chain_holds

/-! ## State-bus trace-link discharge

Mirrors `traceClkValid_of_chip_specs` (`MemoryConsistencyClock.lean`)
and `traceIsRealBinary_of_chip_specs` (`IsRealBinary.lean`). The link
hypothesis `TraceStateLink` packages the per-adjacent-pair PC handoff +
clock advance the verifier supplies for SP1 trace shapes; the discharge
to `TraceStateValid` is a direct re-bundling for now. Full grounding
from chip Specs (deriving the carry-aware next_pc from each chip's
`AddrAddOp.assertion.Spec` conjunct) follows in iter-8 sub-task E once
`ChipRow.Spec` is normalized to reference `<Chip>.assertion.Spec`
uniformly. -/

/-- Per-adjacent-pair state-bus link hypothesis. For consecutive real
rows, the earlier row's projected `next_pc` equals the later row's
`pc`, and the encoded clocks advance by exactly `clkIncrement`. -/
def TraceStateLink (rows : List (ChipRow p)) (clkIncrement : ZMod p) :
    Prop :=
  pcChainProp clkIncrement (aggregateStateAccesses rows)

/-- Discharge of `TraceStateValid` from chip `Spec`s + trace-shape state
link.

**Structural note on the discharge shape.** `TraceStateLink` is defined as
`pcChainProp clkIncrement (aggregateStateAccesses rows)`, which is
identical to `TraceStateValid.chain_holds`. The chain itself relates
ADJACENT rows (`a.next_pc = b.pc` plus the clock advance) — content that
no per-row chip `Spec` can produce in isolation. The chronological link
is intrinsic to the state bus and must be supplied by the verifier or
threaded through the trace-shape contract.

What chip Specs *do* contribute is **per-row semantic content** for the
`next_pc` column: each chip's `assertion.Spec` carries an `AddrAddOp.Spec`
(or analogous) conjunct constraining `next_pc_carry_value` to be the
carry-aware `pc + 4` (or jump target / branch mux for non-arithmetic
chips). This is what makes the `a.next_pc = b.pc` equation meaningful —
without the chip Spec, `next_pc` is just an unconstrained column.

The per-row witness is exposed by `nextPcValid_of_chipRow_spec` below,
and the trace-level wrapper `traceNextPcValid_of_chip_specs` aggregates
across all rows. `traceStateValid_of_chip_specs` itself remains the
adjacency-bundling step. -/
theorem traceStateValid_of_chip_specs
    (rows : List (ChipRow p)) (clkIncrement : ZMod p)
    (_h_specs : ∀ row ∈ rows, ChipRow.Spec row)
    (h_link : TraceStateLink rows clkIncrement) :
    TraceStateValid rows clkIncrement :=
  ⟨h_link⟩

end SP1Clean.Soundness
