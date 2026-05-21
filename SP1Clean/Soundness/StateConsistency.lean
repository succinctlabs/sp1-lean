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

For chips with an explicit `next_pc` (or `jump_target`) column —
Jal, Jalr, Branch — the projection reads that column (truncating to
3 limbs for 4-limb columns). For all other chips the `next_pc` is
the placeholder `pc + #v[4, 0, 0]` (element-wise, no carry handling).
The placeholder is correct precisely when the chip's underlying
`pc + 4` carries are zero, which is the trace shape's normal case
but can fail at chip boundaries; the discharge work for
`TraceStateValid` from chip `Spec`s — analogous to `TraceClkValid`
discharge in `MemoryConsistencyClock.lean` — fully resolves the
placeholder semantics.

`pcChainProp` itself is fully proven from a bundled trace-shape
hypothesis; the obligation to *discharge* the hypothesis from chip
`Spec`s + a chronological trace-link assumption is the deferred work. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Per-chip state-access projection. Returns the row's clock
components, current `pc`, the row's claimed `next_pc`, and the
`is_real` flag — computed inline for chips without an explicit column
(see file docstring). -/
def ChipRow.stateAccess : ChipRow p → StateAccess (ZMod p)
  | .add cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .loadByte cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_lb + cols.is_lbu }
  | .storeByte cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .jal cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]],
        is_real := cols.is_real }
  | .mul cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_mul + cols.is_mulh + cols.is_mulw +
          cols.is_mulhsu + cols.is_mulhu }
  | .shiftLeft cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_sll + cols.is_sllw }
  | .addw cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .uType cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .jalr cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.jump_target[0], cols.jump_target[1],
          cols.jump_target[2]],
        is_real := cols.is_real }
  | .lt cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_slt + cols.is_sltu }
  | .storeWord cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .storeDouble cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .storeHalf cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .loadDouble cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .loadWord cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_lw + cols.is_lwu }
  | .loadHalf cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_lh + cols.is_lhu }
  | .branch cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := cols.next_pc,
        is_real := cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
          cols.is_bltu + cols.is_bgeu }
  | .loadX0 cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld }
  | .shiftRight cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw }
  | .divRem cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .addi cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .bitwise cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_xor + cols.is_or + cols.is_and }
  | .sub cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
        is_real := cols.is_real }
  | .subw cols =>
      { clk_high := cols.clk_high,
        clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536,
        pc := cols.pc,
        next_pc := #v[cols.pc[0] + 4, cols.pc[1], cols.pc[2]],
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

/-- The aggregated state-access list satisfies the PC chain under
`TraceStateValid`. The hypothesis already bundles the conclusion (this
theorem is the structural unfolding), so the proof is a direct
projection. Future work proves `TraceStateValid` from chip `Spec`s. -/
theorem aggregateStateAccesses_pcChain
    (rows : List (ChipRow p)) (clkIncrement : ZMod p)
    (h : TraceStateValid rows clkIncrement) :
    pcChainProp clkIncrement (aggregateStateAccesses rows) :=
  h.chain_holds

end SP1Clean.Soundness
