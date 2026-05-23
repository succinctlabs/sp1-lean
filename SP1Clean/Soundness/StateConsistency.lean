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

Each chip's `next_pc` projection reads a Clean-side column that the
chip's `FormalSpec` constrains to the carry-aware semantic next_pc:

- **20 arithmetic chips + Mul** (Add, Addi, Addw, Bitwise, DivRem,
  Load{Byte,Double,Half,Word,X0}, Lt, Mul, Shift{Left,Right},
  Store{Byte,Double,Half,Word}, Sub, Subw, UType): read
  `cols.next_pc_carry_value`, the 3-limb result of `pc + #v[4,0,0,0]`
  constrained by the chip's `AddrAddOp.assertion.Spec` clause.
- **Jal**: reads `cols.next_pc[0..2]`, truncating the 4-limb column.
- **Jalr**: reads `cols.jump_target[0..2]` with bit-0 of the low limb
  cleared (`jump_target[0] - cols.lsb`) to match the chip's
  alignment masking.
- **Branch**: reads `cols.next_pc` directly (already 3-limb); for
  Branch the FormalSpec widening in iter-8 surfaces the case-split on
  `is_branching` so this column equals either `pc + imm` (taken) or
  `pc + 4` (not taken).

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
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .loadByte cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_lb + cols.is_lbu }
  | .storeByte cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
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
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_mul + cols.is_mulh + cols.is_mulw +
          cols.is_mulhsu + cols.is_mulhu }
  | .shiftLeft cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_sll + cols.is_sllw }
  | .addw cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .uType cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
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
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_slt + cols.is_sltu }
  | .storeWord cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .storeDouble cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .storeHalf cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .loadDouble cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .loadWord cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_lw + cols.is_lwu }
  | .loadHalf cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
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
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld }
  | .shiftRight cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw }
  | .divRem cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .addi cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .bitwise cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_xor + cols.is_or + cols.is_and }
  | .sub cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
        is_real := cols.is_real }
  | .subw cols =>
      { clk_high := cols.state.clk_high,
        clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
        pc := cols.state.pc,
        next_pc := cols.next_pc_carry_value,
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

/-! ## Per-chip `nextPc_of_spec_<chip>` projection lemmas

For each chip whose `FormalSpec` contains an `AddrAddOp.assertion.Spec`
conjunct on `(pc.push 0, #v[4,0,0,0], next_pc_carry_value)`, project the
conjunct out. These take `<Chip>.assertion.Spec cols` (NOT the legacy
`<Chip>.Spec cols` referenced by today's `ChipRow.Spec`) and serve as
standalone utility lemmas; they become live trace-level consumers once
sub-task E normalizes `ChipRow.Spec` to `assertion.Spec`.

Jal projects an `AddOp.Spec` (jump-target sum). Jalr projects a gated
`is_real = 0 ∨ GatedAddOp.Spec` disjunction (the `lsb`-cleared
jump-target sum). Branch has no `next_pc` constraint in its current
FormalSpec — that lands in iter-8 sub-task C. -/

theorem nextPc_of_spec_add (cols : Add.AddCols (ZMod p))
    (h : Add.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Add.Assertion.FormalSpec cols at h
  exact h.2.2.2.1

theorem nextPc_of_spec_addi (cols : Addi.AddiCols (ZMod p))
    (h : Addi.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Addi.Assertion.FormalSpec cols at h
  exact h.2.2.2.1

theorem nextPc_of_spec_addw (cols : Addw.AddwCols (ZMod p))
    (h : Addw.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Addw.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_bitwise (cols : Bitwise.BitwiseCols (ZMod p))
    (h : Bitwise.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Bitwise.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_divRem (cols : DivRem.DivRemCols (ZMod p))
    (h : DivRem.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change DivRem.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_loadByte (cols : LoadByte.LoadByteCols (ZMod p))
    (h : LoadByte.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change LoadByte.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_loadDouble (cols : LoadDouble.LoadDoubleCols (ZMod p))
    (h : LoadDouble.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change LoadDouble.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_loadHalf (cols : LoadHalf.LoadHalfCols (ZMod p))
    (h : LoadHalf.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change LoadHalf.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_loadWord (cols : LoadWord.LoadWordCols (ZMod p))
    (h : LoadWord.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change LoadWord.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_loadX0 (cols : LoadX0.LoadX0Cols (ZMod p))
    (h : LoadX0.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change LoadX0.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_lt (cols : Lt.LtCols (ZMod p))
    (h : Lt.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Lt.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_mul (cols : Mul.MulCols (ZMod p))
    (h : Mul.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Mul.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_shiftLeft (cols : ShiftLeft.ShiftLeftCols (ZMod p))
    (h : ShiftLeft.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change ShiftLeft.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_shiftRight (cols : ShiftRight.ShiftRightCols (ZMod p))
    (h : ShiftRight.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change ShiftRight.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_storeByte (cols : StoreByte.StoreByteCols (ZMod p))
    (h : StoreByte.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change StoreByte.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_storeDouble (cols : StoreDouble.StoreDoubleCols (ZMod p))
    (h : StoreDouble.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change StoreDouble.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_storeHalf (cols : StoreHalf.StoreHalfCols (ZMod p))
    (h : StoreHalf.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change StoreHalf.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_storeWord (cols : StoreWord.StoreWordCols (ZMod p))
    (h : StoreWord.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change StoreWord.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_sub (cols : Sub.SubCols (ZMod p))
    (h : Sub.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Sub.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_subw (cols : Sub.W.SubwCols (ZMod p))
    (h : Sub.W.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change Sub.W.Assertion.FormalSpec cols at h
  exact h.2.2.1

theorem nextPc_of_spec_uType (cols : UType.UTypeCols (ZMod p))
    (h : UType.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
      ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
       #v[(4 : ZMod p), 0, 0, 0],
       cols.next_pc_carry_value⟩ := by
  change UType.Assertion.FormalSpec cols at h
  exact h.2.2.1

/-- Jal's next_pc is constrained as `pc + imm` via `AddOp.Spec` on the
4-limb augmented PC. Conjunct #1 of `Jal.Assertion.FormalSpec` (after the
leading `cpuStateSpec` conjunct added in Phase 2). -/
theorem nextPc_of_spec_jal (cols : Jal.JalCols (ZMod p))
    (h : Jal.assertion.Spec cols) :
    SP1Clean.AddOp.Spec (cols.state.pc.push 0) cols.imm cols.next_pc := by
  change Jal.Assertion.FormalSpec cols at h
  exact h.2.1

/-- Jalr's jump_target is constrained as `op_b + op_c_imm` via a gated
`AddOp.Spec` (gated on `is_real`). The disjunction form `is_real = 0 ∨
…` lives at conjunct #2 of `Jalr.Assertion.FormalSpec`; the actual
projected `next_pc` is `jump_target` with bit-0 cleared (see
`ChipRow.stateAccess`'s Jalr arm). -/
theorem nextPc_of_spec_jalr (cols : Jalr.JalrCols (ZMod p))
    (h : Jalr.assertion.Spec cols) :
    cols.is_real = 0 ∨ SP1Clean.GatedAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm cols.jump_target := by
  change Jalr.Assertion.FormalSpec cols at h
  exact h.2.2.1

/-- Branch's `next_pc` is the `is_branching`-mux of two carry-aware arms.
Sub-task C widened `Branch.Assertion.FormalSpec` with `AddrAddOp.assertion.Spec`
conjuncts for the taken arm (`pc + op_c_imm = next_pc_branched_carry`) and
not-taken arm (`pc + 4 = next_pc_unbranched_carry`), an `is_branching`
boolean gate, and three per-limb mux equations. This lemma projects both
AddrAddOp arms as a bundled pair. -/
theorem nextPc_of_spec_branch (cols : Branch.BranchCols (ZMod p))
    (h : Branch.assertion.Spec cols) :
    SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         cols.op_c_imm,
         cols.next_pc_branched_carry⟩ ∧
    SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_unbranched_carry⟩ := by
  change Branch.Assertion.FormalSpec cols at h
  refine ⟨h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## Per-row `nextPc`-validity dispatch (iter-8 Phase 2)

`ChipRow.nextPcValid` packages the per-row `next_pc`-column semantic
content as a single predicate keyed on the chip constructor. For
arithmetic chips it's the `AddrAddOp.assertion.Spec` on `pc + 4 =
next_pc_carry_value`; for jumps/branches it's the chip-specific
next_pc-witness.

`nextPcValid_of_chipRow_spec` then dispatches the 24
`nextPc_of_spec_<chip>` lemmas via `cases row` — a structurally
analogous wrap-up to `cpuStateSpec_of_chipRow_spec` in
`MemoryConsistencyClock.lean` and `traceIsRealBinary_of_chip_specs`
in `IsRealBinary.lean`. -/

/-- Per-row `next_pc`-validity predicate, dispatched on chip identity.
Each arm extracts the chip-specific next_pc-witness that
`ChipRow.Spec` already establishes. -/
def ChipRow.nextPcValid : ChipRow p → Prop
  | .add cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .addi cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .addw cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .bitwise cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .branch cols =>
      SP1Clean.AddrAddOp.assertion.Spec
          ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
           cols.op_c_imm,
           cols.next_pc_branched_carry⟩ ∧
      SP1Clean.AddrAddOp.assertion.Spec
          ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
           #v[(4 : ZMod p), 0, 0, 0],
           cols.next_pc_unbranched_carry⟩
  | .divRem cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .jal cols =>
      SP1Clean.AddOp.Spec (cols.state.pc.push 0) cols.imm cols.next_pc
  | .jalr cols =>
      cols.is_real = 0 ∨ SP1Clean.GatedAddOp.Spec
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm cols.jump_target
  | .loadByte cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .loadDouble cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .loadHalf cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .loadWord cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .loadX0 cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .lt cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .mul cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .shiftLeft cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .shiftRight cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .storeByte cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .storeDouble cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .storeHalf cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .storeWord cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .sub cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .subw cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  | .uType cols =>
      SP1Clean.AddrAddOp.assertion.Spec
        ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
         #v[(4 : ZMod p), 0, 0, 0],
         cols.next_pc_carry_value⟩
  -- Boundary chips: no `next_pc` semantic content. Placeholder `True`
  -- since boundary chips don't participate in the PC chain.
  | .memInit _ => True
  | .memFinalize _ => True

/-- Top-level dispatch: every `ChipRow.Spec row` yields the per-row
`nextPcValid` witness. Mirrors `cpuStateSpec_of_chipRow_spec`'s
24-arm dispatch in `MemoryConsistencyClock.lean`. -/
theorem nextPcValid_of_chipRow_spec
    (row : ChipRow p) (h : ChipRow.Spec row) : row.nextPcValid := by
  cases row with
  | add cols => exact nextPc_of_spec_add cols h
  | addi cols => exact nextPc_of_spec_addi cols h
  | addw cols => exact nextPc_of_spec_addw cols h
  | bitwise cols => exact nextPc_of_spec_bitwise cols h
  | branch cols => exact nextPc_of_spec_branch cols h
  | divRem cols => exact nextPc_of_spec_divRem cols h
  | jal cols => exact nextPc_of_spec_jal cols h
  | jalr cols => exact nextPc_of_spec_jalr cols h
  | loadByte cols => exact nextPc_of_spec_loadByte cols h
  | loadDouble cols => exact nextPc_of_spec_loadDouble cols h
  | loadHalf cols => exact nextPc_of_spec_loadHalf cols h
  | loadWord cols => exact nextPc_of_spec_loadWord cols h
  | loadX0 cols => exact nextPc_of_spec_loadX0 cols h
  | lt cols => exact nextPc_of_spec_lt cols h
  | mul cols => exact nextPc_of_spec_mul cols h
  | shiftLeft cols => exact nextPc_of_spec_shiftLeft cols h
  | shiftRight cols => exact nextPc_of_spec_shiftRight cols h
  | storeByte cols => exact nextPc_of_spec_storeByte cols h
  | storeDouble cols => exact nextPc_of_spec_storeDouble cols h
  | storeHalf cols => exact nextPc_of_spec_storeHalf cols h
  | storeWord cols => exact nextPc_of_spec_storeWord cols h
  | sub cols => exact nextPc_of_spec_sub cols h
  | subw cols => exact nextPc_of_spec_subw cols h
  | uType cols => exact nextPc_of_spec_uType cols h
  | memInit _ => trivial
  | memFinalize _ => trivial

/-- Trace-level `nextPc`-validity: every chip row's `next_pc` column
is constrained by its chip Spec. Per-row content for the state-bus
chain; combined with the chronological `TraceStateLink` adjacency
hypothesis, this gives the full `TraceStateValid`. -/
def TraceNextPcValid (rows : List (ChipRow p)) : Prop :=
  ∀ row ∈ rows, row.nextPcValid

/-- Discharge of `TraceNextPcValid` from chip Specs. This is the
per-row `next_pc`-semantic-content half of the state-bus discharge.
The chronological pcChainProp half is `TraceStateLink`. -/
theorem traceNextPcValid_of_chip_specs (rows : List (ChipRow p))
    (h_specs : ∀ row ∈ rows, ChipRow.Spec row) :
    TraceNextPcValid rows := by
  intro row h_mem
  exact nextPcValid_of_chipRow_spec row (h_specs row h_mem)

end SP1Clean.Soundness
