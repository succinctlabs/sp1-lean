import SP1Clean.Soundness.MemoryConsistency
import SP1Clean.Reader.CPUState

/-! # Trace-level clock invariants for memory access aggregation

This file proves
`aggregateMemoryAccesses_isTimestampSorted` and
`aggregateMemoryAccesses_Notimestampdup` — the trace-shape side
conditions of `chip_specs_admit_offline_bridge` in
`SP1Clean/Soundness/MemoryConsistency.lean`.

## Proof structure

`aggregateMemoryAccesses rows` is `rows.reverse.flatMap rowAccessTuples`.
`List.pairwise_flatMap` decomposes Pairwise on this expression into two
pieces:

1. **Per-row Pairwise** (`intra_row_sorted`): every row's local access
   list is itself `Pairwise timestamp_ordering`.
2. **Inter-row Pairwise** (`inter_row_sorted`): for any two rows `r₁`
   (later in chronological order, head-side in `rows.reverse`) and `r₂`
   (earlier), every access in `r₁` has timestamp strictly greater than
   every access in `r₂`.

The `TraceClkValid` predicate bundles both. Future work discharges it
from per-chip `Spec`s plus a strict clock-monotonicity trace
assumption (see notes on `chipRowEncodedClk` below).

`Notimestampdup` (no duplicate timestamps) follows from
`isTimestampSorted` plus strictness of `timestamp_ordering`. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Encoded chip-row clock as a `ℕ`: `clk_high.val * 2^24 + clk_low.val`.

Defined here for use in future discharge work
(`TraceClkValid_of_chipSpecs`): the trace-shape assumption on these
encoded clocks (strictly increasing chronologically with separation
≥ 5 between consecutive rows) is what justifies `inter_row_sorted`. -/
def ChipRow.encodedClk (row : ChipRow p) : ℕ :=
  let (clk_high, clk_low) := row.clockComponents
  clk_high.val * (2 ^ 24) + clk_low.val

/-- Trace-shape clock invariant bundling the per-row and inter-row
Pairwise hypotheses needed by `pairwise_flatMap` to conclude the
aggregated list is `Pairwise timestamp_ordering`.

Both fields are stated at the `MemoryAccess`-tuple level (not on
encoded clocks directly) to keep the bridge to upstream OfflineMemory's
`Pairwise timestamp_ordering` direct.

A future discharge lemma (see `docs/CLEAN_PILOT_NOTES.md` Phase A.3.2)
will derive `TraceClkValid` from per-chip `Spec`s (`cpuStateSpec` plus
`memoryAccessSpec`) given a strict clock-monotonicity trace assumption
on `ChipRow.encodedClk`. -/
structure TraceClkValid (rows : List (ChipRow p)) : Prop where
  /-- Within each chip row, its per-row access list is sorted in
  strictly decreasing timestamp order (the chip's `offsets` field is
  emitted in decreasing order, e.g. `[4, 3, 2]`). -/
  intra_row_sorted :
    ∀ row ∈ rows, (ChipRow.rowAccessTuples row).Pairwise timestamp_ordering
  /-- Between any two rows in `rows.reverse` (head-side row later in
  chronological order than tail-side row), every access in the
  head-side row has timestamp strictly greater than every access in
  the tail-side row. -/
  inter_row_sorted :
    rows.reverse.Pairwise (fun r₁ r₂ =>
      ∀ x ∈ ChipRow.rowAccessTuples r₁,
        ∀ y ∈ ChipRow.rowAccessTuples r₂, timestamp_ordering x y)

/-- The aggregated memory-access list is timestamp-sorted (Pairwise
`timestamp_ordering`) under `TraceClkValid`. -/
theorem aggregateMemoryAccesses_isTimestampSorted
    (rows : List (ChipRow p)) (h : TraceClkValid rows) :
    (aggregateMemoryAccesses rows).isTimestampSorted := by
  change List.Pairwise timestamp_ordering (rows.reverse.flatMap ChipRow.rowAccessTuples)
  rw [List.pairwise_flatMap]
  refine ⟨?_, h.inter_row_sorted⟩
  intro row hrow
  rw [List.mem_reverse] at hrow
  exact h.intra_row_sorted row hrow

/-- The aggregated memory-access list has no duplicate timestamps under
`TraceClkValid`. Derived from `isTimestampSorted` plus strictness of
`timestamp_ordering` (`t1 < t2` implies `t1 ≠ t2`). -/
theorem aggregateMemoryAccesses_Notimestampdup
    (rows : List (ChipRow p)) (h : TraceClkValid rows) :
    (aggregateMemoryAccesses rows).Notimestampdup := by
  have h_sorted := aggregateMemoryAccesses_isTimestampSorted rows h
  change List.Pairwise MemoryAccessList.timestamps_neq _
  apply List.Pairwise.imp ?_ h_sorted
  intro x y hxy
  obtain ⟨t2, _, _, _⟩ := x
  obtain ⟨t1, _, _, _⟩ := y
  simp only [timestamp_ordering] at hxy
  simp only [MemoryAccessList.timestamps_neq]
  omega

/-! ## Discharge of `TraceClkValid` from chip `Spec`s

The remaining content of this file derives `TraceClkValid` from per-row
chip `Spec`s plus a single chronological clock-link hypothesis
(`TraceClkLink`). This is §3a of `docs/TRACE_SOUNDNESS_STATUS.md`.

The discharge requires the field to be larger than `2^24` so that the
encoded clock `clk_high.val * 2^24 + clk_low.val` plus a small offset
(≤ 4) does not wrap modulo `p`. KoalaBear (`~2^31`) satisfies this. -/

/-- Strict chronological separation of adjacent rows' encoded clocks.

`rows` is in chronological order (row 0 earliest, row n-1 latest);
`rows.reverse` flips that so the head is the latest row. The `Pairwise`
predicate then asserts every "later" row's encoded clock is at least
`clkIncrement` greater than every "earlier" row's encoded clock.

Combined with the per-row offset bound (offsets ∈ [0,4]) and
`clkIncrement ≥ 5` (canonically `8`), this is enough to derive the
inter-row arm of `TraceClkValid`. -/
def TraceClkLink (rows : List (ChipRow p)) (clkIncrement : ℕ) : Prop :=
  rows.reverse.Pairwise (fun later earlier =>
    earlier.encodedClk + clkIncrement ≤ later.encodedClk)

/-! ### Per-chip `cpuStateSpec` projection lemmas

Each chip's `Spec` (the predicate used by `ChipRow.Spec`) contains
`CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24` as a conjunct.
These 24 lemmas project that conjunct, mirroring the
`is_real_binary_<chip>` recipe in `IsRealBinary.lean`. -/

theorem cpuStateSpec_of_spec_add (cols : Add.AddCols (ZMod p))
    (h : Add.assertion.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  change Add.Assertion.FormalSpec cols at h
  exact h.2.1

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_addi (cols : Addi.AddiCols (ZMod p))
    (h : Addi.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Addi.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_addw (cols : Addw.AddwCols (ZMod p))
    (h : Addw.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Addw.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_bitwise (cols : Bitwise.BitwiseCols (ZMod p))
    (h : Bitwise.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Bitwise.Spec at h
  tauto

theorem cpuStateSpec_of_spec_branch (cols : Branch.BranchCols (ZMod p))
    (h : Branch.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Branch.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_divRem (cols : DivRem.DivRemCols (ZMod p))
    (h : DivRem.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold DivRem.Spec at h
  tauto

theorem cpuStateSpec_of_spec_jal (cols : Jal.JalCols (ZMod p))
    (h : Jal.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Jal.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_jalr (cols : Jalr.JalrCols (ZMod p))
    (h : Jalr.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Jalr.Spec at h
  tauto

theorem cpuStateSpec_of_spec_loadByte (cols : LoadByte.LoadByteCols (ZMod p))
    (h : LoadByte.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold LoadByte.Spec at h
  tauto

theorem cpuStateSpec_of_spec_loadDouble
    (cols : LoadDouble.LoadDoubleCols (ZMod p))
    (h : LoadDouble.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold LoadDouble.Spec at h
  tauto

theorem cpuStateSpec_of_spec_loadHalf (cols : LoadHalf.LoadHalfCols (ZMod p))
    (h : LoadHalf.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold LoadHalf.Spec at h
  tauto

theorem cpuStateSpec_of_spec_loadWord (cols : LoadWord.LoadWordCols (ZMod p))
    (h : LoadWord.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold LoadWord.Spec at h
  tauto

theorem cpuStateSpec_of_spec_loadX0 (cols : LoadX0.LoadX0Cols (ZMod p))
    (h : LoadX0.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold LoadX0.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_lt (cols : Lt.LtCols (ZMod p))
    (h : Lt.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Lt.Spec at h
  tauto

theorem cpuStateSpec_of_spec_mul (cols : Mul.MulCols (ZMod p))
    (h : Mul.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Mul.Spec at h
  tauto

theorem cpuStateSpec_of_spec_shiftLeft (cols : ShiftLeft.ShiftLeftCols (ZMod p))
    (h : ShiftLeft.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold ShiftLeft.Spec at h
  tauto

theorem cpuStateSpec_of_spec_shiftRight
    (cols : ShiftRight.ShiftRightCols (ZMod p))
    (h : ShiftRight.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold ShiftRight.Spec at h
  tauto

theorem cpuStateSpec_of_spec_storeByte (cols : StoreByte.StoreByteCols (ZMod p))
    (h : StoreByte.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold StoreByte.Spec at h
  tauto

theorem cpuStateSpec_of_spec_storeDouble
    (cols : StoreDouble.StoreDoubleCols (ZMod p))
    (h : StoreDouble.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold StoreDouble.Spec at h
  tauto

theorem cpuStateSpec_of_spec_storeHalf
    (cols : StoreHalf.StoreHalfCols (ZMod p))
    (h : StoreHalf.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold StoreHalf.Spec at h
  tauto

theorem cpuStateSpec_of_spec_storeWord
    (cols : StoreWord.StoreWordCols (ZMod p))
    (h : StoreWord.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold StoreWord.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_sub (cols : Sub.SubCols (ZMod p))
    (h : Sub.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Sub.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_subw (cols : Sub.W.SubwCols (ZMod p))
    (h : Sub.W.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold Sub.W.Spec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
theorem cpuStateSpec_of_spec_uType (cols : UType.UTypeCols (ZMod p))
    (h : UType.Spec cols) :
    CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  unfold UType.Spec at h
  tauto

/-- Row-level cpuStateSpec predicate: every chip carries the same
`((clk_0_16 - 1) * 8⁻¹).val < 8192 ∧ clk_16_24 < 256` constraint on its
clock fields. -/
def ChipRow.cpuStateSpec : ChipRow p → Prop
  | .add cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .addi cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .addw cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .bitwise cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .branch cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .divRem cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .jal cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .jalr cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .loadByte cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .loadDouble cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .loadHalf cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .loadWord cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .loadX0 cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .lt cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .mul cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .shiftLeft cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .shiftRight cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .storeByte cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .storeDouble cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .storeHalf cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .storeWord cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .sub cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .subw cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24
  | .uType cols => CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24

/-- Top-level projection: every `ChipRow.Spec row` yields the
`cpuStateSpec` bound on the row's underlying clock fields. Mirrors
`traceIsRealBinary_of_chip_specs`'s 24-arm dispatch. -/
theorem cpuStateSpec_of_chipRow_spec
    (row : ChipRow p) (h : ChipRow.Spec row) : row.cpuStateSpec := by
  cases row with
  | add cols => exact cpuStateSpec_of_spec_add cols h
  | addi cols => exact cpuStateSpec_of_spec_addi cols h
  | addw cols => exact cpuStateSpec_of_spec_addw cols h
  | bitwise cols => exact cpuStateSpec_of_spec_bitwise cols h
  | branch cols => exact cpuStateSpec_of_spec_branch cols h
  | divRem cols => exact cpuStateSpec_of_spec_divRem cols h
  | jal cols => exact cpuStateSpec_of_spec_jal cols h
  | jalr cols => exact cpuStateSpec_of_spec_jalr cols h
  | loadByte cols => exact cpuStateSpec_of_spec_loadByte cols h
  | loadDouble cols => exact cpuStateSpec_of_spec_loadDouble cols h
  | loadHalf cols => exact cpuStateSpec_of_spec_loadHalf cols h
  | loadWord cols => exact cpuStateSpec_of_spec_loadWord cols h
  | loadX0 cols => exact cpuStateSpec_of_spec_loadX0 cols h
  | lt cols => exact cpuStateSpec_of_spec_lt cols h
  | mul cols => exact cpuStateSpec_of_spec_mul cols h
  | shiftLeft cols => exact cpuStateSpec_of_spec_shiftLeft cols h
  | shiftRight cols => exact cpuStateSpec_of_spec_shiftRight cols h
  | storeByte cols => exact cpuStateSpec_of_spec_storeByte cols h
  | storeDouble cols => exact cpuStateSpec_of_spec_storeDouble cols h
  | storeHalf cols => exact cpuStateSpec_of_spec_storeHalf cols h
  | storeWord cols => exact cpuStateSpec_of_spec_storeWord cols h
  | sub cols => exact cpuStateSpec_of_spec_sub cols h
  | subw cols => exact cpuStateSpec_of_spec_subw cols h
  | uType cols => exact cpuStateSpec_of_spec_uType cols h

/-! ### Bounds derived from `cpuStateSpec`

The `cpuStateSpec` predicate is stated in field-arithmetic terms;
the discharge below needs Nat-level bounds for the no-wrap argument. -/

section TraceClkValidDischarge

variable [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
private lemma val_of_small_nat (n : ℕ) (h : n < 2 ^ 17) : ((n : ZMod p) : ZMod p).val = n := by
  have hp : 2 ^ 17 < p := Fact.out
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

omit [Fact (2 ^ 24 < p)] in
/-- From `((x - 1) * 8⁻¹).val < 8192`, conclude `x.val ≤ 65529`. -/
private lemma val_le_of_cpuStateSpec_clk_0_16
    (x : ZMod p) (h : ((x - 1) * (8 : ZMod p)⁻¹).val < 8192) :
    x.val ≤ 65529 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  set y := (x - 1) * (8 : ZMod p)⁻¹ with hy_def
  have h8_val : (8 : ZMod p).val = 8 := by
    rw [show (8 : ZMod p) = ((8 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h8_ne : (8 : ZMod p) ≠ 0 := by
    intro h8
    have : (8 : ZMod p).val = 0 := by rw [h8]; exact ZMod.val_zero
    omega
  have h_eq : x = 8 * y + 1 := by
    rw [hy_def]
    have : 8 * ((x - 1) * (8 : ZMod p)⁻¹) = x - 1 := by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ h8_ne, mul_one]
    rw [this]; ring
  have h_1_val : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  have h_8y_val : (8 * y).val = 8 * y.val := by
    rw [ZMod.val_mul, h8_val, Nat.mod_eq_of_lt]
    have : 8 * y.val < 8 * 8192 := by have := h; omega
    omega
  have h_8y1_val : (8 * y + 1).val = 8 * y.val + 1 := by
    rw [ZMod.val_add, h_8y_val, h_1_val, Nat.mod_eq_of_lt]
    have : 8 * y.val + 1 < 8 * 8192 + 1 := by have := h; omega
    omega
  rw [h_eq, h_8y1_val]
  have : y.val < 8192 := h
  omega

omit [Fact (2 ^ 24 < p)] in
/-- From `clk_16_24 < (256 : ZMod p)`, conclude `clk_16_24.val < 256`. -/
private lemma val_lt_of_cpuStateSpec_clk_16_24
    (x : ZMod p) (h : x < (256 : ZMod p)) : x.val < 256 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h256 : (256 : ZMod p).val = 256 := by
    rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  change x.val < (256 : ZMod p).val at h
  omega

/-- Combined: `clk_0_16 + clk_16_24 * 65536` as a Nat does not wrap. -/
private lemma clk_low_val_lt
    {clk_0_16 clk_16_24 : ZMod p}
    (h : CPUState.cpuStateSpec clk_0_16 clk_16_24) :
    (clk_0_16 + clk_16_24 * 65536).val ≤ 65529 + 255 * 65536 := by
  have hp17 : 2 ^ 17 < p := Fact.out
  have hp24 : 2 ^ 24 < p := Fact.out
  obtain ⟨h_clk_0_16, h_clk_16_24⟩ := h
  have h_clk_0_16_val := val_le_of_cpuStateSpec_clk_0_16 clk_0_16 h_clk_0_16
  have h_clk_16_24_val := val_lt_of_cpuStateSpec_clk_16_24 clk_16_24 h_clk_16_24
  have h_65536_val : (65536 : ZMod p).val = 65536 := by
    rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h_mul_val : (clk_16_24 * 65536).val = clk_16_24.val * 65536 := by
    rw [ZMod.val_mul, h_65536_val, Nat.mod_eq_of_lt]
    have : clk_16_24.val * 65536 < 256 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : 0 < 65536)).mpr h_clk_16_24_val
    omega
  rw [ZMod.val_add, h_mul_val, Nat.mod_eq_of_lt]
  · have : clk_0_16.val + clk_16_24.val * 65536 ≤ 65529 + 255 * 65536 := by
      have : clk_16_24.val * 65536 ≤ 255 * 65536 := by
        apply Nat.mul_le_mul_right; omega
      omega
    exact this
  · have h_sum : clk_0_16.val + clk_16_24.val * 65536 ≤ 65529 + 255 * 65536 := by
      have : clk_16_24.val * 65536 ≤ 255 * 65536 := by
        apply Nat.mul_le_mul_right; omega
      omega
    omega

omit [Fact (2 ^ 17 < p)] in
/-- Adding a small offset (≤ 4) to a clk_low value that's ≤ `65529 + 255 * 65536`
does not wrap modulo `p`. -/
private lemma clk_low_add_small_val
    (clk_low : ZMod p) (off : ZMod p)
    (h_clk_low : clk_low.val ≤ 65529 + 255 * 65536)
    (h_off : off.val ≤ 4) :
    (clk_low + off).val = clk_low.val + off.val := by
  have hp : 2 ^ 24 < p := Fact.out
  rw [ZMod.val_add, Nat.mod_eq_of_lt]
  have h2 : (65529 + 255 * 65536 : ℕ) + 4 < 2 ^ 24 := by decide
  omega

omit [Fact (2 ^ 24 < p)] in
/-- `(n : ZMod p).val = n` for small literals (≤ 4). -/
private lemma small_offset_val (n : ℕ) (h : n ≤ 4) : ((n : ZMod p)).val = n := by
  have hp : 2 ^ 17 < p := Fact.out
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-! ### Per-tuple timestamp helpers -/

omit [Fact (2 ^ 17 < p)] in
/-- The timestamp component of `toAccessTuple` factors as
`clk_high.val * 2^24 + clk_low.val + offset.val` when no wrap occurs. -/
private lemma toAccessTuple_fst_eq
    (clk_high clk_low : ZMod p) (off : ZMod p)
    (acc : SP1Clean.MemoryAccess (ZMod p)) (wv : Word (ZMod p))
    (h_clk_low : clk_low.val ≤ 65529 + 255 * 65536)
    (h_off : off.val ≤ 4) :
    (acc.toAccessTuple clk_high clk_low off wv).1 =
      clk_high.val * 2 ^ 24 + clk_low.val + off.val := by
  simp only [SP1Clean.MemoryAccess.toAccessTuple]
  rw [clk_low_add_small_val clk_low off h_clk_low h_off]
  ring

omit [Fact (2 ^ 17 < p)] in
/-- Strict ordering on `toAccessTuple` outputs derived from offset comparison. -/
private lemma toAccessTuple_timestamp_ordering
    (clk_high clk_low : ZMod p) (off1 off2 : ZMod p)
    (acc1 acc2 : SP1Clean.MemoryAccess (ZMod p))
    (wv1 wv2 : Word (ZMod p))
    (h_clk_low : clk_low.val ≤ 65529 + 255 * 65536)
    (h_off1 : off1.val ≤ 4) (h_off2 : off2.val ≤ 4)
    (h_lt : off2.val < off1.val) :
    timestamp_ordering
      (acc1.toAccessTuple clk_high clk_low off1 wv1)
      (acc2.toAccessTuple clk_high clk_low off2 wv2) := by
  change (acc2.toAccessTuple clk_high clk_low off2 wv2).1 <
       (acc1.toAccessTuple clk_high clk_low off1 wv1).1
  rw [toAccessTuple_fst_eq clk_high clk_low off1 acc1 wv1 h_clk_low h_off1,
      toAccessTuple_fst_eq clk_high clk_low off2 acc2 wv2 h_clk_low h_off2]
  omega

/-! ### Intra-row Pairwise lemma

Each chip's `rowAccessTuples` list is `Pairwise timestamp_ordering` under
the `cpuStateSpec` clock bounds. The proof is uniform over the offset
lists (`[4,3,2]`, `[4,3,1]`, `[4,3,0]`, `[4,3]`, `[4]`) — at most a
3-element list with strictly decreasing offsets ≤ 4. -/

omit [Fact (2 ^ 17 < p)] in
/-- Generic Pairwise lemma: given a zipped `entries` list of (access × offset)
pairs with offsets in `[0, 4]` and pairwise strictly decreasing, the
resulting timestamps are `Pairwise timestamp_ordering`. -/
private lemma toAccessTuples_pairwise
    (clk_high clk_low : ZMod p)
    (h_clk_low : clk_low.val ≤ 65529 + 255 * 65536)
    (entries : List ((SP1Clean.MemoryAccess (ZMod p) × Word (ZMod p)) × ZMod p))
    (h_off_bound : ∀ e ∈ entries, e.2.val ≤ 4)
    (h_off_desc : entries.Pairwise (fun e1 e2 => e2.2.val < e1.2.val)) :
    (entries.map fun e =>
        e.1.1.toAccessTuple clk_high clk_low e.2 e.1.2).Pairwise
      timestamp_ordering := by
  induction entries with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
    rcases List.pairwise_cons.mp h_off_desc with ⟨h_head_lt, h_tail_desc⟩
    have h_head_off : head.2.val ≤ 4 := h_off_bound head List.mem_cons_self
    refine List.Pairwise.cons ?_ ?_
    · intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨x, hx_mem, rfl⟩ := hy
      have h_x_off : x.2.val ≤ 4 := h_off_bound x (List.mem_cons_of_mem _ hx_mem)
      exact toAccessTuple_timestamp_ordering _ _ _ _ _ _ _ _ h_clk_low
        h_head_off h_x_off (h_head_lt x hx_mem)
    · exact ih (fun e he => h_off_bound e (List.mem_cons_of_mem _ he)) h_tail_desc

omit [Fact (2 ^ 24 < p)] in
/-- The `val`s of small ZMod literals 0..4 are themselves. -/
private lemma zmod_small_vals :
    ((0 : ZMod p)).val = 0 ∧
    ((1 : ZMod p)).val = 1 ∧
    ((2 : ZMod p)).val = 2 ∧
    ((3 : ZMod p)).val = 3 ∧
    ((4 : ZMod p)).val = 4 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  refine ⟨ZMod.val_zero, ?_, ?_, ?_, ?_⟩
  · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  all_goals
    first
    | (rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; rfl,
           ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)])
    | (rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl,
           ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)])
    | (rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl,
           ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)])

omit [Fact (2 ^ 24 < p)] in
/-- Offsets list per chip has each offset's `.val ≤ 4` and is pairwise
strictly decreasing in `.val`. -/
private lemma chipRow_offsets_props (row : ChipRow p) :
    (∀ o ∈ row.offsets, o.val ≤ 4) ∧
    row.offsets.Pairwise (fun o1 o2 => o2.val < o1.val) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := zmod_small_vals (p := p)
  cases row <;>
    refine ⟨?_, ?_⟩ <;>
    simp_all [ChipRow.offsets, List.pairwise_cons]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
/-- Lift "each offset ≤ 4" to "each zipped-entry's offset ≤ 4". -/
private lemma zipped_off_bound
    {α : Type*} (xs : List α) (offs : List (ZMod p))
    (h : ∀ o ∈ offs, o.val ≤ 4) :
    ∀ e ∈ xs.zip offs, e.2.val ≤ 4 := by
  intro e he
  exact h _ (List.of_mem_zip he).2

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
/-- Lift "offsets pairwise descending" to "zipped entries pairwise
descending in .2". -/
private lemma zipped_off_desc
    {α : Type*} (xs : List α) (offs : List (ZMod p))
    (h : offs.Pairwise (fun o1 o2 => o2.val < o1.val)) :
    (xs.zip offs).Pairwise (fun e1 e2 => e2.2.val < e1.2.val) := by
  induction xs generalizing offs with
  | nil => simp
  | cons x xs ih =>
    cases offs with
    | nil => simp
    | cons o os =>
      rcases List.pairwise_cons.mp h with ⟨h_head, h_tail⟩
      simp only [List.zip_cons_cons, List.pairwise_cons]
      refine ⟨?_, ih os h_tail⟩
      intro e he
      exact h_head _ (List.of_mem_zip he).2

/-- Each chip's per-row access tuple list is `Pairwise timestamp_ordering`
under `cpuStateSpec` on its clock fields. -/
private lemma rowAccessTuples_pairwise_of_cpuStateSpec
    (row : ChipRow p) (h_cpu : row.cpuStateSpec) :
    row.rowAccessTuples.Pairwise timestamp_ordering := by
  obtain ⟨h_off_bound, h_off_desc⟩ := chipRow_offsets_props row
  cases row <;> (
    simp only [ChipRow.rowAccessTuples, ChipRow.clockComponents]
    apply toAccessTuples_pairwise _ _ (clk_low_val_lt h_cpu) _
      (zipped_off_bound _ _ h_off_bound) (zipped_off_desc _ _ h_off_desc))

/-! ### Inter-row Pairwise lemma

For two rows `r1, r2` with `r2.encodedClk + 8 ≤ r1.encodedClk`, every
access in `r1` has timestamp strictly greater than every access in `r2`.
The bound `8` corresponds to `clkIncrement` (SP1's per-row clock step);
in the discharge this is supplied by `TraceClkLink`. -/

/-- For any access tuple `x` in `row.rowAccessTuples`, the timestamp
`x.1` lies in `[row.encodedClk, row.encodedClk + 4]` under `cpuStateSpec`. -/
private lemma rowAccessTuples_timestamp_range
    (row : ChipRow p) (h_cpu : row.cpuStateSpec)
    (x : _root_.MemoryAccess) (hx : x ∈ row.rowAccessTuples) :
    row.encodedClk ≤ x.1 ∧ x.1 ≤ row.encodedClk + 4 := by
  obtain ⟨h_off_bound, _⟩ := chipRow_offsets_props row
  cases row <;> (
    simp only [ChipRow.rowAccessTuples, ChipRow.clockComponents] at hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he_mem, rfl⟩ := hx
    have h_off : e.2.val ≤ 4 := zipped_off_bound _ _ h_off_bound _ he_mem
    rw [toAccessTuple_fst_eq _ _ _ _ _ (clk_low_val_lt h_cpu) h_off]
    simp only [ChipRow.encodedClk, ChipRow.clockComponents]
    refine ⟨by omega, by omega⟩)

/-- Inter-row timestamp comparison: every tuple of the later row has
strictly higher timestamp than every tuple of the earlier row, given
the encoded-clock separation. -/
private lemma rowAccessTuples_inter_of_link
    (r1 r2 : ChipRow p) (h_cpu1 : r1.cpuStateSpec) (h_cpu2 : r2.cpuStateSpec)
    (h_link : r2.encodedClk + 8 ≤ r1.encodedClk) :
    ∀ x ∈ r1.rowAccessTuples, ∀ y ∈ r2.rowAccessTuples, timestamp_ordering x y := by
  intro x hx y hy
  have hx_range := rowAccessTuples_timestamp_range r1 h_cpu1 x hx
  have hy_range := rowAccessTuples_timestamp_range r2 h_cpu2 y hy
  change y.1 < x.1
  omega

/-! ### Top-level discharge -/

/-- Discharge of `TraceClkValid` from per-row chip `Spec`s plus a
chronological clock-link hypothesis. Mirrors
`traceIsRealBinary_of_chip_specs`. -/
theorem traceClkValid_of_chip_specs
    (rows : List (ChipRow p))
    (h_specs : ∀ row ∈ rows, ChipRow.Spec row)
    (h_link : TraceClkLink rows 8) :
    TraceClkValid rows := by
  refine ⟨?_, ?_⟩
  · intro row h_mem
    exact rowAccessTuples_pairwise_of_cpuStateSpec row
      (cpuStateSpec_of_chipRow_spec row (h_specs row h_mem))
  · refine List.Pairwise.imp_of_mem ?_ h_link
    intro r1 r2 h_r1_mem h_r2_mem h_sep
    have hr1 := h_specs r1 (List.mem_reverse.mp h_r1_mem)
    have hr2 := h_specs r2 (List.mem_reverse.mp h_r2_mem)
    exact rowAccessTuples_inter_of_link r1 r2
      (cpuStateSpec_of_chipRow_spec r1 hr1)
      (cpuStateSpec_of_chipRow_spec r2 hr2)
      h_sep

end TraceClkValidDischarge

end SP1Clean.Soundness
