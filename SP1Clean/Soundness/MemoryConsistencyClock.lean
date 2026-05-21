import SP1Clean.Soundness.MemoryConsistency

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

end SP1Clean.Soundness
