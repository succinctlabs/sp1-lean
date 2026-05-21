import SP1Foundations.Field

/-! # Per-row state-bus record

`StateAccess` mirrors SP1's `AirInteraction.state` shape (see
`SP1Foundations/Constraint.lean:9-22`): the clock components, the
current row's `pc`, the row's claimed `next_pc`, and the row's
`is_real` multiplicity gate.

The state bus is two-sided per row: each chip's CPUState reader emits
both a `receive (.state … pc)` and a `send (.state … next_pc)` with
`mult = is_real`. Trace-level consistency (this row's `next_pc` =
next row's `pc`, when both rows are real) is established in
`SP1Clean/Soundness/StateConsistency.lean`. -/

namespace SP1Clean

/-- The per-row state-bus record. Fields:
- `clk_high, clk_low` : the row's encoded clock components (matches
  `clockComponents` from `SP1Clean/Soundness/MemoryConsistency.lean`).
- `pc`                : the row's current 3-limb PC.
- `next_pc`           : the row's claimed next 3-limb PC. For arithmetic
  chips this is the chip's symbolic `pc + 4`; for jumps it is the
  chip's stored jump-target column (3 limbs; the 4th limb is asserted
  zero where applicable).
- `is_real`           : the SP1 row-validity multiplicity (gates every
  state-bus interaction). -/
structure StateAccess (F : Type) where
  clk_high : F
  clk_low  : F
  pc       : Vector F 3
  next_pc  : Vector F 3
  is_real  : F

end SP1Clean
