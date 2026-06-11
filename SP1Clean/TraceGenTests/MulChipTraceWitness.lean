import SP1Clean.Chips.MulChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.MulChipTraceVectors

/-! # Whole-trace conformance anchor for `MulChip` (scoped: MUL/MULHU, masked flags/`a`).

Same derivation as `AddChipTraceWitness`: every row is rebuilt from `MulChip.main`'s own witness
closures (`flags`, the 45-column `MulOperation` struct via `MulOperation.populate`, the `a` word)
plus the output-struct layout, with `EventPopulate.rTypeEventInputs` mirroring the event → input
extraction.

**Scope gap (deliberate):** the chip witnesses its five variant flags as constant zeros
(`Chips/MulChip/Defs.lean`, the `flags` `witnessVector`; completeness in `Formal.lean` relies on
that padding shape), so the derived flag columns — and the flag-weighted `a` word — cannot match
SP1's real one-hot rows. The dump therefore contains only **MUL / MULHU** events (whose
`is_mulh/is_mulhsu/is_mulw` inputs to `populate` are all zero, making the 45-column
`mul_operation` block identical to the zero-flag derivation), and the comparison masks columns
`28–31` (`a`) and `77–81` (flags) via `mulCheckedRanges`. Upgrading the flags to hint-driven
witnesses (`env.hint`) would close the gap and is tracked as a follow-up; everything else —
state, adapter, and the whole `mul_operation` block — is checked cell-for-cell. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- `MulCols` checked ranges: state+adapter `[0, 28)` and `mul_operation` `[32, 77)`; the masked
remainder is `a` `[28, 32)` and the five flags `[77, 82)` (see the module doc). -/
def mulCheckedRanges : List (ℕ × ℕ) := [(0, 28), (32, 77)]

/-- The `MulChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def mulChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e => circuitTraceRow MulChip.Inputs (MulChip.main (p := SP1Prime)) (rTypeEventInputs e))
    MulChipTraceEvents MulChipTraceHeight 82

theorem mulchip_trace_conforms :
    (mulChipDerivedTrace.map (keepCols mulCheckedRanges) ==
      MulChipTraceRows.map (fun r => keepCols mulCheckedRanges (r.toList.map toField))) = true := by
  native_decide

end SP1Clean.TraceGenTests
