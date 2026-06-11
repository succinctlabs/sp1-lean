import SP1Clean.Chips.BitwiseChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.BitwiseChipTraceVectors

/-! # Whole-trace conformance anchor for `BitwiseChip` (scoped: AND only, masked flags).

Same derivation as `AddChipTraceWitness` on the byte-lookup chip: every row is rebuilt from
`BitwiseChip.main`'s own witness closures (the three variant flags and the 16-column
`BitwiseU16Operation` struct via its `populate` — the two low-byte decompositions plus the eight
result bytes), with `EventPopulate.aluTypeEventInputs` mirroring the `ALUTypeReader` event → input
extraction (register-`c` AND events).

**Scope gap (deliberate, the Mul/Lt pattern):** the chip witnesses its three variant flags as
constant zeros (`Chips/BitwiseChip/Defs.lean`, the `flags` `witnessVector`; completeness relies on
that padding shape), so the derived flag columns cannot match SP1's real one-hot rows — and the
gadget's `byte_opcode = is_xor·2 + is_or·1` evaluates to `0` = **AND**. The dump therefore
contains only AND events (whose real `byte_opcode` is also `0`, making the witnessed 16-column
block identical on both sides), and the comparison masks the three flag columns `48–50` via
`bitwiseCheckedRanges`. Hint-driven flags would close the gap (the same follow-up as MulChip);
everything else — state, adapter, and the whole bitwise block — is checked cell-for-cell. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- `BitwiseCols` checked ranges: everything except the three variant flags `[48, 51)`
(see the module doc). -/
def bitwiseCheckedRanges : List (ℕ × ℕ) := [(0, 48)]

/-- The `BitwiseChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def bitwiseChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRow BitwiseChip.Inputs (BitwiseChip.main (p := SP1Prime)) (aluTypeEventInputs e))
    BitwiseChipTraceEvents BitwiseChipTraceHeight 51

theorem bitwisechip_trace_conforms :
    (bitwiseChipDerivedTrace.map (keepCols bitwiseCheckedRanges) ==
      BitwiseChipTraceRows.map
        (fun r => keepCols bitwiseCheckedRanges (r.toList.map toField))) = true := by
  native_decide

end SP1Clean.TraceGenTests
