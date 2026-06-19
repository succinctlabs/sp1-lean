import SP1Clean.Native.Chips.SubwChip.Defs
import SP1Clean.Proofs.TraceGenTests.TraceGenerator
import SP1Clean.Proofs.TraceGenTests.SubwChipTraceVectors

/-! # Whole-trace conformance anchor for `SubwChip` — a W-instruction trace, fully unmasked.

Same derivation as `AddChipTraceWitness`, on a chip whose witnessed block is **not** a plain
result word: `SubwChip.main` witnesses the two low result limbs (`SubwOperation.subwValueWitness`,
the wrapping 32-bit `rs1 - rs2`) and the sign bit (`subwMsbWitness`) separately, and the 32-column
`SubwCols` layout — state, `RTypeReader` adapter, `{value₀, value₁, msb}`, `is_real` — comes from
`main`'s output struct. The anchor checks the derived matrix equals SP1's real `generate_trace`
dump cell-for-cell (unmasked), covering the sign-extension witness path the Add/Sub anchors
don't exercise. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- The `SubwChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def subwChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e => circuitTraceRow SubwChip.Inputs (SubwChip.main (p := SP1Prime)) (rTypeEventInputs e))
    SubwChipTraceEvents SubwChipTraceHeight 32

theorem subwchip_trace_conforms :
    (subwChipDerivedTrace == SubwChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
