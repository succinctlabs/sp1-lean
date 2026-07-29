import SP1Clean.Faithful.SubChip
import SP1CleanTest.TraceGenTests.TraceGenerator
import SP1CleanTest.TraceGenTests.SubChipTraceVectors

/-! # Whole-trace conformance anchor for `SubChip` — the circuit IS the trace generator.

The `AddChipTraceWitness` derivation on the SUB clone: for every dumped event,
`EventPopulate.rTypeEventInputs` mirrors the input-column extraction, and `circuitTraceRow`
derives the rest — the witnessed `sub_operation.value` columns from `main`'s own `witnessVector`
closure (which calls `SubOperation.populate`, the wrapping `rs1 - rs2`), and the 33-column Rust row
layout through the audited whole-row `subChipReconfigure` map — then zero padding rows mirror SP1's
zero-fill. The anchor checks the derived matrix equals the dumped one cell-for-cell (unmasked). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- The `SubChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def subChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e => circuitTraceRowMapped SubChip.Inputs (SubChip.main (p := SP1Prime))
      Faithful.subChipReconfigure (rTypeEventInputs e))
    SubChipTraceEvents SubChipTraceHeight 33

theorem subchip_trace_conforms :
    (subChipDerivedTrace == SubChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
