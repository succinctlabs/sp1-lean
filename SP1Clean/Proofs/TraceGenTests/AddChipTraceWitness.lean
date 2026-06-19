import SP1Clean.Native.Chips.AddChip.Defs
import SP1Clean.Proofs.TraceGenTests.TraceGenerator
import SP1Clean.Proofs.TraceGenTests.AddChipTraceVectors

/-! # Whole-trace conformance anchor for `AddChip` — the circuit IS the trace generator.

`addChipDerivedTrace` rebuilds SP1's `AddChip` trace **from the chip's own circuit**: for every
dumped event, `EventPopulate.rTypeEventInputs` mirrors the input-column extraction (the only
hand-written part of SP1's `generate_trace`), and `circuitTraceRow` derives the rest — the
witnessed `add_operation.value` columns from `main`'s own `witnessVector` closure (which calls
`AddOperation.populate`), and the 33-column row layout from `main`'s output struct — then zero
padding rows mirror SP1's zero-fill. The anchor checks the derived matrix equals the dumped one
cell-for-cell, covering witness formulas, environment wiring, emission order, the full `AddCols`
column layout, and padding in a single `native_decide` (confined here per the WitnessTests
convention; `circuitTraceRow` itself is axiom-clean). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- The `AddChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def addChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e => circuitTraceRow AddChip.Inputs (AddChip.main (p := SP1Prime)) (rTypeEventInputs e))
    AddChipTraceEvents AddChipTraceHeight 33

theorem addchip_trace_conforms :
    (addChipDerivedTrace == AddChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
