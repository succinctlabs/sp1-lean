import SP1Clean.Faithful.AddChip
import SP1CleanTest.TraceGenTests.TraceGenerator
import SP1CleanTest.TraceGenTests.AddChipTraceVectors

/-! # Whole-trace conformance anchor for `AddChip` — the circuit IS the trace generator.

`addChipDerivedTrace` rebuilds SP1's `AddChip` trace **from the chip's own circuit**: for every
dumped event, `EventPopulate.rTypeEventInputs` mirrors the input-column extraction (the only
hand-written part of SP1's `generate_trace`), and `circuitTraceRow` derives the rest — the
witnessed `add_operation.value` columns by evaluating `main`'s own witness-IR program
(`AddOperation.populateIR`, tied to `populate` by `populateIR_eval`), and the 33-column Rust layout through the audited whole-row
`addChipReconfigure` map — then zero padding rows mirror SP1's zero-fill. The anchor checks the
derived matrix equals the dumped one cell-for-cell, covering witness formulas, environment wiring,
emission order, the full native Add row column layout, and padding in a single `native_decide`
(confined here per the WitnessTests convention; `circuitTraceRow` itself is axiom-clean). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- The `AddChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def addChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e => circuitTraceRowMapped AddChip.Inputs (AddChip.main (p := SP1Prime))
      Faithful.addChipReconfigure (rTypeEventInputs e))
    AddChipTraceEvents AddChipTraceHeight 33

theorem addchip_trace_conforms :
    (addChipDerivedTrace == AddChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
