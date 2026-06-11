import SP1Clean.Chips.AddwChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.AddwChipTraceVectors

/-! # Whole-trace conformance anchor for `AddwChip` — the first `ALUTypeReader` trace, unmasked.

Same derivation as `AddChipTraceWitness`, on the immediate-capable adapter: the 36-column
`AddwCols` layout carries an `ALUTypeReader` (the `op_c` slot is a `Word` + access block + `imm_c`
flag), mirrored by `EventPopulate.aluTypeEventInputs` / `aluTypeReaderPopulate`. The dumped
battery is register-`c` ADDW events (`op_c = [7, 0, 0, 0]`, the register-index word; the operand
is the `op_c_memory.prev_value` read). The witnessed block is the W-result pair
(`AddwOperation.addwValueWitness` low limbs + `addwMsbWitness` sign bit); the anchor checks the
derived matrix equals SP1's real `generate_trace` dump cell-for-cell (unmasked). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- The `AddwChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def addwChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRow AddwChip.Inputs (AddwChip.main (p := SP1Prime)) (aluTypeEventInputs e))
    AddwChipTraceEvents AddwChipTraceHeight 36

theorem addwchip_trace_conforms :
    (addwChipDerivedTrace == AddwChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
