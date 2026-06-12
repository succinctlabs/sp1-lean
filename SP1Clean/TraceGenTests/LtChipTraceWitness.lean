import SP1Clean.Chips.LtChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.LtChipTraceVectors

/-! # Whole-trace conformance anchor for `LtChip` — hint-driven flags, unmasked.

Every row is rebuilt from `LtChip.main`'s own witness closures (the `"lt_flags"` hint flags and
the `LtOperationSigned` column block via `LtOperationSigned.populate` at `is_signed = is_slt`)
plus the output-struct layout, with `ltHint` building the per-event flag `ProverHint` from the
dumped executor opcode (SLT = 9, SLTU = 10). The battery cycles **both variants**, immediate-`c`
rows only (on register-`c` rows the chip's compare operand `adapter.op_c` is the register-index
word rather than the read value — a documented adapter-projection scope gap, independent of the
flags), and the comparison is **unmasked** (all 44 columns). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- Per-event flag hint: the `"lt_flags"` one-hot from the dumped executor opcode. -/
def ltHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "lt_flags", 2 => #[#v[if op = 9 then 1 else 0, if op = 10 then 1 else 0]]
  | _, _ => #[]

/-- The `LtChip` trace derived from the circuit: one `circuitTraceRow` per dumped event (flag
hint from the event's opcode), zero padding to SP1's height. -/
def ltChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRow LtChip.Inputs (LtChip.main (p := SP1Prime))
        (aluTypeOpEventInputs e) (ltHint e.opcode))
    LtChipTraceEvents LtChipTraceHeight 44

theorem ltchip_trace_conforms :
    (ltChipDerivedTrace == LtChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
