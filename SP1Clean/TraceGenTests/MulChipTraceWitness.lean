import SP1Clean.Chips.MulChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.MulChipTraceVectors

/-! # Whole-trace conformance anchor for `MulChip` — hint-driven flags, unmasked.

Every row is rebuilt from `MulChip.main`'s own witness closures (the `"mul_flags"` hint flags, the
45-column `MulOperation` struct via `MulOperation.populate`, the flag-weighted `a` word) plus the
output-struct layout, with `EventPopulate.rTypeOpEventInputs` mirroring the event → input
extraction and `mulHint` building the per-event flag `ProverHint` from the dumped executor opcode
(MUL = 11, MULH = 12, MULHU = 13, MULHSU = 14, MULW = 24 — the same discriminants the circuit's
flag-weighted opcode expression uses). The battery cycles **all five variants** and the comparison
is **unmasked** (all 82 columns) — closing the former masked-flags scope gap. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- Per-event flag hint: the `"mul_flags"` one-hot from the dumped executor opcode. -/
def mulHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "mul_flags", 5 =>
    #[#v[if op = 11 then 1 else 0, if op = 12 then 1 else 0, if op = 13 then 1 else 0,
         if op = 14 then 1 else 0, if op = 24 then 1 else 0]]
  | _, _ => #[]

/-- The `MulChip` trace derived from the circuit: one `circuitTraceRow` per dumped event (flag
hint from the event's opcode), zero padding to SP1's height. -/
def mulChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRow MulChip.Inputs (MulChip.main (p := SP1Prime)) (rTypeOpEventInputs e)
        (mulHint e.opcode))
    MulChipTraceEvents MulChipTraceHeight 82

theorem mulchip_trace_conforms :
    (mulChipDerivedTrace == MulChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
