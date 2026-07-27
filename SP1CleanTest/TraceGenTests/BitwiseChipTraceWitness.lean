import SP1Clean.Faithful.BitwiseChip
import SP1CleanTest.TraceGenTests.TraceGenerator
import SP1CleanTest.TraceGenTests.BitwiseChipTraceVectors

/-! # Whole-trace conformance anchor for `BitwiseChip` — hint-driven flags, unmasked.

Every row is rebuilt from `BitwiseChip.main`'s own witness closures (the `"bitwise_flags"` hint
flags and the 16-column `BitwiseU16Operation` struct via `BitwiseU16Operation.populate` at the
flag-weighted byte opcode) plus the output-struct layout (reaching the Rust 51-column `BitwiseCols` order through the
audited whole-row `bitwiseChipReconfigure` map), with `bitwiseHint` building the
per-event flag `ProverHint` from the dumped executor opcode (XOR = 3, OR = 4, AND = 5 — the same
discriminants the circuit's reader opcode expression uses). The battery cycles **all three
variants** (register-`c`) and the comparison is **unmasked** (all 51 columns) — closing the
former masked-flags scope gap. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- Per-event flag hint: the `"bitwise_flags"` one-hot from the dumped executor opcode. -/
def bitwiseHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "bitwise_flags", 3 =>
    #[#v[if op = 3 then 1 else 0, if op = 4 then 1 else 0, if op = 5 then 1 else 0]]
  | _, _ => #[]

/-- The `BitwiseChip` trace derived from the circuit: one `circuitTraceRow` per dumped event (flag
hint from the event's opcode), zero padding to SP1's height. -/
def bitwiseChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRowMapped BitwiseChip.Inputs (BitwiseChip.main (p := SP1Prime))
        Faithful.bitwiseChipReconfigure (aluTypeOpEventInputs e) (bitwiseHint e.opcode))
    BitwiseChipTraceEvents BitwiseChipTraceHeight 51

theorem bitwisechip_trace_conforms :
    (bitwiseChipDerivedTrace
      == BitwiseChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
