import SP1Clean.Faithful.DivRemChip
import SP1CleanTest.TraceGenTests.TraceGenerator
import SP1CleanTest.TraceGenTests.DivRemChipTraceVectors

/-! # Whole-trace conformance anchor for `DivRemChip` — hint-driven flags, unmasked.

Every row is rebuilt from `DivRemChip.main`'s own witness closures (the eight `"div_rem_flags"`
hint flags, the `quotBits`/`remBits` division core, the gated `MulOperation`/`IsEqualWord`/
`AddOperation`/`LtOperationUnsigned` structs, the carry chain) plus the output-struct layout, with
`EventPopulate.rTypeOpEventInputs` mirroring the event → input extraction and `divRemHint` building
the per-event flag `ProverHint` from the dumped executor opcode (DIV = 15, DIVU = 16, REM = 17,
REMU = 18, DIVW = 25, DIVUW = 26, REMW = 27, REMUW = 28 — note the flag-slot order is
`[div, divu, rem, remu, divw, remw, divuw, remuw]`, so slot 5 carries REMW = 27 and slot 6
DIVUW = 26). The battery cycles **all eight variants** with forced divisor-zero rows (the
W-variants with a zero-low-32/nonzero-high `c`) and the signed-overflow patterns, and the
comparison is **unmasked** (all 246 columns).

SP1's padding rows are **not** all-zero (`mod.rs:549-569` — "0 divided by 1"): `is_divu = 1`,
`op_c_memory.prev_value = Word(1)`, `c[0] = abs_c[0] = max_abs_c_or_1[0] = 1`,
`b_not_neg_not_overflow = 1`, and `is_c_0.populate(1)`. The derived `divRemPadRow` reproduces it
from the synthetic padding **input** (all-zero except the `op_c` read = 1) with the **empty hint**
(whose `hintFlags` default is exactly the `is_divu` template). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- Per-event flag hint: the `"div_rem_flags"` one-hot from the dumped executor opcode. -/
def divRemHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "div_rem_flags", 8 =>
    #[#v[if op = 15 then 1 else 0, if op = 16 then 1 else 0, if op = 17 then 1 else 0,
         if op = 18 then 1 else 0, if op = 25 then 1 else 0, if op = 27 then 1 else 0,
         if op = 26 then 1 else 0, if op = 28 then 1 else 0]]
  | _, _ => #[]

/-- The synthetic padding input: all-zero except the `op_c` register read
(`adapter.op_c_memory.prev_value[0]`, flat index `1 + 6 + 16 = 23`) `= 1` — SP1's padded rows
divide 0 by 1. -/
def divRemPadInputs : List (ZMod SP1Prime) :=
  (List.replicate 29 0).set 23 1

/-- The derived padding row: the circuit's witness closures on the padding input with the empty
hint (default flags = the `is_divu` template). -/
def divRemPadRow : List (ZMod SP1Prime) :=
  circuitTraceRowMapped DivRemChip.Inputs (DivRemChip.main (p := SP1Prime))
    Faithful.divRemChipReconfigure divRemPadInputs

/-- The `DivRemChip` trace derived from the circuit: one `circuitTraceRow` per dumped event (flag
hint from the event's opcode), template padding to SP1's height. -/
def divRemChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRowMapped DivRemChip.Inputs (DivRemChip.main (p := SP1Prime))
        Faithful.divRemChipReconfigure (rTypeOpEventInputs e) (divRemHint e.opcode))
    DivRemChipTraceEvents DivRemChipTraceHeight 246 divRemPadRow

theorem divremchip_trace_conforms :
    (divRemChipDerivedTrace
      == DivRemChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
