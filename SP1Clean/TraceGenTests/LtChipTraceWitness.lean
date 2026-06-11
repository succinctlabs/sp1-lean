import SP1Clean.Chips.LtChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.LtChipTraceVectors

/-! # Whole-trace conformance anchor for `LtChip` (scoped: SLTU immediate-`c`, masked flags).

Same derivation as `AddChipTraceWitness` on the compare chip: every row is rebuilt from
`LtChip.main`'s own witness closures (the two variant flags and the 10-column `LtOperationSigned`
struct via its `populate` — the unsigned-compare block plus the two sign-bit columns), with
`EventPopulate.aluTypeEventInputs` mirroring the `ALUTypeReader` event → input extraction.

**Scope gaps (deliberate, the Mul/Bitwise pattern):**

1. the chip witnesses `is_slt`/`is_sltu` as constant zeros (`Chips/LtChip/Defs.lean`, the `flags`
   `witnessVector`), so the derived flag columns cannot match SP1's one-hot rows — and the
   gadget's mode selector `is_signed := is_slt` evaluates to `0` = **unsigned**. The dump
   therefore contains only SLTU events (whose real `is_signed` is also false, making the witnessed
   compare block identical on both sides — both sign-bit columns zero), and the comparison masks
   the two flag columns `32–33` via `ltCheckedRanges`;
2. the events are **immediate-`c`** (the executor's SLTIU shape): `LtChip`'s compare operand is
   `adapter.op_c` (`Inputs.op_c_val`), which on register-`c` rows is the register-index word
   rather than the read value — on immediate rows `op_c` *is* the operand value on both sides.

Hint-driven flags would close gap 1 (the same follow-up as MulChip); everything else — state,
adapter (including the immediate `op_c` block), and the whole compare block — is checked
cell-for-cell. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- `LtCols` checked ranges: state+adapter `[0, 32)` and `lt_operation` `[34, 44)`; the masked
remainder is the two variant flags `[32, 34)` (see the module doc). -/
def ltCheckedRanges : List (ℕ × ℕ) := [(0, 32), (34, 44)]

/-- The `LtChip` trace derived from the circuit: one `circuitTraceRow` per dumped event, zero
padding to SP1's height. -/
def ltChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e => circuitTraceRow LtChip.Inputs (LtChip.main (p := SP1Prime)) (aluTypeEventInputs e))
    LtChipTraceEvents LtChipTraceHeight 44

theorem ltchip_trace_conforms :
    (ltChipDerivedTrace.map (keepCols ltCheckedRanges) ==
      LtChipTraceRows.map (fun r => keepCols ltCheckedRanges (r.toList.map toField))) = true := by
  native_decide

end SP1Clean.TraceGenTests
