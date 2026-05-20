import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.JTypeReader
import SP1Chips.UTypeChip
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader

/-! # Chip-level `UTypeChip` mirror — bundled U-type (LUI/AUIPC)

The U-type chip bundles two RV64IM variants (`auipc` and `lui`) into a
single 31-column trace, distinguished by the `is_auipc` selector at
`Main[29]`. The chip's `AddOperation` adds a conditional addend
(`is_auipc * pc` — i.e., `pc` for AUIPC, `0` for LUI) to the 32-bit
immediate, producing the 64-bit value written to `op_a`.

Structural mirror discipline (same as JalChip / MulChip / ShiftLeftChip):
defines `UTypeCols`, `main`, and `Spec`; no `iff_sp1` / `correct_*`
bridges, no `FormalAssertion` promotion. The chip-level Spec composes
`AddOperation.constraints.allHold_poly` (kept in raw form because the
operation's is_real arg is the conditional `is_real - op_a_0`),
`cpuStateSpec`, `jtypeReaderSpec`, and the chip's selector + alignment
trailing asserts.
-/

namespace SP1Clean.UType

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `UTypeCols<T>`.
`pc_addend` is the conditional `is_auipc * pc` carried into the
AddOperation, and `add_result` is the 64-bit AddOp output written to
op_a. -/
structure UTypeCols (T : Type) where
  clk_high : T
  clk_16_24 : T
  clk_0_16 : T
  pc : Vector T 3
  op_a : T
  op_a_memory_prev_value : Vector T 4
  op_a_memory_prev_low : T
  op_a_memory_diff_low : T
  op_a_0 : T
  op_b_imm : Vector T 4
  op_c_imm : Vector T 4
  pc_addend : Vector T 3
  add_result : Vector T 4
  is_auipc : T
  is_real : T
deriving ProvableStruct

/-- Clean-side circuit. Emits CPUState range lookups (via subcircuit),
the program-bus interaction with the selector-weighted opcode
(`is_auipc * 48 + (1 - is_auipc) * 49` — AUIPC=48, LUI=49), and the
trailing assertZero gates (is_real boolean, is_auipc boolean, three
`pc_addend = is_auipc * pc` clauses, the `(is_real - 1) * op_a_0 = 0`
gate). The AddOperation sub-fragment (operating on `pc_addend` and
`op_b_imm`) is intentionally not emitted as a subcircuit — its
constraints are captured propositionally in `Spec` below. -/
def main (cols : Var UTypeCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b_imm,
       op_c_imm, pc_addend, _add_result, is_auipc, is_real⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_auipc * 48 + (1 - is_auipc) * 49,
      op_a, op_b_imm, op_c_imm,
      op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  is_auipc * (is_auipc - 1) === 0
  pc_addend[0] - is_auipc * pc[0] === 0
  pc_addend[1] - is_auipc * pc[1] === 0
  pc_addend[2] - is_auipc * pc[2] === 0
  (is_real - 1) * op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `UTypeCols (ZMod p)`. The
`AddOperation` clause is left in raw `allHold_poly` form (under
is_real arg `is_real - op_a_0`) because the iff lemma is only stated
for `is_real arg = 1`. -/
def Spec (cols : UTypeCols (ZMod p)) : Prop :=
  let opcode_e : ZMod p := cols.is_auipc * 48 + (1 - cols.is_auipc) * 49
  let addend : Word (ZMod p) :=
    #v[cols.pc_addend[0], cols.pc_addend[1], cols.pc_addend[2], 0]
  (_root_.AddOperation.constraints (F := ZMod p)
      addend cols.op_b_imm { value := cols.add_result }
      (cols.is_real - cols.op_a_0)).allHold_poly ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.JTypeReader.jtypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) opcode_e cols.pc
      cols.add_result
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory_prev_low,
                diff_low_limb := cols.op_a_memory_diff_low } },
        op_a_0 := cols.op_a_0,
        op_b_imm := cols.op_b_imm, op_c_imm := cols.op_c_imm } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.is_auipc * (cols.is_auipc - 1) = 0 ∧
  cols.pc_addend[0] - cols.is_auipc * cols.pc[0] = 0 ∧
  cols.pc_addend[1] - cols.is_auipc * cols.pc[1] = 0 ∧
  cols.pc_addend[2] - cols.is_auipc * cols.pc[2] = 0 ∧
  (cols.is_real - 1) * cols.op_a_0 = 0

/-- The op_a register access (read prior, write result), exposed for
trace-level OfflineMemory aggregation. `write_value` at aggregation
time is `cols.add_result`. -/
def opAMemoryAccess (cols : UTypeCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory_prev_value,
    prev_low := cols.op_a_memory_prev_low,
    diff_low_limb := cols.op_a_memory_diff_low }

end SP1Clean.UType
