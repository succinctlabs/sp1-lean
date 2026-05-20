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
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.LtChip
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader

/-! # Chip-level `LtChip` mirror — bundled signed/unsigned compare

The Lt chip bundles four RV64I variants — `slt` / `sltu` (R-type) and
`slti` / `sltiu` (I-type) — into a single 44-column trace. Variants
distinguished by selectors `is_slt`/`is_sltu` (Main[32..33]) and
`imm_c` (Main[31]). The signed/unsigned distinction is carried into the
`LtOperationSigned` sub-fragment via `is_signed := Main[32]`.

Structural mirror discipline (Spec only). The `LtOperationSigned`
constraint clause is left in raw `allHold_poly` form — no Clean
operation wrapper yet for this Compare-family sub-fragment.

Opcode encoding: `is_slt * 9 + is_sltu * 10` (SLT=9, SLTU=10).
Result is a 1-bit boolean written into `op_a_write_value[0]` (via
`Main[34]`), with the other 3 limbs zero.
-/

namespace SP1Clean.Lt

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `LtCols<T>`. -/
structure LtCols (T : Type) where
  clk_high : T
  clk_16_24 : T
  clk_0_16 : T
  pc : Vector T 3
  op_a : T
  op_a_memory_prev_value : Vector T 4
  op_a_memory_prev_low : T
  op_a_memory_diff_low : T
  op_a_0 : T
  op_b : T
  op_b_memory_prev_value : Vector T 4
  op_b_memory_prev_low : T
  op_b_memory_diff_low : T
  op_c : Vector T 4
  op_c_memory_prev_value : Vector T 4
  op_c_memory_prev_low : T
  op_c_memory_diff_low : T
  imm_c : T
  is_slt : T
  is_sltu : T
  compare_bit : T
  u16_flags : Vector T 4
  not_eq_inv : T
  comparison_limbs : Vector T 2
  b_msb : T
  c_msb : T
deriving ProvableStruct

/-- Clean-side circuit. Emits CPUState range lookups, the program-bus
interaction (opcode = `is_slt * 9 + is_sltu * 10`), and the trailing
assertZero gates (the two opcode-selector booleans, the sum-boolean,
and the op_a_0 = 0 forcing). The `LtOperationSigned` sub-fragment
constraints are captured propositionally in `Spec` below. -/
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       _op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c, _op_c_memory_prev_value, _op_c_memory_prev_low,
       _op_c_memory_diff_low, imm_c, is_slt, is_sltu, compare_bit,
       _u16_flags, _not_eq_inv, _comparison_limbs, _b_msb, _c_msb⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_slt * 9 + is_sltu * 10,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  let _ := compare_bit
  -- Trailing assertZero gates.
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `LtCols (ZMod p)`. The
`LtOperationSigned` clause is left in raw `allHold_poly` form (it
internally fans out into `U16MSBOperation` and `LtOperationUnsigned`
sub-fragments). The chip-level `is_signed` argument is `is_slt`; the
chip-level `is_real` argument is `is_slt + is_sltu`. -/
def Spec (cols : LtCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_slt + cols.is_sltu
  let lt_cols : _root_.LtOperationSigned (ZMod p) :=
    { result :=
        { u16_compare_operation := { bit := cols.compare_bit },
          u16_flags := cols.u16_flags,
          not_eq_inv := cols.not_eq_inv,
          comparison_limbs := cols.comparison_limbs },
      b_msb := { msb := cols.b_msb },
      c_msb := { msb := cols.c_msb } }
  (_root_.LtOperationSigned.constraints (F := ZMod p)
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      lt_cols cols.is_slt is_real).allHold_poly ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536)
      (cols.is_slt * 9 + cols.is_sltu * 10) cols.pc
      #v[cols.compare_bit, 0, 0, 0]
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory_prev_low,
                diff_low_limb := cols.op_a_memory_diff_low } },
        op_a_0 := cols.op_a_0, op_b := cols.op_b,
        op_b_memory :=
          { prev_value := cols.op_b_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_b_memory_prev_low,
                diff_low_limb := cols.op_b_memory_diff_low } },
        op_c := cols.op_c,
        op_c_memory :=
          { prev_value := cols.op_c_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_c_memory_prev_low,
                diff_low_limb := cols.op_c_memory_diff_low } },
        imm_c := cols.imm_c } ∧
  cols.is_slt * (cols.is_slt - 1) = 0 ∧
  cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
  (cols.is_slt + cols.is_sltu) * (cols.is_slt + cols.is_sltu - 1) = 0 ∧
  cols.op_a_0 = 0

/-- The op_a / op_b / op_c register accesses, exposed for trace-level
OfflineMemory aggregation. op_a writes the 4-limb boolean result
`#v[compare_bit, 0, 0, 0]`. -/
def opAMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory_prev_value,
    prev_low := cols.op_a_memory_prev_low,
    diff_low_limb := cols.op_a_memory_diff_low }

def opBMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_b, 0, 0],
    prev_value := cols.op_b_memory_prev_value,
    prev_low := cols.op_b_memory_prev_low,
    diff_low_limb := cols.op_b_memory_diff_low }

def opCMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_c[0], 0, 0],
    prev_value := cols.op_c_memory_prev_value,
    prev_low := cols.op_c_memory_prev_low,
    diff_low_limb := cols.op_c_memory_diff_low }

end SP1Clean.Lt
