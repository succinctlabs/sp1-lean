import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.SubOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.SubChip
import SP1Clean.SubOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader

/-! # Chip-level `SubChip` mirror — R-type, operation-swap of `AddChip`

The R-type Sub chip: 33 columns, identical in shape to `SP1Clean.Add`
except for the operation fragment (`SubOp` instead of `AddOp`) and the
opcode index (`2` for `SUB` instead of `0` for `ADD`) flowing into
`RTypeReader`.
-/

namespace SP1Clean.Sub

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `SubCols<T>`. Identical
to `SP1Clean.Add.AddCols`. -/
structure SubCols (T : Type) where
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
  op_c : T
  op_c_memory_prev_value : Vector T 4
  op_c_memory_prev_low : T
  op_c_memory_diff_low : T
  op_a_write_value : Vector T 4
  is_real : T
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `SubChip::eval(builder, cols)`. -/
def main (cols : Var SubCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c, op_c_memory_prev_value, _op_c_memory_prev_low,
       _op_c_memory_diff_low, op_a_write_value, is_real⟩ := cols
  -- SubOperation: op_b_memory.prev_value - op_c_memory.prev_value = op_a_write_value.
  SP1Clean.SubOp.main op_b_memory_prev_value op_c_memory_prev_value op_a_write_value
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction (opcode = 2 = SUB; R-type discipline).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 2, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing assertZero gates.
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `SubCols (ZMod p)`. Uses the
helper Specs from `SP1Clean.SubOp`, `SP1Clean.CPUState`, and
`SP1Clean.RTypeReader`. Opcode index `2` (`SUB`) flows into the
RTypeReader fragment. -/
def Spec (cols : SubCols (ZMod p)) : Prop :=
  SP1Clean.SubOp.Spec
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) 2 cols.pc
      cols.op_a_write_value
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
                diff_low_limb := cols.op_c_memory_diff_low } } } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0

/-- Project a raw SP1 row into the structured `SubCols` view. Mirrors the
index map in `SP1Chips/Sub/Constraints.lean`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : SubCols (ZMod p) :=
  ⟨Main[0], Main[1], Main[2],
   #v[Main[3], Main[4], Main[5]],
   Main[6],
   #v[Main[7], Main[8], Main[9], Main[10]],
   Main[11], Main[12], Main[13], Main[14],
   #v[Main[15], Main[16], Main[17], Main[18]],
   Main[19], Main[20], Main[21],
   #v[Main[22], Main[23], Main[24], Main[25]],
   Main[26], Main[27],
   #v[Main[28], Main[29], Main[30], Main[31]],
   Main[32]⟩

/-- The chip-level bridge: SP1's `allHold_poly` over the flat row
`Sub.constraints Main` is exactly `Spec (fromMain Main)`, under
`is_real = Main[32] = 1`. -/
theorem iff_sp1
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Sub.constraints Main).allHold_poly ↔ Spec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, Spec, SP1Clean.SubOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec]
  rw [show (_root_.Sub.constraints Main).allHold_poly ↔
        ((SubOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[22], Main[23], Main[24], Main[25]]
            { value := #v[Main[28], Main[29], Main[30], Main[31]] }
            Main[32]).allHold_poly ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[32]).allHold_poly ∧
          (RTypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 2
            #v[Main[28], Main[29], Main[30], Main[31]]
            { op_a := Main[6],
              op_a_memory :=
                { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                  access_timestamp :=
                    { prev_low := Main[11], diff_low_limb := Main[12] } },
              op_a_0 := Main[13], op_b := Main[14],
              op_b_memory :=
                { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                  access_timestamp :=
                    { prev_low := Main[19], diff_low_limb := Main[20] } },
              op_c := Main[21],
              op_c_memory :=
                { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                  access_timestamp :=
                    { prev_low := Main[26], diff_low_limb := Main[27] } } }
            Main[32] Main[32]).allHold_poly ∧
          (Main[32] * (Main[32] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Sub.constraints, SP1ConstraintList.allHold_poly,
        List.forall_append, List.Forall, SP1Constraint.toProp_poly]]
  rw [h_is_real]
  rw [SubOperation.allHold_constraints_iff_poly,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

/-- Clean-side `correct_sub`: same Sail equivalence statement as SP1's
`Sub.correct_sub`, but with the constraint hypothesis re-expressed against
the Clean-flavored `Spec` predicate over a structured `SubCols` view.
Pure composition with the SP1 proof via `iff_sp1.mpr`. -/
theorem correct_sub
    (Main : Vector (ZMod p) 33) (s : SailState)
    (h_is_real : Main[32] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Sub.constraints Main).initialState_poly s) :
    let op_c := _root_.Sub.sp1_op_c Main
    let op_b := _root_.Sub.sp1_op_b Main
    let op_a := _root_.Sub.sp1_op_a Main
    (_root_.Sub.spec_sub (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Sub.sp1_sub Main).run s :=
  _root_.Sub.correct_sub Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    h_is_real state_cstrs

end SP1Clean.Sub
