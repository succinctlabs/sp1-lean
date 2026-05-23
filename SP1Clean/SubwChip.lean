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
import SP1Operations.Operation.SubwOperation.SubwOperation
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Subw.SubwChip
import SP1Clean.SubwOperation
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Reader.OperandAccess

/-! # Chip-level `SubwChip` mirror — 32-bit R-type subtract with sign-extension

The R-type Subw chip: 32 columns, composes `SP1Clean.SubwOp` with
`CPUState` and `RTypeReader` Spec helpers. The 32-bit result is stored in
two limbs (`Main[28]`, `Main[29]`) plus a `msb` column (`Main[30]`) that
both seeds the high-bit decomposition and drives the sign-extension limbs
fed into the RTypeReader's `op_a_write_value` (limbs 2-3 reconstructed as
`msb * 65535`).
-/

namespace SP1Clean.Sub

open Circuit ProvableType

namespace W

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `SubwCols<T>`. -/
structure SubwCols (T : Type) where
  state : CPUState T
  op_a : T
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T
  op_b : T
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T
  op_c_memory : MemoryAccessInSharedCols T
  subw_value : Vector T 2
  subw_msb : T
  is_real : T
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `SubwChip::eval(builder, cols)`. -/
def main (cols : Var SubwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a, _op_a_memory, op_a_0, op_b,
       op_b_memory,
       op_c, op_c_memory, subw_value, subw_msb, is_real,
       _next_pc_carry_value⟩ := cols
  -- SubwOperation: op_b_memory.prev_value - op_c_memory.prev_value = subw_value (low 32 bits).
  SP1Clean.SubwOp.main op_b_memory.prev_value op_c_memory.prev_value subw_value subw_msb
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction (opcode = 20 = SUBW; R-type discipline).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 20, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing assertZero gates.
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `SubwCols (ZMod p)`. Opcode
index `20` (`SUBW`) flows into the RTypeReader fragment; the
`op_a_write_value` passed to the reader is the 4-limb reconstruction
`[subw_value[0], subw_value[1], subw_msb * 65535, subw_msb * 65535]`. -/
def Spec (cols : SubwCols (ZMod p)) : Prop :=
  SP1Clean.SubwOp.Spec
      cols.op_b_memory.prev_value cols.op_c_memory.prev_value
      { value := cols.subw_value, msb := { msb := cols.subw_msb } } ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 20 cols.state.pc
      #v[cols.subw_value[0], cols.subw_value[1],
         cols.subw_msb * 65535, cols.subw_msb * 65535]
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory.access_timestamp.prev_low,
                diff_low_limb := cols.op_a_memory.access_timestamp.diff_low_limb } },
        op_a_0 := cols.op_a_0, op_b := cols.op_b,
        op_b_memory :=
          { prev_value := cols.op_b_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.op_b_memory.access_timestamp.prev_low,
                diff_low_limb := cols.op_b_memory.access_timestamp.diff_low_limb } },
        op_c := cols.op_c,
        op_c_memory :=
          { prev_value := cols.op_c_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.op_c_memory.access_timestamp.prev_low,
                diff_low_limb := cols.op_c_memory.access_timestamp.diff_low_limb } } } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0

/-- Project a raw SP1 row into the structured `SubwCols` view. Mirrors the
index map in `SP1Chips/Subw/Constraints.lean`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 32) : SubwCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      Main[6],
   ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩, Main[13], Main[14],
   ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩, Main[21],
   ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩,
   #v[Main[28], Main[29]],
   Main[30], Main[31], #v[0, 0, 0]⟩

/-- The chip-level bridge: SP1's `allHold` over the flat row
`Subw.constraints Main` is exactly `Spec (fromMain Main)`, under
`is_real = Main[31] = 1`. -/
theorem iff_sp1
    (Main : Vector (ZMod p) 32) (h_is_real : Main[31] = 1) :
    (_root_.Subw.constraints Main).allHold ↔ Spec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, Spec, SP1Clean.SubwOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec]
  rw [show (_root_.Subw.constraints Main).allHold ↔
        ((SubwOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[22], Main[23], Main[24], Main[25]]
            { value := #v[Main[28], Main[29]], msb := { msb := Main[30] } }
            Main[31]).allHold ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[31]).allHold ∧
          (RTypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 20
            #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535]
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
            Main[31] Main[31]).allHold ∧
          (Main[31] * (Main[31] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Subw.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [SubwOperation.allHold_constraints_iff,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.SubwOp.Spec, SP1Clean.CPUState.cpuStateSpec,
    SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

/-- Clean-side `correct_subw`: same Sail equivalence statement as SP1's
`Subw.correct_subw`, but with the constraint hypothesis re-expressed
against the Clean-flavored `Spec` predicate over a structured `SubwCols`
view. Pure composition with the SP1 proof via `iff_sp1.mpr`. -/
theorem correct_subw
    (Main : Vector (ZMod p) 32) (s : SailState)
    (h_is_real : Main[31] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Subw.constraints Main).initialState s) :
    let op_c := _root_.Subw.sp1_op_c Main
    let op_b := _root_.Subw.sp1_op_b Main
    let op_a := _root_.Subw.sp1_op_a Main
    (_root_.Subw.spec_subw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Subw.sp1_subw Main).run s :=
  _root_.Subw.correct_subw Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    h_is_real state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2 design)

Mirrors `SP1Clean.Addw.Assertion`: drops `SubwOp.main` from
`Assertion.main`, so the FormalSpec covers `CPUState`, `ProgramTable`,
and boolean asserts only. The SubwOp 32-bit-with-MSB surface continues
to be carried by the legacy chip-level `Spec` / `iff_sp1` / `correct_subw`
route. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var SubwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a, op_a_memory, op_a_0, op_b,
       op_b_memory,
       op_c, op_c_memory, _subw_value, _subw_msb, is_real,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 20 = SUBW; R-type discipline).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 20, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type offsets: op_a at +4, op_b at +3, op_c at +2.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low, op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubwCols unit where
  name := "SP1Clean.Subw"
  main := main
  localLength _ := 0

def Assumptions (_ : SubwCols (ZMod p)) : Prop := True

def FormalSpec (cols : SubwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 20, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 0 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.op_a_memory.access_timestamp.prev_low, cols.op_a_memory.access_timestamp.diff_low_limb,
     cols.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.op_b_memory.access_timestamp.prev_low, cols.op_b_memory.access_timestamp.diff_low_limb,
     cols.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.op_c_memory.access_timestamp.prev_low, cols.op_c_memory.access_timestamp.diff_low_limb,
     cols.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_oa_a, h_oa_b, h_oa_c,
          h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩
  · linear_combination h_isreal
  · exact h_op_a_0

end Assertion

def assertion : FormalAssertion (ZMod p) SubwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end W
end SP1Clean.Sub
