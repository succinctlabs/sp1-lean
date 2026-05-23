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
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Addw.AddwChip
import SP1Clean.AddwOperation
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Reader.OperandAccess

/-! # Chip-level `AddwChip` mirror — 32-bit ALU-type add with sign-extension

The Addw chip bundles two RV64IM variants (`addw` R-type and `addiw`
I-type) into a single 36-column trace, distinguished by the shared
`ALUTypeReader`'s `imm_c` flag at `Main[31]`. The 32-bit result is
stored in two limbs (`Main[32..33]`) plus a `msb` column (`Main[34]`)
that seeds the high-bit decomposition; the 4-limb `op_a_write_value`
fed into the reader is reconstructed as `[addw_value[0], addw_value[1],
msb * 65535, msb * 65535]`.

Layout mirrors `SP1Clean.Bitwise` for ALU-type discipline and
`SP1Clean.Sub.W` for the 2-limb + msb operation shape. -/

namespace SP1Clean.Addw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `AddwCols<T>`. -/
structure AddwCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  addw_value : Vector T 2
  addw_msb : T
  is_real : T
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `AddwChip::eval(builder, cols)`. -/
def main (cols : Var AddwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩, addw_value, addw_msb, is_real,
       _next_pc_carry_value⟩ := cols
  -- AddwOperation: op_b_memory.prev_value + op_c_memory.prev_value = addw_value (low 32 bits).
  SP1Clean.AddwOp.main op_b_memory.prev_value op_c_memory.prev_value addw_value addw_msb
  -- CPUState range lookups (clk_0_16 progression + clk_16_24 U8 bound).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 19 = ADDW; imm_c toggles R/I-type
  -- at the reader level — when imm_c = 0 op_c is a single-limb register
  -- index with limbs 1..3 zero, when imm_c = 1 op_c carries a 4-limb
  -- immediate).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 19, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing assertZero gates.
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `AddwCols (ZMod p)`. Opcode
index `19` (`ADDW`) flows into the ALUTypeReader fragment; the
`op_a_write_value` is the 4-limb reconstruction
`[addw_value[0], addw_value[1], addw_msb * 65535, addw_msb * 65535]`. -/
def Spec (cols : AddwCols (ZMod p)) : Prop :=
  SP1Clean.AddwOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      { value := cols.addw_value, msb := { msb := cols.addw_msb } } ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 19 cols.state.pc
      #v[cols.addw_value[0], cols.addw_value[1],
         cols.addw_msb * 65535, cols.addw_msb * 65535]
      { op_a := cols.adapter.op_a,
        op_a_memory :=
          { prev_value := cols.adapter.op_a_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } },
        op_a_0 := cols.adapter.op_a_0, op_b := cols.adapter.op_b,
        op_b_memory :=
          { prev_value := cols.adapter.op_b_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } },
        op_c := cols.adapter.op_c,
        op_c_memory :=
          { prev_value := cols.adapter.op_c_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } },
        imm_c := cols.adapter.imm_c } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- Project a raw SP1 row into the structured `AddwCols` view. Mirrors the
index map in `SP1Chips/Addw/Constraints.lean`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 36) : AddwCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   #v[Main[32], Main[33]],
   Main[34], Main[35], #v[0, 0, 0]⟩

/-- The chip-level bridge: SP1's `allHold` over the flat row
`Addw.constraints Main` is exactly `Spec (fromMain Main)`, under
`is_real = Main[35] = 1`. -/
theorem iff_sp1
    (Main : Vector (ZMod p) 36) (h_is_real : Main[35] = 1) :
    (_root_.Addw.constraints Main).allHold ↔ Spec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, Spec, SP1Clean.AddwOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.ALUTypeReader.aluTypeReaderSpec]
  rw [show (_root_.Addw.constraints Main).allHold ↔
        ((AddwOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[25], Main[26], Main[27], Main[28]]
            { value := #v[Main[32], Main[33]], msb := { msb := Main[34] } }
            Main[35]).allHold ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[35]).allHold ∧
          (ALUTypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 19
            #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535]
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
              op_c := #v[Main[21], Main[22], Main[23], Main[24]],
              op_c_memory :=
                { prev_value := #v[Main[25], Main[26], Main[27], Main[28]],
                  access_timestamp :=
                    { prev_low := Main[29], diff_low_limb := Main[30] } },
              imm_c := Main[31] }
            Main[35] Main[35]).allHold ∧
          (Main[35] * (Main[35] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Addw.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [AddwOperation.allHold_constraints_iff,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.ALUTypeReader.aluTypeReaderSpec_iff_sp1]
  simp [SP1Clean.AddwOp.Spec, SP1Clean.CPUState.cpuStateSpec,
    SP1Clean.ALUTypeReader.aluTypeReaderSpec, and_assoc]

/-- Clean-side `correct_addw`: ADDW R-type case (`imm_c = 0`). -/
theorem correct_addw
    (Main : Vector (ZMod p) 36) (s : SailState)
    (h_is_real : Main[35] = 1) (h_is_addw : Main[31] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Addw.constraints Main).initialState s) :
    let op_c := _root_.Addw.sp1_op_c Main
    let op_b := _root_.Addw.sp1_op_b Main
    let op_a := _root_.Addw.sp1_op_a Main
    (_root_.Addw.spec_addw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Addw.sp1_addw Main).run s :=
  _root_.Addw.correct_addw Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    h_is_real h_is_addw state_cstrs

/-- Clean-side `correct_addiw`: ADDIW I-type case (`imm_c = 1`). -/
theorem correct_addiw
    (Main : Vector (ZMod p) 36) (s : SailState)
    (h_is_real : Main[35] = 1) (h_is_addiw : Main[31] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Addw.constraints Main).initialState s) :
    let op_c := _root_.Addiw.sp1_op_c Main
    let op_b := _root_.Addiw.sp1_op_b Main
    let op_a := _root_.Addiw.sp1_op_a Main
    (_root_.Addiw.spec_addiw op_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Addw.sp1_addw Main).run s :=
  _root_.Addiw.correct_addw Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    h_is_real h_is_addiw state_cstrs

/-! ## Full `FormalAssertion` promotion

Wraps the chip's lookup surface (CPUState + ProgramTable subcircuits +
trailing asserts) into a Clean `FormalAssertion`. The `FormalSpec`
drops both the `AddwOp` carry chain and the `aluTypeReaderSpec`
register-read content (neither has a Clean `FormalAssertion` wrapper
yet, and `Assertion.main` does not emit those lookups). Matches the
Bitwise multi-variant precedent. -/

namespace Assertion

open Circuit ProvableType

/-- Refactored chip-level circuit using subcircuit composition. Emits
only the CPUState and ProgramTable subcircuits plus the two trailing
assertZero gates — the AddwOp byte lookups are not promoted here. -/
@[reducible]
def main (cols : Var AddwCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩, _addw_value, _addw_msb, is_real,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 19, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type-shaped: op_a at +4, op_b at +3, op_c at +2 (the 4-limb op_c
  -- column doubles as I-type immediate; the op_c-memory triple
  -- characterises the register-read consequence either way).
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

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddwCols unit where
  name := "SP1Clean.Addw"
  main := main
  localLength _ := 0

def Assumptions (_ : AddwCols (ZMod p)) : Prop := True

/-- The byte and program lookup derivable subset of `Spec`. -/
def FormalSpec (cols : AddwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 19, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
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
          e17, e18, e19, e20, e21, e22⟩ := h_input
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
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

/-- The full Clean `FormalAssertion` for the byte and program lookup
derivable subset of `AddwChip`'s constraint surface. -/
def assertion : FormalAssertion (ZMod p) AddwCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addw
