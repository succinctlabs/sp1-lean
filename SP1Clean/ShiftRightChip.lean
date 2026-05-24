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
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.ShiftRight.ShiftRightChip
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.CPUState

/-! # Chip-level `ShiftRightChip` mirror — bundled 4-variant right shift

The ShiftRight chip bundles four RV64IM right-shift variants
(`srl`/`sra`/`srlw`/`sraw`) into a single 69-column trace, distinguished
by selectors at `Main[64..67]`. Same structural-mirror discipline as
`ShiftLeftChip`: shift-arithmetic content (bit-decomposition correctness,
shift power chain, byte-shift one-hot, limb-shift) is captured as a
placeholder `shiftSpec` (currently `True`).

Opcode encoding: SRL=7, SRA=8, SRLW=22, SRAW=23.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure ShiftRightCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  op_a_write_value : Vector T 4             -- Main[32..35] (= upstream `a : Word<T>`)
  -- Phase 3e: aux:28 decomposed into 11 named upstream sub-fields.
  -- Slot mapping verified against `SP1Chips/ShiftRight/Constraints.lean`
  -- (the U16MSBOperation calls at lines 191-197 pin Main[36]/[37], the
  -- bit-boolean asserts pin Main[38..43], the shift-pow chain E124-E135
  -- pins Main[45..47], the limb arithmetic pins Main[48..63]).
  b_msb : U16MSBOperation T                 -- Main[36]
  srw_msb : U16MSBOperation T               -- Main[37]
  c_bits : Vector T 6                       -- Main[38..43]
  sra_msb_v0123 : T                         -- Main[44]
  v_0123 : T                                -- Main[45]
  v_012 : T                                 -- Main[46]
  v_01 : T                                  -- Main[47]
  lower_limb : Vector T 4                   -- Main[48..51]
  higher_limb : Vector T 4                  -- Main[52..55]
  limb_result : Vector T 4                  -- Main[56..59]
  shift_u16 : Vector T 4                    -- Main[60..63]
  is_srl : T                                -- Main[64]
  is_sra : T                                -- Main[65]
  is_srlw : T                               -- Main[66]
  is_sraw : T                               -- Main[67]
  sign_extend : T                           -- Main[68]
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

def isRealExpr (cols : Var ShiftRightCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw

/-- Selector-weighted opcode: SRL=7, SRA=8, SRLW=22, SRAW=23. -/
def opcodeExpr (cols : Var ShiftRightCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23

def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory, imm_c⟩,
       _op_a_write_value,
       _b_msb, _srw_msb, _c_bits, _sra_msb_v0123, _v_0123, _v_012, _v_01,
       _lower_limb, _higher_limb, _limb_result, _shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, _sign_extend,
       _next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  let sum := is_srl + is_sra + is_srlw + is_sraw
  sum * (sum - 1) === 0
  op_a_0 === 0

/-- Placeholder for the shift-arithmetic Spec content (bit-decomposition,
shift power chain, byte-shift one-hot, limb-shift, sign-extension via
U16MSB). Currently trivially `True`. -/
def shiftSpec (_cols : ShiftRightCols (ZMod p)) : Prop := True

def Spec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  let opcode_e : ZMod p :=
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
      { prev_value := cols.adapter.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_c[0]
      { prev_value := cols.adapter.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  shiftSpec cols

/-- Project a raw SP1 row into the structured `ShiftRightCols` view.
69 columns; `intermediates_aux : Vector T 28` packed from Main[36..63]. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 69) : ShiftRightCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   #v[Main[32], Main[33], Main[34], Main[35]],
   ⟨Main[36]⟩,                          -- b_msb : U16MSBOperation
   ⟨Main[37]⟩,                          -- srw_msb : U16MSBOperation
   #v[Main[38], Main[39], Main[40], Main[41], Main[42], Main[43]],  -- c_bits
   Main[44],                            -- sra_msb_v0123
   Main[45],                            -- v_0123
   Main[46],                            -- v_012
   Main[47],                            -- v_01
   #v[Main[48], Main[49], Main[50], Main[51]],  -- lower_limb
   #v[Main[52], Main[53], Main[54], Main[55]],  -- higher_limb
   #v[Main[56], Main[57], Main[58], Main[59]],  -- limb_result
   #v[Main[60], Main[61], Main[62], Main[63]],  -- shift_u16
   Main[64], Main[65], Main[66], Main[67], Main[68],
   #v[0, 0, 0]⟩

/-- The chip-level half-iff bridge (ShiftRight). **Proof body sorry'd**. -/
theorem spec_implies_allHold (Main : Vector (ZMod p) 69)
    (h_is_real : Main[64] + Main[65] + Main[66] + Main[67] = 1)
    (h_spec : Spec (fromMain Main)) :
    (_root_.ShiftRight.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_srl`: R-type logical right shift. -/
theorem correct_srl
    (Main : Vector (ZMod p) 69) (s : SailState)
    (h_is_srl : Main[64] = 1) (h_imm_c : Main[31] = 0)
    (h_others_zero : Main[65] = 0 ∧ Main[66] = 0 ∧ Main[67] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.ShiftRight.constraints Main).initialState s) :
    let op_c := _root_.ShiftRight.sp1_op_c Main
    let op_b := _root_.ShiftRight.sp1_op_b Main
    let op_a := _root_.ShiftRight.sp1_op_a Main
    (_root_.Srl.Poly.spec_srl (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.ShiftRight.sp1_shift_right Main).run s :=
  _root_.Srl.Poly.correct_srl Main s
    (spec_implies_allHold Main
      (by obtain ⟨h65, h66, h67⟩ := h_others_zero
          rw [h_is_srl, h65, h66, h67]; ring)
      h_spec)
    ⟨h_is_srl, h_imm_c⟩ state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2)

`Assertion.main` is identical to the chip's `main` (no byte lookups to
drop here — `ShiftRight`'s `main` already only emits `CPUState`,
`ProgramTable`, and scalar boolean gates). The shift-arithmetic content
in `intermediates_aux` stays in legacy `Spec` (via `shiftSpec`
placeholder) and is deferred to the trace-level OfflineMemory bridge.
Memory-bus consistency is similarly deferred. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       _op_a_write_value,
       _b_msb, _srw_msb, _c_bits, _sra_msb_v0123, _v_0123, _v_012, _v_01,
       _lower_limb, _higher_limb, _limb_result, _shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, _sign_extend,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  let sum := is_srl + is_sra + is_srlw + is_sraw
  sum * (sum - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
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

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 26 input fields + 4 subcircuit calls + 3 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftRightCols unit where
  name := "SP1Clean.ShiftRight"
  main := main
  localLength _ := 0

def Assumptions (_ : ShiftRightCols (ZMod p)) : Prop := True

def FormalSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  let opcode_e : ZMod p :=
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
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
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_srl, h_sra, h_srlw, h_sraw,
          h_sum, h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_srl
  · linear_combination h_sra
  · linear_combination h_srlw
  · linear_combination h_sraw
  · linear_combination h_sum
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_srl, h_sra, h_srlw, h_sraw, h_sum,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_srl
  · linear_combination h_sra
  · linear_combination h_srlw
  · linear_combination h_sraw
  · linear_combination h_sum
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftRightCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftRight
