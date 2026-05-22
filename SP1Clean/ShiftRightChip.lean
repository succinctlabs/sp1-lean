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
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddrAddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftRightChip
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
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

namespace SP1Clean.ShiftRight

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure ShiftRightCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18]
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c : Vector T 4                         -- Main[21..24]
  op_c_memory_prev_value : Vector T 4       -- Main[25..28]
  op_c_memory_prev_low : T                  -- Main[29]
  op_c_memory_diff_low : T                  -- Main[30]
  imm_c : T                                 -- Main[31]
  op_a_write_value : Vector T 4             -- Main[32..35]
  intermediates_aux : Vector T 28           -- Main[36..63] (shift-arithmetic ws)
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
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, imm_c, _op_a_write_value,
       _intermediates_aux, is_srl, is_sra, is_srlw, is_sraw, _sign_extend,
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
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory_prev_low,
            diff_low_limb := cols.op_b_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_c[0]
      { prev_value := cols.op_c_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_c_memory_prev_low,
            diff_low_limb := cols.op_c_memory_diff_low } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := opcode_e,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.op_a_0 = 0 ∧
  shiftSpec cols

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
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c, _op_c_memory_prev_value,
       _op_c_memory_prev_low, _op_c_memory_diff_low, imm_c, _op_a_write_value,
       _intermediates_aux, is_srl, is_sra, is_srlw, is_sraw, _sign_extend,
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
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := opcode_e, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0], op_c := cols.op_c,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := cols.imm_c } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.pc[0], cols.pc[1], cols.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_srl, h_sra, h_srlw, h_sraw,
          h_sum, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_srl, h_sra, h_srlw, h_sraw, h_sum,
          h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftRightCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftRight
