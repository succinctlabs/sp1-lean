import SP1Clean.Chips.ALU.BitwiseChip.Multiplicity.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.Operations.BitwiseU16Operation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `BitwiseChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Composes the Rust subcircuit graph for `BitwiseChip::eval`:
- `BitwiseU16Op.assertion` (8 gated byte-table lookups on the algebraic
  8-byte decomposition of `op_b` / `op_c`, plus an `is_real` binary gate),
- `CPUState.assertion` (clk byte bounds),
- `ALUTypeReader.assertion` (ProgramTable + 3 gated OperandAccess + imm_c
  switch), with the opcode selector `is_xor*3 + is_or*4 + is_and*5`
  encoding the 6 variants and `op_a_write_value` reconstructed from
  `bitwise_operation.bitwise_operation.result[0..7]` as 4 u16 limbs,
- 5 trailing scalar gates (3 selectors binary + sum binary + op_a_0). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `BitwiseChip::eval(builder, cols)`.
Composes the 8 byte-table lookups via `BitwiseU16Op.assertion`, the
clk-byte bounds via `CPUState.assertion`, and the program/memory bus +
imm_c switch via `ALUTypeReader.assertion`. The reconstructed 4-limb
`op_a_write_value` is wired into the reader.

Cols projections are kept un-destructured (e.g. `cols.adapter`,
`cols.bitwise_operation.result`) so the sub-assertion `Spec` payloads
land in the *same projection chain* used by `FormalSpec`. This avoids a
struct-eta mismatch in the soundness/completeness `refine` step. -/
@[reducible]
def main (cols : Var BitwiseCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let res := cols.bitwise_operation.bitwise_operation.result
  let is_real := cols.is_xor + cols.is_or + cols.is_and
  let opcode_bw : Expression (ZMod p) :=
    cols.is_xor * 2 + cols.is_or * 1 + cols.is_and * 0
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[res[0] + res[1] * 256, res[2] + res[3] * 256,
       res[4] + res[5] * 256, res[6] + res[7] * 256]
  SP1Clean.BitwiseU16Op.assertion
    (⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
       cols.bitwise_operation.b_low_bytes.low_bytes,
       cols.bitwise_operation.c_low_bytes.low_bytes,
       cols.bitwise_operation.bitwise_operation.result,
       opcode_bw, is_real⟩ :
      Var SP1Clean.BitwiseU16Op.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ :
      Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.assertion
    (⟨cols.state.clk_high, clk_low,
       cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5,
       cols.state.pc, op_a_write_value, cols.adapter⟩ :
      Var SP1Clean.ALUTypeReader.Inputs (ZMod p))
  cols.is_xor * (cols.is_xor - 1) === 0
  cols.is_or * (cols.is_or - 1) === 0
  cols.is_and * (cols.is_and - 1) === 0
  (cols.is_xor + cols.is_or + cols.is_and) *
    (cols.is_xor + cols.is_or + cols.is_and - 1) === 0
  cols.adapter.op_a_0 === 0

set_option maxHeartbeats 3200000 in
-- 5 scalar gates + 3 subcircuits exceeds the default tactic budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BitwiseCols unit where
  name := "SP1Clean.Bitwise"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : BitwiseCols (ZMod p)) : Prop := True

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.BitwiseChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.BitwiseChip.FormalSpec p

set_option maxHeartbeats 3200000 in
-- Reads `h_holds` (the three sub-`Assertion.Spec`s + 5 scalar equalities)
-- and reassembles the flat `FormalSpec` conjunction one-for-one. No
-- bridging to `(Bitwise.constraints …).allHold` — every conjunct of
-- `FormalSpec` lives directly in `h_holds`.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start [SP1Clean.BitwiseChip.FormalSpec]
  -- Deeply destructure h_input so every leaf equation (Expression.eval env
  -- input_var_<X> = input_<X>) is exposed for `subst_eqs` to substitute.
  obtain ⟨⟨e_clk_h, e_clk_16, e_clk_0, e_pc⟩,
          ⟨e_oa, ⟨e_oapv, ⟨e_oapl, e_oadll⟩⟩, e_oa0, e_ob,
            ⟨e_obpv, ⟨e_obpl, e_obdll⟩⟩, e_oc,
            ⟨e_ocpv, ⟨e_ocpl, e_ocdll⟩⟩, e_imm⟩,
          ⟨⟨e_blb⟩, ⟨e_clb⟩, ⟨e_br⟩⟩,
          e_xor, e_or, e_and, ⟨e_itrust⟩⟩ := h_input
  subst_eqs
  obtain ⟨h_bw_sub, h_cpu_sub, h_alu_sub,
          h_xor_eq, h_or_eq, h_and_eq, h_sum_eq, h_op_a_0⟩ := h_holds
  unfold id at *
  -- Bridge `(Vector.map (eval env) vec)[i]` (in goal) ↔ `eval env vec[i]`
  -- (in `h_*_sub` hyps).
  simp only [Vector.getElem_map]
  refine ⟨h_bw_sub trivial, h_cpu_sub trivial, h_alu_sub trivial,
          ?_, ?_, ?_, ?_, h_op_a_0⟩
  · rcases mul_eq_zero.mp h_xor_eq with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp h_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp h_and_eq with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp h_sum_eq with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)

set_option maxHeartbeats 3200000 in
-- Mirror of `soundness`. From `h_spec` (the flat conjunction) build the
-- three sub-`Assertion.Spec` premises plus the 5 scalar equalities.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start [SP1Clean.BitwiseChip.FormalSpec]
  obtain ⟨⟨e_clk_h, e_clk_16, e_clk_0, e_pc⟩,
          ⟨e_oa, ⟨e_oapv, ⟨e_oapl, e_oadll⟩⟩, e_oa0, e_ob,
            ⟨e_obpv, ⟨e_obpl, e_obdll⟩⟩, e_oc,
            ⟨e_ocpv, ⟨e_ocpl, e_ocdll⟩⟩, e_imm⟩,
          ⟨⟨e_blb⟩, ⟨e_clb⟩, ⟨e_br⟩⟩,
          e_xor, e_or, e_and, ⟨e_itrust⟩⟩ := h_input
  subst_eqs
  obtain ⟨h_bw, h_cpu, h_alu, h_xor_bin, h_or_bin, h_and_bin,
          h_sum_bin, h_op_a_0⟩ := h_spec
  unfold id at *
  -- Same `Vector.getElem_map` bridge as soundness, applied to `h_spec`'s
  -- ALU conjunct which the chip's sub-circuit completeness premise needs.
  simp only [Vector.getElem_map] at h_alu
  refine ⟨⟨trivial, h_bw⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_alu⟩,
          ?_, ?_, ?_, ?_, h_op_a_0⟩
  · rcases h_xor_bin with h | h
    · linear_combination h * (Expression.eval env input_var_is_xor - 1)
    · linear_combination h * Expression.eval env input_var_is_xor
  · rcases h_or_bin with h | h
    · linear_combination h * (Expression.eval env input_var_is_or - 1)
    · linear_combination h * Expression.eval env input_var_is_or
  · rcases h_and_bin with h | h
    · linear_combination h * (Expression.eval env input_var_is_and - 1)
    · linear_combination h * Expression.eval env input_var_is_and
  · rcases h_sum_bin with h | h
    · linear_combination (Expression.eval env input_var_is_xor +
        Expression.eval env input_var_is_or +
        Expression.eval env input_var_is_and - 1) * h
    · linear_combination (Expression.eval env input_var_is_xor +
        Expression.eval env input_var_is_or +
        Expression.eval env input_var_is_and) * h

end Assertion

/-- The full Clean `FormalAssertion` for `BitwiseChip`. -/
def assertion : FormalAssertion (ZMod p) BitwiseCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.BitwiseChip
