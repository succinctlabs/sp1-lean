import SP1Clean.Semantics.Specs.Chips.Lt
import SP1Clean.Circuits.Gadgets.LtSigned
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native less-than instruction circuit

Committed SLT/SLTU selectors determine activity, comparison mode and the fetched opcode.
Clean's witness IR constructs the ten comparison cells. Bundled CPU, ALU and register-write
circuits supply the reader contracts and State, Memory and Program interactions.
-/

namespace SP1Clean.LtChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Build a less-than row from reader inputs and committed selectors, without flag hints. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let is_slt := input.isSlt; let is_sltu := input.isSltu
  let lt_cols ← witness (var := Var Circuits.Types.LtOperationSigned)
    (LtOperationSigned.populateFE input.op_b_val input.op_c_val is_slt input.is_real)
  assertion LtOperationSigned.circuit ⟨input.op_b_val, input.op_c_val, lt_cols, is_slt, input.is_real⟩
  let _ ← Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_slt * 9 + is_sltu * 10,
     lt_cols.result.u16_compare_operation.bit, 0, 0, 0⟩
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[lt_cols.result.u16_compare_operation.bit, 0, 0, 0], input.is_real⟩
  assertZero (input.is_real * (input.is_real - 1))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, is_slt, is_sltu, lt_cols⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.state, input.adapter, input.isSlt, input.isSltu,
      varFromOffset Circuits.Types.LtOperationSigned offset⟩
  output_eq := by intro input offset; simp only [main, circuit_norm]
  channelsLawful := by
    preserve_tactic_target
    simp only [Inputs.is_real, circuit_norm, main, LtOperationSigned.circuit,
      Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  localLength _ := 10
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The completed row, exposed as a folded value for chip-boundary proofs. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter, input.isSlt, input.isSltu,
        varFromOffset Circuits.Types.LtOperationSigned offset⟩ : Var Columns (ZMod p)) := rfl

@[circuit_norm] theorem eval_opBVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_b_val
      = Vector.map (Expression.eval env) input.op_b_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_b_val, eval_inputs, Readers.ALUTypeReader.eval_cols,
    Readers.ALUTypeReader.eval_accessCols]
  exact ProvableType.eval_fields env _

@[circuit_norm] theorem eval_opCVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_c_val
      = Vector.map (Expression.eval env) input.op_c_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_c_val, eval_inputs, Readers.ALUTypeReader.eval_cols,
    Readers.ALUTypeReader.eval_accessCols]
  exact ProvableType.eval_fields env _

end SP1Clean.LtChip
