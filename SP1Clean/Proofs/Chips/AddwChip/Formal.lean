import SP1Clean.Native.Chips.AddwChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.AddwChip` — contract: `Assumptions` / soundness / completeness / `circuit`

`Spec` (ALUTypeReader.Spec ∧ binary ∧ gated `RV64.addw`) + `Assumptions`/`ProverAssumptions` in
`FormalModel/Contracts/`. -/

namespace SP1Clean.AddwChip

open Circuit
open Extracted (AddwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.AddwChip` namespace). -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- W-instruction soundness. Landmines: use `.2.1`/`.2.2.1`/`.2.2.2` projections on `h_holds` (never
`obtain`/`rcases`), keep `Spec` opaque so `RV64.addw` stays out of `circuit_norm`; arith goes via
`rv64_addw_eq` by hand. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h_addw := h_holds.2.1
  have h_adapter := h_holds.2.2.1
  have h_bin := bool_of_mul_pred h_holds.2.2.2
  have ha := h_assumptions.1
  have hb := h_assumptions.2
  have h_as : AddwOperation.circuit.Assumptions
      { a := input_adapter_op_b_memory_prev_value, b := input_adapter_op_c_memory_prev_value,
        cols := ⟨Vector.map (Expression.eval env) (Vector.mapRange 2 fun i => var { index := i₀ + i }),
          ⟨env.get (i₀ + 2)⟩⟩, is_real := input_is_real } := ⟨ha, hb, h_bin⟩
  refine ⟨⟨?_, h_bin, fun hr => ?_⟩, ?_⟩
  · simpa only [resultWord, Vector.getElem_map] using h_adapter h_bin
  · refine trans ?_ (rv64_addw_eq _ _).symm
    simpa only [resultWord, AddwOperation.resultWord, Vector.getElem_map] using
      ((h_addw h_as).2 hr).2
  · and_intros <;> first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr h_as

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, himm, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  -- `op_c_memory` is grouped since `imm_c` is the final field of the ALU adapter block.
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, ⟨hoc, -, -⟩, -⟩ := h_input
  obtain ⟨h_env_val, h_env_msb⟩ := h_env
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_b_memory_prev_value := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hceq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_c_memory_prev_value := by
    rw [← hoc]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i => var { index := i₀ + i }) : Vector (ZMod p) 2)
      = AddwOperation.addwValueWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env_val ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2) = AddwOperation.addwMsbWitness input_adapter_op_b_memory_prev_value
      input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · rw [hval, hmsbeq]; exact AddwOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The ADDW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the CPUState + the immediate-capable register reader; output is the extracted `AddwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddwCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.AddwChip
