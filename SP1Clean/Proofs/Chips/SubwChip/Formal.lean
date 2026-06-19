import SP1Clean.Native.Chips.SubwChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.SubwChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.SubwChip

open Circuit
open Extracted (SubwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.SubwChip` namespace). -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- W-instruction soundness. Landmines: (1) use `.2.1`/`.2.2.1`/`.2.2.2` projections on `h_holds`
(never `obtain`/`rcases` — the nested `.msb.msb * 65535` sign-fill in the reader's bus emits forces
deep `ProvableStruct` whnf via the case-motive and blows past 16M heartbeats); (2) the inlined `Spec`
keeps `RV64.subw` intact through `circuit_proof_start`; arith via `rv64_subw_eq`. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h_subw := h_holds.2.1
  have h_adapter := h_holds.2.2.1
  have h_bin := bool_of_mul_pred h_holds.2.2.2
  have ha := h_assumptions.1
  have hb := h_assumptions.2
  have h_as : SubwOperation.circuit.Assumptions
      { a := input_adapter_op_b_memory_prev_value, b := input_adapter_op_c_memory_prev_value,
        cols := ⟨Vector.map (Expression.eval env) (Vector.mapRange 2 fun i => var { index := i₀ + i }),
          ⟨env.get (i₀ + 2)⟩⟩, is_real := input_is_real } := ⟨ha, hb, h_bin⟩
  refine ⟨⟨?_, h_bin, fun hr => ?_⟩, ?_⟩
  · simpa only [Vector.getElem_map] using h_adapter h_bin
  · refine trans ?_ (rv64_subw_eq _ _).symm
    simpa only [SubwOperation.resultWord, Vector.getElem_map] using
      ((h_subw h_as).2 hr).2
  · and_intros <;> first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr h_as

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
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
      = SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env_val ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2)
      = SubwOperation.subwMsbWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · rw [hval, hmsbeq]; exact SubwOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The SUBW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the two readers; output is the extracted `SubwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs SubwCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.SubwChip
