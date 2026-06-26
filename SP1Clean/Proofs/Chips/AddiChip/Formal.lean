import SP1Clean.Native.Chips.AddiChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.AddiChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.AddiChip

open Circuit
open Extracted (AddiCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.AddiChip` namespace). -/

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_, h_add, h_adapter, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => (h_add ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ hr).2⟩, ?_⟩
  and_intros <;>
    first | exact h_bin | exact ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ | exact Or.inl rfl | exact Or.inr h_bin
          | exact Or.inr ⟨fun _ => ⟨ha, hb⟩, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b⟩ := h_assumptions
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, hoc⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have mapEq : ∀ (vv : Word (Expression (ZMod p))) (v : Word (ZMod p)),
      Vector.map (Expression.eval env.toEnvironment) vv = v →
      (#v[Expression.eval env.toEnvironment vv[0], Expression.eval env.toEnvironment vv[1],
        Expression.eval env.toEnvironment vv[2], Expression.eval env.toEnvironment vv[3]] : Word (ZMod p)) = v :=
    fun vv v h => by rw [← h]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hbeq := mapEq input_var_adapter_op_b_memory_prev_value _ hob
  have hceq := mapEq input_var_adapter_op_c_imm _ hoc
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b⟩, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The `Addi` chip row as a `GeneralFormalCircuit`: single-variant `is_real`-gated RV64 `add`
semantic contract over a register source + immediate, composing the witnessed `AddOperation` gadget;
output is the extracted `AddiCols` column struct. Soundness/completeness are fully proven. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddiCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw] }

end SP1Clean.AddiChip
