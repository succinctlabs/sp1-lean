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
  obtain ⟨_, h_add, h_adapter, _h_regwrite, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- **Option B cycle-break.** The immediate `op_c`'s `isU64` is assumed (`h_assumptions`); the register
  -- `op_b`'s `isU64` is *derived* from the `ITypeReader` reader sub-`Spec` (its 6th conjunct is the memory-
  -- pull-derived pair `is_real=1 → isU64 op_a/op_b prev`). Feeding both into `AddOperation` gives `isU64 value`
  -- (.1) + the gated add identity (.2); the result `isU64` discharges the new `RegisterWrite` op_a write push.
  have h_rspec := h_adapter ⟨h_bin, h_bin⟩
  have h_pair := h_rspec.2.2.2.2.2
  have h_addspec := h_add ⟨fun hr => ⟨(h_pair hr).2, h_assumptions⟩, h_bin⟩
  refine ⟨⟨h_rspec, h_bin, fun hr => (h_addspec hr).2⟩, ?_⟩
  and_intros <;>
    first
      | exact h_bin
      | exact ⟨h_bin, h_bin⟩
      | exact Or.inl rfl
      | exact Or.inr ⟨h_bin, h_bin⟩
      | exact ⟨fun hr => ⟨(h_pair hr).2, h_assumptions⟩, h_bin⟩
      | exact Or.inr ⟨fun hr => ⟨(h_pair hr).2, h_assumptions⟩, h_bin⟩
      | exact Or.inr ⟨h_bin, fun hr => (h_addspec hr).1⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hdec⟩ := h_assumptions
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
    ⟨⟨hbin, hbin⟩, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hdec,
      fun hr => ⟨ha_prev hr, ha⟩⟩,
    ⟨⟨hbin, ?_⟩, trivial⟩, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed result `value = populate op_b op_c_imm`,
    -- whose `isU64` is `spec_populate.1`.
    intro hr; rw [hval]; exact (AddOperation.spec_populate ha hb input_is_real hr).1
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
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input _ =>
      expose stateChannel
        [ pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.ITypeReader.circuit, Readers.ITypeReader.main,
        Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main] }

end SP1Clean.AddiChip
