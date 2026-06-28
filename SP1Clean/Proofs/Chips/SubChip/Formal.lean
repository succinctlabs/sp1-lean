import SP1Clean.Native.Chips.SubChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.SubChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.SubChip

open Circuit
open Extracted (SubCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.SubChip` namespace). -/

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  -- `circuit_proof_start` unfolds the inlined R-type Spec, re-normalizes
  -- `wv*` result-word fields, and drops the leading CPUState `True` fragment.
  circuit_proof_start
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_, h_sub, h_adapter, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- `RTypeReader.Assumptions` is now `⟨is_real binary, is_trusted binary⟩` (W11 flip; `is_trusted = is_real`
  -- here, so both are `h_bin`); its `Spec` now also carries the **derived** decode bounds.
  refine ⟨⟨h_adapter ⟨h_bin, h_bin⟩, h_bin, fun hr => (h_sub ⟨ha, hb, h_bin⟩ hr).2⟩, ?_⟩
  and_intros <;>
    first | exact h_bin | exact ⟨h_bin, h_bin⟩ | exact Or.inl rfl | exact Or.inr ⟨h_bin, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c, hdec⟩ := h_assumptions
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have mapEq : ∀ (vv : Word (Expression (ZMod p))) (v : Word (ZMod p)),
      Vector.map (Expression.eval env.toEnvironment) vv = v →
      (#v[Expression.eval env.toEnvironment vv[0], Expression.eval env.toEnvironment vv[1],
        Expression.eval env.toEnvironment vv[2], Expression.eval env.toEnvironment vv[3]] : Word (ZMod p)) = v :=
    fun vv v h => by rw [← h]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hbeq := mapEq input_var_adapter_op_b_memory_prev_value _ hob
  have hceq := mapEq input_var_adapter_op_c_memory_prev_value _ hoc
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = SubOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin⟩, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec⟩, ?_⟩
  · rw [hval]; exact SubOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The Sub chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed
gadget + the two readers; output is the extracted `SubCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs SubCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `programChannel` dropped (W11 flip — now pulled via `RTypeReader`, a guarantee not a requirement).
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- A2: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8) so the
    -- chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone State pull+push.
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
        Readers.RTypeReader.circuit, Readers.RTypeReader.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main] }

end SP1Clean.SubChip
