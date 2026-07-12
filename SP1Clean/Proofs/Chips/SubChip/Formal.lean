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
  obtain ⟨_, h_sub, h_adapter, _h_regwrite, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- **Option B cycle-break.** No operand `isU64` is assumed (chip `Assumptions = True`). Apply the
  -- `RTypeReader` sub-soundness `h_adapter` (its `Assumptions` is `⟨is_real binary, is_trusted binary⟩`,
  -- both `h_bin` since `is_trusted = is_real`) to get its `Spec`; its 7th conjunct is the **memory-pull-
  -- derived** operand `isU64` trio `(is_real = 1 → isU64 op_a/op_b/op_c prev)`. Operand `isU64` thus flows
  -- reader → here, not from a chip assumption — no cycle.
  have h_rspec := h_adapter ⟨h_bin, h_bin⟩
  have h_trio := h_rspec.2.2.2.2.2.2
  -- Feed operand `isU64` (gated on `is_real`) into `SubOperation`'s sub-soundness → `isU64 value` (.1) + the
  -- gated sub identity (.2). The witnessed result `value`'s `isU64` then discharges the new `RegisterWrite`
  -- op_a write push's `Assumptions`.
  have h_subspec := h_sub ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩, h_bin⟩
  refine ⟨⟨h_rspec, h_bin, fun hr => (h_subspec hr).2⟩, ?_⟩
  and_intros <;>
    first
      | exact h_bin
      | exact ⟨h_bin, h_bin⟩
      | exact Or.inl rfl
      | exact Or.inr ⟨h_bin, h_bin⟩
      | exact ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩, h_bin⟩
      | exact Or.inr ⟨h_bin, fun hr => (h_subspec hr).1⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c, hdec, h_st, h_prog⟩ :=
    h_assumptions
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
    -- `h_env` now bundles the chip's `value` witness-gen equations with the GFC `RTypeReader`
    -- subcircuit's completeness obligation — the witness equations are `h_env.1`.
    rw [h_env.2.1 ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    simp only [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu, h_st⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
      fun hr => ⟨ha_prev hr, ha, hb⟩⟩, h_prog⟩,
    ⟨⟨hbin, ?_⟩, trivial⟩, ?_⟩
  · rw [hval]; exact SubOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed result `value = populate op_b op_c`,
    -- whose `isU64` is `spec_populate.1`.
    intro hr; rw [hval]; exact (SubOperation.spec_populate ha hb input_is_real hr).1
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
      stateChannel.expose
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
        List.map_cons, List.map_nil]
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.RTypeReader.circuit, Readers.RTypeReader.main,
        Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf] }

end SP1Clean.SubChip
