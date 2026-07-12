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
  -- `RegisterWrite` is now `h_holds.2.2.2.1`; the inline gate shifted to `.2.2.2.2`.
  have h_bin := bool_of_mul_pred h_holds.2.2.2.2
  -- **Option B cycle-break.** No operand `isU64` is assumed (chip `Assumptions = True`). Derive it from the
  -- `RTypeReader` sub-`Spec`'s memory-pull `isU64` trio (its 7th conjunct, gated on `is_real`).
  have h_rspec := h_adapter ⟨h_bin, h_bin⟩
  have h_trio := h_rspec.2.2.2.2.2.2
  have h_as : SubwOperation.circuit.Assumptions
      { a := input_adapter_op_b_memory_prev_value, b := input_adapter_op_c_memory_prev_value,
        cols := ⟨Vector.map (Expression.eval env) (Vector.mapRange 2 fun i => var { index := i₀ + i }),
          ⟨env.get (i₀ + 2)⟩⟩, is_real := input_is_real } :=
    ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩, h_bin⟩
  -- The `RegisterWrite` op_a write push owes `isU64` of the sign-extended write word `[v0, v1, msb·65535,
  -- msb·65535]` (= `SubwOperation.resultWord cols`); align its `Vector.map`/`env.get` slots.
  have h_rw_isU64 : input_is_real = 1 →
      Word.isU64 (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2) * 65535, env.get (i₀ + 2) * 65535]
        : Word (ZMod p)) := fun hr => by
    simpa only [SubwOperation.resultWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      using ((h_subw h_as).2 hr).1
  refine ⟨⟨?_, h_bin, fun hr => ?_⟩, ?_⟩
  · simpa only [Vector.getElem_map] using h_rspec
  · refine trans ?_ (rv64_subw_eq _ _).symm
    simpa only [SubwOperation.resultWord, Vector.getElem_map] using
      ((h_subw h_as).2 hr).2
  · and_intros <;>
      first
        | exact h_bin
        | exact ⟨h_bin, h_bin⟩
        | exact Or.inl rfl
        | exact Or.inr ⟨h_bin, h_bin⟩
        | exact ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩, h_bin⟩
        | exact Or.inr ⟨h_bin, h_rw_isU64⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c, hdec, h_st, h_prog⟩ :=
    h_assumptions
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  -- `h_env` now bundles the `value`/`msb` witness-gen equations with the GFC `RTypeReader` subcircuit's
  -- completeness obligation (its third component); the witness equations are the first two.
  obtain ⟨-, h_env_val, h_env_msb, -⟩ := h_env
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
    simp only [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2)
      = SubwOperation.subwMsbWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu, h_st⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
      fun hr => ⟨ha_prev hr, ha, hb⟩⟩, h_prog⟩,
    ⟨⟨hbin, ?_⟩, trivial⟩, ?_⟩
  · rw [hval, hmsbeq]; exact SubwOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed op_a write word is the sign-extended
    -- `resultWord (populate op_b op_c)`, whose `isU64` is `spec_populate.2 _ |>.1`. The write value appears
    -- as individual `env.get` slots, so bridge them to the operation's witnessed limbs via `hval`/`hmsbeq`.
    intro hr
    have h0 : env.get i₀ = (SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
        input_adapter_op_c_memory_prev_value)[0] := by
      simpa only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        using congrArg (fun v => v[0]) hval
    have h1 : env.get (i₀ + 1) = (SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
        input_adapter_op_c_memory_prev_value)[1] := by
      simpa only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        using congrArg (fun v => v[1]) hval
    have hword : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2) * 65535, env.get (i₀ + 2) * 65535]
          : Word (ZMod p))
        = SubwOperation.resultWord (SubwOperation.populate input_adapter_op_b_memory_prev_value
            input_adapter_op_c_memory_prev_value) := by
      rw [h0, h1, hmsbeq]; simp only [SubwOperation.resultWord, SubwOperation.populate]
    rw [hword]
    exact ((SubwOperation.spec_populate ha hb input_is_real).2 hr).1
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The SUBW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the two readers; output is the extracted `SubwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs SubwCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
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
        SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
        SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf] }

end SP1Clean.SubwChip
