import SP1Clean.Native.Chips.AddChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.AddChip` — contract: `Assumptions` / soundness / completeness / `circuit`

This is the canonical "template" chip for the porting recipe (`docs/agents/porting-recipe.md`). When
golfing / cleaning proofs here or in any sibling chip, follow `docs/agents/proof-patterns.md` §
"Golf & cleanup discipline". -/

namespace SP1Clean.AddChip

open Circuit
open Extracted (AddCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.AddChip` namespace). -/

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  -- The `Spec` is the inlined R-type-with-readers contract; `circuit_proof_start` unfolds it,
  -- re-normalizes `wv*` result-word fields, and drops the leading CPUState `True` fragment.
  circuit_proof_start
  obtain ⟨_, h_add, h_adapter, _h_regwrite, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- **Option B cycle-break.** No operand `isU64` is assumed (chip `Assumptions = True`). Apply the
  -- `RTypeReader` sub-soundness `h_adapter` (its `Assumptions` is `⟨is_real binary, is_trusted binary⟩`,
  -- both `h_bin` since `is_trusted = is_real`) to get its `Spec`; its 7th conjunct is the **memory-pull-
  -- derived** operand `isU64` trio `(is_real = 1 → isU64 op_a/op_b/op_c prev)`. Operand `isU64` thus flows
  -- reader → here, not from a chip assumption — no cycle.
  have h_rspec := h_adapter ⟨h_bin, h_bin⟩
  have h_trio := h_rspec.2.2.2.2.2.2
  -- Feed operand `isU64` (gated on `is_real`; `op_b_val`/`op_c_val` are defeq the `op_b/op_c` prev_values)
  -- into `AddOperation`'s sub-soundness → `isU64 value` (.1) + the gated add identity (.2). The witnessed
  -- result `value`'s `isU64` then discharges the new `RegisterWrite` op_a write push's `Assumptions`.
  have h_addspec := h_add ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩, h_bin⟩
  refine ⟨⟨h_rspec, h_bin, fun hr => (h_addspec hr).2⟩, ?_⟩
  -- The sub-circuit `Assumptions` tail (post-Clean-`main`: each is a bare `Assumptions` or a
  -- `channelsWithRequirements = [] ∨ Assumptions` disjunct). The new `RegisterWrite` one needs `isU64 value`,
  -- read off `h_addspec.1`; the rest are discharged by the binary gate.
  and_intros <;>
    first
      | exact h_bin
      | exact ⟨h_bin, h_bin⟩
      | exact Or.inl rfl
      | exact Or.inr ⟨h_bin, h_bin⟩
      | exact ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩, h_bin⟩
      | exact Or.inr ⟨h_bin, fun hr => (h_addspec hr).1⟩

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
  -- The witnessed `value` is `populate op_b op_c` (`h_env` per-limb).
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    -- `h_env` now bundles the GFC `CPUState` obligation (`.1`, since it too is a GFC subcircuit now),
    -- the chip's `value` witness-gen equations (`.2.1`), and the `RTypeReader` obligation (`.2.2`).
    rw [h_env.2.1 ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu, h_st⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
        fun hr => ⟨ha_prev hr, ha, hb⟩⟩, h_prog⟩,
    ⟨⟨hbin, ?_⟩, trivial⟩, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed result `value = populate op_b op_c`,
    -- whose `isU64` is `spec_populate.1`.
    intro hr; rw [hval]; exact (AddOperation.spec_populate ha hb input_is_real hr).1
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The Add chip row as a `GeneralFormalCircuit`: semantic contract, composing the
witnessed gadget; output is the extracted `AddCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddCols where
  main
  elaborated
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness
  -- `programChannel` dropped (W11 flip — now pulled via `RTypeReader`, a guarantee not a requirement).
  channelsWithRequirements :=
    [stateChannel.toRaw, memoryChannel.toRaw]
  -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (the gated VM channel
  -- interactions, descended from the composed `CPUState` subcircuit) so the chip can be a `VmTables` table.
  exposedChannels := fun input _ =>
    stateChannel.expose
      [ stateChannel.pulledIf input.is_real
          ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
           input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
        stateChannel.pushedIf input.is_real
          ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
           input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]
  exposedChannels_eq := by
    intro input offset
    -- reduce `ExposedChannelsLawful (stateChannel.expose [pull, push])` to a single
    -- `interactionsWith stateChannel.toRaw = [pull.toRaw, push.toRaw]` goal (the `VmChannel` analog of
    -- Clean's `Channel.exposedChannelsLawful_expose`), then descend as before.
    simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
      List.map_cons, List.map_nil]
    -- descend the chip into its composed sub-readers (`circuit_norm` +
    -- `FormalAssertion.toSubcircuit_interactions`); `interactionsWith stateChannel` is itself a channel
    -- `List.filter`, so the closing `simp` drops the byte/mem/program pulls (channel distinctness) and the
    -- `Gadgets.Equality` constraint-only sub-ops (no interactions), leaving CPUState's State pull + push.
    simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.RTypeReader.circuit, Readers.RTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf]

end SP1Clean.AddChip
