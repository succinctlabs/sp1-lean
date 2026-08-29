import SP1Clean.Native.Chips.HaltChip.Defs
import Clean.Utils.Tactics

/-! # Halt table: soundness, completeness, and the bundled circuit

The halt row's proofs (contract: `FormalModel/Contracts/SystemChips.lean`). Soundness derives the
`is_real`-binary fact from the inline gate, the reader sub-`Spec`s from the composed sub-circuits,
the pc limb bounds from the Program pull's `RowSpec` guarantee, and — on a real row — the gated
tail (`x5 = 0`, the three read words' `isU64`, the pulled clocks' 24-bit bounds) from the gated
asserts and the three Memory read-prior pull guarantees; the read-back pushes' and Exit push's
requirements are discharged from the paired pulls plus the `CPUState`-derived clock discipline.
Completeness replays the same facts from `ProverAssumptions := Spec` (an all-zero padding row
satisfies it: selector `0`, every gated conjunct vacuous). -/

namespace SP1Clean.HaltChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- The ECALL operand-index literal bound: `(5 : ZMod p).val < 32` (from `2^17 < p`). -/
private lemma val5_lt (hp : (2 : ℕ) ^ 17 < p) : ((5 : ZMod p)).val < 32 := by
  have : ((5 : ZMod p)) = ((5 : ℕ) : ZMod p) := by norm_num
  rw [this, ZMod.val_natCast_of_lt (by omega)]
  omega

theorem soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
      (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, programChannel, exitChannel,
    Channels.MemoryMsg.isU64, Channels.MemoryMsg.ClkBound, Channels.ProgramMsg.RowSpec]
    at h_holds ⊢
  obtain ⟨h_gate, h_cpu, h_rac5, h_rac10, h_rac11, h_prog, z0, z1, z2, z3,
    h_m5, h_m10, h_m11⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- The two `Vector`-component eval crossings `h_input` leaves whole: the pc limbs and the x5 word.
  have epc : ∀ i (hi : i < 3),
      Expression.eval env input_var_state_pc[i] = input_state_pc[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2
    simpa using this
  have e5 : ∀ i (hi : i < 4),
      Expression.eval env input_var_x5_memory_prev_value[i]
        = input_x5_memory_prev_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.1.1
    simpa using this
  refine ⟨⟨h_bin, h_cpu h_bin, h_rac5 h_bin, h_rac10 h_bin, h_rac11 h_bin,
      fun hr => ?_, fun hr => ?_⟩, ?_⟩
  · -- pc limb bounds: the Program pull's `RowSpec` guarantee.
    have hneg : -input_is_real = -1 := by rw [hr]
    exact ⟨epc 0 (by norm_num) ▸ (h_prog hneg).2.1,
      epc 1 (by norm_num) ▸ (h_prog hneg).2.2.1,
      epc 2 (by norm_num) ▸ (h_prog hneg).2.2.2⟩
  · -- the gated tail: `x5 = 0` from the gated asserts, `isU64`/clock bounds from the pulls.
    have hneg : -input_is_real = -1 := by rw [hr]
    rw [hr, one_mul] at z0 z1 z2 z3
    exact ⟨⟨e5 0 (by norm_num) ▸ z0, e5 1 (by norm_num) ▸ z1,
      e5 2 (by norm_num) ▸ z2, e5 3 (by norm_num) ▸ z3⟩,
      (h_m5 hneg).1, (h_m10 hneg).1, (h_m11 hneg).1,
      (h_m5 hneg).2, (h_m10 hneg).2, (h_m11 hneg).2⟩
  · -- the requirement tail: sub-circuit assumptions, off-gate pulls, push requirements.
    and_intros <;>
      first
        | exact h_bin
        | exact Or.inl rfl
        | exact Or.inr h_bin
        | exact fun h1 h0 => off_gate_vacuous h_bin h1 h0
        | (intro _ h0
           have hr : input_is_real = 1 := h_bin.resolve_left h0
           first
             | exact ⟨(h_m5 (by rw [hr])).1, h_clk.at_four hr⟩
             | exact ⟨(h_m10 (by rw [hr])).1, h_clk.at_three hr⟩
             | exact ⟨(h_m11 (by rw [hr])).1, h_clk.at_two hr⟩
             | exact (h_m10 (by rw [hr])).1)

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
      (fun input _ _ => Spec input) (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_bin, h_cpu, h_rac5, h_rac10, h_rac11, h_pc, h_tail⟩ := h_assumptions
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2
    simpa using this
  have e5 : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_x5_memory_prev_value[i]
        = input_x5_memory_prev_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.1.1
    simpa using this
  -- Slots, in op order: the gate, the `CPUState`/register-access sub pairs, the gated Program
  -- pull, the four `x5 = 0` asserts, and the three Memory read-prior pulls (a push owes nothing
  -- in completeness — its requirement is a soundness-side obligation).
  refine ⟨?_, ⟨h_bin, h_cpu⟩, ⟨h_bin, h_rac5⟩, ⟨h_bin, h_rac10⟩, ⟨h_bin, h_rac11⟩,
    fun hneg => ?_, ?_, ?_, ?_, ?_,
    fun hneg => ?_, fun hneg => ?_, fun hneg => ?_⟩
  · rcases h_bin with h | h <;> rw [h] <;> simp
  · -- Program pull: `RowSpec` of the ECALL fetch, from the pc bounds + the index literal.
    have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨val5_lt (Fact.out (p := 2 ^ 17 < p)),
      (epc 0 (by norm_num)).symm ▸ (h_pc hr).1,
      (epc 1 (by norm_num)).symm ▸ (h_pc hr).2.1,
      (epc 2 (by norm_num)).symm ▸ (h_pc hr).2.2, Or.inl rfl⟩
  · rcases h_bin with h | h <;> rw [h]
    · rw [zero_mul]
    · rw [one_mul, e5 0 (by norm_num)]; exact ((h_tail h).1).1
  · rcases h_bin with h | h <;> rw [h]
    · rw [zero_mul]
    · rw [one_mul, e5 1 (by norm_num)]; exact ((h_tail h).1).2.1
  · rcases h_bin with h | h <;> rw [h]
    · rw [zero_mul]
    · rw [one_mul, e5 2 (by norm_num)]; exact ((h_tail h).1).2.2.1
  · rcases h_bin with h | h <;> rw [h]
    · rw [zero_mul]
    · rw [one_mul, e5 3 (by norm_num)]; exact ((h_tail h).1).2.2.2
  · -- x5 read-prior pull: `isU64` + the pulled clock's 24-bit bound.
    have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_tail hr).2.1, (h_tail hr).2.2.2.2.1⟩
  · have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_tail hr).2.2.1, (h_tail hr).2.2.2.2.2.1⟩
  · have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_tail hr).2.2.2.1, (h_tail hr).2.2.2.2.2.2⟩

/-- The Halt system table as a `GeneralFormalCircuit`: the halting shard's ECALL witness row.
`Assumptions := True` (everything is proved in-circuit or received from the buses);
`ProverAssumptions := Spec` (an all-zero padding row satisfies it). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Assumptions := fun _ _ => True
  Spec := fun input _ _ => Spec input
  ProverAssumptions := fun input _ _ => Spec input
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := [memoryChannel.toRaw, exitChannel.toRaw]
  requirementsChannelsLawful := fun input_var i₀ => by
    dsimp only [Operations.RequirementsChannelsLawful]
    refine ⟨by simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit], ?_, ?_⟩
    · intro channel h_channel
      simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit] at h_channel
      -- one Program entry, six Memory entries, one Exit entry
      rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact Or.inr List.mem_cons_self
          | exact Or.inr (List.mem_cons_of_mem _ List.mem_cons_self)
          | exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              List.mem_cons_self))
    · intro env h_constraints
      have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
          (ProvableStruct.eval env input_var).is_real = 1 := by
        apply bool_of_mul_pred
        simpa only [circuit_norm] using h_constraints.1
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction h_interaction
      simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit] at h_interaction
      -- The Program pull's off-gate requirement is vacuous via the inline binary gate; every
      -- Memory/Exit interaction's channel is in `channelsWithRequirements`.
      rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        rw [ChannelInteraction.toRaw_requirements]; intro h1 h0
        simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_bool h1 h0
      all_goals first
        | exact Or.inl List.mem_cons_self
        | exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements
      = [memoryChannel.toRaw, exitChannel.toRaw] := rfl

end SP1Clean.HaltChip
