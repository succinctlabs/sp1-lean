import SP1Clean.Native.Chips.StateBumpChip.Defs
import Clean.Utils.Tactics

/-! # StateBump: soundness, completeness, and the bundled circuit (W3, report Finding 2)

The flat own-assert table's proofs. Soundness derives the two boolean gates and the pc borrow
cascade from the ungated asserts, and — on a real row — the pushed-limb range facts from the byte
pull `Guarantees` and the clock-carry equations from the gated asserts. Completeness replays the
same facts from `ProverAssumptions := Spec` (an all-zero padding row satisfies it: both selectors
`0`, the cascade with zero borrows, the gated tail vacuous). The State bus carries `Guarantees :=
True`, so the pull/push pair owes nothing on either side. -/

namespace SP1Clean.StateBumpChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel StateMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] in
/-- `13 < p`, the `Range` width-column round-trip bound (from `2^17 < p`). -/
private lemma h13p : (13 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

theorem soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
      (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start
  simp only [circuit_norm, byteChannel, stateChannel] at h_holds ⊢
  obtain ⟨h_gate, b13, b16, bpair, h_isclk, h_clkhi, h_clklo, c0, c1, -, czero,
    bpc0, bpc1, bpc2⟩ := h_holds
  have h_bool := bool_of_mul_pred h_gate
  -- the top pc borrow vanishes: multiply `czero` back up by `65536`
  have hc2 : (((input_pc0 - input_next_pc0) * (65536 : ZMod p)⁻¹ + input_pc1 - input_next_pc1)
      * (65536 : ZMod p)⁻¹ + input_pc2 - input_next_pc2) = 0 := by
    have h' := congrArg (· * (65536 : ZMod p)) czero
    rwa [zero_mul, mul_assoc, inv_mul_cancel₀ val_65536_ne_zero, mul_one] at h'
  refine ⟨⟨h_bool, bool_of_mul_pred h_isclk,
    ⟨(input_pc0 - input_next_pc0) * (65536 : ZMod p)⁻¹,
     ((input_pc0 - input_next_pc0) * (65536 : ZMod p)⁻¹ + input_pc1 - input_next_pc1)
       * (65536 : ZMod p)⁻¹,
     bool_of_mul_pred c0, bool_of_mul_pred c1, ?_, ?_, ?_⟩, fun hr1 => ?_⟩,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun h1 h0 => off_gate_vacuous h_bool h1 h0,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun h1 h0 => off_gate_vacuous h_bool h1 h0,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun h1 h0 => off_gate_vacuous h_bool h1 h0⟩
  · rw [mul_assoc, inv_mul_cancel₀ val_65536_ne_zero, mul_one]; ring
  · rw [mul_assoc, inv_mul_cancel₀ val_65536_ne_zero, mul_one]; ring
  · linear_combination hc2
  · rw [hr1, one_mul] at h_clkhi h_clklo
    have hneg : -input_is_real = -1 := by rw [hr1]
    refine ⟨(byteRowSpec_range _ h13p).mp (by rw [Nat.cast_ofNat]; exact b13 hneg),
      ((byteRowSpec_u8range_pair _ _).mp (bpair hneg)).1,
      ((byteRowSpec_u8range_pair _ _).mp (bpair hneg)).2,
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact b16 hneg),
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact bpc0 hneg),
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact bpc1 hneg),
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact bpc2 hneg),
      ?_, ?_⟩
    · linear_combination h_clkhi
    · linear_combination h_clklo

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
      (fun input _ _ => Spec input) (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_bool, h_isclk, ⟨b0, b1, hb0, hb1, e0, e1, e2⟩, h_gated⟩ := h_assumptions
  -- the borrow expressions collapse onto the `Spec` witnesses
  have hb0e : (input_pc0 - input_next_pc0) * (65536 : ZMod p)⁻¹ = b0 := by
    rw [e0, add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ val_65536_ne_zero, mul_one]
  have hb1e : ((input_pc0 - input_next_pc0) * (65536 : ZMod p)⁻¹ + input_pc1 - input_next_pc1)
      * (65536 : ZMod p)⁻¹ = b1 := by
    rw [hb0e, show b0 + input_pc1 - input_next_pc1 = b1 * 65536 by linear_combination e1,
      mul_assoc, mul_inv_cancel₀ val_65536_ne_zero, mul_one]
  have hb2e : (((input_pc0 - input_next_pc0) * (65536 : ZMod p)⁻¹ + input_pc1 - input_next_pc1)
      * (65536 : ZMod p)⁻¹ + input_pc2 - input_next_pc2) * (65536 : ZMod p)⁻¹ = 0 := by
    rw [hb1e, show b1 + input_pc2 - input_next_pc2 = 0 by linear_combination e2, zero_mul]
  rcases h_bool with h0 | h1
  · -- padding row: the gated asserts vanish, the gated pulls fire only off-padding
    have hne : ∀ {P : Prop}, -input_is_real = -1 → P :=
      fun h => absurd (neg_inj.mp h) (by rw [h0]; exact zero_ne_one)
    refine ⟨by rw [h0, zero_mul], hne, hne, hne, hne, ?_, by rw [h0, zero_mul],
      by rw [h0, zero_mul], ?_, ?_, ?_, hb2e, hne, hne, hne⟩
    · rcases h_isclk with h | h <;> simp [h]
    · rw [hb0e]; rcases hb0 with h | h <;> simp [h]
    · rw [hb1e]; rcases hb1 with h | h <;> simp [h]
    · rw [hb2e, zero_mul]
  · -- real row: the gated facts come from the `Spec` tail
    obtain ⟨r13, r1624, r2432, r3248, rpc0, rpc1, rpc2, eqhi, eqlo⟩ := h_gated h1
    refine ⟨by rw [h1, sub_self, mul_zero],
      fun _ => trivial,
      fun _ => (byteRowSpec_range _ h13p).mpr r13,
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr r3248,
      fun _ => (byteRowSpec_u8range_pair _ _).mpr ⟨r1624, r2432⟩,
      ?_, by rw [h1, one_mul]; linear_combination eqhi,
      by rw [h1, one_mul]; linear_combination eqlo,
      ?_, ?_, ?_, hb2e,
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr rpc0,
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr rpc1,
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr rpc2⟩
    · rcases h_isclk with h | h <;> simp [h]
    · rw [hb0e]; rcases hb0 with h | h <;> simp [h]
    · rw [hb1e]; rcases hb1 with h | h <;> simp [h]
    · rw [hb2e, zero_mul]

/-- The StateBump system table as a `GeneralFormalCircuit`: the canonical clock/pc re-limbing row.
`Assumptions := True` (everything is proved in-circuit or received from the byte bus);
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
  channelsWithRequirements := []
  requirementsChannelsLawful := fun input_var i₀ => by
    change Operations.RequirementsChannelsLawful
      ([.assert _, .interact _, .interact _, .interact _, .interact _, .interact _, .assert _,
        .assert _, .assert _, .assert _, .assert _, .assert _, .assert _, .interact _,
        .interact _, .interact _] : Operations (ZMod p))
        [byteChannel.toRaw, stateChannel.toRaw] []
    dsimp only [Operations.RequirementsChannelsLawful]
    refine ⟨by simp only [circuit_norm], ?_, ?_⟩
    · intro channel h_channel
      simp only [circuit_norm] at h_channel
      rcases h_channel with rfl | rfl | rfl
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact Or.inl List.mem_cons_self
    · intro env h_constraints
      have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
          (ProvableStruct.eval env input_var).is_real = 1 := by
        apply bool_of_mul_pred
        simpa only [circuit_norm] using h_constraints.1
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction h_interaction
      simp only [circuit_norm] at h_interaction
      -- Two shapes only: the State pair's requirement is `True`, and the byte pulls are
      -- `is_real`-gated so their requirement is off-gate vacuous.
      rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;>
        first
          | (simp only [ChannelInteraction.toRaw_requirements, ChannelInteraction.Requirements,
                stateChannel]; intros; trivial)
          | (rw [ChannelInteraction.toRaw_requirements]; intro h1 h0;
             simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_bool h1 h0)

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

end SP1Clean.StateBumpChip
