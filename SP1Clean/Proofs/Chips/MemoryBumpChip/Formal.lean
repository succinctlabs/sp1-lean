import SP1Clean.Native.Chips.MemoryBumpChip.Defs
import Clean.Utils.Tactics

/-! # MemoryBump: soundness, completeness, and the bundled circuit (W3, report Finding 2)

The register-record timestamp refresh's proofs. Soundness derives `is_real` boolean from the inline
gate and — on a real row — the pulled record's `isU64 ∧ ClkBound` from the memory pull `Guarantees`,
the refreshed-limb ranges and register-index bound from the byte pulls, and the comparison evidence
from the gated asserts; the refreshed **push**'s `isU64 ∧ ClkBound` requirement is discharged from
the pull's value guarantee (same word) and the own limb checks (`clkLow_lt_2pow24`). Completeness
replays everything from `ProverAssumptions := Spec` (an all-zero padding row satisfies it). -/

namespace SP1Clean.MemoryBumpChip

open Circuit
open SP1Clean.Channels (memoryChannel byteChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `32 < p`, the register-index round-trip bound (from `2^17 < p`). -/
private lemma h32p : (32 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The register-index literal round-trips through `ZMod.val`. -/
private lemma val32 : (32 : ZMod p).val = 32 := by
  rw [show ((32 : ZMod p)) = ((32 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast_of_lt h32p]

/-- The `LTU` flag literal round-trips through `ZMod.val`. -/
private lemma val1 : (1 : ZMod p).val = 1 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  exact ZMod.val_one p

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` is a genuine 24-bit value once its limbs
are 16/8-bit — the push side of `MemoryMsg.ClkBound` for a bump row. The `p ≤ 2^24` branch mirrors
`Channels.MemoryMsg.clkBound_of_cpuState_bounds`: there every value is `< 2^24` outright, which keeps
the lemma inside the project-standard `Fact (2^17 < p)`. -/
private lemma clkLow_lt_2pow24 {a b : ZMod p} (ha : a.val < 2 ^ 16) (hb : b.val < 2 ^ 8) :
    (a + b * 65536).val < 2 ^ 24 := by
  by_cases hp : p ≤ 2 ^ 24
  · exact lt_of_lt_of_le (ZMod.val_lt _) hp
  have hp24 : 2 ^ 24 < p := by omega
  have hmul : (b * 65536).val = b.val * 65536 := by
    rw [ZMod.val_mul_of_lt (by rw [val_65536_zmod_p]; omega), val_65536_zmod_p]
  rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]
  omega

theorem soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
      (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start
  simp only [circuit_norm, byteChannel, memoryChannel, Channels.MemoryMsg.isU64,
    Channels.MemoryMsg.ClkBound] at h_holds ⊢
  obtain ⟨h_gate, b016, b3248, bpair, bltu, a_cl, a_hieq, a_diff, bdlow, bdhigh, h_mem⟩ := h_holds
  have h_bool := bool_of_mul_pred h_gate
  refine ⟨⟨h_bool, fun hr1 => ?_⟩,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun h1 h0 => off_gate_vacuous h_bool h1 h0,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun h1 h0 => off_gate_vacuous h_bool h1 h0,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun h1 h0 => off_gate_vacuous h_bool h1 h0,
    fun h1 h0 => off_gate_vacuous h_bool h1 h0, fun _ h0 => ?_⟩
  · -- the `Spec` consequent on a real row
    have hneg : -input_is_real = -1 := by rw [hr1]
    rw [hr1, one_mul] at a_cl a_hieq a_diff
    obtain ⟨hisu, hclk⟩ := h_mem hneg
    refine ⟨hisu, hclk,
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact b016 hneg),
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact b3248 hneg),
      ((byteRowSpec_u8range_pair _ _).mp (bpair hneg)).1,
      ((byteRowSpec_u8range_pair _ _).mp (bpair hneg)).2,
      ?_, bool_of_mul_pred a_cl, a_hieq, by linear_combination a_diff,
      (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact bdlow hneg),
      ((byteRowSpec_u8range_pair _ _).mp (bdhigh hneg)).1⟩
    -- the register index: project the byte-bus `LTU` fact through `a = 1`
    have hltu := (byteRowSpec_ltu _ _ _).mp (bltu hneg)
    have := hltu.2.2.mp rfl
    rwa [val32] at this
  · -- the refreshed push's requirement: same value word as the pull, own canonical limbs
    have hr1 := h_bool.resolve_left h0
    have hneg : -input_is_real = -1 := by rw [hr1]
    obtain ⟨hisu, -⟩ := h_mem hneg
    exact ⟨hisu, clkLow_lt_2pow24
      ((byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact b016 hneg))
      (((byteRowSpec_u8range_pair _ _).mp (bpair hneg)).1)⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
      (fun input _ _ => Spec input) (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_bool, h_gated⟩ := h_assumptions
  rcases h_bool with h0 | h1
  · -- padding row: the gated asserts vanish, the gated pulls fire only off-padding
    have hne : ∀ {P : Prop}, -input_is_real = -1 → P :=
      fun h => absurd (neg_inj.mp h) (by rw [h0]; exact zero_ne_one)
    exact ⟨by rw [h0, zero_mul], hne, hne, hne, hne, by rw [h0, zero_mul],
      by rw [h0, zero_mul], by rw [h0, zero_mul], hne, hne, hne⟩
  · -- real row: everything from the `Spec` tail
    obtain ⟨hisu, hclk, r016, r3248, r1624, r2432, haddr, hcl, hhieq, hdiff, rdlow, rdhigh⟩ :=
      h_gated h1
    refine ⟨by rw [h1, sub_self, mul_zero],
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr r016,
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr r3248,
      fun _ => (byteRowSpec_u8range_pair _ _).mpr ⟨r1624, r2432⟩,
      fun _ => (byteRowSpec_ltu _ _ _).mpr
        ⟨⟨by rw [val1]; norm_num, by omega, by rw [val32]; norm_num⟩,
         Or.inr rfl, ⟨fun _ => by rw [val32]; exact haddr, fun _ => rfl⟩⟩,
      by rw [h1, one_mul]; rcases hcl with h | h <;> simp [h],
      by rw [h1, one_mul]; linear_combination hhieq,
      by rw [h1, one_mul]; linear_combination hdiff,
      fun _ => (byteRowSpec_range _ sixteen_lt).mpr rdlow,
      fun _ => (byteRowSpec_u8range_pair _ _).mpr ⟨rdhigh, by rw [ZMod.val_zero]; norm_num⟩,
      fun _ => ⟨hisu, hclk⟩⟩

/-- The MemoryBump system table as a `GeneralFormalCircuit`: the register-record timestamp refresh.
`Assumptions := True` (everything is proved in-circuit or received from the byte/memory pulls);
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
  channelsWithRequirements := [memoryChannel.toRaw]
  requirementsChannelsLawful := fun input_var i₀ => by
    change Operations.RequirementsChannelsLawful
      ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
        .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p))
        [byteChannel.toRaw, memoryChannel.toRaw] [memoryChannel.toRaw]
    dsimp only [Operations.RequirementsChannelsLawful]
    refine ⟨by simp only [circuit_norm], ?_, ?_⟩
    · intro channel h_channel
      simp only [circuit_norm] at h_channel
      rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact Or.inl List.mem_cons_self
          | exact Or.inr List.mem_cons_self
    · intro env h_constraints
      have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
          (ProvableStruct.eval env input_var).is_real = 1 := by
        apply bool_of_mul_pred
        simpa only [circuit_norm] using h_constraints.1
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction h_interaction
      simp only [circuit_norm] at h_interaction
      -- The byte pulls and the record pull are `is_real`-gated (off-gate vacuous); only the
      -- refreshed **push** (unnegated multiplicity) is delegated to `channelsWithRequirements`.
      rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | (right; rw [ChannelInteraction.toRaw_requirements]; intro h1 h0;
             simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_bool h1 h0)
          | exact Or.inl List.mem_cons_self

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] := rfl

end SP1Clean.MemoryBumpChip
