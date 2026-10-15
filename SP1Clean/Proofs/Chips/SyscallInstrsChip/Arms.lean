import SP1Clean.Native.Chips.SyscallInstrsChip.Arms
import Clean.Utils.Tactics

/-! # The `SyscallInstrs` arms' soundness and completeness

One bundled `FormalAssertion` per arm. Each proof sees only the constraints of its own arm, which
is the whole point of the decomposition — see the module docstring of
`Native/Chips/SyscallInstrsChip/Arms.lean`. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- A gated constraint holds when the gate is boolean and the gated fact holds on a live gate. -/
private lemma gate_zero {x y : ZMod p}
    (hx : x = 0 ∨ x = 1) (h : x = 1 → y = 0) : x * y = 0 := by
  rcases hx with h0 | h1
  · rw [h0]; ring
  · rw [h1, one_mul]; exact h h1

omit [Fact (2 ^ 17 < p)] in
private lemma one_sub_bool {x : ZMod p}
    (hx : x = 0 ∨ x = 1) : (1 : ZMod p) - x = 0 ∨ (1 : ZMod p) - x = 1 := by
  rcases hx with h | h <;> rw [h] <;> simp

omit [Fact (2 ^ 17 < p)] in
omit [Fact (2 ^ 17 < p)] in
private lemma gated_of_cases {x y : ZMod p}
    (h : x = 0 ∨ y = 0) : x * y = 0 := by
  rcases h with h | h <;> rw [h] <;> ring

omit [Fact (2 ^ 17 < p)] in
private lemma eq_zero_of_one_sub {x : ZMod p}
    (h : (1 : ZMod p) - x = 1) : x = 0 := by linear_combination -h

namespace PcArm

omit [Fact (2 ^ 17 < p)] in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_hbin⟩ := h_assumptions
  obtain ⟨e0, e1, e2, h0, h1, h2⟩ := h_holds
  have epc : ∀ i (hi : i < 3),
      Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have enp : ∀ i (hi : i < 3),
      Expression.eval env input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  rw [enp 0 (by norm_num)] at e0 h0
  rw [enp 1 (by norm_num)] at e1 h1
  rw [enp 2 (by norm_num)] at e2 h2
  rw [epc 0 (by norm_num)] at e0
  rw [epc 1 (by norm_num)] at e1
  rw [epc 2 (by norm_num)] at e2
  refine ⟨fun hh => ?_, fun hr hnh => ?_⟩
  · rw [hh, one_mul] at h0 h1 h2
    exact ⟨by linear_combination h0, h1, h2⟩
  · rw [hr, one_mul, hnh] at e0 e1 e2
    simp only [sub_zero, one_mul] at e0 e1 e2
    exact ⟨by linear_combination e0, by linear_combination e1, by linear_combination e2⟩

omit [Fact (2 ^ 17 < p)] in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_hbin⟩ := h_assumptions
  obtain ⟨h_halt, h_next⟩ := h_spec
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have enp : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  simp only [epc, enp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_next hr (eq_zero_of_one_sub hg)).1))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_next hr (eq_zero_of_one_sub hg)).2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_next hr (eq_zero_of_one_sub hg)).2.2))
  · exact gate_zero h_hbin (fun hh => by linear_combination (h_halt hh).1)
  · exact gate_zero h_hbin (fun hh => (h_halt hh).2.1)
  · exact gate_zero h_hbin (fun hh => (h_halt hh).2.2)

/-- The program-counter arm as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithGuarantees :
    ((circuit (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithRequirements :
    ((circuit (p := p)).channelsWithRequirements : List (RawChannel (ZMod p))) = [] := rfl

end PcArm

namespace CommitArm

omit [Fact (2 ^ 17 < p)] in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_cbin, h_dbin, h_sumbin⟩ := h_assumptions
  have ebits : ∀ i (hi : i < 8),
      Expression.eval env input_var_index_bits[i] = input_index_bits[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have edw : ∀ i (hi : i < 4),
      Expression.eval env input_var_digest_word[i] = input_digest_word[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  have eob : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_b[i] = input_op_b[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.1; simpa using this
  have eoc : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_c[i] = input_op_c[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.1; simpa using this
  simp only [circuit_norm, ebits, edw, eob, eoc] at h_holds
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hs1, hs0, x0, x1, x2, x3, x4, x5, x6, x7,
    hup, hp0, hp1, hp2, hp3⟩ := h_holds
  have boolOf : ∀ x : ZMod p, input_is_real * (x * (x - 1)) = 0 → input_is_real = 1 →
      (x = 0 ∨ x = 1) := by
    intro x hx hr
    apply bool_of_mul_pred
    rw [hr, one_mul] at hx
    exact hx
  have idxOf : ∀ (x v : ZMod p), input_is_real * (x * (input_op_b[0] - v)) = 0 →
      input_is_real = 1 → x = 1 → input_op_b[0] = v := by
    intro x v hx hr h1
    rw [hr, one_mul, h1, one_mul] at hx
    linear_combination hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hr
    fin_cases i
    · exact boolOf _ b0 hr
    · exact boolOf _ b1 hr
    · exact boolOf _ b2 hr
    · exact boolOf _ b3 hr
    · exact boolOf _ b4 hr
    · exact boolOf _ b5 hr
    · exact boolOf _ b6 hr
    · exact boolOf _ b7 hr
  · intro hr i hb
    fin_cases i
    · simpa using idxOf _ _ x0 hr hb
    · simpa using idxOf _ _ x1 hr hb
    · simpa using idxOf _ _ x2 hr hb
    · simpa using idxOf _ _ x3 hr hb
    · simpa using idxOf _ _ x4 hr hb
    · simpa using idxOf _ _ x5 hr hb
    · simpa using idxOf _ _ x6 hr hb
    · simpa using idxOf _ _ x7 hr hb
  · intro hr hc
    rw [hr, one_mul, hc, one_mul] at hs1
    simp only [bitSum]
    linear_combination hs1
  · intro hr hc
    rw [hr, one_mul, hc] at hs0
    simp only [sub_zero, one_mul, bitSum] at hs0 ⊢
    linear_combination hs0
  · intro hr hc
    rw [hr, one_mul, hc, one_mul] at hup
    exact hup
  · intro hr hc
    rw [hr, one_mul, hc, one_mul] at hp0 hp1 hp2 hp3
    exact ⟨by linear_combination -hp0, by linear_combination -hp1, hp2, hp3⟩

omit [Fact (2 ^ 17 < p)] in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_cbin, h_dbin, h_sumbin⟩ := h_assumptions
  obtain ⟨h_bits, h_idx, h_sum1, h_sum0, h_up, h_pack⟩ := h_spec
  have ebits : ∀ i (hi : i < 8),
      Expression.eval env.toEnvironment input_var_index_bits[i] = input_index_bits[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have edw : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_digest_word[i] = input_digest_word[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  have eob : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_b[i] = input_op_b[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.1; simpa using this
  have eoc : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_c[i] = input_op_c[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.1; simpa using this
  simp only [circuit_norm, ebits, edw, eob, eoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 0 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 1 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 2 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 3 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 4 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 5 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 6 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 7 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_sumbin hr) (fun hc => by
      have := h_sum1 hr hc; simp only [bitSum] at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool (h_sumbin hr)) (fun hg => by
      have := h_sum0 hr (eq_zero_of_one_sub hg); simp only [bitSum] at this
      linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 0 hr) (fun hb => by
      have := h_idx hr 0 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 1 hr) (fun hb => by
      have := h_idx hr 1 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 2 hr) (fun hb => by
      have := h_idx hr 2 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 3 hr) (fun hb => by
      have := h_idx hr 3 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 4 hr) (fun hb => by
      have := h_idx hr 4 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 5 hr) (fun hb => by
      have := h_idx hr 5 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 6 hr) (fun hb => by
      have := h_idx hr 6 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_bits 7 hr) (fun hb => by
      have := h_idx hr 7 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_sumbin hr) (fun hc => h_up hr hc))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin (fun hc => by
      linear_combination -(h_pack hr hc).1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin (fun hc => by
      linear_combination -(h_pack hr hc).2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin (fun hc => (h_pack hr hc).2.2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin (fun hc => (h_pack hr hc).2.2.2))

/-- The commit arms as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithGuarantees :
    ((circuit (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithRequirements :
    ((circuit (p := p)).channelsWithRequirements : List (RawChannel (ZMod p))) = [] := rfl

end CommitArm

namespace WriteArm

omit [Fact (2 ^ 17 < p)] in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_a0bin, h_ebin, h_sumbin⟩ := h_assumptions
  have eap : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_a_prev[i] = input_op_a_prev[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have eav : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  simp only [circuit_norm, eap, eav] at h_holds
  obtain ⟨hz, z0, z1, z2, z3, e0, e1, e2, e3, u0, u1, u2, u3⟩ := h_holds
  have ax : ∀ (i : Fin 4), input_op_a_0 = 1 → input_op_a_value[i] = 0 := by
    intro i h1
    fin_cases i
    · rw [h1, one_mul] at z0; exact z0
    · rw [h1, one_mul] at z1; exact z1
    · rw [h1, one_mul] at z2; exact z2
    · rw [h1, one_mul] at z3; exact z3
  have ae : ∀ (i : Fin 4), input_is_real = 1 → input_is_enter_unconstrained = 1 →
      input_op_a_value[i] = 0 := by
    intro i hr he
    fin_cases i
    · rw [hr, one_mul, he, one_mul] at e0; exact e0
    · rw [hr, one_mul, he, one_mul] at e1; exact e1
    · rw [hr, one_mul, he, one_mul] at e2; exact e2
    · rw [hr, one_mul, he, one_mul] at e3; exact e3
  have au : ∀ (i : Fin 4), input_is_real = 1 →
      input_is_enter_unconstrained + input_is_hint_len = 0 →
      input_op_a_value[i] = input_op_a_prev[i] := by
    intro i hr hs
    fin_cases i
    · rw [hr, one_mul, hs] at u0; linear_combination -u0
    · rw [hr, one_mul, hs] at u1; linear_combination -u1
    · rw [hr, one_mul, hs] at u2; linear_combination -u2
    · rw [hr, one_mul, hs] at u3; linear_combination -u3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hr; rw [hr, one_mul] at hz; exact hz
  · intro hzo i; exact ax i hzo
  · intro hr he i; exact ae i hr he
  · intro hr hs i; exact au i hr hs

omit [Fact (2 ^ 17 < p)] in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_a0bin, h_ebin, h_sumbin⟩ := h_assumptions
  obtain ⟨h_real0, h_x0, h_enter, h_unch⟩ := h_spec
  have eap : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_a_prev[i] = input_op_a_prev[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have eav : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  simp only [circuit_norm, eap, eav]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gate_zero h_rbin h_real0
  · exact gate_zero h_a0bin (fun hz => h_x0 hz 0)
  · exact gate_zero h_a0bin (fun hz => h_x0 hz 1)
  · exact gate_zero h_a0bin (fun hz => h_x0 hz 2)
  · exact gate_zero h_a0bin (fun hz => h_x0 hz 3)
  · exact gate_zero h_rbin (fun hr => gate_zero (h_ebin hr) (fun he => h_enter hr he 0))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_ebin hr) (fun he => h_enter hr he 1))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_ebin hr) (fun he => h_enter hr he 2))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_ebin hr) (fun he => h_enter hr he 3))
  · exact gate_zero h_rbin (fun hr => gated_of_cases ((h_sumbin hr).elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_unch hr h0 0)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gated_of_cases ((h_sumbin hr).elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_unch hr h0 1)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gated_of_cases ((h_sumbin hr).elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_unch hr h0 2)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gated_of_cases ((h_sumbin hr).elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_unch hr h0 3)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))

/-- The `t0` write arms as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithGuarantees :
    ((circuit (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithRequirements :
    ((circuit (p := p)).channelsWithRequirements : List (RawChannel (ZMod p))) = [] := rfl

end WriteArm

namespace FieldBoundArm

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_u16⟩ := h_assumptions
  have hbound : ((fieldLimbBound : ℕ) : ZMod p).val = fieldLimbBound := by
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by simp only [fieldLimbBound]; omega)
  have ew : ∀ i (hi : i < 4),
      Expression.eval env input_var_word[i] = input_word[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  simp only [circuit_norm, ew] at h_holds
  obtain ⟨h2, h3, h_cmp, hc1, hc0⟩ := h_holds
  have hspec := h_cmp ⟨fun hr => ⟨h_u16 hr, by rw [hbound]; simp only [fieldLimbBound]; omega⟩,
    h_rbin⟩
  have hb : input_bit = 0 ∨ input_bit = 1 := by simpa using hspec.1
  refine ⟨⟨hb, fun hr => ?_⟩, Or.inl rfl⟩
  have hbit : input_bit = (if (input_word[1]).val < fieldLimbBound then 1 else 0) := by
    have := hspec.2 hr
    rwa [hbound] at this
  refine ⟨hbit, ?_, ?_, ?_⟩
  · rw [hr, one_mul] at h2; exact h2
  · rw [hr, one_mul] at h3; exact h3
  · by_cases hlt : (input_word[1]).val < fieldLimbBound
    · exact Or.inl hlt
    have hbit0 : input_bit = 0 := by rw [hbit, if_neg hlt]
    refine Or.inr ⟨?_, ?_⟩
    · rw [hr, one_mul, hbit0] at hc1
      have heq : input_word[1] = ((fieldLimbBound : ℕ) : ZMod p) := by linear_combination -hc1
      rw [heq, hbound]
    · rw [hr, one_mul, hbit0] at hc0
      linear_combination -hc0

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_u16⟩ := h_assumptions
  obtain ⟨h_bitbool, h_live⟩ := h_spec
  have hbound : ((fieldLimbBound : ℕ) : ZMod p).val = fieldLimbBound := by
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by simp only [fieldLimbBound]; omega)
  have ew : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_word[i] = input_word[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  simp only [circuit_norm, ew]
  refine ⟨gate_zero h_rbin (fun hr => (h_live hr).2.1),
    gate_zero h_rbin (fun hr => (h_live hr).2.2.1), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact ⟨fun hr => ⟨h_u16 hr, by rw [hbound]; simp only [fieldLimbBound]; omega⟩, h_rbin⟩
  · exact ⟨h_bitbool, fun hr => by rw [(h_live hr).1, hbound]⟩
  · exact gate_zero h_rbin (fun hr => gated_of_cases (by
      by_cases hlt : (input_word[1]).val < fieldLimbBound
      · exact Or.inl (by rw [(h_live hr).1, if_pos hlt]; ring)
      · refine Or.inr ?_
        rcases (h_live hr).2.2.2 with h | h
        · exact absurd h hlt
        · have : input_word[1] = ((fieldLimbBound : ℕ) : ZMod p) := by
            have h2 : ((input_word[1]).val : ZMod p) = ((fieldLimbBound : ℕ) : ZMod p) := by
              rw [h.1]
            simpa [ZMod.natCast_val, ZMod.cast_id] using h2
          rw [this]; ring))
  · exact gate_zero h_rbin (fun hr => gated_of_cases (by
      by_cases hlt : (input_word[1]).val < fieldLimbBound
      · exact Or.inl (by rw [(h_live hr).1, if_pos hlt]; ring)
      · refine Or.inr ?_
        rcases (h_live hr).2.2.2 with h | h
        · exact absurd h hlt
        · exact h.2))

/-- One valid-field-element check as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := fun input_var i₀ => by
      preserve_tactic_target
      simp only [circuit_norm, main, U16CompareOperation.circuit] }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithRequirements :
    ((circuit (p := p)).channelsWithRequirements : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithGuarantees :
    ((circuit (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [byteChannel.toRaw] := rfl

end FieldBoundArm

namespace DispatchArm

omit [Fact (2 ^ 17 < p)] in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have eob : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_b[i] = input_op_b[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have eoc : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_c[i] = input_op_c[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  simp only [circuit_norm, eob, eoc] at h_holds
  obtain ⟨hb, hc⟩ := h_holds
  intro ht
  rw [ht, one_mul] at hb hc
  exact ⟨hb, hc⟩

omit [Fact (2 ^ 17 < p)] in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have eob : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_b[i] = input_op_b[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have eoc : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_c[i] = input_op_c[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  simp only [circuit_norm, eob, eoc]
  exact ⟨gate_zero h_assumptions (fun ht => (h_spec ht).1),
    gate_zero h_assumptions (fun ht => (h_spec ht).2)⟩

/-- The generic-dispatch check as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithGuarantees :
    ((circuit (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_channelsWithRequirements :
    ((circuit (p := p)).channelsWithRequirements : List (RawChannel (ZMod p))) = [] := rfl

end DispatchArm

end SP1Clean.SyscallInstrsChip
