import SP1Clean.Native.Chips.BranchChip.Defs
import SP1Clean.Proofs.Chips.BranchChip.Decision

/-! # Computed branch decisions

The existing signed-comparison certificate determines the branch bit. Binary selectors
and bounded operands suffice; callers provide neither a decision hint nor its validity.
-/

namespace SP1Clean.BranchChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The generated comparison satisfies its semantic contract in the selected mode. -/
theorem populateComparison_spec (input : Inputs (ZMod p))
    (h₁ : Word.isU64 (rs1WordInput input)) (h₂ : Word.isU64 (rs2WordInput input))
    (hf : ∀ i : Fin 6, input.flags[i] = 0 ∨ input.flags[i] = 1)
    (hr : input.is_real = 0 ∨ input.is_real = 1) :
    LtOperationSigned.Spec
      ⟨rs1WordInput input, rs2WordInput input, populateComparison input,
       input.isBlt + input.isBge, input.is_real⟩ := by
  have hs := signed_selector_valid (hf 0) (hf 1) (hf 2) (hf 3) (hf 4) (hf 5) hr
  exact LtOperationSigned.spec_populate h₁ h₂ hs.1 hr hs.2

/-- The computed branch bit is binary, including on padding. -/
theorem populateBranching_binary (input : Inputs (ZMod p))
    (h₁ : Word.isU64 (rs1WordInput input)) (h₂ : Word.isU64 (rs2WordInput input))
    (hf : ∀ i : Fin 6, input.flags[i] = 0 ∨ input.flags[i] = 1)
    (hr : input.is_real = 0 ∨ input.is_real = 1) :
    populateBranching input = 0 ∨ populateBranching input = 1 := by
  have hs := populateComparison_spec input h₁ h₂ hf hr
  exact branchDecision_binary (hf 0) (hf 1) (hf 2) (hf 3) (hf 4) (hf 5) hr
    hs.2.2.1.1 (LtOperationSigned.flags_sum_binary hs)

/-- Zero activity computes a zero branch bit independently of the operands. -/
theorem populateBranching_inactive (input : Inputs (ZMod p))
    (hf : ∀ i : Fin 6, input.flags[i] = 0 ∨ input.flags[i] = 1)
    (hr : input.is_real = 0) : populateBranching input = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    flags_zero_of_sum_zero (hf 0) (hf 1) (hf 2) (hf 3) (hf 4) (hf 5) hr
  dsimp [Inputs.flags] at h0 h1 h2 h3 h4 h5
  simp only [populateBranching, branchDecision, h0, h1, h2, h3, h4, h5,
    zero_mul, zero_add]

/-- The computed decision agrees with the selected RV64 branch condition. -/
theorem populateBranching_conditions (input : Inputs (ZMod p))
    (h₁ : Word.isU64 (rs1WordInput input)) (h₂ : Word.isU64 (rs2WordInput input))
    (hf : ∀ i : Fin 6, input.flags[i] = 0 ∨ input.flags[i] = 1)
    (hr : input.is_real = 1) :
    (input.isBeq = 1 → (populateBranching input = 1 ↔
      Word.toBitVec64 (rs1WordInput input) = Word.toBitVec64 (rs2WordInput input))) ∧
    (input.isBne = 1 → (populateBranching input = 1 ↔
      Word.toBitVec64 (rs1WordInput input) ≠ Word.toBitVec64 (rs2WordInput input))) ∧
    (input.isBlt = 1 → (populateBranching input = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (input.isBge = 1 → (populateBranching input = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = false)) ∧
    (input.isBltu = 1 → (populateBranching input = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (input.isBgeu = 1 → (populateBranching input = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = false)) := by
  have hs := populateComparison_spec input h₁ h₂ hf (Or.inr hr)
  obtain ⟨hbit, heq⟩ := LtOperationSigned.result_semantic hs hr
  exact branch_conditions_of_decision_eq h₁ h₂ (hf 0) (hf 1) (hf 2) (hf 3) (hf 4) (hf 5)
    (populateBranching_binary input h₁ h₂ hf (Or.inr hr)) hr hbit heq rfl

end SP1Clean.BranchChip
