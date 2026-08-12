import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Math.Gate

/-! # `SP1Clean.BranchChip` — the six-way decision dispatch (shared field lemmas)

The BRANCH chip relates the prover's `is_branching` bit to a six-way, one-hot opcode dispatch
(BEQ/BNE/BLT/BGE/BLTU/BGEU). Both soundness and completeness need this dispatch, in opposite
directions:

* `branch_conditions_of_decision_eq` — from the in-circuit decision equation `is_branching = decision`
  derive the six per-opcode `is_branching = 1 ↔ <RV64 condition>` biconditionals (soundness);
* `branch_decision_eq_of_conditions` — the dual: from the six biconditionals reconstruct
  `is_branching = decision` (completeness / honest-prover witness generation).

Both are stated over **plain `ZMod p` field elements** and two operand words — no `Environment`/circuit
context — so the heavy one-hot case analysis is elaborated **once, in a small context** instead of twice
under the giant `circuit_proof_start` chip goal. This is what lets `Formal.lean`'s soundness/completeness
drop their `maxHeartbeats` ceilings.

The flag↔index convention matches `Defs.lean`'s `main` and `FormalModel/Contracts/Chips.lean`'s `Spec`:
`is_beq = b0, is_bne = b1, is_blt = b2, is_bge = b3, is_bltu = b4, is_bgeu = b5`; the signed-compare
selector is `is_signed = is_blt + is_bge = b2 + b3`; `is_eq = 1 - sum` where `sum` is the four
`u16_flags`; and
`decision = b0·(1-sum) + b1·(1-(1-sum)) + (b3+b5)·(1-bit) + (b2+b4)·bit`. -/

namespace SP1Clean.BranchChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-! ## Field micro-lemmas (binary-element algebra) -/

/-- `(0 : ZMod p) ≠ 1` (since `2^17 < p`). -/
lemma zero_ne_one' : (0 : ZMod p) ≠ 1 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  exact zero_ne_one

/-- The `ℕ`-value of a binary field element (`0` or `1`). -/
lemma val_of_bool {b : ZMod p} (h : b = 0 ∨ b = 1) : b.val = 0 ∨ b.val = 1 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rcases h with h | h <;> rw [h] <;> simp [ZMod.val_one]

/-- **One-hot.** Six binary flags whose sum is binary have at most one flag set: the sum of all six
values is `≤ 1`. -/
lemma one_hot6 {b0 b1 b2 b3 b4 b5 : ZMod p}
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1) (h2 : b2 = 0 ∨ b2 = 1)
    (h3 : b3 = 0 ∨ b3 = 1) (h4 : b4 = 0 ∨ b4 = 1) (h5 : b5 = 0 ∨ b5 = 1)
    (hsum : (b0 + b1 + b2 + b3 + b4 + b5) * (b0 + b1 + b2 + b3 + b4 + b5 - 1) = 0) :
    b0.val + b1.val + b2.val + b3.val + b4.val + b5.val ≤ 1 := by
  have hp : (7 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  set S := b0 + b1 + b2 + b3 + b4 + b5 with hS
  have v0 := bool_val_le h0; have v1 := bool_val_le h1; have v2 := bool_val_le h2
  have v3 := bool_val_le h3; have v4 := bool_val_le h4; have v5 := bool_val_le h5
  have hScast : S = ((b0.val + b1.val + b2.val + b3.val + b4.val + b5.val : ℕ) : ZMod p) := by
    rw [hS]; push_cast [ZMod.natCast_zmod_val]; ring
  have hSval : S.val = b0.val + b1.val + b2.val + b3.val + b4.val + b5.val := by
    rw [hScast]; exact ZMod.val_natCast_of_lt (by omega)
  have hSbool : S.val = 0 ∨ S.val = 1 := by
    rcases bool_of_mul_pred hsum with h | h
    · left; rw [h, ZMod.val_zero]
    · right; rw [h, ZMod.val_one]
  omega

/-- Six binary flags whose field sum is one form the exact disjunction used by the Branch
semantic contract.  Keeping the finite case split here prevents the whole-chip soundness proof
from elaborating it under the full circuit context. -/
lemma flagsOneHot_of_sum_one {b0 b1 b2 b3 b4 b5 : ZMod p}
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1) (h2 : b2 = 0 ∨ b2 = 1)
    (h3 : b3 = 0 ∨ b3 = 1) (h4 : b4 = 0 ∨ b4 = 1) (h5 : b5 = 0 ∨ b5 = 1)
    (hsum : b0 + b1 + b2 + b3 + b4 + b5 = 1) :
    (b0 = 1 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0) ∨
      (b1 = 1 ∧ b0 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0) ∨
      (b2 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0) ∨
      (b3 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b4 = 0 ∧ b5 = 0) ∨
      (b4 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b5 = 0) ∨
      (b5 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0) := by
  have atMost := one_hot6 h0 h1 h2 h3 h4 h5 (by rw [hsum]; simp)
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
    rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl
  all_goals
    simp only [ZMod.val_zero, ZMod.val_one] at atMost
    first | omega | simp at hsum ⊢

/-- **One-hot, resolved.** If the binary flag `x` is set and the six binary flags sum to `1`, the
other five are zero. This is the per-branch specialisation both dispatch lemmas below need; the
argument order is permuted at each call site, with the sum hypothesis carried by
`linear_combination`. -/
private lemma rest_zero {x y z w u v : ZMod p} (hx : x = 1)
    (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1)
    (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1) (hsum : x + y + z + w + u + v = 1) :
    y = 0 ∧ z = 0 ∧ w = 0 ∧ u = 0 ∧ v = 0 := by
  have hle := one_hot6 (Or.inr hx) hy hz hw hu hv (by rw [hsum]; simp)
  have hxv : x.val = 1 := by rw [hx]; simp [ZMod.val_one]
  exact ⟨(ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega),
    (ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega),
    (ZMod.val_eq_zero _).mp (by omega)⟩

omit [Fact (2 ^ 17 < p)] in
/-- A binary `x` with `x = 1 ↔ ¬ P` (where `bit = if P then 1 else 0`) is `1 - bit`. -/
private lemma bool_eq_one_sub_ite {x bit : ZMod p} (hx : x = 0 ∨ x = 1) {P : Prop} [Decidable P]
    (hbit : bit = if P then 1 else 0) (h : x = 1 ↔ ¬ P) : x = 1 - bit := by
  by_cases hP : P
  · rw [hbit, if_pos hP, sub_self]; exact hx.resolve_right fun h1 => h.mp h1 hP
  · rw [hbit, if_neg hP, sub_zero]; exact h.mpr hP

omit [Fact (2 ^ 17 < p)] in
/-- A binary `x` with `x = 1 ↔ y ≠ 0` (for binary `y`) equals `y`. -/
private lemma bool_eq_of_iff_ne {x y : ZMod p} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (h : x = 1 ↔ y ≠ 0) : x = y := by
  rcases hy with rfl | rfl
  · exact hx.resolve_right fun h1 => h.mp h1 rfl
  · exact h.mpr one_ne_zero

/-! ## The six-way decision dispatch

`branchDecision` is the in-circuit decision expression; the two lemmas below are the dual readings of
`is_branching = branchDecision`. They take the signed-compare gadget couplings (`h_bit`/`h_eqf`/`h_eqbin`)
in exactly the form `LtOperationSigned.Spec` exposes them (after the operand-word eval bridges). -/

/-- The in-circuit branch decision as a field expression (matches `Defs.main`'s `decision`). -/
def branchDecision (b0 b1 b2 b3 b4 b5 bit sum : ZMod p) : ZMod p :=
  b0 * (1 - sum) + b1 * (1 - (1 - sum)) + (b3 + b5) * (1 - bit) + (b2 + b4) * bit

/-- **Soundness direction.** Given the in-circuit decision equation `br = branchDecision …`, the six
binary opcode flags (one-hot, summing to `1`), the binary `br`, and the signed-compare couplings, derive
the six per-opcode `br = 1 ↔ <RV64 condition>` biconditionals (verbatim `FormalModel/Contracts/Chips.lean` Branch `Spec`
form). -/
lemma branch_conditions_of_decision_eq {rs1 rs2 : Word (ZMod p)}
    (hrs1U : Word.isU64 rs1) (hrs2U : Word.isU64 rs2)
    {b0 b1 b2 b3 b4 b5 br bit sum : ZMod p}
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1)
    (hb3 : b3 = 0 ∨ b3 = 1) (hb4 : b4 = 0 ∨ b4 = 1) (hb5 : b5 = 0 ∨ b5 = 1)
    (hbr : br = 0 ∨ br = 1) (hone : b0 + b1 + b2 + b3 + b4 + b5 = 1)
    (h_bit : bit = if (if b2 + b3 = 1
        then (Word.toBitVec64 rs1).toInt < (Word.toBitVec64 rs2).toInt
        else Word.toNat rs1 < Word.toNat rs2) then 1 else 0)
    (h_eqf : b2 + b3 = 0 → (sum = 0 ↔ Word.toBitVec64 rs1 = Word.toBitVec64 rs2))
    (hbrdec : br = branchDecision b0 b1 b2 b3 b4 b5 bit sum) :
    (b0 = 1 → (br = 1 ↔ Word.toBitVec64 rs1 = Word.toBitVec64 rs2))
      ∧ (b1 = 1 → (br = 1 ↔ Word.toBitVec64 rs1 ≠ Word.toBitVec64 rs2))
      ∧ (b2 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).slt (Word.toBitVec64 rs2) = true))
      ∧ (b3 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).slt (Word.toBitVec64 rs2) = false))
      ∧ (b4 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).ult (Word.toBitVec64 rs2) = true))
      ∧ (b5 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).ult (Word.toBitVec64 rs2) = false)) := by
  simp only [branchDecision] at hbrdec
  refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
  · -- BEQ: other five flags zero; `br = 1 - sum`; `is_signed = 0`.
    obtain ⟨e1, e2, e3, e4, e5⟩ := rest_zero hf hb1 hb2 hb3 hb4 hb5 hone
    have hsig0 : b2 + b3 = 0 := by rw [e2, e3]; simp
    rw [hf, e1, e2, e3, e4, e5] at hbrdec
    refine Iff.trans ?_ (h_eqf hsig0)
    constructor
    · intro hib; linear_combination hbrdec - hib
    · intro hF; linear_combination hbrdec - hF
  · -- BNE: `br = sum-indicator`; binary; `br = 1 ↔ sum ≠ 0 ↔ rs1 ≠ rs2`.
    obtain ⟨e0, e2, e3, e4, e5⟩ := rest_zero hf hb0 hb2 hb3 hb4 hb5 (by linear_combination hone)
    have hsig0 : b2 + b3 = 0 := by rw [e2, e3]; simp
    rw [hf, e0, e2, e3, e4, e5] at hbrdec
    refine Iff.trans ?_ (not_congr (h_eqf hsig0))
    constructor
    · intro hib hF; exact zero_ne_one' (by linear_combination -hbrdec + hib - hF)
    · intro hF; rcases hbr with h0 | h1
      · exact absurd (by linear_combination -hbrdec + h0) hF
      · exact h1
  · -- BLT: `br = bit`; `is_signed = 1`; `br = 1 ↔ rs1 <ₛ rs2`.
    obtain ⟨e0, e1, e3, e4, e5⟩ := rest_zero hf hb0 hb1 hb3 hb4 hb5 (by linear_combination hone)
    have hsig1 : b2 + b3 = 1 := by rw [hf, e3]; simp
    rw [hf, e0, e1, e3, e4, e5] at hbrdec
    simp only [if_pos hsig1] at h_bit
    rw [slt_true_iff]
    exact eq_one_iff_of_ite (x := br) (by linear_combination hbrdec + h_bit)
  · -- BGE: `br = 1 - bit`; `is_signed = 1`; `br = 1 ↔ ¬ rs1 <ₛ rs2`.
    obtain ⟨e0, e1, e2, e4, e5⟩ := rest_zero hf hb0 hb1 hb2 hb4 hb5 (by linear_combination hone)
    have hsig1 : b2 + b3 = 1 := by rw [hf, e2]; simp
    rw [hf, e0, e1, e2, e4, e5] at hbrdec
    simp only [if_pos hsig1] at h_bit
    rw [slt_false_iff]
    rw [h_bit] at hbrdec
    refine eq_one_iff_of_one_sub_ite (x := br) ?_
    linear_combination hbrdec
  · -- BLTU: `br = bit`; `is_signed = 0`; `br = 1 ↔ rs1 <ᵤ rs2`.
    obtain ⟨e0, e1, e2, e3, e5⟩ := rest_zero hf hb0 hb1 hb2 hb3 hb5 (by linear_combination hone)
    have hsig0 : ¬ (b2 + b3 = 1) := by rw [e2, e3, add_zero]; exact zero_ne_one'
    rw [hf, e0, e1, e2, e3, e5] at hbrdec
    simp only [if_neg hsig0] at h_bit
    rw [ult_true_iff, Word.toBitVec64_toNat hrs1U, Word.toBitVec64_toNat hrs2U]
    exact eq_one_iff_of_ite (x := br) (by linear_combination hbrdec + h_bit)
  · -- BGEU: `br = 1 - bit`; `is_signed = 0`; `br = 1 ↔ ¬ rs1 <ᵤ rs2`.
    obtain ⟨e0, e1, e2, e3, e4⟩ := rest_zero hf hb0 hb1 hb2 hb3 hb4 (by linear_combination hone)
    have hsig0 : ¬ (b2 + b3 = 1) := by rw [e2, e3, add_zero]; exact zero_ne_one'
    rw [hf, e0, e1, e2, e3, e4] at hbrdec
    simp only [if_neg hsig0] at h_bit
    rw [ult_false_iff, Word.toBitVec64_toNat hrs1U, Word.toBitVec64_toNat hrs2U]
    rw [h_bit] at hbrdec
    refine eq_one_iff_of_one_sub_ite (x := br) ?_
    linear_combination hbrdec

/-- **Completeness direction.** The dual: from the six per-opcode biconditionals (the honest-prover
contract), the one-hot binary flags, and the signed-compare couplings, reconstruct the in-circuit
decision equation `br = branchDecision …`. -/
lemma branch_decision_eq_of_conditions {rs1 rs2 : Word (ZMod p)}
    (hrs1U : Word.isU64 rs1) (hrs2U : Word.isU64 rs2)
    {b0 b1 b2 b3 b4 b5 br bit sum : ZMod p}
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1)
    (hb3 : b3 = 0 ∨ b3 = 1) (hb4 : b4 = 0 ∨ b4 = 1) (hb5 : b5 = 0 ∨ b5 = 1)
    (hbr : br = 0 ∨ br = 1) (hone : b0 + b1 + b2 + b3 + b4 + b5 = 1)
    (h_bit : bit = if (if b2 + b3 = 1
        then (Word.toBitVec64 rs1).toInt < (Word.toBitVec64 rs2).toInt
        else Word.toNat rs1 < Word.toNat rs2) then 1 else 0)
    (h_eqf : b2 + b3 = 0 → (sum = 0 ↔ Word.toBitVec64 rs1 = Word.toBitVec64 rs2))
    (h_eqbin : b2 + b3 = 0 → (sum = 0 ∨ sum = 1))
    (hd0 : b0 = 1 → (br = 1 ↔ Word.toBitVec64 rs1 = Word.toBitVec64 rs2))
    (hd1 : b1 = 1 → (br = 1 ↔ Word.toBitVec64 rs1 ≠ Word.toBitVec64 rs2))
    (hd2 : b2 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).slt (Word.toBitVec64 rs2) = true))
    (hd3 : b3 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).slt (Word.toBitVec64 rs2) = false))
    (hd4 : b4 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).ult (Word.toBitVec64 rs2) = true))
    (hd5 : b5 = 1 → (br = 1 ↔ (Word.toBitVec64 rs1).ult (Word.toBitVec64 rs2) = false)) :
    br = branchDecision b0 b1 b2 b3 b4 b5 bit sum := by
  simp only [branchDecision]
  rcases flagsOneHot_of_sum_one hb0 hb1 hb2 hb3 hb4 hb5 hone with
    ⟨hf0, e1, e2, e3, e4, e5⟩ | ⟨hf1, e0, e2, e3, e4, e5⟩ | ⟨hf2, e0, e1, e3, e4, e5⟩ |
      ⟨hf3, e0, e1, e2, e4, e5⟩ | ⟨hf4, e0, e1, e2, e3, e5⟩ | ⟨hf5, e0, e1, e2, e3, e4⟩
  · -- BEQ (`b0 = 1`): `br = 1 - sum-indicator`, `is_signed = 0`.
    have hsig0 : b2 + b3 = 0 := by rw [e2, e3]; simp
    rw [hf0, e1, e2, e3, e4, e5]
    linear_combination bool_eq_one_sub hbr (h_eqbin hsig0) ((hd0 hf0).trans (h_eqf hsig0).symm)
  · -- BNE (`b1 = 1`): `br = sum-indicator`, `is_signed = 0`.
    have hsig0 : b2 + b3 = 0 := by rw [e2, e3]; simp
    rw [e0, hf1, e2, e3, e4, e5]
    linear_combination bool_eq_of_iff_ne hbr (h_eqbin hsig0)
      ((hd1 hf1).trans (not_congr (h_eqf hsig0)).symm)
  · -- BLT (`b2 = 1`): `br = bit`, `is_signed = 1`.
    have hsig1 : b2 + b3 = 1 := by rw [hf2, e3, add_zero]
    simp only [eq_true hsig1] at h_bit
    have hbreq := (bool_eq_ite_of_iff hbr ((hd2 hf2).trans (slt_true_iff _ _))).trans h_bit.symm
    rw [e0, e1, hf2, e3, e4, e5]
    linear_combination hbreq
  · -- BGE (`b3 = 1`): `br = 1 - bit`, `is_signed = 1`.
    have hsig1 : b2 + b3 = 1 := by rw [e2, hf3, zero_add]
    simp only [eq_true hsig1] at h_bit
    rw [e0, e1, e2, hf3, e4, e5]
    linear_combination bool_eq_one_sub_ite hbr h_bit ((hd3 hf3).trans (slt_false_iff _ _))
  · -- BLTU (`b4 = 1`): `br = bit`, `is_signed = 0`.
    have hsigne : ¬ (b2 + b3 = 1) := by rw [e2, e3, add_zero]; exact zero_ne_one'
    simp only [eq_false hsigne] at h_bit
    have hiff := (hd4 hf4).trans (ult_true_iff _ _)
    rw [Word.toBitVec64_toNat hrs1U, Word.toBitVec64_toNat hrs2U] at hiff
    rw [e0, e1, e2, e3, hf4, e5]
    linear_combination (bool_eq_ite_of_iff hbr hiff).trans h_bit.symm
  · -- BGEU (`b5 = 1`): `br = 1 - bit`, `is_signed = 0`.
    have hsigne : ¬ (b2 + b3 = 1) := by rw [e2, e3, add_zero]; exact zero_ne_one'
    simp only [eq_false hsigne] at h_bit
    have hiff := (hd5 hf5).trans (ult_false_iff _ _)
    rw [Word.toBitVec64_toNat hrs1U, Word.toBitVec64_toNat hrs2U] at hiff
    rw [e0, e1, e2, e3, e4, hf5]
    linear_combination bool_eq_one_sub_ite hbr h_bit hiff

end SP1Clean.BranchChip
