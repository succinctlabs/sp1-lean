import SP1Clean.Math.Word
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # `AddOperation` — the arithmetic core (`RawSpec` + carry-chain lemmas)

The structural carry-bool + limb-range form `RawSpec`, and the two native carry-chain theorems
(`addSemantics_of_carries` / `carries_of_addSemantics`) the gadget's soundness/completeness route
through. Uses only the local `limb_lift`/`val_65536_*` foundations. The `FormalAssertion` contract
lives in the sibling `Formal` module; `Operations/AddOperation.lean` re-exports all three. -/

namespace SP1Clean.AddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Assertion half** — the carry-bool form (the part of SP1's `AddOperation` that comes from the
`asserts` list), stated against the result word `value`. -/
def AssertSpec (a b value : Word (ZMod p)) : Prop :=
  let c0 : ZMod p := (a[0] + b[0] - value[0]) * 65536⁻¹
  let c1 : ZMod p := (a[1] + b[1] - value[1] + c0) * 65536⁻¹
  let c2 : ZMod p := (a[2] + b[2] - value[2] + c1) * 65536⁻¹
  let c3 : ZMod p := (a[3] + b[3] - value[3] + c2) * 65536⁻¹
  (c0 = 0 ∨ c0 = 1) ∧ (c1 = 0 ∨ c1 = 1) ∧ (c2 = 0 ∨ c2 = 1) ∧ (c3 = 0 ∨ c3 = 1)

/-- **Interaction half** — the limb-range form (the part that comes from the byte-range `interactions`
list — four `Range` byte sends). -/
def InteractSpec (value : Word (ZMod p)) : Prop :=
  value[0].val < 65536 ∧ value[1].val < 65536 ∧ value[2].val < 65536 ∧ value[3].val < 65536

/-- Forward (soundness) core — native port of `AddOperation.spec`: the carry-bool +
range form implies the result is a 64-bit value equal to the BitVec sum. -/
theorem addSemantics_of_carries {a b value : Word (ZMod p)}
    (ha : a.isU64) (hb : b.isU64)
    (h_assert : AssertSpec a b value) (h_interact : InteractSpec value) :
    value.isU64 ∧ value.toBitVec64 = a.toBitVec64 + b.toBitVec64 := by
  obtain ⟨hc0, hc1, hc2, hc3⟩ := h_assert
  obtain ⟨hv0, hv1, hv2, hv3⟩ := h_interact
  have h_isU64_v : value.isU64 := Word.isU64_of_cases hv0 hv1 hv2 hv3
  refine ⟨h_isU64_v, ?_⟩
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_isU64_v, Word.toBitVec64_toNat hb, Word.toBitVec64_toNat ha,
      Word.toNat_def, Word.toNat_def, Word.toNat_def]
  set c0 : ZMod p := (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (a[1] + b[1] - value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (a[2] + b[2] - value[2] + c1) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (a[3] + b[3] - value[3] + c2) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : a[0] + b[0] + (0 : ZMod p) = value[0] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (a[0] + b[0] - value[0]) * h65inv
  have e1 : a[1] + b[1] + c0 = value[1] + c1 * 65536 := by
    rw [hc1_def]; linear_combination -1 * (a[1] + b[1] - value[1] + c0) * h65inv
  have e2 : a[2] + b[2] + c1 = value[2] + c2 * 65536 := by
    rw [hc2_def]; linear_combination -1 * (a[2] + b[2] - value[2] + c1) * h65inv
  have e3 : a[3] + b[3] + c2 = value[3] + c3 * 65536 := by
    rw [hc3_def]; linear_combination -1 * (a[3] + b[3] - value[3] + c2) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0 hc_zero hc0 e0
  have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1 hc0 hc1 e1
  have n2 := limb_lift _ _ _ _ _ ha2 hbb2 hv2 hc1 hc2 e2
  have n3 := limb_lift _ _ _ _ _ ha3 hbb3 hv3 hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero] at n0
  have hc0_lt : c0.val ≤ 1 := by rcases hc0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by rcases hc2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by rcases hc3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

/-- Backward (completeness) core — native port of `AddOperation.spec_inv`: a 64-bit
value equal to the BitVec sum witnesses the unique boolean carry chain + ranges. -/
theorem carries_of_addSemantics {a b value : Word (ZMod p)}
    (ha : a.isU64) (hb : b.isU64) (hv : value.isU64)
    (h_bv : value.toBitVec64 = a.toBitVec64 + b.toBitVec64) :
    AssertSpec a b value ∧ InteractSpec value := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hv0, hv1, hv2, hv3⟩ := Word.lt_cases_of_isU64 hv
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat hv, Word.toBitVec64_toNat hb, Word.toBitVec64_toNat ha,
      Word.toNat_def, Word.toNat_def, Word.toNat_def] at h_bv
  set q0 : ℕ := (a[0].val + b[0].val) / 65536 with hq0_def
  set q1 : ℕ := (a[1].val + b[1].val + q0) / 65536 with hq1_def
  set q2 : ℕ := (a[2].val + b[2].val + q1) / 65536 with hq2_def
  set q3 : ℕ := (a[3].val + b[3].val + q2) / 65536 with hq3_def
  have h_chain :
      q0 ≤ 1 ∧ q1 ≤ 1 ∧ q2 ≤ 1 ∧ q3 ≤ 1 ∧
      a[0].val + b[0].val = value[0].val + q0 * 65536 ∧
      a[1].val + b[1].val + q0 = value[1].val + q1 * 65536 ∧
      a[2].val + b[2].val + q1 = value[2].val + q2 * 65536 ∧
      a[3].val + b[3].val + q2 = value[3].val + q3 * 65536 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hq0_def, hq1_def, hq2_def, hq3_def] <;> omega
  obtain ⟨hq0, hq1, hq2, hq3, e0n, e1n, e2n, e3n⟩ := h_chain
  have hc0_lift : (a[0] : ZMod p) + b[0] = value[0] + (q0 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc1_lift : (a[1] : ZMod p) + b[1] + (q0 : ZMod p) = value[1] + (q1 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc2_lift : (a[2] : ZMod p) + b[2] + (q1 : ZMod p) = value[2] + (q2 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e2n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc3_lift : (a[3] : ZMod p) + b[3] + (q2 : ZMod p) = value[3] + (q3 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e3n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  have hc0_eq : (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹ = (q0 : ZMod p) := by
    have h : a[0] + b[0] - value[0] = (q0 : ZMod p) * 65536 := by linear_combination hc0_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc1_eq : (a[1] + b[1] - value[1] +
      (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹ = (q1 : ZMod p) := by
    rw [hc0_eq]
    have h : a[1] + b[1] - value[1] + (q0 : ZMod p) = (q1 : ZMod p) * 65536 := by
      linear_combination hc1_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc2_eq : (a[2] + b[2] - value[2] + ((a[1] + b[1] - value[1] +
      (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹)) *
      (65536 : ZMod p)⁻¹ = (q2 : ZMod p) := by
    rw [hc1_eq]
    have h : a[2] + b[2] - value[2] + (q1 : ZMod p) = (q2 : ZMod p) * 65536 := by
      linear_combination hc2_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc3_eq : (a[3] + b[3] - value[3] + ((a[2] + b[2] - value[2] +
      ((a[1] + b[1] - value[1] +
      (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹)) *
      (65536 : ZMod p)⁻¹)) * (65536 : ZMod p)⁻¹ = (q3 : ZMod p) := by
    rw [hc2_eq]
    have h : a[3] + b[3] - value[3] + (q2 : ZMod p) = (q3 : ZMod p) * 65536 := by
      linear_combination hc3_lift
    rw [h, mul_assoc, h65inv, mul_one]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hv0, hv1, hv2, hv3⟩
  · rw [hc0_eq]; interval_cases q0 <;> simp
  · rw [hc1_eq]; interval_cases q1 <;> simp
  · rw [hc2_eq]; interval_cases q2 <;> simp
  · rw [hc3_eq]; interval_cases q3 <;> simp

end SP1Clean.AddOperation
