import SP1Clean.Math.Word
import SP1Clean.Extracted.LtOperationUnsigned
import SP1Clean.Native.Operations.U16CompareOperation.RawSpec
import SP1Clean.Proofs.Operations.U16CompareOperation.Formal
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Mathlib.Tactic.LinearCombination

/-! # `LtOperationUnsigned` — structural `RawSpec` + soundness cores

Unsigned word less-than `b <ᵤ cc`. The `u16_flags` one-hot-select the most-significant differing
limb; `not_eq_inv` witnesses they differ; a `U16CompareOperation` on the selected limb pair yields
`bit = (b <ᵤ cc)`. `RawSpec` is the literal constraint list at `is_real = 1`.

Soundness cores (`ltUnsigned_core`, `comparison_limbs_lt`, `flags_sum_zero_iff_eq`) live here so
`LtOperationSigned` can reuse them via `ltUnsigned_semantic` without an import cycle. -/

namespace SP1Clean.LtOperationUnsigned

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

omit [Fact (2 ^ 17 < p)] in
/-- A boolean field element has `val ≤ 1`. -/
private lemma bool_val_le {x : ZMod p} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rcases h with h | h <;> simp [h, ZMod.val_one]

set_option maxHeartbeats 1000000 in
/-- Four boolean flags whose field sum is `0` or `1` have **at most one** set: the assignment is
one of the five all-but-one-zero patterns. The key step lifts the field sum-bound to `ℕ`
(`f0.val + … + f3.val ≤ 1`, no wrap since the sum is `< 2^17 < p`), then `omega`/`tauto` decide. -/
private lemma at_most_one {f0 f1 f2 f3 : ZMod p}
    (h0 : f0 = 0 ∨ f0 = 1) (h1 : f1 = 0 ∨ f1 = 1)
    (h2 : f2 = 0 ∨ f2 = 1) (h3 : f3 = 0 ∨ f3 = 1)
    (hs : f0 + f1 + f2 + f3 = 0 ∨ f0 + f1 + f2 + f3 = 1) :
    (f0 = 0 ∧ f1 = 0 ∧ f2 = 0 ∧ f3 = 0) ∨ (f3 = 1 ∧ f0 = 0 ∧ f1 = 0 ∧ f2 = 0) ∨
    (f2 = 1 ∧ f0 = 0 ∧ f1 = 0 ∧ f3 = 0) ∨ (f1 = 1 ∧ f0 = 0 ∧ f2 = 0 ∧ f3 = 0) ∨
    (f0 = 1 ∧ f1 = 0 ∧ f2 = 0 ∧ f3 = 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  have b0 := bool_val_le h0; have b1 := bool_val_le h1
  have b2 := bool_val_le h2; have b3 := bool_val_le h3
  have e : f0 + f1 + f2 + f3 = ((f0.val + f1.val + f2.val + f3.val : ℕ) : ZMod p) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have hle : f0.val + f1.val + f2.val + f3.val ≤ 1 := by
    rcases hs with h | h <;>
      · rw [e] at h
        have hh := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt (show f0.val + f1.val + f2.val + f3.val < p by omega)] at hh
        simp only [ZMod.val_zero, ZMod.val_one] at hh
        omega
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;>
    first
      | (exfalso; simp only [ZMod.val_zero, ZMod.val_one] at hle; omega)
      | tauto

/-- Literal meaning of SP1's `LtOperationUnsigned` constraint list at `is_real = 1`. -/
def RawSpec (b cc : Word (ZMod p)) (cols : Extracted.LtOperationUnsigned (ZMod p)) : Prop :=
  let f0 := cols.u16_flags[0]; let f1 := cols.u16_flags[1]
  let f2 := cols.u16_flags[2]; let f3 := cols.u16_flags[3]
  let cl0 := cols.comparison_limbs[0]; let cl1 := cols.comparison_limbs[1]
  let sumf := f0 + f1 + f2 + f3
  U16CompareOperation.RawSpec cl0 cl1 ⟨cols.u16_compare_operation.bit⟩ ∧
  (f0 = 0 ∨ f0 = 1) ∧ (f1 = 0 ∨ f1 = 1) ∧ (f2 = 0 ∨ f2 = 1) ∧ (f3 = 0 ∨ f3 = 1) ∧
  (sumf = 0 ∨ sumf = 1) ∧
  ((1 - f3) * (b[3] - cc[3]) = 0) ∧
  ((1 - (f3 + f2)) * (b[2] - cc[2]) = 0) ∧
  ((1 - (f3 + f2 + f1)) * (b[1] - cc[1]) = 0) ∧
  ((1 - (f3 + f2 + f1 + f0)) * (b[0] - cc[0]) = 0) ∧
  ((b[3] * f3 + b[2] * f2 + b[1] * f1 + b[0] * f0) - cl0 = 0) ∧
  ((cc[3] * f3 + cc[2] * f2 + cc[1] * f1 + cc[0] * f0) - cl1 = 0) ∧
  (((1 - sumf) - 1) * (cols.not_eq_inv * (cl0 - cl1) - 1) = 0)

/-- The non-`U16Compare` conjuncts of `RawSpec`: the flag booleans, the sum-bound, the four
prefix-sum selectors, the two limb extractions, and the non-equality witness. `RawSpec` is exactly
`U16CompareOperation.RawSpec … ∧ Selectors b cc cols`. -/
def Selectors (b cc : Word (ZMod p)) (cols : Extracted.LtOperationUnsigned (ZMod p)) : Prop :=
  let f0 := cols.u16_flags[0]; let f1 := cols.u16_flags[1]
  let f2 := cols.u16_flags[2]; let f3 := cols.u16_flags[3]
  let cl0 := cols.comparison_limbs[0]; let cl1 := cols.comparison_limbs[1]
  let sumf := f0 + f1 + f2 + f3
  (f0 = 0 ∨ f0 = 1) ∧ (f1 = 0 ∨ f1 = 1) ∧ (f2 = 0 ∨ f2 = 1) ∧ (f3 = 0 ∨ f3 = 1) ∧
  (sumf = 0 ∨ sumf = 1) ∧
  ((1 - f3) * (b[3] - cc[3]) = 0) ∧
  ((1 - (f3 + f2)) * (b[2] - cc[2]) = 0) ∧
  ((1 - (f3 + f2 + f1)) * (b[1] - cc[1]) = 0) ∧
  ((1 - (f3 + f2 + f1 + f0)) * (b[0] - cc[0]) = 0) ∧
  ((b[3] * f3 + b[2] * f2 + b[1] * f1 + b[0] * f0) - cl0 = 0) ∧
  ((cc[3] * f3 + cc[2] * f2 + cc[1] * f1 + cc[0] * f0) - cl1 = 0) ∧
  (((1 - sumf) - 1) * (cols.not_eq_inv * (cl0 - cl1) - 1) = 0)

omit [Fact (2 ^ 17 < p)] in
/-- Distinct field elements have distinct `val`s. -/
private lemma val_ne {x y : ZMod p} (h : x ≠ y) : x.val ≠ y.val := fun hv =>
  h (by rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, hv])

set_option maxHeartbeats 1000000 in
/-- Soundness core: the boolean flags select the most-significant differing limb (all higher limbs
forced equal by the prefix-sum selectors, the selected limb forced distinct by the `not_eq_inv`
witness), so the `U16CompareOperation` on the selected limb pair reproduces the whole-word order.
Phrased on the subcircuit *implication* `hsub` (`Assumptions → Spec`) so it composes directly in the
chip soundness. `at_most_one` reduces to five flag patterns; in each, the selected limb is bounded
(discharging `hsub`) and the limb decomposition of `toNat` lets `omega` decide it dominates. -/
theorem ltUnsigned_core {cols : Extracted.LtOperationUnsigned (ZMod p)}
    (b cc : Word (ZMod p)) (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (hsub : U16CompareOperation.circuit.Assumptions
        ⟨cols.comparison_limbs[0], cols.comparison_limbs[1], cols.u16_compare_operation, 1⟩ →
      U16CompareOperation.circuit.Spec
        ⟨cols.comparison_limbs[0], cols.comparison_limbs[1], cols.u16_compare_operation, 1⟩)
    (h_sel : Selectors b cc cols) :
    cols.u16_compare_operation.bit = if Word.toNat b < Word.toNat cc then 1 else 0 := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hsel3, hsel2, hsel1, hsel0, hcl0, hcl1, hne⟩ := h_sel
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Word.lt_cases_of_isU64 hcc
  rcases at_most_one hf0 hf1 hf2 hf3 hsum with
    ⟨g0, g1, g2, g3⟩ | ⟨g3, g0, g1, g2⟩ | ⟨g2, g0, g1, g3⟩ | ⟨g1, g0, g2, g3⟩ | ⟨g0, g1, g2, g3⟩
  · -- all flags 0: every limb equal, cl0 = cl1 = 0, result 0
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hsel0 hsel1 hsel2 hsel3
    have ecl0 : cols.comparison_limbs[0] = 0 := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = 0 := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have e2 : b[2].val = cc[2].val := congrArg ZMod.val (by linear_combination hsel2)
    have e1 : b[1].val = cc[1].val := congrArg ZMod.val (by linear_combination hsel1)
    have e0 : b[0].val = cc[0].val := congrArg ZMod.val (by linear_combination hsel0)
    have hb0' : cols.comparison_limbs[0].val < 2 ^ 16 := by rw [ecl0, ZMod.val_zero]; norm_num
    have hd0' : cols.comparison_limbs[1].val < 2 ^ 16 := by rw [ecl1, ZMod.val_zero]; norm_num
    have hbit : cols.u16_compare_operation.bit
        = if cols.comparison_limbs[0].val < cols.comparison_limbs[1].val then 1 else 0 :=
      (hsub ⟨fun _ => ⟨hb0', hd0'⟩, Or.inr rfl⟩).2 rfl
    rw [hbit, ecl0, ecl1]
    simp only [Word.toNat_def, ZMod.val_zero]
    split_ifs <;> first | rfl | (exfalso; omega)
  · -- f3 = 1: limb 3 differs and is most significant
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne
    have ecl0 : cols.comparison_limbs[0] = b[3] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[3] := by linear_combination -hcl1
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    have hb0' : cols.comparison_limbs[0].val < 2 ^ 16 := by rw [ecl0]; exact hb3
    have hd0' : cols.comparison_limbs[1].val < 2 ^ 16 := by rw [ecl1]; exact hd3
    have hbit : cols.u16_compare_operation.bit
        = if cols.comparison_limbs[0].val < cols.comparison_limbs[1].val then 1 else 0 :=
      (hsub ⟨fun _ => ⟨hb0', hd0'⟩, Or.inr rfl⟩).2 rfl
    rw [hbit, ecl0, ecl1]
    simp only [Word.toNat_def]
    split_ifs <;> first | rfl | (exfalso; omega)
  · -- f2 = 1: limb 3 equal, limb 2 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne hsel3
    have ecl0 : cols.comparison_limbs[0] = b[2] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[2] := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    have hb0' : cols.comparison_limbs[0].val < 2 ^ 16 := by rw [ecl0]; exact hb2
    have hd0' : cols.comparison_limbs[1].val < 2 ^ 16 := by rw [ecl1]; exact hd2
    have hbit : cols.u16_compare_operation.bit
        = if cols.comparison_limbs[0].val < cols.comparison_limbs[1].val then 1 else 0 :=
      (hsub ⟨fun _ => ⟨hb0', hd0'⟩, Or.inr rfl⟩).2 rfl
    rw [hbit, ecl0, ecl1]
    simp only [Word.toNat_def]
    split_ifs <;> first | rfl | (exfalso; omega)
  · -- f1 = 1: limbs 3,2 equal, limb 1 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne hsel3 hsel2
    have ecl0 : cols.comparison_limbs[0] = b[1] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[1] := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have e2 : b[2].val = cc[2].val := congrArg ZMod.val (by linear_combination hsel2)
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    have hb0' : cols.comparison_limbs[0].val < 2 ^ 16 := by rw [ecl0]; exact hb1
    have hd0' : cols.comparison_limbs[1].val < 2 ^ 16 := by rw [ecl1]; exact hd1
    have hbit : cols.u16_compare_operation.bit
        = if cols.comparison_limbs[0].val < cols.comparison_limbs[1].val then 1 else 0 :=
      (hsub ⟨fun _ => ⟨hb0', hd0'⟩, Or.inr rfl⟩).2 rfl
    rw [hbit, ecl0, ecl1]
    simp only [Word.toNat_def]
    split_ifs <;> first | rfl | (exfalso; omega)
  · -- f0 = 1: limbs 3,2,1 equal, limb 0 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne hsel3 hsel2 hsel1
    have ecl0 : cols.comparison_limbs[0] = b[0] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[0] := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have e2 : b[2].val = cc[2].val := congrArg ZMod.val (by linear_combination hsel2)
    have e1 : b[1].val = cc[1].val := congrArg ZMod.val (by linear_combination hsel1)
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    have hb0' : cols.comparison_limbs[0].val < 2 ^ 16 := by rw [ecl0]; exact hb0
    have hd0' : cols.comparison_limbs[1].val < 2 ^ 16 := by rw [ecl1]; exact hd0
    have hbit : cols.u16_compare_operation.bit
        = if cols.comparison_limbs[0].val < cols.comparison_limbs[1].val then 1 else 0 :=
      (hsub ⟨fun _ => ⟨hb0', hd0'⟩, Or.inr rfl⟩).2 rfl
    rw [hbit, ecl0, ecl1]
    simp only [Word.toNat_def]
    split_ifs <;> first | rfl | (exfalso; omega)

set_option maxHeartbeats 1000000 in
/-- The selected comparison limbs are genuine 16-bit values (each is one operand limb or `0`). Needed
to discharge the composed `U16CompareOperation`'s `Assumptions`. -/
theorem comparison_limbs_lt {cols : Extracted.LtOperationUnsigned (ZMod p)}
    (b cc : Word (ZMod p)) (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (h_sel : Selectors b cc cols) :
    cols.comparison_limbs[0].val < 2 ^ 16 ∧ cols.comparison_limbs[1].val < 2 ^ 16 := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, _, _, _, _, hcl0, hcl1, _⟩ := h_sel
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Word.lt_cases_of_isU64 hcc
  rcases at_most_one hf0 hf1 hf2 hf3 hsum with
    ⟨g0, g1, g2, g3⟩ | ⟨g3, g0, g1, g2⟩ | ⟨g2, g0, g1, g3⟩ | ⟨g1, g0, g2, g3⟩ | ⟨g0, g1, g2, g3⟩ <;>
    simp only [g0, g1, g2, g3] at hcl0 hcl1
  · exact ⟨by rw [show cols.comparison_limbs[0] = 0 by linear_combination -hcl0, ZMod.val_zero]; norm_num,
      by rw [show cols.comparison_limbs[1] = 0 by linear_combination -hcl1, ZMod.val_zero]; norm_num⟩
  · exact ⟨by rw [show cols.comparison_limbs[0] = b[3] by linear_combination -hcl0]; exact hb3,
      by rw [show cols.comparison_limbs[1] = cc[3] by linear_combination -hcl1]; exact hd3⟩
  · exact ⟨by rw [show cols.comparison_limbs[0] = b[2] by linear_combination -hcl0]; exact hb2,
      by rw [show cols.comparison_limbs[1] = cc[2] by linear_combination -hcl1]; exact hd2⟩
  · exact ⟨by rw [show cols.comparison_limbs[0] = b[1] by linear_combination -hcl0]; exact hb1,
      by rw [show cols.comparison_limbs[1] = cc[1] by linear_combination -hcl1]; exact hd1⟩
  · exact ⟨by rw [show cols.comparison_limbs[0] = b[0] by linear_combination -hcl0]; exact hb0,
      by rw [show cols.comparison_limbs[1] = cc[0] by linear_combination -hcl1]; exact hd0⟩

set_option maxHeartbeats 1000000 in
/-- Equality companion to `ltUnsigned_core`: the one-hot flags sum to `0` exactly when the operands are
equal. Same five-case selector split — the all-flags-zero case forces every limb equal; each one-flag
case forces the selected limb distinct (so the words differ) while the flag sum is `1 ≠ 0`. -/
theorem flags_sum_zero_iff_eq {cols : Extracted.LtOperationUnsigned (ZMod p)}
    (b cc : Word (ZMod p)) (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (h_sel : Selectors b cc cols) :
    (cols.u16_flags[0] + cols.u16_flags[1] + cols.u16_flags[2] + cols.u16_flags[3] = 0)
      ↔ Word.toNat b = Word.toNat cc := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hsel3, hsel2, hsel1, hsel0, hcl0, hcl1, hne⟩ := h_sel
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Word.lt_cases_of_isU64 hcc
  have h10 : (1 : ZMod p) ≠ 0 := by
    haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact one_ne_zero
  rcases at_most_one hf0 hf1 hf2 hf3 hsum with
    ⟨g0, g1, g2, g3⟩ | ⟨g3, g0, g1, g2⟩ | ⟨g2, g0, g1, g3⟩ | ⟨g1, g0, g2, g3⟩ | ⟨g0, g1, g2, g3⟩
  · -- all flags 0: sum 0, every limb equal
    simp only [g0, g1, g2, g3] at hsel0 hsel1 hsel2 hsel3
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have e2 : b[2].val = cc[2].val := congrArg ZMod.val (by linear_combination hsel2)
    have e1 : b[1].val = cc[1].val := congrArg ZMod.val (by linear_combination hsel1)
    have e0 : b[0].val = cc[0].val := congrArg ZMod.val (by linear_combination hsel0)
    exact ⟨fun _ => by simp only [Word.toNat_def]; omega, fun _ => by rw [g0, g1, g2, g3]; ring⟩
  · -- f3 = 1: sum 1 ≠ 0, limb 3 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne
    have ecl0 : cols.comparison_limbs[0] = b[3] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[3] := by linear_combination -hcl1
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    refine ⟨fun h => absurd (show (1 : ZMod p) = 0 by rw [g0, g1, g2, g3] at h; linear_combination h)
      h10, fun heq => ?_⟩
    exfalso; simp only [Word.toNat_def] at heq; omega
  · -- f2 = 1: limb 3 equal, limb 2 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne hsel3
    have ecl0 : cols.comparison_limbs[0] = b[2] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[2] := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    refine ⟨fun h => absurd (show (1 : ZMod p) = 0 by rw [g0, g1, g2, g3] at h; linear_combination h)
      h10, fun heq => ?_⟩
    exfalso; simp only [Word.toNat_def] at heq; omega
  · -- f1 = 1: limbs 3,2 equal, limb 1 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne hsel3 hsel2
    have ecl0 : cols.comparison_limbs[0] = b[1] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[1] := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have e2 : b[2].val = cc[2].val := congrArg ZMod.val (by linear_combination hsel2)
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    refine ⟨fun h => absurd (show (1 : ZMod p) = 0 by rw [g0, g1, g2, g3] at h; linear_combination h)
      h10, fun heq => ?_⟩
    exfalso; simp only [Word.toNat_def] at heq; omega
  · -- f0 = 1: limbs 3,2,1 equal, limb 0 differs
    simp only [g0, g1, g2, g3] at hcl0 hcl1 hne hsel3 hsel2 hsel1
    have ecl0 : cols.comparison_limbs[0] = b[0] := by linear_combination -hcl0
    have ecl1 : cols.comparison_limbs[1] = cc[0] := by linear_combination -hcl1
    have e3 : b[3].val = cc[3].val := congrArg ZMod.val (by linear_combination hsel3)
    have e2 : b[2].val = cc[2].val := congrArg ZMod.val (by linear_combination hsel2)
    have e1 : b[1].val = cc[1].val := congrArg ZMod.val (by linear_combination hsel1)
    have hneq : cols.comparison_limbs[0] ≠ cols.comparison_limbs[1] := by
      intro heq; rw [heq] at hne
      exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination hne)
    rw [ecl0, ecl1] at hneq
    have hv := val_ne hneq
    refine ⟨fun h => absurd (show (1 : ZMod p) = 0 by rw [g0, g1, g2, g3] at h; linear_combination h)
      h10, fun heq => ?_⟩
    exfalso; simp only [Word.toNat_def] at heq; omega

/-- Semantic readout from `RawSpec` (used by `LtOperationSigned` and the `Faithful` anchor): the
`U16Compare` `RawSpec` yields the subcircuit implication via `compare_of_raw`, so the compare `bit`
is the unsigned-less-than indicator; the equality conjunct comes from `flags_sum_zero_iff_eq`. -/
theorem ltUnsigned_semantic {cols : Extracted.LtOperationUnsigned (ZMod p)}
    (b cc : Word (ZMod p)) (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (h_raw : RawSpec b cc cols) :
    (cols.u16_compare_operation.bit = if Word.toNat b < Word.toNat cc then 1 else 0) ∧
    ((cols.u16_flags[0] + cols.u16_flags[1] + cols.u16_flags[2] + cols.u16_flags[3] = 0)
      ↔ Word.toNat b = Word.toNat cc) := by
  obtain ⟨hcmp, h_sel⟩ := h_raw
  exact ⟨ltUnsigned_core b cc hb hcc
    (fun hass => ⟨hcmp.1, fun _ => U16CompareOperation.compare_of_raw (hass.1 rfl).1 (hass.1 rfl).2 hcmp⟩) h_sel,
    flags_sum_zero_iff_eq b cc hb hcc h_sel⟩

end SP1Clean.LtOperationUnsigned
