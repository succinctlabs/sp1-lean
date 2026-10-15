module

public import SP1Clean.Semantics.Specs.LtUnsigned
public import SP1Clean.Circuits.Gadgets.U16Compare
public import SP1Clean.Model.Channels
public import Clean.Gadgets.Equality
import SP1Clean.Math.Gate
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Tactic.LinearCombination

/-! # Native unsigned word comparison

The bundled assertion checks a semantic limb-selection certificate. Local algebraic evidence
connects that contract to the unchanged AIR; reverse-extraction faithfulness still consumes
the real-row RawSpec until its Rust replacement has equivalent coverage.
-/

@[expose] public section

namespace SP1Clean.LtOperationUnsigned

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Circuits.Types

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- Four boolean flags whose field sum is `0` or `1` have **at most one** set: the assignment is
one of the five all-but-one-zero patterns. The key step lifts the field sum-bound to `ℕ`
(`f0.val + … + f3.val ≤ 1`, no wrap since the sum is `< 2^17 < p`); the sixteen flag assignments
then split into the five satisfiable patterns (closed by an explicit `Or` introduction) and eleven
contradictory ones (closed by `omega` on the lifted bound). -/
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
      | exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
      | (exfalso; simp only [ZMod.val_zero, ZMod.val_one] at hle; omega)

/-- The non-`U16Compare` conjuncts of `RawSpec`: the flag booleans, the sum-bound, the four
prefix-sum selectors, the two limb extractions, and the non-equality witness. `RawSpec` is exactly
`U16CompareOperation.RawSpec … ∧ Selectors b cc cols`. -/
def Selectors (b cc : Word (ZMod p)) (cols : Circuits.Types.LtOperationUnsigned (ZMod p)) : Prop :=
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

/-- Legacy real-row constraint relation, sharing the native selector evidence. -/
def RawSpec (b cc : Word (ZMod p)) (cols : Circuits.Types.LtOperationUnsigned (ZMod p)) : Prop :=
  U16CompareOperation.RawSpec cols.comparison_limbs[0] cols.comparison_limbs[1]
    ⟨cols.u16_compare_operation.bit⟩ ∧ Selectors b cc cols

/-- Soundness core: the boolean flags select the most-significant differing limb (all higher limbs
forced equal by the prefix-sum selectors, the selected limb forced distinct by the `not_eq_inv`
witness), so the `U16CompareOperation` on the selected limb pair reproduces the whole-word order.
Phrased on the subcircuit *implication* `hsub` (`Assumptions → Spec`) so it composes directly in the
chip soundness. `at_most_one` reduces to five flag patterns; in each, the selected limb is bounded
(discharging `hsub`) and the limb decomposition of `toNat` lets `omega` decide it dominates. -/
theorem ltUnsigned_core {cols : Circuits.Types.LtOperationUnsigned (ZMod p)}
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
    rw [hbit, ecl0, ecl1, Word.toNat_def b, Word.toNat_def cc]
    simp only [ZMod.val_zero]
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
    rw [hbit, ecl0, ecl1, Word.toNat_def b, Word.toNat_def cc]
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
    rw [hbit, ecl0, ecl1, Word.toNat_def b, Word.toNat_def cc]
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
    rw [hbit, ecl0, ecl1, Word.toNat_def b, Word.toNat_def cc]
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
    rw [hbit, ecl0, ecl1, Word.toNat_def b, Word.toNat_def cc]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The selected comparison limbs are genuine 16-bit values (each is one operand limb or `0`). Needed
to discharge the composed `U16CompareOperation`'s `Assumptions`. -/
theorem comparison_limbs_lt {cols : Circuits.Types.LtOperationUnsigned (ZMod p)}
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

/-- Equality companion to `ltUnsigned_core`: the one-hot flags sum to `0` exactly when the operands are
equal. Same five-case selector split — the all-flags-zero case forces every limb equal; each one-flag
case forces the selected limb distinct (so the words differ) while the flag sum is `1 ≠ 0`. -/
theorem flags_sum_zero_iff_eq {cols : Circuits.Types.LtOperationUnsigned (ZMod p)}
    (b cc : Word (ZMod p)) (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (h_sel : Selectors b cc cols) :
    (cols.u16_flags[0] + cols.u16_flags[1] + cols.u16_flags[2] + cols.u16_flags[3] = 0)
      ↔ Word.toNat b = Word.toNat cc := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hsel3, hsel2, hsel1, hsel0, hcl0, hcl1, hne⟩ := h_sel
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Word.lt_cases_of_isU64 hcc
  have h10 : (1 : ZMod p) ≠ 0 := by
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
theorem ltUnsigned_semantic {cols : Circuits.Types.LtOperationUnsigned (ZMod p)}
    (b cc : Word (ZMod p)) (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (h_raw : RawSpec b cc cols) :
    (cols.u16_compare_operation.bit = if Word.toNat b < Word.toNat cc then 1 else 0) ∧
    ((cols.u16_flags[0] + cols.u16_flags[1] + cols.u16_flags[2] + cols.u16_flags[3] = 0)
      ↔ Word.toNat b = Word.toNat cc) := by
  obtain ⟨hcmp, h_sel⟩ := h_raw
  exact ⟨ltUnsigned_core b cc hb hcc
    (fun hass => ⟨hcmp.1, fun _ => U16CompareOperation.compare_of_raw (hass.1 rfl).1 (hass.1 rfl).2 hcmp⟩) h_sel,
    flags_sum_zero_iff_eq b cc hb hcc h_sel⟩

/-- Native witness for the `comparison_limbs` column, **field-generic** over `ZMod p`: the
`(bᵢ, ccᵢ)` pair at the most-significant differing limb (all-equal ⇒ `0`). This is SP1's
`LtOperationUnsigned::populate_unsigned` limb-scan ported to Lean. -/
def comparisonLimbsWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 2 :=
  if b[3] ≠ cc[3] then #v[b[3], cc[3]] else if b[2] ≠ cc[2] then #v[b[2], cc[2]]
  else if b[1] ≠ cc[1] then #v[b[1], cc[1]] else if b[0] ≠ cc[0] then #v[b[0], cc[0]]
  else (#v[0, 0] : Vector (ZMod p) 2)

/-- Native witness for the `u16_flags` column: the one-hot flag at the most-significant differing
limb (all-equal ⇒ all zero). -/
def flagsWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 4 :=
  if b[3] ≠ cc[3] then #v[0, 0, 0, 1] else if b[2] ≠ cc[2] then #v[0, 0, 1, 0]
  else if b[1] ≠ cc[1] then #v[0, 1, 0, 0] else if b[0] ≠ cc[0] then #v[1, 0, 0, 0]
  else (#v[0, 0, 0, 0] : Vector (ZMod p) 4)

/-- Native witness for the `not_eq_inv` column: the **field inverse** `(bᵢ - ccᵢ)⁻¹` at the
most-significant differing limb (all-equal ⇒ `0`). This is the column with no ℕ analogue — SP1's
`(b_limb - c_limb).inverse()` — so its conformance can only be checked at SP1's concrete field. -/
def notEqInvWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 1 :=
  if b[3] ≠ cc[3] then #v[(b[3] - cc[3])⁻¹] else if b[2] ≠ cc[2] then #v[(b[2] - cc[2])⁻¹]
  else if b[1] ≠ cc[1] then #v[(b[1] - cc[1])⁻¹] else if b[0] ≠ cc[0] then #v[(b[0] - cc[0])⁻¹]
  else (#v[0] : Vector (ZMod p) 1)

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (`DivRemChip`'s `remainder_lt_operation` when the remainder-check
multiplicity is `0`). `spec_zero` discharges the composed assertion's obligation at
this value. -/
def zeroCols : Circuits.Types.LtOperationUnsigned (ZMod p) :=
  ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩

/-- Fully witnessed `LtOperationUnsigned` column struct (SP1's `populate_unsigned`): one-hot flags,
comparison limbs, non-equality inverse, and the composed `U16CompareOperation` bit. -/
def populate (b cc : Word (ZMod p)) : Circuits.Types.LtOperationUnsigned (ZMod p) :=
  let cl := comparisonLimbsWitness b cc
  let f := flagsWitness b cc
  let ni := notEqInvWitness b cc
  ⟨⟨U16CompareOperation.populate_bit cl[0] cl[1]⟩, f, ni[0], cl⟩

/-! ### Witness IR

The `FExpr` twins of the limb-scan witnesses, over **abstract** limb expressions (the composing
`LtOperationSigned.populateFE` instantiates them at the sign-adjusted limbs; `DivRemChip` will
instantiate them at its remainder/divisor words). Everything here is field-sort — the scans branch
on limb (dis)equality via `=?` (`BExpr.feq`), the inverse leaf is `FExpr.inv`, the compare bit is
`<?` (`BExpr.flt`, exact field-`val` comparison) — so the eval lemmas are pure `if`-congruences
needing no bounds. Deliberately **not** `@[circuit_norm]` (the opacity doctrine). -/

/-- The `FExpr` twin of `comparisonLimbsWitness`: cell `k` scans most-significant-first for the
first differing limb pair (`if a = b then <continue> else <this pair>` — the value scan's `≠` with
the branches swapped). -/
def comparisonLimbsF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) (k : Fin 2) :
    Witgen.FExpr (ZMod p) :=
  .ite (b[3] =? cc[3])
    (.ite (b[2] =? cc[2])
      (.ite (b[1] =? cc[1])
        (.ite (b[0] =? cc[0]) 0 (if k = 0 then b[0] else cc[0]))
        (if k = 0 then b[1] else cc[1]))
      (if k = 0 then b[2] else cc[2]))
    (if k = 0 then b[3] else cc[3])

/-- The `FExpr` twin of `flagsWitness`: the one-hot flag at the most-significant differing limb. -/
def flagsF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) (k : Fin 4) : Witgen.FExpr (ZMod p) :=
  .ite (b[3] =? cc[3])
    (.ite (b[2] =? cc[2])
      (.ite (b[1] =? cc[1])
        (.ite (b[0] =? cc[0]) 0 (if k = 0 then 1 else 0))
        (if k = 1 then 1 else 0))
      (if k = 2 then 1 else 0))
    (if k = 3 then 1 else 0)

/-- The `FExpr` twin of `notEqInvWitness`: the field inverse of the first differing limb pair. -/
def notEqInvF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) : Witgen.FExpr (ZMod p) :=
  .ite (b[3] =? cc[3])
    (.ite (b[2] =? cc[2])
      (.ite (b[1] =? cc[1])
        (.ite (b[0] =? cc[0]) 0 (b[0] - cc[0])⁻¹)
        (b[1] - cc[1])⁻¹)
      (b[2] - cc[2])⁻¹)
    (b[3] - cc[3])⁻¹

/-- The `FExpr` twin of the composed `U16CompareOperation.populate_bit` at the scanned limb pair. -/
def compareBitF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) : Witgen.FExpr (ZMod p) :=
  (comparisonLimbsF b cc 0 <? comparisonLimbsF b cc 1).toField

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the scan twins is exactly the value-level scans on the evaluated limbs (a pure
`if`-congruence — the four conditions match under `heval`, and every leaf is a mirrored field
expression). Stated for all four cell families at once, over abstract limb evaluations. -/
theorem scanF_eval (ctx : Witgen.Ctx (ZMod p)) (b cc : Vector (Witgen.FExpr (ZMod p)) 4)
    (vb vcc : Word (ZMod p))
    (hb : ∀ (i : ℕ) (_ : i < 4), (b[i]).eval ctx = vb[i])
    (hcc : ∀ (i : ℕ) (_ : i < 4), (cc[i]).eval ctx = vcc[i]) :
    (∀ k : Fin 2, (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsWitness vb vcc)[(k : ℕ)]) ∧
    (∀ k : Fin 4, (flagsF b cc k).eval ctx = (flagsWitness vb vcc)[(k : ℕ)]) ∧
    (notEqInvF b cc).eval ctx = (notEqInvWitness vb vcc)[0] ∧
    (compareBitF b cc).eval ctx
      = U16CompareOperation.populate_bit (comparisonLimbsWitness vb vcc)[0]
          (comparisonLimbsWitness vb vcc)[1] := by
  have hb0 := hb 0 (by omega); have hb1 := hb 1 (by omega)
  have hb2 := hb 2 (by omega); have hb3 := hb 3 (by omega)
  have hc0 := hcc 0 (by omega); have hc1 := hcc 1 (by omega)
  have hc2 := hcc 2 (by omega); have hc3 := hcc 3 (by omega)
  have hscan : ∀ k : Fin 2,
      (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsWitness vb vcc)[(k : ℕ)] := by
    intro k
    fin_cases k <;>
    · simp only [comparisonLimbsF, comparisonLimbsWitness, circuit_norm,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      split_ifs <;> simp_all [circuit_norm]
  refine ⟨hscan, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;>
    · simp only [flagsF, flagsWitness, circuit_norm,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      split_ifs <;> simp_all [circuit_norm]
  · simp only [notEqInvF, notEqInvWitness, circuit_norm,
      hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
    split_ifs <;> simp_all [circuit_norm]
  · simp only [compareBitF, U16CompareOperation.populate_bit, circuit_norm,
      hscan 0, hscan 1]

omit [Fact (2 ^ 17 < p)] in
/-- Comparison witnesses depend only on their operand values, including across local IR contexts. -/
theorem scanF_congr (ctx ctx' : Witgen.Ctx (ZMod p)) (b cc : Vector (Witgen.FExpr (ZMod p)) 4)
    {b' cc' : Vector (Witgen.FExpr (ZMod p)) 4}
    (hb : ∀ (i : ℕ) (_ : i < 4), (b[i]).eval ctx = (b'[i]).eval ctx')
    (hcc : ∀ (i : ℕ) (_ : i < 4), (cc[i]).eval ctx = (cc'[i]).eval ctx') :
    (∀ k : Fin 2,
      (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsF b' cc' k).eval ctx') ∧
    (∀ k : Fin 4, (flagsF b cc k).eval ctx = (flagsF b' cc' k).eval ctx') ∧
    (notEqInvF b cc).eval ctx = (notEqInvF b' cc').eval ctx' ∧
    (compareBitF b cc).eval ctx = (compareBitF b' cc').eval ctx' := by
  have hb0 := hb 0 (by omega); have hb1 := hb 1 (by omega)
  have hb2 := hb 2 (by omega); have hb3 := hb 3 (by omega)
  have hc0 := hcc 0 (by omega); have hc1 := hcc 1 (by omega)
  have hc2 := hcc 2 (by omega); have hc3 := hcc 3 (by omega)
  have hscan : ∀ k : Fin 2,
      (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsF b' cc' k).eval ctx' := by
    intro k
    fin_cases k <;>
    · simp only [comparisonLimbsF, circuit_norm, -Witgen.u64Wrap,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      all_goals split_ifs <;> simp_all [circuit_norm, -Witgen.u64Wrap]
  refine ⟨hscan, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;>
    · simp only [flagsF, circuit_norm, -Witgen.u64Wrap,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      all_goals split_ifs <;> simp_all [circuit_norm, -Witgen.u64Wrap]
  · simp only [notEqInvF, circuit_norm, -Witgen.u64Wrap,
      hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
  · simp only [compareBitF, circuit_norm, -Witgen.u64Wrap, hscan 0, hscan 1]

/-- Check the supplied comparison certificate through the bundled 16-bit comparator. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let cc := input.cc
  let cols := input.cols
  let is_real := input.is_real
  let E0 := is_real - 1
  let E1 := is_real * E0
  let E2 := cols.u16_flags[0] + cols.u16_flags[1]
  let E3 := E2 + cols.u16_flags[2]
  let E4 := E3 + cols.u16_flags[3]
  let E5 := cols.u16_flags[0] - 1
  let E6 := cols.u16_flags[0] * E5
  let E7 := cols.u16_flags[1] - 1
  let E8 := cols.u16_flags[1] * E7
  let E9 := cols.u16_flags[2] - 1
  let E10 := cols.u16_flags[2] * E9
  let E11 := cols.u16_flags[3] - 1
  let E12 := cols.u16_flags[3] * E11
  let E13 := E4 - 1
  let E14 := E4 * E13
  let E15 := 1 - E4
  let E16 := (0 : Expression (ZMod p)) + cols.u16_flags[3]
  let E17 := is_real - E16
  let E18 := b[3] - cc[3]
  let E19 := E17 * E18
  let E20 := b[3] * cols.u16_flags[3]
  let E21 := (0 : Expression (ZMod p)) + E20
  let E22 := cc[3] * cols.u16_flags[3]
  let E23 := (0 : Expression (ZMod p)) + E22
  let E24 := E16 + cols.u16_flags[2]
  let E25 := is_real - E24
  let E26 := b[2] - cc[2]
  let E27 := E25 * E26
  let E28 := b[2] * cols.u16_flags[2]
  let E29 := E21 + E28
  let E30 := cc[2] * cols.u16_flags[2]
  let E31 := E23 + E30
  let E32 := E24 + cols.u16_flags[1]
  let E33 := is_real - E32
  let E34 := b[1] - cc[1]
  let E35 := E33 * E34
  let E36 := b[1] * cols.u16_flags[1]
  let E37 := E29 + E36
  let E38 := cc[1] * cols.u16_flags[1]
  let E39 := E31 + E38
  let E40 := E32 + cols.u16_flags[0]
  let E41 := is_real - E40
  let E42 := b[0] - cc[0]
  let E43 := E41 * E42
  let E44 := b[0] * cols.u16_flags[0]
  let E45 := E37 + E44
  let E46 := cc[0] * cols.u16_flags[0]
  let E47 := E39 + E46
  let E48 := E45 - cols.comparison_limbs[0]
  let E49 := E47 - cols.comparison_limbs[1]
  let E50 := E15 - 1
  let E51 := cols.comparison_limbs[0] - cols.comparison_limbs[1]
  let E52 := cols.not_eq_inv * E51
  let E53 := E52 - is_real
  let E54 := E50 * E53
  assertion U16CompareOperation.circuit ⟨cols.comparison_limbs[0], cols.comparison_limbs[1], { bit := cols.u16_compare_operation.bit }, is_real⟩
  E1 === 0
  E6 === 0
  E8 === 0
  E10 === 0
  E12 === 0
  E14 === 0
  E19 === 0
  E27 === 0
  E35 === 0
  E43 === 0
  E48 === 0
  E49 === 0
  E54 === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- Local algebraic evidence connecting the semantic certificate to the AIR. This relation
is private; callers use the limb-selection and whole-word contract. -/
private def ConstraintEvidence (input : Inputs (ZMod p)) : Prop :=
  let cols := input.cols
  let f0 := cols.u16_flags[0]; let f1 := cols.u16_flags[1]
  let f2 := cols.u16_flags[2]; let f3 := cols.u16_flags[3]
  let cl0 := cols.comparison_limbs[0]; let cl1 := cols.comparison_limbs[1]
  let sumf := f0 + f1 + f2 + f3
  let ir := input.is_real
  (f0 = 0 ∨ f0 = 1) ∧ (f1 = 0 ∨ f1 = 1) ∧ (f2 = 0 ∨ f2 = 1) ∧ (f3 = 0 ∨ f3 = 1) ∧
  (sumf = 0 ∨ sumf = 1) ∧
  ((ir - f3) * (input.b[3] - input.cc[3]) = 0) ∧
  ((ir - (f3 + f2)) * (input.b[2] - input.cc[2]) = 0) ∧
  ((ir - (f3 + f2 + f1)) * (input.b[1] - input.cc[1]) = 0) ∧
  ((ir - (f3 + f2 + f1 + f0)) * (input.b[0] - input.cc[0]) = 0) ∧
  ((input.b[3] * f3 + input.b[2] * f2 + input.b[1] * f1 + input.b[0] * f0) - cl0 = 0) ∧
  ((input.cc[3] * f3 + input.cc[2] * f2 + input.cc[1] * f1 + input.cc[0] * f0) - cl1 = 0) ∧
  ((-sumf) * (cols.not_eq_inv * (cl0 - cl1) - ir) = 0) ∧
  (cols.u16_compare_operation.bit = 0 ∨ cols.u16_compare_operation.bit = 1) ∧
  (ir = 1 → cols.u16_compare_operation.bit = if cl0.val < cl1.val then 1 else 0)

omit [Fact (2 ^ 17 < p)] in
/-- On a real row (`is_real = 1`), the structural `ConstraintEvidence` collapses to the `is_real = 1`-form
`Selectors` the soundness cores consume. -/
private theorem selectors_of_evidence_real {input : Inputs (ZMod p)} (hs : ConstraintEvidence input)
    (hir : input.is_real = 1) : Selectors input.b input.cc input.cols := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0, hcl1, hinv, _, _⟩ := hs
  rw [hir] at hs3 hs2 hs1 hs0 hinv
  exact ⟨hf0, hf1, hf2, hf3, hsum, by linear_combination hs3, by linear_combination hs2,
    by linear_combination hs1, by linear_combination hs0, hcl0, hcl1, by linear_combination hinv⟩

/-- Whole-word interpretation of the local algebraic evidence. -/
private theorem result_of_evidence {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc) (hir : input.is_real = 1)
    (hs : ConstraintEvidence input) :
    (input.cols.u16_compare_operation.bit
        = if Word.toNat input.b < Word.toNat input.cc then 1 else 0) ∧
    ((input.cols.u16_flags[0] + input.cols.u16_flags[1] + input.cols.u16_flags[2]
        + input.cols.u16_flags[3] = 0) ↔ Word.toNat input.b = Word.toNat input.cc) := by
  have h_sel := selectors_of_evidence_real hs hir
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbitbool, hbitord⟩ := hs
  exact ⟨ltUnsigned_core input.b input.cc hb hcc
      (fun _ => ⟨hbitbool, fun _ => hbitord hir⟩) h_sel,
    flags_sum_zero_iff_eq input.b input.cc hb hcc h_sel⟩

private theorem selection_of_evidence {input : Inputs (ZMod p)}
    (hs : ConstraintEvidence input) : Selection input := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0, hcl1, hinv, _, _⟩ := hs
  have pivot (i : Fin 4)
      (hf : input.cols.u16_flags = Vector.ofFn (fun j => if j = i then 1 else 0)) :
      Pivot input i := by
    have hcl : input.cols.comparison_limbs = #v[input.b[i], input.cc[i]] := by
      apply Vector.ext
      intro j hj
      fin_cases i <;> interval_cases j <;>
        simp [hf] at hcl0 hcl1 ⊢ <;>
        first | linear_combination -hcl0 | linear_combination -hcl1
    refine ⟨hf, hcl, ?_, ?_⟩
    · intro hr
      have hi : input.cols.not_eq_inv * (input.b[i] - input.cc[i]) = 1 := by
        fin_cases i <;> simp [hf, hcl, hr] at hinv ⊢ <;> linear_combination -hinv
      refine ⟨?_, ?_, eq_inv_of_mul_eq_one_left hi⟩
      · intro j hij
        fin_cases i <;> fin_cases j <;> simp at hij <;>
          simp [hf, hr, sub_eq_zero] at hs3 hs2 hs1 hs0 ⊢ <;> assumption
      · intro heq
        simp [heq] at hi
    · intro hr j hij
      fin_cases i <;> fin_cases j <;> simp at hij <;>
        simp [hf, hr, sub_eq_zero] at hs3 hs2 hs1 hs0 ⊢ <;> symm <;> assumption
  rcases at_most_one hf0 hf1 hf2 hf3 hsum with
    ⟨g0, g1, g2, g3⟩ | ⟨g3, g0, g1, g2⟩ | ⟨g2, g0, g1, g3⟩ |
    ⟨g1, g0, g2, g3⟩ | ⟨g0, g1, g2, g3⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · apply Vector.ext; intro i hi; interval_cases i <;> simp [g0, g1, g2, g3]
    · apply Vector.ext; intro i hi; interval_cases i <;> simp [g0, g1, g2, g3] at hcl0 hcl1 ⊢ <;> assumption
    · intro hr
      rw [hr] at hs3 hs2 hs1 hs0
      apply Vector.ext
      intro i hi
      interval_cases i <;>
        simp [g0, g1, g2, g3, sub_eq_zero] at hs3 hs2 hs1 hs0 hcl0 hcl1 ⊢ <;> assumption
  · exact Or.inr ⟨3, pivot 3 (by
      apply Vector.ext; intro i hi; interval_cases i <;> simp [g0, g1, g2, g3])⟩
  · exact Or.inr ⟨2, pivot 2 (by
      apply Vector.ext; intro i hi; interval_cases i <;> simp [g0, g1, g2, g3])⟩
  · exact Or.inr ⟨1, pivot 1 (by
      apply Vector.ext; intro i hi; interval_cases i <;> simp [g0, g1, g2, g3])⟩
  · exact Or.inr ⟨0, pivot 0 (by
      apply Vector.ext; intro i hi; interval_cases i <;> simp [g0, g1, g2, g3])⟩

omit [Fact (2 ^ 17 < p)] in
private theorem evidence_of_selection {input : Inputs (ZMod p)}
    (hr : input.is_real = 0 ∨ input.is_real = 1)
    (hs : Selection input)
    (hbit : input.cols.u16_compare_operation.bit = 0 ∨ input.cols.u16_compare_operation.bit = 1)
    (hord : input.is_real = 1 → input.cols.u16_compare_operation.bit =
      if input.cols.comparison_limbs[0].val < input.cols.comparison_limbs[1].val then 1 else 0) :
    ConstraintEvidence input := by
  rcases hs with ⟨hf, hcl, heq⟩ | ⟨i, hf, hcl, hreal, hpad⟩
  · rcases hr with hr | hr
    · simp [ConstraintEvidence, hf, hcl, hr, hbit]
    · have heq := heq hr
      simp [ConstraintEvidence, hf, hcl, hr, heq, hord]
  · rcases hr with hr | hr
    · have heq := hpad hr
      simp only [Fin.forall_fin_succ] at heq
      simp only [ConstraintEvidence, hf, hcl]
      fin_cases i <;> simp_all
    · obtain ⟨heq, hne, hinv⟩ := hreal hr
      have hcancel := inv_mul_cancel₀ (sub_ne_zero.mpr hne)
      simp only [Fin.forall_fin_succ] at heq
      simp only [ConstraintEvidence, hf, hcl]
      fin_cases i <;> simp_all <;> rfl

private theorem spec_iff_evidence {input : Inputs (ZMod p)} (ha : Assumptions input) :
    Spec input ↔ ConstraintEvidence input := by
  constructor
  · rintro ⟨hbit, hsel, hresult⟩
    apply evidence_of_selection ha.2 hsel hbit
    intro hr
    let bit : ZMod p :=
      if input.cols.comparison_limbs[0].val < input.cols.comparison_limbs[1].val then 1 else 0
    let selected : Inputs (ZMod p) :=
      { input with cols := { input.cols with u16_compare_operation := ⟨bit⟩ } }
    have hsel' : Selection selected := hsel
    have he : ConstraintEvidence selected := evidence_of_selection ha.2 hsel'
      (by dsimp [selected, bit]; split <;> simp) (fun _ => rfl)
    have horder := (result_of_evidence (input := selected) (ha.1 hr).1 (ha.1 hr).2 hr he).1
    exact (hresult hr).1.trans horder.symm
  · intro he
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbit, _⟩ := he
    exact ⟨hbit, selection_of_evidence he,
      fun hr => result_of_evidence (ha.1 hr).1 (ha.1 hr).2 hr he⟩

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- The witnessed columns `populate b cc` satisfy the `is_real = 1`-form `Selectors`: the one-hot flag
at the most-significant differing limb makes every prefix selector vanish, the comparison limbs are the
selected pair, and the non-equality inverse closes the gate. (SP1's `populate_unsigned` correctness.)

Each differing-limb branch binds the inverse cancellation once as `k`; leading the ladder with the
*failing* `ring1` stops both `linear_combination`s being tried on the eleven goals that do not need
them. **`ring1`, not `ring`** — `ring`'s `ring_nf` fallback never fails, so a leading `ring` swallows
the non-equality goal and blocks the alternatives behind it. -/
theorem sel_populate {b cc : Word (ZMod p)} :
    Selectors b cc (populate b cc) := by
  simp only [Selectors, populate, comparisonLimbsWitness, flagsWitness, notEqInvWitness]
  by_cases h3 : b[3] = cc[3]
  · by_cases h2 : b[2] = cc[2]
    · by_cases h1 : b[1] = cc[1]
      · by_cases h0 : b[0] = cc[0]
        · -- all limbs equal
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [ne_eq, h3, h2, h1, h0, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
              true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
              List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
              zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero]
        · -- limb 0 differs
          have k := inv_mul_cancel₀ (sub_ne_zero.mpr h0)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [ne_eq, h3, h2, h1, h0, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
              true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
              List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
              zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
            first | ring1 | linear_combination k | linear_combination -k
      · -- limb 1 differs
        have k := inv_mul_cancel₀ (sub_ne_zero.mpr h1)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, h3, h2, h1, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
            true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
            List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
            zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
          first | ring1 | linear_combination k | linear_combination -k
    · -- limb 2 differs
      have k := inv_mul_cancel₀ (sub_ne_zero.mpr h2)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [ne_eq, h3, h2, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
          true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
          zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
        first | ring1 | linear_combination k | linear_combination -k
  · -- limb 3 differs (most significant)
    have k := inv_mul_cancel₀ (sub_ne_zero.mpr h3)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ne_eq, h3, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
        true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
        zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
      first | ring1 | linear_combination k | linear_combination -k

omit [Fact (2 ^ 17 < p)] in
/-- The limb-scan generator supplies the private algebraic certificate. -/
private theorem evidence_populate {b cc : Word (ZMod p)} :
    ConstraintEvidence (⟨b, cc, populate b cc, 1⟩ : Inputs (ZMod p)) := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0, hcl1, hinv⟩ :=
    (sel_populate : Selectors b cc (populate b cc))
  have hbit : (populate b cc).u16_compare_operation.bit
      = if (populate b cc).comparison_limbs[0].val < (populate b cc).comparison_limbs[1].val
        then 1 else 0 := rfl
  refine ⟨hf0, hf1, hf2, hf3, hsum, by linear_combination hs3, by linear_combination hs2,
    by linear_combination hs1, by linear_combination hs0, hcl0, hcl1, by linear_combination hinv,
    U16CompareOperation.populate_bit_bool _ _, fun _ => hbit⟩

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbcc_imp, hbin⟩ := h_assumptions
  let row : Inputs (ZMod p) :=
    ⟨input_b, input_cc, ⟨⟨input_cols_u16_compare_operation_bit⟩, input_cols_u16_flags,
      input_cols_not_eq_inv, input_cols_comparison_limbs⟩, input_is_real⟩
  obtain ⟨hib, hicc, hicols, hir⟩ := h_input
  obtain ⟨_hibit, hiflags, _hineinv, hicl⟩ := hicols
  have eb : ∀ i (hi : i < 4), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_u16_flags[i] = input_cols_u16_flags[i] := by
    intro i hi; rw [← hiflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2),
      Expression.eval env input_var_cols_comparison_limbs[i] = input_cols_comparison_limbs[i] := by
    intro i hi; rw [← hicl]; simp only [Vector.getElem_map]
  simp only [eb, ec, ef, ecl] at h_holds ⊢
  obtain ⟨h_cmp, hE1, hE6, hE8, hE10, hE12, hE14, hE19, hE27, hE35, hE43, hE48, hE49, hE54⟩ := h_holds
  -- the composed `U16Compare` assertion's `Assumptions` (cl ranges on a real row, via the cores).
  have hCmpAs : U16CompareOperation.circuit.Assumptions
      ⟨input_cols_comparison_limbs[0], input_cols_comparison_limbs[1],
        ⟨input_cols_u16_compare_operation_bit⟩, input_is_real⟩ := by
    refine ⟨fun hir1 => ?_, hbin⟩
    have hr1 : input_is_real = 1 := hir1
    obtain ⟨hb, hcc⟩ := hbcc_imp hr1
    have h_sel : Selectors input_b input_cc
        ⟨⟨input_cols_u16_compare_operation_bit⟩, input_cols_u16_flags, input_cols_not_eq_inv,
          input_cols_comparison_limbs⟩ := by
      simp only [Selectors]
      exact ⟨bool_of_mul_pred hE6, bool_of_mul_pred hE8, bool_of_mul_pred hE10,
        bool_of_mul_pred hE12, bool_of_mul_pred hE14,
        by linear_combination hE19 - (input_b[3] - input_cc[3]) * hr1,
        by linear_combination hE27 - (input_b[2] - input_cc[2]) * hr1,
        by linear_combination hE35 - (input_b[1] - input_cc[1]) * hr1,
        by linear_combination hE43 - (input_b[0] - input_cc[0]) * hr1,
        by linear_combination hE48, by linear_combination hE49,
        by linear_combination hE54 + (1 - (input_cols_u16_flags[0] + input_cols_u16_flags[1]
          + input_cols_u16_flags[2] + input_cols_u16_flags[3]) - 1) * hr1⟩
    exact comparison_limbs_lt input_b input_cc hb hcc h_sel
  obtain ⟨hbitbool, hbitord⟩ := h_cmp hCmpAs
  exact ⟨(spec_iff_evidence (input := row) ⟨hbcc_imp, hbin⟩).mpr
    ⟨bool_of_mul_pred hE6, bool_of_mul_pred hE8, bool_of_mul_pred hE10, bool_of_mul_pred hE12,
      bool_of_mul_pred hE14, by linear_combination hE19, by linear_combination hE27,
      by linear_combination hE35, by linear_combination hE43, by linear_combination hE48,
      by linear_combination hE49, by linear_combination hE54, hbitbool, hbitord⟩, Or.inr hCmpAs⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbcc_imp, hbin⟩ := h_assumptions
  let row : Inputs (ZMod p) :=
    ⟨input_b, input_cc, ⟨⟨input_cols_u16_compare_operation_bit⟩, input_cols_u16_flags,
      input_cols_not_eq_inv, input_cols_comparison_limbs⟩, input_is_real⟩
  obtain ⟨hib, hicc, hicols, hir⟩ := h_input
  obtain ⟨_hibit, hiflags, _hineinv, hicl⟩ := hicols
  have eb : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_cols_u16_flags[i] = input_cols_u16_flags[i] := by
    intro i hi; rw [← hiflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2),
      Expression.eval env.toEnvironment input_var_cols_comparison_limbs[i]
        = input_cols_comparison_limbs[i] := by
    intro i hi; rw [← hicl]; simp only [Vector.getElem_map]
  have h_evidence : ConstraintEvidence row :=
    (spec_iff_evidence ⟨hbcc_imp, hbin⟩).mp h_spec
  dsimp only [row] at h_evidence
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0eq, hcl1eq, hinv, hbitbool, hbitord⟩ := h_evidence
  -- the composed `U16Compare` assertion's `Assumptions` ∧ `Spec` (cl ranges via the cores on a real row).
  have h_sel_real : input_is_real = 1 → Selectors input_b input_cc
      ⟨⟨input_cols_u16_compare_operation_bit⟩, input_cols_u16_flags, input_cols_not_eq_inv,
        input_cols_comparison_limbs⟩ := by
    intro hir1
    rw [hir1] at hs3 hs2 hs1 hs0 hinv
    simp only [Selectors]
    exact ⟨hf0, hf1, hf2, hf3, hsum, by linear_combination hs3, by linear_combination hs2,
      by linear_combination hs1, by linear_combination hs0, hcl0eq, hcl1eq, by linear_combination hinv⟩
  have hCmpAs : U16CompareOperation.circuit.Assumptions
      ⟨input_cols_comparison_limbs[0], input_cols_comparison_limbs[1],
        ⟨input_cols_u16_compare_operation_bit⟩, input_is_real⟩ :=
    ⟨fun hir1 => comparison_limbs_lt input_b input_cc (hbcc_imp hir1).1 (hbcc_imp hir1).2
      (h_sel_real hir1), hbin⟩
  have hCmpSpec : U16CompareOperation.circuit.Spec
      ⟨input_cols_comparison_limbs[0], input_cols_comparison_limbs[1],
        ⟨input_cols_u16_compare_operation_bit⟩, input_is_real⟩ := ⟨hbitbool, hbitord⟩
  simp only [eb, ec, ef, ecl]
  refine ⟨⟨hCmpAs, hCmpSpec⟩, ?_, ?_, ?_, ?_, ?_, ?_, by linear_combination hs3,
    by linear_combination hs2, by linear_combination hs1, by linear_combination hs0,
    by linear_combination hcl0eq, by linear_combination hcl1eq, by linear_combination hinv⟩
  · rcases hbin with h | h <;> rw [h] <;> ring
  · rcases hf0 with h | h <;> rw [h] <;> ring
  · rcases hf1 with h | h <;> rw [h] <;> ring
  · rcases hf2 with h | h <;> rw [h] <;> ring
  · rcases hf3 with h | h <;> rw [h] <;> ring
  · rcases hsum with h | h <;> rw [h] <;> ring

/-- The limb-scan witness satisfies the semantic comparison contract for bounded words. -/
theorem spec_populate {b cc : Word (ZMod p)} (hb : Word.isU64 b) (hcc : Word.isU64 cc) :
    Spec (⟨b, cc, populate b cc, 1⟩ : Inputs (ZMod p)) :=
  (spec_iff_evidence ⟨fun _ => ⟨hb, hcc⟩, Or.inr rfl⟩).mpr evidence_populate

omit [Fact (2 ^ 17 < p)] in
/-- All-zero inactive columns are valid for arbitrary operands. -/
theorem spec_zero (b cc : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨b, cc, zeroCols, is_real⟩ : Inputs (ZMod p)) := by
  subst hr
  refine ⟨Or.inl rfl, Or.inl ⟨rfl, rfl, ?_⟩, ?_⟩ <;> simp

/-- The native unsigned comparison assertion, with a semantic certificate contract. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [] }

@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [] := rfl

@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.LtOperationUnsigned
