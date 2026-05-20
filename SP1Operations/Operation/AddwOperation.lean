import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Operation.AddwOperation.Operation
import SP1Operations.Operation.AddwOperation.Constraints

namespace AddwOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. The
auto-gen carries match the iff RHS's natural form (Add-style, no sign-flip),
so bare `simp + tauto` closes. -/
lemma allHold_constraints_iff_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : AddwOperation (ZMod p)) :
    SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
      let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      List.Forall SP1Constraint.toProp (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536)) := by
  simp [constraints, U16MSBOperation.constraints,
        sub_eq_zero, SP1Constraint.toProp]
  tauto

/-- Per-limb Nat lift: same as `SubwOperation.limb_lift`. -/
private lemma limb_lift {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (bb vv aa prev cc : ZMod p)
    (hbb : bb.val < 2 ^ 16) (hvv : vv.val < 2 ^ 16) (haa : aa.val < 2 ^ 16)
    (hprev : prev = 0 ∨ prev = 1) (hcc : cc = 0 ∨ cc = 1)
    (h : bb + vv + prev = aa + cc * 65536) :
    bb.val + vv.val + prev.val = aa.val + cc.val * 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  apply_fun ZMod.val at h
  have hprev_lt : prev.val ≤ 1 := by
    rcases hprev with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hcc_lt : cc.val ≤ 1 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hbv : (bb + vv).val = bb.val + vv.val :=
    ZMod.val_add_of_lt (by omega)
  have h1 : (bb + vv + prev).val = bb.val + vv.val + prev.val := by
    rw [ZMod.val_add_of_lt (by rw [hbv]; omega), hbv]
  have h2 : (cc * 65536 : ZMod p).val = cc.val * 65536 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, val_65536_zmod_p, ZMod.val_one]
  have h3 : (aa + cc * 65536 : ZMod p).val = aa.val + cc.val * 65536 := by
    rw [ZMod.val_add_of_lt
      (by rw [h2]; rcases hcc with h | h <;>
            simp [h, ZMod.val_zero, ZMod.val_one] <;> omega), h2]
  rw [h1, h3] at h
  exact h

set_option maxHeartbeats 16000000 in
-- Like `AddOperation.spec_poly` adapted to the 32-bit `HWord` result and
-- the U16MSB cascade. Two carries instead of four; the same
-- linear_combination + limb_lift recipe closes the BitVec goal, and
-- `U16MSBOperation.spec_poly` discharges the MSB clause.
theorem spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : AddwOperation (ZMod p)}
  (h_isU64_a : a.isU64_poly)
  (h_isU64_b : b.isU64_poly) :
  SP1ConstraintList.allHold_poly (constraints a b cols 1) →
    HWord.isU32_poly cols.value ∧
    HWord.toBitVec32_poly cols.value = execute_RTYPEW_pure_32_w_poly a b .ADDW ∧
    cols.msb.msb = if (HWord.toBitVec32_poly cols.value).msb then 1 else 0 := by
  intro cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨hmsb, hc0, hc1, hv0, hv1⟩ := cstrs
  have h_isU32_v : HWord.isU32_poly cols.value :=
    HWord.isU32_of_cases_poly hv0 hv1
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64_poly h_isU64_a
  obtain ⟨hbb0, hbb1, _, _⟩ := Word.lt_cases_of_isU64_poly h_isU64_b
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  refine ⟨h_isU32_v, ?_, ?_⟩
  · -- BitVec equation: cols.value = a.low + b.low
    rw [show execute_RTYPEW_pure_32_w_poly a b .ADDW =
          a.low_poly.toBitVec32_poly + b.low_poly.toBitVec32_poly from rfl,
        ← BitVec.toNat_inj, BitVec.toNat_add,
        HWord.toBitVec32_poly_toNat_poly h_isU32_v,
        HWord.toBitVec32_poly_toNat_poly (Word.isU64_poly_low_poly_isU32_poly h_isU64_b),
        HWord.toBitVec32_poly_toNat_poly (Word.isU64_poly_low_poly_isU32_poly h_isU64_a)]
    simp only [HWord.toNat_poly, Word.low_poly, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    set c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
    set c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
    have e0 : a[0] + b[0] + (0 : ZMod p) = cols.value[0] + c0 * 65536 := by
      rw [hc0_def]; linear_combination -1 * (a[0] + b[0] - cols.value[0]) * h65inv
    have e1 : a[1] + b[1] + c0 = cols.value[1] + c1 * 65536 := by
      rw [hc1_def]; linear_combination -1 * (a[1] + b[1] - cols.value[1] + c0) * h65inv
    have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
    have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0 hc_zero hc0 e0
    have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1 hc0 hc1 e1
    simp only [ZMod.val_zero, add_zero] at n0
    have hc1_lt : c1.val ≤ 1 := by
      rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
    omega
  · -- MSB clause
    apply U16MSBOperation.spec_poly hv1 at hmsb
    rw [hmsb]
    simp only [HWord.toBitVec32_poly, HWord.toNat_poly, BitVec.msb_eq_toNat,
      BitVec.toNat_ofNat]
    have h_sum_lt : cols.value[0].val + cols.value[1].val * 2 ^ 16 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt h_sum_lt]
    split_ifs <;> simp_all <;> omega

end AddwOperation
