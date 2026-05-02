import SP1Foundations
import SP1Operations.Operation.SubwOperation.Operation
import SP1Operations.Operation.SubwOperation.Constraints

namespace SubwOperation

lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : SubwOperation (Fin KB)) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin KB := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
      let carry1 : Fin KB := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
      List.Forall SP1Constraint.toProp (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0] < 65536) ∧
      (cols.value[1] < 65536)) := by
  simp [constraints, ← inv_65536BB_eq', sub_eq_zero]
  omega

/-- Disjunction-shift helper for the Subw carry-bridging proof; mirrors
the Sub-side `carry_swap_iff_poly` (Sub-phase B.10). -/
private lemma carry_swap_iff_poly {p : ℕ} [Fact (Nat.Prime p)]
    (x y : ZMod p) (hxy : x = 1 - y) :
    (x = 0 ∨ x = 1) ↔ (y = 0 ∨ y = 1) := by
  rw [hxy, sub_eq_zero, sub_eq_self]
  constructor
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm

set_option maxHeartbeats 4000000 in
-- Carry-bridging proof needs the elevated heartbeat limit (mirrors Sub).
/-- Polymorphic companion of `allHold_constraints_iff` over `ZMod p`. Same
borrow-form ↔ natural-form bridging recipe as Sub: pose carries `c_i`
(natural) and `d_i` (borrow), prove `d_i = 1 - c_i` via
`linear_combination`, close the borrow-form iff via bare simp, then
bridge each carry-binary clause via `carry_swap_iff_poly`. -/
lemma allHold_constraints_iff_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : SubwOperation (ZMod p)) :
    SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
      let carry0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
      let carry1 : ZMod p := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
      List.Forall SP1Constraint.toProp_poly (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
      ((carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536)) := by
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  set c0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹ with hc0_def
  set c1 : ZMod p := (b[1] + cols.value[1] - a[1] + c0) * 65536⁻¹ with hc1_def
  set d0 : ZMod p := (a[0] + 65536 - 1 - b[0] - cols.value[0] + 1) * 65536⁻¹ with hd0_def
  set d1 : ZMod p := (a[1] + 65536 - 1 - b[1] - cols.value[1] + d0) * 65536⁻¹ with hd1_def
  have hd0_swap : d0 = 1 - c0 := by
    rw [hd0_def, hc0_def]; linear_combination (1 : ZMod p) * hbridge
  have hd1_swap : d1 = 1 - c1 := by
    rw [hd1_def, hd0_swap, hc1_def, hc0_def]
    linear_combination (1 : ZMod p) * hbridge
  have h_borrow :
      SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
        List.Forall SP1Constraint.toProp_poly (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
        (d0 = 0 ∨ d0 = 1) ∧ (d1 = 0 ∨ d1 = 1) ∧
        cols.value[0].val < 65536 ∧ cols.value[1].val < 65536 := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly,
          hd0_def, hd1_def]
  rw [h_borrow,
      carry_swap_iff_poly d0 c0 hd0_swap,
      carry_swap_iff_poly d1 c1 hd1_swap]

theorem spec
  {a b : Word (Fin KB)}
  {cols : SubwOperation (Fin KB)}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    HWord.isU32 (cols.value) ∧
    HWord.toBitVec32 (cols.value) = execute_RTYPEW_pure_32_w a b .SUBW ∧
    cols.msb.msb = if (HWord.toBitVec32 cols.value).msb then 1 else 0
  := by
    intro cstrs
    simp [allHold_constraints_iff] at cstrs
    obtain ⟨hmsb, h0, h1, hbds⟩ := cstrs
    apply Word.lt_cases_of_isU64 at h_isU64_a
    apply Word.lt_cases_of_isU64 at h_isU64_b
    split_ands
    · clear *- hbds; aesop
    · simp [BitVec.eq_sub_iff_add_eq]
      simp [HWord.toBitVec32, Word.low, HWord.toNat]
      rw [← BitVec.toNat_inj, BitVec.toNat_add]
      aesop (add safe (by omega))
    · simp [Fin.lt_def] at hbds
      apply U16MSBOperation.spec (by omega) at hmsb
      simp [HWord.toBitVec32, HWord.toNat, BitVec.msb_eq_toNat]
      simp at hmsb; split_ifs at * <;> omega

/-- Per-limb Nat lift: same as `SubOperation.limb_lift`. -/
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
-- Mirror of `SubOperation.spec_poly` adapted to the 32-bit `HWord` result
-- and the U16MSB cascade. Two carries instead of four; otherwise the same
-- linear_combination + limb_lift recipe closes the BitVec goal, and
-- `U16MSBOperation.spec_poly` discharges the MSB clause.
/-- Polymorphic companion of `spec`. -/
theorem spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : SubwOperation (ZMod p)}
  (h_isU64_a : a.isU64_poly)
  (h_isU64_b : b.isU64_poly) :
  SP1ConstraintList.allHold_poly (constraints a b cols 1) →
    HWord.isU32_poly cols.value ∧
    HWord.toBitVec32_poly cols.value = execute_RTYPEW_pure_32_w_poly a b .SUBW ∧
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
  · -- BitVec equation: cols.value = a.low - b.low
    rw [show execute_RTYPEW_pure_32_w_poly a b .SUBW =
          a.low_poly.toBitVec32_poly - b.low_poly.toBitVec32_poly from rfl,
        BitVec.eq_sub_iff_add_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
        HWord.toBitVec32_poly_toNat_poly h_isU32_v,
        HWord.toBitVec32_poly_toNat_poly (Word.isU64_poly_low_poly_isU32_poly h_isU64_b),
        HWord.toBitVec32_poly_toNat_poly (Word.isU64_poly_low_poly_isU32_poly h_isU64_a)]
    simp only [HWord.toNat_poly, Word.low_poly, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    set c0 : ZMod p := (b[0] + cols.value[0] - a[0]) * (65536 : ZMod p)⁻¹ with hc0_def
    set c1 : ZMod p := (b[1] + cols.value[1] - a[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
    have e0 : b[0] + cols.value[0] + (0 : ZMod p) = a[0] + c0 * 65536 := by
      rw [hc0_def]; linear_combination -1 * (b[0] + cols.value[0] - a[0]) * h65inv
    have e1 : b[1] + cols.value[1] + c0 = a[1] + c1 * 65536 := by
      rw [hc1_def]; linear_combination -1 * (b[1] + cols.value[1] - a[1] + c0) * h65inv
    have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
    have n0 := limb_lift _ _ _ _ _ hbb0 hv0 ha0 hc_zero hc0 e0
    have n1 := limb_lift _ _ _ _ _ hbb1 hv1 ha1 hc0 hc1 e1
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

end SubwOperation
