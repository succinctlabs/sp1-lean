import SP1Foundations
import SP1Operations.Operation.SubwOperation.Operation
import SP1Operations.Operation.SubwOperation.Constraints

namespace SubwOperation

set_option linter.style.setOption false
set_option linter.style.longLine false

/-- Disjunction-shift helper for the Subw carry-bridging proof; mirrors
the Sub-side `carry_swap_iff`. -/
private lemma carry_swap_iff {p : ℕ} [Fact (Nat.Prime p)]
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
-- Carry-bridging proof needs the elevated heartbeat limit.
/-- Borrow-form ↔ natural-form bridging recipe (mirrors Sub): pose
carries `c_i` (natural) and `d_i` (borrow), prove `d_i = 1 - c_i` via
`linear_combination`, close the borrow-form iff via bare simp, then
bridge each carry-binary clause via `carry_swap_iff`. -/
lemma allHold_constraints_iff
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : SubwOperation (ZMod p)) :
    SP1ConstraintList.allHold (constraints a b cols 1) ↔
      let carry0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
      let carry1 : ZMod p := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
      List.Forall SP1Constraint.toProp (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
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
      SP1ConstraintList.allHold (constraints a b cols 1) ↔
        List.Forall SP1Constraint.toProp (U16MSBOperation.constraints cols.value[1] cols.msb 1) ∧
        (d0 = 0 ∨ d0 = 1) ∧ (d1 = 0 ∨ d1 = 1) ∧
        cols.value[0].val < 65536 ∧ cols.value[1].val < 65536 := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp,
          hd0_def, hd1_def]
  rw [h_borrow,
      carry_swap_iff d0 c0 hd0_swap,
      carry_swap_iff d1 c1 hd1_swap]

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
-- Like `SubOperation.spec` adapted to the 32-bit `HWord` result and
-- the U16MSB cascade. Two carries instead of four; the same
-- linear_combination + limb_lift recipe closes the BitVec goal, and
-- `U16MSBOperation.spec` discharges the MSB clause.
theorem spec
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : SubwOperation (ZMod p)}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  SP1ConstraintList.allHold (constraints a b cols 1) →
    HWord.isU32 cols.value ∧
    HWord.toBitVec32 cols.value = execute_RTYPEW_pure_32_w a b .SUBW ∧
    cols.msb.msb = if (HWord.toBitVec32 cols.value).msb then 1 else 0 := by
  intro cstrs
  rw [allHold_constraints_iff] at cstrs
  obtain ⟨hmsb, hc0, hc1, hv0, hv1⟩ := cstrs
  have h_isU32_v : HWord.isU32 cols.value :=
    HWord.isU32_of_cases hv0 hv1
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 h_isU64_a
  obtain ⟨hbb0, hbb1, _, _⟩ := Word.lt_cases_of_isU64 h_isU64_b
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  refine ⟨h_isU32_v, ?_, ?_⟩
  · -- BitVec equation: cols.value = a.low - b.low
    rw [show execute_RTYPEW_pure_32_w a b .SUBW =
          a.low.toBitVec32 - b.low.toBitVec32 from rfl,
        BitVec.eq_sub_iff_add_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
        HWord.toBitVec32_toNat h_isU32_v,
        HWord.toBitVec32_toNat (Word.isU64_low_isU32 h_isU64_b),
        HWord.toBitVec32_toNat (Word.isU64_low_isU32 h_isU64_a)]
    simp only [HWord.toNat, Word.low, Vector.getElem_mk,
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
    apply U16MSBOperation.spec hv1 at hmsb
    rw [hmsb]
    simp only [HWord.toBitVec32, HWord.toNat, BitVec.msb_eq_toNat,
      BitVec.toNat_ofNat]
    have h_sum_lt : cols.value[0].val + cols.value[1].val * 2 ^ 16 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt h_sum_lt]
    split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 16000000 in
-- Mirrors `SubOperation.spec_inv` for the 2-limb HWord case, plus
-- composes `U16MSBOperation.spec_inv` on `value[1]` for the MSB clause.
/-- Inverse direction of `SubwOperation.spec`. -/
theorem spec_inv {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} {cols : SubwOperation (ZMod p)}
    (h_isU64_a : a.isU64) (h_isU64_b : b.isU64)
    (h_isU32_v : HWord.isU32 cols.value)
    (h_bv : HWord.toBitVec32 cols.value = execute_RTYPEW_pure_32_w a b .SUBW)
    (h_msb_eq : cols.msb.msb =
      if (HWord.toBitVec32 cols.value).msb then 1 else 0) :
    SP1ConstraintList.allHold (SubwOperation.constraints a b cols 1) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 h_isU64_a
  obtain ⟨hbb0, hbb1, _, _⟩ := Word.lt_cases_of_isU64 h_isU64_b
  obtain ⟨hv0, hv1⟩ := HWord.lt_cases_of_isU32 h_isU32_v
  -- Convert `h_msb_eq` from BitVec-msb form to val-form for U16MSB spec_inv.
  have h_msb_val :
      cols.msb.msb = if cols.value[1].val ≥ 32768 then 1 else 0 := by
    rw [h_msb_eq]
    simp only [HWord.toBitVec32, HWord.toNat, BitVec.msb_eq_toNat,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega :
      cols.value[0].val + cols.value[1].val * 2 ^ 16 < 2 ^ 32)]
    split_ifs <;> simp_all <;> omega
  -- Reduce h_bv to Nat-level limb equation.
  rw [show execute_RTYPEW_pure_32_w a b .SUBW =
        a.low.toBitVec32 - b.low.toBitVec32 from rfl,
      BitVec.eq_sub_iff_add_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
      HWord.toBitVec32_toNat h_isU32_v,
      HWord.toBitVec32_toNat (Word.isU64_low_isU32 h_isU64_b),
      HWord.toBitVec32_toNat (Word.isU64_low_isU32 h_isU64_a)] at h_bv
  simp only [HWord.toNat, Word.low, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h_bv
  rw [SubwOperation.allHold_constraints_iff]
  refine ⟨U16MSBOperation.spec_inv hv1 h_msb_val, ?_, ?_, hv0, hv1⟩
  · -- carry0 ∈ {0, 1}
    set q0 : ℕ := (cols.value[0].val + b[0].val) / 65536 with hq0_def
    set q1 : ℕ := (cols.value[1].val + b[1].val + q0) / 65536 with hq1_def
    have h_chain :
        q0 ≤ 1 ∧ q1 ≤ 1 ∧
        cols.value[0].val + b[0].val = a[0].val + q0 * 65536 ∧
        cols.value[1].val + b[1].val + q0 = a[1].val + q1 * 65536 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [hq0_def, hq1_def] <;> omega
    obtain ⟨hq0_le, _, e0n, _⟩ := h_chain
    have hc0_lift : (cols.value[0] : ZMod p) + b[0] =
        a[0] + (q0 : ZMod p) * 65536 := by
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
      push_cast at hcast
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
      mul_inv_cancel₀ val_65536_ne_zero
    have hc0_eq : (b[0] + cols.value[0] - a[0]) * (65536 : ZMod p)⁻¹ =
        (q0 : ZMod p) := by
      have h : b[0] + cols.value[0] - a[0] = (q0 : ZMod p) * 65536 := by
        linear_combination hc0_lift
      rw [h, mul_assoc, h65inv, mul_one]
    rw [hc0_eq]; interval_cases q0 <;> simp
  · -- carry1 ∈ {0, 1}
    set q0 : ℕ := (cols.value[0].val + b[0].val) / 65536 with hq0_def
    set q1 : ℕ := (cols.value[1].val + b[1].val + q0) / 65536 with hq1_def
    have h_chain :
        q0 ≤ 1 ∧ q1 ≤ 1 ∧
        cols.value[0].val + b[0].val = a[0].val + q0 * 65536 ∧
        cols.value[1].val + b[1].val + q0 = a[1].val + q1 * 65536 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [hq0_def, hq1_def] <;> omega
    obtain ⟨_, hq1_le, e0n, e1n⟩ := h_chain
    have hc0_lift : (cols.value[0] : ZMod p) + b[0] =
        a[0] + (q0 : ZMod p) * 65536 := by
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
      push_cast at hcast
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    have hc1_lift : (cols.value[1] : ZMod p) + b[1] + (q0 : ZMod p) =
        a[1] + (q1 : ZMod p) * 65536 := by
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
      push_cast at hcast
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
      mul_inv_cancel₀ val_65536_ne_zero
    have hc0_eq : (b[0] + cols.value[0] - a[0]) * (65536 : ZMod p)⁻¹ =
        (q0 : ZMod p) := by
      have h : b[0] + cols.value[0] - a[0] = (q0 : ZMod p) * 65536 := by
        linear_combination hc0_lift
      rw [h, mul_assoc, h65inv, mul_one]
    have hc1_eq : (b[1] + cols.value[1] - a[1] +
        (b[0] + cols.value[0] - a[0]) * (65536 : ZMod p)⁻¹) *
        (65536 : ZMod p)⁻¹ = (q1 : ZMod p) := by
      rw [hc0_eq]
      have h : b[1] + cols.value[1] - a[1] + (q0 : ZMod p) =
          (q1 : ZMod p) * 65536 := by
        linear_combination hc1_lift
      rw [h, mul_assoc, h65inv, mul_one]
    rw [hc1_eq]; interval_cases q1 <;> simp

/-- Bidirectional bridge between `SubwOperation.allHold` (with multiplicity
fixed to `1`) and the BitVec + MSB semantic. -/
theorem iff_sp1_full {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} {cols : SubwOperation (ZMod p)}
    (h_isU64_a : a.isU64) (h_isU64_b : b.isU64) :
    (SubwOperation.constraints a b cols 1).allHold ↔
      (HWord.isU32 cols.value ∧
       HWord.toBitVec32 cols.value = execute_RTYPEW_pure_32_w a b .SUBW ∧
       cols.msb.msb =
         if (HWord.toBitVec32 cols.value).msb then 1 else 0) :=
  ⟨SubwOperation.spec h_isU64_a h_isU64_b,
   fun ⟨h_isU32_v, h_bv, h_msb⟩ =>
     SubwOperation.spec_inv h_isU64_a h_isU64_b h_isU32_v h_bv h_msb⟩

end SubwOperation
