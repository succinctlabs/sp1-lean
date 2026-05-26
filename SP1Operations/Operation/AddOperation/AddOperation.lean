import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation
import SP1Operations.Operation.AddOperation.Constraints

namespace AddOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : AddOperation (ZMod p)) :
    SP1ConstraintList.allHold (constraints a b cols 1) ↔
      let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : ZMod p := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : ZMod p := (a[3] + b[3] - cols.value[3] + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) ∧
      (cols.value[3].val < 65536) := by
  simp [constraints, sub_eq_zero, SP1Constraint.toProp]

/-- Per-limb Nat lift: given the ZMod-level limb equation
`bb + vv + prev = aa + cc * 65536` (where `prev, cc ∈ {0, 1}` and the
`bb, vv, aa` limbs are bounded by `2^16`), produce the Nat equation
`bb.val + vv.val + prev.val = aa.val + cc.val * 65536`. The `[Fact (2^17
< p)]` hypothesis ensures every additive sum on either side fits in
`< p`, so `apply_fun ZMod.val` plus `ZMod.val_add_of_lt` lifts cleanly.
Mirrors `SubOperation.limb_lift` verbatim — kept private here rather than
extracted to a shared header until a third op needs it. -/
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
-- The 4 `linear_combination`-based carry rearrangements plus the BitVec
-- ↔ Nat bridge sit in the 4–8M heartbeat range; 16M leaves headroom.
/-- Rearranges each iff carry from inverse-form to a sum equation
`a[i] + b[i] + prev = cols.value[i] + c_i * 65536` via `linear_combination`
over `(65536 : ZMod p) * 65536⁻¹ = 1`, then applies `limb_lift` to convert
each to a Nat equation, and closes the BitVec goal (after
`Word.toBitVec64_toNat` bridges) by omega. -/
theorem spec
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : AddOperation (ZMod p)}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  SP1ConstraintList.allHold (constraints a b cols 1) →
    cols.value.isU64 ∧
    cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD := by
  intro cstrs
  rw [allHold_constraints_iff] at cstrs
  obtain ⟨hc0, hc1, hc2, hc3, hv0, hv1, hv2, hv3⟩ := cstrs
  have h_isU64_v : cols.value.isU64 :=
    Word.isU64_of_cases hv0 hv1 hv2 hv3
  refine ⟨h_isU64_v, ?_⟩
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 h_isU64_a
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 h_isU64_b
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [show execute_RTYPE_pure_w a b .ADD =
        a.toBitVec64 + b.toBitVec64 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_isU64_v,
      Word.toBitVec64_toNat h_isU64_b,
      Word.toBitVec64_toNat h_isU64_a,
      Word.toNat_def, Word.toNat_def, Word.toNat_def]
  set c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (a[2] + b[2] - cols.value[2] + c1) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (a[3] + b[3] - cols.value[3] + c2) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : a[0] + b[0] + (0 : ZMod p) = cols.value[0] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (a[0] + b[0] - cols.value[0]) * h65inv
  have e1 : a[1] + b[1] + c0 = cols.value[1] + c1 * 65536 := by
    rw [hc1_def]; linear_combination -1 * (a[1] + b[1] - cols.value[1] + c0) * h65inv
  have e2 : a[2] + b[2] + c1 = cols.value[2] + c2 * 65536 := by
    rw [hc2_def]; linear_combination -1 * (a[2] + b[2] - cols.value[2] + c1) * h65inv
  have e3 : a[3] + b[3] + c2 = cols.value[3] + c3 * 65536 := by
    rw [hc3_def]; linear_combination -1 * (a[3] + b[3] - cols.value[3] + c2) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0 hc_zero hc0 e0
  have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1 hc0 hc1 e1
  have n2 := limb_lift _ _ _ _ _ ha2 hbb2 hv2 hc1 hc2 e2
  have n3 := limb_lift _ _ _ _ _ ha3 hbb3 hv3 hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero] at n0
  have hc0_lt : c0.val ≤ 1 := by
    rcases hc0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by
    rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by
    rcases hc2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by
    rcases hc3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

set_option maxHeartbeats 16000000 in
-- The 4 `linear_combination` carry rearrangements + 4 ZMod-cast lifts
-- + 4 `interval_cases` discharges land in the 4-8M heartbeat range;
-- 16M leaves headroom (mirrors `spec`'s budget).
/-- Inverse direction of `AddOperation.spec`: given that the operand and
result Words all fit in 64 bits and the BitVec sum identity holds, the
8-conjunct `AddOperation.constraints` evaluates to `allHold`. Witnesses
the unique base-65536 carry-chain decomposition of the BitVec sum. -/
theorem spec_inv {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} {cols : AddOperation (ZMod p)}
    (h_isU64_a : a.isU64) (h_isU64_b : b.isU64)
    (h_isU64_v : cols.value.isU64)
    (h_bv : cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD) :
    SP1ConstraintList.allHold (AddOperation.constraints a b cols 1) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  rw [AddOperation.allHold_constraints_iff]
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 h_isU64_a
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 h_isU64_b
  obtain ⟨hv0, hv1, hv2, hv3⟩ := Word.lt_cases_of_isU64 h_isU64_v
  rw [show execute_RTYPE_pure_w a b .ADD = a.toBitVec64 + b.toBitVec64 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_isU64_v,
      Word.toBitVec64_toNat h_isU64_b,
      Word.toBitVec64_toNat h_isU64_a,
      Word.toNat_def, Word.toNat_def, Word.toNat_def] at h_bv
  set q0 : ℕ := (a[0].val + b[0].val) / 65536 with hq0_def
  set q1 : ℕ := (a[1].val + b[1].val + q0) / 65536 with hq1_def
  set q2 : ℕ := (a[2].val + b[2].val + q1) / 65536 with hq2_def
  set q3 : ℕ := (a[3].val + b[3].val + q2) / 65536 with hq3_def
  have h_chain :
      q0 ≤ 1 ∧ q1 ≤ 1 ∧ q2 ≤ 1 ∧ q3 ≤ 1 ∧
      a[0].val + b[0].val = cols.value[0].val + q0 * 65536 ∧
      a[1].val + b[1].val + q0 = cols.value[1].val + q1 * 65536 ∧
      a[2].val + b[2].val + q1 = cols.value[2].val + q2 * 65536 ∧
      a[3].val + b[3].val + q2 = cols.value[3].val + q3 * 65536 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hq0_def, hq1_def, hq2_def, hq3_def] <;> omega
  obtain ⟨hq0, hq1, hq2, hq3, e0n, e1n, e2n, e3n⟩ := h_chain
  have hc0_lift : (a[0] : ZMod p) + b[0] =
      cols.value[0] + (q0 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc1_lift : (a[1] : ZMod p) + b[1] + (q0 : ZMod p) =
      cols.value[1] + (q1 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc2_lift : (a[2] : ZMod p) + b[2] + (q1 : ZMod p) =
      cols.value[2] + (q2 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e2n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc3_lift : (a[3] : ZMod p) + b[3] + (q2 : ZMod p) =
      cols.value[3] + (q3 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e3n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  have hc0_eq : (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ =
      (q0 : ZMod p) := by
    have h : a[0] + b[0] - cols.value[0] = (q0 : ZMod p) * 65536 := by
      linear_combination hc0_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc1_eq : (a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) *
      (65536 : ZMod p)⁻¹ = (q1 : ZMod p) := by
    rw [hc0_eq]
    have h : a[1] + b[1] - cols.value[1] + (q0 : ZMod p) =
        (q1 : ZMod p) * 65536 := by
      linear_combination hc1_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc2_eq : (a[2] + b[2] - cols.value[2] + ((a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) *
      (65536 : ZMod p)⁻¹)) * (65536 : ZMod p)⁻¹ = (q2 : ZMod p) := by
    rw [hc1_eq]
    have h : a[2] + b[2] - cols.value[2] + (q1 : ZMod p) =
        (q2 : ZMod p) * 65536 := by
      linear_combination hc2_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc3_eq : (a[3] + b[3] - cols.value[3] + ((a[2] + b[2] - cols.value[2] +
      ((a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) *
      (65536 : ZMod p)⁻¹)) * (65536 : ZMod p)⁻¹)) *
      (65536 : ZMod p)⁻¹ = (q3 : ZMod p) := by
    rw [hc2_eq]
    have h : a[3] + b[3] - cols.value[3] + (q2 : ZMod p) =
        (q3 : ZMod p) * 65536 := by
      linear_combination hc3_lift
    rw [h, mul_assoc, h65inv, mul_one]
  refine ⟨?_, ?_, ?_, ?_, hv0, hv1, hv2, hv3⟩
  · rw [hc0_eq]; interval_cases q0 <;> simp
  · rw [hc1_eq]; interval_cases q1 <;> simp
  · rw [hc2_eq]; interval_cases q2 <;> simp
  · rw [hc3_eq]; interval_cases q3 <;> simp

/-- Bidirectional bridge between `AddOperation.allHold` (with multiplicity
fixed to `1`) and the BitVec semantic: a fully-bounded operand triple
satisfies the constraints iff the result is also bounded and the BitVec
sum identity holds. Composes `AddOperation.spec` (forward) with
`AddOperation.spec_inv` (backward). -/
theorem iff_sp1_full {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} {cols : AddOperation (ZMod p)}
    (h_isU64_a : a.isU64) (h_isU64_b : b.isU64) :
    (AddOperation.constraints a b cols 1).allHold ↔
      (cols.value.isU64 ∧
       cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD) :=
  ⟨AddOperation.spec h_isU64_a h_isU64_b,
   fun ⟨h_isU64_v, h_bv⟩ =>
     AddOperation.spec_inv h_isU64_a h_isU64_b h_isU64_v h_bv⟩

section gen

theorem spec.gen
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : AddOperation (ZMod p)}
  {is_real : ZMod p}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols is_real) →
    is_real = 1 →
      cols.value.isU64 ∧
      cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD := by
  intros cstrs hir
  subst hir
  exact spec h_isU64_a h_isU64_b cstrs

end gen

end AddOperation
