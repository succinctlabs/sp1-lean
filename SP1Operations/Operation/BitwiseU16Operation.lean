import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.U16toU8OperationSafe
import SP1Operations.Operation.BitwiseOperation
import SP1Operations.Operation.BitwiseU16Operation.Operation
import SP1Operations.Operation.BitwiseU16Operation.Constraints

set_option linter.style.setOption false
set_option maxHeartbeats 10000000

namespace BitwiseU16Operation

set_option maxHeartbeats 64000000 in
-- `bv_decide`-after-byte-decomposition recipe; uses `spec.unsafe.return_poly`
-- + `Word.toBitVec64_poly` and explicit `.val` arithmetic to remove `% p`
-- from the byte-AND/OR/XOR equations (`byte.val < 256 < p` makes `% p` an
-- identity).
lemma spec.and_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {b cc : Word (ZMod p)} {cols : BitwiseU16Operation (ZMod p)}
    (h_isU64_b : b.isU64_poly) (h_isU64_cc : cc.isU64_poly) :
    List.Forall SP1Constraint.toProp_poly (constraints b cc cols 0 1).2 →
      Word.toBitVec64_poly (constraints b cc cols 0 1).1 = execute_RTYPE_pure_w_poly b cc .AND
        := by
  intro cstrs
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  have h_bw_b := @U16toU8OperationSafe.spec.unsafe.return_poly p _ _ b
    { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1],
      cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] } (by
    simp [constraints, BitwiseOperation.constraints,
      U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints, h0_lt_256] at *
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := cstrs
    aesop)
  have h_bw_c := @U16toU8OperationSafe.spec.unsafe.return_poly p _ _ cc
    { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1],
      cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] } (by
    simp [constraints, BitwiseOperation.constraints,
      U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints, h0_lt_256] at *
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := cstrs
    aesop)
  obtain ⟨hb0lt, hb1lt, hb2lt, hb3lt⟩ := Word.lt_cases_of_isU64_poly h_isU64_b
  obtain ⟨hc0lt, hc1lt, hc2lt, hc3lt⟩ := Word.lt_cases_of_isU64_poly h_isU64_cc
  simp [U16toU8OperationUnsafe.constraints, Word.toBWord_poly] at h_bw_b h_bw_c
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := h_bw_b
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := h_bw_c
  simp_all [constraints, U16toU8OperationUnsafe.constraints]
  simp [BitwiseOperation.constraints] at cstrs
  obtain ⟨⟨⟨hr0, _, _⟩, heq_0⟩, ⟨⟨hr1, _, _⟩, heq_1⟩, ⟨⟨hr2, _, _⟩, heq_2⟩,
          ⟨⟨hr3, _, _⟩, heq_3⟩, ⟨⟨hr4, _, _⟩, heq_4⟩, ⟨⟨hr5, _, _⟩, heq_5⟩,
          ⟨⟨hr6, _, _⟩, heq_6⟩, ⟨⟨hr7, _, _⟩, heq_7⟩⟩ := cstrs
  have h256_val : (256 : ZMod p).val = 256 :=
    ZMod.val_natCast_of_lt (show (256 : ℕ) < p by omega)
  have hr0' : cols.bitwise_operation.result[0].val < 256 := by
    have h : cols.bitwise_operation.result[0].val < (256 : ZMod p).val := hr0
    rw [h256_val] at h; exact h
  have hr1' : cols.bitwise_operation.result[1].val < 256 := by
    have h : cols.bitwise_operation.result[1].val < (256 : ZMod p).val := hr1
    rw [h256_val] at h; exact h
  have hr2' : cols.bitwise_operation.result[2].val < 256 := by
    have h : cols.bitwise_operation.result[2].val < (256 : ZMod p).val := hr2
    rw [h256_val] at h; exact h
  have hr3' : cols.bitwise_operation.result[3].val < 256 := by
    have h : cols.bitwise_operation.result[3].val < (256 : ZMod p).val := hr3
    rw [h256_val] at h; exact h
  have hr4' : cols.bitwise_operation.result[4].val < 256 := by
    have h : cols.bitwise_operation.result[4].val < (256 : ZMod p).val := hr4
    rw [h256_val] at h; exact h
  have hr5' : cols.bitwise_operation.result[5].val < 256 := by
    have h : cols.bitwise_operation.result[5].val < (256 : ZMod p).val := hr5
    rw [h256_val] at h; exact h
  have hr6' : cols.bitwise_operation.result[6].val < 256 := by
    have h : cols.bitwise_operation.result[6].val < (256 : ZMod p).val := hr6
    rw [h256_val] at h; exact h
  have hr7' : cols.bitwise_operation.result[7].val < 256 := by
    have h : cols.bitwise_operation.result[7].val < (256 : ZMod p).val := hr7
    rw [h256_val] at h; exact h
  have hbm0 : b[0].val % 256 % p = b[0].val % 256 := Nat.mod_eq_of_lt (by have : b[0].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd0 : b[0].val / 256 % p = b[0].val / 256 := Nat.mod_eq_of_lt (by have : b[0].val / 256 ≤ b[0].val := Nat.div_le_self _ _; omega)
  have hbm1 : b[1].val % 256 % p = b[1].val % 256 := Nat.mod_eq_of_lt (by have : b[1].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd1 : b[1].val / 256 % p = b[1].val / 256 := Nat.mod_eq_of_lt (by have : b[1].val / 256 ≤ b[1].val := Nat.div_le_self _ _; omega)
  have hbm2 : b[2].val % 256 % p = b[2].val % 256 := Nat.mod_eq_of_lt (by have : b[2].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd2 : b[2].val / 256 % p = b[2].val / 256 := Nat.mod_eq_of_lt (by have : b[2].val / 256 ≤ b[2].val := Nat.div_le_self _ _; omega)
  have hbm3 : b[3].val % 256 % p = b[3].val % 256 := Nat.mod_eq_of_lt (by have : b[3].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd3 : b[3].val / 256 % p = b[3].val / 256 := Nat.mod_eq_of_lt (by have : b[3].val / 256 ≤ b[3].val := Nat.div_le_self _ _; omega)
  have hcm0 : cc[0].val % 256 % p = cc[0].val % 256 := Nat.mod_eq_of_lt (by have : cc[0].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd0 : cc[0].val / 256 % p = cc[0].val / 256 := Nat.mod_eq_of_lt (by have : cc[0].val / 256 ≤ cc[0].val := Nat.div_le_self _ _; omega)
  have hcm1 : cc[1].val % 256 % p = cc[1].val % 256 := Nat.mod_eq_of_lt (by have : cc[1].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd1 : cc[1].val / 256 % p = cc[1].val / 256 := Nat.mod_eq_of_lt (by have : cc[1].val / 256 ≤ cc[1].val := Nat.div_le_self _ _; omega)
  have hcm2 : cc[2].val % 256 % p = cc[2].val % 256 := Nat.mod_eq_of_lt (by have : cc[2].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd2 : cc[2].val / 256 % p = cc[2].val / 256 := Nat.mod_eq_of_lt (by have : cc[2].val / 256 ≤ cc[2].val := Nat.div_le_self _ _; omega)
  have hcm3 : cc[3].val % 256 % p = cc[3].val % 256 := Nat.mod_eq_of_lt (by have : cc[3].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd3 : cc[3].val / 256 % p = cc[3].val / 256 := Nat.mod_eq_of_lt (by have : cc[3].val / 256 ≤ cc[3].val := Nat.div_le_self _ _; omega)
  simp only [hbm0, hbd0, hbm1, hbd1, hbm2, hbd2, hbm3, hbd3] at heq_0 heq_1 heq_2 heq_3 heq_4 heq_5 heq_6 heq_7
  simp only [hcm0, hcd0, hcm1, hcd1, hcm2, hcd2, hcm3, hcd3] at heq_0 heq_1 heq_2 heq_3 heq_4 heq_5 heq_6 heq_7
  have hadd : ∀ (x y : ZMod p), x.val < 256 → y.val < 256 →
      (x + y * 256).val = x.val + y.val * 256 := by
    intro x y hx hy
    rw [ZMod.val_add_of_lt, ZMod.val_mul_of_lt]
    · rw [h256_val]
    · rw [h256_val]; nlinarith
    · rw [ZMod.val_mul_of_lt (by rw [h256_val]; nlinarith), h256_val]; nlinarith
  unfold Word.toBitVec64_poly
  simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  rw [hadd _ _ hr0' hr1', hadd _ _ hr2' hr3', hadd _ _ hr4' hr5', hadd _ _ hr6' hr7']
  rw [heq_0, heq_1, heq_2, heq_3, heq_4, heq_5, heq_6, heq_7]
  set b00 := b[0].val % 256
  set b01 := b[0].val / 256
  set b10 := b[1].val % 256
  set b11 := b[1].val / 256
  set b20 := b[2].val % 256
  set b21 := b[2].val / 256
  set b30 := b[3].val % 256
  set b31 := b[3].val / 256
  set c00 := cc[0].val % 256
  set c01 := cc[0].val / 256
  set c10 := cc[1].val % 256
  set c11 := cc[1].val / 256
  set c20 := cc[2].val % 256
  set c21 := cc[2].val / 256
  set c30 := cc[3].val % 256
  set c31 := cc[3].val / 256
  have hb_b0 : b00 < 256 ∧ b01 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[0].val / 256 < 256; omega⟩
  have hb_b1 : b10 < 256 ∧ b11 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[1].val / 256 < 256; omega⟩
  have hb_b2 : b20 < 256 ∧ b21 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[2].val / 256 < 256; omega⟩
  have hb_b3 : b30 < 256 ∧ b31 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[3].val / 256 < 256; omega⟩
  have hb_c0 : c00 < 256 ∧ c01 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[0].val / 256 < 256; omega⟩
  have hb_c1 : c10 < 256 ∧ c11 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[1].val / 256 < 256; omega⟩
  have hb_c2 : c20 < 256 ∧ c21 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[2].val / 256 < 256; omega⟩
  have hb_c3 : c30 < 256 ∧ c31 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[3].val / 256 < 256; omega⟩
  have hb0d : b[0].val = b00 + b01 * 256 := by change b[0].val = b[0].val % 256 + b[0].val / 256 * 256; omega
  have hb1d : b[1].val = b10 + b11 * 256 := by change b[1].val = b[1].val % 256 + b[1].val / 256 * 256; omega
  have hb2d : b[2].val = b20 + b21 * 256 := by change b[2].val = b[2].val % 256 + b[2].val / 256 * 256; omega
  have hb3d : b[3].val = b30 + b31 * 256 := by change b[3].val = b[3].val % 256 + b[3].val / 256 * 256; omega
  have hc0d : cc[0].val = c00 + c01 * 256 := by change cc[0].val = cc[0].val % 256 + cc[0].val / 256 * 256; omega
  have hc1d : cc[1].val = c10 + c11 * 256 := by change cc[1].val = cc[1].val % 256 + cc[1].val / 256 * 256; omega
  have hc2d : cc[2].val = c20 + c21 * 256 := by change cc[2].val = cc[2].val % 256 + cc[2].val / 256 * 256; omega
  have hc3d : cc[3].val = c30 + c31 * 256 := by change cc[3].val = cc[3].val % 256 + cc[3].val / 256 * 256; omega
  rw [hb0d, hb1d, hb2d, hb3d, hc0d, hc1d, hc2d, hc3d]
  obtain ⟨bb00, bb01⟩ := hb_b0
  obtain ⟨bb10, bb11⟩ := hb_b1
  obtain ⟨bb20, bb21⟩ := hb_b2
  obtain ⟨bb30, bb31⟩ := hb_b3
  obtain ⟨cc00, cc01⟩ := hb_c0
  obtain ⟨cc10, cc11⟩ := hb_c1
  obtain ⟨cc20, cc21⟩ := hb_c2
  obtain ⟨cc30, cc31⟩ := hb_c3
  rw [Nat.lift_lt 64 (by omega) (by omega)] at bb00 bb01 bb10 bb11 bb20 bb21 bb30 bb31
  rw [Nat.lift_lt 64 (by omega) (by omega)] at cc00 cc01 cc10 cc11 cc20 cc21 cc30 cc31
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_and]
  bv_decide

lemma spec.or_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {b cc : Word (ZMod p)} {cols : BitwiseU16Operation (ZMod p)}
    (h_isU64_b : b.isU64_poly) (h_isU64_cc : cc.isU64_poly) :
    List.Forall SP1Constraint.toProp_poly (constraints b cc cols 1 1).2 →
      Word.toBitVec64_poly (constraints b cc cols 1 1).1 = execute_RTYPE_pure_w_poly b cc .OR
        := by
  intro cstrs
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_bw_b := @U16toU8OperationSafe.spec.unsafe.return_poly p _ _ b
    { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1],
      cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] } (by
    simp [constraints, BitwiseOperation.constraints,
      U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints, h0_lt_256,
      h1_val] at *
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := cstrs
    aesop)
  have h_bw_c := @U16toU8OperationSafe.spec.unsafe.return_poly p _ _ cc
    { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1],
      cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] } (by
    simp [constraints, BitwiseOperation.constraints,
      U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints, h0_lt_256,
      h1_val] at *
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := cstrs
    aesop)
  obtain ⟨hb0lt, hb1lt, hb2lt, hb3lt⟩ := Word.lt_cases_of_isU64_poly h_isU64_b
  obtain ⟨hc0lt, hc1lt, hc2lt, hc3lt⟩ := Word.lt_cases_of_isU64_poly h_isU64_cc
  simp [U16toU8OperationUnsafe.constraints, Word.toBWord_poly] at h_bw_b h_bw_c
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := h_bw_b
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := h_bw_c
  simp_all [constraints, U16toU8OperationUnsafe.constraints]
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h1_val' : (1 : ZMod p).val = 1 := ZMod.val_one p
  simp [BitwiseOperation.constraints, h1_val'] at cstrs
  obtain ⟨⟨⟨hr0, _, _⟩, heq_0⟩, ⟨⟨hr1, _, _⟩, heq_1⟩, ⟨⟨hr2, _, _⟩, heq_2⟩,
          ⟨⟨hr3, _, _⟩, heq_3⟩, ⟨⟨hr4, _, _⟩, heq_4⟩, ⟨⟨hr5, _, _⟩, heq_5⟩,
          ⟨⟨hr6, _, _⟩, heq_6⟩, ⟨⟨hr7, _, _⟩, heq_7⟩⟩ := cstrs
  have h256_val : (256 : ZMod p).val = 256 :=
    ZMod.val_natCast_of_lt (show (256 : ℕ) < p by omega)
  have hr0' : cols.bitwise_operation.result[0].val < 256 := by
    have h : cols.bitwise_operation.result[0].val < (256 : ZMod p).val := hr0
    rw [h256_val] at h; exact h
  have hr1' : cols.bitwise_operation.result[1].val < 256 := by
    have h : cols.bitwise_operation.result[1].val < (256 : ZMod p).val := hr1
    rw [h256_val] at h; exact h
  have hr2' : cols.bitwise_operation.result[2].val < 256 := by
    have h : cols.bitwise_operation.result[2].val < (256 : ZMod p).val := hr2
    rw [h256_val] at h; exact h
  have hr3' : cols.bitwise_operation.result[3].val < 256 := by
    have h : cols.bitwise_operation.result[3].val < (256 : ZMod p).val := hr3
    rw [h256_val] at h; exact h
  have hr4' : cols.bitwise_operation.result[4].val < 256 := by
    have h : cols.bitwise_operation.result[4].val < (256 : ZMod p).val := hr4
    rw [h256_val] at h; exact h
  have hr5' : cols.bitwise_operation.result[5].val < 256 := by
    have h : cols.bitwise_operation.result[5].val < (256 : ZMod p).val := hr5
    rw [h256_val] at h; exact h
  have hr6' : cols.bitwise_operation.result[6].val < 256 := by
    have h : cols.bitwise_operation.result[6].val < (256 : ZMod p).val := hr6
    rw [h256_val] at h; exact h
  have hr7' : cols.bitwise_operation.result[7].val < 256 := by
    have h : cols.bitwise_operation.result[7].val < (256 : ZMod p).val := hr7
    rw [h256_val] at h; exact h
  have hbm0 : b[0].val % 256 % p = b[0].val % 256 := Nat.mod_eq_of_lt (by have : b[0].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd0 : b[0].val / 256 % p = b[0].val / 256 := Nat.mod_eq_of_lt (by have : b[0].val / 256 ≤ b[0].val := Nat.div_le_self _ _; omega)
  have hbm1 : b[1].val % 256 % p = b[1].val % 256 := Nat.mod_eq_of_lt (by have : b[1].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd1 : b[1].val / 256 % p = b[1].val / 256 := Nat.mod_eq_of_lt (by have : b[1].val / 256 ≤ b[1].val := Nat.div_le_self _ _; omega)
  have hbm2 : b[2].val % 256 % p = b[2].val % 256 := Nat.mod_eq_of_lt (by have : b[2].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd2 : b[2].val / 256 % p = b[2].val / 256 := Nat.mod_eq_of_lt (by have : b[2].val / 256 ≤ b[2].val := Nat.div_le_self _ _; omega)
  have hbm3 : b[3].val % 256 % p = b[3].val % 256 := Nat.mod_eq_of_lt (by have : b[3].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd3 : b[3].val / 256 % p = b[3].val / 256 := Nat.mod_eq_of_lt (by have : b[3].val / 256 ≤ b[3].val := Nat.div_le_self _ _; omega)
  have hcm0 : cc[0].val % 256 % p = cc[0].val % 256 := Nat.mod_eq_of_lt (by have : cc[0].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd0 : cc[0].val / 256 % p = cc[0].val / 256 := Nat.mod_eq_of_lt (by have : cc[0].val / 256 ≤ cc[0].val := Nat.div_le_self _ _; omega)
  have hcm1 : cc[1].val % 256 % p = cc[1].val % 256 := Nat.mod_eq_of_lt (by have : cc[1].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd1 : cc[1].val / 256 % p = cc[1].val / 256 := Nat.mod_eq_of_lt (by have : cc[1].val / 256 ≤ cc[1].val := Nat.div_le_self _ _; omega)
  have hcm2 : cc[2].val % 256 % p = cc[2].val % 256 := Nat.mod_eq_of_lt (by have : cc[2].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd2 : cc[2].val / 256 % p = cc[2].val / 256 := Nat.mod_eq_of_lt (by have : cc[2].val / 256 ≤ cc[2].val := Nat.div_le_self _ _; omega)
  have hcm3 : cc[3].val % 256 % p = cc[3].val % 256 := Nat.mod_eq_of_lt (by have : cc[3].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd3 : cc[3].val / 256 % p = cc[3].val / 256 := Nat.mod_eq_of_lt (by have : cc[3].val / 256 ≤ cc[3].val := Nat.div_le_self _ _; omega)
  simp only [hbm0, hbd0, hbm1, hbd1, hbm2, hbd2, hbm3, hbd3] at heq_0 heq_1 heq_2 heq_3 heq_4 heq_5 heq_6 heq_7
  simp only [hcm0, hcd0, hcm1, hcd1, hcm2, hcd2, hcm3, hcd3] at heq_0 heq_1 heq_2 heq_3 heq_4 heq_5 heq_6 heq_7
  have hadd : ∀ (x y : ZMod p), x.val < 256 → y.val < 256 →
      (x + y * 256).val = x.val + y.val * 256 := by
    intro x y hx hy
    rw [ZMod.val_add_of_lt, ZMod.val_mul_of_lt]
    · rw [h256_val]
    · rw [h256_val]; nlinarith
    · rw [ZMod.val_mul_of_lt (by rw [h256_val]; nlinarith), h256_val]; nlinarith
  unfold Word.toBitVec64_poly
  simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  rw [hadd _ _ hr0' hr1', hadd _ _ hr2' hr3', hadd _ _ hr4' hr5', hadd _ _ hr6' hr7']
  rw [heq_0, heq_1, heq_2, heq_3, heq_4, heq_5, heq_6, heq_7]
  set b00 := b[0].val % 256
  set b01 := b[0].val / 256
  set b10 := b[1].val % 256
  set b11 := b[1].val / 256
  set b20 := b[2].val % 256
  set b21 := b[2].val / 256
  set b30 := b[3].val % 256
  set b31 := b[3].val / 256
  set c00 := cc[0].val % 256
  set c01 := cc[0].val / 256
  set c10 := cc[1].val % 256
  set c11 := cc[1].val / 256
  set c20 := cc[2].val % 256
  set c21 := cc[2].val / 256
  set c30 := cc[3].val % 256
  set c31 := cc[3].val / 256
  have hb_b0 : b00 < 256 ∧ b01 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[0].val / 256 < 256; omega⟩
  have hb_b1 : b10 < 256 ∧ b11 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[1].val / 256 < 256; omega⟩
  have hb_b2 : b20 < 256 ∧ b21 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[2].val / 256 < 256; omega⟩
  have hb_b3 : b30 < 256 ∧ b31 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[3].val / 256 < 256; omega⟩
  have hb_c0 : c00 < 256 ∧ c01 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[0].val / 256 < 256; omega⟩
  have hb_c1 : c10 < 256 ∧ c11 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[1].val / 256 < 256; omega⟩
  have hb_c2 : c20 < 256 ∧ c21 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[2].val / 256 < 256; omega⟩
  have hb_c3 : c30 < 256 ∧ c31 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[3].val / 256 < 256; omega⟩
  have hb0d : b[0].val = b00 + b01 * 256 := by change b[0].val = b[0].val % 256 + b[0].val / 256 * 256; omega
  have hb1d : b[1].val = b10 + b11 * 256 := by change b[1].val = b[1].val % 256 + b[1].val / 256 * 256; omega
  have hb2d : b[2].val = b20 + b21 * 256 := by change b[2].val = b[2].val % 256 + b[2].val / 256 * 256; omega
  have hb3d : b[3].val = b30 + b31 * 256 := by change b[3].val = b[3].val % 256 + b[3].val / 256 * 256; omega
  have hc0d : cc[0].val = c00 + c01 * 256 := by change cc[0].val = cc[0].val % 256 + cc[0].val / 256 * 256; omega
  have hc1d : cc[1].val = c10 + c11 * 256 := by change cc[1].val = cc[1].val % 256 + cc[1].val / 256 * 256; omega
  have hc2d : cc[2].val = c20 + c21 * 256 := by change cc[2].val = cc[2].val % 256 + cc[2].val / 256 * 256; omega
  have hc3d : cc[3].val = c30 + c31 * 256 := by change cc[3].val = cc[3].val % 256 + cc[3].val / 256 * 256; omega
  rw [hb0d, hb1d, hb2d, hb3d, hc0d, hc1d, hc2d, hc3d]
  obtain ⟨bb00, bb01⟩ := hb_b0
  obtain ⟨bb10, bb11⟩ := hb_b1
  obtain ⟨bb20, bb21⟩ := hb_b2
  obtain ⟨bb30, bb31⟩ := hb_b3
  obtain ⟨cc00, cc01⟩ := hb_c0
  obtain ⟨cc10, cc11⟩ := hb_c1
  obtain ⟨cc20, cc21⟩ := hb_c2
  obtain ⟨cc30, cc31⟩ := hb_c3
  rw [Nat.lift_lt 64 (by omega) (by omega)] at bb00 bb01 bb10 bb11 bb20 bb21 bb30 bb31
  rw [Nat.lift_lt 64 (by omega) (by omega)] at cc00 cc01 cc10 cc11 cc20 cc21 cc30 cc31
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_or]
  bv_decide

lemma spec.xor_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {b cc : Word (ZMod p)} {cols : BitwiseU16Operation (ZMod p)}
    (h_isU64_b : b.isU64_poly) (h_isU64_cc : cc.isU64_poly) :
    List.Forall SP1Constraint.toProp_poly (constraints b cc cols 2 1).2 →
      Word.toBitVec64_poly (constraints b cc cols 2 1).1 = execute_RTYPE_pure_w_poly b cc .XOR
        := by
  intro cstrs
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  have h2_val : (2 : ZMod p).val = 2 := val_2_zmod_p
  have h_bw_b := @U16toU8OperationSafe.spec.unsafe.return_poly p _ _ b
    { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1],
      cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] } (by
    simp [constraints, BitwiseOperation.constraints,
      U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints, h0_lt_256,
      h2_val] at *
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := cstrs
    aesop)
  have h_bw_c := @U16toU8OperationSafe.spec.unsafe.return_poly p _ _ cc
    { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1],
      cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] } (by
    simp [constraints, BitwiseOperation.constraints,
      U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints, h0_lt_256,
      h2_val] at *
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := cstrs
    aesop)
  obtain ⟨hb0lt, hb1lt, hb2lt, hb3lt⟩ := Word.lt_cases_of_isU64_poly h_isU64_b
  obtain ⟨hc0lt, hc1lt, hc2lt, hc3lt⟩ := Word.lt_cases_of_isU64_poly h_isU64_cc
  simp [U16toU8OperationUnsafe.constraints, Word.toBWord_poly] at h_bw_b h_bw_c
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := h_bw_b
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := h_bw_c
  simp_all [constraints, U16toU8OperationUnsafe.constraints]
  have h2_val' : (2 : ZMod p).val = 2 := by
    have h : ((2 : ℕ) : ZMod p).val = 2 :=
      ZMod.val_natCast_of_lt (show (2 : ℕ) < p by omega)
    simpa using h
  simp [BitwiseOperation.constraints, h2_val'] at cstrs
  obtain ⟨⟨⟨hr0, _, _⟩, heq_0⟩, ⟨⟨hr1, _, _⟩, heq_1⟩, ⟨⟨hr2, _, _⟩, heq_2⟩,
          ⟨⟨hr3, _, _⟩, heq_3⟩, ⟨⟨hr4, _, _⟩, heq_4⟩, ⟨⟨hr5, _, _⟩, heq_5⟩,
          ⟨⟨hr6, _, _⟩, heq_6⟩, ⟨⟨hr7, _, _⟩, heq_7⟩⟩ := cstrs
  have h256_val : (256 : ZMod p).val = 256 :=
    ZMod.val_natCast_of_lt (show (256 : ℕ) < p by omega)
  have hr0' : cols.bitwise_operation.result[0].val < 256 := by
    have h : cols.bitwise_operation.result[0].val < (256 : ZMod p).val := hr0
    rw [h256_val] at h; exact h
  have hr1' : cols.bitwise_operation.result[1].val < 256 := by
    have h : cols.bitwise_operation.result[1].val < (256 : ZMod p).val := hr1
    rw [h256_val] at h; exact h
  have hr2' : cols.bitwise_operation.result[2].val < 256 := by
    have h : cols.bitwise_operation.result[2].val < (256 : ZMod p).val := hr2
    rw [h256_val] at h; exact h
  have hr3' : cols.bitwise_operation.result[3].val < 256 := by
    have h : cols.bitwise_operation.result[3].val < (256 : ZMod p).val := hr3
    rw [h256_val] at h; exact h
  have hr4' : cols.bitwise_operation.result[4].val < 256 := by
    have h : cols.bitwise_operation.result[4].val < (256 : ZMod p).val := hr4
    rw [h256_val] at h; exact h
  have hr5' : cols.bitwise_operation.result[5].val < 256 := by
    have h : cols.bitwise_operation.result[5].val < (256 : ZMod p).val := hr5
    rw [h256_val] at h; exact h
  have hr6' : cols.bitwise_operation.result[6].val < 256 := by
    have h : cols.bitwise_operation.result[6].val < (256 : ZMod p).val := hr6
    rw [h256_val] at h; exact h
  have hr7' : cols.bitwise_operation.result[7].val < 256 := by
    have h : cols.bitwise_operation.result[7].val < (256 : ZMod p).val := hr7
    rw [h256_val] at h; exact h
  have hbm0 : b[0].val % 256 % p = b[0].val % 256 := Nat.mod_eq_of_lt (by have : b[0].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd0 : b[0].val / 256 % p = b[0].val / 256 := Nat.mod_eq_of_lt (by have : b[0].val / 256 ≤ b[0].val := Nat.div_le_self _ _; omega)
  have hbm1 : b[1].val % 256 % p = b[1].val % 256 := Nat.mod_eq_of_lt (by have : b[1].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd1 : b[1].val / 256 % p = b[1].val / 256 := Nat.mod_eq_of_lt (by have : b[1].val / 256 ≤ b[1].val := Nat.div_le_self _ _; omega)
  have hbm2 : b[2].val % 256 % p = b[2].val % 256 := Nat.mod_eq_of_lt (by have : b[2].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd2 : b[2].val / 256 % p = b[2].val / 256 := Nat.mod_eq_of_lt (by have : b[2].val / 256 ≤ b[2].val := Nat.div_le_self _ _; omega)
  have hbm3 : b[3].val % 256 % p = b[3].val % 256 := Nat.mod_eq_of_lt (by have : b[3].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hbd3 : b[3].val / 256 % p = b[3].val / 256 := Nat.mod_eq_of_lt (by have : b[3].val / 256 ≤ b[3].val := Nat.div_le_self _ _; omega)
  have hcm0 : cc[0].val % 256 % p = cc[0].val % 256 := Nat.mod_eq_of_lt (by have : cc[0].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd0 : cc[0].val / 256 % p = cc[0].val / 256 := Nat.mod_eq_of_lt (by have : cc[0].val / 256 ≤ cc[0].val := Nat.div_le_self _ _; omega)
  have hcm1 : cc[1].val % 256 % p = cc[1].val % 256 := Nat.mod_eq_of_lt (by have : cc[1].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd1 : cc[1].val / 256 % p = cc[1].val / 256 := Nat.mod_eq_of_lt (by have : cc[1].val / 256 ≤ cc[1].val := Nat.div_le_self _ _; omega)
  have hcm2 : cc[2].val % 256 % p = cc[2].val % 256 := Nat.mod_eq_of_lt (by have : cc[2].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd2 : cc[2].val / 256 % p = cc[2].val / 256 := Nat.mod_eq_of_lt (by have : cc[2].val / 256 ≤ cc[2].val := Nat.div_le_self _ _; omega)
  have hcm3 : cc[3].val % 256 % p = cc[3].val % 256 := Nat.mod_eq_of_lt (by have : cc[3].val % 256 < 256 := Nat.mod_lt _ (by omega); omega)
  have hcd3 : cc[3].val / 256 % p = cc[3].val / 256 := Nat.mod_eq_of_lt (by have : cc[3].val / 256 ≤ cc[3].val := Nat.div_le_self _ _; omega)
  simp only [hbm0, hbd0, hbm1, hbd1, hbm2, hbd2, hbm3, hbd3] at heq_0 heq_1 heq_2 heq_3 heq_4 heq_5 heq_6 heq_7
  simp only [hcm0, hcd0, hcm1, hcd1, hcm2, hcd2, hcm3, hcd3] at heq_0 heq_1 heq_2 heq_3 heq_4 heq_5 heq_6 heq_7
  have hadd : ∀ (x y : ZMod p), x.val < 256 → y.val < 256 →
      (x + y * 256).val = x.val + y.val * 256 := by
    intro x y hx hy
    rw [ZMod.val_add_of_lt, ZMod.val_mul_of_lt]
    · rw [h256_val]
    · rw [h256_val]; nlinarith
    · rw [ZMod.val_mul_of_lt (by rw [h256_val]; nlinarith), h256_val]; nlinarith
  unfold Word.toBitVec64_poly
  simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  rw [hadd _ _ hr0' hr1', hadd _ _ hr2' hr3', hadd _ _ hr4' hr5', hadd _ _ hr6' hr7']
  rw [heq_0, heq_1, heq_2, heq_3, heq_4, heq_5, heq_6, heq_7]
  set b00 := b[0].val % 256
  set b01 := b[0].val / 256
  set b10 := b[1].val % 256
  set b11 := b[1].val / 256
  set b20 := b[2].val % 256
  set b21 := b[2].val / 256
  set b30 := b[3].val % 256
  set b31 := b[3].val / 256
  set c00 := cc[0].val % 256
  set c01 := cc[0].val / 256
  set c10 := cc[1].val % 256
  set c11 := cc[1].val / 256
  set c20 := cc[2].val % 256
  set c21 := cc[2].val / 256
  set c30 := cc[3].val % 256
  set c31 := cc[3].val / 256
  have hb_b0 : b00 < 256 ∧ b01 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[0].val / 256 < 256; omega⟩
  have hb_b1 : b10 < 256 ∧ b11 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[1].val / 256 < 256; omega⟩
  have hb_b2 : b20 < 256 ∧ b21 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[2].val / 256 < 256; omega⟩
  have hb_b3 : b30 < 256 ∧ b31 < 256 := ⟨Nat.mod_lt _ (by omega), by change b[3].val / 256 < 256; omega⟩
  have hb_c0 : c00 < 256 ∧ c01 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[0].val / 256 < 256; omega⟩
  have hb_c1 : c10 < 256 ∧ c11 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[1].val / 256 < 256; omega⟩
  have hb_c2 : c20 < 256 ∧ c21 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[2].val / 256 < 256; omega⟩
  have hb_c3 : c30 < 256 ∧ c31 < 256 := ⟨Nat.mod_lt _ (by omega), by change cc[3].val / 256 < 256; omega⟩
  have hb0d : b[0].val = b00 + b01 * 256 := by change b[0].val = b[0].val % 256 + b[0].val / 256 * 256; omega
  have hb1d : b[1].val = b10 + b11 * 256 := by change b[1].val = b[1].val % 256 + b[1].val / 256 * 256; omega
  have hb2d : b[2].val = b20 + b21 * 256 := by change b[2].val = b[2].val % 256 + b[2].val / 256 * 256; omega
  have hb3d : b[3].val = b30 + b31 * 256 := by change b[3].val = b[3].val % 256 + b[3].val / 256 * 256; omega
  have hc0d : cc[0].val = c00 + c01 * 256 := by change cc[0].val = cc[0].val % 256 + cc[0].val / 256 * 256; omega
  have hc1d : cc[1].val = c10 + c11 * 256 := by change cc[1].val = cc[1].val % 256 + cc[1].val / 256 * 256; omega
  have hc2d : cc[2].val = c20 + c21 * 256 := by change cc[2].val = cc[2].val % 256 + cc[2].val / 256 * 256; omega
  have hc3d : cc[3].val = c30 + c31 * 256 := by change cc[3].val = cc[3].val % 256 + cc[3].val / 256 * 256; omega
  rw [hb0d, hb1d, hb2d, hb3d, hc0d, hc1d, hc2d, hc3d]
  obtain ⟨bb00, bb01⟩ := hb_b0
  obtain ⟨bb10, bb11⟩ := hb_b1
  obtain ⟨bb20, bb21⟩ := hb_b2
  obtain ⟨bb30, bb31⟩ := hb_b3
  obtain ⟨cc00, cc01⟩ := hb_c0
  obtain ⟨cc10, cc11⟩ := hb_c1
  obtain ⟨cc20, cc21⟩ := hb_c2
  obtain ⟨cc30, cc31⟩ := hb_c3
  rw [Nat.lift_lt 64 (by omega) (by omega)] at bb00 bb01 bb10 bb11 bb20 bb21 bb30 bb31
  rw [Nat.lift_lt 64 (by omega) (by omega)] at cc00 cc01 cc10 cc11 cc20 cc21 cc30 cc31
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_xor]
  bv_decide

end BitwiseU16Operation
