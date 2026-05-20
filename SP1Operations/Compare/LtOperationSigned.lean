import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Compare.LtOperationSigned.Constraints

namespace LtOperationSigned

set_option linter.style.setOption false
set_option linter.style.longLine false

lemma allHold_constraints_iff
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b : Word (ZMod p)}
  {d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  {is_signed : ZMod p} :
  List.Forall SP1Constraint.toProp (constraints b d cols is_signed 1) ↔
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints b[3] cols.b_msb is_signed) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints d[3] cols.c_msb is_signed) ∧
    List.Forall SP1Constraint.toProp (LtOperationUnsigned.constraints
      #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * cols.b_msb.msb]
      #v[d[0], d[1], d[2], d[3] + is_signed * 32768 - 65536 * cols.c_msb.msb]
      { u16_compare_operation := cols.result.u16_compare_operation,
        u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1], cols.result.u16_flags[2], cols.result.u16_flags[3]],
        not_eq_inv := cols.result.not_eq_inv,
        comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] }
      1) ∧
    (is_signed = 0 ∨ is_signed = 1) ∧
    (is_signed = 1 ∨ cols.b_msb.msb = 0) ∧
    (is_signed = 1 ∨ cols.c_msb.msb = 0)
  := by simp [constraints, sub_eq_zero, SP1Constraint.toProp]

/-- Natural-form unsigned spec: with `is_signed = 0`, the msb constraints
force `cols.{b,c}_msb.msb = 0`, so the `LtOperationUnsigned` sub-proof on
the same b, d applies. -/
lemma spec.unsigned
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b : Word (ZMod p)}
  {d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 0 1) →
    cols.result.u16_compare_operation.bit =
      if b.toNat < d.toNat then (1 : ZMod p) else (0 : ZMod p)
  := by
    intro cstrs
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨h_b_msb, h_c_msb, h_lt, h_is_signed_bool, h_is_signed_b_msb, h_is_signed_c_msb⟩
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    apply LtOperationUnsigned.spec.nat at h_lt
    · simp_all [Word.toNat]
    · apply Word.isU64_of_cases <;> simp_all
    · apply Word.isU64_of_cases <;> simp_all

set_option maxHeartbeats 4000000 in
-- Heartbeats elevated for the structured `.val`-arithmetic case-split
-- on `cols.{b,c}_msb.msb` plus the `LtOperationUnsigned.spec.nat`
-- chain through the shifted vectors.
/-- Natural-form signed spec. The shifted limb 3
(`b[3] + 32768 - 65536 * msb`) converts a signed comparison into an
unsigned one: in both `msb` cases the resulting `Word.toNat` equals
`b.toInt + 32768 * 2^48`, so `shifted_b < shifted_d` iff
`b.toInt < d.toInt`. -/
lemma spec.signed
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1 1) →
    cols.result.u16_compare_operation.bit =
      if b.toInt < d.toInt then (1 : ZMod p) else (0 : ZMod p)
  := by
    intro cstrs
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have hp_lt := Fact.out (p := 2 ^ 17 < p)
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨h_b_msb, h_c_msb, h_lt, _⟩
    have h_b_msb_eq := U16MSBOperation.spec.U64 h_b_isU64 h_b_msb
    have h_c_msb_eq := U16MSBOperation.spec.U64 h_d_isU64 h_c_msb
    obtain ⟨h_b0, h_b1, h_b2, h_b3⟩ := Word.lt_cases_of_isU64 h_b_isU64
    obtain ⟨h_d0, h_d1, h_d2, h_d3⟩ := Word.lt_cases_of_isU64 h_d_isU64
    simp only [one_mul] at h_lt
    have h32768_val : (32768 : ZMod p).val = 32768 := by
      have : 131072 < p := by have := hp_lt; omega
      exact ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by omega)
    have h65536_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
    have h_shifted_lt :
      ∀ (b3 : ZMod p) (_hb3 : b3.val < 65536) (msb : ZMod p)
        (_hmsb_eq : msb = if b3.val ≥ 32768 then (1 : ZMod p) else 0),
        (b3 + 32768 - 65536 * msb).val < 65536 := by
      intro b3 hb3 msb hmsb_eq
      by_cases hneg : b3.val ≥ 32768
      · rw [hmsb_eq, if_pos hneg, mul_one]
        have hadd : (b3 + 32768).val = b3.val + 32768 := by
          rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
        rw [val_sub_cases]
        split_ifs with h
        · rw [hadd, h65536_val]; omega
        · rw [hadd, h65536_val] at h; omega
      · rw [hmsb_eq, if_neg hneg, mul_zero, sub_zero]
        rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]; omega
    have h_shifted_val :
      ∀ (b3 : ZMod p) (_hb3 : b3.val < 65536) (msb : ZMod p)
        (_hmsb_eq : msb = if b3.val ≥ 32768 then (1 : ZMod p) else 0),
        ((b3 + 32768 - 65536 * msb).val : ℤ) =
          (b3.val : ℤ) + 32768 - (if b3.val ≥ 32768 then 65536 else 0) := by
      intro b3 hb3 msb hmsb_eq
      by_cases hneg : b3.val ≥ 32768
      · rw [hmsb_eq, if_pos hneg, mul_one, if_pos hneg]
        have hadd : (b3 + 32768).val = b3.val + 32768 := by
          rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
        rw [val_sub_cases]
        split_ifs with h
        · rw [hadd, h65536_val]; push_cast; omega
        · rw [hadd, h65536_val] at h; omega
      · rw [hmsb_eq, if_neg hneg, mul_zero, sub_zero, if_neg hneg]
        rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
        push_cast; omega
    have h_sb_isU64 : Word.isU64
        #v[b[0], b[1], b[2], b[3] + 32768 - 65536 * cols.b_msb.msb] := by
      apply Word.isU64_of_cases <;> simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      · exact h_b0
      · exact h_b1
      · exact h_b2
      · exact h_shifted_lt b[3] h_b3 cols.b_msb.msb
          (by simpa [Word.isNegative] using h_b_msb_eq)
    have h_sd_isU64 : Word.isU64
        #v[d[0], d[1], d[2], d[3] + 32768 - 65536 * cols.c_msb.msb] := by
      apply Word.isU64_of_cases <;> simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      · exact h_d0
      · exact h_d1
      · exact h_d2
      · exact h_shifted_lt d[3] h_d3 cols.c_msb.msb
          (by simpa [Word.isNegative] using h_c_msb_eq)
    have h_lt_nat := LtOperationUnsigned.spec.nat h_sb_isU64 h_sd_isU64 h_lt
    have h_b_eq := h_shifted_val b[3] h_b3 cols.b_msb.msb
      (by simpa [Word.isNegative] using h_b_msb_eq)
    have h_d_eq := h_shifted_val d[3] h_d3 cols.c_msb.msb
      (by simpa [Word.isNegative] using h_c_msb_eq)
    rw [h_lt_nat]
    congr 1
    apply propext
    simp only [Word.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    unfold Word.toInt Word.toNat
    constructor <;> intro h
    · have h' : ((b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
                  + (b[3] + 32768 - 65536 * cols.b_msb.msb).val * 2 ^ 48 : ℕ) : ℤ) <
                 ((d[0].val + d[1].val * 2 ^ 16 + d[2].val * 2 ^ 32
                  + (d[3] + 32768 - 65536 * cols.c_msb.msb).val * 2 ^ 48 : ℕ) : ℤ) := by
        exact_mod_cast h
      push_cast at h'
      rw [h_b_eq, h_d_eq] at h'
      simp only [Word.isNegative]
      split_ifs <;> push_cast <;> omega
    · simp only [Word.isNegative] at h
      have h' : ((b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
                  + (b[3] + 32768 - 65536 * cols.b_msb.msb).val * 2 ^ 48 : ℕ) : ℤ) <
                 ((d[0].val + d[1].val * 2 ^ 16 + d[2].val * 2 ^ 32
                  + (d[3] + 32768 - 65536 * cols.c_msb.msb).val * 2 ^ 48 : ℕ) : ℤ) := by
        push_cast
        rw [h_b_eq, h_d_eq]
        split_ifs at h <;> push_cast at h <;> omega
      exact_mod_cast h'

/-- Natural-form branch spec: uses `Word` equality directly and
`toNat`/`toInt` ordering. -/
def spec.branch.def {p : ℕ} [NeZero p]
    (b : (Word (ZMod p)))
    (c : (Word (ZMod p)))
    (cols : LtOperationSigned (ZMod p))
    (is_signed : (ZMod p))
    : Prop :=
  (is_signed = 0 →
    (b = c
      ↔ (cols.result.u16_flags[0] = 0
        ∧ cols.result.u16_flags[1] = 0
        ∧ cols.result.u16_flags[2] = 0
        ∧ cols.result.u16_flags[3] = 0))
    ∧ (¬ b = c
        ↔ cols.result.u16_flags[0]
          + cols.result.u16_flags[1]
          + cols.result.u16_flags[2]
          + cols.result.u16_flags[3] = 1)
    ∧ if b.toNat < c.toNat
      then (cols.result.u16_compare_operation.bit = 1)
      else (cols.result.u16_compare_operation.bit = 0))
  ∧ (is_signed = 1 →
      (b = c
        ↔ (cols.result.u16_flags[0] = 0
          ∧ cols.result.u16_flags[1] = 0
          ∧ cols.result.u16_flags[2] = 0
          ∧ cols.result.u16_flags[3] = 0))
      ∧ (¬ b = c
          ↔ cols.result.u16_flags[0]
            + cols.result.u16_flags[1]
            + cols.result.u16_flags[2]
            + cols.result.u16_flags[3] = 1)
      ∧ if b.toInt < c.toInt
        then (cols.result.u16_compare_operation.bit = 1)
        else (cols.result.u16_compare_operation.bit = 0))

set_option maxHeartbeats 16000000 in
-- Heartbeats elevated for the 16-way flag-bool case-split discharging
-- impossible flag-sum cases via `linear_combination + val_k_ne_zero`.
private lemma branch_helper_eq_iff_unsigned
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)} :
  List.Forall SP1Constraint.toProp (constraints b d cols 0 1) →
    (b = d ↔ cols.result.u16_flags[0] = 0 ∧ cols.result.u16_flags[1] = 0
            ∧ cols.result.u16_flags[2] = 0 ∧ cols.result.u16_flags[3] = 0)
    := by
  intro cstrs
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h_zero_ne_one : (0 : ZMod p) ≠ 1 := zero_ne_one
  rw [allHold_constraints_iff] at cstrs
  rcases cstrs with ⟨_, _, h_lt, _, h_msb_b_eq, h_msb_d_eq⟩
  have hmsb_b : cols.b_msb.msb = 0 := h_msb_b_eq.resolve_left h_zero_ne_one
  have hmsb_d : cols.c_msb.msb = 0 := h_msb_d_eq.resolve_left h_zero_ne_one
  rw [hmsb_b, hmsb_d] at h_lt
  simp only [mul_zero, sub_zero, zero_mul, add_zero] at h_lt
  rw [LtOperationUnsigned.allHold_constraints_iff] at h_lt
  rcases h_lt with ⟨_, _, h_f0, h_f1, h_f2, h_f3,
     _, lt_d3, lt_d2, lt_d1, lt_d0, h_cmp_b, h_cmp_d, h_neq⟩
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h_f0 h_f1 h_f2 h_f3 lt_d3 lt_d2 lt_d1 lt_d0
                                  h_cmp_b h_cmp_d h_neq
  have h_eq_iff : b = d ↔ b[0] = d[0] ∧ b[1] = d[1] ∧ b[2] = d[2] ∧ b[3] = d[3] := by
    rw [← Word.eq_pointwise]
  rw [h_eq_iff]
  constructor
  · intro ⟨h0, h1, h2, h3⟩
    have h_cmp_eq : cols.result.comparison_limbs[0] = cols.result.comparison_limbs[1] := by
      rw [← h_cmp_b, ← h_cmp_d, h0, h1, h2, h3]
    rcases h_neq with h_neq | h_neq
    · rcases h_f0 with hf0 | hf0 <;> rcases h_f1 with hf1 | hf1 <;>
        rcases h_f2 with hf2 | hf2 <;> rcases h_f3 with hf3 | hf3
      all_goals first
        | exact ⟨hf0, hf1, hf2, hf3⟩
        | (exfalso
           rw [hf0, hf1, hf2, hf3] at h_neq
           first
             | (have h2 : (2 : ZMod p) = 0 := by linear_combination -h_neq
                exact val_2_ne_zero h2)
             | (have h3 : (3 : ZMod p) = 0 := by linear_combination -h_neq
                exact val_3_ne_zero h3)
             | (have h4 : (4 : ZMod p) = 0 := by linear_combination -h_neq
                exact val_4_ne_zero h4)
             | (have h1 : (1 : ZMod p) = 0 := by linear_combination -h_neq
                exact h_one_ne_zero h1))
    · rw [h_cmp_eq, sub_self, mul_zero] at h_neq
      exact absurd h_neq.symm h_one_ne_zero
  · intro ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases lt_d0 with h | h
      · exfalso; rw [h0, h1, h2, h3] at h; simp at h
      · exact h
    · rcases lt_d1 with h | h
      · exfalso; rw [h1, h2, h3] at h; simp at h
      · exact h
    · rcases lt_d2 with h | h
      · exfalso; rw [h2, h3] at h; simp at h
      · exact h
    · rcases lt_d3 with h | h
      · exfalso; rw [h3] at h; exact h_one_ne_zero h
      · exact h

set_option maxHeartbeats 32000000 in
-- Heartbeats elevated for the 16-way flag-bool case-split + 4-way
-- (b.isNegative, d.isNegative) sub-case-split for limb 3
-- (using `val_sub_cases` to discharge cross-msb cases).
private lemma branch_helper_eq_iff_signed
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1 1) →
    (b = d ↔ cols.result.u16_flags[0] = 0 ∧ cols.result.u16_flags[1] = 0
            ∧ cols.result.u16_flags[2] = 0 ∧ cols.result.u16_flags[3] = 0)
    := by
  intro cstrs
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt := Fact.out (p := 2 ^ 17 < p)
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
  obtain ⟨_, _, _, h_b3_lt⟩ := Word.lt_cases_of_isU64 h_b_isU64
  obtain ⟨_, _, _, h_d3_lt⟩ := Word.lt_cases_of_isU64 h_d_isU64
  rw [allHold_constraints_iff] at cstrs
  rcases cstrs with ⟨h_b_msb, h_d_msb, h_lt, _⟩
  have h_b_msb_eq := U16MSBOperation.spec.U64 h_b_isU64 h_b_msb
  have h_c_msb_eq := U16MSBOperation.spec.U64 h_d_isU64 h_d_msb
  have h32768_val : (32768 : ZMod p).val = 32768 := by
    have : 131072 < p := by omega
    exact ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by omega)
  have h65536_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  rw [LtOperationUnsigned.allHold_constraints_iff] at h_lt
  rcases h_lt with ⟨_, _, h_f0, h_f1, h_f2, h_f3,
     _, lt_d3, lt_d2, lt_d1, lt_d0, h_cmp_b, h_cmp_d, h_neq⟩
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, one_mul] at h_f0 h_f1 h_f2 h_f3 lt_d3 lt_d2 lt_d1 lt_d0
                                          h_cmp_b h_cmp_d h_neq
  have h_eq_iff : b = d ↔ b[0] = d[0] ∧ b[1] = d[1] ∧ b[2] = d[2] ∧ b[3] = d[3] := by
    rw [← Word.eq_pointwise]
  rw [h_eq_iff]
  constructor
  · intro ⟨h0, h1, h2, h3⟩
    have h_msb_eq : cols.b_msb.msb = cols.c_msb.msb := by
      rw [h_b_msb_eq, h_c_msb_eq]
      simp [Word.isNegative, h3]
    have h_cmp_eq : cols.result.comparison_limbs[0] = cols.result.comparison_limbs[1] := by
      rw [← h_cmp_b, ← h_cmp_d, h0, h1, h2, h3, h_msb_eq]
    rcases h_neq with h_neq | h_neq
    · rcases h_f0 with hf0 | hf0 <;> rcases h_f1 with hf1 | hf1 <;>
        rcases h_f2 with hf2 | hf2 <;> rcases h_f3 with hf3 | hf3
      all_goals first
        | exact ⟨hf0, hf1, hf2, hf3⟩
        | (exfalso
           rw [hf0, hf1, hf2, hf3] at h_neq
           first
             | (have h2 : (2 : ZMod p) = 0 := by linear_combination -h_neq
                exact val_2_ne_zero h2)
             | (have h3 : (3 : ZMod p) = 0 := by linear_combination -h_neq
                exact val_3_ne_zero h3)
             | (have h4 : (4 : ZMod p) = 0 := by linear_combination -h_neq
                exact val_4_ne_zero h4)
             | (have h1 : (1 : ZMod p) = 0 := by linear_combination -h_neq
                exact h_one_ne_zero h1))
    · rw [h_cmp_eq, sub_self, mul_zero] at h_neq
      exact absurd h_neq.symm h_one_ne_zero
  · intro ⟨h0, h1, h2, h3⟩
    have hb0eqd0 : b[0] = d[0] := by
      rcases lt_d0 with h | h
      · exfalso; rw [h0, h1, h2, h3] at h; simp at h
      · exact h
    have hb1eqd1 : b[1] = d[1] := by
      rcases lt_d1 with h | h
      · exfalso; rw [h1, h2, h3] at h; simp at h
      · exact h
    have hb2eqd2 : b[2] = d[2] := by
      rcases lt_d2 with h | h
      · exfalso; rw [h2, h3] at h; simp at h
      · exact h
    have h_shifted_eq : b[3] + 32768 - 65536 * cols.b_msb.msb
                       = d[3] + 32768 - 65536 * cols.c_msb.msb := by
      rcases lt_d3 with h | h
      · exfalso; rw [h3] at h; exact h_one_ne_zero h
      · exact h
    have hb3eqd3 : b[3] = d[3] := by
      rw [h_b_msb_eq, h_c_msb_eq] at h_shifted_eq
      simp only [Word.isNegative] at h_shifted_eq
      by_cases hbn : b[3].val ≥ 32768 <;> by_cases hdn : d[3].val ≥ 32768
      all_goals simp [hbn, hdn] at h_shifted_eq
      · linear_combination h_shifted_eq
      · exfalso
        have h_subval : (b[3] + 32768 - 65536).val = b[3].val + 32768 - 65536 := by
          have hadd : (b[3] + 32768).val = b[3].val + 32768 := by
            rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
          rw [val_sub_cases, hadd, h65536_val, if_pos (by omega)]
        have h_dv : (d[3] + 32768).val = d[3].val + 32768 := by
          rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
        have h_eq_val : (b[3] + 32768 - 65536).val = (d[3] + 32768).val :=
          congrArg ZMod.val h_shifted_eq
        rw [h_subval, h_dv] at h_eq_val
        omega
      · exfalso
        have h_subval : (d[3] + 32768 - 65536).val = d[3].val + 32768 - 65536 := by
          have hadd : (d[3] + 32768).val = d[3].val + 32768 := by
            rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
          rw [val_sub_cases, hadd, h65536_val, if_pos (by omega)]
        have h_bv : (b[3] + 32768).val = b[3].val + 32768 := by
          rw [ZMod.val_add_of_lt (by rw [h32768_val]; omega), h32768_val]
        have h_eq_val : (b[3] + 32768).val = (d[3] + 32768 - 65536).val :=
          congrArg ZMod.val h_shifted_eq
        rw [h_subval, h_bv] at h_eq_val
        omega
      · linear_combination h_shifted_eq
    exact ⟨hb0eqd0, hb1eqd1, hb2eqd2, hb3eqd3⟩

set_option maxHeartbeats 16000000 in
-- Heartbeats elevated for the inline neq-iff proof
-- (16-way flag-bool case-split via h_sum) plus the spec.{unsigned,signed}
-- bridge to the if-then-else conclusion.
/-- Branch-form spec. Both `is_signed = 0` and `is_signed = 1` branches
reuse the same combinatorial argument for the equality + sum iffs
(extracted into `branch_helper_eq_iff_unsigned` and
`branch_helper_eq_iff_signed`); the if-then-else conclusion comes
from `spec.unsigned` / `spec.signed`. -/
lemma spec.branch
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  {is_signed : ZMod p}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_signed 1) →
    spec.branch.def b d cols is_signed
    := by
  intro cstrs
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
  refine ⟨?_, ?_⟩
  · intro h_sgn0
    subst h_sgn0
    have h_eq := branch_helper_eq_iff_unsigned cstrs
    have h_cstrs := cstrs
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨_, _, h_lt, _⟩
    rw [LtOperationUnsigned.allHold_constraints_iff] at h_lt
    rcases h_lt with ⟨_, _, h_f0, h_f1, h_f2, h_f3, h_sum, _⟩
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h_f0 h_f1 h_f2 h_f3 h_sum
    have h_neq : ¬ b = d ↔ cols.result.u16_flags[0] + cols.result.u16_flags[1]
        + cols.result.u16_flags[2] + cols.result.u16_flags[3] = 1 := by
      constructor
      · intro h_ne
        have h_not_all_zero : ¬ (cols.result.u16_flags[0] = 0
            ∧ cols.result.u16_flags[1] = 0 ∧ cols.result.u16_flags[2] = 0
            ∧ cols.result.u16_flags[3] = 0) := fun h => h_ne (h_eq.mpr h)
        rcases h_sum with h_sum | h_sum
        · exfalso
          apply h_not_all_zero
          rcases h_f0 with hf0 | hf0 <;> rcases h_f1 with hf1 | hf1 <;>
            rcases h_f2 with hf2 | hf2 <;> rcases h_f3 with hf3 | hf3
          all_goals first
            | exact ⟨hf0, hf1, hf2, hf3⟩
            | (exfalso
               rw [hf0, hf1, hf2, hf3] at h_sum
               first
                 | (have h2 : (2 : ZMod p) = 0 := by linear_combination h_sum
                    exact val_2_ne_zero h2)
                 | (have h3 : (3 : ZMod p) = 0 := by linear_combination h_sum
                    exact val_3_ne_zero h3)
                 | (have h4 : (4 : ZMod p) = 0 := by linear_combination h_sum
                    exact val_4_ne_zero h4)
                 | (have h1 : (1 : ZMod p) = 0 := by linear_combination h_sum
                    exact h_one_ne_zero h1))
        · exact h_sum
      · intro h_sum_eq h_eq_bd
        have ⟨h0, h1, h2, h3⟩ := h_eq.mp h_eq_bd
        rw [h0, h1, h2, h3] at h_sum_eq
        simp at h_sum_eq
    refine ⟨h_eq, h_neq, ?_⟩
    have h_unsigned := spec.unsigned h_b_isU64 h_d_isU64 h_cstrs
    split_ifs with hcond <;> simp [hcond] at h_unsigned <;> exact h_unsigned
  · intro h_sgn1
    subst h_sgn1
    have h_eq := branch_helper_eq_iff_signed h_b_isU64 h_d_isU64 cstrs
    have h_cstrs := cstrs
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨_, _, h_lt, _⟩
    rw [LtOperationUnsigned.allHold_constraints_iff] at h_lt
    rcases h_lt with ⟨_, _, h_f0, h_f1, h_f2, h_f3, h_sum, _⟩
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] at h_f0 h_f1 h_f2 h_f3 h_sum
    have h_neq : ¬ b = d ↔ cols.result.u16_flags[0] + cols.result.u16_flags[1]
        + cols.result.u16_flags[2] + cols.result.u16_flags[3] = 1 := by
      constructor
      · intro h_ne
        have h_not_all_zero : ¬ (cols.result.u16_flags[0] = 0
            ∧ cols.result.u16_flags[1] = 0 ∧ cols.result.u16_flags[2] = 0
            ∧ cols.result.u16_flags[3] = 0) := fun h => h_ne (h_eq.mpr h)
        rcases h_sum with h_sum | h_sum
        · exfalso
          apply h_not_all_zero
          rcases h_f0 with hf0 | hf0 <;> rcases h_f1 with hf1 | hf1 <;>
            rcases h_f2 with hf2 | hf2 <;> rcases h_f3 with hf3 | hf3
          all_goals first
            | exact ⟨hf0, hf1, hf2, hf3⟩
            | (exfalso
               rw [hf0, hf1, hf2, hf3] at h_sum
               first
                 | (have h2 : (2 : ZMod p) = 0 := by linear_combination h_sum
                    exact val_2_ne_zero h2)
                 | (have h3 : (3 : ZMod p) = 0 := by linear_combination h_sum
                    exact val_3_ne_zero h3)
                 | (have h4 : (4 : ZMod p) = 0 := by linear_combination h_sum
                    exact val_4_ne_zero h4)
                 | (have h1 : (1 : ZMod p) = 0 := by linear_combination h_sum
                    exact h_one_ne_zero h1))
        · exact h_sum
      · intro h_sum_eq h_eq_bd
        have ⟨h0, h1, h2, h3⟩ := h_eq.mp h_eq_bd
        rw [h0, h1, h2, h3] at h_sum_eq
        simp at h_sum_eq
    refine ⟨h_eq, h_neq, ?_⟩
    have h_signed := spec.signed h_b_isU64 h_d_isU64 h_cstrs
    split_ifs with hcond <;> simp [hcond] at h_signed <;> exact h_signed

end LtOperationSigned
