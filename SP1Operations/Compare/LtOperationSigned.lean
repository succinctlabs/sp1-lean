import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Compare.LtOperationSigned.Constraints

namespace LtOperationSigned


-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false in
lemma allHold_constraints_iff
  {b : Word (Fin KB)}
  {d : Word (Fin KB)}
  {cols : LtOperationSigned (Fin KB)}
  {is_signed : Fin KB} :
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
  := by simp [constraints, sub_eq_zero]

/-- Polymorphic companion of `allHold_constraints_iff` over `ZMod p`. -/
lemma allHold_constraints_iff_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b : Word (ZMod p)}
  {d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  {is_signed : ZMod p} :
  List.Forall SP1Constraint.toProp_poly (constraints b d cols is_signed 1) ↔
    List.Forall SP1Constraint.toProp_poly (U16MSBOperation.constraints b[3] cols.b_msb is_signed) ∧
    List.Forall SP1Constraint.toProp_poly (U16MSBOperation.constraints d[3] cols.c_msb is_signed) ∧
    List.Forall SP1Constraint.toProp_poly (LtOperationUnsigned.constraints
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
  := by simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly]

-- spec proof with 32-bit comparison lemmas
lemma spec.unsigned
  {b : Word (Fin KB)}
  {d : Word (Fin KB)}
  {cols : LtOperationSigned (Fin KB)}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 0 1) →
    BitVec.ofNat 64 cols.result.u16_compare_operation.bit = execute_RTYPE_pure_w b d .SLTU
  := by
    intro cstrs
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨h_b_msb, h_c_msb, h_lt, h_is_signed_bool, h_is_signed_b_msb, h_is_signed_c_msb⟩
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    apply LtOperationUnsigned.spec at h_lt
    · simp_all [execute_RTYPE_pure_w, Word.toNat]
    · apply Word.isU64_of_cases <;> simp_all
    · apply Word.isU64_of_cases <;> simp_all

/-- Polymorphic companion of `spec.unsigned` (natural-form, not BitVec).
With `is_signed = 0`, the msb constraints force `cols.{b,c}_msb.msb = 0`,
so the `LtOperationUnsigned` sub-proof on the same b, d applies. -/
lemma spec.unsigned_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {b : Word (ZMod p)}
  {d : Word (ZMod p)}
  {cols : LtOperationSigned (ZMod p)}
  (h_b_isU64 : Word.isU64_poly b)
  (h_d_isU64 : Word.isU64_poly d) :
  List.Forall SP1Constraint.toProp_poly (constraints b d cols 0 1) →
    cols.result.u16_compare_operation.bit =
      if b.toNat_poly < d.toNat_poly then (1 : ZMod p) else (0 : ZMod p)
  := by
    intro cstrs
    rw [allHold_constraints_iff_poly] at cstrs
    rcases cstrs with ⟨h_b_msb, h_c_msb, h_lt, h_is_signed_bool, h_is_signed_b_msb, h_is_signed_c_msb⟩
    apply Word.lt_cases_of_isU64_poly at h_b_isU64
    apply Word.lt_cases_of_isU64_poly at h_d_isU64
    apply LtOperationUnsigned.spec.nat_poly at h_lt
    · simp_all [Word.toNat_poly]
    · apply Word.isU64_of_cases_poly <;> simp_all
    · apply Word.isU64_of_cases_poly <;> simp_all

-- spec proof with 32-bit comparison lemmas
lemma spec.signed
  {b : Word (Fin KB)}
  {d : Word (Fin KB)}
  {cols : LtOperationSigned (Fin KB)}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols 1 1) →
    BitVec.ofNat 64 cols.result.u16_compare_operation.bit = execute_RTYPE_pure_w b d .SLT
  := by
    intro cstrs
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨ h_b_msb, h_c_msb, h_lt, h_is_signed_bool, h_is_signed_b_msb, h_is_signed_c_msb⟩
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_b_isU64) at h_b_msb
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_d_isU64) at h_c_msb
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    simp at *
    have h_sb_isU64 : Word.isU64 #v[b[0], b[1], b[2], b[3] + 32768 - 65536 * cols.b_msb.msb] := by
      rw [h_b_msb]; clear h_lt h_b_msb h_c_msb
      by_cases b.isNegative <;> unfold Word.isNegative at *
      · apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> grind
      · apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> grind
    have h_sd_isU64 : Word.isU64 #v[d[0], d[1], d[2], d[3] + 32768 - 65536 * cols.c_msb.msb] := by
      rw [h_c_msb]; clear h_lt h_b_msb h_c_msb
      by_cases d.isNegative <;> unfold Word.isNegative at *
      · apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> grind
      · apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> grind
    apply LtOperationUnsigned.spec (h_b_isU64 := h_sb_isU64) (h_d_isU64 := h_sd_isU64) at h_lt
    simp [Word.toNat] at h_lt
    rw [h_lt, h_b_msb, h_c_msb]
    simp only [Word.toInt, Word.toNat_def, Word.isNegative]
    split_ifs <;> simp <;> omega

def spec.branch.def
  (b : (Word (Fin KB)))
  (c : (Word (Fin KB)))
  (cols : LtOperationSigned (Fin KB))
  (is_signed : (Fin KB))
  : Prop :=
  let bv := b.toBitVec64
  let cv := c.toBitVec64
  (is_signed = 0 →
    (bv = cv
      ↔ (cols.result.u16_flags[0] = 0
        ∧ cols.result.u16_flags[1] = 0
        ∧ cols.result.u16_flags[2] = 0
        ∧ cols.result.u16_flags[3] = 0))
    ∧ (¬ bv = cv
        ↔ cols.result.u16_flags[0]
          + cols.result.u16_flags[1]
          + cols.result.u16_flags[2]
          + cols.result.u16_flags[3] = 1)
    ∧ if BitVec.ult bv cv
      then (cols.result.u16_compare_operation.bit = 1)
      else (cols.result.u16_compare_operation.bit = 0))
  ∧ (is_signed = 1 →
      (bv = cv
        ↔ (cols.result.u16_flags[0] = 0
          ∧ cols.result.u16_flags[1] = 0
          ∧ cols.result.u16_flags[2] = 0
          ∧ cols.result.u16_flags[3] = 0))
      ∧ (¬ bv = cv
          ↔ cols.result.u16_flags[0]
            + cols.result.u16_flags[1]
            + cols.result.u16_flags[2]
            + cols.result.u16_flags[3] = 1)
      ∧ if BitVec.slt bv cv
        then (cols.result.u16_compare_operation.bit = 1)
        else (cols.result.u16_compare_operation.bit = 0))

set_option maxHeartbeats 10000000 in
-- branch-form spec over Word (Fin KB)
set_option linter.style.multiGoal false in
lemma spec.branch
  {b : (Word (Fin KB))}
  {d : (Word (Fin KB))}
  {cols : LtOperationSigned (Fin KB)}
  {is_signed : (Fin KB)}
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_signed 1) →
    spec.branch.def b d cols is_signed
    := by
  intro cstrs; have cstrs := cstrs
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 h_b_isU64
  obtain ⟨d0_16, d1_16, d2_16, d3_16⟩ := Word.lt_cases_of_isU64 h_d_isU64
  have : b.toBitVec64 = d.toBitVec64 ↔ b[0] = d[0] ∧ b[1] = d[1] ∧ b[2] = d[2] ∧ b[3] = d[3] := by
    simp_all [← BitVec.toNat_inj, Word.toBitVec64, Word.toNat]
    omega
  rw [allHold_constraints_iff] at cstrs
  rcases cstrs with ⟨h_b_msb, h_d_msb, h_lt, ⟨h_is_signed_bool, h_is_signed_b_msb, h_is_signed_d_msb⟩⟩
  rw [LtOperationUnsigned.allHold_constraints_iff] at h_lt
  rcases h_lt with ⟨h_comp_limbs, ⟨h_is_real_bool, h_flag_0_bool, h_flag_1_bool, h_flag_2_bool, h_flag_3_bool, lt_00, lt_01, lt_02, lt_03, lt_04, lt_05, lt_06, lt_07⟩⟩
  simp [U16CompareOperation.constraints] at h_comp_limbs
  rcases h_comp_limbs with ⟨cmp_00, cmp_01⟩
  simp_all
  constructor <;> intro sgn <;> (repeat rw [this]) <;> clear this <;> simp_all
  · have spec.unsigned := spec.unsigned h_b_isU64 h_d_isU64 cstrs
    rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
    rcases h_flag_2_bool <;> rcases h_flag_3_bool <;>
    simp_all <;> split_ands
    symm at lt_05 lt_06; simp_all
    on_goal 2 => intros; intro eqc; simp_all
    on_goal 3 => intros; intro eqc; simp_all
    on_goal 4 => intros; intro eqc; simp_all
    on_goal 5 => intro eqc; simp_all
    all_goals {
      split_ifs at spec.unsigned with cond
      all_goals {
        iterate 2 rw [← Word.toBitVec64_toNat (by assumption)] at cond
        rw [← BitVec.ult_iff_toNat_lt (w := 64)] at cond
        simp [← BitVec.toNat_inj] at spec.unsigned
        simp_all; omega
      }
    }
  · have spec.signed := spec.signed h_b_isU64 h_d_isU64 cstrs
    rw [U16MSBOperation.allHold_constraints_iff] at h_b_msb
    rw [U16MSBOperation.allHold_constraints_iff] at h_d_msb
    rcases h_b_msb with ⟨_, b_msb_b, hb3⟩; rcases h_d_msb with ⟨_, b_msb_d, hd3⟩
    simp only [show (1 : Fin KB) ≠ 0 by decide, not_false_iff, forall_true_left] at hb3 hd3
    rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
    rcases h_flag_2_bool <;> rcases h_flag_3_bool <;>
    symm at lt_05 lt_06 <;>
    simp_all <;> split_ands <;>
    rcases b_msb_b with bm | bm <;> rcases b_msb_d with dm | dm <;>
    simp_all <;>
    (first
      | (split_ifs at spec.signed with cond <;>
          (iterate 2 rw [← Word.toBitVec64_toInt (by assumption)] at cond) <;>
          rw [← BitVec.slt_iff_toInt_lt (w := 64)] at cond <;>
          simp [← BitVec.toNat_inj] at spec.signed <;>
          simp_all <;> omega)
      | (intros; rename_i eqc; exfalso;
          rw [eqc] at lt_07;
          simp only [sub_self, mul_zero] at lt_07;
          exact absurd lt_07 (by decide))
      | (intros; subst_vars; grind))

end LtOperationSigned
