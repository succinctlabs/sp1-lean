import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Compare.LtOperationSigned.Constraints

namespace LtOperationSigned

lemma allHold_constraints_iff
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationSigned)
  (is_signed : Fin BB)
  (is_real : Fin BB) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_signed is_real) ↔
    (U16MSBOperation.constraints b[3] cols.b_msb is_signed).allHold ∧
    (U16MSBOperation.constraints d[3] cols.c_msb is_signed).allHold ∧
    (LtOperationUnsigned.constraints
      #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * cols.b_msb.msb]
      #v[d[0], d[1], d[2], d[3] + is_signed * 32768 - 65536 * cols.c_msb.msb]
      { u16_compare_operation := cols.result.u16_compare_operation,
        u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1], cols.result.u16_flags[2], cols.result.u16_flags[3]],
        not_eq_inv := cols.result.not_eq_inv,
        comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] }
      is_real).allHold ∧
    ((is_signed = 0 ∨ is_signed = 1) ∧
    (is_real = 0 ∨ is_real = 1) ∧
    (is_real = 1 ∨ is_signed = 0) ∧
    (is_signed = 1 ∨ cols.b_msb.msb = 0) ∧
    (is_signed = 1 ∨ cols.c_msb.msb = 0))
  := by
    simp [and_assoc, constraints, sub_eq_zero, Fin.lt_iff_val_lt_val]

set_option maxHeartbeats 1000000 in
lemma spec.unsigned
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationSigned)
  (is_signed : Fin BB)
  (is_real : Fin BB)
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_signed is_real) →
    (is_real ≠ 0 → is_signed = 0 → BitVec.ofNat 64 cols.result.u16_compare_operation.bit = execute_RTYPE_pure_w b d .SLTU)
  := by
    intro cstrs h_is_real h_is_signed
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨ h_b_msb, h_c_msb, h_lt, ⟨ h_is_signed_bool, h_is_real_bool, h_is_real_is_signed, h_is_signed_b_msb, h_is_signed_c_msb ⟩ ⟩
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_b_isU64) at h_b_msb
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_d_isU64) at h_c_msb
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    apply LtOperationUnsigned.spec at h_lt
    . simp_all [execute_RTYPE_pure_w, Word.toNat]
    . apply Word.isU64_of_cases <;> simp_all
    . apply Word.isU64_of_cases <;> simp_all

set_option maxHeartbeats 1000000 in
lemma spec.signed
  (b : Word (Fin BB))
  (d : Word (Fin BB))
  (cols : LtOperationSigned)
  (is_signed : Fin BB)
  (is_real : Fin BB)
  (h_b_isU64 : Word.isU64 b)
  (h_d_isU64 : Word.isU64 d) :
  List.Forall SP1Constraint.toProp (constraints b d cols is_signed is_real) →
    (is_real ≠ 0 → is_signed = 1 → BitVec.ofNat 64 cols.result.u16_compare_operation.bit = execute_RTYPE_pure_w b d .SLT)
  := by
    intro cstrs h_is_real h_is_signed
    rw [allHold_constraints_iff] at cstrs
    rcases cstrs with ⟨  h_b_msb, h_c_msb, h_lt, ⟨ h_is_signed_bool, h_is_real_bool, h_is_real_is_signed, h_is_signed_b_msb, h_is_signed_c_msb ⟩ ⟩
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_b_isU64) at h_b_msb
    apply U16MSBOperation.spec.U64 (h_w_isU64 := h_d_isU64) at h_c_msb
    apply Word.lt_cases_of_isU64 at h_b_isU64
    apply Word.lt_cases_of_isU64 at h_d_isU64
    subst is_signed; simp at *
    have h_sb_isU64 : Word.isU64 #v[b[0], b[1], b[2], b[3] + 32768 - 65536 * cols.b_msb.msb] := by
      rw [h_b_msb]; clear h_lt h_b_msb h_c_msb
      by_cases b.isNegative <;> unfold Word.isNegative at * <;> simp_all
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        omega
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        rw [if_neg] <;> omega
    have h_sd_isU64 : Word.isU64 #v[d[0], d[1], d[2], d[3] + 32768 - 65536 * cols.c_msb.msb] := by
      rw [h_c_msb]; clear h_lt h_b_msb h_c_msb
      by_cases d.isNegative <;> unfold Word.isNegative at * <;> simp_all
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        omega
      . apply Word.isU64_of_cases <;> rw [Vector.getElem_mk] <;> simp_all
        rw [if_neg] <;> omega
    apply LtOperationUnsigned.spec (h_b_isU64 := h_sb_isU64) (h_d_isU64 := h_sd_isU64) at h_lt
    simp [Word.toNat] at h_lt
    rw [h_lt (by trivial), h_b_msb, h_c_msb]
    unfold Word.toInt Word.toNat Word.isNegative
    split_ifs <;> simp <;> omega

def spec.branch.def
  (b : (Word (Fin BB)))
  (c : (Word (Fin BB)))
  (cols : LtOperationSigned)
  (is_signed : (Fin BB))
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
lemma spec.branch
  (b : (Word (Fin BB)))
  (d : (Word (Fin BB)))
  (cols : LtOperationSigned)
  (is_signed : (Fin BB))
  (is_real : Fin BB)
  (cstrs : (constraints b d cols is_signed is_real).allHold)
  (h_is_real : is_real = 1) : b.isU64 → d.isU64 → spec.branch.def b d cols is_signed
    := by
  intros is_U64_b is_U64_d
  obtain ⟨ b0_16, b1_16, b2_16, b3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_b
  obtain ⟨ d0_16, d1_16, d2_16, d3_16 ⟩ := Word.lt_cases_of_isU64 is_U64_d
  have spec.unsigned := spec.unsigned _ _ _ _ _ is_U64_b is_U64_d cstrs (by omega)
  have spec.signed := spec.signed _ _ _ _ _ is_U64_b is_U64_d cstrs (by omega)
  have : b.toBitVec64 = d.toBitVec64 ↔ b[0] = d[0] ∧ b[1] = d[1] ∧ b[2] = d[2] ∧ b[3] = d[3] := by
    simp_all [← BitVec.toNat_inj, Word.toBitVec64, Word.toNat]
    omega

  rw [SP1ConstraintList.allHold, allHold_constraints_iff] at cstrs
  rcases cstrs with ⟨ h_b_msb, h_d_msb, h_lt, ⟨ h_is_signed_bool, h_is_real_bool, h_is_real_is_signed, h_is_signed_b_msb, h_is_signed_d_msb ⟩ ⟩
  rw [LtOperationUnsigned.allHold_constraints_iff] at h_lt
  rcases h_lt with ⟨ h_comp_limbs, ⟨ h_is_real_bool, h_flag_0_bool, h_flag_1_bool, h_flag_2_bool, h_flag_3_bool, lt_00, lt_01, lt_02, lt_03, lt_04, lt_05, lt_06, lt_07 ⟩ ⟩
  rw [U16CompareOperation.allHold_constraints_iff] at h_comp_limbs
  rcases h_comp_limbs with ⟨ cmp_00, cmp_01, cmp_02 ⟩
  simp only [Nat.shiftLeft_eq] at *
  simp_all
  stop
  constructor <;> intro sgn <;> (repeat rw [this]) <;> clear this <;> simp_all


  . rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
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
  . rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_b_msb
    rw [← SP1ConstraintList.allHold, U16MSBOperation.allHold_constraints_iff] at h_d_msb
    rcases h_b_msb with ⟨ _, b_msb_b, hb3 ⟩; rcases h_d_msb with ⟨ _, b_msb_d, hd3 ⟩

    rcases h_flag_0_bool <;> rcases h_flag_1_bool <;>
    rcases h_flag_2_bool <;> rcases h_flag_3_bool <;>
    simp_all <;> split_ands

    on_goal 1 =>
      symm at lt_05 lt_06
      rcases b_msb_b <;> rcases b_msb_d <;> rcases cmp_01 <;> simp_all <;> omega

    on_goal 1 =>
      symm at lt_05 lt_06
      rcases b_msb_b <;> rcases b_msb_d <;> rcases cmp_01 <;> simp_all <;> omega

    on_goal 2 =>
      intros; intro eq; simp_all
      rcases b_msb_b <;> rcases b_msb_d <;> rcases cmp_01 <;> simp_all <;> (try omega)
      all_goals {
        clear *- d3_16 hb3 hd3
        simp_all [Fin.lt_def, Fin.mul_def, Fin.sub_def]
        rw [Nat.mod_eq_of_lt (by omega)] at hd3
        rw [Nat.mod_eq_of_lt (by omega)] at hb3
        omega
      }

    on_goal 3 => { intros; intro eqc; simp_all }
    on_goal 4 => { intros; intro eqc; simp_all }
    on_goal 5 => { intros; intro eqc; simp_all }

    all_goals {
      split_ifs at spec.signed with cond
      all_goals {
        iterate 2 rw [← Word.toBitVec64_toInt (by assumption)] at cond
        rw [← BitVec.slt_iff_toInt_lt (w := 64)] at cond
        simp [← BitVec.toNat_inj] at spec.signed
        simp_all; omega
      }
    }

end LtOperationSigned
