import Mathlib
import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

open BitVec

namespace AddrAddOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin BB)) (cols : AddrAddOperation) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin BB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin BB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin BB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin BB := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) := by
  simp [constraints, sub_eq_zero, inv_16BB_eq']

lemma isU64_of_allHold_constraints (a b : Word (Fin BB)) (cols : AddrAddOperation)
    (h : (constraints a b cols 1).allHold) :
    cols.value[0] < 65536 ∧ cols.value[1] < 65536 ∧ cols.value[2] < 65536 := by
  simp [allHold_constraints_iff] at h
  obtain ⟨_, _, _, _, h0, h1, h2⟩ := h
  exact ⟨h0, h1, h2⟩

/-- The specification for AddrAddOperation: it computes a 3-limb addition (address addition).
    The result is stored in the lower 3 limbs, with the 4th limb being 0. -/
def spec (a b : Word (Fin BB)) (cols : AddrAddOperation) : Prop :=
  a.isU64 → b.isU64 →
    cols.value[0] < 65536 ∧ cols.value[1] < 65536 ∧ cols.value[2] < 65536 ∧
    Word.toBitVec64 #v[cols.value[0], cols.value[1], cols.value[2], 0] = a.toBitVec64 + b.toBitVec64

set_option maxHeartbeats 1000000 in
theorem is_u48_sum (a b : Word (Fin BB)) (cols : AddrAddOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (cstrs : (constraints a b cols is_real).allHold)
    (ha : a.isU64)
    (hb : b.isU64)
    : (a.toNat + b.toNat) % 2^64 < 2^48 := by
      simp [SP1ConstraintList.allHold, h_is_real] at cstrs
      rw [allHold_constraints_iff a b cols] at cstrs
      obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := cstrs
      simp [← inv_16BB_eq'] at *

      have ha' := Word.lt_cases_of_isU64 ha
      have hb' := Word.lt_cases_of_isU64 hb
      simp at ha' hb'

      simp [Word.toNat]
      stop
      cases h0 <;> rename_i h0
      <;> simp [sub_eq_zero] at h0
      <;> simp [h0] at h1 h2 h3
      <;> cases h1 <;> rename_i h1
      <;> simp [sub_eq_zero] at h1
      <;> simp [h0, h1] at h2 h3
      <;> cases h2 <;> rename_i h2
      <;> simp [sub_eq_zero] at h2
      <;> simp [h0, h1, h2] at h3
      <;> cases h3 <;> rename_i h3
      <;> simp [sub_eq_zero] at h3
      <;> omega

set_option maxHeartbeats 1000000 in
theorem cols_is_a_sum_b (a b : Word (Fin BB)) (cols : AddrAddOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (cstrs : (constraints a b cols is_real).allHold)
    (ha : a.isU64)
    (hb : b.isU64)
    : (a.toNat + b.toNat) % 2^64 = Word.toNat #v[cols.value[0], cols.value[1], cols.value[2], 0]
    := by
      have h_sum_u48 := is_u48_sum _ _ _ _ h_is_real cstrs ha hb
      simp [Word.toNat] at h_sum_u48

      simp [SP1ConstraintList.allHold, h_is_real] at cstrs
      rw [allHold_constraints_iff a b cols] at cstrs
      obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := cstrs
      simp [← inv_16BB_eq'] at *

      have ha' := Word.lt_cases_of_isU64 ha
      have hb' := Word.lt_cases_of_isU64 hb
      simp at ha' hb'
      stop
      simp [Word.toNat]
      cases h0 <;> rename_i h0
      <;> simp [sub_eq_zero] at h0
      <;> simp [h0] at h1 h2 h3
      <;> cases h1 <;> rename_i h1
      <;> simp [sub_eq_zero] at h1
      <;> simp [h0, h1] at h2 h3
      <;> cases h2 <;> rename_i h2
      <;> simp [sub_eq_zero] at h2
      <;> simp [h0, h1, h2] at h3
      <;> cases h3 <;> rename_i h3
      <;> simp [sub_eq_zero] at h3
      <;> omega

theorem bvmod
  : BitVec.ofNat w (x % 2^w) = BitVec.ofNat w x
  := by
    unfold BitVec.ofNat
    apply congrArg
    aesop

/-- If the operation is real and the input words have correctly bounded limbs,
then the constraints imply the spec. -/
theorem correct (a b : Word (Fin BB)) (cols : AddrAddOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (cstrs : (constraints a b cols is_real).allHold) :
    spec a b cols := by
  intro ha hb
  have h_sum_u48 := is_u48_sum _ _ _ _ h_is_real cstrs ha hb
  have h_cols_sum := cols_is_a_sum_b _ _ _ _ h_is_real cstrs ha hb

  cases h_is_real

  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := cstrs

  have ha' := Word.lt_cases_of_isU64 ha
  have hb' := Word.lt_cases_of_isU64 hb

  refine ⟨hbd0, hbd1, hbd2, ?_⟩
  stop
  have h_cols_is_u64 : Word.isU64 #v[cols.value[0], cols.value[1], cols.value[2], 0] := by
    exact Word.isU64_of_cases _ hbd0 hbd1 hbd2 (by simp)

  simp [Word.toBitVec64_LT_eq_toNat h_cols_is_u64]
  conv =>
    rhs
    simp [Word.toBitVec64]
    rw [←BitVec.ofNat_add]

  clear * - h_cols_sum
  have := congrArg (BitVec.ofNat 64) h_cols_sum
  rw [bvmod] at this
  rw [this]
  refine BitVec.ofNatLT_eq_ofNat ?_

end AddrAddOperation
