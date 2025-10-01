import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddrAddOperation

lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : AddrAddOperation) :
    (constraints a b cols 1).allHold ↔
      let carry0 : Fin KB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin KB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin KB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin KB := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) := by
  simp [constraints, sub_eq_zero, inv_16BB_eq']

theorem is_u48_sum (a b : Word (Fin KB)) (cols : AddrAddOperation) (is_real : Fin KB)
    (h_is_real : is_real = 1)
    (cstrs : (constraints a b cols is_real).allHold)
    (ha : a.isU64)
    (hb : b.isU64)
    : (a.toNat + b.toNat) % 2^64 < 2^48 := by
      simp [SP1ConstraintList.allHold, h_is_real] at cstrs
      simp only [allHold_constraints_iff a b cols] at cstrs

      obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := cstrs
      simp [← inv_16BB_eq'] at *

      have ha' := Word.lt_cases_of_isU64 ha
      have hb' := Word.lt_cases_of_isU64 hb
      simp at ha' hb'

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

set_option maxHeartbeats 1000000 in
theorem cols_is_a_sum_b (a b : Word (Fin KB)) (cols : AddrAddOperation) (is_real : Fin KB)
    (h_is_real : is_real = 1)
    (cstrs : (constraints a b cols is_real).allHold)
    (ha : a.isU64)
    (hb : b.isU64)
    : (a.toNat + b.toNat) % 2^64 = Word.toNat #v[cols.value[0], cols.value[1], cols.value[2], 0]
    := by
      have h_sum_u48 := is_u48_sum _ _ _ _ h_is_real cstrs ha hb
      simp [Word.toNat] at h_sum_u48

      simp [SP1ConstraintList.allHold, h_is_real] at cstrs
      simp [allHold_constraints_iff a b cols] at cstrs
      obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := cstrs
      simp [← inv_16BB_eq'] at *

      have ha' := Word.lt_cases_of_isU64 ha
      have hb' := Word.lt_cases_of_isU64 hb
      simp at ha' hb'

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

def spec (a b : Word (Fin KB)) (cols : AddrAddOperation) : Prop :=
  let cols_word : Word (Fin KB) := #v[cols.value[0], cols.value[1], cols.value[2], 0]
  cols_word.isU64 ∧ cols_word.toBitVec64 = a.toBitVec64 + b.toBitVec64

set_option debug.skipKernelTC true in
lemma spec_of_constraints (a : Word (Fin KB)) (b : Word (Fin KB))
    (ha : a.isU64) (hb : b.isU64)
    (cols : AddrAddOperation)
    (h : SP1ConstraintList.allHold (AddrAddOperation.constraints a b cols 1)) :
    (spec a b cols) := by
  have h_sum_u48 := is_u48_sum _ _ _ _ rfl h ha hb
  have h_cols_sum := cols_is_a_sum_b _ _ _ _ rfl h ha hb
  simp [spec]
  rw [allHold_constraints_iff] at h
  obtain ⟨h0, h1, h2, h3, hbd0, hbd1, hbd2⟩ := h
  constructor
  · apply Word.isU64_of_cases <;> simp [hbd0, hbd1, hbd2]
  · simp [Word.toBitVec64, ← h_cols_sum, BitVec.toNat_eq]

end AddrAddOperation
