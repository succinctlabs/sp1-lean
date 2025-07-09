import SP1Foundations

structure AddOperation where
  value : Word (Fin BB)

namespace AddOperation

def constraints
  (a : (Word (Fin BB)))
  (b : (Word (Fin BB)))
  (cols : AddOperation)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := a[0] + b[0]
  let E3 : Fin BB := E2 - cols.value[0]
  let E4 : Fin BB := E3 + 0
  let E5 : Fin BB := E4 * 2013235201
  let E6 : Fin BB := E5 - 1
  let E7 : Fin BB := E5 * E6
  let E8 : Fin BB := is_real * E7
  let E9 : Fin BB := a[1] + b[1]
  let E10 : Fin BB := E9 - cols.value[1]
  let E11 : Fin BB := E10 + E5
  let E12 : Fin BB := E11 * 2013235201
  let E13 : Fin BB := E12 - 1
  let E14 : Fin BB := E12 * E13
  let E15 : Fin BB := is_real * E14
  let E16 : Fin BB := a[2] + b[2]
  let E17 : Fin BB := E16 - cols.value[2]
  let E18 : Fin BB := E17 + E12
  let E19 : Fin BB := E18 * 2013235201
  let E20 : Fin BB := E19 - 1
  let E21 : Fin BB := E19 * E20
  let E22 : Fin BB := is_real * E21
  let E23 : Fin BB := a[3] + b[3]
  let E24 : Fin BB := E23 - cols.value[3]
  let E25 : Fin BB := E24 + E19
  let E26 : Fin BB := E25 * 2013235201
  let E27 : Fin BB := E26 - 1
  let E28 : Fin BB := E26 * E27
  let E29 : Fin BB := is_real * E28
  [
    (.assertZero E1),
    (.assertZero E8),
    (.assertZero E15),
    (.assertZero E22),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 7) cols.value[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 7) cols.value[1] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 7) cols.value[2] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 7) cols.value[3] 16 0) is_real),
  ]

-- def constraintsProp (a b : Word (Fin BB)) (cols : AddOperation) : Prop :=
--   let carry0  : Fin BB := 0
--   let carry1  : Fin BB := (a[0] + b[0] - cols.value[0] + carry0) * 65536⁻¹
--   let carry2  : Fin BB := (a[1] + b[1] - cols.value[1] + carry1) * 65536⁻¹
--   let carry3  : Fin BB := (a[2] + b[2] - cols.value[2] + carry2) * 65536⁻¹
--   (carry1 = 0 ∨ carry1 = 1) ∧
--   (carry2 = 0 ∨ carry2 = 1) ∧
--   (carry3 = 0 ∨ carry3 = 1) ∧
--   (cols.value[0] < 65536) ∧
--   (cols.value[1] < 65536) ∧
--   (cols.value[2] < 65536) ∧
--   (cols.value[3] < 65536)

/-- Equivalent formulation of constraints given that `is_real = 1`.
dt: could extract this as above but doesn't seem especially useful -/
lemma allHold_constraints_iff (a b : Word (Fin BB)) (cols : AddOperation) :
    (constraints a b cols 1).allHold ↔
      let carry0 : Fin BB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin BB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin BB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin BB := (a[3] + b[3] - cols.value[3] + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0] < 65536) ∧
      (cols.value[1] < 65536) ∧
      (cols.value[2] < 65536) ∧
      (cols.value[3] < 65536) := by
  simp [constraints, sub_eq_zero, inv_16BB_eq']

def spec (a b : Word (Fin BB)) (cols : AddOperation) : Prop :=
  cols.value.toBitVec64 = a.toBitVec64 + b.toBitVec64

theorem correct (a b : Word (Fin BB)) (cols : AddOperation) (is_real : Fin BB)
    (h_is_real : is_real = 1)
    (h_cstrs : (constraints a b cols is_real).allHold) :
    spec a b cols := by
  cases h_is_real
  rw [allHold_constraints_iff] at h_cstrs
  obtain ⟨h0, h1, h2, h3, hbds⟩ := h_cstrs
  unfold spec
  sorry
  -- rw [Word.toBitVec64_add_toBitVec64 a b]
  -- match h0, h1, h2, h3 with
  -- | .inl h0, .inl h1, .inl h2, .inl h3 => {
  --   -- simp [h0] at h1 h2 h3
  --   sorry
  -- }
  -- | _, _, _, _ => sorry


-- lemma lt_of_constraintsAllHold
--     (h : (constraints a b cols is_real).allHold)
--     (h_is_real : is_real = 1) : cols.value[0] < 65536 := by
--   rw [constraints_iff_constraintsProp] at h
--   rw [constraintsProp] at h
--   simp at h
--   subst h_is_real
--   tauto

-- lemma lt_of_constraintsAllHold'
--     (h : (constraints a b cols is_real).allHold)
--     (h_is_real : is_real = 1) : cols.value[1] < 65536 := by
--   rw [constraints_iff_constraintsProp] at h
--   rw [constraintsProp] at h
--   simp at h
--   subst h_is_real
--   tauto

-- /-- Version of correctness using specific bitvecs.
-- To get good rewrites we allow arbitrary proofs on the left (should do the reverse for ← rw to work)-/
-- lemma correct'
--     (a b : Word U16)
--     (cols : AddOperation)
--     (is_real : U1)
--     (h : (constraints a b cols is_real).allHold)
--     (h_is_real : is_real = 1)
--     (pf : cols.value[0].val + cols.value[1].val * 65536 < 2 ^ 32) :
--     (cols.value[0].val + cols.value[1].val * 65536)#'pf =
--       (a.toBV32_U16 + b.toBV32_U16) := by
--   let c0' : U16 := ⟨cols.value[0], lt_of_constraintsAllHold h (by aesop)⟩
--   let c1' : U16 := ⟨cols.value[1], lt_of_constraintsAllHold' h (by aesop)⟩
--   rw [BitVec.ofNatLT_eq_ofNat pf]
--   refine correct a b { value := #v[c0', c1'] } is_real h h_is_real

-- lemma correct''
--     (a b : Word U16)
--     (cols : AddOperation)
--     (is_real : Fin BB)
--     (h : (constraints a b cols is_real).allHold)
--     (h_is_real : is_real = 1)
--     (pf : cols.value[0].val + cols.value[1].val * 65536 < 2 ^ 32) :
--     (cols.value[0].val + cols.value[1].val * 65536)#'pf =
--       (a.toBV32_U16 + b.toBV32_U16) := by
--   -- TODO(gzgz): don't use aesop
--   let c0' : U16 := ⟨cols.value[0], lt_of_constraintsAllHold h (by aesop)⟩
--   let c1' : U16 := ⟨cols.value[1], lt_of_constraintsAllHold' h (by aesop)⟩
--   rw [BitVec.ofNatLT_eq_ofNat pf]
--   refine correct a b { value := #v[c0', c1'] } ⟨is_real, by aesop⟩ h (by aesop)

end AddOperation
