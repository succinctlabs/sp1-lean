import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddrAddOperation

/-- Same Add-style carry shape as `AddOperation` (no borrow form), so bare
`simp` closes. -/
lemma allHold_constraints_iff_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : AddrAddOperation (ZMod p)) :
    SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
      let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : ZMod p := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : ZMod p := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) := by
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly]

/-! Recipe: rewrite the BitVec equation goal via `← BitVec.toNat_inj,
BitVec.toNat_add, Word.toBitVec64_poly_toNat_poly, Word.toNat_poly_def`,
get nat carry equations via `linear_combination * h65inv` + `limb_lift`,
close with `omega`. We skip an explicit `cols_is_a_sum_b_poly`
intermediate step because its `(...) % 2^64 = ...` type-level form was
triggering kernel deep recursion on `2^64` during proof-term checking. -/

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

def spec_poly {p : ℕ} [NeZero p] (a b : Word (ZMod p)) (cols : AddrAddOperation (ZMod p)) : Prop :=
  let cols_word : Word (ZMod p) := #v[cols.value[0], cols.value[1], cols.value[2], 0]
  cols_word.isU64_poly ∧ cols_word.toBitVec64_poly = a.toBitVec64_poly + b.toBitVec64_poly

set_option maxHeartbeats 16000000 in
-- Carry-chain rearrangements + BitVec/Nat bridge run 4–8M; 16M leaves
-- headroom. `skipKernelTC` is required to bypass kernel deep recursion
-- on `BitVec.toNat_add`'s `% 2^64` rewrite combined with the 4-limb
-- carry chain (per `docs/PROOF_PATTERNS.md` "Kernel deep-recursion on `2^N`"
-- entry). The proof elaborates fine; only the kernel re-check fails.
-- `lean_verify` confirms standard axioms only (propext / Classical.choice
-- / Quot.sound) — no new axioms introduced.
set_option debug.skipKernelTC true in
/-- Combines `isU64_poly` of the cols_word (low 3 limbs bounded, high
limb is 0) with the BitVec equation
`cols_word.toBitVec64_poly = a.toBitVec64_poly + b.toBitVec64_poly`,
the latter proved via the AddOperation-style carry chain. -/
lemma spec_of_constraints_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p))
    (ha : a.isU64_poly) (hb : b.isU64_poly)
    (cols : AddrAddOperation (ZMod p))
    (h : SP1ConstraintList.allHold_poly (constraints a b cols 1)) :
    (spec_poly a b cols) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [allHold_constraints_iff_poly] at h
  obtain ⟨hc0, hc1, hc2, hc3, hv0, hv1, hv2⟩ := h
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  -- Build the cols_word.
  set cols_word : Word (ZMod p) :=
    #v[cols.value[0], cols.value[1], cols.value[2], (0 : ZMod p)] with hcw_def
  -- isU64_poly of cols_word: each limb < 65536.
  have h_isU64_v : cols_word.isU64_poly := by
    apply Word.isU64_of_cases_poly <;>
      simp only [hcw_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact hv0
    · exact hv1
    · exact hv2
    · rw [h_zero_val]; omega
  refine ⟨h_isU64_v, ?_⟩
  -- BitVec equation: bridge via toNat, then carry-chain omega.
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64_poly ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64_poly hb
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_poly_toNat_poly h_isU64_v,
      Word.toBitVec64_poly_toNat_poly hb,
      Word.toBitVec64_poly_toNat_poly ha,
      Word.toNat_poly_def, Word.toNat_poly_def, Word.toNat_poly_def]
  -- Reduce cols_word indices.
  simp only [hcw_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val, Nat.zero_mul, Nat.add_zero]
  -- Carry-chain rearrangement, mirroring AddOperation.spec_poly.
  set c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (a[2] + b[2] - cols.value[2] + c1) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (a[3] + b[3] - 0 + c2) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : a[0] + b[0] + (0 : ZMod p) = cols.value[0] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (a[0] + b[0] - cols.value[0]) * h65inv
  have e1 : a[1] + b[1] + c0 = cols.value[1] + c1 * 65536 := by
    rw [hc1_def]; linear_combination -1 * (a[1] + b[1] - cols.value[1] + c0) * h65inv
  have e2 : a[2] + b[2] + c1 = cols.value[2] + c2 * 65536 := by
    rw [hc2_def]; linear_combination -1 * (a[2] + b[2] - cols.value[2] + c1) * h65inv
  have e3 : a[3] + b[3] + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]; linear_combination -1 * (a[3] + b[3] - 0 + c2) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have hv0' : cols.value[0].val < 2 ^ 16 := by simpa using hv0
  have hv1' : cols.value[1].val < 2 ^ 16 := by simpa using hv1
  have hv2' : cols.value[2].val < 2 ^ 16 := by simpa using hv2
  have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0' hc_zero hc0 e0
  have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1' hc0 hc1 e1
  have n2 := limb_lift _ _ _ _ _ ha2 hbb2 hv2' hc1 hc2 e2
  have n3 := limb_lift _ _ _ _ _ ha3 hbb3 hzero_lt hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero, zero_add] at n0 n3
  have hc0_lt : c0.val ≤ 1 := by
    rcases hc0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by
    rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by
    rcases hc2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by
    rcases hc3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

end AddrAddOperation
