import SP1Foundations
import SP1Operations.Operation.SubOperation.Operation
import SP1Operations.Operation.SubOperation.Constraints

namespace SubOperation

set_option maxHeartbeats 1000000 in
-- iff-characterization of constraints
lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : SubOperation (Fin KB)) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
    let carry0 : Fin KB := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
    let carry1 : Fin KB := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
    let carry2 : Fin KB := (b[2] + cols.value[2] - a[2] + carry1) * 65536⁻¹
    let carry3 : Fin KB := (b[3] + cols.value[3] - a[3] + carry2) * 65536⁻¹
    (carry0 = 0 ∨ carry0 = 1) ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (carry3 = 0 ∨ carry3 = 1) ∧
    (cols.value[0].val < 65536) ∧
    (cols.value[1].val < 65536) ∧
    (cols.value[2].val < 65536) ∧
    (cols.value[3].val < 65536) := by
  simp [constraints, ← inv_65536BB_eq', sub_eq_zero]
  constructor <;> intro ⟨h0, h1, h2, h3, r0, r1, r2, r3⟩ <;> split_ands <;>
  [ clear *- h0; clear *- h1; clear *- h2; clear *- h3; exact r0; exact r1; exact r2; exact r3;
    clear *- h0; clear *- h1; clear *- h2; clear *- h3; exact r0; exact r1; exact r2; exact r3 ] <;>
  omega

/-- Disjunction-shift helper: if `x = 1 - y`, then `x ∈ {0, 1} ↔ y ∈ {0, 1}`
(the disjunction commutes). Used to bridge the borrow-form auto-gen
carries (`d_i = (a + 65536 - 1 - b - c + d_{i-1}) * 65536⁻¹`) to the
natural-form iff carries (`c_i = (b + c - a + c_{i-1}) * 65536⁻¹`),
which differ by `d_i = 1 - c_i`. -/
private lemma carry_swap_iff_poly {p : ℕ} [Fact (Nat.Prime p)]
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
-- The proof's `set`-then-`linear_combination` cascade is heartbeat-heavy
-- (4 carry-swap bridges, each closing via field arithmetic); the elevated
-- limit is well below the maximum and stays in cache.
/-- Polymorphic companion of `allHold_constraints_iff` over `ZMod p`. Unlike
the `Fin KB` version (which drops into omega via `← inv_65536BB_eq'` over
the literal `2130673921`), this proof bridges the borrow-form auto-gen
carries (`d_i`) to the natural-form iff carries (`c_i`) via the relation
`d_i = 1 - c_i` plus `carry_swap_iff_poly`. -/
lemma allHold_constraints_iff_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : SubOperation (ZMod p)) :
    SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
    let carry0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
    let carry1 : ZMod p := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
    let carry2 : ZMod p := (b[2] + cols.value[2] - a[2] + carry1) * 65536⁻¹
    let carry3 : ZMod p := (b[3] + cols.value[3] - a[3] + carry2) * 65536⁻¹
    (carry0 = 0 ∨ carry0 = 1) ∧
    (carry1 = 0 ∨ carry1 = 1) ∧
    (carry2 = 0 ∨ carry2 = 1) ∧
    (carry3 = 0 ∨ carry3 = 1) ∧
    (cols.value[0].val < 65536) ∧
    (cols.value[1].val < 65536) ∧
    (cols.value[2].val < 65536) ∧
    (cols.value[3].val < 65536) := by
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  set c0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹ with hc0_def
  set c1 : ZMod p := (b[1] + cols.value[1] - a[1] + c0) * 65536⁻¹ with hc1_def
  set c2 : ZMod p := (b[2] + cols.value[2] - a[2] + c1) * 65536⁻¹ with hc2_def
  set c3 : ZMod p := (b[3] + cols.value[3] - a[3] + c2) * 65536⁻¹ with hc3_def
  set d0 : ZMod p := (a[0] + 65536 - 1 - b[0] - cols.value[0] + 1) * 65536⁻¹ with hd0_def
  set d1 : ZMod p := (a[1] + 65536 - 1 - b[1] - cols.value[1] + d0) * 65536⁻¹ with hd1_def
  set d2 : ZMod p := (a[2] + 65536 - 1 - b[2] - cols.value[2] + d1) * 65536⁻¹ with hd2_def
  set d3 : ZMod p := (a[3] + 65536 - 1 - b[3] - cols.value[3] + d2) * 65536⁻¹ with hd3_def
  have hd0_swap : d0 = 1 - c0 := by
    rw [hd0_def, hc0_def]; linear_combination (1 : ZMod p) * hbridge
  have hd1_swap : d1 = 1 - c1 := by
    rw [hd1_def, hd0_swap, hc1_def, hc0_def]
    linear_combination (1 : ZMod p) * hbridge
  have hd2_swap : d2 = 1 - c2 := by
    rw [hd2_def, hd1_swap, hc2_def, hc1_def, hc0_def]
    linear_combination (1 : ZMod p) * hbridge
  have hd3_swap : d3 = 1 - c3 := by
    rw [hd3_def, hd2_swap, hc3_def, hc2_def, hc1_def, hc0_def]
    linear_combination (1 : ZMod p) * hbridge
  -- The borrow-form iff closes by bare simp because the auto-gen carries
  -- `d_i` match the LHS structure verbatim (no shape mismatch).
  have h_borrow :
      SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
        (d0 = 0 ∨ d0 = 1) ∧ (d1 = 0 ∨ d1 = 1) ∧ (d2 = 0 ∨ d2 = 1) ∧ (d3 = 0 ∨ d3 = 1) ∧
        cols.value[0].val < 65536 ∧ cols.value[1].val < 65536 ∧
        cols.value[2].val < 65536 ∧ cols.value[3].val < 65536 := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly,
          hd0_def, hd1_def, hd2_def, hd3_def]
  rw [h_borrow,
      carry_swap_iff_poly d0 c0 hd0_swap,
      carry_swap_iff_poly d1 c1 hd1_swap,
      carry_swap_iff_poly d2 c2 hd2_swap,
      carry_swap_iff_poly d3 c3 hd3_swap]

set_option maxHeartbeats 1000000 in

-- arithmetic spec proof over Word/BitVec
theorem spec
  {a b : Word (Fin KB)}
  {cols : SubOperation (Fin KB)}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .SUB := by
  intro cstrs
  simp [allHold_constraints_iff] at cstrs
  obtain ⟨h0, h1, h2, h3, hbds⟩ := cstrs
  apply Word.lt_cases_of_isU64 at h_isU64_a
  apply Word.lt_cases_of_isU64 at h_isU64_b
  constructor
  · clear *- hbds; aesop
  · simp [BitVec.eq_sub_iff_add_eq]
    simp [Word.toBitVec64, Word.toNat]
    rw [← BitVec.toNat_inj, BitVec.toNat_add]
    rcases h0 <;> rcases h1 <;> rcases h2 <;> rcases h3 <;>
    simp_all <;> omega

/-- Per-limb Nat lift: given the ZMod-level limb equation
`bb + vv + prev = aa + cc * 65536` (where `prev, cc ∈ {0, 1}` and the
`bb, vv, aa` limbs are bounded by `2^16`), produce the Nat equation
`bb.val + vv.val + prev.val = aa.val + cc.val * 65536`. The `[Fact (2^17
< p)]` hypothesis ensures every additive sum on either side fits in
`< p`, so `apply_fun ZMod.val` plus `ZMod.val_add_of_lt` lifts cleanly. -/
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
/-- Polymorphic companion of `spec`. The `Fin KB` version closes via
`simp_all <;> omega` after carry rcases, leveraging the `inv_65536BB_eq'`
literal-inverse simp lemma that doesn't generalize. The `_poly` recipe
re-arranges each iff_poly carry from inverse-form to a sum equation
`b[i] + v[i] + prev = a[i] + c_i * 65536` via `linear_combination` over
`(65536 : ZMod p) * 65536⁻¹ = 1`, then applies `limb_lift` to convert
each to a Nat equation, and closes the BitVec goal (after
`Word.toBitVec64_poly_toNat_poly` bridges) by omega. -/
theorem spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : SubOperation (ZMod p)}
  (h_isU64_a : a.isU64_poly)
  (h_isU64_b : b.isU64_poly) :
  SP1ConstraintList.allHold_poly (constraints a b cols 1) →
    cols.value.isU64_poly ∧
    cols.value.toBitVec64_poly = execute_RTYPE_pure_w_poly a b .SUB := by
  intro cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  obtain ⟨hc0, hc1, hc2, hc3, hv0, hv1, hv2, hv3⟩ := cstrs
  have h_isU64_v : cols.value.isU64_poly :=
    Word.isU64_of_cases_poly hv0 hv1 hv2 hv3
  refine ⟨h_isU64_v, ?_⟩
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64_poly h_isU64_a
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64_poly h_isU64_b
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [show execute_RTYPE_pure_w_poly a b .SUB =
        a.toBitVec64_poly - b.toBitVec64_poly from rfl,
      BitVec.eq_sub_iff_add_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_poly_toNat_poly h_isU64_v,
      Word.toBitVec64_poly_toNat_poly h_isU64_b,
      Word.toBitVec64_poly_toNat_poly h_isU64_a,
      Word.toNat_poly_def, Word.toNat_poly_def, Word.toNat_poly_def]
  set c0 : ZMod p := (b[0] + cols.value[0] - a[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (b[1] + cols.value[1] - a[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (b[2] + cols.value[2] - a[2] + c1) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (b[3] + cols.value[3] - a[3] + c2) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : b[0] + cols.value[0] + (0 : ZMod p) = a[0] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (b[0] + cols.value[0] - a[0]) * h65inv
  have e1 : b[1] + cols.value[1] + c0 = a[1] + c1 * 65536 := by
    rw [hc1_def]; linear_combination -1 * (b[1] + cols.value[1] - a[1] + c0) * h65inv
  have e2 : b[2] + cols.value[2] + c1 = a[2] + c2 * 65536 := by
    rw [hc2_def]; linear_combination -1 * (b[2] + cols.value[2] - a[2] + c1) * h65inv
  have e3 : b[3] + cols.value[3] + c2 = a[3] + c3 * 65536 := by
    rw [hc3_def]; linear_combination -1 * (b[3] + cols.value[3] - a[3] + c2) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have n0 := limb_lift _ _ _ _ _ hbb0 hv0 ha0 hc_zero hc0 e0
  have n1 := limb_lift _ _ _ _ _ hbb1 hv1 ha1 hc0 hc1 e1
  have n2 := limb_lift _ _ _ _ _ hbb2 hv2 ha2 hc1 hc2 e2
  have n3 := limb_lift _ _ _ _ _ hbb3 hv3 ha3 hc2 hc3 e3
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

end SubOperation
