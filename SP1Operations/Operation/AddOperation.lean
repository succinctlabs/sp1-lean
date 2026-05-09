import SP1Foundations
import SP1Operations.Operation.AddOperation.Operation
import SP1Operations.Operation.AddOperation.Constraints

namespace AddOperation

/-- Equivalent formulation of constraints given that `is_real = 1`. -/
lemma allHold_constraints_iff (a b : Word (Fin KB)) (cols : AddOperation (Fin KB)) :
    List.Forall SP1Constraint.toProp (constraints a b cols 1) ↔
      let carry0 : Fin KB := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
      let carry1 : Fin KB := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
      let carry2 : Fin KB := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
      let carry3 : Fin KB := (a[3] + b[3] - cols.value[3] + carry2) * 65536⁻¹
      (carry0 = 0 ∨ carry0 = 1) ∧
      (carry1 = 0 ∨ carry1 = 1) ∧
      (carry2 = 0 ∨ carry2 = 1) ∧
      (carry3 = 0 ∨ carry3 = 1) ∧
      (cols.value[0].val < 65536) ∧
      (cols.value[1].val < 65536) ∧
      (cols.value[2].val < 65536) ∧
      (cols.value[3].val < 65536) := by
  simp [constraints, sub_eq_zero]

/-- Polymorphic companion to `allHold_constraints_iff`, stated over a generic
prime field `ZMod p` with `[Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]`. The
proof closes via the same `simp` recipe as the `Fin KB` version, with the
new `mul_inv_65536_eq_one_iff_poly` / `inv_65536_zero_or_one_poly` simp
lemmas in `Field.lean` discharging the carry-binary clauses. -/
lemma allHold_constraints_iff_poly
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (a b : Word (ZMod p)) (cols : AddOperation (ZMod p)) :
    SP1ConstraintList.allHold_poly (constraints a b cols 1) ↔
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
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly]

set_option maxHeartbeats 1000000 in

-- arithmetic spec proof over Word/BitVec
theorem spec
  {a b : Word (Fin KB)}
  {cols : AddOperation (Fin KB)}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols 1) →
    cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD := by
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
/-- Polymorphic companion of `spec`. The `Fin KB` version closes via
`simp_all <;> omega` after carry rcases, leveraging the `inv_65536BB_eq'`
literal-inverse simp lemma that doesn't generalize. The `_poly` recipe
re-arranges each iff_poly carry from inverse-form to a sum equation
`a[i] + b[i] + prev = cols.value[i] + c_i * 65536` via `linear_combination`
over `(65536 : ZMod p) * 65536⁻¹ = 1`, then applies `limb_lift` to convert
each to a Nat equation, and closes the BitVec goal (after
`Word.toBitVec64_poly_toNat_poly` bridges) by omega. Symmetric to
`SubOperation.spec_poly` — Add's natural-form carries don't need the
borrow-form bridge that Sub does. -/
theorem spec_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : AddOperation (ZMod p)}
  (h_isU64_a : a.isU64_poly)
  (h_isU64_b : b.isU64_poly) :
  SP1ConstraintList.allHold_poly (constraints a b cols 1) →
    cols.value.isU64_poly ∧
    cols.value.toBitVec64_poly = execute_RTYPE_pure_w_poly a b .ADD := by
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
  rw [show execute_RTYPE_pure_w_poly a b .ADD =
        a.toBitVec64_poly + b.toBitVec64_poly from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_poly_toNat_poly h_isU64_v,
      Word.toBitVec64_poly_toNat_poly h_isU64_b,
      Word.toBitVec64_poly_toNat_poly h_isU64_a,
      Word.toNat_poly_def, Word.toNat_poly_def, Word.toNat_poly_def]
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

section gen

theorem spec.gen
  {a b : Word (Fin KB)}
  {cols : AddOperation (Fin KB)}
  {is_real : Fin KB}
  (h_isU64_a : a.isU64)
  (h_isU64_b : b.isU64) :
  List.Forall SP1Constraint.toProp (constraints a b cols is_real) →
    is_real = 1 →
      cols.value.isU64 ∧ cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD := by
  intro cstrs is_real; simp_all
  exact spec h_isU64_a h_isU64_b cstrs

/-- Polymorphic counterpart of `spec.gen`. -/
theorem spec.gen_poly
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  {a b : Word (ZMod p)}
  {cols : AddOperation (ZMod p)}
  {is_real : ZMod p}
  (h_isU64_a : a.isU64_poly)
  (h_isU64_b : b.isU64_poly) :
  List.Forall SP1Constraint.toProp_poly (constraints a b cols is_real) →
    is_real = 1 →
      cols.value.isU64_poly ∧
      cols.value.toBitVec64_poly = execute_RTYPE_pure_w_poly a b .ADD := by
  intros cstrs hir
  subst hir
  exact spec_poly h_isU64_a h_isU64_b cstrs

end gen

end AddOperation
