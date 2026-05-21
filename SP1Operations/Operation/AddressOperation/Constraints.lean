import SP1Foundations
import SP1Operations.Operation.AddressOperation.Operation
import SP1Operations.Operation.AddrAddOperation.Constraints

namespace AddressOperation

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (b : (Word F))
  (cc : (Word F))
  (offset_bit0 : F)
  (offset_bit1 : F)
  (offset_bit2 : F)
  (is_real : F)
  (cols : AddressOperation F)
  : (Vector F 3) × SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := offset_bit0 - 1
  let E3 : F := offset_bit0 * E2
  let E4 : F := offset_bit1 - 1
  let E5 : F := offset_bit1 * E4
  let E6 : F := offset_bit2 - 1
  let E7 : F := offset_bit2 * E6
  let CS0 : SP1ConstraintList F := AddrAddOperation.constraints #v[b[0], b[1], b[2], b[3]] #v[cc[0], cc[1], cc[2], cc[3]] { value := #v[cols.addr_operation.value[0], cols.addr_operation.value[1], cols.addr_operation.value[2]] } is_real
  let E8 : F := cols.addr_operation.value[1] + cols.addr_operation.value[2]
  let E9 : F := cols.top_two_limb_inv * E8
  let E10 : F := E9 - is_real
  let E11 : F := 4 * offset_bit2
  let E12 : F := cols.addr_operation.value[0] - E11
  let E13 : F := 2 * offset_bit1
  let E14 : F := E12 - E13
  let E15 : F := E14 - offset_bit0
  let E16 : F := E15 * ((8 : F)⁻¹)
  let E17 : F := 4 * offset_bit2
  let E18 : F := cols.addr_operation.value[0] - E17
  let E19 : F := 2 * offset_bit1
  let E20 : F := E18 - E19
  let E21 : F := E20 - offset_bit0
  ⟨#v[E21, cols.addr_operation.value[1], cols.addr_operation.value[2]], CS0 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E10),
    (.send (.byte (ByteOpcode.ofNat 6) E16 13 0) is_real),
  ]⟩

end constraints

section bounds

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- The top-two-limb-inverse trick used by `AddressOperation` (`E10` of the
constraint list, `top_two_limb_inv * (addr[1] + addr[2]) = is_real`) plus u16
bounds on the three address limbs gives the SP1 PMA window
`[2^16, 2^48)` on the limb-encoded address. Used by chip-side `correct_*`
proofs to discharge the `range_subset` precondition of `run_vmem_*`. -/
lemma addr_limbs_bounds
    (a₀ a₁ a₂ inv : ZMod p)
    (ha₀ : a₀.val < 2 ^ 16) (ha₁ : a₁.val < 2 ^ 16) (ha₂ : a₂.val < 2 ^ 16)
    (h_top : inv * (a₁ + a₂) = 1) :
    2 ^ 16 ≤ a₀.val + a₁.val * 2 ^ 16 + a₂.val * 2 ^ 32 ∧
      a₀.val + a₁.val * 2 ^ 16 + a₂.val * 2 ^ 32 < 2 ^ 48 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  refine ⟨?_, by nlinarith⟩
  by_contra hzero
  push Not at hzero
  have h₁ : a₁.val = 0 := by nlinarith
  have h₂ : a₂.val = 0 := by nlinarith
  have e₁ : a₁ = 0 := (ZMod.val_eq_zero _).mp h₁
  have e₂ : a₂ = 0 := (ZMod.val_eq_zero _).mp h₂
  rw [e₁, e₂, add_zero, mul_zero] at h_top
  exact one_ne_zero h_top.symm

end bounds

end AddressOperation
