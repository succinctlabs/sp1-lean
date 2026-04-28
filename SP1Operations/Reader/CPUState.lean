import SP1Operations.Reader.CPUState.Operation
import SP1Operations.Reader.CPUState.Constraints

namespace CPUState

lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints cols next_pc clk_increment is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_real = 0 →
      ((cols.clk_0_16 - 1) * (8 : Fin KB)⁻¹) < 8192 ∧
      cols.clk_16_24 < 256)
   := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp]
    tauto

lemma allHold_constraints_iff_is_real (h : is_real = 1) :
  List.Forall SP1Constraint.toProp (constraints cols next_pc clk_increment is_real) ↔
      ((cols.clk_0_16 - 1) * (8 : Fin KB)⁻¹) < 8192 ∧
      cols.clk_16_24 < 256
    := by simp_all [allHold_constraints_iff]

/-- Polymorphic companion of `allHold_constraints_iff`. RHS is stated in
`.val`-level Nat-arithmetic form (matching simp's natural output after
`SP1Constraint.toProp_poly`) rather than the field-level `<` form of the
`Fin KB` version. At `p := KB` the two forms are definitionally equal, but
for generic `p` the `.val`-level shape avoids spurious `val_*_zmod_p`
rewrites at the chip-consumer site. -/
lemma allHold_constraints_iff_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    [Fact (2 ^ 17 < p)]
    {cols : CPUState (ZMod p)} {next_pc : Vector (ZMod p) 3}
    {clk_increment is_real : ZMod p} :
  List.Forall SP1Constraint.toProp_poly (constraints cols next_pc clk_increment is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_real = 0 →
      ((cols.clk_0_16 - (1 : ZMod p)) * (8 : ZMod p)⁻¹).val < 8192 ∧
      cols.clk_16_24 < (256 : ZMod p))
   := by
    have h13 : (13 : ZMod p).val = 13 := by
      have := (Fact.out : 2 ^ 17 < p)
      exact ZMod.val_natCast_of_lt (show (13 : ℕ) < p by omega)
    have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
      change (0 : ZMod p).val < (256 : ZMod p).val
      simp
    simp [constraints, SP1Constraint.toProp_poly, sub_eq_zero, h13, h0_lt_256, imp_and]

lemma allHold_constraints_iff_is_real_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    [Fact (2 ^ 17 < p)]
    {cols : CPUState (ZMod p)} {next_pc : Vector (ZMod p) 3}
    {clk_increment is_real : ZMod p}
    (h : is_real = 1) :
  List.Forall SP1Constraint.toProp_poly (constraints cols next_pc clk_increment is_real) ↔
      ((cols.clk_0_16 - (1 : ZMod p)) * (8 : ZMod p)⁻¹).val < 8192 ∧
      cols.clk_16_24 < (256 : ZMod p)
    := by simp_all [allHold_constraints_iff_poly]

end CPUState
