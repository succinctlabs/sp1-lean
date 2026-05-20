import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Load

namespace LoadDouble


section constraints

-- Generated Lean code for chip LoadDoubleChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 39) : SP1ConstraintList F :=
  let E0 : F := Main[1] * 65536
  let E1 : F := Main[2] + E0
  let E2 : F := Main[38] - 1
  let E3 : F := Main[38] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 0 Main[38] { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E7 : F := E1 + 1
  let E8 : F := Main[38] - 1
  let E9 : F := Main[38] * E8
  let E10 : F := Main[35] - 1
  let E11 : F := Main[35] * E10
  let E12 : F := Main[38] * E11
  let E13 : F := Main[0] - Main[33]
  let E14 : F := Main[35] * E13
  let E15 : F := Main[38] * E14
  let E16 : F := Main[35] * Main[34]
  let E17 : F := 1 - Main[35]
  let E18 : F := E17 * Main[33]
  let E19 : F := E16 + E18
  let E20 : F := Main[35] * E7
  let E21 : F := 1 - Main[35]
  let E22 : F := E21 * Main[0]
  let E23 : F := E20 + E22
  let E24 : F := E23 - E19
  let E25 : F := E24 - 1
  let E26 : F := Main[37] * 65536
  let E27 : F := Main[36] + E26
  let E28 : F := E25 - E27
  let E29 : F := Main[38] * E28
  let E30 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E30, Main[4], Main[5]] 8 Main[38]
  let CS2 : SP1ConstraintList F := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] 35 #v[Main[29], Main[30], Main[31], Main[32]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } Main[38] Main[38]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E9),
    (.assertZero E12),
    (.assertZero E15),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) Main[38]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) Main[38]),
    (.send (.memory Main[33] Main[34] E4 E5 E6 Main[29] Main[30] Main[31] Main[32]) Main[38]),
    (.receive (.memory Main[0] E7 E4 E5 E6 Main[29] Main[30] Main[31] Main[32]) Main[38]),
    (.assertZero Main[13]),
  ]

end constraints

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_ld_poly (Main : Vector (ZMod p) 39) : Prop := Main[38] = 1

set_option maxHeartbeats 800000 in
-- Range bounds are stated as `.val < N` (Nat-level) and `< (256 : ZMod p)`
-- (field-level) depending on which form the surrounding `_poly` predicates use.
lemma allHold_constraints_iff_of_is_ld_poly (Main : Vector (ZMod p) 39)
    (h_is_ld : is_ld_poly Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]]
        { value := #v[Main[25], Main[26], Main[27]] } 1) ∧
    Main[28] * (Main[26] + Main[27]) = 1 ∧
    (Main[25] * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
        #v[Main[3], Main[4], Main[5]] 35
        #v[Main[29], Main[30], Main[31], Main[32]]
        { op_a := Main[6], op_a_memory :=
        { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
          access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
          op_a_0 := Main[13], op_b := Main[14],
          op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } 1 1) ∧
    (Main[35] = 0 ∨ Main[35] = 1) ∧
    (Main[35] = 0 ∨ Main[0] = Main[33]) ∧
    Main[35] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[35]) * Main[0] -
    (Main[35] * Main[34] + (1 - Main[35]) * Main[33]) - 1 = Main[36] + Main[37] * 65536 ∧
    Main[36].val < 65536 ∧
    ((0 : ZMod p) < 256 ∧ Main[37] < (256 : ZMod p) ∧ (0 : ZMod p) < 256) ∧
    Word.isU64_poly #v[Main[29], Main[30], Main[31], Main[32]] ∧
    Main[13] = 0) := by
  have : Main[38] = 1 := h_is_ld
  simp [constraints, AddressOperation.constraints, this, sub_eq_zero,
    SP1Constraint.toProp]

end poly_helpers

end LoadDouble

end Load
