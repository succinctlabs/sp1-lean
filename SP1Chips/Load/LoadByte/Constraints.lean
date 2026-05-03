import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadByte

section constraints

-- Generated Lean code for chip LoadByteChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 47) : SP1ConstraintList F :=
  let E0 : F := Main[1] * 65536
  let E1 : F := Main[2] + E0
  let E2 : F := 29 * Main[45]
  let E3 : F := 32 * Main[46]
  let E4 : F := E2 + E3
  let E5 : F := Main[45] * 0
  let E6 : F := Main[46] * 4
  let E7 : F := E5 + E6
  let E8 : F := Main[45] * 0
  let E9 : F := Main[46] * 0
  let E10 : F := E8 + E9
  let E11 : F := Main[45] * 3
  let E12 : F := Main[46] * 3
  let E13 : F := E11 + E12
  let E14 : F := Main[45] * 4
  let E15 : F := Main[46] * 4
  let E16 : F := E14 + E15
  let E17 : F := Main[45] + Main[46]
  let E18 : F := Main[45] - 1
  let E19 : F := Main[45] * E18
  let E20 : F := Main[46] - 1
  let E21 : F := Main[46] * E20
  let E22 : F := E17 - 1
  let E23 : F := E17 * E22
  let ⟨⟨⟨[E24, E25, E26]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[38] Main[39] Main[40] E17 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E27 : F := E1 + 1
  let E28 : F := E17 - 1
  let E29 : F := E17 * E28
  let E30 : F := Main[35] - 1
  let E31 : F := Main[35] * E30
  let E32 : F := E17 * E31
  let E33 : F := Main[0] - Main[33]
  let E34 : F := Main[35] * E33
  let E35 : F := E17 * E34
  let E36 : F := Main[35] * Main[34]
  let E37 : F := 1 - Main[35]
  let E38 : F := E37 * Main[33]
  let E39 : F := E36 + E38
  let E40 : F := Main[35] * E27
  let E41 : F := 1 - Main[35]
  let E42 : F := E41 * Main[0]
  let E43 : F := E40 + E42
  let E44 : F := E43 - E39
  let E45 : F := E44 - 1
  let E46 : F := Main[37] * 65536
  let E47 : F := Main[36] + E46
  let E48 : F := E45 - E47
  let E49 : F := E17 * E48
  let E50 : F := Main[39] - 1
  let E51 : F := Main[40] - 1
  let E52 : F := Main[41] - Main[29]
  let E53 : F := E51 * E52
  let E54 : F := E50 * E53
  let E55 : F := Main[40] - 1
  let E56 : F := Main[41] - Main[30]
  let E57 : F := E55 * E56
  let E58 : F := Main[39] * E57
  let E59 : F := Main[39] - 1
  let E60 : F := Main[41] - Main[31]
  let E61 : F := Main[40] * E60
  let E62 : F := E59 * E61
  let E63 : F := Main[41] - Main[32]
  let E64 : F := Main[40] * E63
  let E65 : F := Main[39] * E64
  let E66 : F := Main[41] - Main[42]
  let E67 : F := E66 * ((256 : F)⁻¹)
  let E68 : F := Main[38] * E67
  let E69 : F := 1 - Main[38]
  let E70 : F := E69 * Main[42]
  let E71 : F := E68 + E70
  let E72 : F := Main[43] - E71
  let E73 : F := Main[46] * Main[44]
  let E74 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E74, Main[4], Main[5]] 8 E17
  let E75 : F := 65280 * Main[44]
  let E76 : F := Main[43] + E75
  let E77 : F := 65535 * Main[44]
  let E78 : F := 65535 * Main[44]
  let E79 : F := 65535 * Main[44]
  let CS2 : SP1ConstraintList F := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E16, E13, E7, E10] #v[E76, E77, E78, E79] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E17
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E19),
    (.assertZero E21),
    (.assertZero E23),
    (.assertZero E29),
    (.assertZero E32),
    (.assertZero E35),
    (.assertZero E49),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) E17),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) E17),
    (.send (.memory Main[33] Main[34] E24 E25 E26 Main[29] Main[30] Main[31] Main[32]) E17),
    (.receive (.memory Main[0] E27 E24 E25 E26 Main[29] Main[30] Main[31] Main[32]) E17),
    (.assertZero Main[13]),
    (.assertZero E54),
    (.assertZero E58),
    (.assertZero E62),
    (.assertZero E65),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[42] E67) E17),
    (.assertZero E72),
    (.assertZero E73),
    (.send (.byte (ByteOpcode.ofNat 5) Main[44] Main[43] 0) Main[45]),
  ]

end constraints

variable (Main : Vector (Fin KB) 47)

def is_lb := Main[45] = 1
def is_lbu := Main[46] = 1

lemma allHold_constraints_iff_of_is_lb (h_is_lb : is_lb Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[25], Main[26], Main[27]] } 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[40] = 0 ∨ Main[40] = 1) ∧
    Main[28] * (Main[26] + Main[27]) = 1 ∧
    ↑((Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38]) * (8 : Fin KB)⁻¹) < 8192 ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 29
        #v[4, 3, 0, 0] #v[Main[43] + 65280 * Main[44], 65535 * Main[44], 65535 * Main[44], 65535 * Main[44]]
        { op_a := Main[6], op_a_memory :=
        { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
          access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
          op_a_0 := Main[13], op_b := Main[14],
          op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } 1) ∧
    (Main[35] = 0 ∨ Main[35] = 1) ∧
    (Main[35] = 0 ∨ Main[0] = Main[33]) ∧
    Main[35] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[35]) * Main[0] -
    (Main[35] * Main[34] + (1 - Main[35]) * Main[33]) - 1 = Main[36] + Main[37] * 65536 ∧
    ↑Main[36] < 65536 ∧ Main[37] < 256 ∧
    (SP1Constraint.send (AirInteraction.memory Main[33] Main[34]
      (Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38]) Main[26] Main[27] Main[29]
      Main[30] Main[31] Main[32]) 1).toProp ∧
    (SP1Constraint.receive
    (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
      (Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38]) Main[26] Main[27] Main[29] Main[30] Main[31] Main[32])
    1).toProp ∧
    Main[46] = 0 ∧ Main[13] = 0 ∧
    (Main[39] = 1 ∨ Main[40] = 1 ∨ Main[41] = Main[29]) ∧
    (Main[39] = 0 ∨ Main[40] = 1 ∨ Main[41] = Main[30]) ∧
    (Main[39] = 1 ∨ Main[40] = 0 ∨ Main[41] = Main[31]) ∧
    (Main[39] = 0 ∨ Main[40] = 0 ∨ Main[41] = Main[32]) ∧
    (Main[42] < 256 ∧ (Main[41] - Main[42]) * (256 : Fin KB)⁻¹ < 256) ∧
    Main[43] = Main[38] * ((Main[41] - Main[42]) * (256 : Fin KB)⁻¹) + (1 - Main[38]) * Main[42] ∧
    (Main[44] < 256 ∧ Main[43] < 256) ∧
    (Main[44] = 0 ∨ Main[44] = 1) ∧
    (Main[44] = 1 ↔ (128 : Fin KB) ≤ Main[43])) := by
  have : Main[45] = 1 := h_is_lb
  by_cases h46 : Main[46] = 0
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h46]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h46]
    by_cases h46' : Main[46] = 1
    · simp [h46']
    · simp [h46']

lemma allHold_constraints_iff_of_is_lbu (h_is_lbu : is_lbu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[25], Main[26], Main[27]] } 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[40] = 0 ∨ Main[40] = 1) ∧
    Main[28] * (Main[26] + Main[27]) = 1 ∧
    ↑((Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38]) * (8 : Fin KB)⁻¹) < 8192 ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 32
        #v[4, 3, 4, 0] #v[Main[43] + 65280 * Main[44], 65535 * Main[44], 65535 * Main[44], 65535 * Main[44]]
        { op_a := Main[6], op_a_memory :=
        { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
          access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
          op_a_0 := Main[13], op_b := Main[14],
          op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } 1) ∧
    (Main[35] = 0 ∨ Main[35] = 1) ∧
    (Main[35] = 0 ∨ Main[0] = Main[33]) ∧
    Main[35] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[35]) * Main[0] -
    (Main[35] * Main[34] + (1 - Main[35]) * Main[33]) - 1 = Main[36] + Main[37] * 65536 ∧
    ↑Main[36] < 65536 ∧ Main[37] < 256 ∧
    (SP1Constraint.send (AirInteraction.memory Main[33] Main[34]
      (Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38]) Main[26] Main[27] Main[29]
      Main[30] Main[31] Main[32]) 1).toProp ∧
    (SP1Constraint.receive
    (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
      (Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38]) Main[26] Main[27] Main[29] Main[30] Main[31] Main[32])
    1).toProp ∧
    Main[45] = 0 ∧ Main[13] = 0 ∧
    (Main[39] = 1 ∨ Main[40] = 1 ∨ Main[41] = Main[29]) ∧
    (Main[39] = 0 ∨ Main[40] = 1 ∨ Main[41] = Main[30]) ∧
    (Main[39] = 1 ∨ Main[40] = 0 ∨ Main[41] = Main[31]) ∧
    (Main[39] = 0 ∨ Main[40] = 0 ∨ Main[41] = Main[32]) ∧
    (Main[42] < 256 ∧ (Main[41] - Main[42]) * (256 : Fin KB)⁻¹ < 256) ∧
    Main[43] = Main[38] * ((Main[41] - Main[42]) * (256 : Fin KB)⁻¹) + (1 - Main[38]) * Main[42] ∧
    (Main[44] = 0)) := by
  have : Main[46] = 1 := h_is_lbu
  by_cases h45 : Main[45] = 0
  · simp [h45, constraints, AddressOperation.constraints, this, sub_eq_zero]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h45]
    by_cases h45' : Main[45] = 1
    · simp [h45']
    · simp [h45']

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_lb_poly (Main : Vector (ZMod p) 47) : Prop := Main[45] = 1
@[simp] def is_lbu_poly (Main : Vector (ZMod p) 47) : Prop := Main[46] = 1

end poly_helpers

end LoadByte

end Load
