import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadByte

section constraints

-- Generated Lean code for chip LoadByteChip
@[irreducible] def constraints (Main : Vector (Fin KB) 49) : SP1ConstraintList :=
  let E0 : Fin KB := Main[1] * 65536
  let E1 : Fin KB := Main[2] + E0
  let E2 : Fin KB := 19 * Main[46]
  let E3 : Fin KB := 22 * Main[47]
  let E4 : Fin KB := E2 + E3
  let E5 : Fin KB := Main[46] * 0
  let E6 : Fin KB := Main[47] * 4
  let E7 : Fin KB := E5 + E6
  let E8 : Fin KB := Main[46] * 0
  let E9 : Fin KB := Main[47] * 0
  let E10 : Fin KB := E8 + E9
  let E11 : Fin KB := Main[46] * 3
  let E12 : Fin KB := Main[47] * 3
  let E13 : Fin KB := E11 + E12
  let E14 : Fin KB := Main[46] * 4
  let E15 : Fin KB := Main[47] * 4
  let E16 : Fin KB := E14 + E15
  let E17 : Fin KB := Main[46] + Main[47]
  let E18 : Fin KB := Main[46] - 1
  let E19 : Fin KB := Main[46] * E18
  let E20 : Fin KB := Main[47] - 1
  let E21 : Fin KB := Main[47] * E20
  let E22 : Fin KB := E17 - 1
  let E23 : Fin KB := E17 * E22
  let ⟨⟨⟨[E24, E25, E26]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[39] Main[40] Main[41] E17 { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E27 : Fin KB := E1 + 1
  let E28 : Fin KB := E17 - 1
  let E29 : Fin KB := E17 * E28
  let E30 : Fin KB := Main[36] - 1
  let E31 : Fin KB := Main[36] * E30
  let E32 : Fin KB := E17 * E31
  let E33 : Fin KB := Main[0] - Main[34]
  let E34 : Fin KB := Main[36] * E33
  let E35 : Fin KB := E17 * E34
  let E36 : Fin KB := Main[36] * Main[35]
  let E37 : Fin KB := 1 - Main[36]
  let E38 : Fin KB := E37 * Main[34]
  let E39 : Fin KB := E36 + E38
  let E40 : Fin KB := Main[36] * E27
  let E41 : Fin KB := 1 - Main[36]
  let E42 : Fin KB := E41 * Main[0]
  let E43 : Fin KB := E40 + E42
  let E44 : Fin KB := E43 - E39
  let E45 : Fin KB := E44 - 1
  let E46 : Fin KB := Main[38] * 65536
  let E47 : Fin KB := Main[37] + E46
  let E48 : Fin KB := E45 - E47
  let E49 : Fin KB := E17 * E48
  let E50 : Fin KB := public_value () 151 * E17
  let E51 : Fin KB := Main[48] - E50
  let E52 : Fin KB := E1 + 1
  let E53 : Fin KB := Main[40] - 1
  let E54 : Fin KB := Main[41] - 1
  let E55 : Fin KB := Main[42] - Main[30]
  let E56 : Fin KB := E54 * E55
  let E57 : Fin KB := E53 * E56
  let E58 : Fin KB := Main[41] - 1
  let E59 : Fin KB := Main[42] - Main[31]
  let E60 : Fin KB := E58 * E59
  let E61 : Fin KB := Main[40] * E60
  let E62 : Fin KB := Main[40] - 1
  let E63 : Fin KB := Main[42] - Main[32]
  let E64 : Fin KB := Main[41] * E63
  let E65 : Fin KB := E62 * E64
  let E66 : Fin KB := Main[42] - Main[33]
  let E67 : Fin KB := Main[41] * E66
  let E68 : Fin KB := Main[40] * E67
  let E69 : Fin KB := Main[42] - Main[43]
  let E70 : Fin KB := E69 * 2122383361
  let E71 : Fin KB := Main[39] * E70
  let E72 : Fin KB := 1 - Main[39]
  let E73 : Fin KB := E72 * Main[43]
  let E74 : Fin KB := E71 + E73
  let E75 : Fin KB := Main[44] - E74
  let E76 : Fin KB := Main[47] * Main[45]
  let E77 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E77, Main[4], Main[5]] 8 E17
  let E78 : Fin KB := 65280 * Main[45]
  let E79 : Fin KB := Main[44] + E78
  let E80 : Fin KB := 65535 * Main[45]
  let E81 : Fin KB := 65535 * Main[45]
  let E82 : Fin KB := 65535 * Main[45]
  let CS2 : SP1ConstraintList := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E16, E13, E7, E10] #v[E79, E80, E81, E82] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } E17
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E19),
    (.assertZero E21),
    (.assertZero E23),
    (.assertZero E29),
    (.assertZero E32),
    (.assertZero E35),
    (.assertZero E49),
    (.send (.byte (ByteOpcode.ofNat 6) Main[37] 16 0) E17),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[38] 0) E17),
    (.send (.memory Main[34] Main[35] E24 E25 E26 Main[30] Main[31] Main[32] Main[33]) E17),
    (.receive (.memory Main[0] E27 E24 E25 E26 Main[30] Main[31] Main[32] Main[33]) E17),
    (.assertZero E51),
    (.assertZero Main[13]),
    (.assertZero E57),
    (.assertZero E61),
    (.assertZero E65),
    (.assertZero E68),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[43] E70) E17),
    (.assertZero E75),
    (.assertZero E76),
    (.send (.byte (ByteOpcode.ofNat 5) Main[45] Main[44] 0) Main[46]),
  ]

end constraints

variable (Main : Vector (Fin KB) 49)

def is_lb := Main[46] = 1
def is_lbu := Main[47] = 1

lemma allHold_constraints_iff_of_is_lb (h_is_lb : is_lb Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[26], Main[27], Main[28]] } 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[40] = 0 ∨ Main[40] = 1) ∧
    (Main[41] = 0 ∨ Main[41] = 1) ∧
    Main[29] * (Main[27] + Main[28]) = 1 ∧
    ↑((Main[26] - 4 * Main[41] - 2 * Main[40] - Main[39]) * 1864368129) < 8192 ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 19
        #v[4, 3, 0, 0] #v[Main[44] + 65280 * Main[45], 65535 * Main[45], 65535 * Main[45], 65535 * Main[45]]
        { op_a := Main[6], op_a_memory :=
        { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
          access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
          op_a_0 := Main[13], op_b := Main[14],
          op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } 1) ∧
    (Main[36] = 0 ∨ Main[36] = 1) ∧
    (Main[36] = 0 ∨ Main[0] = Main[34]) ∧
    Main[36] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[36]) * Main[0] -
    (Main[36] * Main[35] + (1 - Main[36]) * Main[34]) - 1 = Main[37] + Main[38] * 65536 ∧
    ↑Main[37] < 65536 ∧ Main[38] < 256 ∧
    (SP1Constraint.send (AirInteraction.memory Main[34] Main[35]
      (Main[26] - 4 * Main[41] - 2 * Main[40] - Main[39]) Main[27] Main[28] Main[30]
      Main[31] Main[32] Main[33]) 1).toProp ∧
    (SP1Constraint.receive
    (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
      (Main[26] - 4 * Main[41] - 2 * Main[40] - Main[39]) Main[27] Main[28] Main[30] Main[31] Main[32] Main[33])
    1).toProp ∧
    Main[47] = 0 ∧ Main[48] = 0 ∧ Main[13] = 0 ∧
    (Main[40] = 1 ∨ Main[41] = 1 ∨ Main[42] = Main[30]) ∧
    (Main[40] = 0 ∨ Main[41] = 1 ∨ Main[42] = Main[31]) ∧
    (Main[40] = 1 ∨ Main[41] = 0 ∨ Main[42] = Main[32]) ∧
    (Main[40] = 0 ∨ Main[41] = 0 ∨ Main[42] = Main[33]) ∧
    (Main[43] < 256 ∧ (Main[42] - Main[43]) * 2122383361 < 256) ∧
    Main[44] = Main[39] * ((Main[42] - Main[43]) * 2122383361) + (1 - Main[39]) * Main[43] ∧
    (Main[45] < 256 ∧ Main[44] < 256) ∧
    (Main[45] = 0 ∨ Main[45] = 1) ∧
    (Main[45] = 1 ↔ (128 : Fin KB) ≤ Main[44])) := by
  have : Main[46] = 1 := h_is_lb
  by_cases h47 : Main[47] = 0
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h47]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h47]
    by_cases h47' : Main[47] = 1
    · simp [h47']
    · simp [h47']

lemma allHold_constraints_iff_of_is_lbu (h_is_lbu : is_lbu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[26], Main[27], Main[28]] } 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[40] = 0 ∨ Main[40] = 1) ∧
    (Main[41] = 0 ∨ Main[41] = 1) ∧
    Main[29] * (Main[27] + Main[28]) = 1 ∧
    ↑((Main[26] - 4 * Main[41] - 2 * Main[40] - Main[39]) * 1864368129) < 8192 ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 22
        #v[4, 3, 4, 0] #v[Main[44], 0, 0, 0]
        { op_a := Main[6], op_a_memory :=
        { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
          access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
          op_a_0 := Main[13], op_b := Main[14],
          op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } 1) ∧
    (Main[36] = 0 ∨ Main[36] = 1) ∧
    (Main[36] = 0 ∨ Main[0] = Main[34]) ∧
    Main[36] * (Main[2] + Main[1] * 65536 + 1) + (1 - Main[36]) * Main[0] -
    (Main[36] * Main[35] + (1 - Main[36]) * Main[34]) - 1 = Main[37] + Main[38] * 65536 ∧
    ↑Main[37] < 65536 ∧ Main[38] < 256 ∧
    (SP1Constraint.send (AirInteraction.memory Main[34] Main[35]
      (Main[26] - 4 * Main[41] - 2 * Main[40] - Main[39]) Main[27] Main[28] Main[30]
      Main[31] Main[32] Main[33]) 1).toProp ∧
    (SP1Constraint.receive
    (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
      (Main[26] - 4 * Main[41] - 2 * Main[40] - Main[39]) Main[27] Main[28] Main[30] Main[31] Main[32] Main[33])
    1).toProp ∧
    Main[46] = 0 ∧ Main[48] = 0 ∧ Main[13] = 0 ∧
    (Main[40] = 1 ∨ Main[41] = 1 ∨ Main[42] = Main[30]) ∧
    (Main[40] = 0 ∨ Main[41] = 1 ∨ Main[42] = Main[31]) ∧
    (Main[40] = 1 ∨ Main[41] = 0 ∨ Main[42] = Main[32]) ∧
    (Main[40] = 0 ∨ Main[41] = 0 ∨ Main[42] = Main[33]) ∧
    (Main[43] < 256 ∧ (Main[42] - Main[43]) * 2122383361 < 256) ∧
    Main[44] = Main[39] * ((Main[42] - Main[43]) * 2122383361) + (1 - Main[39]) * Main[43] ∧
    (Main[44] < 256) ∧
    (Main[45] = 0)) := by
  have : Main[47] = 1 := h_is_lbu
  by_cases h46 : Main[46] = 0
  · by_cases h45 : Main[45] = 0
    · simp [h45, h46, constraints, AddressOperation.constraints, this, sub_eq_zero]
      intros
      have : Main[39] = 0 ∨ Main[39] = 1 := by simp_all only
      cases this <;> simp_all
    · simp [h45, h46, constraints, AddressOperation.constraints, this, sub_eq_zero]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h46]
    by_cases h46' : Main[46] = 1
    · simp [h46']
    · simp [h46']

end LoadByte

end Load
