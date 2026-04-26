import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadHalf

section constraints

-- Generated Lean code for chip LoadHalfChip
@[irreducible] def constraints (Main : Vector (Fin KB) 44) : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := Main[1] * 65536
  let E1 : Fin KB := Main[2] + E0
  let E2 : Fin KB := 30 * Main[42]
  let E3 : Fin KB := 33 * Main[43]
  let E4 : Fin KB := E2 + E3
  let E5 : Fin KB := Main[42] * 1
  let E6 : Fin KB := Main[43] * 5
  let E7 : Fin KB := E5 + E6
  let E8 : Fin KB := Main[42] * 0
  let E9 : Fin KB := Main[43] * 0
  let E10 : Fin KB := E8 + E9
  let E11 : Fin KB := Main[42] * 3
  let E12 : Fin KB := Main[43] * 3
  let E13 : Fin KB := E11 + E12
  let E14 : Fin KB := Main[42] * 4
  let E15 : Fin KB := Main[43] * 4
  let E16 : Fin KB := E14 + E15
  let E17 : Fin KB := Main[42] + Main[43]
  let E18 : Fin KB := Main[42] - 1
  let E19 : Fin KB := Main[42] * E18
  let E20 : Fin KB := Main[43] - 1
  let E21 : Fin KB := Main[43] * E20
  let E22 : Fin KB := E17 - 1
  let E23 : Fin KB := E17 * E22
  let ⟨⟨⟨[E24, E25, E26]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 Main[38] Main[39] E17 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E27 : Fin KB := E1 + 1
  let E28 : Fin KB := E17 - 1
  let E29 : Fin KB := E17 * E28
  let E30 : Fin KB := Main[35] - 1
  let E31 : Fin KB := Main[35] * E30
  let E32 : Fin KB := E17 * E31
  let E33 : Fin KB := Main[0] - Main[33]
  let E34 : Fin KB := Main[35] * E33
  let E35 : Fin KB := E17 * E34
  let E36 : Fin KB := Main[35] * Main[34]
  let E37 : Fin KB := 1 - Main[35]
  let E38 : Fin KB := E37 * Main[33]
  let E39 : Fin KB := E36 + E38
  let E40 : Fin KB := Main[35] * E27
  let E41 : Fin KB := 1 - Main[35]
  let E42 : Fin KB := E41 * Main[0]
  let E43 : Fin KB := E40 + E42
  let E44 : Fin KB := E43 - E39
  let E45 : Fin KB := E44 - 1
  let E46 : Fin KB := Main[37] * 65536
  let E47 : Fin KB := Main[36] + E46
  let E48 : Fin KB := E45 - E47
  let E49 : Fin KB := E17 * E48
  let E50 : Fin KB := Main[38] - 1
  let E51 : Fin KB := Main[39] - 1
  let E52 : Fin KB := Main[40] - Main[29]
  let E53 : Fin KB := E51 * E52
  let E54 : Fin KB := E50 * E53
  let E55 : Fin KB := Main[39] - 1
  let E56 : Fin KB := Main[40] - Main[30]
  let E57 : Fin KB := E55 * E56
  let E58 : Fin KB := Main[38] * E57
  let E59 : Fin KB := Main[38] - 1
  let E60 : Fin KB := Main[40] - Main[31]
  let E61 : Fin KB := Main[39] * E60
  let E62 : Fin KB := E59 * E61
  let E63 : Fin KB := Main[40] - Main[32]
  let E64 : Fin KB := Main[39] * E63
  let E65 : Fin KB := Main[38] * E64
  let E66 : Fin KB := Main[43] * Main[41]
  let CS1 : SP1ConstraintList (Fin KB) := U16MSBOperation.constraints Main[40] { msb := Main[41] } Main[42]
  let E67 : Fin KB := Main[3] + 4
  let CS2 : SP1ConstraintList (Fin KB) := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E67, Main[4], Main[5]] 8 E17
  let E68 : Fin KB := 65535 * Main[41]
  let E69 : Fin KB := 65535 * Main[41]
  let E70 : Fin KB := 65535 * Main[41]
  let CS3 : SP1ConstraintList (Fin KB) := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E16, E13, E7, E10] #v[Main[40], E68, E69, E70] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E17
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ [
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
    (.assertZero E66),
  ]

end constraints

variable (Main : Vector (Fin KB) 44)

def is_lh := Main[42] = 1
def is_lhu := Main[43] = 1

lemma allHold_constraints_iff_of_is_lh (h_is_lh : is_lh Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[25], Main[26], Main[27]] } 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[28] * (Main[26] + Main[27]) = 1) ∧
    ↑((Main[25] - 4 * Main[39] - 2 * Main[38]) * 1864368129) < 8192 ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[40] { msb := Main[41] } 1) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 30
        #v[4, 3, 1, 0] #v[Main[40], 65535 * Main[41], 65535 * Main[41], 65535 * Main[41]]
        { op_a := Main[6],
          op_a_memory :=
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
    ↑Main[36] < 65536 ∧
    Main[37] < 256 ∧
    (SP1Constraint.send
      (AirInteraction.memory Main[33] Main[34] (Main[25] - 4 * Main[39] - 2 * Main[38])
        Main[26] Main[27] Main[29] Main[30] Main[31] Main[32]) 1).toProp ∧
    (SP1Constraint.receive
      (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
        (Main[25] - 4 * Main[39] - 2 * Main[38]) Main[26] Main[27] Main[29] Main[30]
        Main[31] Main[32]) 1).toProp ∧
    Main[43] = 0 ∧ Main[13] = 0 ∧
    (Main[38] = 1 ∨ Main[39] = 1 ∨ Main[40] = Main[29]) ∧
    (Main[38] = 0 ∨ Main[39] = 1 ∨ Main[40] = Main[30]) ∧
    (Main[38] = 1 ∨ Main[39] = 0 ∨ Main[40] = Main[31]) ∧
    (Main[38] = 0 ∨ Main[39] = 0 ∨ Main[40] = Main[32])) := by
  have : Main[42] = 1 := h_is_lh
  by_cases h43 : Main[43] = 0
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h43]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h43]
    intros
    simp_all

lemma allHold_constraints_iff_of_is_lhu (h_is_lhu : is_lhu Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[25], Main[26], Main[27]] } 1) ∧
    (Main[38] = 0 ∨ Main[38] = 1) ∧
    (Main[39] = 0 ∨ Main[39] = 1) ∧
    (Main[28] * (Main[26] + Main[27]) = 1) ∧
    ↑((Main[25] - 4 * Main[39] - 2 * Main[38]) * 1864368129) < 8192 ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[40] { msb := Main[41] } 0) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 33
        #v[4, 3, 5, 0] #v[Main[40], 65535 * Main[41], 65535 * Main[41], 65535 * Main[41]]
        { op_a := Main[6],
          op_a_memory :=
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
    ↑Main[36] < 65536 ∧
    Main[37] < 256 ∧
    (SP1Constraint.send
      (AirInteraction.memory Main[33] Main[34] (Main[25] - 4 * Main[39] - 2 * Main[38])
        Main[26] Main[27] Main[29] Main[30] Main[31] Main[32]) 1).toProp ∧
    (SP1Constraint.receive
      (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
        (Main[25] - 4 * Main[39] - 2 * Main[38]) Main[26] Main[27] Main[29] Main[30]
        Main[31] Main[32]) 1).toProp ∧
    Main[42] = 0 ∧ Main[13] = 0 ∧
    (Main[38] = 1 ∨ Main[39] = 1 ∨ Main[40] = Main[29]) ∧
    (Main[38] = 0 ∨ Main[39] = 1 ∨ Main[40] = Main[30]) ∧
    (Main[38] = 1 ∨ Main[39] = 0 ∨ Main[40] = Main[31]) ∧
    (Main[38] = 0 ∨ Main[39] = 0 ∨ Main[40] = Main[32]) ∧
    Main[41] = 0) := by
  have : Main[43] = 1 := h_is_lhu
  by_cases h42 : Main[42] = 0
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h42]
  · simp [constraints, AddressOperation.constraints, this, sub_eq_zero, h42]
    intros
    simp_all

end LoadHalf

end Load
