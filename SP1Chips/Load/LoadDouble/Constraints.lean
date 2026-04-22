import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadDouble

section constraints

-- Generated Lean code for chip LoadDoubleChip
@[irreducible] def constraints (Main : Vector (Fin KB) 41) : SP1ConstraintList :=
  let E0 : Fin KB := Main[1] * 65536
  let E1 : Fin KB := Main[2] + E0
  let E2 : Fin KB := Main[39] - 1
  let E3 : Fin KB := Main[39] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 0 Main[39] { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E7 : Fin KB := E1 + 1
  let E8 : Fin KB := Main[39] - 1
  let E9 : Fin KB := Main[39] * E8
  let E10 : Fin KB := Main[36] - 1
  let E11 : Fin KB := Main[36] * E10
  let E12 : Fin KB := Main[39] * E11
  let E13 : Fin KB := Main[0] - Main[34]
  let E14 : Fin KB := Main[36] * E13
  let E15 : Fin KB := Main[39] * E14
  let E16 : Fin KB := Main[36] * Main[35]
  let E17 : Fin KB := 1 - Main[36]
  let E18 : Fin KB := E17 * Main[34]
  let E19 : Fin KB := E16 + E18
  let E20 : Fin KB := Main[36] * E7
  let E21 : Fin KB := 1 - Main[36]
  let E22 : Fin KB := E21 * Main[0]
  let E23 : Fin KB := E20 + E22
  let E24 : Fin KB := E23 - E19
  let E25 : Fin KB := E24 - 1
  let E26 : Fin KB := Main[38] * 65536
  let E27 : Fin KB := Main[37] + E26
  let E28 : Fin KB := E25 - E27
  let E29 : Fin KB := Main[39] * E28
  let E30 : Fin KB := public_value () 151 * Main[39]
  let E31 : Fin KB := Main[40] - E30
  let E32 : Fin KB := E1 + 1
  let E33 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E33, Main[4], Main[5]] 8 Main[39]
  let CS2 : SP1ConstraintList := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] 45 #v[4, 3, 3, 0] #v[Main[30], Main[31], Main[32], Main[33]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } Main[39]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E9),
    (.assertZero E12),
    (.assertZero E15),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[37] 16 0) Main[39]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[38] 0) Main[39]),
    (.send (.memory Main[34] Main[35] E4 E5 E6 Main[30] Main[31] Main[32] Main[33]) Main[39]),
    (.receive (.memory Main[0] E7 E4 E5 E6 Main[30] Main[31] Main[32] Main[33]) Main[39]),
    (.assertZero E31),
    (.assertZero Main[13]),
  ]

end constraints

variable (Main : Vector (Fin KB) 41)

def is_ld := Main[39] = 1

lemma allHold_constraints_iff_of_is_ld (h_is_ld : is_ld Main) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    (List.Forall SP1Constraint.toProp
      (AddrAddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[26], Main[27], Main[28]] } 1) ∧
    Main[29] * (Main[27] + Main[28]) = 1 ∧
    ↑(Main[26] * 1864368129) < 8192 ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 1) ∧
    List.Forall SP1Constraint.toProp
      (ITypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 45
        #v[4, 3, 3, 0] #v[Main[30], Main[31], Main[32], Main[33]]
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
      Main[26] Main[27] Main[28] Main[30]
      Main[31] Main[32] Main[33]) 1).toProp ∧
    (SP1Constraint.receive
    (AirInteraction.memory Main[0] (Main[2] + Main[1] * 65536 + 1)
      Main[26] Main[27] Main[28] Main[30] Main[31] Main[32] Main[33])
    1).toProp ∧
    Main[40] = 0 ∧ Main[13] = 0) := by
  have : Main[39] = 1 := h_is_ld
  simp [constraints, AddressOperation.constraints, this, sub_eq_zero]

end LoadDouble

end Load
