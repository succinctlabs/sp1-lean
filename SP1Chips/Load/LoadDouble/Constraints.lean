import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadDouble

section constraints

-- Generated Lean code for chip LoadDoubleChip
def constraints (Main : Vector (Fin BB) 41) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := Main[39] - 1
  let E3 : Fin BB := Main[39] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 0 Main[39] { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E7 : Fin BB := E1 + 1
  let E8 : Fin BB := Main[39] - 1
  let E9 : Fin BB := Main[39] * E8
  let E10 : Fin BB := Main[36] - 1
  let E11 : Fin BB := Main[36] * E10
  let E12 : Fin BB := Main[39] * E11
  let E13 : Fin BB := Main[0] - Main[34]
  let E14 : Fin BB := Main[36] * E13
  let E15 : Fin BB := Main[39] * E14
  let E16 : Fin BB := Main[36] * Main[35]
  let E17 : Fin BB := 1 - Main[36]
  let E18 : Fin BB := E17 * Main[34]
  let E19 : Fin BB := E16 + E18
  let E20 : Fin BB := Main[36] * E7
  let E21 : Fin BB := 1 - Main[36]
  let E22 : Fin BB := E21 * Main[0]
  let E23 : Fin BB := E20 + E22
  let E24 : Fin BB := E23 - E19
  let E25 : Fin BB := E24 - 1
  let E26 : Fin BB := Main[38] * 65536
  let E27 : Fin BB := Main[37] + E26
  let E28 : Fin BB := E25 - E27
  let E29 : Fin BB := Main[39] * E28
  let E30 : Fin BB := mprotect_enabled () * Main[39]
  let E31 : Fin BB := Main[40] - E30
  let E32 : Fin BB := E1 + 1
  let E33 : Fin BB := Main[3] + 4
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

end LoadDouble

end Load
