import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Store

namespace StoreWord

section constraints

-- Generated Lean code for chip StoreWordChip
@[irreducible] def constraints (Main : Vector (Fin KB) 44) : SP1ConstraintList :=
  let E0 : Fin KB := Main[1] * 65536
  let E1 : Fin KB := Main[2] + E0
  let E2 : Fin KB := Main[43] - 1
  let E3 : Fin KB := Main[43] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 Main[38] Main[43] { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E7 : Fin KB := E1 + 1
  let E8 : Fin KB := Main[43] - 1
  let E9 : Fin KB := Main[43] * E8
  let E10 : Fin KB := Main[35] - 1
  let E11 : Fin KB := Main[35] * E10
  let E12 : Fin KB := Main[43] * E11
  let E13 : Fin KB := Main[0] - Main[33]
  let E14 : Fin KB := Main[35] * E13
  let E15 : Fin KB := Main[43] * E14
  let E16 : Fin KB := Main[35] * Main[34]
  let E17 : Fin KB := 1 - Main[35]
  let E18 : Fin KB := E17 * Main[33]
  let E19 : Fin KB := E16 + E18
  let E20 : Fin KB := Main[35] * E7
  let E21 : Fin KB := 1 - Main[35]
  let E22 : Fin KB := E21 * Main[0]
  let E23 : Fin KB := E20 + E22
  let E24 : Fin KB := E23 - E19
  let E25 : Fin KB := E24 - 1
  let E26 : Fin KB := Main[37] * 65536
  let E27 : Fin KB := Main[36] + E26
  let E28 : Fin KB := E25 - E27
  let E29 : Fin KB := Main[43] * E28
  let E30 : Fin KB := Main[7] - Main[29]
  let E31 : Fin KB := 1 - Main[38]
  let E32 : Fin KB := E30 * E31
  let E33 : Fin KB := Main[29] + E32
  let E34 : Fin KB := Main[39] - E33
  let E35 : Fin KB := Main[8] - Main[30]
  let E36 : Fin KB := 1 - Main[38]
  let E37 : Fin KB := E35 * E36
  let E38 : Fin KB := Main[30] + E37
  let E39 : Fin KB := Main[40] - E38
  let E40 : Fin KB := Main[7] - Main[31]
  let E41 : Fin KB := E40 * Main[38]
  let E42 : Fin KB := Main[31] + E41
  let E43 : Fin KB := Main[41] - E42
  let E44 : Fin KB := Main[8] - Main[32]
  let E45 : Fin KB := E44 * Main[38]
  let E46 : Fin KB := Main[32] + E45
  let E47 : Fin KB := Main[42] - E46
  let E48 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E48, Main[4], Main[5]] 8 Main[43]
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] 38 #v[64, 35, 2, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } Main[43]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E9),
    (.assertZero E12),
    (.assertZero E15),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) Main[43]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) Main[43]),
    (.send (.memory Main[33] Main[34] E4 E5 E6 Main[29] Main[30] Main[31] Main[32]) Main[43]),
    (.receive (.memory Main[0] E7 E4 E5 E6 Main[39] Main[40] Main[41] Main[42]) Main[43]),
    (.assertZero E34),
    (.assertZero E39),
    (.assertZero E43),
    (.assertZero E47),
  ]

end constraints

end StoreWord

end Store
