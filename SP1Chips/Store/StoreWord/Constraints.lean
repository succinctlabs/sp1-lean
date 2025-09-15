import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Store

namespace StoreWord

section constraints

-- Generated Lean code for chip StoreWordChip
def constraints (Main : Vector (Fin BB) 46) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := Main[44] - 1
  let E3 : Fin BB := Main[44] * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] 0 0 Main[39] Main[44] { addr_operation := { value := #v[Main[26], Main[27], Main[28]] }, top_two_limb_inv := Main[29] }
  let E7 : Fin BB := E1 + 1
  let E8 : Fin BB := Main[44] - 1
  let E9 : Fin BB := Main[44] * E8
  let E10 : Fin BB := Main[36] - 1
  let E11 : Fin BB := Main[36] * E10
  let E12 : Fin BB := Main[44] * E11
  let E13 : Fin BB := Main[0] - Main[34]
  let E14 : Fin BB := Main[36] * E13
  let E15 : Fin BB := Main[44] * E14
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
  let E29 : Fin BB := Main[44] * E28
  let E30 : Fin BB := mprotect_enabled () * Main[44]
  let E31 : Fin BB := Main[45] - E30
  let E32 : Fin BB := E1 + 1
  let E33 : Fin BB := Main[7] - Main[30]
  let E34 : Fin BB := 1 - Main[39]
  let E35 : Fin BB := E33 * E34
  let E36 : Fin BB := Main[30] + E35
  let E37 : Fin BB := Main[40] - E36
  let E38 : Fin BB := Main[8] - Main[31]
  let E39 : Fin BB := 1 - Main[39]
  let E40 : Fin BB := E38 * E39
  let E41 : Fin BB := Main[31] + E40
  let E42 : Fin BB := Main[41] - E41
  let E43 : Fin BB := Main[7] - Main[32]
  let E44 : Fin BB := E43 * Main[39]
  let E45 : Fin BB := Main[32] + E44
  let E46 : Fin BB := Main[42] - E45
  let E47 : Fin BB := Main[8] - Main[33]
  let E48 : Fin BB := E47 * Main[39]
  let E49 : Fin BB := Main[33] + E48
  let E50 : Fin BB := Main[43] - E49
  let E51 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E51, Main[4], Main[5]] 8 Main[44]
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] 26 #v[64, 35, 2, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]], is_trusted := Main[25] } Main[44]
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E9),
    (.assertZero E12),
    (.assertZero E15),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[37] 16 0) Main[44]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[38] 0) Main[44]),
    (.send (.memory Main[34] Main[35] E4 E5 E6 Main[30] Main[31] Main[32] Main[33]) Main[44]),
    (.receive (.memory Main[0] E7 E4 E5 E6 Main[40] Main[41] Main[42] Main[43]) Main[44]),
    (.assertZero E31),
    (.assertZero E37),
    (.assertZero E42),
    (.assertZero E46),
    (.assertZero E50),
  ]

end constraints

end StoreWord

end Store
