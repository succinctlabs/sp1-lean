import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Store

namespace StoreHalf

section constraints

-- Generated Lean code for chip StoreHalfChip
def constraints (Main : Vector (Fin BB) 45) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1]$ * 65536
  let E1 : Fin BB := Main[2]$ + E0
  let E2 : Fin BB := Main[44]$ - 1
  let E3 : Fin BB := Main[44]$ * E2
  let ⟨⟨⟨[E4, E5, E6]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$] #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$] 0 Main[38]$ Main[39]$ Main[44]$ { addr_operation := { value := #v[Main[25]$, Main[26]$, Main[27]$] }, top_two_limb_inv := Main[28]$ }
  let E7 : Fin BB := Main[44]$ - 1
  let E8 : Fin BB := Main[44]$ * E7
  let E9 : Fin BB := Main[35]$ - 1
  let E10 : Fin BB := Main[35]$ * E9
  let E11 : Fin BB := Main[44]$ * E10
  let E12 : Fin BB := Main[0]$ - Main[33]$
  let E13 : Fin BB := Main[35]$ * E12
  let E14 : Fin BB := Main[44]$ * E13
  let E15 : Fin BB := Main[35]$ * Main[34]$
  let E16 : Fin BB := 1 - Main[35]$
  let E17 : Fin BB := E16 * Main[33]$
  let E18 : Fin BB := E15 + E17
  let E19 : Fin BB := Main[35]$ * E1
  let E20 : Fin BB := 1 - Main[35]$
  let E21 : Fin BB := E20 * Main[0]$
  let E22 : Fin BB := E19 + E21
  let E23 : Fin BB := E22 - E18
  let E24 : Fin BB := E23 - 1
  let E25 : Fin BB := Main[37]$ * 65536
  let E26 : Fin BB := Main[36]$ + E25
  let E27 : Fin BB := E24 - E26
  let E28 : Fin BB := Main[44]$ * E27
  let E29 : Fin BB := Main[7]$ - Main[29]$
  let E30 : Fin BB := 1 - Main[38]$
  let E31 : Fin BB := E29 * E30
  let E32 : Fin BB := 1 - Main[39]$
  let E33 : Fin BB := E31 * E32
  let E34 : Fin BB := Main[29]$ + E33
  let E35 : Fin BB := Main[40]$ - E34
  let E36 : Fin BB := Main[7]$ - Main[30]$
  let E37 : Fin BB := E36 * Main[38]$
  let E38 : Fin BB := 1 - Main[39]$
  let E39 : Fin BB := E37 * E38
  let E40 : Fin BB := Main[30]$ + E39
  let E41 : Fin BB := Main[41]$ - E40
  let E42 : Fin BB := Main[7]$ - Main[31]$
  let E43 : Fin BB := 1 - Main[38]$
  let E44 : Fin BB := E42 * E43
  let E45 : Fin BB := E44 * Main[39]$
  let E46 : Fin BB := Main[31]$ + E45
  let E47 : Fin BB := Main[42]$ - E46
  let E48 : Fin BB := Main[7]$ - Main[32]$
  let E49 : Fin BB := E48 * Main[38]$
  let E50 : Fin BB := E49 * Main[39]$
  let E51 : Fin BB := Main[32]$ + E50
  let E52 : Fin BB := Main[43]$ - E51
  let E53 : Fin BB := Main[3]$ + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0]$, clk_16_24 := Main[1]$, clk_0_16 := Main[2]$, pc := #v[Main[3]$, Main[4]$, Main[5]$] } #v[E53, Main[4]$, Main[5]$] 8 Main[44]$
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0]$ E1 #v[Main[3]$, Main[4]$, Main[5]$] 25 #v[35, 1, 0] { op_a := Main[6]$, op_a_memory := { prev_value := #v[Main[7]$, Main[8]$, Main[9]$, Main[10]$], access_timestamp := { prev_low := Main[11]$, diff_low_limb := Main[12]$ } }, op_a_0 := Main[13]$, op_b := Main[14]$, op_b_memory := { prev_value := #v[Main[15]$, Main[16]$, Main[17]$, Main[18]$], access_timestamp := { prev_low := Main[19]$, diff_low_limb := Main[20]$ } }, op_c_imm := #v[Main[21]$, Main[22]$, Main[23]$, Main[24]$] } Main[44]$
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E3),
    (.assertZero E8),
    (.assertZero E11),
    (.assertZero E14),
    (.assertZero E28),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36]$ 16 0) Main[44]$),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37]$ 0) Main[44]$),
    (.send (.memory Main[33]$ Main[34]$ E4 E5 E6 Main[29]$ Main[30]$ Main[31]$ Main[32]$) Main[44]$),
    (.receive (.memory Main[0]$ E1 E4 E5 E6 Main[40]$ Main[41]$ Main[42]$ Main[43]$) Main[44]$),
    (.assertZero E35),
    (.assertZero E41),
    (.assertZero E47),
    (.assertZero E52),
  ]

end constraints

end StoreHalf

end Store
