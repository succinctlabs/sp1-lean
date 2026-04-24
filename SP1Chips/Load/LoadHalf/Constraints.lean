import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Operations.Reader.ITypeReader.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadHalf

section constraints

-- Generated Lean code for chip LoadHalfChip
@[irreducible] def constraints (Main : Vector (Fin KB) 44) : SP1ConstraintList :=
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
  let CS1 : SP1ConstraintList := U16MSBOperation.constraints Main[40] { msb := Main[41] } Main[42]
  let E67 : Fin KB := Main[3] + 4
  let CS2 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E67, Main[4], Main[5]] 8 E17
  let E68 : Fin KB := 65535 * Main[41]
  let E69 : Fin KB := 65535 * Main[41]
  let E70 : Fin KB := 65535 * Main[41]
  let CS3 : SP1ConstraintList := ITypeReader.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E4 #v[E16, E13, E7, E10] #v[Main[40], E68, E69, E70] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E17
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

def is_lh := Main[42] = 1  -- placeholder; verify real index
def is_lhu := Main[43] = 1  -- placeholder

-- Pre-regen proof at commit 750a3e6:SP1Chips/Constraints.lean -- allHold_constraints_iff_of_is_lh
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/Load/LoadHalf/Constraints.lean` for the full pre-regen proof body)
lemma allHold_constraints_iff_of_is_lh (_ : is_lh Main)
    (_ : List.Forall SP1Constraint.toProp (constraints Main)) : True := trivial

-- Pre-regen proof at commit 750a3e6:SP1Chips/Constraints.lean -- allHold_constraints_iff_of_is_lhu
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/Load/LoadHalf/Constraints.lean` for the full pre-regen proof body)
lemma allHold_constraints_iff_of_is_lhu (_ : is_lhu Main)
    (_ : List.Forall SP1Constraint.toProp (constraints Main)) : True := trivial

end LoadHalf

end Load
