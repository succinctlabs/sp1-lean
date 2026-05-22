import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader

namespace Mul

set_option linter.style.setOption false
set_option linter.style.longLine false

section constraints

-- Generated Lean code for chip MulChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 82) : SP1ConstraintList F :=
  let E0 : F := Main[77] + Main[78]
  let E1 : F := E0 + Main[79]
  let E2 : F := E1 + Main[80]
  let E3 : F := E2 + Main[81]
  let CS0 : SP1ConstraintList F := MulOperation.constraints #v[Main[28], Main[29], Main[30], Main[31]] #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { carry := #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]], product := #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54], Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61], Main[62], Main[63]], b_lower_byte := { low_bytes := #v[Main[64], Main[65], Main[66], Main[67]] }, c_lower_byte := { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] }, b_msb := Main[72], c_msb := Main[73], product_msb := { msb := Main[74] }, b_sign_extend := Main[75], c_sign_extend := Main[76] } E3 Main[77] Main[78] Main[81] Main[79] Main[80]
  let E4 : F := Main[77] - 1
  let E5 : F := Main[77] * E4
  let E6 : F := Main[78] - 1
  let E7 : F := Main[78] * E6
  let E8 : F := Main[79] - 1
  let E9 : F := Main[79] * E8
  let E10 : F := Main[81] - 1
  let E11 : F := Main[81] * E10
  let E12 : F := Main[80] - 1
  let E13 : F := Main[80] * E12
  let E14 : F := E3 - 1
  let E15 : F := E3 * E14
  let E16 : F := Main[77] * 11
  let E17 : F := Main[78] * 12
  let E18 : F := E16 + E17
  let E19 : F := Main[79] * 13
  let E20 : F := E18 + E19
  let E21 : F := Main[80] * 14
  let E22 : F := E20 + E21
  let E23 : F := Main[81] * 24
  let E24 : F := E22 + E23
  let E25 : F := Main[77] * 0
  let E26 : F := Main[78] * 1
  let E27 : F := E25 + E26
  let E28 : F := Main[79] * 3
  let E29 : F := E27 + E28
  let E30 : F := Main[80] * 2
  let E31 : F := E29 + E30
  let E32 : F := Main[81] * 0
  let E33 : F := E31 + E32
  let E34 : F := Main[77] * 1
  let E35 : F := Main[78] * 1
  let E36 : F := E34 + E35
  let E37 : F := Main[79] * 1
  let E38 : F := E36 + E37
  let E39 : F := Main[80] * 1
  let E40 : F := E38 + E39
  let E41 : F := Main[81] * 1
  let E42 : F := E40 + E41
  let E43 : F := Main[77] * 51
  let E44 : F := Main[78] * 51
  let E45 : F := E43 + E44
  let E46 : F := Main[79] * 51
  let E47 : F := E45 + E46
  let E48 : F := Main[80] * 51
  let E49 : F := E47 + E48
  let E50 : F := Main[81] * 59
  let E51 : F := E49 + E50
  let E52 : F := Main[77] * 8
  let E53 : F := Main[78] * 8
  let E54 : F := E52 + E53
  let E55 : F := Main[79] * 8
  let E56 : F := E54 + E55
  let E57 : F := Main[80] * 8
  let E58 : F := E56 + E57
  let E59 : F := Main[81] * 8
  let E60 : F := E58 + E59
  let E61 : F := Main[3] + 4
  let CS1 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E61, Main[4], Main[5]] 8 E3
  let E62 : F := Main[1] * 65536
  let E63 : F := Main[2] + E62
  let CS2 : SP1ConstraintList F := RTypeReader.constraints Main[0] E63 #v[Main[3], Main[4], Main[5]] E24 #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } E3 E3
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E13),
    (.assertZero E15),
    (.assertZero Main[13]),
  ]

end constraints

variable {p : ℕ}

section opcodes

@[simp] def is_real (Main : Vector (ZMod p) 82) : Prop :=
  Main[77] = 1 ∨ Main[78] = 1 ∨ Main[79] = 1 ∨ Main[80] = 1 ∨ Main[81] = 1
  deriving Decidable

@[simp] def is_mul (Main : Vector (ZMod p) 82) : Prop :=
  Main[77] = 1 ∧ Main[30] = 0
  deriving Decidable
@[simp] def is_mulh (Main : Vector (ZMod p) 82) : Prop :=
  Main[78] = 1 ∧ Main[30] = 0
  deriving Decidable
@[simp] def is_mulhu (Main : Vector (ZMod p) 82) : Prop :=
  Main[79] = 1 ∧ Main[30] = 0
  deriving Decidable
@[simp] def is_mulhsu (Main : Vector (ZMod p) 82) : Prop :=
  Main[80] = 1 ∧ Main[30] = 0
  deriving Decidable
@[simp] def is_mulw (Main : Vector (ZMod p) 82) : Prop :=
  Main[81] = 1 ∧ Main[30] = 0
  deriving Decidable

@[simp] def sp1_op_a (Main : Vector (ZMod p) 82) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val
@[simp] def sp1_op_b (Main : Vector (ZMod p) 82) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val
@[simp] def sp1_op_c (Main : Vector (ZMod p) 82) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

end opcodes

end Mul
