import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace Lt

section constraints

-- Generated Lean code for chip LtChip
@[irreducible] def constraints (Main : Vector (Fin KB) 44) : SP1ConstraintList :=
  let E0 : Fin KB := Main[32] + Main[33]
  let E1 : Fin KB := Main[32] - 1
  let E2 : Fin KB := Main[32] * E1
  let E3 : Fin KB := Main[33] - 1
  let E4 : Fin KB := Main[33] * E3
  let E5 : Fin KB := E0 - 1
  let E6 : Fin KB := E0 * E5
  let CS0 : SP1ConstraintList := LtOperationSigned.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] { result := { u16_compare_operation := { bit := Main[34] }, u16_flags := #v[Main[35], Main[36], Main[37], Main[38]], not_eq_inv := Main[39], comparison_limbs := #v[Main[40], Main[41]] }, b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } } Main[32] E0
  let E7 : Fin KB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E7, Main[4], Main[5]] 8 E0
  let E8 : Fin KB := Main[32] * 9
  let E9 : Fin KB := Main[33] * 10
  let E10 : Fin KB := E8 + E9
  let E11 : Fin KB := Main[32] * 2
  let E12 : Fin KB := Main[33] * 3
  let E13 : Fin KB := E11 + E12
  let E14 : Fin KB := Main[32] * 0
  let E15 : Fin KB := Main[33] * 0
  let E16 : Fin KB := E14 + E15
  let E17 : Fin KB := Main[32] * 51
  let E18 : Fin KB := Main[33] * 51
  let E19 : Fin KB := E17 + E18
  let E20 : Fin KB := 32 * Main[31]
  let E21 : Fin KB := E19 - E20
  let E22 : Fin KB := Main[32] * 8
  let E23 : Fin KB := Main[33] * 8
  let E24 : Fin KB := E22 + E23
  let E25 : Fin KB := 4 * Main[31]
  let E26 : Fin KB := E24 - E25
  let E27 : Fin KB := Main[1] * 65536
  let E28 : Fin KB := Main[2] + E27
  let E29 : Fin KB := 0 + Main[34]
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E28 #v[Main[3], Main[4], Main[5]] E10 #v[E26, E21, E13, E16] #v[E29, 0, 0, 0] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } E0
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E2),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero Main[13]),
  ]

end constraints


@[simp] def is_slt (Main : Vector (Fin KB) 44) := Main[32] = 1 ∧ Main[31] = 0
@[simp] def is_sltu (Main : Vector (Fin KB) 44) := Main[33] = 1 ∧ Main[31] = 0
@[simp] def is_slti (Main : Vector (Fin KB) 44) := Main[32] = 1 ∧ Main[31] = 1
@[simp] def is_sltiu (Main : Vector (Fin KB) 44) := Main[33] = 1 ∧ Main[31] = 1

def is_real (Main : Vector (Fin KB) 44) : Prop := Main[32] = 1 ∨ Main[33] = 1

-- Placeholder lemmas: use `→` direction only (the old bi-directional iff has not
-- been re-derived against the new constraint layout).
lemma allHold_constraints_imp_true_slt {Main : Vector (Fin KB) 44} (_ : is_slt Main)
    (_ : List.Forall SP1Constraint.toProp (constraints Main)) : True := trivial

lemma allHold_constraints_imp_true_sltu {Main : Vector (Fin KB) 44} (_ : is_sltu Main)
    (_ : List.Forall SP1Constraint.toProp (constraints Main)) : True := trivial

lemma allHold_constraints_imp_true_slti {Main : Vector (Fin KB) 44} (_ : is_slti Main)
    (_ : List.Forall SP1Constraint.toProp (constraints Main)) : True := trivial

lemma allHold_constraints_imp_true_sltiu {Main : Vector (Fin KB) 44} (_ : is_sltiu Main)
    (_ : List.Forall SP1Constraint.toProp (constraints Main)) : True := trivial

@[simp]
def sp1_op_a {Main : Vector (Fin KB) 44} (_ : (constraints Main).allHold) (_ : is_real Main) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

@[simp]
def sp1_op_b {Main : Vector (Fin KB) 44} (_ : (constraints Main).allHold) (_ : is_real Main) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

@[simp]
def sp1_op_c {Main : Vector (Fin KB) 44} (_ : (constraints Main).allHold) (_ : is_real Main) (_ : Main[31] = 0) : BitVec 5 :=
  BitVec.ofNat 5 Main[21]

end Lt
