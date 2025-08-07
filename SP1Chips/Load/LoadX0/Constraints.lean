import SP1Foundations
import SP1Operations.Operation.AddressOperation.Constraints
import SP1Operations.Reader.ITypeReaderImmutable.Constraints
import SP1Operations.Reader.CPUState.Constraints

namespace Load

namespace LoadX0

section constraints

-- Generated Lean code for chip LoadX0Chip
def constraints (Main : Vector (Fin BB) 48) : SP1ConstraintList :=
  let E0 : Fin BB := Main[1] * 65536
  let E1 : Fin BB := Main[2] + E0
  let E2 : Fin BB := 19 * Main[41]
  let E3 : Fin BB := 22 * Main[42]
  let E4 : Fin BB := E2 + E3
  let E5 : Fin BB := 20 * Main[43]
  let E6 : Fin BB := E4 + E5
  let E7 : Fin BB := 23 * Main[44]
  let E8 : Fin BB := E6 + E7
  let E9 : Fin BB := 21 * Main[45]
  let E10 : Fin BB := E8 + E9
  let E11 : Fin BB := 44 * Main[46]
  let E12 : Fin BB := E10 + E11
  let E13 : Fin BB := 45 * Main[47]
  let E14 : Fin BB := E12 + E13
  let E15 : Fin BB := Main[41] * 0
  let E16 : Fin BB := Main[42] * 4
  let E17 : Fin BB := E15 + E16
  let E18 : Fin BB := Main[43] * 1
  let E19 : Fin BB := E17 + E18
  let E20 : Fin BB := Main[44] * 5
  let E21 : Fin BB := E19 + E20
  let E22 : Fin BB := Main[45] * 2
  let E23 : Fin BB := E21 + E22
  let E24 : Fin BB := Main[46] * 6
  let E25 : Fin BB := E23 + E24
  let E26 : Fin BB := Main[47] * 3
  let E27 : Fin BB := E25 + E26
  let E28 : Fin BB := Main[41] * 0
  let E29 : Fin BB := Main[42] * 0
  let E30 : Fin BB := E28 + E29
  let E31 : Fin BB := Main[43] * 0
  let E32 : Fin BB := E30 + E31
  let E33 : Fin BB := Main[44] * 0
  let E34 : Fin BB := E32 + E33
  let E35 : Fin BB := Main[45] * 0
  let E36 : Fin BB := E34 + E35
  let E37 : Fin BB := Main[46] * 0
  let E38 : Fin BB := E36 + E37
  let E39 : Fin BB := Main[47] * 0
  let E40 : Fin BB := E38 + E39
  let E41 : Fin BB := Main[41] * 3
  let E42 : Fin BB := Main[42] * 3
  let E43 : Fin BB := E41 + E42
  let E44 : Fin BB := Main[43] * 3
  let E45 : Fin BB := E43 + E44
  let E46 : Fin BB := Main[44] * 3
  let E47 : Fin BB := E45 + E46
  let E48 : Fin BB := Main[45] * 3
  let E49 : Fin BB := E47 + E48
  let E50 : Fin BB := Main[46] * 3
  let E51 : Fin BB := E49 + E50
  let E52 : Fin BB := Main[47] * 3
  let E53 : Fin BB := E51 + E52
  let E54 : Fin BB := Main[41] + Main[42]
  let E55 : Fin BB := E54 + Main[43]
  let E56 : Fin BB := E55 + Main[44]
  let E57 : Fin BB := E56 + Main[45]
  let E58 : Fin BB := E57 + Main[46]
  let E59 : Fin BB := E58 + Main[47]
  let E60 : Fin BB := Main[41] - 1
  let E61 : Fin BB := Main[41] * E60
  let E62 : Fin BB := Main[42] - 1
  let E63 : Fin BB := Main[42] * E62
  let E64 : Fin BB := Main[43] - 1
  let E65 : Fin BB := Main[43] * E64
  let E66 : Fin BB := Main[44] - 1
  let E67 : Fin BB := Main[44] * E66
  let E68 : Fin BB := Main[45] - 1
  let E69 : Fin BB := Main[45] * E68
  let E70 : Fin BB := Main[46] - 1
  let E71 : Fin BB := Main[46] * E70
  let E72 : Fin BB := Main[47] - 1
  let E73 : Fin BB := Main[47] * E72
  let E74 : Fin BB := E59 - 1
  let E75 : Fin BB := E59 * E74
  let ⟨⟨⟨[E76, E77, E78]⟩, _⟩, CS0⟩ := AddressOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] Main[38] Main[39] Main[40] E59 { addr_operation := { value := #v[Main[25], Main[26], Main[27]] }, top_two_limb_inv := Main[28] }
  let E79 : Fin BB := Main[47] * Main[40]
  let E80 : Fin BB := Main[45] + Main[46]
  let E81 : Fin BB := E80 + Main[47]
  let E82 : Fin BB := E81 * Main[39]
  let E83 : Fin BB := Main[43] + Main[44]
  let E84 : Fin BB := E83 + Main[45]
  let E85 : Fin BB := E84 + Main[46]
  let E86 : Fin BB := E85 + Main[47]
  let E87 : Fin BB := E86 * Main[38]
  let E88 : Fin BB := E59 - 1
  let E89 : Fin BB := E59 * E88
  let E90 : Fin BB := Main[35] - 1
  let E91 : Fin BB := Main[35] * E90
  let E92 : Fin BB := E59 * E91
  let E93 : Fin BB := Main[0] - Main[33]
  let E94 : Fin BB := Main[35] * E93
  let E95 : Fin BB := E59 * E94
  let E96 : Fin BB := Main[35] * Main[34]
  let E97 : Fin BB := 1 - Main[35]
  let E98 : Fin BB := E97 * Main[33]
  let E99 : Fin BB := E96 + E98
  let E100 : Fin BB := Main[35] * E1
  let E101 : Fin BB := 1 - Main[35]
  let E102 : Fin BB := E101 * Main[0]
  let E103 : Fin BB := E100 + E102
  let E104 : Fin BB := E103 - E99
  let E105 : Fin BB := E104 - 1
  let E106 : Fin BB := Main[37] * 65536
  let E107 : Fin BB := Main[36] + E106
  let E108 : Fin BB := E105 - E107
  let E109 : Fin BB := E59 * E108
  let E110 : Fin BB := Main[13] - 1
  let E111 : Fin BB := E59 * E110
  let E112 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E112, Main[4], Main[5]] 8 E59
  let CS2 : SP1ConstraintList := ITypeReaderImmutable.constraints Main[0] E1 #v[Main[3], Main[4], Main[5]] E14 #v[E53, E27, E40] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E59
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E61),
    (.assertZero E63),
    (.assertZero E65),
    (.assertZero E67),
    (.assertZero E69),
    (.assertZero E71),
    (.assertZero E73),
    (.assertZero E75),
    (.assertZero E79),
    (.assertZero E82),
    (.assertZero E87),
    (.assertZero E89),
    (.assertZero E92),
    (.assertZero E95),
    (.assertZero E109),
    (.send (.byte (ByteOpcode.ofNat 6) Main[36] 16 0) E59),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[37] 0) E59),
    (.send (.memory Main[33] Main[34] E76 E77 E78 Main[29] Main[30] Main[31] Main[32]) E59),
    (.receive (.memory Main[0] E1 E76 E77 E78 Main[29] Main[30] Main[31] Main[32]) E59),
    (.assertZero E111),
  ]

end constraints

section helpers

scoped syntax:max term noWs "[" withoutPosition(term) "]$" : term
scoped macro_rules | `($x[$i]$) => `(getElem $x $i (by norm_num1))

variable
  (Main : Vector (Fin BB) 48)
  (s : SailState)
  (cstrs : (constraints Main).allHold)

def sp1_imm : BitVec 12 := BitVec.ofNat 12 Main[21].val

set_option maxHeartbeats 40000000 in
theorem h_exactly_one
  (Main : Vector (Fin BB) 48)
  (cstrs : (constraints Main).allHold)
  : (Main[41]$ = 1 → Main[41]$ = 1 ∧ Main[42]$ = 0 ∧ Main[43]$ = 0 ∧ Main[44]$ = 0 ∧ Main[45]$ = 0 ∧ Main[46]$ = 0 ∧ Main[47]$ = 0)
  ∧ (Main[42]$ = 1 → Main[41]$ = 0 ∧ Main[42]$ = 1 ∧ Main[43]$ = 0 ∧ Main[44]$ = 0 ∧ Main[45]$ = 0 ∧ Main[46]$ = 0 ∧ Main[47]$ = 0)
  ∧ (Main[43]$ = 1 → Main[41]$ = 0 ∧ Main[42]$ = 0 ∧ Main[43]$ = 1 ∧ Main[44]$ = 0 ∧ Main[45]$ = 0 ∧ Main[46]$ = 0 ∧ Main[47]$ = 0)
  ∧ (Main[44]$ = 1 → Main[41]$ = 0 ∧ Main[42]$ = 0 ∧ Main[43]$ = 0 ∧ Main[44]$ = 1 ∧ Main[45]$ = 0 ∧ Main[46]$ = 0 ∧ Main[47]$ = 0)
  ∧ (Main[45]$ = 1 → Main[41]$ = 0 ∧ Main[42]$ = 0 ∧ Main[43]$ = 0 ∧ Main[44]$ = 0 ∧ Main[45]$ = 1 ∧ Main[46]$ = 0 ∧ Main[47]$ = 0)
  ∧ (Main[46]$ = 1 → Main[41]$ = 0 ∧ Main[42]$ = 0 ∧ Main[43]$ = 0 ∧ Main[44]$ = 0 ∧ Main[45]$ = 0 ∧ Main[46]$ = 1 ∧ Main[47]$ = 0)
  ∧ (Main[47]$ = 1 → Main[41]$ = 0 ∧ Main[42]$ = 0 ∧ Main[43]$ = 0 ∧ Main[44]$ = 0 ∧ Main[45]$ = 0 ∧ Main[46]$ = 0 ∧ Main[47]$ = 1)
  := by
    simp [constraints, List.Forall, SP1Constraint.toProp, AddressOperation.constraints, sub_eq_zero] at cstrs
    obtain ⟨_, _, _, _, _, _, _, _, _, chip_cstrs⟩ := cstrs
    clear * - chip_cstrs

    have h_is_lb_is_bool  : Main[41]$ = 0 ∨ Main[41]$ = 1 := by simp_all only
    have h_is_lbu_is_bool : Main[42]$ = 0 ∨ Main[42]$ = 1 := by simp_all only
    have h_is_lh_is_bool  : Main[43]$ = 0 ∨ Main[43]$ = 1 := by simp_all only
    have h_is_lhu_is_bool : Main[44]$ = 0 ∨ Main[44]$ = 1 := by simp_all only
    have h_is_lw_is_bool  : Main[45]$ = 0 ∨ Main[45]$ = 1 := by simp_all only
    have h_is_lwu_is_bool : Main[46]$ = 0 ∨ Main[46]$ = 1 := by simp_all only
    have h_is_ld_is_bool  : Main[47]$ = 0 ∨ Main[47]$ = 1 := by simp_all only
    have h_sum_is_bool :
      Main[41]$ + Main[42]$ + Main[43]$ + Main[44]$ + Main[45]$ + Main[46]$ + Main[47]$ = 0
      ∨ Main[41]$ + Main[42]$ + Main[43]$ + Main[44]$ + Main[45]$ + Main[46]$ + Main[47]$ = 1
      := by simp_all only
    clear * - h_is_lb_is_bool h_is_lbu_is_bool
              h_is_lh_is_bool h_is_lhu_is_bool
              h_is_lw_is_bool h_is_lwu_is_bool
              h_is_ld_is_bool h_sum_is_bool

    split_ands
    all_goals
      intro h_target
      cases h_is_lb_is_bool <;> rename_i h_lb
      <;> cases h_is_lbu_is_bool <;> rename_i h_lbu
      <;> cases h_is_lh_is_bool <;> rename_i h_lh
      <;> cases h_is_lhu_is_bool <;> rename_i h_lhu
      <;> cases h_is_lw_is_bool <;> rename_i h_lw
      <;> cases h_is_lwu_is_bool <;> rename_i h_lwu
      <;> cases h_is_ld_is_bool <;> rename_i h_ld
      <;> simp [h_target, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld] at h_sum_is_bool
      <;> tauto

end helpers

end LoadX0

end Load
