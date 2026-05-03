import SP1Foundations
import SP1Operations.Reader.CPUState
import SP1Operations.Compare.LtOperationSigned
import SP1Operations.Reader.ITypeReaderImmutable

namespace Branch

section constraints

-- Generated Lean code for chip BranchChip
@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ] (Main : Vector F 45) : SP1ConstraintList F :=
  let E0 : F := Main[28] - 1
  let E1 : F := Main[28] * E0
  let E2 : F := Main[29] - 1
  let E3 : F := Main[29] * E2
  let E4 : F := Main[30] - 1
  let E5 : F := Main[30] * E4
  let E6 : F := Main[31] - 1
  let E7 : F := Main[31] * E6
  let E8 : F := Main[32] - 1
  let E9 : F := Main[32] * E8
  let E10 : F := Main[33] - 1
  let E11 : F := Main[33] * E10
  let E12 : F := Main[28] + Main[29]
  let E13 : F := E12 + Main[30]
  let E14 : F := E13 + Main[31]
  let E15 : F := E14 + Main[32]
  let E16 : F := E15 + Main[33]
  let E17 : F := E16 - 1
  let E18 : F := E16 * E17
  let E19 : F := Main[28] * 40
  let E20 : F := Main[29] * 41
  let E21 : F := E19 + E20
  let E22 : F := Main[30] * 42
  let E23 : F := E21 + E22
  let E24 : F := Main[31] * 43
  let E25 : F := E23 + E24
  let E26 : F := Main[32] * 44
  let E27 : F := E25 + E26
  let E28 : F := Main[33] * 45
  let E29 : F := E27 + E28
  let E30 : F := Main[28] * 0
  let E31 : F := Main[29] * 1
  let E32 : F := E30 + E31
  let E33 : F := Main[30] * 4
  let E34 : F := E32 + E33
  let E35 : F := Main[31] * 5
  let E36 : F := E34 + E35
  let E37 : F := Main[32] * 6
  let E38 : F := E36 + E37
  let E39 : F := Main[33] * 7
  let E40 : F := E38 + E39
  let E41 : F := Main[28] * 0
  let E42 : F := Main[29] * 0
  let E43 : F := E41 + E42
  let E44 : F := Main[30] * 0
  let E45 : F := E43 + E44
  let E46 : F := Main[31] * 0
  let E47 : F := E45 + E46
  let E48 : F := Main[32] * 0
  let E49 : F := E47 + E48
  let E50 : F := Main[33] * 0
  let E51 : F := E49 + E50
  let E52 : F := Main[28] * 99
  let E53 : F := Main[29] * 99
  let E54 : F := E52 + E53
  let E55 : F := Main[30] * 99
  let E56 : F := E54 + E55
  let E57 : F := Main[31] * 99
  let E58 : F := E56 + E57
  let E59 : F := Main[32] * 99
  let E60 : F := E58 + E59
  let E61 : F := Main[33] * 99
  let E62 : F := E60 + E61
  let E63 : F := Main[28] * 32
  let E64 : F := Main[29] * 32
  let E65 : F := E63 + E64
  let E66 : F := Main[30] * 32
  let E67 : F := E65 + E66
  let E68 : F := Main[31] * 32
  let E69 : F := E67 + E68
  let E70 : F := Main[32] * 32
  let E71 : F := E69 + E70
  let E72 : F := Main[33] * 32
  let E73 : F := E71 + E72
  let CS0 : SP1ConstraintList F := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[25], Main[26], Main[27]] 8 E16
  let E74 : F := Main[1] * 65536
  let E75 : F := Main[2] + E74
  let CS1 : SP1ConstraintList F := ITypeReaderImmutable.constraints Main[0] E75 #v[Main[3], Main[4], Main[5]] E29 #v[E73, E62, E40, E51] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] } E16
  let E76 : F := Main[30] + Main[31]
  let CS2 : SP1ConstraintList F := LtOperationSigned.constraints #v[Main[7], Main[8], Main[9], Main[10]] #v[Main[15], Main[16], Main[17], Main[18]] { result := { u16_compare_operation := { bit := Main[35] }, u16_flags := #v[Main[36], Main[37], Main[38], Main[39]], not_eq_inv := Main[40], comparison_limbs := #v[Main[41], Main[42]] }, b_msb := { msb := Main[43] }, c_msb := { msb := Main[44] } } E76 E16
  let E77 : F := Main[36] + Main[37]
  let E78 : F := E77 + Main[38]
  let E79 : F := E78 + Main[39]
  let E80 : F := 1 - E79
  let E81 : F := Main[28] * E80
  let E82 : F := 0 + E81
  let E83 : F := 1 - E80
  let E84 : F := Main[29] * E83
  let E85 : F := E82 + E84
  let E86 : F := Main[31] + Main[33]
  let E87 : F := 1 - Main[35]
  let E88 : F := E86 * E87
  let E89 : F := E85 + E88
  let E90 : F := Main[30] + Main[32]
  let E91 : F := E90 * Main[35]
  let E92 : F := E89 + E91
  let E93 : F := Main[34] - 1
  let E94 : F := Main[34] * E93
  let E95 : F := Main[34] - E92
  let E96 : F := E16 * E95
  let E97 : F := 0 + Main[3]
  let E98 : F := E97 + Main[21]
  let E99 : F := E98 - Main[25]
  let E100 : F := E99 * ((65536 : F)⁻¹)
  let E101 : F := E100 - 1
  let E102 : F := E100 * E101
  let E103 : F := Main[34] * E102
  let E104 : F := E100 + Main[4]
  let E105 : F := E104 + Main[22]
  let E106 : F := E105 - Main[26]
  let E107 : F := E106 * ((65536 : F)⁻¹)
  let E108 : F := E107 - 1
  let E109 : F := E107 * E108
  let E110 : F := Main[34] * E109
  let E111 : F := E107 + Main[5]
  let E112 : F := E111 + Main[23]
  let E113 : F := E112 - Main[27]
  let E114 : F := E113 * ((65536 : F)⁻¹)
  let E115 : F := E114 - 1
  let E116 : F := E114 * E115
  let E117 : F := Main[34] * E116
  let E118 : F := E114 + 0
  let E119 : F := E118 + Main[24]
  let E120 : F := E119 - 0
  let E121 : F := E120 * ((65536 : F)⁻¹)
  let E122 : F := E121 - 1
  let E123 : F := E121 * E122
  let E124 : F := Main[34] * E123
  let E125 : F := 0 + Main[3]
  let E126 : F := E125 + 4
  let E127 : F := E126 - Main[25]
  let E128 : F := E127 * ((65536 : F)⁻¹)
  let E129 : F := E16 - Main[34]
  let E130 : F := E128 - 1
  let E131 : F := E128 * E130
  let E132 : F := E129 * E131
  let E133 : F := E128 + Main[4]
  let E134 : F := E133 + 0
  let E135 : F := E134 - Main[26]
  let E136 : F := E135 * ((65536 : F)⁻¹)
  let E137 : F := E16 - Main[34]
  let E138 : F := E136 - 1
  let E139 : F := E136 * E138
  let E140 : F := E137 * E139
  let E141 : F := E136 + Main[5]
  let E142 : F := E141 + 0
  let E143 : F := E142 - Main[27]
  let E144 : F := E143 * ((65536 : F)⁻¹)
  let E145 : F := E16 - Main[34]
  let E146 : F := E144 - 1
  let E147 : F := E144 * E146
  let E148 : F := E145 * E147
  let E149 : F := E144 + 0
  let E150 : F := E149 + 0
  let E151 : F := E150 - 0
  let E152 : F := E151 * ((65536 : F)⁻¹)
  let E153 : F := E16 - Main[34]
  let E154 : F := E152 - 1
  let E155 : F := E152 * E154
  let E156 : F := E153 * E155
  let E157 : F := Main[25] * ((4 : F)⁻¹)
  CS0 ++ CS1 ++ CS2 ++ [
    (.assertZero E1),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E18),
    (.assertZero E94),
    (.assertZero E96),
    (.assertZero E103),
    (.assertZero E110),
    (.assertZero E117),
    (.assertZero E124),
    (.assertZero E132),
    (.assertZero E140),
    (.assertZero E148),
    (.assertZero E156),
    (.send (.byte (ByteOpcode.ofNat 6) E157 14 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[26] 16 0) E16),
    (.send (.byte (ByteOpcode.ofNat 6) Main[27] 16 0) E16),
  ]

end constraints

def is_real (Main : Vector (Fin KB) 45) :=
  Main[28] = 1 ∨ Main[29] = 1 ∨ Main[30] = 1 ∨ Main[31] = 1 ∨ Main[32] = 1 ∨ Main[33] = 1

lemma single_op (Main : Vector (Fin KB) 45) (cstrs : (constraints Main).allHold) :
    (Main[28] = 1 → Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[29] = 1 → Main[28] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[30] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[31] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[32] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[33] = 0) ∧
    (Main[33] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0) := by
  simp [constraints, sub_eq_zero] at cstrs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, rest⟩ := cstrs
  clear h1 h2 h3 rest
  cases h4 <;> cases h5 <;> cases h6 <;> cases h7 <;> cases h8 <;> cases h9
  all_goals simp_all only [Fin.isValue, add_zero, zero_add, one_ne_zero, or_true, zero_ne_one,
    and_self, implies_true, Fin.reduceAdd, Fin.reduceEq, or_self]

-- large 6-arm case split over `is_real`
lemma eq_signExtend_of_is_real (Main : Vector (Fin KB) 45)
    (cstrs : (constraints Main).allHold)
    (is_real : is_real Main) :
    Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21]) := by
  have := single_op Main cstrs
  rcases is_real with h | h | h | h | h | h
  all_goals
  · simp_all [constraints, ITypeReaderImmutable.constraints,
      SP1Constraint.toProp, Opcode.ofNat, Nat.ble]

-- 6-arm case split with `signExtend` unfolding
lemma add_signExtend_of_constraints (Main : Vector (Fin KB) 45)
    (cstrs : (constraints Main).allHold)
    (is_real : is_real Main) :
    (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] +
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21])) % 4 = 0 := by
  have := single_op Main cstrs
  rcases is_real with h | h | h | h | h | h
  all_goals
  · simp only [Fin.isValue, one_ne_zero, h] at this
    simp only [SP1ConstraintList.allHold, constraints, Fin.isValue, mul_zero, mul_one, zero_add,
      add_zero, List.append_assoc, sub_sub_cancel, Nat.cast_one, Nat.cast_zero, sub_zero,
      ByteOpcode.ofNat_seven, List.forall_append, List.Forall, SP1Constraint.toProp_assertZero,
      mul_eq_zero, Fin.reduceEq, or_false, SP1Constraint.toProp_send_byte, ne_eq,
      ByteOpcode.constrain_Range, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reducePow] at cstrs
    obtain ⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩ := cstrs
    clear lt_cstrs chip_cstrs
    simp_all
    simp [ITypeReaderImmutable.constraints, SP1Constraint.toProp,
      Opcode.ofNat, Nat.ble] at reader_cstrs
    have h_pc0_nat_mul4 : Main[3].val % 4 = 0 := by
      have : Main[3] % 4 = 0 := by simp_all only [Fin.isValue]
      rwa [Fin.mod_def, ← Fin.val_inj] at this
    have h_trusted_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21]) := by simp_all only
    have h_pc0_mul4 : Main[21].val % 4 = 0 := by simp_all only
    apply BitVec.add_mod4_eq_zero_of_mod4_eq_zero
    · change _ % 4#64 = 0#64
      rw [BitVec.ofNat64_mod_4_eq_zero_iff]
      exact h_pc0_nat_mul4
    · simp only [← h_trusted_signExtend, Word.toBitVec64, Word.toNat, Nat.reducePow,
      Word.toNat_aux_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, BitVec.ofNat_eq_ofNat, BitVec.ofNat64_mod_4_eq_zero_iff]
      omega

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_real_poly (Main : Vector (ZMod p) 45) : Prop :=
  Main[28] = 1 ∨ Main[29] = 1 ∨ Main[30] = 1 ∨ Main[31] = 1 ∨ Main[32] = 1 ∨ Main[33] = 1

@[simp] def is_beq_poly (Main : Vector (ZMod p) 45) := Main[28] = 1
@[simp] def is_bne_poly (Main : Vector (ZMod p) 45) := Main[29] = 1
@[simp] def is_blt_poly (Main : Vector (ZMod p) 45) := Main[30] = 1
@[simp] def is_bge_poly (Main : Vector (ZMod p) 45) := Main[31] = 1
@[simp] def is_bltu_poly (Main : Vector (ZMod p) 45) := Main[32] = 1
@[simp] def is_bgeu_poly (Main : Vector (ZMod p) 45) := Main[33] = 1

set_option maxHeartbeats 1600000 in
-- Polymorphic counterpart of `single_op`. Same 6-way nested case split as
-- the Fin KB version, closed by `simp_all` once the disjunctions are
-- destructured. Heartbeats elevated for the 64-case combinatorial closure.
lemma single_op_poly (Main : Vector (ZMod p) 45)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main)) :
    (Main[28] = 1 → Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[29] = 1 → Main[28] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[30] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[31] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[32] = 0 ∧ Main[33] = 0) ∧
    (Main[32] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[33] = 0) ∧
    (Main[33] = 1 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  -- For k ∈ {2, 3, 4, 5, 6}: (k : ZMod p) ≠ 0 ∧ ≠ 1, since k.val = k < p.
  have h2_ne : ((2 : ℕ) : ZMod p) ≠ 0 ∧ ((2 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h3_ne : ((3 : ℕ) : ZMod p) ≠ 0 ∧ ((3 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((3 : ℕ) : ZMod p).val = 3 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h4_ne : ((4 : ℕ) : ZMod p) ≠ 0 ∧ ((4 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h5_ne : ((5 : ℕ) : ZMod p) ≠ 0 ∧ ((5 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((5 : ℕ) : ZMod p).val = 5 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  have h6_ne : ((6 : ℕ) : ZMod p) ≠ 0 ∧ ((6 : ℕ) : ZMod p) ≠ 1 := by
    have hv : ((6 : ℕ) : ZMod p).val = 6 := ZMod.val_natCast_of_lt (by omega)
    refine ⟨?_, ?_⟩ <;> intro heq <;>
      (first | rw [heq, ZMod.val_zero] at hv | rw [heq, ZMod.val_one] at hv) <;> omega
  -- Convert to ZMod-side cast-free non-equalities for use in simp_all.
  have h2_ne_zero : (1 + 1 : ZMod p) ≠ 0 := fun h => h2_ne.1 (by push_cast; linear_combination h)
  have h2_ne_one  : (1 + 1 : ZMod p) ≠ 1 := fun h => h2_ne.2 (by push_cast; linear_combination h)
  have h3_ne_zero : (1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h3_ne.1 (by push_cast; linear_combination h)
  have h3_ne_one  : (1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h3_ne.2 (by push_cast; linear_combination h)
  have h4_ne_zero : (1 + 1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h4_ne.1 (by push_cast; linear_combination h)
  have h4_ne_one  : (1 + 1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h4_ne.2 (by push_cast; linear_combination h)
  have h5_ne_zero : (1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h5_ne.1 (by push_cast; linear_combination h)
  have h5_ne_one  : (1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h5_ne.2 (by push_cast; linear_combination h)
  have h6_ne_zero : (1 + 1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 0 :=
    fun h => h6_ne.1 (by push_cast; linear_combination h)
  have h6_ne_one  : (1 + 1 + 1 + 1 + 1 + 1 : ZMod p) ≠ 1 :=
    fun h => h6_ne.2 (by push_cast; linear_combination h)
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly] at cstrs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, rest⟩ := cstrs
  clear h1 h2 h3 rest
  cases h4 <;> cases h5 <;> cases h6 <;> cases h7 <;> cases h8 <;> cases h9
  all_goals simp_all only [add_zero, zero_add, one_ne_zero, or_true, zero_ne_one,
    and_self, implies_true, or_self,
    h2_ne_zero, h2_ne_one, h3_ne_zero, h3_ne_one,
    h4_ne_zero, h4_ne_one, h5_ne_zero, h5_ne_one,
    h6_ne_zero, h6_ne_one]

end poly_helpers

end Branch
