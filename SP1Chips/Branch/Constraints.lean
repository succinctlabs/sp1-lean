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

set_option maxHeartbeats 1600000 in
-- Polymorphic counterpart of `eq_signExtend_of_is_real`. The 6-arm
-- case-split over `is_real` extracts the trusted_instr signExtend
-- bridge from the active variant's reader constraint. Each variant
-- pins the opcode to a specific small constant (40-45 for branch
-- variants); supply `(k : ZMod p).val = k` simp lemmas explicitly.
lemma eq_signExtend_of_is_real_poly (Main : Vector (ZMod p) 45)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (is_real : is_real_poly Main) :
    Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h40_lt : (40 : ℕ) < p := by omega
  have h41_lt : (41 : ℕ) < p := by omega
  have h42_lt : (42 : ℕ) < p := by omega
  have h43_lt : (43 : ℕ) < p := by omega
  have h44_lt : (44 : ℕ) < p := by omega
  have h45_lt : (45 : ℕ) < p := by omega
  have h40_val : (40 : ZMod p).val = 40 := ZMod.val_natCast_of_lt h40_lt
  have h41_val : (41 : ZMod p).val = 41 := ZMod.val_natCast_of_lt h41_lt
  have h42_val : (42 : ZMod p).val = 42 := ZMod.val_natCast_of_lt h42_lt
  have h43_val : (43 : ZMod p).val = 43 := ZMod.val_natCast_of_lt h43_lt
  have h44_val : (44 : ZMod p).val = 44 := ZMod.val_natCast_of_lt h44_lt
  have h45_val : (45 : ZMod p).val = 45 := ZMod.val_natCast_of_lt h45_lt
  have := single_op_poly Main cstrs
  rcases is_real with h | h | h | h | h | h
  all_goals
  · simp_all [constraints, ITypeReaderImmutable.constraints,
      SP1Constraint.toProp_poly, Opcode.ofNat, Nat.ble,
      h40_val, h41_val, h42_val, h43_val, h44_val, h45_val]

set_option maxHeartbeats 1600000 in
-- Polymorphic counterpart of `add_signExtend_of_constraints`. Uses the
-- ZMod %4 → Nat %4 bridge (`val_mod_4_eq_zero_iff_zmod` in Field.lean)
-- to convert `Main[3] % 4 = 0` from the iff_poly's pc-alignment clause
-- into `Main[3].val % 4 = 0`, then closes via the field-agnostic
-- `BitVec.add_mod4_eq_zero_of_mod4_eq_zero` + `BitVec.ofNat64_mod_4_eq_zero_iff`.
-- `skipKernelTC` for the same reason as AddrAddOperation.spec_of_constraints_poly:
-- BitVec.toNat_add's `% 2^64` triggers kernel deep recursion.
set_option debug.skipKernelTC true in
lemma add_signExtend_of_constraints_poly (Main : Vector (ZMod p) 45)
    (cstrs : SP1ConstraintList.allHold_poly (constraints Main))
    (is_real : is_real_poly Main) :
    (Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
      BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val)) % 4 = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_signExt := eq_signExtend_of_is_real_poly Main cstrs is_real
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h40_lt : (40 : ℕ) < p := by omega
  have h41_lt : (41 : ℕ) < p := by omega
  have h42_lt : (42 : ℕ) < p := by omega
  have h43_lt : (43 : ℕ) < p := by omega
  have h44_lt : (44 : ℕ) < p := by omega
  have h45_lt : (45 : ℕ) < p := by omega
  have h40_val : (40 : ZMod p).val = 40 := ZMod.val_natCast_of_lt h40_lt
  have h41_val : (41 : ZMod p).val = 41 := ZMod.val_natCast_of_lt h41_lt
  have h42_val : (42 : ZMod p).val = 42 := ZMod.val_natCast_of_lt h42_lt
  have h43_val : (43 : ZMod p).val = 43 := ZMod.val_natCast_of_lt h43_lt
  have h44_val : (44 : ZMod p).val = 44 := ZMod.val_natCast_of_lt h44_lt
  have h45_val : (45 : ZMod p).val = 45 := ZMod.val_natCast_of_lt h45_lt
  -- Extract Main[3] % 4 = 0 from the active variant's reader iff (as ZMod equation).
  have h_pc_mod_zmod : Main[3] % (4 : ZMod p) = (0 : ZMod p) := by
    have := single_op_poly Main cstrs
    rcases is_real with h | h | h | h | h | h
    all_goals
    · simp_all [constraints, ITypeReaderImmutable.constraints,
        SP1Constraint.toProp_poly, Opcode.ofNat, Nat.ble,
        h40_val, h41_val, h42_val, h43_val, h44_val, h45_val]
  have h_pc_mod : Main[3].val % 4 = 0 := (val_mod_4_eq_zero_iff_zmod _).mp h_pc_mod_zmod
  -- pc[0] limb bound for the Word.toNat decomposition.
  -- Extract the alignment fact from the active variant's trusted_instr (b_type's 4th clause).
  have h_imm_aligned :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] % 4#64 = 0#64 := by
    have := single_op_poly Main cstrs
    rcases is_real with h | h | h | h | h | h
    all_goals
    · simp_all [constraints, ITypeReaderImmutable.constraints,
        SP1Constraint.toProp_poly, Opcode.ofNat, Nat.ble,
        h40_val, h41_val, h42_val, h43_val, h44_val, h45_val]
  apply BitVec.add_mod4_eq_zero_of_mod4_eq_zero
  · -- pc[0]'s BitVec form is mod-4-zero.
    change _ % 4#64 = 0#64
    simp only [Word.toBitVec64_poly]
    rw [BitVec.ofNat64_mod_4_eq_zero_iff]
    simp only [Word.toNat_poly_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero,
      Nat.zero_mul, Nat.add_zero]
    omega
  · -- signExtend(imm) is mod-4-zero: bridge via h_signExt to the imm's toBitVec64_poly form.
    rw [← h_signExt]
    exact h_imm_aligned

/-- Per-limb Nat lift: same as `AddrAddOperation.limb_lift`. Converts a ZMod
equation `bb + vv + prev = aa + cc * 65536` (where prev/cc are carry bits and
the other three limbs are < 2^16) to the corresponding Nat equation. Public
so the chip-level `correct_b*_poly` proofs can lift the post-simp ZMod
limb equations directly without round-tripping through `pc_plus_4_eq_poly`'s
strict carry-disjunction shape. -/
lemma limb_lift_branch
    (bb vv aa prev cc : ZMod p)
    (hbb : bb.val < 2 ^ 16) (hvv : vv.val < 2 ^ 16) (haa : aa.val < 2 ^ 16)
    (hprev : prev = 0 ∨ prev = 1) (hcc : cc = 0 ∨ cc = 1)
    (h : bb + vv + prev = aa + cc * 65536) :
    bb.val + vv.val + prev.val = aa.val + cc.val * 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  apply_fun ZMod.val at h
  have hprev_lt : prev.val ≤ 1 := by
    rcases hprev with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hcc_lt : cc.val ≤ 1 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hbv : (bb + vv).val = bb.val + vv.val :=
    ZMod.val_add_of_lt (by omega)
  have h1 : (bb + vv + prev).val = bb.val + vv.val + prev.val := by
    rw [ZMod.val_add_of_lt (by rw [hbv]; omega), hbv]
  have h2 : (cc * 65536 : ZMod p).val = cc.val * 65536 := by
    rcases hcc with h | h <;> simp [h, ZMod.val_zero, val_65536_zmod_p, ZMod.val_one]
  have h3 : (aa + cc * 65536 : ZMod p).val = aa.val + cc.val * 65536 := by
    rw [ZMod.val_add_of_lt
      (by rw [h2]; rcases hcc with h | h <;>
            simp [h, ZMod.val_zero, ZMod.val_one] <;> omega), h2]
  rw [h1, h3] at h
  exact h

set_option maxHeartbeats 16000000 in
-- Polymorphic counterpart of `branch_addr_eq`. Mirrors
-- `AddrAddOperation.spec_of_constraints_poly`'s `linear_combination * h65inv`
-- + `limb_lift` recipe. The four carry hypotheses come from the chip's
-- assertZero'd limb-binarity constraints (E102/E109/E116/E123 with Main[34]=1
-- substituted), which after destructuring yield disjunctions of the form
-- `c = 0 ∨ c = 1` where `c` is the inverse-form carry expression. The high
-- limb of the result vector is `0` (the chip pins next_pc[3] = 0 via E121's
-- final-carry = 0 case). `skipKernelTC` for kernel deep-recursion on
-- `BitVec.toNat_add`'s `% 2^64` (per `docs/GOTCHAS.md`).
set_option debug.skipKernelTC true in
lemma branch_addr_eq_poly
    (Main : Vector (ZMod p) 45)
    (h_imm_signExtend :
      Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val))
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h_imm_0 : Main[21].val < 65536) (h_imm_1 : Main[22].val < 65536)
    (h_imm_2 : Main[23].val < 65536) (h_imm_3 : Main[24].val < 65536)
    (h25 : Main[25].val < 65536) (h26 : Main[26].val < 65536)
    (h27 : Main[27].val < 65536)
    (hc0 : (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ = 1)
    (hc1 : ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ = 0
        ∨ ((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ = 1)
    (hc2 : (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ = 1)
    (hc3 : ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ +
              Main[24]) * (65536 : ZMod p)⁻¹ = 0
        ∨ ((((Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + Main[22] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ +
              Main[24]) * (65536 : ZMod p)⁻¹ = 1) :
    Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] +
        BitVec.signExtend 64 (BitVec.ofNat 13 Main[21].val)
      = Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [← h_imm_signExtend]
  -- isU64_poly facts to feed Word.toBitVec64_poly_toNat_poly.
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  have h_pc_isU64 : Word.isU64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_pc_0
    · exact h_pc_1
    · exact h_pc_2
    · rw [h_zero_val]; omega
  have h_imm_isU64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_imm_0
    · exact h_imm_1
    · exact h_imm_2
    · exact h_imm_3
  have h_npc_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h25
    · exact h26
    · exact h27
    · rw [h_zero_val]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_poly_toNat_poly h_npc_isU64,
      Word.toBitVec64_poly_toNat_poly h_imm_isU64,
      Word.toBitVec64_poly_toNat_poly h_pc_isU64,
      Word.toNat_poly_def, Word.toNat_poly_def, Word.toNat_poly_def]
  -- Reduce vector literal indices and the high-limb-zero terms.
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val, Nat.zero_mul, Nat.add_zero]
  -- Carry-chain rearrangement, mirroring AddrAddOperation.spec_of_constraints_poly.
  set c0 : ZMod p := (Main[3] + Main[21] - Main[25]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (c0 + Main[4] + Main[22] - Main[26]) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (c1 + Main[5] + Main[23] - Main[27]) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (c2 + Main[24]) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : Main[3] + Main[21] + (0 : ZMod p) = Main[25] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (Main[3] + Main[21] - Main[25]) * h65inv
  have e1 : Main[4] + Main[22] + c0 = Main[26] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (c0 + Main[4] + Main[22] - Main[26]) * h65inv
  have e2 : Main[5] + Main[23] + c1 = Main[27] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (c1 + Main[5] + Main[23] - Main[27]) * h65inv
  have e3 : (0 : ZMod p) + Main[24] + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * (c2 + Main[24]) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have h_pc_0_lt : Main[3].val < 2 ^ 16 := by simpa using h_pc_0
  have h_pc_1_lt : Main[4].val < 2 ^ 16 := by simpa using h_pc_1
  have h_pc_2_lt : Main[5].val < 2 ^ 16 := by simpa using h_pc_2
  have h_imm_0_lt : Main[21].val < 2 ^ 16 := by simpa using h_imm_0
  have h_imm_1_lt : Main[22].val < 2 ^ 16 := by simpa using h_imm_1
  have h_imm_2_lt : Main[23].val < 2 ^ 16 := by simpa using h_imm_2
  have h_imm_3_lt : Main[24].val < 2 ^ 16 := by simpa using h_imm_3
  have h25_lt : Main[25].val < 2 ^ 16 := by simpa using h25
  have h26_lt : Main[26].val < 2 ^ 16 := by simpa using h26
  have h27_lt : Main[27].val < 2 ^ 16 := by simpa using h27
  have n0 := limb_lift_branch _ _ _ _ _ h_pc_0_lt h_imm_0_lt h25_lt hc_zero hc0 e0
  have n1 := limb_lift_branch _ _ _ _ _ h_pc_1_lt h_imm_1_lt h26_lt hc0 hc1 e1
  have n2 := limb_lift_branch _ _ _ _ _ h_pc_2_lt h_imm_2_lt h27_lt hc1 hc2 e2
  have n3 := limb_lift_branch _ _ _ _ _ hzero_lt h_imm_3_lt hzero_lt hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero, zero_add] at n0 n3
  have hc0_lt : c0.val ≤ 1 := by
    rcases hc0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by
    rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by
    rcases hc2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by
    rcases hc3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

set_option maxHeartbeats 16000000 in
-- Polymorphic counterpart of the not-branching-case PC arithmetic. Same
-- recipe as `branch_addr_eq_poly` but with the addend fixed to `4#64`
-- (i.e. `b = #v[4, 0, 0, 0]` viewed as a Word). The four carry hypotheses
-- come from the chip's E131/E139/E147/E155 binarity assertZeros (gated by
-- `E16 - Main[34] = 1` when not branching, i.e. Main[34] = 0). The high
-- three limbs of the addend are 0; only the low limb gets `+4`. This is
-- the missing companion to `branch_addr_eq_poly` for the BEQ/BNE/etc.
-- "branch was not taken" path.
set_option debug.skipKernelTC true in
lemma pc_plus_4_eq_poly
    (Main : Vector (ZMod p) 45)
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h25 : Main[25].val < 65536) (h26 : Main[26].val < 65536)
    (h27 : Main[27].val < 65536)
    (hc0 : (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 1)
    (hc1 : ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ = 0
        ∨ ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ = 1)
    (hc2 : (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ = 0
        ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ = 1)
    (hc3 : ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ +
              0 + 0 - 0) * (65536 : ZMod p)⁻¹ = 0
        ∨ ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] + 0 - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ +
              0 + 0 - 0) * (65536 : ZMod p)⁻¹ = 1) :
    Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4#64
      = Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  have h_pc_isU64 : Word.isU64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_pc_0
    · exact h_pc_1
    · exact h_pc_2
    · rw [h_zero_val]; omega
  have h_npc_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h25
    · exact h26
    · exact h27
    · rw [h_zero_val]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  -- Bridge `... + 4#64 = ...` via toNat:
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_poly_toNat_poly h_npc_isU64,
      Word.toBitVec64_poly_toNat_poly h_pc_isU64,
      Word.toNat_poly_def, Word.toNat_poly_def, BitVec.toNat_ofNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val, Nat.zero_mul, Nat.add_zero]
  set c0 : ZMod p := (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (c0 + Main[4] + 0 - Main[26]) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (c1 + Main[5] + 0 - Main[27]) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (c2 + 0 + 0 - 0) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : Main[3] + (4 : ZMod p) + (0 : ZMod p) = Main[25] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (Main[3] + 4 - Main[25]) * h65inv
  have e1 : Main[4] + (0 : ZMod p) + c0 = Main[26] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (c0 + Main[4] + 0 - Main[26]) * h65inv
  have e2 : Main[5] + (0 : ZMod p) + c1 = Main[27] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (c1 + Main[5] + 0 - Main[27]) * h65inv
  have e3 : (0 : ZMod p) + (0 : ZMod p) + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * (c2 + 0 + 0 - 0) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have h_pc_0_lt : Main[3].val < 2 ^ 16 := by simpa using h_pc_0
  have h_pc_1_lt : Main[4].val < 2 ^ 16 := by simpa using h_pc_1
  have h_pc_2_lt : Main[5].val < 2 ^ 16 := by simpa using h_pc_2
  have h25_lt : Main[25].val < 2 ^ 16 := by simpa using h25
  have h26_lt : Main[26].val < 2 ^ 16 := by simpa using h26
  have h27_lt : Main[27].val < 2 ^ 16 := by simpa using h27
  -- Treat `4` as `((4 : ℕ) : ZMod p)` for limb_lift_branch (which expects
  -- the second arg as the "vv" limb with vv.val < 2^16).
  have h4_val : ((4 : ℕ) : ZMod p).val = 4 := by
    have hp : 2 ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by omega)
  have h4_lt : ((4 : ZMod p)).val < 2 ^ 16 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
    omega
  have n0 := limb_lift_branch _ _ _ _ _ h_pc_0_lt h4_lt h25_lt hc_zero hc0 e0
  have n1 := limb_lift_branch _ _ _ _ _ h_pc_1_lt hzero_lt h26_lt hc0 hc1 e1
  have n2 := limb_lift_branch _ _ _ _ _ h_pc_2_lt hzero_lt h27_lt hc1 hc2 e2
  have n3 := limb_lift_branch _ _ _ _ _ hzero_lt hzero_lt hzero_lt hc2 hc3 e3
  have h4val_eq : ((4 : ZMod p)).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
  rw [h4val_eq] at n0
  simp only [ZMod.val_zero, add_zero, zero_add] at n1 n2 n3
  have hc0_lt : c0.val ≤ 1 := by
    rcases hc0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by
    rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by
    rcases hc2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by
    rcases hc3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

set_option maxHeartbeats 16000000 in
-- Variant of `pc_plus_4_eq_poly` accepting the chip's *natural* post-simp
-- limb form: each carry hypothesis is the simp-fragmented disjunction
-- `((a = b ∨ 65536 = 0) ∨ (a - b) * 65536⁻¹ = 1)` from default simp's
-- `mul_eq_zero` + `inv_eq_zero` + `sub_eq_zero` firing on the assertZero
-- constraint `((a - b) * 65536⁻¹) * (((a - b) * 65536⁻¹) - 1) = 0`. The chip
-- proof passes `chip_cstrs.h_limb0..3` directly without any pre-bridge step.
-- Internally bridges to canonical form, then mirrors `pc_plus_4_eq_poly`'s
-- `limb_lift_branch` chain. Heartbeats elevated for the bridges + chain.
-- `skipKernelTC` for `BitVec.toNat_add`'s `% 2^64` deep-recursion gotcha
-- (per `docs/GOTCHAS.md`).
set_option debug.skipKernelTC true in
lemma pc_plus_4_eq_poly_chip
    (Main : Vector (ZMod p) 45)
    (h_pc_0 : Main[3].val < 65536) (h_pc_1 : Main[4].val < 65536)
    (h_pc_2 : Main[5].val < 65536)
    (h25 : Main[25].val < 65536) (h26 : Main[26].val < 65536)
    (h27 : Main[27].val < 65536)
    (hc0 : (Main[3] + 4 = Main[25] ∨ (65536 : ZMod p) = 0)
        ∨ (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 1)
    (hc1 : (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] = Main[26]
              ∨ (65536 : ZMod p) = 0)
        ∨ ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ = 1))
    (hc2 : ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] = Main[27] ∨ (65536 : ZMod p) = 0)
        ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ = 1))
    (hc3 : ((((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] = Main[27] ∨ (65536 : ZMod p) = 0)
        ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26]) *
              (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ *
                (65536 : ZMod p)⁻¹ = 1)) :
    Word.toBitVec64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4#64
      = Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_65_ne : (65536 : ZMod p) ≠ 0 := val_65536_ne_zero
  -- Bridge each carry from the chip's messy form to canonical `c = 0 ∨ c = 1`.
  have hc0' : (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 0
      ∨ (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc0 with (h | h) | h
    · left; rw [show Main[3] + 4 - Main[25] = 0 from by linear_combination h, zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  have hc1' : ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ = 0
      ∨ ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc1 with (h | h) | h
    · left
      rw [show (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26] = 0
          from by linear_combination h, zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  have hc2' :
      (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ = 0
      ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc2 with (h | h) | h
    · left
      rw [show ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27] = 0 from by linear_combination h,
          zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  have hc3' :
      (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹
                * (65536 : ZMod p)⁻¹ = 0
      ∨ (((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹
                * (65536 : ZMod p)⁻¹ = 1 := by
    rcases hc3 with (h | h) | h
    · left
      rw [show ((Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ + Main[4] - Main[26])
                  * (65536 : ZMod p)⁻¹ + Main[5] - Main[27] = 0 from by linear_combination h,
          zero_mul, zero_mul]
    · exact absurd h h_65_ne
    · right; exact h
  -- Now mirror pc_plus_4_eq_poly's body using the canonical-form carries.
  have h_zero_val : ((0 : ZMod p)).val = 0 := ZMod.val_zero
  have hzero_lt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [h_zero_val]; omega
  have h_pc_isU64 : Word.isU64_poly #v[Main[3], Main[4], Main[5], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h_pc_0
    · exact h_pc_1
    · exact h_pc_2
    · rw [h_zero_val]; omega
  have h_npc_isU64 : Word.isU64_poly #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact h25
    · exact h26
    · exact h27
    · rw [h_zero_val]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_poly_toNat_poly h_npc_isU64,
      Word.toBitVec64_poly_toNat_poly h_pc_isU64,
      Word.toNat_poly_def, Word.toNat_poly_def, BitVec.toNat_ofNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, h_zero_val, Nat.zero_mul, Nat.add_zero]
  set c0 : ZMod p := (Main[3] + 4 - Main[25]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (c0 + Main[4] - Main[26]) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (c1 + Main[5] - Main[27]) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := c2 * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : Main[3] + (4 : ZMod p) + (0 : ZMod p) = Main[25] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (Main[3] + 4 - Main[25]) * h65inv
  have e1 : Main[4] + (0 : ZMod p) + c0 = Main[26] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (c0 + Main[4] - Main[26]) * h65inv
  have e2 : Main[5] + (0 : ZMod p) + c1 = Main[27] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (c1 + Main[5] - Main[27]) * h65inv
  have e3 : (0 : ZMod p) + (0 : ZMod p) + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * c2 * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have h_pc_0_lt : Main[3].val < 2 ^ 16 := by simpa using h_pc_0
  have h_pc_1_lt : Main[4].val < 2 ^ 16 := by simpa using h_pc_1
  have h_pc_2_lt : Main[5].val < 2 ^ 16 := by simpa using h_pc_2
  have h25_lt : Main[25].val < 2 ^ 16 := by simpa using h25
  have h26_lt : Main[26].val < 2 ^ 16 := by simpa using h26
  have h27_lt : Main[27].val < 2 ^ 16 := by simpa using h27
  have h4_val : ((4 : ℕ) : ZMod p).val = 4 := by
    have hp : 2 ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by omega)
  have h4_lt : ((4 : ZMod p)).val < 2 ^ 16 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
    omega
  have n0 := limb_lift_branch _ _ _ _ _ h_pc_0_lt h4_lt h25_lt hc_zero hc0' e0
  have n1 := limb_lift_branch _ _ _ _ _ h_pc_1_lt hzero_lt h26_lt hc0' hc1' e1
  have n2 := limb_lift_branch _ _ _ _ _ h_pc_2_lt hzero_lt h27_lt hc1' hc2' e2
  have n3 := limb_lift_branch _ _ _ _ _ hzero_lt hzero_lt hzero_lt hc2' hc3' e3
  have h4val_eq : ((4 : ZMod p)).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl, h4_val]
  rw [h4val_eq] at n0
  simp only [ZMod.val_zero, add_zero, zero_add] at n1 n2 n3
  have hc0_lt : c0.val ≤ 1 := by
    rcases hc0' with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by
    rcases hc1' with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by
    rcases hc2' with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by
    rcases hc3' with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

end poly_helpers

end Branch
