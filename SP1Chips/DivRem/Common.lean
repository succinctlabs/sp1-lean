import SP1Chips.DivRem.Constraints

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
-- The chip's `correct_*` proofs drive an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at` that operates on one focused case at a
-- time. Rewriting each to `<;>` would flatten the tree but require goal-state
-- reasoning the linter can't see; keep the existing structure.
set_option linter.style.multiGoal false

variable (Main : Vector (Fin KB) 246)

section field_arithmetic

lemma KB_bool_to_le {x : Fin KB} : x = (0 : Fin KB) ∨ x = (1 : Fin KB) ↔ (0 : Fin KB) ≤ x ∧ x ≤ (1 : Fin KB) := by grind

end field_arithmetic

section opcodes

@[simp] def is_real := Main[244] = 1

@[simp] def is_div := Main[201] = 1
@[simp] def is_divu := Main[202] = 1
@[simp] def is_rem := Main[203] = 1
@[simp] def is_remu := Main[204] = 1
@[simp] def is_divw := Main[205] = 1
@[simp] def is_remw := Main[206] = 1
@[simp] def is_divuw := Main[207] = 1
@[simp] def is_remuw := Main[208] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[201] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[202] = 1 → Main[201] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[203] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[204] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[205] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[206] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
  (Main[207] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0) ∧
  (Main[208] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0)
   := by
  intro cstrs
  have := allHold_constraints_alu_ops Main cstrs
  obtain ⟨alu, b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw, b_one_of_ops⟩ := this
  clear alu cstrs
  rw [KB_bool_to_le] at *
  split_ands <;> grind

end opcodes

section entailed_constraints

lemma register_bounds :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main →
      Main[6] < 32 ∧ Main[14] < 32 ∧ Main[21] < 32 ∧ Main[3] < 65536
    := by
  intro cstrs is_real
  have ⟨sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8⟩ := single_op Main cstrs
  apply allHold_constraints_alu_ops at cstrs
  obtain ⟨alu, b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw, b_one_of_ops⟩ := cstrs
  simp_all only [DivRem.is_real, Fin.isValue, Nat.cast_ofNat]
  rw [RTypeReader.allHold_constraints_iff_is_real] at alu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, rest⟩ := alu; clear rest
  -- simp_all
  rcases b_is_div; rcases b_is_divu; rcases b_is_rem; rcases b_is_remu
  rcases b_is_divw; rcases b_is_divuw; rcases b_is_remw; rcases b_is_remuw
  all_goals
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

lemma op_a_is_0 :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main →
      Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 := by
  intro cstrs is_real is_zero
  apply allHold_constraints_alu_ops at cstrs
  obtain ⟨alu, rest⟩ := cstrs; clear rest; simp_all
  rw [RTypeReader.allHold_constraints_iff_is_real rfl rfl] at alu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := alu
  simp_all

lemma ops_U64_b_c :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main →
      Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
      Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  intro cstrs is_real
  apply allHold_constraints_alu_ops at cstrs
  obtain ⟨alu, rest⟩ := cstrs; clear rest; simp_all
  rw [RTypeReader.allHold_constraints_iff_is_real rfl rfl] at alu
  obtain ⟨h1, h2, h3, h4, h5, b_imm, h7, h8⟩ := alu
  simp_all

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := register_bounds Main cstrs real
  tauto

end operands

section auxiliaries

lemma div_mod_decomposition_w {a b c : Fin KB} :
  a.val < 65536 → c.val < 2130706433 / 65536 → (a = b - c * 65536 ↔ a = b % 65536 ∧ c = b / 65536) := by
  intro ub_a ub_c
  constructor
  · intro eq_a
    simp [Fin.lt_def, Fin.ext_iff] at *
    have lb_b : c * 65536 ≤ b := by
      by_contra lb_b
      simp [Fin.lt_def, Fin.sub_def, Fin.mul_def] at *
      rw [Nat.mod_eq_of_lt (a := (c : ℕ) * 65536) (by omega)] at eq_a lb_b
      omega
    rw [Fin.sub_val_of_le lb_b] at eq_a
    simp [Fin.mul_def] at eq_a
    rw [Nat.mod_eq_of_lt (by omega)] at eq_a
    omega
  · intro ⟨eq_a, eq_c⟩
    simp_all
    symm; rw [sub_eq_iff_eq_add]; symm
    rw [mul_comm, add_comm]
    simp [Fin.ext_iff, Fin.mul_def, Fin.add_def, Fin.mod_def]
    omega

/-- Polymorphic counterpart of `div_mod_decomposition_w`. Statement is
phrased at the `.val` level since `ZMod p` lacks native `% / /` operators.
The KB-specific bound `c.val < 2130706433 / 65536` is replaced by
`c.val < 2` since at every use site `c` is a carry bit (the
`b_cry0..b_cry7 : cry = 0 ∨ cry = 1` family). The wrap-around branch
of `val_sub_cases` is ruled out via `Fact (2 ^ 17 < p)` (else
`a.val ≥ p - 65536 > 65536`, contradicting `a.val < 65536`). -/
lemma div_mod_decomposition_w_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b c : ZMod p} :
    a.val < 65536 → c.val < 2 →
    (a = b - c * 65536 ↔ a.val = b.val % 65536 ∧ c.val = b.val / 65536) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  have h65536_val : ((65536 : ℕ) : ZMod p).val = 65536 :=
    ZMod.val_natCast_of_lt (by omega)
  have h65536_eq : (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) := by push_cast; rfl
  intro ub_a ub_c
  have hcm_val : (c * 65536).val = c.val * 65536 := by
    rw [h65536_eq, ZMod.val_mul, h65536_val, Nat.mod_eq_of_lt (by omega)]
  have hbv_lt : b.val < p := ZMod.val_lt b
  constructor
  · intro eq_a
    have eq_a_val : a.val = (b - c * 65536).val := by rw [eq_a]
    rw [val_sub_cases] at eq_a_val
    by_cases h_le : (c * 65536).val ≤ b.val
    · rw [if_pos h_le, hcm_val] at eq_a_val
      rw [hcm_val] at h_le
      have hb_eq : b.val = a.val + c.val * 65536 := by omega
      have hdm := Nat.div_add_mod b.val 65536
      have hmod_lt : b.val % 65536 < 65536 := Nat.mod_lt _ (by omega)
      refine ⟨by omega, by omega⟩
    · exfalso
      rw [if_neg h_le, hcm_val] at eq_a_val
      rw [Nat.not_le, hcm_val] at h_le
      omega
  · intro ⟨eq_a_val, eq_c_val⟩
    have hb_decomp : b.val = c.val * 65536 + a.val := by
      have hdm := Nat.div_add_mod b.val 65536
      omega
    have h_le : (c * 65536).val ≤ b.val := by rw [hcm_val]; omega
    apply ZMod.val_injective
    rw [val_sub_cases, if_pos h_le, hcm_val]
    omega

lemma tdiv_tmod_unique_full {b c q r : ℤ} (hcnz : c ≠ 0) :
  q = b.tdiv c ∧ r = b.tmod c ↔
  b = q * c + r ∧
  |r| < |c| ∧
  (r = 0 ∨ r.sign = b.sign) := by
  have hmod1 := @Int.tdiv_tmod_unique b c r q
  have hmod2 := @Int.tdiv_tmod_unique' b c r q
  rw [@eq_comm (a := q), @eq_comm (a := r), @eq_comm (a := b), add_comm, mul_comm]
  repeat rw [Int.natCast_natAbs] at *; repeat rw [Int.abs_cases] at *
  by_cases hb_split : 0 ≤ b
  · simp_all; intro heq; clear hmod1 hmod2
    constructor <;> intro ⟨h0, h1⟩
    · simp_all
      by_cases hr_split : r = 0 <;> [ simp_all; right ]
      rw [Int.sign_eq_one_of_pos (by omega)]
      rw [Int.sign_eq_one_of_pos]
      suffices : ¬ b = 0
      · omega
      · intro bz; simp_all
        apply Int.split_nzp q <;> intro hq <;> [ skip; simp_all; skip ]
        all_goals
          have : c * q > r := by split_ifs at * <;> nlinarith
          omega
    · rcases h1 with rz | h_sign <;> [ omega; skip ]
      split_ifs with hc_split <;> split_ifs at h0 with hr_split <;> simp_all
      all_goals
        rw [Int.sign_eq_neg_one_of_neg (by assumption)] at h_sign
        symm at h_sign; rw [Int.sign_eq_neg_one_iff_neg] at h_sign
        omega
  · rw [hmod2 (by omega) hcnz]; simp_all; intro heq; clear hmod2
    constructor <;> intro ⟨h0, h1⟩
    · constructor
      · by_cases hr_split : r = 0 <;> [ simp_all; skip ]
        rw [if_neg (by omega)]
        omega
      · by_cases hr_split : r = 0 <;> [ simp_all; right ]
        rw [Int.sign_eq_neg_one_of_neg (by omega)]
        rw [Int.sign_eq_neg_one_of_neg hb_split]
    · rcases h1 with rz | h_sign <;> [ omega; skip ]
      rw [Int.sign_eq_neg_one_of_neg hb_split] at h_sign
      rw [Int.sign_eq_neg_one_iff_neg] at h_sign
      rw [if_neg (by omega)] at h0
      omega

lemma tdiv_tmod_unique_full_nat {b c q r : ℕ} (hcnz : c ≠ 0) :
  q = ((b : ℤ).tdiv c).toNat ∧ r = ((b : ℤ).tmod c).toNat ↔
  b = q * c + r ∧ r < c := by
  have hmod := @Int.tdiv_tmod_unique b c r q
  simp_all [Int.tmod_eq_emod]
  rw [@eq_comm (a := q), @eq_comm (a := r), @eq_comm (a := b), add_comm, mul_comm]
  trans (r : ℤ) + c * q = b ∧ r < c
  · rw [← hmod]
    rw [Int.ofNat_ediv_ofNat, ← Int.natCast_emod]
    rw [Int.toNat_natCast, Int.toNat_natCast, Int.natCast_inj, Int.natCast_inj]
  · omega

lemma sum_zero_abs {wx wy : Word (Fin KB)} (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx.isNegative →
    Word.toBitVec64 #v[0, 0, 0, 0] = Word.toBitVec64 wx + Word.toBitVec64 wy →
    (wx.toInt = -2^63 → wy.toInt = -2^63) ∧
    (¬ wx.toInt = -2^63 → wy.toInt = |wx.toInt|) := by
  intro neg_wx sum_zero
  rw [Word.isNegative_toInt is64_wx] at neg_wx
  rw [Int.abs_cases, if_neg (by omega)]
  simp [← BitVec.toInt_inj] at sum_zero
  rw [Word.toBitVec64_toInt is64_wx, Word.toBitVec64_toInt is64_wy] at sum_zero
  simp [Word.toBitVec64, Word.toNat] at sum_zero
  apply Word.isU64_toInt at is64_wx
  apply Word.isU64_toInt at is64_wy
  constructor <;> intro hwx <;> [ (simp [hwx] at *; simp_all); skip ]
  all_goals
    rw [Int.bmod_eq_emod] at sum_zero
    split_ifs at sum_zero with h_bmod <;> omega

/-- Polymorphic counterpart of `sum_zero_abs`. Required by `divw_remw_poly`'s
4-way `b_rem_neg × b_c_neg` h_abs block. -/
lemma sum_zero_abs_poly {p : ℕ} [NeZero p] {wx wy : Word (ZMod p)}
    (is64_wx : Word.isU64_poly wx) (is64_wy : Word.isU64_poly wy) :
  wx.isNegative_poly →
    Word.toBitVec64_poly (#v[0, 0, 0, 0] : Word (ZMod p))
      = wx.toBitVec64_poly + wy.toBitVec64_poly →
    (wx.toInt_poly = -2^63 → wy.toInt_poly = -2^63) ∧
    (¬ wx.toInt_poly = -2^63 → wy.toInt_poly = |wx.toInt_poly|) := by
  intro neg_wx sum_zero
  rw [Word.isNegative_poly_toInt_poly is64_wx] at neg_wx
  rw [Int.abs_cases, if_neg (by omega)]
  simp [← BitVec.toInt_inj] at sum_zero
  rw [Word.toBitVec64_poly_toInt_poly is64_wx, Word.toBitVec64_poly_toInt_poly is64_wy] at sum_zero
  simp [Word.toBitVec64_poly, Word.toNat_poly, ZMod.val_zero] at sum_zero
  apply Word.isU64_poly_toInt_poly at is64_wx
  apply Word.isU64_poly_toInt_poly at is64_wy
  constructor <;> intro hwx <;> [ (simp [hwx] at *; simp_all); skip ]
  all_goals
    rw [Int.bmod_eq_emod] at sum_zero
    split_ifs at sum_zero with h_bmod <;> omega

lemma extractLsb_is_toInt {x : BitVec 128} (hlb : -9223372036854775808 ≤ x.toInt) (hub : x.toInt < 9223372036854775808) :
  (BitVec.extractLsb 63 0 x).toInt = x.toInt := by
    by_cases case : 0 ≤ x.toInt <;> simp at case
    · simp [BitVec.toInt] at *; split_ifs at * <;> omega
    · trans (BitVec.signExtend 128 (BitVec.extractLsb 63 0 x)).toInt
      · rw [BitVec.toInt_signExtend_of_le (by simp)]
      · rw [BitVec.toInt_inj]
        simp [BitVec.toInt] at *; split_ifs at * <;> [ omega; simp at * ]
        suffices : 340282366920938463454151235394913435648#128 ≤ x
        · bv_decide
        · simp [BitVec.le_def]; omega

/-- Bridge: when `c1` has its high bit set, the 4-limb Word with sign-extended
high limbs (`65535`s) has the same `toInt_poly` as the 2-limb HWord. Used in
`divw_remw_poly`'s h_abs negative-side cases (after `sum_zero_abs_poly`). -/
lemma Word_toInt_poly_neg_form_eq_HWord_toInt_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {c0 c1 : ZMod p}
    (h_neg : (32768 : ZMod p) ≤ c1)
    (h65535_val : (65535 : ZMod p).val = 65535) :
    Word.toInt_poly (#v[c0, c1, 65535, 65535] : Word (ZMod p))
      = HWord.toInt_poly (#v[c0, c1] : HWord (ZMod p)) := by
  have h17 : 2 ^ 17 < p := Fact.out
  have h131072 : 131072 < p := by omega
  have h32768_val : (32768 : ZMod p).val = 32768 :=
    ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by omega)
  have h_neg_nat : 32768 ≤ c1.val := by
    have : (32768 : ZMod p).val ≤ c1.val := h_neg
    rwa [h32768_val] at this
  unfold Word.toInt_poly HWord.toInt_poly Word.toNat_poly HWord.toNat_poly
    Word.isNegative_poly HWord.isNegative_poly
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  rw [if_pos (by rw [h65535_val]; omega), if_pos h_neg_nat]
  rw [h65535_val]; push_cast; ring

end auxiliaries

attribute [-simp] mul_eq_zero not_and

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- Polymorphic counterpart of `is_real`. -/
@[simp] def is_real_poly (Main : Vector (ZMod p) 246) : Prop :=
  Main[244] = 1

@[simp] def is_div_poly (Main : Vector (ZMod p) 246) : Prop := Main[201] = 1
@[simp] def is_divu_poly (Main : Vector (ZMod p) 246) : Prop := Main[202] = 1
@[simp] def is_rem_poly (Main : Vector (ZMod p) 246) : Prop := Main[203] = 1
@[simp] def is_remu_poly (Main : Vector (ZMod p) 246) : Prop := Main[204] = 1
@[simp] def is_divw_poly (Main : Vector (ZMod p) 246) : Prop := Main[205] = 1
@[simp] def is_remw_poly (Main : Vector (ZMod p) 246) : Prop := Main[206] = 1
@[simp] def is_divuw_poly (Main : Vector (ZMod p) 246) : Prop := Main[207] = 1
@[simp] def is_remuw_poly (Main : Vector (ZMod p) 246) : Prop := Main[208] = 1

/-- Polymorphic counterpart of `sp1_op_a`. -/
@[simp] def sp1_op_a_poly (Main : Vector (ZMod p) 246) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

/-- Polymorphic counterpart of `sp1_op_b`. -/
@[simp] def sp1_op_b_poly (Main : Vector (ZMod p) 246) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

/-- Polymorphic counterpart of `sp1_op_c`. -/
@[simp] def sp1_op_c_poly (Main : Vector (ZMod p) 246) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

/-- Polymorphic counterpart of `ops_U64_b_c` (line 1070). Both `b` and `c`
operands are 64-bit values. Uses `RTypeReader.allHold_constraints_iff_is_real_poly`
after extracting CS18 (the RTypeReader sub-list) via direct destructure of
the chip's `allHold_poly`. The 18-deep nested left-pair pattern mirrors
`List.forall_append`'s expansion of the `CS0 ++ CS1 ++ ... ++ CS18 ++ trailing`
constraint list (19 CS entries). -/
lemma ops_U64_b_c_poly (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main) :
    Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64_poly #v[Main[22], Main[23], Main[24], Main[25]] := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, SP1Constraint.toProp_poly_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real] at h_alu
  obtain ⟨_, _, _, _, _, _, _, h_complex, _⟩ := h_alu
  obtain ⟨_, _, _, h_isU64_b, h_isU64_c⟩ := h_complex
  exact ⟨h_isU64_b, h_isU64_c⟩

/-- Polymorphic counterpart of `register_bounds` (line 1041), restricted to
the variant-INDEPENDENT bounds available directly from
`RTypeReader.allHold_constraints_iff_is_real_poly`: `op_a < 32`,
`op_b < 65536`, `op_c < 65536`, `pc[0] < 65536`. The chip-level Fin KB
`register_bounds` further refines `op_b < 32` and `op_c < 32` via
per-variant opcode reduction (`Opcode.ofNat`); chip-level `correct_*_poly`
proofs perform that refinement themselves once the variant flag is in
scope. -/
lemma register_bounds_poly (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main) :
    Main[6].val < 32 ∧ Main[14].val < 65536 ∧ Main[21].val < 65536 ∧
      Main[3].val < 65536 := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hp_lt : 65536 < p := by
    have : (2 : ℕ) ^ 17 < p := Fact.out
    omega
  have h32_val : ((32 : ℕ) : ZMod p).val = 32 :=
    ZMod.val_natCast_of_lt (by omega)
  have h65536_val : ((65536 : ℕ) : ZMod p).val = 65536 :=
    ZMod.val_natCast_of_lt (by omega)
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, SP1Constraint.toProp_poly_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real] at h_alu
  obtain ⟨_, h_op_a_lt, h_op_b_lt, h_op_c_lt, _, _, h_pc, _, _⟩ := h_alu
  obtain ⟨_, h_pc0_lt, _, _⟩ := h_pc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : Main[6].val < ((32 : ℕ) : ZMod p).val := h_op_a_lt
    rwa [h32_val] at this
  · have : Main[14].val < ((65536 : ℕ) : ZMod p).val := h_op_b_lt
    rwa [h65536_val] at this
  · have : Main[21].val < ((65536 : ℕ) : ZMod p).val := h_op_c_lt
    rwa [h65536_val] at this
  · have : Main[3].val < ((65536 : ℕ) : ZMod p).val := h_pc0_lt
    rwa [h65536_val] at this

/-- 8-way mutual exclusion: from 8 boolean disjunctions and their left-associated
sum equaling 1, with the leftmost flag active, derive that all others are 0.
The proof bridges to `Nat` via `ZMod.val` chained through 7 `ZMod.val_add_of_lt`
steps (each running sum `< 8 < p` since `Fact (2 ^ 17 < p)`), then closes via
`omega` on the resulting Nat-arithmetic constraint. -/
private lemma eight_mutex_left
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ZMod p}
    (b1 : a₁ = 0 ∨ a₁ = 1) (b2 : a₂ = 0 ∨ a₂ = 1) (b3 : a₃ = 0 ∨ a₃ = 1)
    (b4 : a₄ = 0 ∨ a₄ = 1) (b5 : a₅ = 0 ∨ a₅ = 1) (b6 : a₆ = 0 ∨ a₆ = 1)
    (b7 : a₇ = 0 ∨ a₇ = 1) (b8 : a₈ = 0 ∨ a₈ = 1)
    (sum : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ = 1)
    (h : a₁ = 1) :
    a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 ∧ a₇ = 0 ∧ a₈ = 0 := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h_p : 8 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have val_le_one : ∀ (x : ZMod p), x = 0 ∨ x = 1 → x.val ≤ 1 := fun x b => by
    rcases b with rfl | rfl
    · simp
    · rw [ZMod.val_one]
  have v1 := val_le_one _ b1
  have v2 := val_le_one _ b2
  have v3 := val_le_one _ b3
  have v4 := val_le_one _ b4
  have v5 := val_le_one _ b5
  have v6 := val_le_one _ b6
  have v7 := val_le_one _ b7
  have v8 := val_le_one _ b8
  have h_a1_val : a₁.val = 1 := by rw [h]; exact ZMod.val_one p
  have h12 : (a₁ + a₂).val = a₁.val + a₂.val :=
    ZMod.val_add_of_lt (by omega)
  have h123 : (a₁ + a₂ + a₃).val = a₁.val + a₂.val + a₃.val := by
    rw [show a₁ + a₂ + a₃ = (a₁ + a₂) + a₃ from rfl,
        ZMod.val_add_of_lt (by omega), h12]
  have h1234 : (a₁ + a₂ + a₃ + a₄).val = a₁.val + a₂.val + a₃.val + a₄.val := by
    rw [show a₁ + a₂ + a₃ + a₄ = (a₁ + a₂ + a₃) + a₄ from rfl,
        ZMod.val_add_of_lt (by omega), h123]
  have h12345 : (a₁ + a₂ + a₃ + a₄ + a₅).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ = (a₁ + a₂ + a₃ + a₄) + a₅ from rfl,
        ZMod.val_add_of_lt (by omega), h1234]
  have h123456 : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val + a₆.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ + a₆ = (a₁ + a₂ + a₃ + a₄ + a₅) + a₆ from rfl,
        ZMod.val_add_of_lt (by omega), h12345]
  have h1234567 : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val + a₆.val + a₇.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ = (a₁ + a₂ + a₃ + a₄ + a₅ + a₆) + a₇ from rfl,
        ZMod.val_add_of_lt (by omega), h123456]
  have h_sum : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈).val =
      a₁.val + a₂.val + a₃.val + a₄.val + a₅.val + a₆.val + a₇.val + a₈.val := by
    rw [show a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈ =
        (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇) + a₈ from rfl,
        ZMod.val_add_of_lt (by omega), h1234567]
  have h_sum_val : (a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ + a₈).val = 1 := by
    rw [sum]; exact ZMod.val_one p
  rw [h_sum] at h_sum_val
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply (ZMod.val_eq_zero _).mp <;> omega

/-- Polymorphic counterpart of `single_op` (line 1020). 8-way mutual exclusion:
exactly one variant flag among `Main[201..208]` is active per real row. The
proof destructures the chip's `allHold_poly` over its 19-CS-entry constraint
list + 153-item trailing list (positions 134-141 carry the boolean
disjunctions for `Main[201..208]`, position 152 carries the `1 = sum`
constraint), then applies `eight_mutex_left` for each variant after
permuting the sum to put the active flag first via `linear_combination`. -/
lemma single_op_poly (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold_poly) :
    (Main[201] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧
        Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[202] = 1 → Main[201] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧
        Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[203] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[204] = 0 ∧
        Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[204] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧
        Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[205] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧
        Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[206] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧
        Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0) ∧
    (Main[207] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧
        Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0) ∧
    (Main[208] = 1 → Main[201] = 0 ∧ Main[202] = 0 ∧ Main[203] = 0 ∧
        Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0) := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, SP1Constraint.toProp_poly_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _,
    b201, b202, b203, b204, b205, b206, b207, b208,
    _, _, _, _, _, _, _, _, _, _,
    sum_disj, _h_M13⟩ := cstrs
  -- sum_disj : 1 = Main[202] + Main[204] + Main[201] + Main[203] + Main[205]
  --                + Main[206] + Main[207] + Main[208]
  -- Permute to put each active flag first, then apply eight_mutex_left.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · have hsum : Main[201] + Main[202] + Main[203] + Main[204] +
        Main[205] + Main[206] + Main[207] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b201 b202 b203 b204 b205 b206 b207 b208 hsum h
  · have hsum : Main[202] + Main[201] + Main[203] + Main[204] +
        Main[205] + Main[206] + Main[207] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b202 b201 b203 b204 b205 b206 b207 b208 hsum h
  · have hsum : Main[203] + Main[201] + Main[202] + Main[204] +
        Main[205] + Main[206] + Main[207] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b203 b201 b202 b204 b205 b206 b207 b208 hsum h
  · have hsum : Main[204] + Main[201] + Main[202] + Main[203] +
        Main[205] + Main[206] + Main[207] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b204 b201 b202 b203 b205 b206 b207 b208 hsum h
  · have hsum : Main[205] + Main[201] + Main[202] + Main[203] +
        Main[204] + Main[206] + Main[207] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b205 b201 b202 b203 b204 b206 b207 b208 hsum h
  · have hsum : Main[206] + Main[201] + Main[202] + Main[203] +
        Main[204] + Main[205] + Main[207] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b206 b201 b202 b203 b204 b205 b207 b208 hsum h
  · have hsum : Main[207] + Main[201] + Main[202] + Main[203] +
        Main[204] + Main[205] + Main[206] + Main[208] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b207 b201 b202 b203 b204 b205 b206 b208 hsum h
  · have hsum : Main[208] + Main[201] + Main[202] + Main[203] +
        Main[204] + Main[205] + Main[206] + Main[207] = 1 := by
      linear_combination -sum_disj
    exact eight_mutex_left b208 b201 b202 b203 b204 b205 b206 b207 hsum h

/-- Polymorphic counterpart of `op_a_is_0` (line 1059). When `Main[6] = 0`
(i.e. the destination register is `x0`), the four limbs of `op_a_write_value`
(Main[28..31]) must be zero. -/
lemma op_a_is_0_poly (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold_poly)
    (h_is_real : is_real_poly Main) :
    Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 := by
  simp only [SP1ConstraintList.allHold_poly, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, SP1Constraint.toProp_poly_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real h_is_real] at h_alu
  obtain ⟨_, _, _, _, _, h_op_a_0_iff, _, _, h_zero⟩ := h_alu
  intro h_op_a_eq_0
  have h_op_a_0_eq_1 : Main[13] = 1 := h_op_a_0_iff.mpr h_op_a_eq_0
  have h_op_a_0_ne_0 : Main[13] ≠ 0 := by
    rw [h_op_a_0_eq_1]
    intro h_one_eq_zero
    haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
    have : (1 : ZMod p).val = 0 := by rw [h_one_eq_zero]; exact ZMod.val_zero
    rw [ZMod.val_one] at this
    omega
  have ⟨ha28, ha29, ha30, ha31⟩ := h_zero h_op_a_0_ne_0
  exact ⟨ha28, ha29, ha30, ha31⟩

end poly_helpers

end DivRem
