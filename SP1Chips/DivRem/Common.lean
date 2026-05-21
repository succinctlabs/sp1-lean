import SP1Chips.DivRem.Constraints

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
-- The chip's `correct_*` proofs drive an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at` that operates on one focused case at a
-- time. Rewriting each to `<;>` would flatten the tree but require goal-state
-- reasoning the linter can't see; keep the existing structure.
set_option linter.style.multiGoal false
set_option linter.style.longLine false


section auxiliaries

/-- Phrased at the `.val` level since `ZMod p` lacks native `% / /`
operators. The `c.val < 2` bound holds because at every use site `c` is a
carry bit (the `b_cry0..b_cry7 : cry = 0 ∨ cry = 1` family). The
wrap-around branch of `val_sub_cases` is ruled out via `Fact (2 ^ 17 < p)`
(else `a.val ≥ p - 65536 > 65536`, contradicting `a.val < 65536`). -/
lemma div_mod_decomposition_w {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
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

/-- Required by `divw_remw`'s 4-way `b_rem_neg × b_c_neg` h_abs block. -/
lemma sum_zero_abs {p : ℕ} [NeZero p] {wx wy : Word (ZMod p)}
    (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx.isNegative →
    Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p))
      = wx.toBitVec64 + wy.toBitVec64 →
    (wx.toInt = -2^63 → wy.toInt = -2^63) ∧
    (¬ wx.toInt = -2^63 → wy.toInt = |wx.toInt|) := by
  intro neg_wx sum_zero
  rw [Word.isNegative_toInt is64_wx] at neg_wx
  rw [Int.abs_cases, if_neg (by omega)]
  simp [← BitVec.toInt_inj] at sum_zero
  rw [Word.toBitVec64_toInt is64_wx, Word.toBitVec64_toInt is64_wy] at sum_zero
  simp [Word.toBitVec64, Word.toNat, ZMod.val_zero] at sum_zero
  apply Word.isU64_toInt at is64_wx
  apply Word.isU64_toInt at is64_wy
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
high limbs (`65535`s) has the same `toInt` as the 2-limb HWord. Used in
`divw_remw`'s h_abs negative-side cases (after `sum_zero_abs`). -/
lemma Word_toInt_neg_form_eq_HWord_toInt {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {c0 c1 : ZMod p}
    (h_neg : (32768 : ZMod p) ≤ c1)
    (h65535_val : (65535 : ZMod p).val = 65535) :
    Word.toInt (#v[c0, c1, 65535, 65535] : Word (ZMod p))
      = HWord.toInt (#v[c0, c1] : HWord (ZMod p)) := by
  have h17 : 2 ^ 17 < p := Fact.out
  have h131072 : 131072 < p := by omega
  have h32768_val : (32768 : ZMod p).val = 32768 :=
    ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by omega)
  have h_neg_nat : 32768 ≤ c1.val := by
    have : (32768 : ZMod p).val ≤ c1.val := h_neg
    rwa [h32768_val] at this
  unfold Word.toInt HWord.toInt Word.toNat HWord.toNat
    Word.isNegative HWord.isNegative
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  rw [if_pos (by rw [h65535_val]; omega), if_pos h_neg_nat]
  rw [h65535_val]; push_cast; ring

end auxiliaries


section poly_constraints_iff

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxRecDepth 1000000 in
-- Inner sub-constraint lists, `(...).val < N` Range bounds, and individual
-- `assertZero`-derived equalities/disjunctions are structurally identical
-- across field instantiations; only the outer `List.Forall` wrapper switches
-- to `SP1Constraint.toProp`.
lemma allHold_constraints_iff (Main : Vector (ZMod p) 246) :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
    (MulOperation.constraints
      #v[Main[68], Main[69], Main[70], Main[71]]
      #v[Main[44], Main[45], Main[46], Main[47]] #v[Main[36], Main[37], Main[38], Main[39]]
      {
        carry := #v[Main[76], Main[77], Main[78], Main[79], Main[80], Main[81], Main[82], Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89], Main[90], Main[91]],
        product := #v[Main[92], Main[93], Main[94], Main[95], Main[96], Main[97], Main[98], Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105], Main[106], Main[107]],
        b_lower_byte := { low_bytes := #v[Main[108], Main[109], Main[110], Main[111]] },
        c_lower_byte := { low_bytes := #v[Main[112], Main[113], Main[114], Main[115]] },
        b_msb := Main[116],
        c_msb := Main[117],
        product_msb := { msb := Main[118] },
        b_sign_extend := Main[119],
        c_sign_extend := Main[120]
      }
      Main[244] Main[244] 0 0 0 0) ∧
    List.Forall SP1Constraint.toProp
    (MulOperation.constraints
      #v[Main[72], Main[73], Main[74], Main[75]]
      #v[Main[44], Main[45], Main[46], Main[47]]
      #v[Main[36], Main[37], Main[38], Main[39]]
      {
        carry := #v[Main[121], Main[122], Main[123], Main[124], Main[125], Main[126], Main[127], Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134], Main[135], Main[136]],
        product := #v[Main[137], Main[138], Main[139], Main[140], Main[141], Main[142], Main[143], Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150], Main[151], Main[152]],
        b_lower_byte := { low_bytes := #v[Main[153], Main[154], Main[155], Main[156]] },
        c_lower_byte := { low_bytes := #v[Main[157], Main[158], Main[159], Main[160]] },
        b_msb := Main[161],
        c_msb := Main[162],
        product_msb := { msb := Main[163] },
        b_sign_extend := Main[164],
        c_sign_extend := Main[165]
      }
      Main[239] 0 (Main[201] + Main[203]) 0 (Main[202] + Main[204]) 0) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[0, 0, 0, 32768]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[210], result := Main[211] }, { inverse := Main[212], result := Main[213] }, { inverse := Main[214], result := Main[215] }, { inverse := Main[216], result := Main[217] }],
          is_zero_first_half := Main[218],
          is_zero_second_half := Main[219],
          result := Main[220]
        }
      }
      Main[239]) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[22], Main[23], Main[24], Main[25]]
      #v[65535, 65535, 65535, 65535]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[221], result := Main[222] }, { inverse := Main[223], result := Main[224] }, { inverse := Main[225], result := Main[226] }, { inverse := Main[227], result := Main[228] }],
          is_zero_first_half := Main[229],
          is_zero_second_half := Main[230],
          result := Main[231]
        }
      }
      Main[239]) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[15], Main[16], 0, 0]
      #v[0, 32768, 0, 0]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[210], result := Main[211] }, { inverse := Main[212], result := Main[213] }, { inverse := Main[214], result := Main[215] }, { inverse := Main[216], result := Main[217] }],
          is_zero_first_half := Main[218],
          is_zero_second_half := Main[219],
          result := Main[220]
        }
      }
      (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[22], Main[23], 0, 0]
      #v[65535, 65535, 0, 0]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[221], result := Main[222] }, { inverse := Main[223], result := Main[224] }, { inverse := Main[225], result := Main[226] }, { inverse := Main[227], result := Main[228] }],
          is_zero_first_half := Main[229],
          is_zero_second_half := Main[230],
          result := Main[231]
        }
      }
      (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    List.Forall SP1Constraint.toProp
    (IsZeroWordOperation.constraints
      #v[Main[36], Main[37], Main[38], Main[39]]
      {
        is_zero_limb := #v[{ inverse := Main[190], result := Main[191] }, { inverse := Main[192], result := Main[193] }, { inverse := Main[194], result := Main[195] }, { inverse := Main[196], result := Main[197] }],
        is_zero_first_half := Main[198],
        is_zero_second_half := Main[199],
        result := Main[200]
      }
      Main[244]) ∧
    List.Forall SP1Constraint.toProp
    (AddOperation.constraints
      #v[Main[36], Main[37], Main[38], Main[39]]
      #v[Main[60], Main[61], Main[62], Main[63]]
      { value := #v[Main[166], Main[167], Main[168], Main[169]] }
      Main[242]) ∧
    List.Forall SP1Constraint.toProp
    (AddOperation.constraints
      #v[Main[48], Main[49], Main[50], Main[51]]
      #v[Main[56], Main[57], Main[58], Main[59]]
      { value := #v[Main[170], Main[171], Main[172], Main[173]] }
      Main[243]) ∧
    List.Forall SP1Constraint.toProp
    (LtOperationUnsigned.constraints
      #v[Main[56], Main[57], Main[58], Main[59]]
      #v[Main[64], Main[65], Main[66], Main[67]]
      {
          u16_compare_operation := { bit := Main[174] },
          u16_flags := #v[Main[175], Main[176], Main[177], Main[178]]
          not_eq_inv := Main[179],
          comparison_limbs := #v[Main[180], Main[181]]
      }
      Main[245]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[18] { msb := Main[232] } Main[239]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[25] { msb := Main[234] } Main[239]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[55] { msb := Main[233] } Main[239]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[16] { msb := Main[232] } (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[23] { msb := Main[234] } (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[53] { msb := Main[233] } (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[41] { msb := Main[235] } (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 Main[244]) ∧
    List.Forall SP1Constraint.toProp
        (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]]
          (Main[202] * 16 + Main[204] * 18 + Main[201] * 15 + Main[203] * 17 + Main[205] * 25 + Main[206] * 27 + Main[207] * 26 + Main[208] * 28)
      #v[Main[28], Main[29], Main[30], Main[31]]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := Main[21],
            op_c_memory :=
              { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } }
          Main[244] Main[244]) ∧
    Main[239] = Main[244] * (1 - (Main[205] + Main[206] + Main[207] + Main[208])) ∧
    Main[236] = Main[232] * (Main[201] + Main[203] + Main[205] + Main[206]) ∧
    Main[240] = Main[233] * (Main[201] + Main[203] + Main[205] + Main[206]) ∧
    Main[241] = Main[234] * (Main[201] + Main[203] + Main[205] + Main[206]) ∧
    Main[15] = Main[32] ∧
    Main[22] = Main[36] ∧
    Main[16] = Main[33] ∧
    Main[23] = Main[37] ∧
    Main[34] = Main[17] * (1 - (Main[205] + Main[206] + Main[207] + Main[208])) + Main[236] * (Main[205] + Main[206] + Main[207] + Main[208]) * 65535 ∧
    Main[38] = Main[24] * (1 - (Main[205] + Main[206] + Main[207] + Main[208])) + Main[241] * (Main[205] + Main[206] + Main[207] + Main[208]) * 65535 ∧
    Main[35] = Main[18] * (1 - (Main[205] + Main[206] + Main[207] + Main[208])) + Main[236] * (Main[205] + Main[206] + Main[207] + Main[208]) * 65535 ∧
    Main[39] = Main[25] * (1 - (Main[205] + Main[206] + Main[207] + Main[208])) + Main[241] * (Main[205] + Main[206] + Main[207] + Main[208]) * 65535 ∧
    Main[44] = Main[40] ∧
    Main[45] = Main[41] ∧
    (Main[207] + Main[208] = 0 ∨ Main[46] = 0) ∧
    (Main[205] + Main[206] = 0 ∨ Main[46] = Main[235] * 65535) ∧
    (Main[205] + Main[206] + Main[207] + Main[208] = 0 ∨ Main[42] = Main[235] * 65535) ∧
    (Main[202] + Main[204] + Main[201] + Main[203] = 0 ∨ Main[46] = Main[42]) ∧
    (Main[207] + Main[208] = 0 ∨ Main[47] = 0) ∧
    (Main[205] + Main[206] = 0 ∨ Main[47] = Main[235] * 65535) ∧
    (Main[205] + Main[206] + Main[207] + Main[208] = 0 ∨ Main[43] = Main[235] * 65535) ∧
    (Main[202] + Main[204] + Main[201] + Main[203] = 0 ∨ Main[47] = Main[43]) ∧
    Main[48] = Main[52] ∧
    Main[49] = Main[53] ∧
    (Main[207] + Main[208] = 0 ∨ Main[50] = 0) ∧
    (Main[205] + Main[206] = 0 ∨ Main[50] = Main[233] * 65535) ∧
    (Main[205] + Main[206] + Main[207] + Main[208] = 0 ∨ Main[54] = Main[233] * 65535) ∧
    (Main[202] + Main[204] + Main[201] + Main[203] = 0 ∨ Main[50] = Main[54]) ∧
    (Main[207] + Main[208] = 0 ∨ Main[51] = 0) ∧
    (Main[205] + Main[206] = 0 ∨ Main[51] = Main[233] * 65535) ∧
    (Main[205] + Main[206] + Main[207] + Main[208] = 0 ∨ Main[55] = Main[233] * 65535) ∧
    (Main[202] + Main[204] + Main[201] + Main[203] = 0 ∨ Main[51] = Main[55]) ∧
    Main[209] = Main[220] * Main[231] * (Main[201] + Main[203] + Main[205] + Main[206]) ∧
    Main[237] = Main[236] * (1 - Main[209]) ∧
    Main[238] = (1 - Main[236]) * (1 - Main[209]) ∧
    (Main[209] = 0 ∨ Main[40] = Main[32]) ∧
    (Main[209] = 0 ∨ Main[52] = 0) ∧
    (Main[209] = 0 ∨ Main[41] = Main[33]) ∧
    (Main[209] = 0 ∨ Main[53] = 0) ∧
    (Main[209] = 0 ∨ Main[42] = Main[34]) ∧
    (Main[209] = 0 ∨ Main[54] = 0) ∧
    (Main[209] = 0 ∨ Main[43] = Main[35]) ∧
    (Main[209] = 0 ∨ Main[55] = 0) ∧
    (Main[209] = 1 ∨ Main[32] = Main[68] + Main[48] - Main[182] * 65536) ∧
    (Main[209] = 1 ∨ Main[33] = Main[69] + Main[49] - Main[183] * 65536 + Main[182]) ∧
    (Main[209] = 1 ∨ Main[34] = Main[70] + Main[50] - Main[184] * 65536 + Main[183]) ∧
    (Main[209] = 1 ∨ Main[35] = Main[71] + Main[51] - Main[185] * 65536 + Main[184]) ∧
    (Main[209] = 1 ∨ Main[236] * 65535 = Main[72] + Main[240] * 65535 - Main[186] * 65536 + Main[185]) ∧
    (Main[209] = 1 ∨ Main[236] * 65535 = Main[73] + Main[240] * 65535 - Main[187] * 65536 + Main[186]) ∧
    (Main[209] = 1 ∨ Main[236] * 65535 =  Main[74] + Main[240] * 65535 - Main[188] * 65536 + Main[187]) ∧
    (Main[209] = 1 ∨ Main[236] * 65535 = Main[75] + Main[240] * 65535 - Main[189] * 65536 + Main[188]) ∧
    (¬Main[244] = 0 → (Main[68] + Main[48] - Main[182] * 65536).val < 65536) ∧
    (¬Main[244] = 0 → (Main[69] + Main[49] - Main[183] * 65536 + Main[182]).val < 65536) ∧
    (¬Main[244] = 0 → (Main[70] + Main[50] - Main[184] * 65536 + Main[183]).val < 65536) ∧
    (¬Main[244] = 0 → (Main[71] + Main[51] - Main[185] * 65536 + Main[184]).val < 65536) ∧
    (¬Main[244] = 0 → (Main[72] + Main[240] * 65535 - Main[186] * 65536 + Main[185]).val < 65536) ∧
    (¬Main[244] = 0 → (Main[73] + Main[240] * 65535 - Main[187] * 65536 + Main[186]).val < 65536) ∧
    (¬Main[244] = 0 → (Main[74] + Main[240] * 65535 - Main[188] * 65536 + Main[187]).val < 65536) ∧
    (¬Main[244] = 0 → (Main[75] + Main[240] * 65535 - Main[189] * 65536 + Main[188]).val < 65536) ∧
    (Main[202] + Main[201] + Main[205] + Main[207] = 0 ∨ Main[40] = Main[28]) ∧
    (Main[204] + Main[203] + Main[206] + Main[208] = 0 ∨ Main[52] = Main[28]) ∧
    (Main[202] + Main[201] + Main[205] + Main[207] = 0 ∨ Main[41] = Main[29]) ∧
    (Main[204] + Main[203] + Main[206] + Main[208] = 0 ∨ Main[53] = Main[29]) ∧
    (Main[202] + Main[201] + Main[205] + Main[207] = 0 ∨ Main[42] = Main[30]) ∧
    (Main[204] + Main[203] + Main[206] + Main[208] = 0 ∨ Main[54] = Main[30]) ∧
    (Main[202] + Main[201] + Main[205] + Main[207] = 0 ∨ Main[43] = Main[31]) ∧
    (Main[204] + Main[203] + Main[206] + Main[208] = 0 ∨ Main[55] = Main[31]) ∧
    (Main[240] = 0 ∨ Main[236] = 1) ∧
    (Main[52] + Main[53] + Main[54] + Main[55] = 0 ∨ Main[240] = 1 ∨ Main[236] = 0) ∧
    (Main[200] = 0 ∨ Main[40] = 65535) ∧
    (Main[200] = 0 ∨ Main[41] = 65535) ∧
    (Main[200] = 0 ∨ Main[42] = 65535) ∧
    (Main[200] = 0 ∨ Main[43] = 65535) ∧
    (Main[200] = 0 ∨ Main[48] = Main[32]) ∧
    (Main[200] = 0 ∨ Main[49] = Main[33]) ∧
    (Main[200] = 0 ∨ Main[50] = Main[34]) ∧
    (Main[200] = 0 ∨ Main[51] = Main[35]) ∧
    (Main[241] = 1 ∨ Main[36] = Main[60]) ∧
    (Main[240] = 1 ∨ Main[48] = Main[56]) ∧
    (Main[241] = 1 ∨ Main[37] = Main[61]) ∧
    (Main[240] = 1 ∨ Main[49] = Main[57]) ∧
    (Main[241] = 1 ∨ Main[38] = Main[62]) ∧
    (Main[240] = 1 ∨ Main[50] = Main[58]) ∧
    (Main[241] = 1 ∨ Main[39] = Main[63]) ∧
    (Main[240] = 1 ∨ Main[51] = Main[59]) ∧
    (¬Main[244] = 0 → Main[60].val < 65536) ∧
    (¬Main[244] = 0 → Main[61].val < 65536) ∧
    (¬Main[244] = 0 → Main[62].val < 65536) ∧
    (¬Main[244] = 0 → Main[63].val < 65536) ∧
    (Main[242] = 0 ∨ Main[166] = 0) ∧
    (Main[242] = 0 ∨ Main[167] = 0) ∧
    (Main[242] = 0 ∨ Main[168] = 0) ∧
    (Main[242] = 0 ∨ Main[169] = 0) ∧
    (¬Main[244] = 0 → Main[56].val < 65536) ∧
    (¬Main[244] = 0 → Main[57].val < 65536) ∧
    (¬Main[244] = 0 → Main[58].val < 65536) ∧
    (¬Main[244] = 0 → Main[59].val < 65536) ∧
    (Main[243] = 0 ∨ Main[170] = 0) ∧
    (Main[243] = 0 ∨ Main[171] = 0) ∧
    (Main[243] = 0 ∨ Main[172] = 0) ∧
    (Main[243] = 0 ∨ Main[173] = 0) ∧
    Main[242] = Main[241] * Main[244] ∧
    Main[243] = Main[240] * Main[244] ∧
    Main[64] = Main[200] + (1 - Main[200]) * Main[60] ∧
    Main[65] = (1 - Main[200]) * Main[61] ∧
    Main[66] = (1 - Main[200]) * Main[62] ∧
    Main[67] = (1 - Main[200]) * Main[63] ∧
    Main[245] = (1 - Main[200]) * Main[244] ∧
    (Main[245] = 0 ∨ Main[174] = 1) ∧
    (¬Main[244] = 0 → Main[40].val < 65536) ∧
    (¬Main[244] = 0 → Main[41].val < 65536) ∧
    (¬Main[244] = 0 → Main[42].val < 65536) ∧
    (¬Main[244] = 0 → Main[43].val < 65536) ∧
    (¬Main[244] = 0 → Main[52].val < 65536) ∧
    (¬Main[244] = 0 → Main[53].val < 65536) ∧
    (¬Main[244] = 0 → Main[54].val < 65536) ∧
    (¬Main[244] = 0 → Main[55].val < 65536) ∧
    (Main[182] = 0 ∨ Main[182] = 1) ∧
    (Main[183] = 0 ∨ Main[183] = 1) ∧
    (Main[184] = 0 ∨ Main[184] = 1) ∧
    (Main[185] = 0 ∨ Main[185] = 1) ∧
    (Main[186] = 0 ∨ Main[186] = 1) ∧
    (Main[187] = 0 ∨ Main[187] = 1) ∧
    (Main[188] = 0 ∨ Main[188] = 1) ∧
    (Main[189] = 0 ∨ Main[189] = 1) ∧
    (¬Main[244] = 0 → Main[68].val < 65536) ∧
    (¬Main[244] = 0 → Main[69].val < 65536) ∧
    (¬Main[244] = 0 → Main[70].val < 65536) ∧
    (¬Main[244] = 0 → Main[71].val < 65536) ∧
    (¬Main[244] = 0 → Main[72].val < 65536) ∧
    (¬Main[244] = 0 → Main[73].val < 65536) ∧
    (¬Main[244] = 0 → Main[74].val < 65536) ∧
    (¬Main[244] = 0 → Main[75].val < 65536) ∧
    (Main[201] = 0 ∨ Main[201] = 1) ∧
    (Main[202] = 0 ∨ Main[202] = 1) ∧
    (Main[203] = 0 ∨ Main[203] = 1) ∧
    (Main[204] = 0 ∨ Main[204] = 1) ∧
    (Main[205] = 0 ∨ Main[205] = 1) ∧
    (Main[206] = 0 ∨ Main[206] = 1) ∧
    (Main[207] = 0 ∨ Main[207] = 1) ∧
    (Main[208] = 0 ∨ Main[208] = 1) ∧
    (Main[209] = 0 ∨ Main[209] = 1) ∧
    (Main[239] = 0 ∨ Main[239] = 1) ∧
    (Main[236] = 0 ∨ Main[236] = 1) ∧
    (Main[237] = 0 ∨ Main[237] = 1) ∧
    (Main[238] = 0 ∨ Main[238] = 1) ∧
    (Main[240] = 0 ∨ Main[240] = 1) ∧
    (Main[241] = 0 ∨ Main[241] = 1) ∧
    (Main[244] = 0 ∨ Main[244] = 1) ∧
    (Main[242] = 0 ∨ Main[242] = 1) ∧
    (Main[243] = 0 ∨ Main[243] = 1) ∧
    Main[202] + Main[204] + Main[201] + Main[203] + Main[205] + Main[206] + Main[207] + Main[208] = 1 ∧
    Main[13] = 0
  := by
    simp [constraints, sub_eq_zero, and_assoc]
    iterate 3 rw [eq_comm (a := _ * (Main[201] + Main[203] + Main[205] + Main[206]))]
    iterate 3 rw [eq_comm (a := (1 : ZMod p))]
    rw [eq_comm (a := _ * _) (b := Main[245])]
    simp [neg_eq_zero]

end poly_constraints_iff

attribute [-simp] mul_eq_zero not_and

section poly_helpers

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

@[simp] def is_real (Main : Vector (ZMod p) 246) : Prop :=
  Main[244] = 1
  deriving Decidable

@[simp] def is_div (Main : Vector (ZMod p) 246) : Prop := Main[201] = 1
  deriving Decidable
@[simp] def is_divu (Main : Vector (ZMod p) 246) : Prop := Main[202] = 1
  deriving Decidable
@[simp] def is_rem (Main : Vector (ZMod p) 246) : Prop := Main[203] = 1
  deriving Decidable
@[simp] def is_remu (Main : Vector (ZMod p) 246) : Prop := Main[204] = 1
  deriving Decidable
@[simp] def is_divw (Main : Vector (ZMod p) 246) : Prop := Main[205] = 1
  deriving Decidable
@[simp] def is_remw (Main : Vector (ZMod p) 246) : Prop := Main[206] = 1
  deriving Decidable
@[simp] def is_divuw (Main : Vector (ZMod p) 246) : Prop := Main[207] = 1
  deriving Decidable
@[simp] def is_remuw (Main : Vector (ZMod p) 246) : Prop := Main[208] = 1
  deriving Decidable

@[simp] def sp1_op_a (Main : Vector (ZMod p) 246) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

@[simp] def sp1_op_b (Main : Vector (ZMod p) 246) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

@[simp] def sp1_op_c (Main : Vector (ZMod p) 246) : BitVec 5 :=
  BitVec.ofNat 5 Main[21].val

/-- Both `b` and `c` operands are 64-bit values. Uses
`RTypeReader.allHold_constraints_iff_is_real` after extracting CS18
(the RTypeReader sub-list) via direct destructure of the chip's
`allHold`. The 18-deep nested left-pair pattern mirrors
`List.forall_append`'s expansion of the `CS0 ++ CS1 ++ ... ++ CS18 ++ trailing`
constraint list (19 CS entries). -/
lemma ops_U64_b_c (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main) :
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  obtain ⟨_, _, _, _, _, _, _, h_complex, _⟩ := h_alu
  obtain ⟨_, _, _, h_isU64_b, h_isU64_c⟩ := h_complex
  exact ⟨h_isU64_b, h_isU64_c⟩

/-- Variant-INDEPENDENT bounds available directly from
`RTypeReader.allHold_constraints_iff_is_real`: `op_a < 32`,
`op_b < 65536`, `op_c < 65536`, `pc[0] < 65536`. Chip-level
`correct_*` proofs further refine `op_b < 32` / `op_c < 32` via
per-variant opcode reduction (`Opcode.ofNat`) once the variant flag is
in scope. -/
lemma register_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main) :
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
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
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

/-- 8-way mutual exclusion: exactly one variant flag among `Main[201..208]`
is active per real row. The proof destructures the chip's `allHold`
over its 19-CS-entry constraint list + 153-item trailing list (positions
134-141 carry the boolean disjunctions for `Main[201..208]`, position 152
carries the `1 = sum` constraint), then applies `eight_mutex_left` for
each variant after permuting the sum to put the active flag first via
`linear_combination`. -/
lemma single_op (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold) :
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
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
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

/-- When `Main[6] = 0` (i.e. the destination register is `x0`), the four
limbs of `op_a_write_value` (Main[28..31]) must be zero. -/
lemma op_a_is_0 (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main) :
    Main[6] = 0 → Main[28] = 0 ∧ Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 := by
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
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

omit [Fact (2 ^ 17 < p)] in
/-- Closer for the maco-form arm of `spec.<v>` proofs. Extracted into a
named lemma so the case-split on `is_c_0 ∈ {0,1}` runs in a small fresh
context (avoiding the `simp_all` stack overflow that an inline closer hits
against the full spec-proof hypothesis pile). The goal arrives in expanded
form (`maco1<i>` already substituted by the earlier `all_goals` simp). Used
by `spec.{divu,remu,divuw,remuw,divw,remw,div,rem}`. -/
lemma maco_arm_closer
    {is_c_0 ac0 ac1 ac2 ac3 : ZMod p}
    (u16_ac0 : ac0.val < 65536) (u16_ac1 : ac1.val < 65536)
    (u16_ac2 : ac2.val < 65536) (u16_ac3 : ac3.val < 65536)
    (h_bin : is_c_0 = 0 ∨ is_c_0 = 1) :
    Word.isU64 (#v[is_c_0 + (1 - is_c_0) * ac0,
                          (1 - is_c_0) * ac1,
                          (1 - is_c_0) * ac2,
                          (1 - is_c_0) * ac3] : Word (ZMod p)) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  rcases h_bin with h0 | h1
  · subst h0
    simp only [zero_add, sub_zero, one_mul]
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ] <;>
      assumption
  · subst h1
    simp only [sub_self, zero_mul, add_zero]
    apply Word.isU64_of_cases <;>
      simp [ZMod.val_one, ZMod.val_zero]

/-- Closer for the divw/remw / div/rem signed sign-extension arm of
`spec.<v>` proofs. The high two limbs of the constructed word are
`msb * 65535`; given `msb ∈ {0, 1}` they reduce to `0` or `65535`, both U16.
Used by `spec.{divw,remw,div,rem}` to close the rbc/qbc-bearing
`Word.isU64` arms. Polymorphic in the two low limbs (x, y) and in
which msb (msb_rem or msb_quot) is bound. -/
lemma msb_arm_closer
    {x y msb : ZMod p}
    (u16_x : x.val < 65536) (u16_y : y.val < 65536)
    (h_msb_01 : msb = 0 ∨ msb = 1) :
    Word.isU64 (#v[x, y, msb * 65535, msb * 65535] : Word (ZMod p)) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hp17 : 2 ^ 17 < p := Fact.out
  have h65535_val : (65535 : ZMod p).val = 65535 :=
    ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  apply Word.isU64_of_cases <;>
    simp only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · exact u16_x
  · exact u16_y
  · rcases h_msb_01 with h | h
    · rw [h, zero_mul]; simp [ZMod.val_zero]
    · rw [h, one_mul, h65535_val]; omega
  · rcases h_msb_01 with h | h
    · rw [h, zero_mul]; simp [ZMod.val_zero]
    · rw [h, one_mul, h65535_val]; omega

/-- Variant-specific < 32 bounds for op_a/op_b/op_c plus the U64 properties of
operand words, derived from the chip's `allHold` with the divu opcode
trust. Used by `correct_divu` so the heavy reader destructure stays in
this file (avoids the chip-proof body's elaborator stack overflow). -/
lemma divu_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_divu : is_divu Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_divu] at h_is_divu
  obtain ⟨_sop1, sop2, _sop3, _sop4, _sop5, _sop6, _sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_rem, z_remu, z_divw, z_remw, z_divuw, z_remuw⟩ := sop2 h_is_divu
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_divu, z_div, z_rem, z_remu, z_divw, z_remw, z_divuw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `div` opcode. -/
lemma div_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_div : is_div Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_div] at h_is_div
  obtain ⟨sop1, _sop2, _sop3, _sop4, _sop5, _sop6, _sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_divu, z_rem, z_remu, z_divw, z_remw, z_divuw, z_remuw⟩ := sop1 h_is_div
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_div, z_divu, z_rem, z_remu, z_divw, z_remw, z_divuw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `rem` opcode. -/
lemma rem_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_rem : is_rem Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_rem] at h_is_rem
  obtain ⟨_sop1, _sop2, sop3, _sop4, _sop5, _sop6, _sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_divu, z_remu, z_divw, z_remw, z_divuw, z_remuw⟩ := sop3 h_is_rem
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_rem, z_div, z_divu, z_remu, z_divw, z_remw, z_divuw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `remu` opcode. -/
lemma remu_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_remu : is_remu Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_remu] at h_is_remu
  obtain ⟨_sop1, _sop2, _sop3, sop4, _sop5, _sop6, _sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_divu, z_rem, z_divw, z_remw, z_divuw, z_remuw⟩ := sop4 h_is_remu
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_remu, z_div, z_divu, z_rem, z_divw, z_remw, z_divuw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `divw` opcode. -/
lemma divw_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_divw : is_divw Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_divw] at h_is_divw
  obtain ⟨_sop1, _sop2, _sop3, _sop4, sop5, _sop6, _sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_divu, z_rem, z_remu, z_remw, z_divuw, z_remuw⟩ := sop5 h_is_divw
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_divw, z_div, z_divu, z_rem, z_remu, z_remw, z_divuw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `remw` opcode. -/
lemma remw_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_remw : is_remw Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_remw] at h_is_remw
  obtain ⟨_sop1, _sop2, _sop3, _sop4, _sop5, sop6, _sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_divu, z_rem, z_remu, z_divw, z_divuw, z_remuw⟩ := sop6 h_is_remw
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_remw, z_div, z_divu, z_rem, z_remu, z_divw, z_divuw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `divuw` opcode. -/
lemma divuw_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_divuw : is_divuw Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_divuw] at h_is_divuw
  obtain ⟨_sop1, _sop2, _sop3, _sop4, _sop5, _sop6, sop7, _sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_divu, z_rem, z_remu, z_divw, z_remw, z_remuw⟩ := sop7 h_is_divuw
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_divuw, z_div, z_divu, z_rem, z_remu, z_divw, z_remw, z_remuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

/-- Variant-specific < 32 bounds for the `remuw` opcode. -/
lemma remuw_chip_bounds (Main : Vector (ZMod p) 246)
    (cstrs : (constraints Main).allHold)
    (h_is_real : is_real Main)
    (h_is_remuw : is_remuw Main) :
    Main[6].val < 32 ∧ Main[14].val < 32 ∧ Main[21].val < 32 ∧
    Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
    Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  simp [is_remuw] at h_is_remuw
  obtain ⟨_sop1, _sop2, _sop3, _sop4, _sop5, _sop6, _sop7, sop8⟩ := single_op Main cstrs
  obtain ⟨z_div, z_divu, z_rem, z_remu, z_divw, z_remw, z_divuw⟩ := sop8 h_is_remuw
  simp only [SP1ConstraintList.allHold, constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_assertZero, SP1Constraint.toProp_send_byte,
    sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h_alu⟩, _⟩ := cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real h_is_real h_is_real] at h_alu
  simp [Opcode.ofNat, Nat.ble, h_is_remuw, z_div, z_divu, z_rem, z_remu, z_divw, z_remw, z_divuw]
    at h_alu
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b, is_U64_c⟩⟩, _⟩⟩ := h_alu
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  refine ⟨?_, ?_, ?_, is_U64_b, is_U64_c⟩
  · have : Main[6].val < (32 : ZMod p).val := h_op_a_lt; rwa [h32] at this
  · have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1; rwa [h32] at this
  · have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2; rwa [h32] at this

end poly_helpers

section divrem_kernel_helpers

/-- Opaque alias for `2 ^ 128` — referenced in the close-helpers' types so the kernel
re-check at chip call sites doesn't walk the literal. The `2^128` is walked exactly
once inside each of the custom `BitVec.toNat_*_128` lemma oleans and inside `divrem_N128_eq`. -/
@[irreducible] def divrem_N128 : ℕ := 2 ^ 128

lemma divrem_N128_eq : divrem_N128 = 2 ^ 128 := by
  unfold divrem_N128; rfl

/-- Custom `BitVec.toNat_ofNat` specialized to width 128, concluding in the opaque
`divrem_N128` alias. Use in place of `BitVec.toNat_ofNat` inside the DivRem cores'
simp sets to keep `2^128` out of the chip's proof term. -/
lemma BitVec.toNat_ofNat_128 (k : ℕ) :
    (BitVec.ofNat 128 k).toNat = k % divrem_N128 := by
  rw [divrem_N128_eq, _root_.BitVec.toNat_ofNat]

/-- Custom `BitVec.toNat_add` specialized to width 128, concluding in the opaque
`divrem_N128` alias. -/
lemma BitVec.toNat_add_128 (x y : BitVec 128) :
    (x + y).toNat = (x.toNat + y.toNat) % divrem_N128 := by
  rw [divrem_N128_eq, _root_.BitVec.toNat_add]

/-- Bare-`Nat` close-helper for `divu_remu`'s final mod step. Both type and proof
body reference `divrem_N128` (opaque). Manual `Nat.add_mod` + `Nat.add_mul_mod_self_right`
chain avoids `omega`'s `Int.toNat (… % 2^128)` certificate (which trips the kernel). -/
lemma divu_remu_close_helper
    (b0 b1 b2 b3 r0 r1 r2 r3 : ℕ)
    (ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 : ℕ)
    (cry7 : ℕ)
    (h_main :
      b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656 +
        cry7 * divrem_N128 =
      ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
        ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
        ctq6 * 79228162514264337593543950336 +
        ctq7 * 5192296858534827628530496329220096 +
      (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656)) :
    (b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656) % divrem_N128 =
      ((ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
          ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
          ctq6 * 79228162514264337593543950336 +
          ctq7 * 5192296858534827628530496329220096) % divrem_N128 +
        (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656) % divrem_N128) %
      divrem_N128 := by
  rw [← Nat.add_mod, ← h_main, Nat.add_mul_mod_self_right]

/-- Signed-variant close-helper for `div_rem` (mirrors `divu_remu_close_helper`
but with the `msb_b * 65535` and `msb_rem * 65535` sign-extension terms in upper limbs
of `b` and `r`). -/
lemma div_rem_close_helper
    (b0 b1 b2 b3 r0 r1 r2 r3 : ℕ)
    (ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 : ℕ)
    (msb_b_ext msb_rem_ext : ℕ)
    (cry7 : ℕ)
    (h_main :
      b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656 +
        msb_b_ext * 18446744073709551616 + msb_b_ext * 1208925819614629174706176 +
        msb_b_ext * 79228162514264337593543950336 +
        msb_b_ext * 5192296858534827628530496329220096 +
        cry7 * divrem_N128 =
      ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
        ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
        ctq6 * 79228162514264337593543950336 +
        ctq7 * 5192296858534827628530496329220096 +
      (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656 +
        msb_rem_ext * 18446744073709551616 +
        msb_rem_ext * 1208925819614629174706176 +
        msb_rem_ext * 79228162514264337593543950336 +
        msb_rem_ext * 5192296858534827628530496329220096)) :
    (b0 + b1 * 65536 + b2 * 4294967296 + b3 * 281474976710656 +
        msb_b_ext * 18446744073709551616 + msb_b_ext * 1208925819614629174706176 +
        msb_b_ext * 79228162514264337593543950336 +
        msb_b_ext * 5192296858534827628530496329220096) % divrem_N128 =
      ((ctq0 + ctq1 * 65536 + ctq2 * 4294967296 + ctq3 * 281474976710656 +
          ctq4 * 18446744073709551616 + ctq5 * 1208925819614629174706176 +
          ctq6 * 79228162514264337593543950336 +
          ctq7 * 5192296858534827628530496329220096) % divrem_N128 +
        (r0 + r1 * 65536 + r2 * 4294967296 + r3 * 281474976710656 +
          msb_rem_ext * 18446744073709551616 +
          msb_rem_ext * 1208925819614629174706176 +
          msb_rem_ext * 79228162514264337593543950336 +
          msb_rem_ext * 5192296858534827628530496329220096) % divrem_N128) %
      divrem_N128 := by
  rw [← Nat.add_mod, ← h_main, Nat.add_mul_mod_self_right]

end divrem_kernel_helpers

section divrem_h_prod_helper

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- 32M heartbeats + 1M recursion: matches `div_rem`'s budget for the same
-- proof body (8-limb DWord carry chain + Stage A signExtend + close-helper).
/-- Extracted `h_prod` for `div_rem` (signed 64-bit DRS branch).

Lifted from `SP1Chips/DivRem/DivRem.lean:429-646` so its kernel re-check runs in
its own olean independently from `div_rem`'s. The body would otherwise add
`2^128` walks (via `simp at ctq` from `combine_MUL_MULH`, the `Word.extend`
unfoldings, Stage A signExtend chain, and the Step B `DWord.toBitVec128` simps)
to `div_rem`'s kernel check, summing past the kernel's WHNF reduction depth.

Inputs are the post-`simp at *` specialized forms of the chip-level hypotheses
(non-overflow branch, `is_div + is_rem = 1` so all `is_*` flags except is_div/rem
are 0 and `is_word = 0`). Caller derives `is_U64_q`, `is_U64_r` from `u16_q*`,
`u16_r*` + `b_cry*`, and specializes `eq_msb_b`, `eq_msb_rem`, the `nof_eq_ctqpr*`
disjunctions, the `u16_ctqpr*` bounds, `main_mul_low`, and `main_mul_high` before
the call. -/
lemma div_rem_h_prod_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    [Fact (2 ^ 24 < p)]
    {b0 b1 b2 b3 c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3
     ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7
     cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7
     msb_b msb_rem : ZMod p}
    (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_q : Word.isU64 #v[q0, q1, q2, q3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (eq_msb_b : msb_b = if 32768 ≤ b3 then 1 else 0)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (b_cry0 : cry0 = 0 ∨ cry0 = 1) (b_cry1 : cry1 = 0 ∨ cry1 = 1)
    (b_cry2 : cry2 = 0 ∨ cry2 = 1) (b_cry3 : cry3 = 0 ∨ cry3 = 1)
    (b_cry4 : cry4 = 0 ∨ cry4 = 1) (b_cry5 : cry5 = 0 ∨ cry5 = 1)
    (b_cry6 : cry6 = 0 ∨ cry6 = 1) (b_cry7 : cry7 = 0 ∨ cry7 = 1)
    (nof_eq_ctqpr0 : b0 = ctq0 + r0 - cry0 * 65536)
    (nof_eq_ctqpr1 : b1 = ctq1 + r1 - cry1 * 65536 + cry0)
    (nof_eq_ctqpr2 : b2 = ctq2 + r2 - cry2 * 65536 + cry1)
    (nof_eq_ctqpr3 : b3 = ctq3 + r3 - cry3 * 65536 + cry2)
    (nof_eq_ctqpr4 : ctq4 + msb_rem * 65535 - cry4 * 65536 + cry3 = msb_b * 65535)
    (nof_eq_ctqpr5 : ctq5 + msb_rem * 65535 - cry5 * 65536 + cry4 = msb_b * 65535)
    (nof_eq_ctqpr6 : ctq6 + msb_rem * 65535 - cry6 * 65536 + cry5 = msb_b * 65535)
    (nof_eq_ctqpr7 : ctq7 + msb_rem * 65535 - cry7 * 65536 + cry6 = msb_b * 65535)
    (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
    (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
    (u16_ctqpr2 : (ctq2 + r2 - cry2 * 65536 + cry1).val < 65536)
    (u16_ctqpr3 : (ctq3 + r3 - cry3 * 65536 + cry2).val < 65536)
    (u16_ctqpr4 : (ctq4 + msb_rem * 65535 - cry4 * 65536 + cry3).val < 65536)
    (u16_ctqpr5 : (ctq5 + msb_rem * 65535 - cry5 * 65536 + cry4).val < 65536)
    (u16_ctqpr6 : (ctq6 + msb_rem * 65535 - cry6 * 65536 + cry5).val < 65536)
    (u16_ctqpr7 : (ctq7 + msb_rem * 65535 - cry7 * 65536 + cry6).val < 65536)
    (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧
        Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] =
          execute_MUL_pure (Word.toBitVec64 #v[q0, q1, q2, q3])
            (Word.toBitVec64 #v[c0, c1, c2, c3]) mop.MUL)
    (main_mul_high : Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧
        Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] =
          execute_MUL_pure (Word.toBitVec64 #v[q0, q1, q2, q3])
            (Word.toBitVec64 #v[c0, c1, c2, c3]) mop.MULH) :
    Word.toInt #v[b0, b1, b2, b3] =
      Word.toInt #v[q0, q1, q2, q3] * Word.toInt #v[c0, c1, c2, c3] +
      Word.toInt #v[r0, r1, r2, r3] := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h17 : 2 ^ 17 < p := Fact.out
  have h24 : 2 ^ 24 < p := Fact.out
  have h65535_val : (65535 : ZMod p).val = 65535 := by
    have h : ((65535 : ℕ) : ZMod p).val = 65535 := ZMod.val_natCast_of_lt (by omega)
    simpa using h
  have h32768_val : (32768 : ZMod p).val = 32768 := by
    have h : ((32768 : ℕ) : ZMod p).val = 32768 := ZMod.val_natCast_of_lt (by omega)
    exact_mod_cast h
  have h1v : (1 : ZMod p).val = 1 := by
    have : ((1 : ℕ) : ZMod p).val = 1 := ZMod.val_natCast_of_lt (by omega)
    simpa using this
  have h0v : (0 : ZMod p).val = 0 := ZMod.val_zero
  have hcv0 : cry0.val ≤ 1 := by rcases b_cry0 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv1 : cry1.val ≤ 1 := by rcases b_cry1 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv2 : cry2.val ≤ 1 := by rcases b_cry2 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv3 : cry3.val ≤ 1 := by rcases b_cry3 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv4 : cry4.val ≤ 1 := by rcases b_cry4 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv5 : cry5.val ≤ 1 := by rcases b_cry5 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv6 : cry6.val ≤ 1 := by rcases b_cry6 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have hcv7 : cry7.val ≤ 1 := by rcases b_cry7 with h | h <;> rw [h] <;> simp [h0v, h1v]
  have u16_msb_b_v : (msb_b * 65535).val < 65536 := by
    rw [eq_msb_b]; split_ifs <;> simp [h0v, h65535_val]
  have u16_msb_rem_v : (msb_rem * 65535).val < 65536 := by
    rw [eq_msb_rem]; split_ifs <;> simp [h0v, h65535_val]
  have heq32_b3 : (32768 : ZMod p) ≤ b3 ↔ 32768 ≤ b3.val := by
    change (32768 : ZMod p).val ≤ b3.val ↔ _; rw [val_32768_zmod_p]
  have heq32_r3 : (32768 : ZMod p) ≤ r3 ↔ 32768 ≤ r3.val := by
    change (32768 : ZMod p).val ≤ r3.val ↔ _; rw [val_32768_zmod_p]
  obtain ⟨is_U64_ctql, ctq_low⟩ := main_mul_low
  obtain ⟨is_U64_ctqh, ctq_high⟩ := main_mul_high
  have ctq := combine_MUL_MULH is_U64_ctql is_U64_ctqh is_U64_q is_U64_c
    ctq_low ctq_high
  simp at ctq
  have eq_eb : (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535,
        msb_b * 65535, msb_b * 65535] : DWord (ZMod p)) =
      Word.extend #v[b0, b1, b2, b3] true := by
    simp [Word.extend, Word.isNegative, eq_msb_b, heq32_b3]
  have eq_er : (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535,
        msb_rem * 65535, msb_rem * 65535] : DWord (ZMod p)) =
      Word.extend #v[r0, r1, r2, r3] true := by
    simp [Word.extend, Word.isNegative, eq_msb_rem, heq32_r3]
  suffices bv_ctqr :
    DWord.toBitVec128 (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535,
        msb_b * 65535, msb_b * 65535] : DWord (ZMod p)) =
      DWord.toBitVec128 (#v[ctq0, ctq1, ctq2, ctq3,
        ctq4, ctq5, ctq6, ctq7] : DWord (ZMod p)) +
      DWord.toBitVec128 (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535,
        msb_rem * 65535, msb_rem * 65535] : DWord (ZMod p)) by
    rw [eq_eb, eq_er] at bv_ctqr
    rw [ctq] at bv_ctqr
    repeat rw [Word.extend_true_is_signExtend (by assumption)] at bv_ctqr
    simp [← BitVec.toInt_inj] at bv_ctqr
    repeat rw [BitVec.toInt_signExtend_of_le (by simp)] at bv_ctqr
    repeat rw [Word.toBitVec64_toInt (by assumption)] at bv_ctqr
    have lbq := Word.toInt_lb is_U64_q
    have ubq := Word.toInt_ub is_U64_q
    have lbr := Word.toInt_lb is_U64_r
    have ubr := Word.toInt_ub is_U64_r
    have lbc := Word.toInt_lb is_U64_c
    have ubc := Word.toInt_ub is_U64_c
    rw [bv_ctqr]
    apply Int.bmod_eq_of_le <;> simp <;> nlinarith
  · clear is_U64_c eq_msb_b eq_msb_rem ctq_low ctq_high ctq eq_eb eq_er
    apply Word.lt_cases_of_isU64 at is_U64_b
    apply Word.lt_cases_of_isU64 at is_U64_r
    apply Word.lt_cases_of_isU64 at is_U64_q
    apply Word.lt_cases_of_isU64 at is_U64_ctql
    apply Word.lt_cases_of_isU64 at is_U64_ctqh
    simp at *
    rw [eq_comm] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
    rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                                 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                                 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                                 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6
                                 nof_eq_ctqpr7
    rw [div_mod_decomposition_w (by omega) (by omega : cry0.val < 2)]
      at nof_eq_ctqpr0
    rw [div_mod_decomposition_w (by omega) (by omega : cry1.val < 2)]
      at nof_eq_ctqpr1
    rw [div_mod_decomposition_w (by omega) (by omega : cry2.val < 2)]
      at nof_eq_ctqpr2
    rw [div_mod_decomposition_w (by omega) (by omega : cry3.val < 2)]
      at nof_eq_ctqpr3
    rw [div_mod_decomposition_w (by omega) (by omega : cry4.val < 2)]
      at nof_eq_ctqpr4
    rw [div_mod_decomposition_w (by omega) (by omega : cry5.val < 2)]
      at nof_eq_ctqpr5
    rw [div_mod_decomposition_w (by omega) (by omega : cry6.val < 2)]
      at nof_eq_ctqpr6
    rw [div_mod_decomposition_w (by omega) (by omega : cry7.val < 2)]
      at nof_eq_ctqpr7
    obtain ⟨b0_lt, b1_lt, b2_lt, b3_lt⟩ := is_U64_b
    obtain ⟨r0_lt, r1_lt, r2_lt, r3_lt⟩ := is_U64_r
    obtain ⟨ctq0_lt, ctq1_lt, ctq2_lt, ctq3_lt⟩ := is_U64_ctql
    obtain ⟨ctq4_lt, ctq5_lt, ctq6_lt, ctq7_lt⟩ := is_U64_ctqh
    have hsum01 : (ctq0 + r0).val = ctq0.val + r0.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum1' : (ctq1 + r1).val = ctq1.val + r1.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum1 : (ctq1 + r1 + cry0).val = ctq1.val + r1.val + cry0.val := by
      rw [show (ctq1 + r1 + cry0) = (ctq1 + r1) + cry0 from rfl,
          ZMod.val_add_of_lt (by rw [hsum1']; omega), hsum1']
    have hsum2' : (ctq2 + r2).val = ctq2.val + r2.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum2 : (ctq2 + r2 + cry1).val = ctq2.val + r2.val + cry1.val := by
      rw [show (ctq2 + r2 + cry1) = (ctq2 + r2) + cry1 from rfl,
          ZMod.val_add_of_lt (by rw [hsum2']; omega), hsum2']
    have hsum3' : (ctq3 + r3).val = ctq3.val + r3.val :=
      ZMod.val_add_of_lt (by omega)
    have hsum3 : (ctq3 + r3 + cry2).val = ctq3.val + r3.val + cry2.val := by
      rw [show (ctq3 + r3 + cry2) = (ctq3 + r3) + cry2 from rfl,
          ZMod.val_add_of_lt (by rw [hsum3']; omega), hsum3']
    have hsum4' : (ctq4 + msb_rem * 65535).val =
        ctq4.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum4 : (ctq4 + msb_rem * 65535 + cry3).val =
        ctq4.val + (msb_rem * 65535).val + cry3.val := by
      rw [show (ctq4 + msb_rem * 65535 + cry3) =
            (ctq4 + msb_rem * 65535) + cry3 from rfl,
          ZMod.val_add_of_lt (by rw [hsum4']; omega), hsum4']
    have hsum5' : (ctq5 + msb_rem * 65535).val =
        ctq5.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum5 : (ctq5 + msb_rem * 65535 + cry4).val =
        ctq5.val + (msb_rem * 65535).val + cry4.val := by
      rw [show (ctq5 + msb_rem * 65535 + cry4) =
            (ctq5 + msb_rem * 65535) + cry4 from rfl,
          ZMod.val_add_of_lt (by rw [hsum5']; omega), hsum5']
    have hsum6' : (ctq6 + msb_rem * 65535).val =
        ctq6.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum6 : (ctq6 + msb_rem * 65535 + cry5).val =
        ctq6.val + (msb_rem * 65535).val + cry5.val := by
      rw [show (ctq6 + msb_rem * 65535 + cry5) =
            (ctq6 + msb_rem * 65535) + cry5 from rfl,
          ZMod.val_add_of_lt (by rw [hsum6']; omega), hsum6']
    have hsum7' : (ctq7 + msb_rem * 65535).val =
        ctq7.val + (msb_rem * 65535).val :=
      ZMod.val_add_of_lt (by omega)
    have hsum7 : (ctq7 + msb_rem * 65535 + cry6).val =
        ctq7.val + (msb_rem * 65535).val + cry6.val := by
      rw [show (ctq7 + msb_rem * 65535 + cry6) =
            (ctq7 + msb_rem * 65535) + cry6 from rfl,
          ZMod.val_add_of_lt (by rw [hsum7']; omega), hsum7']
    have eq0 : b0.val + cry0.val * 65536 = ctq0.val + r0.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr0; rw [hsum01] at h1 h2; omega
    have eq1 : b1.val + cry1.val * 65536 = ctq1.val + r1.val + cry0.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr1; rw [hsum1] at h1 h2; omega
    have eq2 : b2.val + cry2.val * 65536 = ctq2.val + r2.val + cry1.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr2; rw [hsum2] at h1 h2; omega
    have eq3 : b3.val + cry3.val * 65536 = ctq3.val + r3.val + cry2.val := by
      obtain ⟨h1, h2⟩ := nof_eq_ctqpr3; rw [hsum3] at h1 h2; omega
    have eq4 : (msb_b * 65535).val + cry4.val * 65536 =
        ctq4.val + (msb_rem * 65535).val + cry3.val := by
      have h1 := nof_eq_ctqpr4.1; have h2 := nof_eq_ctqpr4.2
      rw [hsum4] at h1 h2; omega
    have eq5 : (msb_b * 65535).val + cry5.val * 65536 =
        ctq5.val + (msb_rem * 65535).val + cry4.val := by
      have h1 := nof_eq_ctqpr5.1; have h2 := nof_eq_ctqpr5.2
      rw [hsum5] at h1 h2; omega
    have eq6 : (msb_b * 65535).val + cry6.val * 65536 =
        ctq6.val + (msb_rem * 65535).val + cry5.val := by
      have h1 := nof_eq_ctqpr6.1; have h2 := nof_eq_ctqpr6.2
      rw [hsum6] at h1 h2; omega
    have eq7 : (msb_b * 65535).val + cry7.val * 65536 =
        ctq7.val + (msb_rem * 65535).val + cry6.val := by
      have h1 := nof_eq_ctqpr7.1; have h2 := nof_eq_ctqpr7.2
      rw [hsum7] at h1 h2; omega
    have main_eq :
        b0.val + b1.val * 65536 + b2.val * 4294967296 + b3.val * 281474976710656 +
          (msb_b * 65535).val * 18446744073709551616 +
          (msb_b * 65535).val * 1208925819614629174706176 +
          (msb_b * 65535).val * 79228162514264337593543950336 +
          (msb_b * 65535).val * 5192296858534827628530496329220096 +
          cry7.val * 340282366920938463463374607431768211456 =
        ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
          ctq3.val * 281474976710656 + ctq4.val * 18446744073709551616 +
          ctq5.val * 1208925819614629174706176 +
          ctq6.val * 79228162514264337593543950336 +
          ctq7.val * 5192296858534827628530496329220096 +
        (r0.val + r1.val * 65536 + r2.val * 4294967296 +
          r3.val * 281474976710656 +
          (msb_rem * 65535).val * 18446744073709551616 +
          (msb_rem * 65535).val * 1208925819614629174706176 +
          (msb_rem * 65535).val * 79228162514264337593543950336 +
          (msb_rem * 65535).val * 5192296858534827628530496329220096) := by
      omega
    have dctq : DWord.toBitVec128
        (#v[ctq0, ctq1, ctq2, ctq3, ctq4, ctq5, ctq6, ctq7] : DWord (ZMod p)) =
      BitVec.ofNat 128
        (ctq0.val + ctq1.val * 65536 + ctq2.val * 4294967296 +
          ctq3.val * 281474976710656 + ctq4.val * 18446744073709551616 +
          ctq5.val * 1208925819614629174706176 +
          ctq6.val * 79228162514264337593543950336 +
          ctq7.val * 5192296858534827628530496329220096) := by
      simp [DWord.toBitVec128, DWord.toNat]
    have db : DWord.toBitVec128
        (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535, msb_b * 65535,
            msb_b * 65535] : DWord (ZMod p)) =
      BitVec.ofNat 128
        (b0.val + b1.val * 65536 + b2.val * 4294967296 +
          b3.val * 281474976710656 +
          (msb_b * 65535).val * 18446744073709551616 +
          (msb_b * 65535).val * 1208925819614629174706176 +
          (msb_b * 65535).val * 79228162514264337593543950336 +
          (msb_b * 65535).val * 5192296858534827628530496329220096) := by
      simp [DWord.toBitVec128, DWord.toNat]
    have dr : DWord.toBitVec128
        (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535, msb_rem * 65535,
            msb_rem * 65535] : DWord (ZMod p)) =
      BitVec.ofNat 128
        (r0.val + r1.val * 65536 + r2.val * 4294967296 +
          r3.val * 281474976710656 +
          (msb_rem * 65535).val * 18446744073709551616 +
          (msb_rem * 65535).val * 1208925819614629174706176 +
          (msb_rem * 65535).val * 79228162514264337593543950336 +
          (msb_rem * 65535).val * 5192296858534827628530496329220096) := by
      simp [DWord.toBitVec128, DWord.toNat]
    rw [db, dctq, dr]
    simp only [← _root_.BitVec.toNat_inj, DivRem.BitVec.toNat_ofNat_128,
      DivRem.BitVec.toNat_add_128]
    rw [show (340282366920938463463374607431768211456 : ℕ) = divrem_N128 from by
      rw [divrem_N128_eq]; decide] at main_eq
    exact div_rem_close_helper
      b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val
      ctq0.val ctq1.val ctq2.val ctq3.val
      ctq4.val ctq5.val ctq6.val ctq7.val
      (msb_b * 65535).val (msb_rem * 65535).val
      cry7.val main_eq

end divrem_h_prod_helper

section divrem_h_abs_helper

set_option linter.unusedVariables false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
-- 32M heartbeats + 1M recursion: same budget as `div_rem`. `skipKernelTC`
-- localizes the kernel-trip to this helper's olean; the chip's olean references
-- the constant and does not re-walk the body. Splitting the 4-way rcases body
-- into 4 case helpers would eliminate the trip entirely (each case is 22-56
-- lines, well under the kernel WHNF depth limit) — left for future work.
set_option debug.skipKernelTC true in
/-- Extracted `h_abs` for `div_rem` (signed 64-bit DRS branch).

Lifted from `SP1Chips/DivRem/DivRem.lean` so its 4-way rem_neg × c_neg
case-split body (`simp [...] at *` per case, `subst`, `push_cast`,
`sum_zero_abs` applications) is kernel-checked independently of
`div_rem`. Together with `div_rem_h_prod_aux`, this lift is what
allows `div_rem` to compile without `debug.skipKernelTC`.

Inputs are the post-`simp [z_*, div_rem, nof] at *` chip forms:
`rem_neg` / `c_neg` substituted to `msb_rem` / `msb_c`, `is_word = 0`
specialization applied, but disjunctions like `b_rem_neg` /
`rn_ar*` / `eq_cnop*` left intact — the helper does its own rcases /
simp inside each of the 4 cases. -/
lemma div_rem_h_abs_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {c0 c1 c2 c3 r0 r1 r2 r3
     ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
     cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3
     msb_rem msb_c : ZMod p}
    (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
    (is_U64_r : Word.isU64 #v[r0, r1, r2, r3])
    (is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3])
    (is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3])
    (b_rem_neg : msb_rem = 0 ∨ msb_rem = 1)
    (b_c_neg : msb_c = 0 ∨ msb_c = 1)
    (eq_msb_rem : msb_rem = if 32768 ≤ r3 then 1 else 0)
    (eq_msb_c : msb_c = if 32768 ≤ c3 then 1 else 0)
    (rn_ar0 : msb_rem = 1 ∨ ar0 = r0) (rn_ar1 : msb_rem = 1 ∨ ar1 = r1)
    (rn_ar2 : msb_rem = 1 ∨ ar2 = r2) (rn_ar3 : msb_rem = 1 ∨ ar3 = r3)
    (cn_ac0 : msb_c = 1 ∨ ac0 = c0) (cn_ac1 : msb_c = 1 ∨ ac1 = c1)
    (cn_ac2 : msb_c = 1 ∨ ac2 = c2) (cn_ac3 : msb_c = 1 ∨ ac3 = c3)
    (eq_cnop0 : msb_c = 0 ∨ cnop0 = 0) (eq_cnop1 : msb_c = 0 ∨ cnop1 = 0)
    (eq_cnop2 : msb_c = 0 ∨ cnop2 = 0) (eq_cnop3 : msb_c = 0 ∨ cnop3 = 0)
    (eq_rnop0 : msb_rem = 0 ∨ rnop0 = 0) (eq_rnop1 : msb_rem = 0 ∨ rnop1 = 0)
    (eq_rnop2 : msb_rem = 0 ∨ rnop2 = 0) (eq_rnop3 : msb_rem = 0 ∨ rnop3 = 0)
    (c_neg_sum_zero : msb_c = 1 →
        Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧
        Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] =
          Word.toBitVec64 #v[c0, c1, c2, c3] +
          Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
    (rem_neg_sum_zero : msb_rem = 1 →
        Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧
        Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] =
          Word.toBitVec64 #v[r0, r1, r2, r3] +
          Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
    (abs_check : Word.toNat #v[ar0, ar1, ar2, ar3] <
      Word.toNat #v[ac0, ac1, ac2, ac3]) :
    |Word.toInt #v[r0, r1, r2, r3]| <
      |Word.toInt #v[c0, c1, c2, c3]| := by
  have hp17 : 2 ^ 17 < p := Fact.out
  have ⟨hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := Word.lt_cases_of_isU64 is_U64_c
  have ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt⟩ := Word.lt_cases_of_isU64 is_U64_r
  have ⟨hac0_lt, hac1_lt, hac2_lt, hac3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ac
  have ⟨har0_lt, har1_lt, har2_lt, har3_lt⟩ := Word.lt_cases_of_isU64 is_U64_ar
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
    at hc0_lt hc1_lt hc2_lt hc3_lt hr0_lt hr1_lt hr2_lt hr3_lt
       hac0_lt hac1_lt hac2_lt hac3_lt har0_lt har1_lt har2_lt har3_lt
  -- Word.toInt bounds for the abs/sign reasoning (chip derives these
  -- alongside lb_b/lb_q before the `suffices h_qr`; helper needs the c/r ones).
  have lb_c := Word.toInt_lb is_U64_c; have ub_c := Word.toInt_ub is_U64_c
  have lb_r := Word.toInt_lb is_U64_r; have ub_r := Word.toInt_ub is_U64_r
  -- `abs_check` arrives already in bare Prop form (chip simps reduce the chip
  -- param `is_c_0 = 0 → arlt = if … then 1 else 0` down to the comparison via
  -- `ite_eq_one_iff` + `(1 : ZMod p) ≠ 0`).
  rcases b_rem_neg with rem_nneg | rem_neg <;>
    rcases b_c_neg with c_nneg | c_neg
  · -- Case 1: msb_rem = 0, msb_c = 0. Both non-negative; abs_check closes directly.
    simp [rem_nneg, c_nneg] at *
    subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
    have hr3_lt_val : r3.val < 32768 := by
      by_contra h; push Not at h
      apply eq_msb_rem
      change (32768 : ZMod p).val ≤ r3.val
      rw [val_32768_zmod_p]; exact h
    have hc3_lt_val : c3.val < 32768 := by
      by_contra h; push Not at h
      apply eq_msb_c
      change (32768 : ZMod p).val ≤ c3.val
      rw [val_32768_zmod_p]; exact h
    simp only [Word.toInt, Word.isNegative,
               Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    rw [if_neg (by omega), if_neg (by omega)]
    simp [Word.toNat] at abs_check
    simp [Word.toNat]
    push_cast [ZMod.cast_eq_val]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast abs_check
  · -- Case 2: msb_rem = 0, msb_c = 1. c is negative; use c_neg_sum_zero.
    simp [rem_nneg, c_neg] at *
    subst ar0 ar1 ar2 ar3 cnop0 cnop1 cnop2 cnop3
    obtain ⟨_, heqz⟩ := c_neg_sum_zero
    have hr3_lt_val : r3.val < 32768 := by
      by_contra h; push Not at h
      apply eq_msb_rem
      change (32768 : ZMod p).val ≤ r3.val
      rw [val_32768_zmod_p]; exact h
    have hc3_ge_val : c3.val ≥ 32768 := by
      have hh : (32768 : ZMod p).val ≤ c3.val := eq_msb_c
      rwa [val_32768_zmod_p] at hh
    have c_isNeg : Word.isNegative #v[c0, c1, c2, c3] := by
      unfold Word.isNegative
      simp only [Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      omega
    apply sum_zero_abs is_U64_c is_U64_ac c_isNeg at heqz
    obtain ⟨hc_lb, hc_nlb⟩ := heqz
    have hr_nneg : ¬ Word.isNegative #v[r0, r1, r2, r3] := by
      unfold Word.isNegative
      simp only [Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      omega
    have hr_int_nneg : 0 ≤ Word.toInt #v[r0, r1, r2, r3] := by
      unfold Word.toInt
      rw [if_neg hr_nneg]
      positivity
    by_cases is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63
    · rw [is_c_lb]
      rw [show |(-2 ^ 63 : ℤ)| = 2 ^ 63 from by norm_num]
      rw [abs_of_nonneg hr_int_nneg]
      exact Word.toInt_ub is_U64_r
    · apply hc_nlb at is_c_lb
      have hac_nneg : ¬ Word.isNegative #v[ac0, ac1, ac2, ac3] := by
        rw [Word.isNegative_toInt is_U64_ac, is_c_lb]
        exact not_lt.mpr (abs_nonneg _)
      rw [← is_c_lb]
      unfold Word.toInt
      rw [if_neg hr_nneg, if_neg hac_nneg]
      rw [abs_of_nonneg (by positivity)]
      simp [Word.toNat]
      simp [Word.toNat] at abs_check
      push_cast [ZMod.cast_eq_val]
      exact_mod_cast abs_check
  · -- Case 3: msb_rem = 1, msb_c = 0. r is negative; use rem_neg_sum_zero.
    simp [rem_neg, c_nneg] at *
    subst ac0 ac1 ac2 ac3 rnop0 rnop1 rnop2 rnop3
    obtain ⟨_, heqz⟩ := rem_neg_sum_zero
    have hc3_lt_val : c3.val < 32768 := by
      by_contra h; push Not at h
      apply eq_msb_c
      change (32768 : ZMod p).val ≤ c3.val
      rw [val_32768_zmod_p]; exact h
    have hr3_ge_val : r3.val ≥ 32768 := by
      have hh : (32768 : ZMod p).val ≤ r3.val := eq_msb_rem
      rwa [val_32768_zmod_p] at hh
    have r_isNeg : Word.isNegative #v[r0, r1, r2, r3] := by
      unfold Word.isNegative
      simp only [Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      omega
    apply sum_zero_abs is_U64_r is_U64_ar r_isNeg at heqz
    obtain ⟨hr_lb, hr_nlb⟩ := heqz
    have hc_nneg : ¬ Word.isNegative #v[c0, c1, c2, c3] := by
      unfold Word.isNegative
      simp only [Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      omega
    have hc_int_nneg : 0 ≤ Word.toInt #v[c0, c1, c2, c3] := by
      unfold Word.toInt
      rw [if_neg hc_nneg]
      positivity
    by_cases is_r_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63
    · -- |r| = 2^63, |c| < 2^63 contradicts abs_check
      exfalso
      apply hr_lb at is_r_lb
      -- is_r_lb : Word.toInt #v[ar0..3] = -2^63
      have har_toNat : Word.toNat #v[ar0, ar1, ar2, ar3] = 2 ^ 63 := by
        have := Word.isU64_toInt is_U64_ar
        unfold Word.toInt at is_r_lb
        split_ifs at is_r_lb
        · omega
        · omega
      simp [Word.toNat] at abs_check
      rw [show Word.toNat #v[ar0, ar1, ar2, ar3] =
            ar0.val + ar1.val * 65536 + ar2.val * 4294967296 +
              ar3.val * 281474976710656 from by simp [Word.toNat]] at har_toNat
      omega
    · apply hr_nlb at is_r_lb
      have har_nneg : ¬ Word.isNegative #v[ar0, ar1, ar2, ar3] := by
        rw [Word.isNegative_toInt is_U64_ar, is_r_lb]
        exact not_lt.mpr (abs_nonneg _)
      rw [← is_r_lb]
      unfold Word.toInt
      rw [if_neg har_nneg, if_neg hc_nneg]
      rw [abs_of_nonneg (by positivity)]
      simp [Word.toNat]
      simp [Word.toNat] at abs_check
      push_cast [ZMod.cast_eq_val]
      exact_mod_cast abs_check
  · -- Case 4: msb_rem = 1, msb_c = 1. Both negative; two sum_zero_abs applications.
    simp [rem_neg, c_neg] at *
    subst rnop0 rnop1 rnop2 rnop3 cnop0 cnop1 cnop2 cnop3
    obtain ⟨_, heqz_c⟩ := c_neg_sum_zero
    obtain ⟨_, heqz_r⟩ := rem_neg_sum_zero
    have hr3_ge_val : r3.val ≥ 32768 := by
      have hh : (32768 : ZMod p).val ≤ r3.val := eq_msb_rem
      rwa [val_32768_zmod_p] at hh
    have hc3_ge_val : c3.val ≥ 32768 := by
      have hh : (32768 : ZMod p).val ≤ c3.val := eq_msb_c
      rwa [val_32768_zmod_p] at hh
    have r_isNeg : Word.isNegative #v[r0, r1, r2, r3] := by
      unfold Word.isNegative
      simp only [Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      omega
    have c_isNeg : Word.isNegative #v[c0, c1, c2, c3] := by
      unfold Word.isNegative
      simp only [Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      omega
    apply sum_zero_abs is_U64_c is_U64_ac c_isNeg at heqz_c
    apply sum_zero_abs is_U64_r is_U64_ar r_isNeg at heqz_r
    obtain ⟨hc_lb, hc_nlb⟩ := heqz_c
    obtain ⟨hr_lb, hr_nlb⟩ := heqz_r
    by_cases is_r_lb : Word.toInt #v[r0, r1, r2, r3] = -2 ^ 63 <;>
      by_cases is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63
    · -- Sub-case (r = c = -2^63): abs_check gives contradiction
      exfalso
      have ar_lb := hr_lb is_r_lb
      have ac_lb := hc_lb is_c_lb
      have har_toNat : Word.toNat #v[ar0, ar1, ar2, ar3] = 2 ^ 63 := by
        unfold Word.toInt at ar_lb
        split_ifs at ar_lb <;> omega
      have hac_toNat : Word.toNat #v[ac0, ac1, ac2, ac3] = 2 ^ 63 := by
        unfold Word.toInt at ac_lb
        split_ifs at ac_lb <;> omega
      simp [Word.toNat] at abs_check
      rw [show Word.toNat #v[ar0, ar1, ar2, ar3] =
            ar0.val + ar1.val * 65536 + ar2.val * 4294967296 +
              ar3.val * 281474976710656 from by simp [Word.toNat]] at har_toNat
      rw [show Word.toNat #v[ac0, ac1, ac2, ac3] =
            ac0.val + ac1.val * 65536 + ac2.val * 4294967296 +
              ac3.val * 281474976710656 from by simp [Word.toNat]] at hac_toNat
      omega
    · -- Sub-case (r = -2^63, c ≠ -2^63): abs_check gives contradiction
      exfalso
      have ar_lb := hr_lb is_r_lb
      have ac_eq := hc_nlb is_c_lb
      have har_toNat : Word.toNat #v[ar0, ar1, ar2, ar3] = 2 ^ 63 := by
        unfold Word.toInt at ar_lb
        split_ifs at ar_lb <;> omega
      -- ac.toInt = |c.toInt|, and |c.toInt| < 2^63 since c ≠ -2^63
      have hac_nneg : ¬ Word.isNegative #v[ac0, ac1, ac2, ac3] := by
        rw [Word.isNegative_toInt is_U64_ac, ac_eq]
        exact not_lt.mpr (abs_nonneg _)
      have ub_c := Word.toInt_ub is_U64_c
      have lb_c := Word.toInt_lb is_U64_c
      have hac_toNat_lt : Word.toNat #v[ac0, ac1, ac2, ac3] < 2 ^ 63 := by
        have hac_eq_nat : (Word.toNat #v[ac0, ac1, ac2, ac3] : ℤ) =
            |Word.toInt #v[c0, c1, c2, c3]| := by
          unfold Word.toInt at ac_eq
          rw [if_neg hac_nneg] at ac_eq; exact_mod_cast ac_eq
        have : |Word.toInt #v[c0, c1, c2, c3]| < 2 ^ 63 := by
          rw [abs_lt]; exact ⟨by omega, ub_c⟩
        omega
      simp [Word.toNat] at abs_check
      rw [show Word.toNat #v[ar0, ar1, ar2, ar3] =
            ar0.val + ar1.val * 65536 + ar2.val * 4294967296 +
              ar3.val * 281474976710656 from by simp [Word.toNat]] at har_toNat
      rw [show Word.toNat #v[ac0, ac1, ac2, ac3] =
            ac0.val + ac1.val * 65536 + ac2.val * 4294967296 +
              ac3.val * 281474976710656 from by simp [Word.toNat]]
        at hac_toNat_lt
      omega
    · -- Sub-case (r ≠ -2^63, c = -2^63): |r| < 2^63 = |c|
      rw [is_c_lb]
      rw [show |(-2 ^ 63 : ℤ)| = 2 ^ 63 from by norm_num]
      have ub_r := Word.toInt_ub is_U64_r
      have lb_r := Word.toInt_lb is_U64_r
      rw [abs_lt]
      exact ⟨by omega, ub_r⟩
    · -- Sub-case (r ≠ -2^63, c ≠ -2^63): both heqz_*.2 apply
      have ar_eq := hr_nlb is_r_lb
      have ac_eq := hc_nlb is_c_lb
      have har_nneg : ¬ Word.isNegative #v[ar0, ar1, ar2, ar3] := by
        rw [Word.isNegative_toInt is_U64_ar, ar_eq]
        exact not_lt.mpr (abs_nonneg _)
      have hac_nneg : ¬ Word.isNegative #v[ac0, ac1, ac2, ac3] := by
        rw [Word.isNegative_toInt is_U64_ac, ac_eq]
        exact not_lt.mpr (abs_nonneg _)
      rw [← ar_eq, ← ac_eq]
      unfold Word.toInt
      rw [if_neg har_nneg, if_neg hac_nneg]
      simp [Word.toNat]
      simp [Word.toNat] at abs_check
      push_cast [ZMod.cast_eq_val]
      exact_mod_cast abs_check

end divrem_h_abs_helper


end DivRem
