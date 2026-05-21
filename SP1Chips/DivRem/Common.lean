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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    cstrs⟩ := cstrs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    cstrs⟩ := cstrs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    cstrs⟩ := cstrs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    cstrs⟩ := cstrs
  obtain ⟨_, _, _, _, _, b201, b202, b203, b204, b205, b206, b207, b208,
    _, _, _, _, _, _, _, _, _, _, sum_disj, _h_M13⟩ := cstrs
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

end DivRem
