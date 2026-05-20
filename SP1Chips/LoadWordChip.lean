import SP1Foundations
import SP1Chips.Load.LoadWord.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadWord

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

def sp1_op_a (Main : Vector (ZMod p) 44) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

def sp1_ob_b (Main : Vector (ZMod p) 44) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

def sp1_imm_c (Main : Vector (ZMod p) 44) : BitVec 12 :=
  BitVec.ofNat 12 Main[21].val

def sp1_load_word (Main : Vector (ZMod p) 44) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[39], Main[40],
    65535 * Main[41], 65535 * Main[41]])
  return RETIRE_SUCCESS

noncomputable def spec_lw (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 4)

noncomputable def spec_lwu (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 4)

private lemma halfword_msb (a b : ZMod p)
    (ha_lt : a.val < 65536)
    (h_msb_01 : b = 0 ∨ b = 1)
    (h_hi : (2 * a - b * 65536 : ZMod p).val < 65536) :
    b = 1 ↔ 32768 ≤ a.val := by
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h2_val : (2 : ZMod p).val = 2 := val_2_zmod_p
  have h65536_val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h2a_val : (2 * a : ZMod p).val = 2 * a.val := by
    rw [ZMod.val_mul, h2_val, Nat.mod_eq_of_lt (by omega)]
  rcases h_msb_01 with hb | hb
  · rw [hb] at h_hi
    simp only [zero_mul, sub_zero] at h_hi
    rw [h2a_val] at h_hi
    refine ⟨fun h => absurd (hb.symm.trans h) zero_ne_one, fun h => by omega⟩
  · rw [hb, one_mul] at h_hi
    refine ⟨fun _ => ?_, fun _ => hb⟩
    by_contra hgt
    push Not at hgt
    have h2a_lt : 2 * a.val < 65536 := by omega
    have h_sub_val := val_sub_cases (2 * a) (65536 : ZMod p)
    rw [h2a_val, h65536_val] at h_sub_val
    have hcase : ¬ (65536 ≤ 2 * a.val) := by omega
    rw [if_neg hcase] at h_sub_val
    rw [h_sub_val] at h_hi
    omega

theorem correct_lw (Main : Vector (ZMod p) 44)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadWord.constraints Main).allHold)
    (state_cstrs : (LoadWord.constraints Main).initialState s)
    (h_is_lw : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lw imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_word Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  rw [SP1ConstraintList.allHold,
    Load.LoadWord.allHold_constraints_iff_of_is_lw Main h_is_lw] at h_cstrs
  obtain ⟨h_addr, h38, h28_inv, _h_low_align, h_u16msb, h_cpu, h_reader,
    h35_bool, h35_or_zero, h_window, h36_lt, _h37_bounds, h_mem_isU64,
    h43_zero, h13, h29, h30, h31, h32⟩ := h_cstrs
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h31_lt_p : (31 : ℕ) < p := by omega
  have h31_val : (31 : ZMod p).val = 31 := ZMod.val_natCast_of_lt h31_lt_p
  simp [ITypeReader.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
    h31_val] at h_reader
  have h6_lt_zmod : Main[6] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h_imm_se : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_reader; simp_all only
  have h15u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- h_reader; simp_all only
  have h21_lt_zmod : Main[21] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h22_lt_zmod : Main[22] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h23_lt_zmod : Main[23] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h24_lt_zmod : Main[24] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt_zmod; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h21u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt_zmod; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt_zmod; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt_zmod; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt_zmod; rwa [h65val] at this
  -- U16MSB facts
  simp [U16MSBOperation.constraints, SP1Constraint.toProp] at h_u16msb
  obtain ⟨h41_01, h40_hi⟩ := h_u16msb
  have h41_01' : Main[41] = 0 ∨ Main[41] = 1 := by
    rcases h41_01 with h | h
    · left; exact h
    · right; rw [sub_eq_zero] at h; exact h
  -- Memory bounds
  have h29_lt : Main[29].val < 65536 := h_mem_isU64 0
  have h30_lt : Main[30].val < 65536 := h_mem_isU64 1
  have h31_lt : Main[31].val < 65536 := h_mem_isU64 2
  have h32_lt : Main[32].val < 65536 := h_mem_isU64 3
  -- Pair-wise: (Main[39], Main[40]) = (Main[29], Main[30]) if h38=0; (Main[31], Main[32]) if h38=1
  have h40_41_eq : (Main[39] = Main[29] ∧ Main[40] = Main[30] ∧ Main[38] = 0) ∨
                   (Main[39] = Main[31] ∧ Main[40] = Main[32] ∧ Main[38] = 1) := by
    rcases h38 with h38 | h38
    · left; refine ⟨?_, ?_, h38⟩
      · rcases h29 with h | h
        · rw [h38] at h; exact absurd h zero_ne_one
        · exact h
      · rcases h30 with h | h
        · rw [h38] at h; exact absurd h zero_ne_one
        · exact h
    · right; refine ⟨?_, ?_, h38⟩
      · rcases h31 with h | h
        · rw [h38] at h; exact absurd h one_ne_zero
        · exact h
      · rcases h32 with h | h
        · rw [h38] at h; exact absurd h one_ne_zero
        · exact h
  have h39_lt : Main[39].val < 65536 := by
    rcases h40_41_eq with ⟨he, _, _⟩ | ⟨he, _, _⟩
    · rw [he]; exact h29_lt
    · rw [he]; exact h31_lt
  have h40_lt : Main[40].val < 65536 := by
    rcases h40_41_eq with ⟨_, he, _⟩ | ⟨_, he, _⟩
    · rw [he]; exact h30_lt
    · rw [he]; exact h32_lt
  have h41_iff : Main[41] = 1 ↔ 32768 ≤ Main[40].val :=
    halfword_msb _ _ h40_lt h41_01' h40_hi
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    exact zero_ne_one h28_inv
  -- Initial-state extraction
  simp [SP1ConstraintList.initialState, LoadWord.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints, U16MSBOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h31_val, h_is_lw, h43_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  -- AddrAdd spec
  have haddr_spec := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  -- Derive `h_in_range` from `h28_inv` (top-two-limb-inv) + addr bounds + alignment.
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv
  have h_addr_eq :
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_toNat haddr_isU64,
      Word.toNat_def]; simp
  have h_offset_eq :
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 4 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 4 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_op_a_0_iff : Main[13] = 1 ↔ Main[6] = 0 := by clear *- h_reader; simp_all only
  have h6_ne_zero : Main[6] ≠ 0 := by
    intro h6_eq
    have : Main[13] = 1 := h_op_a_0_iff.mpr h6_eq
    rw [h13] at this; exact zero_ne_one this
  have h6_val_ne : Main[6].val ≠ 0 := by
    intro hv; apply h6_ne_zero; exact (ZMod.val_eq_zero _).mp hv
  have h6_bv : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
    intro heq
    have htn : (BitVec.ofNat 5 Main[6].val).toNat = (0#5).toNat := by rw [heq]
    simp [BitVec.toNat_ofNat] at htn
    omega
  have h_fits_real : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, h25k_val]
    omega
  -- Simplify monadic form
  simp [spec_lw, sp1_load_word,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6_bv]
  rw [run_vmem_read_of_width_4' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[39].val)
    (BitVec.ofNat 8 (Main[39].val >>> 8))
    (BitVec.ofNat 8 Main[40].val)
    (BitVec.ofNat 8 (Main[40].val >>> 8))]
  · by_cases h_neg : 32768 ≤ Main[40].val
    · have h41 : Main[41] = 1 := h41_iff.mpr h_neg
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 (Main[40].val >>> 8) ++
            BitVec.ofNat 8 Main[40].val ++
            BitVec.ofNat 8 (Main[39].val >>> 8) ++ BitVec.ofNat 8 Main[39].val) =
          Word.toBitVec64 #v[Main[39], Main[40], (65535 : ZMod p), (65535 : ZMod p)] :=
        signExtend64_ofNat32_concat_of_ge_32768 Main[39] Main[40] h39_lt h40_lt h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h41, mul_one]
    · push Not at h_neg
      have h41 : Main[41] = 0 := by
        rcases h41_01' with h | h
        · exact h
        · exfalso; exact absurd (h41_iff.mp h) (by omega)
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 (Main[40].val >>> 8) ++
            BitVec.ofNat 8 Main[40].val ++
            BitVec.ofNat 8 (Main[39].val >>> 8) ++ BitVec.ofNat 8 Main[39].val) =
          Word.toBitVec64 #v[Main[39], Main[40], (0 : ZMod p), (0 : ZMod p)] :=
        signExtend64_ofNat32_concat_of_lt_32768 Main[39] Main[40] h39_lt h40_lt h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h41, mul_zero]
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_in_range
  -- Memory byte 0
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨he40, _, he39⟩ | ⟨he40, _, he39⟩
    · rw [he40, show (Main[25] : ZMod p) = Main[25] - 4 * Main[38] by rw [he39]; ring]
      simpa using hL0
    · rw [he40, show (Main[25] : ZMod p) = Main[25] - 4 * Main[38] + 4 by rw [he39]; ring]
      simpa using hL4
  -- Memory byte 1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 1 (by omega)]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨he40, _, he39⟩ | ⟨he40, _, he39⟩
    · rw [he40, show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 1 by rw [he39]; push_cast; ring]
      simpa using hL1
    · rw [he40, show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 5 by rw [he39]; push_cast; ring]
      simpa using hL5
  -- Memory byte 2
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 2 (by omega)]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨_, he41, he39⟩ | ⟨_, he41, he39⟩
    · rw [he41, show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 2 by rw [he39]; push_cast; ring]
      simpa using hL2
    · rw [he41, show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 6 by rw [he39]; push_cast; ring]
      simpa using hL6
  -- Memory byte 3
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 3 (by omega)]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨_, he41, he39⟩ | ⟨_, he41, he39⟩
    · rw [he41, show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 3 by rw [he39]; push_cast; ring]
      simpa using hL3
    · rw [he41, show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 7 by rw [he39]; push_cast; ring]
      simpa using hL7

set_option maxHeartbeats 1600000 in
-- LoadWord (unsigned) correct proof.
theorem correct_lwu (Main : Vector (ZMod p) 44)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadWord.constraints Main).allHold)
    (state_cstrs : (LoadWord.constraints Main).initialState s)
    (h_is_lwu : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lwu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_word Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  rw [SP1ConstraintList.allHold,
    Load.LoadWord.allHold_constraints_iff_of_is_lwu Main h_is_lwu] at h_cstrs
  obtain ⟨h_addr, h38, h28_inv, _h_low_align, _h_u16msb, h_cpu, h_reader,
    h35_bool, h35_or_zero, h_window, h36_lt, _h37_bounds, h_mem_isU64,
    h42_zero, h13, h29, h30, h31, h32, h41_zero⟩ := h_cstrs
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h34_lt_p : (34 : ℕ) < p := by omega
  have h34_val : (34 : ZMod p).val = 34 := ZMod.val_natCast_of_lt h34_lt_p
  simp [ITypeReader.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
    h34_val] at h_reader
  have h6_lt_zmod : Main[6] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h_imm_se : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_reader; simp_all only
  have h15u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- h_reader; simp_all only
  have h21_lt_zmod : Main[21] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h22_lt_zmod : Main[22] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h23_lt_zmod : Main[23] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h24_lt_zmod : Main[24] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt_zmod; rwa [h32val] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32val] at this
  have h21u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt_zmod; rwa [h65val] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt_zmod; rwa [h65val] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt_zmod; rwa [h65val] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt_zmod; rwa [h65val] at this
  have h29_lt : Main[29].val < 65536 := h_mem_isU64 0
  have h30_lt : Main[30].val < 65536 := h_mem_isU64 1
  have h31_lt : Main[31].val < 65536 := h_mem_isU64 2
  have h32_lt : Main[32].val < 65536 := h_mem_isU64 3
  have h40_41_eq : (Main[39] = Main[29] ∧ Main[40] = Main[30] ∧ Main[38] = 0) ∨
                   (Main[39] = Main[31] ∧ Main[40] = Main[32] ∧ Main[38] = 1) := by
    rcases h38 with h38 | h38
    · left; refine ⟨?_, ?_, h38⟩
      · rcases h29 with h | h
        · rw [h38] at h; exact absurd h zero_ne_one
        · exact h
      · rcases h30 with h | h
        · rw [h38] at h; exact absurd h zero_ne_one
        · exact h
    · right; refine ⟨?_, ?_, h38⟩
      · rcases h31 with h | h
        · rw [h38] at h; exact absurd h one_ne_zero
        · exact h
      · rcases h32 with h | h
        · rw [h38] at h; exact absurd h one_ne_zero
        · exact h
  have h39_lt : Main[39].val < 65536 := by
    rcases h40_41_eq with ⟨he, _, _⟩ | ⟨he, _, _⟩
    · rw [he]; exact h29_lt
    · rw [he]; exact h31_lt
  have h40_lt : Main[40].val < 65536 := by
    rcases h40_41_eq with ⟨_, he, _⟩ | ⟨_, he, _⟩
    · rw [he]; exact h30_lt
    · rw [he]; exact h32_lt
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    exact zero_ne_one h28_inv
  simp [SP1ConstraintList.initialState, LoadWord.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints, U16MSBOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h34_val, h_is_lwu, h42_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have haddr_spec := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  -- Derive `h_in_range` from `h28_inv` (top-two-limb-inv) + addr bounds + alignment.
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h28_inv
  have h_addr_eq :
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_eq, Word.toBitVec64_toNat haddr_isU64,
      Word.toNat_def]; simp
  have h_offset_eq :
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_se]; rfl
  have h_align : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 4 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 4 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  have h_op_a_0_iff : Main[13] = 1 ↔ Main[6] = 0 := by clear *- h_reader; simp_all only
  have h6_ne_zero : Main[6] ≠ 0 := by
    intro h6_eq
    have : Main[13] = 1 := h_op_a_0_iff.mpr h6_eq
    rw [h13] at this; exact zero_ne_one this
  have h6_val_ne : Main[6].val ≠ 0 := by
    intro hv; apply h6_ne_zero; exact (ZMod.val_eq_zero _).mp hv
  have h6_bv : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
    intro heq
    have htn : (BitVec.ofNat 5 Main[6].val).toNat = (0#5).toNat := by rw [heq]
    simp [BitVec.toNat_ofNat] at htn
    omega
  have h_fits_real : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  have haddr_nat : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat #v[Main[25], Main[26], Main[27], (0 : ZMod p)] := by
    have heq := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at heq
    rw [← heq, Word.toBitVec64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by
        rw [Word.toNat_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero]
        have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
        rw [hpow]
        have h26m : Main[26].val * 65536 ≤ 65535 * 65536 := by
          have : Main[26].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        have h27m : Main[27].val * 4294967296 ≤ 65535 * 4294967296 := by
          have : Main[27].val ≤ 65535 := by omega
          exact Nat.mul_le_mul_right _ this
        omega)]
  have haddr_plus : ∀ (k : ℕ), k < 8 →
      Word.toNat #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
      Word.toNat #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, h25k_val]
    omega
  simp [spec_lwu, sp1_load_word,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6_bv]
  rw [run_vmem_read_of_width_4' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[39].val)
    (BitVec.ofNat 8 (Main[39].val >>> 8))
    (BitVec.ofNat 8 Main[40].val)
    (BitVec.ofNat 8 (Main[40].val >>> 8))]
  · have hext : BitVec.setWidth 64 (BitVec.ofNat 8 (Main[40].val >>> 8) ++
          BitVec.ofNat 8 Main[40].val ++
          BitVec.ofNat 8 (Main[39].val >>> 8) ++ BitVec.ofNat 8 Main[39].val) =
        Word.toBitVec64 #v[Main[39], Main[40], (0 : ZMod p), (0 : ZMod p)] :=
      setWidth64_ofNat32_concat Main[39] Main[40] h39_lt h40_lt
    simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, bitVecToRegidxVal,
      hext, h41_zero, mul_zero]
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_in_range
  -- Memory byte 0
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨he40, _, he39⟩ | ⟨he40, _, he39⟩
    · rw [he40, show (Main[25] : ZMod p) = Main[25] - 4 * Main[38] by rw [he39]; ring]
      simpa using hL0
    · rw [he40, show (Main[25] : ZMod p) = Main[25] - 4 * Main[38] + 4 by rw [he39]; ring]
      simpa using hL4
  -- Memory byte 1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 1 (by omega)]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨he40, _, he39⟩ | ⟨he40, _, he39⟩
    · rw [he40, show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 1 by rw [he39]; push_cast; ring]
      simpa using hL1
    · rw [he40, show (Main[25] + ((1 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 5 by rw [he39]; push_cast; ring]
      simpa using hL5
  -- Memory byte 2
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 2 (by omega)]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨_, he41, he39⟩ | ⟨_, he41, he39⟩
    · rw [he41, show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 2 by rw [he39]; push_cast; ring]
      simpa using hL2
    · rw [he41, show (Main[25] + ((2 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 6 by rw [he39]; push_cast; ring]
      simpa using hL6
  -- Memory byte 3
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 3 (by omega)]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_41_eq with ⟨_, he41, he39⟩ | ⟨_, he41, he39⟩
    · rw [he41, show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 3 by rw [he39]; push_cast; ring]
      simpa using hL3
    · rw [he41, show (Main[25] + ((3 : ℕ) : ZMod p) : ZMod p) =
            Main[25] - 4 * Main[38] + 7 by rw [he39]; push_cast; ring]
      simpa using hL7

end LoadWord

end Load
