import SP1Foundations
import SP1Chips.Load.LoadByte.Constraints
import SP1Chips.Load.LoadByte.Common
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace Load

namespace LoadByte


variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

def sp1_op_a (Main : Vector (ZMod p) 47) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

def sp1_ob_b (Main : Vector (ZMod p) 47) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

def sp1_imm_c (Main : Vector (ZMod p) 47) : BitVec 12 :=
  BitVec.ofNat 12 Main[21].val

def sp1_load_byte (Main : Vector (ZMod p) 47) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[43] + (65280 : ZMod p) * Main[44],
    (65535 : ZMod p) * Main[44], (65535 : ZMod p) * Main[44], (65535 : ZMod p) * Main[44]])
  return RETIRE_SUCCESS

noncomputable def spec_lb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 1)

noncomputable def spec_lbu (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 1)

set_option maxHeartbeats 1600000 in
-- LoadByte (signed) correct proof — 8-byte fan-out via h38/h39/h40.
theorem correct_lb (Main : Vector (ZMod p) 47)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadByte.constraints Main).allHold)
    (state_cstrs : (LoadByte.constraints Main).initialState s)
    (h_is_lb : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  rw [SP1ConstraintList.allHold,
    Load.LoadByte.allHold_constraints_iff_of_is_lb Main h_is_lb] at h_cstrs
  obtain ⟨h_addr, h38, h39, h40, h28_inv, _h_low_align, h_cpu, h_reader,
    h35_bool, h35_or_zero, h_window, h36_lt, _h37_bounds, h_mem_isU64,
    h46_zero, h13, h29, h30, h31, h32, h_42_43_lt, h43_eq, h44_43_lt, h44_01,
    h44_iff⟩ := h_cstrs
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h256val : (256 : ZMod p).val = 256 := by
    have : (256 : ZMod p).val = 256 % p := by
      rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have h128val : (128 : ZMod p).val = 128 := by
    have : (128 : ZMod p).val = 128 % p := by
      rw [show (128 : ZMod p) = ((128 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have h29_lt_p : (29 : ℕ) < p := by omega
  have h29_val : (29 : ZMod p).val = 29 := ZMod.val_natCast_of_lt h29_lt_p
  simp [ITypeReader.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
    h29_val] at h_reader
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
  -- Bounds on Main[42], Main[43]
  have h42_lt : Main[42].val < 256 := by
    have h42_z : Main[42] < (256 : ZMod p) := h_42_43_lt.2.1
    have : Main[42].val < (256 : ZMod p).val := h42_z; rwa [h256val] at this
  have h42hi_lt : ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val < 256 := by
    have hl : (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ < (256 : ZMod p) := h_42_43_lt.2.2
    have : ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val < (256 : ZMod p).val := hl
    rwa [h256val] at this
  have h43_lt : Main[43].val < 256 := by
    have hl : Main[43] < (256 : ZMod p) := h44_43_lt.2
    have : Main[43].val < (256 : ZMod p).val := hl; rwa [h256val] at this
  have h44_lt : Main[44].val < 256 := by
    have hl : Main[44] < (256 : ZMod p) := h44_43_lt.1
    have : Main[44].val < (256 : ZMod p).val := hl; rwa [h256val] at this
  -- Byte decomposition: lo + hi * 256 = Main[41] (in ZMod p), hence in Nat.
  have h_limb_zmod : Main[42] + ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹) * (2 ^ 8 : ZMod p) =
      Main[41] := by
    have h1 : (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ * (2 ^ 8 : ZMod p) =
              (Main[41] - Main[42]) * (((256 : ZMod p)⁻¹) * (2 ^ 8 : ZMod p)) := by ring
    have h2 : (((256 : ZMod p)⁻¹) * (2 ^ 8 : ZMod p)) = 1 := by
      rw [show (2 ^ 8 : ZMod p) = (256 : ZMod p) by norm_num,
        inv_mul_cancel₀ val_256_ne_zero]
    rw [h1, h2, mul_one]; ring
  have h_decomp : Main[41].val = Main[42].val + ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val * 256 :=
    nat_decomp_of_inv8_decomp _ _ _ h_limb_zmod h42_lt h42hi_lt
  -- Main[41] equals exactly one of Main[29..32]
  have h41_eq : Main[41] = Main[29] ∧ Main[39] = 0 ∧ Main[40] = 0 ∨
                Main[41] = Main[30] ∧ Main[39] = 1 ∧ Main[40] = 0 ∨
                Main[41] = Main[31] ∧ Main[39] = 0 ∧ Main[40] = 1 ∨
                Main[41] = Main[32] ∧ Main[39] = 1 ∧ Main[40] = 1 := by
    rcases h39 with h39 | h39 <;> rcases h40 with h40 | h40
    · left; refine ⟨?_, h39, h40⟩
      rcases h29 with h | h | h
      · rw [h39] at h; exact absurd h zero_ne_one
      · rw [h40] at h; exact absurd h zero_ne_one
      · exact h
    · right; right; left; refine ⟨?_, h39, h40⟩
      rcases h31 with h | h | h
      · rw [h39] at h; exact absurd h zero_ne_one
      · rw [h40] at h; exact absurd h one_ne_zero
      · exact h
    · right; left; refine ⟨?_, h39, h40⟩
      rcases h30 with h | h | h
      · rw [h39] at h; exact absurd h one_ne_zero
      · rw [h40] at h; exact absurd h zero_ne_one
      · exact h
    · right; right; right; refine ⟨?_, h39, h40⟩
      rcases h32 with h | h | h
      · rw [h39] at h; exact absurd h one_ne_zero
      · rw [h40] at h; exact absurd h one_ne_zero
      · exact h
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    exact zero_ne_one h28_inv
  -- Initial-state extraction
  simp [SP1ConstraintList.initialState, LoadByte.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h29_val, h_is_lb, h46_zero, h2728] at state_cstrs
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
  -- Derive `h_in_range` from `h28_inv` (top-two-limb-inv) + addr bounds.
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
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 1 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · rw [h_addr_eq]; omega
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
  -- LB (signed) is_aligned_vaddr is trivially true for width=1
  have h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true := by
    simp only [is_aligned_vaddr, Nat.cast_one, Int.tmod_one, BEq.rfl]
  -- Simplify monadic form
  simp [spec_lb, sp1_load_byte,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6_bv]
  rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[43].val)]
  · -- Main goal: signed sign-extension on Main[43]
    by_cases h_neg : 128 ≤ Main[43].val
    · have h44 : Main[44] = 1 := by
        rw [h44_iff]
        change (128 : ZMod p).val ≤ Main[43].val
        rw [h128val]; exact h_neg
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 Main[43].val) =
          Word.toBitVec64 #v[Main[43] + 65280, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] :=
        signExtend64_ofNat8_of_ge_128 Main[43] h43_lt h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h44, mul_one]
    · push Not at h_neg
      have h_neg_zmod : ¬ (128 : ZMod p) ≤ Main[43] := by
        change ¬ (128 : ZMod p).val ≤ Main[43].val
        rw [h128val]; omega
      have h44 : Main[44] = 0 := by
        rcases h44_01 with h | h
        · exact h
        · exfalso; exact h_neg_zmod (h44_iff.mp h)
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 Main[43].val) =
          Word.toBitVec64 #v[Main[43], (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] :=
        signExtend64_ofNat8_of_lt_128 Main[43] h43_lt h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h44, mul_zero, add_zero]
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_in_range
  -- Memory byte (single byte for LB)
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    -- The 8-case fan-out from h38/h39/h40 selects the right hLk plus a high/low choice via h38.
    -- Cases (h39, h40, h38). For each, find addr offset and the right hLk.
    -- h41 = byte at the address; from h43_eq: Main[43] = h38*high(Main[41]) + (1-h38)*Main[42].
    -- When h38=0: Main[43] = Main[42] (low byte of Main[41]); when h38=1: Main[43] = high byte.
    -- We need to show s.mem[addr]? = some (BitVec.ofNat 8 Main[43].val).
    -- The addr = Main[25]; depending on (h38, h39, h40), it equals base + k where k is the bit-encoded offset.
    rcases h41_eq with ⟨he41, he39, he40⟩ | ⟨he41, he39, he40⟩ | ⟨he41, he39, he40⟩ | ⟨he41, he39, he40⟩
      <;> rcases h38 with h38 | h38
    -- (h39=0, h40=0, h38=0): Main[41] = Main[29], Main[43] = Main[42] = low byte of Main[41]; uses hL0 at base+0.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] by
            rw [h38, he39, he40]; ring]
      -- Main[43] = Main[42] (low byte) since h38=0
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[29].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[29].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL0
    -- (h39=0, h40=0, h38=1): Main[41] = Main[29], Main[43] = high byte; uses hL1 at base+1.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 1 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[29].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[29].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL1
    -- (h39=1, h40=0, h38=0): Main[41] = Main[30], uses hL2 at base+2 with low byte.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 2 by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[30].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[30].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL2
    -- (h39=1, h40=0, h38=1): Main[41] = Main[30], uses hL3 at base+3 with high byte.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 3 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[30].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[30].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL3
    -- (h39=0, h40=1, h38=0): Main[41] = Main[31], uses hL4 at base+4 with low byte.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 4 by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[31].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[31].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL4
    -- (h39=0, h40=1, h38=1): Main[41] = Main[31], uses hL5 at base+5 with high byte.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 5 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[31].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[31].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL5
    -- (h39=1, h40=1, h38=0): Main[41] = Main[32], uses hL6 at base+6 with low byte.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 6 by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[32].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[32].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL6
    -- (h39=1, h40=1, h38=1): Main[41] = Main[32], uses hL7 at base+7 with high byte.
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 7 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[32].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[32].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL7

set_option maxHeartbeats 1600000 in
-- LoadByte (unsigned) correct proof.
theorem correct_lbu (Main : Vector (ZMod p) 47)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadByte.constraints Main).allHold)
    (state_cstrs : (LoadByte.constraints Main).initialState s)
    (h_is_lbu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lbu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_byte Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  rw [SP1ConstraintList.allHold,
    Load.LoadByte.allHold_constraints_iff_of_is_lbu Main h_is_lbu] at h_cstrs
  obtain ⟨h_addr, h38, h39, h40, h28_inv, _h_low_align, h_cpu, h_reader,
    h35_bool, h35_or_zero, h_window, h36_lt, _h37_bounds, h_mem_isU64,
    h45_zero, h13, h29, h30, h31, h32, h_42_43_lt, h43_eq, h44_zero⟩ := h_cstrs
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32val : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65val : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h256val : (256 : ZMod p).val = 256 := by
    have : (256 : ZMod p).val = 256 % p := by
      rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have h32_lt_p : (32 : ℕ) < p := by omega
  have h32_val : (32 : ZMod p).val = 32 := ZMod.val_natCast_of_lt h32_lt_p
  simp [ITypeReader.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
    h32_val] at h_reader
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
  have h42_lt : Main[42].val < 256 := by
    have h42_z : Main[42] < (256 : ZMod p) := h_42_43_lt.2.1
    have : Main[42].val < (256 : ZMod p).val := h42_z; rwa [h256val] at this
  have h42hi_lt : ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val < 256 := by
    have hl : (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ < (256 : ZMod p) := h_42_43_lt.2.2
    have : ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val < (256 : ZMod p).val := hl
    rwa [h256val] at this
  -- For lbu, Main[43] is bounded via case analysis on h38
  have h43_lt : Main[43].val < 256 := by
    rcases h38 with h38 | h38
    · have heq : Main[43] = Main[42] := by
        have := h43_eq; rw [h38] at this; simpa using this
      rw [heq]; exact h42_lt
    · have heq : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        have := h43_eq; rw [h38] at this; simpa using this
      rw [heq]; exact h42hi_lt
  have h_limb_zmod : Main[42] + ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹) * (2 ^ 8 : ZMod p) =
      Main[41] := by
    have h1 : (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ * (2 ^ 8 : ZMod p) =
              (Main[41] - Main[42]) * (((256 : ZMod p)⁻¹) * (2 ^ 8 : ZMod p)) := by ring
    have h2 : (((256 : ZMod p)⁻¹) * (2 ^ 8 : ZMod p)) = 1 := by
      rw [show (2 ^ 8 : ZMod p) = (256 : ZMod p) by norm_num,
        inv_mul_cancel₀ val_256_ne_zero]
    rw [h1, h2, mul_one]; ring
  have h_decomp : Main[41].val = Main[42].val + ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val * 256 :=
    nat_decomp_of_inv8_decomp _ _ _ h_limb_zmod h42_lt h42hi_lt
  have h41_eq : Main[41] = Main[29] ∧ Main[39] = 0 ∧ Main[40] = 0 ∨
                Main[41] = Main[30] ∧ Main[39] = 1 ∧ Main[40] = 0 ∨
                Main[41] = Main[31] ∧ Main[39] = 0 ∧ Main[40] = 1 ∨
                Main[41] = Main[32] ∧ Main[39] = 1 ∧ Main[40] = 1 := by
    rcases h39 with h39 | h39 <;> rcases h40 with h40 | h40
    · left; refine ⟨?_, h39, h40⟩
      rcases h29 with h | h | h
      · rw [h39] at h; exact absurd h zero_ne_one
      · rw [h40] at h; exact absurd h zero_ne_one
      · exact h
    · right; right; left; refine ⟨?_, h39, h40⟩
      rcases h31 with h | h | h
      · rw [h39] at h; exact absurd h zero_ne_one
      · rw [h40] at h; exact absurd h one_ne_zero
      · exact h
    · right; left; refine ⟨?_, h39, h40⟩
      rcases h30 with h | h | h
      · rw [h39] at h; exact absurd h one_ne_zero
      · rw [h40] at h; exact absurd h zero_ne_one
      · exact h
    · right; right; right; refine ⟨?_, h39, h40⟩
      rcases h32 with h | h | h
      · rw [h39] at h; exact absurd h one_ne_zero
      · rw [h40] at h; exact absurd h one_ne_zero
      · exact h
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by
    intro ⟨hm26, hm27⟩
    rw [hm26, hm27, add_zero, mul_zero] at h28_inv
    exact zero_ne_one h28_inv
  simp [SP1ConstraintList.initialState, LoadByte.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h32_val, h_is_lbu, h45_zero, h2728] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have haddr_spec := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  have h25_lt : Main[25].val < 65536 := haddr_isU64 0
  have h26_lt : Main[26].val < 65536 := haddr_isU64 1
  have h27_lt : Main[27].val < 65536 := haddr_isU64 2
  -- Derive `h_in_range` from `h28_inv` (top-two-limb-inv) + addr bounds.
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
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 1 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · rw [h_addr_eq]; omega
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
  have h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true := by
    simp only [is_aligned_vaddr, Nat.cast_one, Int.tmod_one, BEq.rfl]
  simp [spec_lbu, sp1_load_byte,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6_bv]
  rw [run_vmem_read_of_width_1' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[43].val)]
  · -- Zero-extend the byte
    have hext : BitVec.setWidth 64 (BitVec.ofNat 8 Main[43].val) =
        Word.toBitVec64 #v[Main[43], (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] :=
      setWidth64_ofNat8 Main[43] h43_lt
    simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, bitVecToRegidxVal,
      hext, h44_zero, mul_zero, add_zero]
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_in_range
  -- Memory byte (single byte for LBU; same 8-case fan-out as LB)
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h41_eq with ⟨he41, he39, he40⟩ | ⟨he41, he39, he40⟩ | ⟨he41, he39, he40⟩ | ⟨he41, he39, he40⟩
      <;> rcases h38 with h38 | h38
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[29].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[29].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL0
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 1 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[29].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[29].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL1
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 2 by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[30].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[30].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL2
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 3 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[30].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[30].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL3
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 4 by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[31].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[31].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL4
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 5 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[31].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[31].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL5
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 6 by
            rw [h38, he39, he40]; ring]
      have h43_lo : Main[43] = Main[42] := by rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[32].val := congr_arg ZMod.val he41
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 Main[32].val by
            apply bitVec_ofNat8_eq_of_mod
            have : Main[43].val = Main[42].val := congr_arg ZMod.val h43_lo
            omega]
      simpa using hL6
    · rw [show (Main[25] : ZMod p) = Main[25] - 4 * Main[40] - 2 * Main[39] - Main[38] + 7 by
            rw [h38, he39, he40]; ring]
      have h43_hi : Main[43] = (Main[41] - Main[42]) * (256 : ZMod p)⁻¹ := by
        rw [h43_eq, h38]; ring
      have h41eq : Main[41].val = Main[32].val := congr_arg ZMod.val he41
      have h43val : Main[43].val = ((Main[41] - Main[42]) * (256 : ZMod p)⁻¹).val :=
        congr_arg ZMod.val h43_hi
      rw [show (BitVec.ofNat 8 Main[43].val : BitVec 8) = BitVec.ofNat 8 (Main[32].val >>> 8) by
            apply bitVec_ofNat8_eq_of_mod
            rw [h41eq] at h_decomp
            rw [Nat.shiftRight_eq_div_pow]
            rw [h43val]
            omega]
      simpa using hL7

end LoadByte

end Load
