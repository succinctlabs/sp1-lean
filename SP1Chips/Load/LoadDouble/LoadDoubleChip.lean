import SP1Foundations
import SP1Chips.Load.LoadDouble.Constraints
import SP1Chips.Load.LoadDouble.Common
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadDouble

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

def sp1_op_a (Main : Vector (ZMod p) 39) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

def sp1_ob_b (Main : Vector (ZMod p) 39) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

def sp1_imm_c (Main : Vector (ZMod p) 39) : BitVec 12 :=
  BitVec.ofNat 12 Main[21].val

def sp1_ld (Main : Vector (ZMod p) 39) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])
  return RETIRE_SUCCESS

noncomputable def spec_ld (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 8)

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
private lemma byteConcat8_toNat_eq_Word_toNat [NeZero p]
    (a b c d : ZMod p) (ha : a.val < 65536) (hb : b.val < 65536)
    (hc : c.val < 65536) (hd : d.val < 65536) :
    (BitVec.ofNat 8 (d.val >>> 8) ++ BitVec.ofNat 8 d.val ++
      BitVec.ofNat 8 (c.val >>> 8) ++ BitVec.ofNat 8 c.val ++
      BitVec.ofNat 8 (b.val >>> 8) ++ BitVec.ofNat 8 b.val ++
      BitVec.ofNat 8 (a.val >>> 8) ++ BitVec.ofNat 8 a.val).toNat =
      Word.toNat #v[a, b, c, d] := by
  have ha_hi : a.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hb_hi : b.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_hi : c.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hd_hi : d.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have ha_decomp : a.val % 256 + (a.val >>> 8) * 256 = a.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hb_decomp : b.val % 256 + (b.val >>> 8) * 256 = b.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_decomp : c.val % 256 + (c.val >>> 8) * 256 = c.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hd_decomp : d.val % 256 + (d.val >>> 8) * 256 = d.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  rw [Word.toNat_def]
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.reducePow,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    show (2 ^ 8 : ℕ) = 256 from rfl]
  have ha_hi_mod : a.val >>> 8 % 256 = a.val >>> 8 := Nat.mod_eq_of_lt ha_hi
  have hb_hi_mod : b.val >>> 8 % 256 = b.val >>> 8 := Nat.mod_eq_of_lt hb_hi
  have hc_hi_mod : c.val >>> 8 % 256 = c.val >>> 8 := Nat.mod_eq_of_lt hc_hi
  have hd_hi_mod : d.val >>> 8 % 256 = d.val >>> 8 := Nat.mod_eq_of_lt hd_hi
  rw [ha_hi_mod, hb_hi_mod, hc_hi_mod, hd_hi_mod]
  rw [show d.val >>> 8 <<< 8 ||| d.val % 256 = d.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  rw [show d.val <<< 8 ||| c.val >>> 8 = d.val * 256 + c.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hc_hi, Nat.shiftLeft_eq]]
  rw [show (d.val * 256 + c.val >>> 8) <<< 8 ||| c.val % 256 =
      (d.val * 256 + c.val >>> 8) * 256 + c.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  rw [show (d.val * 256 + c.val >>> 8) * 256 + c.val % 256 =
      d.val * 65536 + c.val by
    have := hc_decomp; change _ = _; omega]
  rw [show (d.val * 65536 + c.val) <<< 8 ||| b.val >>> 8 =
      (d.val * 65536 + c.val) * 256 + b.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb_hi, Nat.shiftLeft_eq]]
  rw [show ((d.val * 65536 + c.val) * 256 + b.val >>> 8) <<< 8 ||| b.val % 256 =
      ((d.val * 65536 + c.val) * 256 + b.val >>> 8) * 256 + b.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  rw [show ((d.val * 65536 + c.val) * 256 + b.val >>> 8) * 256 + b.val % 256 =
      d.val * 2 ^ 32 + c.val * 65536 + b.val by
    have := hb_decomp; change _ = _; omega]
  rw [show (d.val * 2 ^ 32 + c.val * 65536 + b.val) <<< 8 ||| a.val >>> 8 =
      (d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) ha_hi, Nat.shiftLeft_eq]]
  rw [show ((d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8) <<< 8 ||| a.val % 256 =
      ((d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8) * 256 + a.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := ha_decomp
  change _ = _
  have : 2 ^ 32 = 4294967296 := by norm_num
  have : 2 ^ 48 = 281474976710656 := by norm_num
  omega

theorem correct_ld (Main : Vector (ZMod p) 39)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadDouble.constraints Main).allHold)
    (state_cstrs : (LoadDouble.constraints Main).initialState s)
    (h_is_ld : Main[38] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 8 = true)
    :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_ld imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_ld Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  rw [SP1ConstraintList.allHold,
    allHold_constraints_iff_of_is_ld Main h_is_ld] at h_cstrs
  obtain ⟨h_addr, h28_inv, h_low_align, h_cpu, h_reader,
    h35_bool, h35_or_zero, h_window, h36_lt, _h37_bounds, h_mem_isU64,
    h13⟩ := h_cstrs
  -- Reader constraints
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h35_lt : (35 : ℕ) < p := by omega
  have h35_val : (35 : ZMod p).val = 35 := ZMod.val_natCast_of_lt h35_lt
  simp [ITypeReader.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble,
    h35_val] at h_reader
  -- Extract reader facts (relying on simp_all only's targeted use of h_reader)
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
    have : Main[6].val < (32 : ZMod p).val := h6_lt_zmod; rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32] at this
  have h21u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt_zmod; rwa [h65] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt_zmod; rwa [h65] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt_zmod; rwa [h65] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt_zmod; rwa [h65] at this
  -- Extract initial-state facts
  simp [SP1ConstraintList.initialState, LoadDouble.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h35_val, h_is_ld] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  -- AddrAdd spec from h_addr
  have haddr_spec := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_addr
  obtain ⟨haddr_isU64, haddr_eq⟩ := haddr_spec
  -- Reduce the .value[i] projections in haddr_isU64 / haddr_eq.
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at haddr_isU64 haddr_eq
  -- Bounds on Main[25..27] from isU64 of cols_word
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
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat % 8 = 0 := by
    have h := h_is_aligned
    rw [← h_imm_se, is_aligned_vaddr_iff_mod] at h
    exact h
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    refine range_subset_sp1_pma _ 8 (by omega) ?_ ?_
    · rw [h_addr_eq]; exact h_addr_lo
    · omega
  -- Bounds on Main[29..32] from isU64 of mem result
  have h29_lt : Main[29].val < 65536 := h_mem_isU64 0
  have h30_lt : Main[30].val < 65536 := h_mem_isU64 1
  have h31_lt : Main[31].val < 65536 := h_mem_isU64 2
  have h32_lt : Main[32].val < 65536 := h_mem_isU64 3
  -- The fits-in-mem bound
  have h_fits_real : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h_imm_se] at this
    omega
  -- Convert haddr_eq to Nat equation
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
  -- haddr_plus: shift k into the Main[25] limb
  have haddr_plus :
      ∀ (k : ℕ), k < 8 →
        Word.toNat #v[Main[25], Main[26], Main[27], (0 : ZMod p)] + k =
        Word.toNat #v[Main[25] + (k : ZMod p), Main[26], Main[27], (0 : ZMod p)] := by
    intro k hk
    have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    have h25k_lt : Main[25].val + (k : ZMod p).val < p := by
      rw [hk_val]; omega
    have h25k_val : (Main[25] + (k : ZMod p)).val = Main[25].val + k := by
      rw [ZMod.val_add_of_lt h25k_lt, hk_val]
    simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, h25k_val]
    omega
  -- Main[6] ≠ 0: from h13 = 0 and the iff `Main[13] = 1 ↔ Main[6] = 0` in h_reader
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
  -- Pull `hload` into the (Main[25].val ≥ 32) branch (since chip-stored addr's low limb
  -- is the address, not a register index).
  -- Actually: hload's `if` is `Main[25].val < 32 ∧ Main[26] = 0 ∧ Main[27] = 0` —
  -- need the else branch.
  have h_addr_not_reg : ¬ (Main[25].val < 32 ∧ Main[26] = 0 ∧ Main[27] = 0) := by
    -- From h28_inv : Main[28] * (Main[26] + Main[27]) = 1, m26 + m27 ≠ 0
    intro ⟨_, hm26, hm27⟩
    rw [hm26, hm27, add_zero] at h28_inv
    rw [mul_zero] at h28_inv; exact zero_ne_one h28_inv
  rw [if_neg h_addr_not_reg] at hload
  -- Simplify monadic form on the spec side
  simp [spec_ld, sp1_ld,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6_bv]
  rw [run_vmem_read_of_width_8' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[29].val)
    (BitVec.ofNat 8 (Main[29].val >>> 8))
    (BitVec.ofNat 8 Main[30].val)
    (BitVec.ofNat 8 (Main[30].val >>> 8))
    (BitVec.ofNat 8 Main[31].val)
    (BitVec.ofNat 8 (Main[31].val >>> 8))
    (BitVec.ofNat 8 Main[32].val)
    (BitVec.ofNat 8 (Main[32].val >>> 8))]
  · -- Main goal: result equals SP1 write
    have hconcat := byteConcat8_toNat_eq_Word_toNat Main[29] Main[30] Main[31] Main[32]
      h29_lt h30_lt h31_lt h32_lt
    have heq_toNat : (BitVec.ofNat 8 (Main[32].val >>> 8) ++ BitVec.ofNat 8 Main[32].val ++
          BitVec.ofNat 8 (Main[31].val >>> 8) ++ BitVec.ofNat 8 Main[31].val ++
          BitVec.ofNat 8 (Main[30].val >>> 8) ++ BitVec.ofNat 8 Main[30].val ++
          BitVec.ofNat 8 (Main[29].val >>> 8) ++ BitVec.ofNat 8 Main[29].val).toNat =
        (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]]).toNat := by
      rw [hconcat, Word.toBitVec64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      rw [Word.toNat_def]
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
      rw [hpow]
      have h30m : Main[30].val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right _ (by omega)
      have h31m : Main[31].val * 4294967296 ≤ 65535 * 4294967296 :=
        Nat.mul_le_mul_right _ (by omega)
      have h32m : Main[32].val * 281474976710656 ≤ 65535 * 281474976710656 :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, bitVecToRegidxVal]
    congr 1
    apply BitVec.toNat_inj.mp
    exact heq_toNat
  · -- Side: isInitialized of post-write-pc state
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs, or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_in_range
  -- Memory bytes: 8 sub-goals discharged by rewriting addr + applying hload
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat]
    simpa using hload.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 1 (by omega)]
    simpa using hload.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 2 (by omega)]
    simpa using hload.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 3 (by omega)]
    simpa using hload.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 4 (by omega)]
    simpa using hload.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 5 (by omega)]
    simpa using hload.2.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 6 (by omega)]
    simpa using hload.2.2.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
          Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h_imm_se.symm,
        haddr_nat, haddr_plus 7 (by omega)]
    simpa using hload.2.2.2.2.2.2.2

end LoadDouble

end Load
