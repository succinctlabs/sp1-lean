import SP1Foundations
import SP1Chips.Load.LoadHalf.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadHalf

def sp1_op_a (Main : Vector (Fin KB) 44) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 44) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 44) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

def sp1_load_half (Main : Vector (Fin KB) 44) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[40], 65535 * Main[41],
    65535 * Main[41], 65535 * Main[41]])
  return RETIRE_SUCCESS

noncomputable def spec_lh (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := false) (width := 2)

noncomputable def spec_lhu (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 2)

/-- From U16MSB on a halfword `a` (where `a < 65536`), determines MSB: `b = 1 ↔ a ≥ 32768`. -/
private lemma halfword_msb (a b : Fin KB)
    (ha_lt : a.val < 65536)
    (h_msb_01 : b = 0 ∨ b = 1)
    (h_hi : (2 * a - b * 65536 : Fin KB).val < 65536) :
    b = 1 ↔ 32768 ≤ a.val := by
  have hKB : (KB : ℕ) = 2130706433 := rfl
  have h2a : (2 * a : Fin KB).val = 2 * a.val := by
    rw [Fin.val_mul, show ((2 : Fin KB).val = 2) from rfl, Nat.mod_eq_of_lt (by
      show 2 * a.val < 2130706433; omega)]
  have h65536 : ((65536 : Fin KB).val = 65536) := rfl
  rcases h_msb_01 with hb | hb
  · -- b = 0
    rw [hb] at h_hi
    simp only [zero_mul, sub_zero] at h_hi
    rw [h2a] at h_hi
    constructor
    · intro h; rw [hb] at h; exact absurd h (by decide)
    · intro h; omega
  · -- b = 1
    rw [hb] at h_hi
    simp only [one_mul] at h_hi
    by_cases ha_ge : 32768 ≤ a.val
    · -- In Fin KB, 2*a ≥ 65536, so sub = 2*a.val - 65536.
      have hleF : (65536 : Fin KB) ≤ 2 * a := by
        rw [Fin.le_def, h65536, h2a]; omega
      rw [Fin.sub_val_of_le hleF, h2a, h65536] at h_hi
      exact ⟨fun _ => ha_ge, fun _ => hb⟩
    · push Not at ha_ge
      -- a.val < 32768, so 2*a < 65536 in Fin KB. Sub wraps.
      -- Use intCast_val_sub_eq_sub_add_ite to analyze the value.
      exfalso
      have hint := Fin.intCast_val_sub_eq_sub_add_ite (2 * a : Fin KB) (65536 : Fin KB)
      have hne_le : ¬ ((65536 : Fin KB) ≤ 2 * a) := by
        rw [Fin.le_def, h65536, h2a]; omega
      simp only [hne_le, ↓reduceIte] at hint
      -- hint: ((2 * a - 65536).val : ℤ) = (2 * a).val - 65536 + KB
      -- i.e. (2 * a - 65536).val = 2 * a.val + KB - 65536 (since 2*a.val < 65536 < KB).
      rw [h2a, h65536] at hint
      -- Convert to Nat
      have hval : ((2 * a - 65536 : Fin KB).val : ℤ) = (2 * a.val : ℤ) - 65536 + KB := hint
      have : ((2 * a - 65536 : Fin KB).val : ℤ) < 65536 := by exact_mod_cast h_hi
      omega

set_option maxHeartbeats 4000000 in
-- correct_lh unfolds Load chip + Sail 2-byte memory read
theorem correct_lh (Main : Vector (Fin KB) 44)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadHalf.constraints Main).allHold)
    (state_cstrs : (LoadHalf.constraints Main).initialState s)
    (h_is_lh : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 2 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lh imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_half Main).run s := by
  extract_lets op_a op_b imm_c
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config
  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_lh Main h_is_lh] at h_cstrs
  obtain ⟨h_addr, h38, h39, h28, hb,
    h_u16msb, h_cpu, h_reader, h35, h33', hds, h36, h37, hmem, hmem',
    h43_zero, h13, h29, h30, h31, h32⟩ := h_cstrs
  -- Extract reader facts
  simp [ITypeReader.constraints] at h_reader
  simp [SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by clear *- h28; aesop
  -- Extract U16MSB facts: Main[41] ∈ {0,1} and (2*Main[40] - Main[41]*65536).val < 65536
  simp [U16MSBOperation.constraints, SP1Constraint.toProp, Opcode.ofNat, Nat.ble] at h_u16msb
  obtain ⟨h42_01, h40_hi⟩ := h_u16msb
  have h42_01' : Main[41] = 0 ∨ Main[41] = 1 := by
    rcases h42_01 with h | h
    · left; exact h
    · right; rw [sub_eq_zero] at h; exact h
  -- Memory send tells us Main[30..33] < 65536 (via Word.isU64).
  have hmem_isU64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by
    have := hmem; simp [SP1Constraint.toProp] at this; exact this
  have h29_lt : Main[29].val < 65536 := by have := hmem_isU64 ⟨0, by decide⟩; simpa using this
  have h30_lt : Main[30].val < 65536 := by have := hmem_isU64 ⟨1, by decide⟩; simpa using this
  have h31_lt : Main[31].val < 65536 := by have := hmem_isU64 ⟨2, by decide⟩; simpa using this
  have h32_lt : Main[32].val < 65536 := by have := hmem_isU64 ⟨3, by decide⟩; simpa using this
  -- Main[40] equals exactly one of Main[30..33] based on h38/h39.
  -- Combining this with h29..h32_lt gives Main[40].val < 65536.
  have h40_eq : Main[40] = Main[29] ∧ Main[38] = 0 ∧ Main[39] = 0 ∨
                Main[40] = Main[30] ∧ Main[38] = 1 ∧ Main[39] = 0 ∨
                Main[40] = Main[31] ∧ Main[38] = 0 ∧ Main[39] = 1 ∨
                Main[40] = Main[32] ∧ Main[38] = 1 ∧ Main[39] = 1 := by
    rcases h38 with h38 | h38 <;> rcases h39 with h39 | h39
    · left; refine ⟨?_, h38, h39⟩
      rcases h29 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
    · right; right; left; refine ⟨?_, h38, h39⟩
      rcases h31 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
    · right; left; refine ⟨?_, h38, h39⟩
      rcases h30 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
    · right; right; right; refine ⟨?_, h38, h39⟩
      rcases h32 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
  have h40_lt : Main[40].val < 65536 := by
    rcases h40_eq with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; exact h29_lt
    · rw [he]; exact h30_lt
    · rw [he]; exact h31_lt
    · rw [he]; exact h32_lt
  -- Derive MSB characterization using the helper lemma
  have h41_iff : Main[41] = 1 ↔ 32768 ≤ Main[40].val := halfword_msb _ _ h40_lt h42_01' h40_hi
  -- Extract initial-state facts
  simp [LoadHalf.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    U16MSBOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h2728, h43_zero, h_is_lh] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega
  -- The immediate fits into a 12-bit word
  have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> {clear *- rest; simp_all}
  have h21' : BitVec.signExtend 64 (BitVec.ofNat 12 (Main[21] : ℕ)) =
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] := h21.symm
  -- From AddrAddOperation: (reg_val + offset) = Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0]
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ (by
    clear *- rest; simp_all only) hu6421 _ h_addr
  obtain ⟨_, haddr_eq⟩ := haddr_add
  simp only [Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at haddr_eq
  have h_fits_real : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h21] at this
    omega
  have haddr_nat : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat #v[Main[25], Main[26], Main[27], 0] := by
    have := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at this
    rw [← this, Word.toBitVec64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
  have h25_isLt : Main[25].val < KB := Main[25].isLt
  have h26_isLt : Main[26].val < KB := Main[26].isLt
  have h27_isLt : Main[27].val < KB := Main[27].isLt
  have h_KB : KB = 2130706433 := rfl
  -- Simplify monadic form on the spec side
  simp [spec_lh, sp1_load_half,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h6]
  rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14])
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[40].val)
    (BitVec.ofNat 8 (Main[40].val >>> 8))]
  -- Main goal: reconstruct the halfword and sign/zero-extend appropriately.
  · by_cases h_neg : 32768 ≤ Main[40].val
    · -- Main[41] = 1
      have h41 : Main[41] = 1 := h41_iff.mpr h_neg
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 (Main[40].val >>> 8) ++
            BitVec.ofNat 8 Main[40].val) =
          Word.toBitVec64 #v[Main[40], 65535, 65535, 65535] :=
        signExtend64_ofNat16_concat_of_ge_32768 Main[40] h40_lt h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h41, mul_one, h_read_pc]
    · push Not at h_neg
      have h41 : Main[41] = 0 := by
        rcases h42_01' with h | h
        · exact h
        · exfalso; exact absurd (h41_iff.mp h) (by omega)
      have hext : BitVec.signExtend 64 (BitVec.ofNat 8 (Main[40].val >>> 8) ++
            BitVec.ofNat 8 Main[40].val) =
          Word.toBitVec64 #v[Main[40], 0, 0, 0] :=
        signExtend64_ofNat16_concat_of_lt_32768 Main[40] h40_lt h_neg
      simp [extend_value, sign_extend, Sail.BitVec.signExtend, bitVecToRegidxVal,
        hext, h41, mul_zero, h_read_pc]
  -- Side condition: isInitialized of post-write-pc state
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
      or_true, implies_true]
  -- Side condition: get_reg? of op_b in post-write-pc state
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  -- Side condition: is_aligned_vaddr
  · exact h_is_aligned
  -- Side condition: isValidMemConfig
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  -- Side condition: fits in 2 ^ 64
  · exact h_fits_in_mem
  -- Side condition: below clint
  · exact h_below_clint
  -- Memory at addr contains low byte
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_eq with ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] by rw [he39, he40]; ring]
      exact hL0
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] + 2 by rw [he39, he40]; ring]
      exact hL2
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] + 4 by rw [he39, he40]; ring]
      exact hL4
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] + 6 by rw [he39, he40]; ring]
      exact hL6
  -- Memory at addr+1 contains high byte
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    have h25_small : Main[25].val + 7 < 2130706433 := by
      have hbc := h_below_clint
      simp only [sp1_imm_c, h21'] at hbc
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real, haddr_nat] at hbc
      rw [Word.toNat_def] at hbc
      simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero] at hbc
      omega
    have haddr_plus_1 : Word.toNat #v[Main[25], Main[26], Main[27], 0] + 1 =
        Word.toNat #v[Main[25] + (1 : Fin KB), Main[26], Main[27], 0] := by
      have hk : ((1 : Fin KB).val = 1) := rfl
      have h26k : (Main[25] + (1 : Fin KB)).val = Main[25].val + 1 := by
        rw [Fin.val_add, hk, Nat.mod_eq_of_lt (by omega)]
      simp only [Word.toNat_def, Fin.isValue, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, h26k]
      omega
    rw [haddr_plus_1]
    rcases h40_eq with ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 1 by
            rw [he39, he40]; ring]
      exact hL1
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 3 by
            rw [he39, he40]; ring]
      exact hL3
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 5 by
            rw [he39, he40]; ring]
      exact hL5
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 7 by
            rw [he39, he40]; ring]
      exact hL7

set_option maxHeartbeats 4000000 in
-- correct_lhu unfolds Load chip + Sail 2-byte memory read
theorem correct_lhu (Main : Vector (Fin KB) 44)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (LoadHalf.constraints Main).allHold)
    (state_cstrs : (LoadHalf.constraints Main).initialState s)
    (h_is_lhu : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 2 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_lhu imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_load_half Main).run s := by
  extract_lets op_a op_b imm_c
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config
  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_lhu Main h_is_lhu] at h_cstrs
  obtain ⟨h_addr, h38, h39, h28, hb,
    h_u16msb, h_cpu, h_reader, h35, h33', hds, h36, h37, hmem, hmem',
    h42_zero, h13, h29, h30, h31, h32, h41_zero⟩ := h_cstrs
  -- Extract reader facts
  simp [ITypeReader.constraints] at h_reader
  simp [SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by clear *- h28; aesop
  -- Memory send tells us Main[30..33] < 65536.
  have hmem_isU64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by
    have := hmem; simp [SP1Constraint.toProp] at this; exact this
  have h29_lt : Main[29].val < 65536 := by have := hmem_isU64 ⟨0, by decide⟩; simpa using this
  have h30_lt : Main[30].val < 65536 := by have := hmem_isU64 ⟨1, by decide⟩; simpa using this
  have h31_lt : Main[31].val < 65536 := by have := hmem_isU64 ⟨2, by decide⟩; simpa using this
  have h32_lt : Main[32].val < 65536 := by have := hmem_isU64 ⟨3, by decide⟩; simpa using this
  have h40_eq : Main[40] = Main[29] ∧ Main[38] = 0 ∧ Main[39] = 0 ∨
                Main[40] = Main[30] ∧ Main[38] = 1 ∧ Main[39] = 0 ∨
                Main[40] = Main[31] ∧ Main[38] = 0 ∧ Main[39] = 1 ∨
                Main[40] = Main[32] ∧ Main[38] = 1 ∧ Main[39] = 1 := by
    rcases h38 with h38 | h38 <;> rcases h39 with h39 | h39
    · left; refine ⟨?_, h38, h39⟩
      rcases h29 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
    · right; right; left; refine ⟨?_, h38, h39⟩
      rcases h31 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
    · right; left; refine ⟨?_, h38, h39⟩
      rcases h30 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
    · right; right; right; refine ⟨?_, h38, h39⟩
      rcases h32 with h | h | h
      · rw [h38] at h; exact absurd h (by decide)
      · rw [h39] at h; exact absurd h (by decide)
      · exact h
  have h40_lt : Main[40].val < 65536 := by
    rcases h40_eq with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; exact h29_lt
    · rw [he]; exact h30_lt
    · rw [he]; exact h31_lt
    · rw [he]; exact h32_lt
  -- Extract initial-state facts (use Main[43] = 1 guard)
  simp [LoadHalf.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    U16MSBOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h2728, h42_zero, h_is_lhu] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega
  have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> {clear *- rest; simp_all}
  have h21' : BitVec.signExtend 64 (BitVec.ofNat 12 (Main[21] : ℕ)) =
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] := h21.symm
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ (by
    clear *- rest; simp_all only) hu6421 _ h_addr
  obtain ⟨_, haddr_eq⟩ := haddr_add
  simp only [Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at haddr_eq
  have h_fits_real : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat < 2 ^ 64 := by
    have := h_fits_in_mem
    simp only [sp1_imm_c] at this
    rw [← h21] at this
    omega
  have haddr_nat : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
          (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Word.toNat #v[Main[25], Main[26], Main[27], 0] := by
    have := congr_arg BitVec.toNat haddr_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real] at this
    rw [← this, Word.toBitVec64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Word.toNat]; omega)]
  have h25_isLt : Main[25].val < KB := Main[25].isLt
  have h26_isLt : Main[26].val < KB := Main[26].isLt
  have h27_isLt : Main[27].val < KB := Main[27].isLt
  have h_KB : KB = 2130706433 := rfl
  simp [spec_lhu, sp1_load_half,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6]
  rw [run_vmem_read_of_width_2' (BitVec.ofNat 5 Main[14])
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val))
    (BitVec.ofNat 8 Main[40].val)
    (BitVec.ofNat 8 (Main[40].val >>> 8))]
  -- Main goal: zero-extend
  · have hext : BitVec.setWidth 64 (BitVec.ofNat 8 (Main[40].val >>> 8) ++
          BitVec.ofNat 8 Main[40].val) =
        Word.toBitVec64 #v[Main[40], 0, 0, 0] :=
      setWidth64_ofNat16_concat Main[40] h40_lt
    simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, bitVecToRegidxVal,
      hext, h41_zero, mul_zero]
  -- Side conditions
  · simp only [isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
      or_true, implies_true]
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  · exact h_is_aligned
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · exact h_fits_in_mem
  · exact h_below_clint
  -- Memory byte 0
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    rcases h40_eq with ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] by rw [he39, he40]; ring]
      exact hL0
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] + 2 by rw [he39, he40]; ring]
      exact hL2
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] + 4 by rw [he39, he40]; ring]
      exact hL4
    · rw [he]
      rw [show Main[25] = Main[25] - 4 * Main[39] - 2 * Main[38] + 6 by rw [he39, he40]; ring]
      exact hL6
  -- Memory byte 1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat]
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hload
    have h25_small : Main[25].val + 7 < 2130706433 := by
      have hbc := h_below_clint
      simp only [sp1_imm_c, h21'] at hbc
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real, haddr_nat] at hbc
      rw [Word.toNat_def] at hbc
      simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero] at hbc
      omega
    have haddr_plus_1 : Word.toNat #v[Main[25], Main[26], Main[27], 0] + 1 =
        Word.toNat #v[Main[25] + (1 : Fin KB), Main[26], Main[27], 0] := by
      have hk : ((1 : Fin KB).val = 1) := rfl
      have h26k : (Main[25] + (1 : Fin KB)).val = Main[25].val + 1 := by
        rw [Fin.val_add, hk, Nat.mod_eq_of_lt (by omega)]
      simp only [Word.toNat_def, Fin.isValue, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, h26k]
      omega
    rw [haddr_plus_1]
    rcases h40_eq with ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩ | ⟨he, he39, he40⟩
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 1 by
            rw [he39, he40]; ring]
      exact hL1
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 3 by
            rw [he39, he40]; ring]
      exact hL3
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 5 by
            rw [he39, he40]; ring]
      exact hL5
    · rw [he]
      rw [show Main[25] + (1 : Fin KB) = Main[25] - 4 * Main[39] - 2 * Main[38] + 7 by
            rw [he39, he40]; ring]
      exact hL7

end LoadHalf

end Load
