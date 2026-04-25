import SP1Foundations
import SP1Chips.Load.LoadDouble.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadDouble

def sp1_op_a (Main : Vector (Fin KB) 39) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 39) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 39) : BitVec 12 :=
  BitVec.ofNat 12 Main[21]

def sp1_ld (Main : Vector (Fin KB) 39) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]])
  return RETIRE_SUCCESS

noncomputable def spec_ld (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 8)

/-- toNat of the 8-byte concatenation equals `Word.toNat` when each halfword fits in 16 bits.
    Left-associative concat matches `run_vmem_read_of_width_8'` output. -/
private lemma byteConcat8_toNat_eq_Word_toNat
    (a b c d : Fin KB) (ha : a.val < 65536) (hb : b.val < 65536)
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
  -- Convert each `x <<< 8 ||| y` with `y < 256` to `x * 2 ^ 8 + y` (using shiftLeft_add_eq_or_of_lt).
  -- We do this step-by-step from innermost to outermost since they nest left-assoc.
  -- First: (d >>> 8) <<< 8 ||| (d % 256) — this is just d.
  rw [show d.val >>> 8 <<< 8 ||| d.val % 256 = d.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  -- Then: d <<< 8 ||| (c >>> 8). Here c >>> 8 < 256.
  rw [show d.val <<< 8 ||| c.val >>> 8 = d.val * 256 + c.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hc_hi, Nat.shiftLeft_eq]]
  -- Then: (d*256 + c>>>8) <<< 8 ||| (c % 256) = (d*256 + c>>>8)*256 + c%256
  rw [show (d.val * 256 + c.val >>> 8) <<< 8 ||| c.val % 256 =
      (d.val * 256 + c.val >>> 8) * 256 + c.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  rw [show (d.val * 256 + c.val >>> 8) * 256 + c.val % 256 =
      d.val * 65536 + c.val by
    have := hc_decomp; change _ = _; omega]
  -- Next: (d*65536 + c) <<< 8 ||| b>>>8 = (d*65536 + c) * 256 + b>>>8
  rw [show (d.val * 65536 + c.val) <<< 8 ||| b.val >>> 8 =
      (d.val * 65536 + c.val) * 256 + b.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb_hi, Nat.shiftLeft_eq]]
  -- Next: ((d*65536 + c)*256 + b>>>8) <<< 8 ||| b%256
  rw [show ((d.val * 65536 + c.val) * 256 + b.val >>> 8) <<< 8 ||| b.val % 256 =
      ((d.val * 65536 + c.val) * 256 + b.val >>> 8) * 256 + b.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  rw [show ((d.val * 65536 + c.val) * 256 + b.val >>> 8) * 256 + b.val % 256 =
      d.val * 2 ^ 32 + c.val * 65536 + b.val by
    have := hb_decomp; change _ = _; omega]
  -- Next: (d*2 ^ 32 + c*65536 + b) <<< 8 ||| a>>>8
  rw [show (d.val * 2 ^ 32 + c.val * 65536 + b.val) <<< 8 ||| a.val >>> 8 =
      (d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) ha_hi, Nat.shiftLeft_eq]]
  -- Final: ((d*2 ^ 32 + c*65536 + b)*256 + a>>>8) <<< 8 ||| a%256
  rw [show ((d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8) <<< 8 ||| a.val % 256 =
      ((d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8) * 256 + a.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := ha_decomp
  change _ = _
  have : 2 ^ 32 = 4294967296 := by norm_num
  have : 2 ^ 48 = 281474976710656 := by norm_num
  omega

set_option maxHeartbeats 2000000 in
-- correct_ld unfolds Load chip + Sail 8-byte memory read
theorem correct_ld (Main : Vector (Fin KB) 39)
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
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 8 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_ld imm_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_ld Main).run s := by
  extract_lets op_a op_b imm_c
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config
  rw [SP1ConstraintList.allHold, allHold_constraints_iff_of_is_ld Main h_is_ld] at h_cstrs
  obtain ⟨h_addr, h29, hb,
    h_cpu, h_reader, h36, h34', hds, h37, h38, hmem, hmem',
    h13⟩ := h_cstrs
  -- Extract reader facts
  simp [ITypeReader.constraints] at h_reader
  -- have h25 : Main[25] = 1 := by have := h_reader.2.2.1.resolve_right (by decide); omega
  simp [SP1Constraint.toProp, Opcode.ofNat, Nat.ble, and_assoc] at h_reader
  obtain ⟨h14, h21, h6, rest⟩ := h_reader
  simp [Fin.lt_def] at rest
  have h2728 : ¬ (Main[26] = 0 ∧ Main[27] = 0) := by clear *- h29; aesop
  -- Extract initial-state facts
  simp [LoadDouble.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReader.constraints, BitVec.ofNatLT_eq_ofNat,
    Opcode.ofNat, Nat.ble, h6, h14, h2728, h_is_ld] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, hload⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h6 : BitVec.ofNat 5 Main[6] ≠ 0#5 := by simp [← BitVec.toNat_inj]; omega
  -- The immediate fits into a 12-bit word
  have hu6421 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> {clear *- rest; simp_all}
  have h21' : BitVec.signExtend 64 (BitVec.ofNat 12 (Main[21] : ℕ)) =
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] := h21.symm
  -- From AddrAddOperation: (reg_val + offset) = Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0]
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ (by
    clear *- rest; simp_all only) hu6421 _ h_addr
  obtain ⟨_, haddr_eq⟩ := haddr_add
  simp only [AddrAddOperation.spec, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at haddr_eq
  -- Get the bounds on Main[30..33] from the send memory interaction (Word.isU64).
  have hmem_isU64 : Word.isU64 #v[Main[29], Main[30], Main[31], Main[32]] := by
    have := hmem; simp [SP1Constraint.toProp] at this; exact this
  have h30_lt : Main[29].val < 65536 := by have := hmem_isU64 ⟨0, by decide⟩; simpa using this
  have h31_lt : Main[30].val < 65536 := by have := hmem_isU64 ⟨1, by decide⟩; simpa using this
  have h32_lt : Main[31].val < 65536 := by have := hmem_isU64 ⟨2, by decide⟩; simpa using this
  have h33_lt : Main[32].val < 65536 := by have := hmem_isU64 ⟨3, by decide⟩; simpa using this
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
  -- Get bounds on Main[26], Main[27], Main[28] for address nat arith.
  have h26_isLt : Main[26].val < KB := Main[26].isLt
  have h27_isLt : Main[27].val < KB := Main[27].isLt
  have h28_isLt : Main[28].val < KB := Main[28].isLt
  have h30_isLt : Main[30].val < KB := Main[30].isLt
  have h31_isLt : Main[31].val < KB := Main[31].isLt
  have h32_isLt : Main[32].val < KB := Main[32].isLt
  have h33_isLt : Main[33].val < KB := Main[33].isLt
  have h_KB : KB = 2130706433 := rfl
  -- Derive a tight bound on Main[26] from h_below_clint via haddr_nat (needed for addr arithmetic).
  have h26_small : Main[25].val + 7 < 2130706433 := by
    have hbc := h_below_clint
    simp only [sp1_imm_c, h21'] at hbc
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h_fits_real, haddr_nat] at hbc
    rw [Word.toNat_def] at hbc
    simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, mul_zero, add_zero] at hbc
    omega
  -- Convert between `Word.toNat #v[m26, m27, m28, 0] + k` and `Word.toNat #v[m26+k, m27, m28, 0]`.
  have haddr_plus :
      ∀ (k : ℕ), k < 8 →
        Word.toNat #v[Main[25], Main[26], Main[27], 0] + k =
        Word.toNat #v[Main[25] + (k : Fin KB), Main[26], Main[27], 0] := by
    intro k hk
    have hkcast : (k : Fin KB).val = k := Fin.val_cast_of_lt (by omega)
    have h26k : (Main[25] + (k : Fin KB)).val = Main[25].val + k := by
      rw [Fin.val_add, hkcast, Nat.mod_eq_of_lt (by omega)]
    simp only [Word.toNat_def, Fin.isValue, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, mul_zero, add_zero, h26k]
    omega
  -- Simplify monadic form on the spec side
  simp [spec_ld, sp1_ld,
    sp1_op_a, sp1_ob_b, sp1_imm_c,
    op_a, op_b, imm_c, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, h_read_pc, h6]
  rw [run_vmem_read_of_width_8' (BitVec.ofNat 5 Main[14])
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
  -- Main goal: the result equals the SP1 write
  · have hconcat := byteConcat8_toNat_eq_Word_toNat Main[29] Main[30] Main[31] Main[32]
      h30_lt h31_lt h32_lt h33_lt
    -- Show the raw concat toNat = Word toBitVec64 toNat.
    have heq_toNat : (BitVec.ofNat 8 (Main[32].val >>> 8) ++ BitVec.ofNat 8 Main[32].val ++
          BitVec.ofNat 8 (Main[31].val >>> 8) ++ BitVec.ofNat 8 Main[31].val ++
          BitVec.ofNat 8 (Main[30].val >>> 8) ++ BitVec.ofNat 8 Main[30].val ++
          BitVec.ofNat 8 (Main[29].val >>> 8) ++ BitVec.ofNat 8 Main[29].val).toNat =
        (Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]]).toNat := by
      rw [hconcat, Word.toBitVec64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      rw [Word.toNat_def]
      simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      omega
    simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, bitVecToRegidxVal]
    -- Final goal: ⋯ ▸ concat = ⋯ ▸ Word.toBitVec64. Both are cast to BitVec 64 (same width, identity cast).
    congr 1
    apply BitVec.toNat_inj.mp
    exact heq_toNat
  -- Side condition: isInitialized of post-write-pc state
  · simp only [Fin.isValue, isInitialized_iff, Std.ExtDHashMap.mem_insert, beq_iff_eq, hs,
      or_true, implies_true]
  -- Side condition: get_reg? of op_b in post-write-pc state
  · simpa [BitVec.ofNatLT_eq_ofNat] using h14_op_a
  -- Side condition: is_aligned_vaddr: given as h_is_aligned
  · exact h_is_aligned
  -- Side condition: isValidMemConfig for post-write-pc state
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  -- Side condition: fits in 2 ^ 64
  · exact h_fits_in_mem
  -- Side condition: below clint
  · exact h_below_clint
  -- Memory bytes: close each of the 8 hmem_k goals by rewriting addr and applying the matching hload entry.
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat]
    exact hload.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 1 (by omega)]
    exact hload.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 2 (by omega)]
    exact hload.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 3 (by omega)]
    exact hload.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 4 (by omega)]
    exact hload.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 5 (by omega)]
    exact hload.2.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 6 (by omega)]
    exact hload.2.2.2.2.2.2.1
  · rw [show BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) =
            Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] from h21.symm,
        haddr_nat, haddr_plus 7 (by omega)]
    exact hload.2.2.2.2.2.2.2

end LoadDouble

end Load
