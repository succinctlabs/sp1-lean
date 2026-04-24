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
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])
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
-- Pre-regen proof at commit 750a3e6:SP1Chips/LoadDoubleChip.lean -- correct_ld
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/LoadDoubleChip.lean` for the full pre-regen proof body)
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
  sorry
end LoadDouble

end Load
