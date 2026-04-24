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
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[41], 65535 * Main[42],
    65535 * Main[42], 65535 * Main[42]])
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
-- Pre-regen proof at commit 750a3e6:SP1Chips/LoadHalfChip.lean -- correct_lh
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/LoadHalfChip.lean` for the full pre-regen proof body)
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
  sorry
set_option maxHeartbeats 4000000 in
-- correct_lhu unfolds Load chip + Sail 2-byte memory read
-- Pre-regen proof at commit 750a3e6:SP1Chips/LoadHalfChip.lean -- correct_lhu
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/LoadHalfChip.lean` for the full pre-regen proof body)
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
  sorry
end LoadHalf

end Load
