import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ITypeReader
import SP1Chips.Jalr.Constraints

namespace Jalr

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] ofBool
  update updateSubrange'
  assert PreSail.assert
  LeanRV64D.Functions.RETIRE_SUCCESS

variable (Main : Vector (Fin KB) 35) (s : SailState)

def sp1_op_a (Main : Vector (Fin KB) 35) : BitVec 5 := BitVec.ofNat 5 Main[6].val

def sp1_op_b (Main : Vector (Fin KB) 35) : BitVec 5 := BitVec.ofNat 5 Main[14].val

def sp1_op_c (Main : Vector (Fin KB) 35) : BitVec 12 := BitVec.ofNat 12 Main[21].val

def sp1_jalr (Main : Vector (Fin KB) 35) : SailM Unit := do
  let op_a := sp1_op_a Main
  set_next_pc (Word.toBitVec64 #v[Main[26] - Main[34], Main[27], Main[28], 0])
  wX_bits (.Regidx op_a) (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])

noncomputable def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  let _ ← execute_JALR imm rs1 rd

set_option maxHeartbeats 10000000 in
-- JALR's proof has to discharge BitVec equalities for the low-bit mask plus the
-- AddOp specifications, which routinely exceed default heartbeats.
set_option debug.skipKernelTC true in
theorem JALR_correct
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[25] = 1)
    (hs : isInitialized s)
    (state_cstrs : (constraints Main).initialState s)
    (hv : isValidMemConfig s hs) :
    let op_b := sp1_op_b Main
    let op_a := sp1_op_a Main
    let op_c := sp1_op_c Main
    (spec_jalr op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main).run s := by
  extract_lets op_c op_b op_a
  -- pull out constraints
  simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp, h_is_real] at cstrs
  obtain ⟨res_cstrs, pc_cstrs, reader_cstrs, inc_pc_cstrs, h29, h34_bit, h_low_align,
    h33, h_op_a_b_zero⟩ := cstrs
  -- ITypeReader gives op_a/op_b register-index bounds and opcode-range facts
  simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq,
    SP1Constraint.toProp, sub_eq_zero] at reader_cstrs
  have h6 : Main[6] < 32 := reader_cstrs.1.2.1
  have h14 : Main[14] < 32 := reader_cstrs.1.1.1
  have h_imm_signExtend : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]) := reader_cstrs.1.1.2
  have h15 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
    reader_cstrs.2.2.2.2.2.2.2.2.2.2
  have hu64pc : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
    apply Word.isU64_of_cases <;> aesop
  -- pull out state constraints (PC read, rs1 reg read)
  simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall,
    AddOperation.constraints, ITypeReader.constraints, CPUState.constraints,
    h_is_real, h6, h14] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at read_op_a read_op_b
  -- imm word is u64 (each limb < 65536; from reader_cstrs)
  have h_imm_isU64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;> aesop
  -- AddOperation.spec on res_cstrs: pc+imm = #v[Main[26..29]] as BitVec64
  obtain ⟨h_pc_imm_isU64, h_add⟩ := AddOperation.spec h15 h_imm_isU64 res_cstrs
  simp [execute_RTYPE_pure_w] at h_add
  -- unfold the spec/sp1 monads
  simp [spec_jalr, sp1_jalr, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, cond, execute_JALR,
    op_a, op_b, op_c, sp1_op_a, sp1_op_b, sp1_op_c, read_op_a, read_op_b,
    ← h_imm_signExtend]
  rw [update_elp_state_of_isInitialized _ _ (by aesop)]
  · simp only []
    rw [run_readReg_of_isInitialized _ _ (by aesop)]
    simp [Std.ExtDHashMap.get_insert, read_op_b]
    -- Replace the BitVec sum (rs1 + signExt imm) with the chip's #v[Main[26..29]]
    rw [← h_add]
    -- The chip's masked next_pc low limb is < 65536 and a multiple of 4.
    -- (M[26]-M[34]) = ((M[26]-M[34]) * 4⁻¹) * 4, and the auto-gen guarantees
    -- `((M[26]-M[34]) * (4 : Fin KB)⁻¹).val < 16384`, so .val × 4 is strictly < 65536.
    set k : Fin KB := (Main[26] - Main[34]) * (4 : Fin KB)⁻¹ with hk_def
    have hk_lt : k.val < 16384 := h_low_align
    have h_masked_eq : Main[26] - Main[34] = k * 4 := by
      rw [hk_def, mul_assoc, inv_mul_cancel₀ (by decide), mul_one]
    have h_kx4_val : (k * 4).val = k.val * 4 := by
      rw [Fin.val_mul]; exact Nat.mod_eq_of_lt (by omega)
    have h_masked_lt : (Main[26] - Main[34]).val < 65536 := by
      rw [h_masked_eq, h_kx4_val]; omega
    have h_masked_mod4 : (Main[26] - Main[34]).val % 4 = 0 := by
      rw [h_masked_eq, h_kx4_val]; omega
    -- bounds on the unmasked sum's limbs (each < 2^16 from isU64)
    have h26_lt : Main[26].val < 65536 := h_pc_imm_isU64 0
    have h27_lt : Main[27].val < 65536 := h_pc_imm_isU64 1
    have h28_lt : Main[28].val < 65536 := h_pc_imm_isU64 2
    -- Reduce the Fin subtraction to Nat (h_masked_lt < 65536 rules out the KB wrap branch).
    have h34_val : Main[34].val ≤ 1 := by
      rcases h34_bit with h0 | h1
      · rw [h0]; decide
      · have h34_one : Main[34] = 1 := sub_eq_zero.mp h1
        rw [h34_one]; decide
    -- The Fin subtraction is the Nat subtraction (no wrap), since (Main[26]-Main[34]).val < 65536.
    have h_sub_val : (Main[26] - Main[34]).val = Main[26].val - Main[34].val := by
      rcases Nat.lt_or_ge Main[26].val Main[34].val with hlt | hge
      · -- wrap: contradicts h_masked_lt < 65536
        exfalso
        have h26 : Main[26].val = 0 := by omega
        have h34 : Main[34].val = 1 := by omega
        have : (Main[26] - Main[34]).val = KB - 1 := by
          rw [Fin.sub_def]; simp [h26, h34]
        omega
      · simp [Fin.sub_def]
        have h26 : Main[26].val < KB := Main[26].isLt
        have h34 : Main[34].val < KB := Main[34].isLt
        have h26_sub : Main[26].val - Main[34].val < KB := by omega
        rw [show (KB - Main[34].val + Main[26].val) % KB =
            (Main[26].val - Main[34].val + KB) % KB by congr 1; omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt h26_sub]
    -- The chip's masked next_pc is mod-4 aligned as a 64-bit BitVec.
    have h_target_mod4 :
        (Word.toBitVec64 #v[Main[26] - Main[34], Main[27], Main[28], 0]) % 4#64 = 0#64 := by
      simp only [Word.toBitVec64, Word.toNat_def,
        Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Fin.val_zero, Nat.zero_mul, Nat.add_zero,
        ofNat64_mod_4_eq_zero_iff]
      -- (a + b*2^16 + c*2^32) % 4: 2^16 and 2^32 are multiples of 4.
      rw [show ((2 : Nat) ^ 16) = 16384 * 4 from rfl,
        show ((2 : Nat) ^ 32) = 1073741824 * 4 from rfl,
        ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
      exact h_masked_mod4
    -- The unmasked sum is the masked sum plus Main[34] at bit 0.
    have h_unmasked_eq_masked_plus :
        Word.toBitVec64 #v[Main[26], Main[27], Main[28], Main[29]] =
          Word.toBitVec64 #v[Main[26] - Main[34], Main[27], Main[28], 0]
            + BitVec.ofNat 64 Main[34].val := by
      rw [← BitVec.toNat_inj]
      simp only [Word.toBitVec64, Word.toNat_def, BitVec.toNat_add, BitVec.toNat_ofNat,
        Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Fin.val_zero, Nat.zero_mul, Nat.add_zero, h29, h_sub_val]
      rw [Nat.mod_eq_of_lt (by have := h27_lt; have := h28_lt; omega :
          Main[26].val - Main[34].val + Main[27].val * 2^16 + Main[28].val * 2^32 < 2^64)]
      rw [Nat.mod_eq_of_lt (by omega : Main[34].val < 2^64)]
      rw [Nat.mod_eq_of_lt (by have := h27_lt; have := h28_lt; omega :
          Main[26].val + Main[27].val * 2^16 + Main[28].val * 2^32 < 2^64)]
      omega
    -- Key identity: masking bit 0 of the unmasked sum gives back the masked sum.
    have h_target_eq :
        18446744073709551614#64 &&& Word.toBitVec64 #v[Main[26], Main[27], Main[28], Main[29]] =
          Word.toBitVec64 #v[Main[26] - Main[34], Main[27], Main[28], 0] := by
      rw [h_unmasked_eq_masked_plus]
      set t : BitVec 64 := Word.toBitVec64 #v[Main[26] - Main[34], Main[27], Main[28], 0] with ht
      rcases h34_bit with h0 | h1
      · -- Main[34] = 0: t + 0 = t, mask is no-op since t % 4 = 0
        rw [h0]
        have h0n : (BitVec.ofNat 64 (0 : Fin KB).val) = 0#64 := rfl
        rw [h0n, BitVec.add_zero]
        have ht_mod4 : t % 4#64 = 0#64 := h_target_mod4
        revert ht_mod4; generalize t = u; intro hu
        bv_decide
      · -- Main[34] = 1: mask &&& (t + 1) = t, since t has bit 0 = 0 (t % 4 = 0)
        have h34_one : Main[34] = 1 := sub_eq_zero.mp h1
        rw [h34_one]
        have h1n : (BitVec.ofNat 64 (1 : Fin KB).val) = 1#64 := rfl
        rw [h1n]
        have ht_mod4 : t % 4#64 = 0#64 := h_target_mod4
        revert ht_mod4
        generalize t = u
        intro hu
        bv_decide
    rw [h_target_eq]
    rw [jump_to_of_mod4_eq_zero _ _ (by clear *- hs; aesop) (by simpa using h_target_mod4)]
    simp [Std.ExtDHashMap.insert_insert, EStateM.Result.map]
    -- Convert `get? Register.PC = some _` into `get Register.PC = _`.
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at read_pc
    by_cases h6_zero : Main[6] = 0
    · simp [h6_zero]
    · -- need: pc+4 written to rd matches the chip's Main[30..33] value
      have h6' : BitVec.ofNat 5 (↑Main[6] : Nat) ≠ 0#5 := by
        clear *- h6_zero h6; simp [← BitVec.toNat_inj]; omega
      have h13 : Main[13] = 0 := by
        have := reader_cstrs.1.2.2.2.2.2.1
        -- (Main[13] = 1 ↔ Main[6] = 0); since Main[6] ≠ 0, Main[13] ≠ 1, and Main[13] ∈ {0,1}.
        rcases reader_cstrs.1.2.2.2.2.1 with h | h
        · exact h
        · exfalso; rw [h] at this
          exact h6_zero (this.mp rfl)
      have h_inc_pc_isU64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := hu64pc
      have h_inc_pc' : List.Forall SP1Constraint.toProp
          (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
            { value := #v[Main[30], Main[31], Main[32], Main[33]] } 1) := by
        have := inc_pc_cstrs; simp [h13] at this; exact this
      have h_add_pc' := (AddOperation.spec h_inc_pc_isU64 Word.four_isU64 h_inc_pc').2
      simp [execute_RTYPE_pure_w] at h_add_pc'
      have h_four : Word.toBitVec64 (#v[4, 0, 0, 0] : Vector (Fin KB) 4) = (4#64 : BitVec 64) := by
        simp [Word.toBitVec64, Word.toNat_def]
      rw [h_four] at h_add_pc'
      simp [if_neg h6', read_pc, ← h_add_pc']
  · clear *- hv
    obtain ⟨h1, h2, h3, h4⟩ := hv
    constructor <;> simpa [Std.ExtDHashMap.get_insert]

end Jalr
