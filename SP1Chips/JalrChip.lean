import SP1Operations
import LeanRV64IM.RiscvInstsEnd

import SP1Chips.Jalr.Constraints

instance : Lean.Grind.NoNatZeroDivisors (Fin 2013265921) where
  no_nat_zero_divisors := sorry

namespace Word

def toBitVec64LT (w : Word (Fin BB)) (h_w : w.isU64) : BitVec 64 :=
  BitVec.ofNatLT w.toNat (by
    simp [Word.toNat]
    have := h_w 0
    have := h_w 1
    have := h_w 2
    have := h_w 3
    simp at *
    linarith)

end Word

namespace BitVec

theorem helper {a b : BitVec 64}
  (h : (a + b) % 4 = 0)
  : 18446744073709551614#64 &&& (a + b) = a + b
  :=
  by
    bv_decide

theorem mul4_add_is_mul4 {a b : BitVec 64}
  (ha : a % 4 = 0)
  (hb : b % 4 = 0)
  : (a + b) % 4 = 0
  :=
  by
    bv_decide

theorem BB_mod_eq {x : Fin BB} {q m : ℕ}
  : (x % q = m) ↔ (BitVec.ofNatLT (w := 64) x (by have := x.isLt; linarith) % q = m)
  :=
  by
    sorry

end BitVec

section

set_option autoImplicit false

namespace Jalr

open PreSail (SequentialState)
open LeanRV64IM.Functions

variable
  (Main : Vector (Fin BB) 38)
  (s : SailState)
  (cstrs : (constraints Main).allHold)
  (h_is_real : Main[29] = 1)

def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_JALR imm rs1 rd
  pure ()

def sp1_imm : BitVec 12 :=
  by
    refine BitVec.ofNatLT
      (Main[21].val + Main[22].val * 2^16 + Main[23].val * 2^32 + Main[24].val * 2^48)
      ?_

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    have trusted_instr_cstrs := reader_cstrs.1
    clear reader_cstrs

    aesop

def sp1_op_b : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[14] ?_
    simp

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    have trusted_instr_cstrs := reader_cstrs.1
    clear reader_cstrs

    itauto

def sp1_op_a : BitVec 5 :=
  by
    refine BitVec.ofNatLT Main[6] ?_
    simp

    have reader_cstrs := by
      simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
      exact cstrs.2.2.1

    clear cstrs
    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs

    have trusted_instr_cstrs := reader_cstrs.1
    clear reader_cstrs

    itauto

def sp1_jalr : SailM Unit := do
  let op_a := sp1_op_a Main cstrs h_is_real
  SailState.write_reg op_a (Word.toBitVec64 #v[Main[34], Main[35], Main[36], Main[37]])
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])

-- attribute [simp] bind StateT.bind EStateM.bind get getThe MonadStateOf.get StateT.get EStateM.get modify modifyGet MonadStateOf.modifyGet StateT.modifyGet EStateM.modifyGet pure EStateM.pure

set_option maxHeartbeats 500000 in
theorem correct 
  (state_cstrs : (constraints Main).initialState s) :
  let imm := sp1_imm Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_jalr imm (.Regidx op_b) (.Regidx op_a)).run s = (sp1_jalr Main cstrs h_is_real).run s
  :=
  by
    extract_lets imm op_b op_a

    -- pull out state constraints about the contents of register and pc reads
    simp [SP1ConstraintList.initialState, constraints, SP1Constraint.toStateProp, List.Forall, AddOperation.constraints, ITypeReader.constraints, CPUState.constraints, h_is_real] at state_cstrs
    obtain ⟨read_pc, ⟨read_op_a, read_op_b⟩⟩ := state_cstrs

    -- pull out constraints
    simp [SP1ConstraintList.allHold, constraints, SP1Constraint.toProp] at cstrs
    obtain ⟨res_cstrs, ⟨pc_cstrs, ⟨reader_cstrs, ⟨inc_pc_cstrs, chip_cstrs⟩⟩⟩⟩ := cstrs

    simp [ITypeReader.constraints, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq, SP1Constraint.toProp] at reader_cstrs
    obtain ⟨⟨h_op_b, ⟨⟨h_c_0, ⟨h_c_1, ⟨h_c_2, h_c_3⟩⟩⟩, h_c_mul4⟩⟩, 
      ⟨h_op_a, ⟨_, ⟨_, ⟨op_a_0_is_bool, ⟨op_a_0_iff_op_a_is_0, ⟨pc_mul_4, ⟨h_pc_0, ⟨h_pc_1, h_pc_2⟩⟩⟩⟩⟩⟩⟩⟩⟩ := reader_cstrs.1
    let read_op_b' := read_op_b h_op_b
    
    have b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := reader_cstrs.2.2.2.2.2.2.2.2.2.2
    let b_bv64 : BitVec 64 := Word.toBitVec64LT #v[Main[15], Main[16], Main[17], Main[18]] b_is_u64

    have imm_is_u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
      refine Word.isU64_of_cases #v[Main[21], Main[22], Main[23], Main[24]] ?_ ?_ ?_ ?_
      · simp
        clear * - h_c_0
        omega
      · simp [h_c_1]
      · simp [h_c_2]
      · simp [h_c_3]

    have pc_is_u64 : Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
      exact Word.isU64_of_cases #v[Main[3], Main[4], Main[5], 0] h_pc_0 h_pc_1 h_pc_2 (by simp)

    have ⟨res_is_u64, h_res⟩ := (AddOperation.correct #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[30], Main[31], Main[32], Main[33]] } Main[29] h_is_real res_cstrs) b_is_u64 imm_is_u64
    rw [Word.toBitVec64_LT_eq_toNat res_is_u64, Word.toBitVec64_LT_eq_toNat b_is_u64, Word.toBitVec64_LT_eq_toNat imm_is_u64] at h_res
    simp [Word.toNat, h_c_1, h_c_2, h_c_3] at h_res

    -- simp [AddOperation.spec, Word.toBitVec64, Word.toNat] at h_res

    clear res_cstrs reader_cstrs pc_cstrs

    simp [spec_jalr, sp1_jalr, EStateM.run, execute_JALR]
    simp [op_a, op_b, imm, sp1_op_a, sp1_op_b, sp1_imm]
    simp [Sail.readReg, Sail.writeReg, PreSail.readReg, PreSail.writeReg]
    simpM
    rw [read_pc]
    simpM

    rw [SailState.get_reg?_is_rX]
    simp [SailState.get_reg?, SequentialState.regs]
    rw [Std.ExtDHashMap.get?_insert]
    simp [SailState.reg_idx_never_nextPC, Option.toSailM]
    simp [SailState.get_reg?] at read_op_b'
    simpM
    rw [read_op_b']
    simp
    /- conv => -/
    /-   lhs -/
    /-   arg 2 -/
    /-   simp only [Option.elim_some, EStateM.pure] -/
    clear read_op_b'

    simpM
    simp [h_c_1, h_c_2, h_c_3]
    -- conv =>
    --   lhs
    --   arg 2
    --   simp

    -- conv =>
    --   lhs
    --   arg 2
    --   arg 2
    --   simp [ext_control_check_addr]
    --   -- arg 1
    --   -- arg 1
    --   -- simp [Word.toBitVec64_eq_add, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend, BitVec.ofInt]
    --   -- simp [BitVec.add_def]
    --   -- rfl
    -- conv =>
    --   lhs 
    --   arg 2
    --   simp only [bits_of_virtaddr]

    simp [ext_control_check_addr, bits_of_virtaddr]
    conv =>
      lhs
      arg 2
      arg 1
      rw [Word.toBitVec64_LT_eq_toNat b_is_u64]
      simp [Word.toNat]
      rfl

    -- should come from bv_decide
    have trusted_jmp : (bit_to_bool (Sail.BitVec.access (Sail.BitVec.update (b_bv64 + sign_extend imm) 0 0#1) 1)) = pure false :=
      by
        sorry
    simp [b_bv64, imm, Word.toBitVec64LT, Word.toNat, sp1_imm, h_c_1, h_c_2, h_c_3] at trusted_jmp
    rw [trusted_jmp]
    clear trusted_jmp

    simpM

    -- Simplify the pure false bind by unfolding definitions
    conv =>
      lhs
      arg 2
      arg 1
      unfold EStateM.pure EStateM.bind
      simp

    -- Now unfold the bind to substitute false
    conv =>
      lhs
      arg 2
      unfold EStateM.bind
      simp

    -- per RISC-V spec. very safe axiom to have
    have always_misa : ∀s : SailState, s.regs.get? Register.misa = some 0 := by sorry

    -- try to reduce currentlyEnabled
    simp only [currentlyEnabled, hartSupports]
    simp [Sail.readReg, PreSail.readReg]
    simpM

    conv =>
      lhs
      arg 2
      intro s'
      simp [always_misa]
    clear always_misa

    -- Now simplify the mapped pure computation  
    conv =>
      lhs
      arg 2
      intro s'
      simp only [Functor.map]
      change match EStateM.Result.ok false s' with
        | EStateM.Result.ok a s => _
        | EStateM.Result.error e s => EStateM.Result.error e s
      simp

    simp [get_next_pc, Sail.readReg, PreSail.readReg]
    simpM

    -- Simplify the register lookup using get?_insert
    -- The state s' has regs = s.regs.insert Register.nextPC ...
    -- and we're looking up Register.nextPC, so we should get the inserted value

    cases op_a_0_is_bool with
    | inl op_a_0_is_0 =>
        -- TODO(gzgz): god this is awful
        have op_a_not_x0 : op_a ≠ 0 := by
          simp only [op_a, sp1_op_a, BitVec.ofNatLT, ne_eq]
          intro h
          simp [op_a_0_is_0] at op_a_0_iff_op_a_is_0
          apply op_a_0_iff_op_a_is_0
          have := congrArg (·.toFin.val) h
          simp at this
          exact this
        simp [op_a, sp1_op_a] at op_a_not_x0

        simp [← bind_pure_comp] 
        simpM
        rw [←SailState.wX_bits_is_regidx_write]
        simp [SailState.regidx_write]
        simp [op_a_not_x0]
        simpM

        simp [set_next_pc, Sail.writeReg, PreSail.writeReg]
        simpM

        have pc_sum_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 :=
          by
            clear * - h_pc_0 h_pc_1 h_pc_2
            simp at *
            omega
        -- have pc_ofNat_eq_pc_ofNatLT := BitVec.ofNatLT_eq_ofNat pc_sum_u64
        -- simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
        rw [←(BitVec.ofNatLT_eq_ofNat pc_sum_u64)]

        simp [sign_extend]
        rw [Sail.sign_extend_no_change (x := Main[21]) (by clear * - h_c_0; omega) (by simp)]

        rw [Word.toBitVec64_LT_eq_toNat b_is_u64]
        simp [Word.toNat]

        -- rw [SailState.write_reg_is_wX]
        -- simp [SailState.write_reg, op_a_not_x0]
        -- simpM

        rw [Word.toBitVec64_LT_eq_toNat res_is_u64]
        simp [Word.toNat]
        rw [h_res]
        clear h_res

        obtain ⟨a_write_is_u64, h_a_write⟩ :=
          AddOperation.correct
          #v[Main[3], Main[4], Main[5], 0]
          #v[4, 0, 0, 0]
          { value := #v[Main[34], Main[35], Main[36], Main[37]] }
          (Main[29] - Main[13])
          (by simp [h_is_real, op_a_0_is_0])
          inc_pc_cstrs
          pc_is_u64
          (by simp [Word.isU64]; clear * - h_pc_0 h_pc_1 h_pc_2; trivial)
        rw [Word.toBitVec64_LT_eq_toNat a_write_is_u64, Word.toBitVec64_LT_eq_toNat pc_is_u64] at h_a_write
        conv at h_a_write =>
          rhs
          simp [Word.toBitVec64, Word.toNat]
          rfl

        rw [Word.toBitVec64_LT_eq_toNat a_write_is_u64]
        simp
        rw [h_a_write]

        simp [SailState.write_reg, op_a_not_x0]
        simpM

        apply Std.ExtDHashMap.ext_get?

        intro idx
        by_cases h_nextPC : Register.nextPC = idx
        · rw [Std.ExtDHashMap.get?_insert]
          simp [h_nextPC]
          rw [Std.ExtDHashMap.get?_insert]
          simp [h_nextPC]

          simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
          apply BitVec.helper
          clear * - b_is_u64 h_c_mul4 h_c_0
          -- have b_limbs := Word.lt_cases_of_isU64 b_is_u64
          -- simp at [b_limbs]

          have h_b_0_mul4 : Main[15].val % 4 = 0 := by sorry
          have h_b_0 : Main[15].val < 65536 := by exact b_is_u64 0
          have h_b_1 : Main[16].val < 65536 := by exact b_is_u64 1
          have h_b_2 : Main[17].val < 65536 := by exact b_is_u64 2
          have h_b_3 : Main[18].val < 65536 := by exact b_is_u64 3
          have h_sum_nat_mul4 : (Main[15].val + Main[16].val * 65536 + Main[17].val * 4294967296 + Main[18].val * 281474976710656) % 4 = 0 :=
            by
              omega
            -- simp [BitVec.umod_def]
          refine BitVec.mul4_add_is_mul4 ?_ ?_
          · simp [BitVec.umod_def]
            apply congrArg
            exact h_sum_nat_mul4
          · simp [BitVec.umod_def]
            -- rw [←BitVec.ofNatLT_eq_ofNat (w := 64) (n := Main[21].val % 4) sorry]
            apply congrArg
            simp [Fin.mod_def] at h_c_mul4
            exact h_c_mul4
        by_cases h_op_a : (reg_idx_to_Register op_a) = idx
        · simp [op_a, sp1_op_a] at h_op_a
          repeat (rw [Std.ExtDHashMap.get?_insert]; simp [h_nextPC, h_op_a])
        simp [op_a, sp1_op_a] at h_op_a
        repeat (rw [Std.ExtDHashMap.get?_insert]; simp [h_nextPC, h_op_a])
    | inr op_a_0_is_1 =>
        have op_a_is_x0 : op_a = 0 := by
          clear * - op_a_0_iff_op_a_is_0 op_a_0_is_1
          simp [op_a, sp1_op_a]
          simp_all only [Fin.isValue, true_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod, BitVec.ofNatLT_zero]
        simp [op_a, sp1_op_a] at op_a_is_x0

        simp [← bind_pure_comp] 
        simpM
        simp [wX_bits, wX, op_a_is_x0]
        simpM
        simp [set_next_pc, Sail.writeReg, PreSail.writeReg]
        simpM
        
        have pc_sum_u64 : Main[3].val + Main[4].val * 65536 + Main[5].val * 4294967296 < 2^64 :=
          by
            clear * - h_pc_0 h_pc_1 h_pc_2
            simp at *
            omega
        -- have pc_ofNat_eq_pc_ofNatLT := BitVec.ofNatLT_eq_ofNat pc_sum_u64
        -- simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
        rw [←(BitVec.ofNatLT_eq_ofNat pc_sum_u64)]

        simp [sign_extend]
        rw [Sail.sign_extend_no_change (x := Main[21]) (by clear * - h_c_0; omega) (by simp)]

        rw [Word.toBitVec64_LT_eq_toNat b_is_u64]
        simp [Word.toNat]

        conv =>
          rhs
          arg 2
          simp [SailState.write_reg]
        simp [op_a_0_is_1] at chip_cstrs
        obtain ⟨_, ⟨_, ⟨_, ⟨op_a3_is_0, ⟨op_a0_is_0, ⟨op_a1_is_0, op_a2_is_0⟩⟩⟩⟩⟩⟩ := chip_cstrs
        simp [op_a0_is_0, op_a3_is_0, op_a1_is_0, op_a2_is_0]
        conv =>
          rhs
          arg 2
          simp [Word.toBitVec64, Word.toNat]
        simpM
        -- move this block above before the `simp` and you can simp fine...

        rw [Word.toBitVec64_LT_eq_toNat res_is_u64]
        simp [Word.toNat]
        rw [h_res]
        clear h_res

        apply Std.ExtDHashMap.ext_get?

        intro idx
        by_cases h_nextPC : Register.nextPC = idx
        · rw [Std.ExtDHashMap.get?_insert]
          simp [h_nextPC]
          rw [Std.ExtDHashMap.get?_insert]
          simp [h_nextPC]

          simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
          apply BitVec.helper
          clear * - b_is_u64 h_c_mul4 h_c_0
          -- have b_limbs := Word.lt_cases_of_isU64 b_is_u64
          -- simp at [b_limbs]

          have h_b_0_mul4 : Main[15].val % 4 = 0 := by sorry
          have h_b_0 : Main[15].val < 65536 := by exact b_is_u64 0
          have h_b_1 : Main[16].val < 65536 := by exact b_is_u64 1
          have h_b_2 : Main[17].val < 65536 := by exact b_is_u64 2
          have h_b_3 : Main[18].val < 65536 := by exact b_is_u64 3
          have h_sum_nat_mul4 : (Main[15].val + Main[16].val * 65536 + Main[17].val * 4294967296 + Main[18].val * 281474976710656) % 4 = 0 :=
            by
              omega
            -- simp [BitVec.umod_def]
          refine BitVec.mul4_add_is_mul4 ?_ ?_
          · simp [BitVec.umod_def]
            apply congrArg
            exact h_sum_nat_mul4
          · simp [BitVec.umod_def]
            -- rw [←BitVec.ofNatLT_eq_ofNat (w := 64) (n := Main[21].val % 4) sorry]
            apply congrArg
            simp [Fin.mod_def] at h_c_mul4
            exact h_c_mul4
        repeat (rw [Std.ExtDHashMap.get?_insert]; simp [h_nextPC])

/-
⊢ 18446744073709551614#64 &&&
    (↑Main[15] + ↑Main[16] * 65536 + ↑Main[17] * 4294967296 + ↑Main[18] * 281474976710656)#'⋯ + (↑Main[21])#'⋯ =
  (↑Main[15] + ↑Main[16] * 65536 + ↑Main[17] * 4294967296 + ↑Main[18] * 281474976710656)#'⋯ + (↑Main[21])#'⋯
-/

end Jalr

end
