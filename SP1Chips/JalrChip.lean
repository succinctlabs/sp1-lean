import SP1Operations
import LeanRV64IM.RiscvInstsEnd

import SP1Chips.Jalr.Constraints

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

def sp1_jalr : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
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

-- attribute [simp] bind StateT.bind EStateM.bind get getThe MonadStateOf.get StateT.get EStateM.get modify modifyGet MonadStateOf.modifyGet StateT.modifyGet EStateM.modifyGet pure EStateM.pure

theorem correct 
  (state_cstrs : (constraints Main).initialState s) :
  let imm := sp1_imm Main cstrs h_is_real
  let op_b := sp1_op_b Main cstrs h_is_real
  let op_a := sp1_op_a Main cstrs h_is_real
  (spec_jalr imm (.Regidx op_b) (.Regidx op_a)).run s = sp1_jalr.run s
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
    obtain ⟨⟨h_op_b, ⟨⟨h_c_0, ⟨h_c_1, ⟨h_c_2, h_c_3⟩⟩⟩, h_c_mul4⟩⟩, _⟩ := reader_cstrs.1
    let read_op_b' := read_op_b h_op_b
    
    -- have h_res := AddOperation.correct #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[21], Main[22], Main[23], Main[24]] { value := #v[Main[30], Main[31], Main[32], Main[33]] } Main[29] h_is_real res_cstrs
    -- simp [AddOperation.spec, Word.toBitVec64, Word.toNat] at h_res
    clear res_cstrs reader_cstrs pc_cstrs inc_pc_cstrs chip_cstrs

    have b_is_u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := 
      by
        sorry
    let b_bv64 : BitVec 64 := Word.toBitVec64LT #v[Main[15], Main[16], Main[17], Main[18]] b_is_u64

    simp [spec_jalr, sp1_jalr, EStateM.run, execute_JALR]
    simp [op_a, op_b, imm, sp1_op_a, sp1_op_b, sp1_imm]
    simp [Sail.readReg, Sail.writeReg, PreSail.readReg, PreSail.writeReg]
    simp [bind,StateT.bind,EStateM.bind,get,getThe,MonadStateOf.get,StateT.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,EStateM.modifyGet,pure,EStateM.pure]
    rw [read_pc]
    simp [bind,StateT.bind,EStateM.bind,get,getThe,MonadStateOf.get,StateT.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,EStateM.modifyGet,pure,EStateM.pure]

    rw [SailState.get_reg?_is_rX]
    simp [SailState.get_reg?, SequentialState.regs]
    rw [Std.ExtDHashMap.get?_insert]
    simp [SailState.reg_idx_never_nextPC, Option.toSailM]
    simp [SailState.get_reg?] at read_op_b'
    simp [bind,StateT.bind,EStateM.bind,get,getThe,MonadStateOf.get,StateT.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,EStateM.modifyGet,pure,EStateM.pure]
    rw [read_op_b']
    simp
    /- conv => -/
    /-   lhs -/
    /-   arg 2 -/
    /-   simp only [Option.elim_some, EStateM.pure] -/
    clear read_op_b'

    
    simp [bind,StateT.bind,EStateM.bind,get,getThe,MonadStateOf.get,StateT.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,EStateM.modifyGet,pure,EStateM.pure]
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

    have trusted_jmp : (bit_to_bool (Sail.BitVec.access (Sail.BitVec.update (b_bv64 + sign_extend imm) 0 0#1) 1)) = pure false :=
      by
        sorry
    simp [b_bv64, imm, Word.toBitVec64LT, Word.toNat, sp1_imm, h_c_1, h_c_2, h_c_3] at trusted_jmp
    rw [trusted_jmp]
  
    simp [bind,StateT.bind,EStateM.bind,get,getThe,MonadStateOf.get,StateT.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,EStateM.modifyGet,pure,StateT.pure,EStateM.pure, pure_bind]

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

    have always_misa : ∀s : SailState, s.regs.get? Register.misa = some 0 := by sorry
    
    -- try to reduce currentlyEnabled
    simp only [currentlyEnabled, hartSupports]
    simp [Sail.readReg, PreSail.readReg]
    simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure]
    
    conv =>
      lhs
      arg 2
      intro s'
      simp [always_misa]
    
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
    simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map]
    
    -- Simplify the register lookup using get?_insert
    -- The state s' has regs = s.regs.insert Register.nextPC ...
    -- and we're looking up Register.nextPC, so we should get the inserted value
    
    simp [← bind_pure_comp] 
    simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map]
    rw [SailState.write_reg_is_wX]
    simp [SailState.write_reg]
    simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

    simp [set_next_pc, Sail.writeReg, PreSail.writeReg]
    simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]

    simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
    _

end Jalr

end
