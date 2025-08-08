import SP1Foundations
import LeanRV64IM.RiscvInstsEnd
import Mathlib

macro "simpM'" : tactic => `(tactic| simp [bind, StateT.bind, EStateM.bind, ExceptT.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, ExceptT.pure, StateT.map, EStateM.map, ExceptT.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet])

namespace Load

open Sail LeanRV64IM.Functions

theorem ayo
  {imm : BitVec 12}
  {op_a op_b : regidx}
  {op_a_val op_b_val : BitVec 64}
  {h_read_op_a : rX_bits op_a = pure op_a_val}
  {h_read_op_b : rX_bits op_b = pure op_b_val}
  : (execute_LOAD imm op_b op_a false 1).run s = (pure RETIRE_SUCCESS : SailM ExecutionResult).run s :=
  by
    simp [execute_LOAD, assert, PreSail.assert, LeanRV64IM.Functions.xlen_bytes]

    simp [vmem_read, ext_data_get_addr]
    simp [h_read_op_b, check_misaligned, LeanRV64IM.Functions.plat_enable_misaligned_access, is_aligned_vaddr, LeanRV64IM.Functions.not]

    simp [split_misaligned]
    have always_aligned : is_aligned_vaddr (virtaddr.Virtaddr (op_b_val + sign_extend imm)) 1 = true := by sorry
    simp [always_aligned]

    simp [untilFuelM, untilFuelM.go, assert, PreSail.assert]

    have always_machine : readReg Register.cur_privilege = pure Privilege.Machine := by sorry
    have always_mmstatus : readReg Register.mstatus = pure 0 := by sorry
    have wtf : (Privilege.Machine == Privilege.Machine) = true := by trivial
    have wtf2 : (SATPMode.Bare == SATPMode.Bare) = true := by trivial
    conv =>
      lhs
      arg 2
      arg 1
      arg 1
      simp [translateAddr]
      simp [always_machine, always_mmstatus]
      simp [effectivePrivilege, _get_Mstatus_MPRV, Sail.BitVec.extractLsb]
      simp [translationMode]
      simp [wtf, wtf2]
      rfl

    have always_phys_mem : ∀(addr) (width), within_phys_mem addr width = pure true := by sorry
    conv =>
      lhs
      arg 2
      arg 1
      arg 1
      arg 1
      simp [bits_of_virtaddr]
      simp [mem_read]
      simp [always_machine, always_mmstatus]
      simp [effectivePrivilege, _get_Mstatus_MPRV, Sail.BitVec.extractLsb]
      unfold mem_read_priv
      unfold mem_read_priv_meta
      simp [cond]
      arg 2
      arg 1
      unfold checked_mem_read
      simp [phys_access_check, always_phys_mem, LeanRV64IM.Functions.sys_pmp_count]
      simp [within_mmio_readable, get_config_rvfi]
      simp [read_kind_of_flags, ext_check_phys_mem_read, phys_mem_read, LeanRV64IM.Functions.read_ram, sail_mem_read, PreSail.sail_mem_read]
      simp [__ReadRAM_Meta, PreSail.readBytes, PreSail.readByte]
      rfl
      -- simp [mem_read_priv, mem_read_priv_meta, checked_mem_read]
      -- simp [phys_access_check, LeanRV64IM.Functions.sys_pmp_count]
      -- rfl

    simp [MemoryOpResult_drop_meta]

    simp [SailME.run, EStateM.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, EStateM.bind, MonadStateOf.get, EStateM.get, getThe, get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, ExceptT.map, EStateM.map, ExceptT.bindCont]
    
    have h_read : s.mem[(zero_extend (m := 64) (BitVec.addInt (op_b_val + sign_extend imm) 0)).toNat]? = some 42 := by sorry
    simp [h_read]

    simpM
    simp [extend_value, sign_extend, Sail.BitVec.signExtend]
    simp [misaligned_order, sys_misaligned_order_decreasing]
    -- simp [bind, StateT.bind, EStateM.bind, ExceptT.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, ExceptT.pure, StateT.map, EStateM.map, ExceptT.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, EStateM.run, SailME.run, ExceptT.run, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, ExceptT.bindCont]

    sorry

section mwe

abbrev M := StateT Nat (Except String)

def repeat_example : M Nat := do
  let final_loop_state ← (do
    let mut loop_state := (false, 0)
    repeat
      let (_, n) := loop_state
      let x ← get
      loop_state ← pure (true, n + x)
    until loop_state.1
    pure loop_state.2
  )
  pure final_loop_state

theorem unfold_repeat : repeat_example.run 2 = .ok 2 :=
  by
    sorry

end mwe

end Load
