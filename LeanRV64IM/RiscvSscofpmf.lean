import LeanRV64IM.RiscvErrors
import LeanRV64IM.RiscvSysRegs
import LeanRV64IM.RiscvZihpm

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV64IM.Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open uop
open sopw
open sop
open seed_opst
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
open instruction
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open cbop_zicbom
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open WaitReason
open TrapVectorMode
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmeventh (index : Nat) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmevent) index) 63 32))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmeventh (index : Nat) (value : (BitVec 32)) : SailM Unit := do
  if ((BitVec.access sys_writable_hpm_counters index) == 1#1)
  then
    writeReg mhpmevent (vectorUpdate (← readReg mhpmevent) index
      (← (legalize_hpmevent
          (Mk_HpmEvent
            (value ++ (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmevent) index) 31 0))))))
  else (pure ())

def get_scountovf (priv : Privilege) : SailM (BitVec 32) := do
  let overflow ← do
    (pure ((_get_HpmEvent_OF (GetElem?.getElem! (← readReg mhpmevent) 31)) ++ ((_get_HpmEvent_OF
            (GetElem?.getElem! (← readReg mhpmevent) 30)) ++ ((_get_HpmEvent_OF
              (GetElem?.getElem! (← readReg mhpmevent) 29)) ++ ((_get_HpmEvent_OF
                (GetElem?.getElem! (← readReg mhpmevent) 28)) ++ ((_get_HpmEvent_OF
                  (GetElem?.getElem! (← readReg mhpmevent) 27)) ++ ((_get_HpmEvent_OF
                    (GetElem?.getElem! (← readReg mhpmevent) 26)) ++ ((_get_HpmEvent_OF
                      (GetElem?.getElem! (← readReg mhpmevent) 25)) ++ ((_get_HpmEvent_OF
                        (GetElem?.getElem! (← readReg mhpmevent) 24)) ++ ((_get_HpmEvent_OF
                          (GetElem?.getElem! (← readReg mhpmevent) 23)) ++ ((_get_HpmEvent_OF
                            (GetElem?.getElem! (← readReg mhpmevent) 22)) ++ ((_get_HpmEvent_OF
                              (GetElem?.getElem! (← readReg mhpmevent) 21)) ++ ((_get_HpmEvent_OF
                                (GetElem?.getElem! (← readReg mhpmevent) 20)) ++ ((_get_HpmEvent_OF
                                  (GetElem?.getElem! (← readReg mhpmevent) 19)) ++ ((_get_HpmEvent_OF
                                    (GetElem?.getElem! (← readReg mhpmevent) 18)) ++ ((_get_HpmEvent_OF
                                      (GetElem?.getElem! (← readReg mhpmevent) 17)) ++ ((_get_HpmEvent_OF
                                        (GetElem?.getElem! (← readReg mhpmevent) 16)) ++ ((_get_HpmEvent_OF
                                          (GetElem?.getElem! (← readReg mhpmevent) 15)) ++ ((_get_HpmEvent_OF
                                            (GetElem?.getElem! (← readReg mhpmevent) 14)) ++ ((_get_HpmEvent_OF
                                              (GetElem?.getElem! (← readReg mhpmevent) 13)) ++ ((_get_HpmEvent_OF
                                                (GetElem?.getElem! (← readReg mhpmevent) 12)) ++ ((_get_HpmEvent_OF
                                                  (GetElem?.getElem! (← readReg mhpmevent) 11)) ++ ((_get_HpmEvent_OF
                                                    (GetElem?.getElem! (← readReg mhpmevent) 10)) ++ ((_get_HpmEvent_OF
                                                      (GetElem?.getElem! (← readReg mhpmevent) 9)) ++ ((_get_HpmEvent_OF
                                                        (GetElem?.getElem! (← readReg mhpmevent) 8)) ++ ((_get_HpmEvent_OF
                                                          (GetElem?.getElem! (← readReg mhpmevent)
                                                            7)) ++ ((_get_HpmEvent_OF
                                                            (GetElem?.getElem!
                                                              (← readReg mhpmevent) 6)) ++ ((_get_HpmEvent_OF
                                                              (GetElem?.getElem!
                                                                (← readReg mhpmevent) 5)) ++ ((_get_HpmEvent_OF
                                                                (GetElem?.getElem!
                                                                  (← readReg mhpmevent) 4)) ++ ((_get_HpmEvent_OF
                                                                  (GetElem?.getElem!
                                                                    (← readReg mhpmevent) 3)) ++ (0b000 : (BitVec 3))))))))))))))))))))))))))))))))
  match priv with
  | Machine => (pure overflow)
  | Supervisor => (pure (overflow &&& (← readReg mcounteren)))
  | User => (internal_error "model/riscv_sscofpmf.sail" 74 "scountovf not readable from User mode")

