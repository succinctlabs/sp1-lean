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

def undefined_CountSmcntrpmf (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CountSmcntrpmf (v : (BitVec 64)) : (BitVec 64) :=
  v

def legalize_smcntrpmf (c : (BitVec 64)) (value : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_CountSmcntrpmf value)
  (pure (_update_CountSmcntrpmf_UINH
      (_update_CountSmcntrpmf_SINH (_update_CountSmcntrpmf_MINH c (_get_CountSmcntrpmf_MINH v))
        (← do
          bif (← (currentlyEnabled Ext_S))
          then (pure (_get_CountSmcntrpmf_SINH v))
          else (pure (0b0 : (BitVec 1)))))
      (← do
        bif (← (currentlyEnabled Ext_U))
        then (pure (_get_CountSmcntrpmf_UINH v))
        else (pure (0b0 : (BitVec 1))))))

def counter_priv_filter_bit (reg : (BitVec 64)) (priv : Privilege) : (BitVec 1) :=
  match priv with
  | Machine => (_get_CountSmcntrpmf_MINH reg)
  | Supervisor => (_get_CountSmcntrpmf_SINH reg)
  | User => (_get_CountSmcntrpmf_UINH reg)

