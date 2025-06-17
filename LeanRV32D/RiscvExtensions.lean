import LeanRV32D.RvfiDii

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV32D.Functions

open zvkfunct6
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
open word_width
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
open vext8funct6
open vext4funct6
open vext2funct6
open uop
open sopw
open sop
open seed_opst
open rounding_mode
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
open fregno
open fregidx
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cbop_zicbom
open cbie
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open ast
open amoop
open agtype
open WaitReason
open TrapVectorMode
open Step
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open HartState
open FetchResult
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def hartSupports_measure (ext : extension) : Int :=
  match ext with
  | Ext_C => 1
  | _ => 0

def hartSupports (merge_var : extension) : Bool :=
  match merge_var with
  | Ext_M => true
  | Ext_A => true
  | Ext_F => true
  | Ext_D => true
  | Ext_B => true
  | Ext_V => true
  | Ext_S => true
  | Ext_U => true
  | Ext_Zicbom => true
  | Ext_Zicboz => true
  | Ext_Zicntr => true
  | Ext_Zicond => true
  | Ext_Zicsr => true
  | Ext_Zifencei => true
  | Ext_Zihpm => true
  | Ext_Zimop => true
  | Ext_Zmmul => false
  | Ext_Zaamo => false
  | Ext_Zabha => true
  | Ext_Zalrsc => false
  | Ext_Zawrs => true
  | Ext_Zfa => true
  | Ext_Zfh => true
  | Ext_Zfhmin => false
  | Ext_Zfinx => false
  | Ext_Zdinx => false
  | Ext_Zca => true
  | Ext_Zcb => true
  | Ext_Zcd => true
  | Ext_Zcf => ((true : Bool) && (xlen == 32))
  | Ext_Zcmop => true
  | Ext_C =>
    ((hartSupports Ext_Zca) && (((hartSupports Ext_Zcf) || ((not (hartSupports Ext_F)) || (xlen != 32))) && ((hartSupports
            Ext_Zcd) || (not (hartSupports Ext_D)))))
  | Ext_Zba => false
  | Ext_Zbb => false
  | Ext_Zbc => true
  | Ext_Zbkb => true
  | Ext_Zbkc => true
  | Ext_Zbkx => true
  | Ext_Zbs => false
  | Ext_Zknd => true
  | Ext_Zkne => true
  | Ext_Zknh => true
  | Ext_Zkr => true
  | Ext_Zksed => true
  | Ext_Zksh => true
  | Ext_Zhinx => false
  | Ext_Zhinxmin => false
  | Ext_Zvbb => true
  | Ext_Zvkb => false
  | Ext_Zvbc => true
  | Ext_Zvkg => true
  | Ext_Zvkned => true
  | Ext_Zvknha => true
  | Ext_Zvknhb => true
  | Ext_Zvksh => true
  | Ext_Sscofpmf => true
  | Ext_Sstc => true
  | Ext_Svinval => true
  | Ext_Svnapot => false
  | Ext_Svpbmt => false
  | Ext_Svbare => true
  | Ext_Sv32 => ((true : Bool) && (xlen == 32))
  | Ext_Sv39 => ((true : Bool) && (xlen == 64))
  | Ext_Sv48 => ((true : Bool) && (xlen == 64))
  | Ext_Sv57 => ((true : Bool) && (xlen == 64))
  | Ext_Smcntrpmf => true
termination_by let ext := merge_var; ((hartSupports_measure ext)).toNat

