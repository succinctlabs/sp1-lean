import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvVlen
import LeanRV64D.RiscvExtensions
import LeanRV64D.RiscvPmpRegs
import LeanRV64D.RiscvPlatform

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

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
open ntl_type
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
open cfregidx
open cbop_zicbom
open cbie
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open bop
open biop_zbs
open barrier_kind
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
open ISA_Format
open HartState
open FetchResult
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def check_privs (_ : Unit) : Bool :=
  if (((hartSupports Ext_S) && (not (hartSupports Ext_U))) : Bool)
  then
    (let _ : Unit :=
      (print_endline "User mode (U) should be enabled if supervisor mode (S) is enabled.")
    false)
  else true

def check_mmu_config (_ : Unit) : Bool :=
  let valid : Bool := true
  let _ : Unit :=
    let _ : Unit :=
      if (((not (hartSupports Ext_S)) && ((hartSupports Ext_Sv57) || ((hartSupports Ext_Sv48) || (hartSupports
                 Ext_Sv39)))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Supervisor mode (S) disabled but one of (Sv57, Sv48, Sv39) is enabled: cannot support address translation without supervisor mode."))
      else ()
    let _ : Unit :=
      if (((hartSupports Ext_Sv57) && (not (hartSupports Ext_Sv48))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Sv57 is enabled but Sv48 is disabled: supporting Sv57 requires supporting Sv48."))
      else ()
    let _ : Unit :=
      if (((hartSupports Ext_Sv48) && (not (hartSupports Ext_Sv39))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Sv48 is enabled but Sv39 is disabled: supporting Sv48 requires supporting Sv39."))
      else ()
    if ((hartSupports Ext_Sv32) : Bool)
    then
      (let valid : Bool := false
      (print_endline "Sv32 is enabled: Sv32 is not supported on RV64."))
    else ()
  valid

def check_vlen_elen (_ : Unit) : Bool :=
  if (((vlen_exp : Nat) <b (elen_exp : Nat)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "VLEN (set to 2^"
          (HAppend.hAppend (Int.repr vlen_exp)
            (HAppend.hAppend ") cannot be less than ELEN (set to 2^"
              (HAppend.hAppend (Int.repr elen_exp) ").")))))
    false)
  else
    (if ((((vlen_exp : Nat) <b 3) || (((vlen_exp : Nat) >b 16) : Bool)) : Bool)
    then
      (let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp) " but must be within [2^3, 2^16].")))
      false)
    else
      (if ((((elen_exp : Nat) <b 3) || (((elen_exp : Nat) >b 16) : Bool)) : Bool)
      then
        (let _ : Unit :=
          (print_endline
            (HAppend.hAppend "ELEN set to 2^"
              (HAppend.hAppend (Int.repr elen_exp) " but must be within [2^3, 2^16].")))
        false)
      else true))

/-- Type quantifiers: b_hi : Nat, b_lo : Nat, a_hi : Nat, a_lo : Nat, 0 ≤ a_lo, 0 ≤ a_hi, 0 ≤
  b_lo, 0 ≤ b_hi -/
def has_overlap (a_lo : Nat) (a_hi : Nat) (b_lo : Nat) (b_hi : Nat) : Bool :=
  (not (((a_lo <b b_lo) && (a_hi <b b_lo)) || ((b_lo <b a_lo) && (b_hi <b a_lo))))

def check_mem_layout (_ : Unit) : SailM Bool := do
  let valid : Bool := true
  let ram_lo ← do (pure (BitVec.toNat (← readReg plat_ram_base)))
  let ram_hi ← do
    (pure ((BitVec.toNat (← readReg plat_ram_base)) +i (BitVec.toNat (← readReg plat_ram_size))))
  let rom_lo ← do (pure (BitVec.toNat (← readReg plat_rom_base)))
  let rom_hi ← do
    (pure ((BitVec.toNat (← readReg plat_rom_base)) +i (BitVec.toNat (← readReg plat_rom_size))))
  let clint_lo ← do (pure (BitVec.toNat (← readReg plat_clint_base)))
  let clint_hi ← do
    (pure ((BitVec.toNat (← readReg plat_clint_base)) +i (BitVec.toNat
          (← readReg plat_clint_size))))
  let valid : Bool :=
    if ((has_overlap rom_lo rom_hi ram_lo ram_hi) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit := (print_endline "The RAM and ROM regions overlap.")
      valid)
    else valid
  let valid : Bool :=
    if ((has_overlap clint_lo clint_hi rom_lo rom_hi) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit := (print_endline "The Clint and ROM regions overlap.")
      valid)
    else valid
  if ((has_overlap clint_lo clint_hi ram_lo ram_hi) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit := (print_endline "The Clint and RAM regions overlap.")
    (pure valid))
  else (pure valid)

def check_pmp (_ : Unit) : Bool :=
  let valid : Bool := true
  if (((true : Bool) && (sys_pmp_grain != 0)) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit := (print_endline "NA4 is not supported if the PMP grain G is non-zero.")
    valid)
  else valid

def config_is_valid (_ : Unit) : SailM Bool := do
  (pure ((check_privs ()) && ((check_mmu_config ()) && ((← (check_mem_layout ())) && ((check_vlen_elen
              ()) && (check_pmp ()))))))

