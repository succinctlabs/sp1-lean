import LeanRV32D.RiscvInstsVextFpUtils

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

def sew_flag_forwards (arg_ : String) : SailM (BitVec 3) := do
  match arg_ with
  | "e8" => (pure (0b000 : (BitVec 3)))
  | "e16" => (pure (0b001 : (BitVec 3)))
  | "e32" => (pure (0b010 : (BitVec 3)))
  | "e64" => (pure (0b011 : (BitVec 3)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def sew_flag_forwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "e8" => true
  | "e16" => true
  | "e32" => true
  | "e64" => true
  | _ => false

def sew_flag_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  bif (b__0 == (0b000 : (BitVec 3)))
  then true
  else
    (bif (b__0 == (0b001 : (BitVec 3)))
    then true
    else
      (bif (b__0 == (0b010 : (BitVec 3)))
      then true
      else
        (bif (b__0 == (0b011 : (BitVec 3)))
        then true
        else false)))

def maybe_lmul_flag_forwards (arg_ : String) : SailM (BitVec 3) := do
  match arg_ with
  | _ => throw Error.Exit

def maybe_lmul_flag_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def maybe_lmul_flag_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  bif (b__0 == (0b101 : (BitVec 3)))
  then true
  else
    (bif (b__0 == (0b110 : (BitVec 3)))
    then true
    else
      (bif (b__0 == (0b111 : (BitVec 3)))
      then true
      else
        (bif (b__0 == (0b000 : (BitVec 3)))
        then true
        else
          (bif (b__0 == (0b001 : (BitVec 3)))
          then true
          else
            (bif (b__0 == (0b010 : (BitVec 3)))
            then true
            else
              (bif (b__0 == (0b011 : (BitVec 3)))
              then true
              else false))))))

def ta_flag_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | _ => throw Error.Exit

def ta_flag_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def ta_flag_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  bif (b__0 == (0b1 : (BitVec 1)))
  then true
  else
    (bif (b__0 == (0b0 : (BitVec 1)))
    then true
    else false)

def ma_flag_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | _ => throw Error.Exit

def ma_flag_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def ma_flag_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  bif (b__0 == (0b1 : (BitVec 1)))
  then true
  else
    (bif (b__0 == (0b0 : (BitVec 1)))
    then true
    else false)

def handle_illegal_vtype (_ : Unit) : SailM Unit := do
  writeReg vtype ((0b1 : (BitVec 1)) ++ (zeros (n := (xlen -i 1))))
  writeReg vl (zeros (n := ((2 ^i 2) *i 8)))
  (csr_name_write_callback "vtype" (← readReg vtype))
  (csr_name_write_callback "vl" (← readReg vl))

def vl_use_ceil : Bool := false

/-- Type quantifiers: VLMAX : Int, AVL : Int -/
def calculate_new_vl (AVL : Int) (VLMAX : Int) : (BitVec (2 ^ 2 * 8)) :=
  let new_vl :=
    bif (AVL ≤b VLMAX)
    then AVL
    else
      (bif (AVL <b (2 *i VLMAX))
      then
        (bif vl_use_ceil
        then (Int.tdiv (AVL +i 1) 2)
        else VLMAX)
      else VLMAX)
  (to_bits_unsafe (l := xlen) new_vl)

