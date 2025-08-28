import LeanRV64D.Sail.Sail
import LeanRV64D.Sail.BitVec
import LeanRV64D.Sail.IntRange
import LeanRV64D.Defs
import LeanRV64D.Specialization
import LeanRV64D.FakeReal
import LeanRV64D.RiscvExtras

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

def encdec_nfields_forwards (arg_ : (BitVec 3)) : Int :=
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then 1
  else
    (if ((b__0 == (0b001 : (BitVec 3))) : Bool)
    then 2
    else
      (if ((b__0 == (0b010 : (BitVec 3))) : Bool)
      then 3
      else
        (if ((b__0 == (0b011 : (BitVec 3))) : Bool)
        then 4
        else
          (if ((b__0 == (0b100 : (BitVec 3))) : Bool)
          then 5
          else
            (if ((b__0 == (0b101 : (BitVec 3))) : Bool)
            then 6
            else
              (if ((b__0 == (0b110 : (BitVec 3))) : Bool)
              then 7
              else 8))))))

/-- Type quantifiers: arg_ : Nat, arg_ > 0 ∧ arg_ ≤ 8 -/
def encdec_nfields_backwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => (0b000 : (BitVec 3))
  | 2 => (0b001 : (BitVec 3))
  | 3 => (0b010 : (BitVec 3))
  | 4 => (0b011 : (BitVec 3))
  | 5 => (0b100 : (BitVec 3))
  | 6 => (0b101 : (BitVec 3))
  | 7 => (0b110 : (BitVec 3))
  | _ => (0b111 : (BitVec 3))

def encdec_nfields_forwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b001 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b010 : (BitVec 3))) : Bool)
      then true
      else
        (if ((b__0 == (0b011 : (BitVec 3))) : Bool)
        then true
        else
          (if ((b__0 == (0b100 : (BitVec 3))) : Bool)
          then true
          else
            (if ((b__0 == (0b101 : (BitVec 3))) : Bool)
            then true
            else
              (if ((b__0 == (0b110 : (BitVec 3))) : Bool)
              then true
              else
                (if ((b__0 == (0b111 : (BitVec 3))) : Bool)
                then true
                else false)))))))

/-- Type quantifiers: arg_ : Nat, arg_ > 0 ∧ arg_ ≤ 8 -/
def encdec_nfields_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | _ => false

def nfields_string_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "" => (pure 1)
  | "seg2" => (pure 2)
  | "seg3" => (pure 3)
  | "seg4" => (pure 4)
  | "seg5" => (pure 5)
  | "seg6" => (pure 6)
  | "seg7" => (pure 7)
  | "seg8" => (pure 8)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ > 0 ∧ arg_ ≤ 8 -/
def nfields_string_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | _ => false

def nfields_string_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "" => true
  | "seg2" => true
  | "seg3" => true
  | "seg4" => true
  | "seg5" => true
  | "seg6" => true
  | "seg7" => true
  | "seg8" => true
  | _ => false

def encdec_nfields_pow2_forwards (arg_ : (BitVec 3)) : SailM Int := do
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then (pure 1)
  else
    (do
      if ((b__0 == (0b001 : (BitVec 3))) : Bool)
      then (pure 2)
      else
        (do
          if ((b__0 == (0b011 : (BitVec 3))) : Bool)
          then (pure 4)
          else
            (do
              if ((b__0 == (0b111 : (BitVec 3))) : Bool)
              then (pure 8)
              else
                (do
                  assert false "Pattern match failure at unknown location"
                  throw Error.Exit))))

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def encdec_nfields_pow2_backwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => (0b000 : (BitVec 3))
  | 2 => (0b001 : (BitVec 3))
  | 4 => (0b011 : (BitVec 3))
  | _ => (0b111 : (BitVec 3))

def encdec_nfields_pow2_forwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b001 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b011 : (BitVec 3))) : Bool)
      then true
      else
        (if ((b__0 == (0b111 : (BitVec 3))) : Bool)
        then true
        else false)))

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def encdec_nfields_pow2_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def nfields_pow2_string_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "1" => (pure 1)
  | "2" => (pure 2)
  | "4" => (pure 4)
  | "8" => (pure 8)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def nfields_pow2_string_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def nfields_pow2_string_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "1" => true
  | "2" => true
  | "4" => true
  | "8" => true
  | _ => false

