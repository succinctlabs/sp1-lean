import LeanRV32IM.Sail.Sail
import LeanRV32IM.Sail.BitVec
import LeanRV32IM.Sail.IntRange
import LeanRV32IM.Defs
import LeanRV32IM.Specialization
import LeanRV32IM.FakeReal
import LeanRV32IM.RiscvExtrasExecutable

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV32IM.Functions

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
open cfregidx
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

def encdec_mul_op_forwards (arg_ : mul_op) : SailM (BitVec 3) := do
  match arg_ with
  | { high := false, signed_rs1 := true, signed_rs2 := true } => (pure (0b000 : (BitVec 3)))
  | { high := true, signed_rs1 := true, signed_rs2 := true } => (pure (0b001 : (BitVec 3)))
  | { high := true, signed_rs1 := true, signed_rs2 := false } => (pure (0b010 : (BitVec 3)))
  | { high := true, signed_rs1 := false, signed_rs2 := false } => (pure (0b011 : (BitVec 3)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mul_op_backwards (arg_ : (BitVec 3)) : SailM mul_op := do
  let b__0 := arg_
  bif (b__0 == (0b000 : (BitVec 3)))
  then
    (pure { high := false
            signed_rs1 := true
            signed_rs2 := true })
  else
    (do
      bif (b__0 == (0b001 : (BitVec 3)))
      then
        (pure { high := true
                signed_rs1 := true
                signed_rs2 := true })
      else
        (do
          bif (b__0 == (0b010 : (BitVec 3)))
          then
            (pure { high := true
                    signed_rs1 := true
                    signed_rs2 := false })
          else
            (do
              bif (b__0 == (0b011 : (BitVec 3)))
              then
                (pure { high := true
                        signed_rs1 := false
                        signed_rs2 := false })
              else
                (do
                  assert false "Pattern match failure at unknown location"
                  throw Error.Exit))))

def encdec_mul_op_forwards_matches (arg_ : mul_op) : Bool :=
  match arg_ with
  | { high := false, signed_rs1 := true, signed_rs2 := true } => true
  | { high := true, signed_rs1 := true, signed_rs2 := true } => true
  | { high := true, signed_rs1 := true, signed_rs2 := false } => true
  | { high := true, signed_rs1 := false, signed_rs2 := false } => true
  | _ => false

def encdec_mul_op_backwards_matches (arg_ : (BitVec 3)) : Bool :=
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

def mul_mnemonic_backwards (arg_ : String) : SailM mul_op := do
  match arg_ with
  | "mul" =>
    (pure { high := false
            signed_rs1 := true
            signed_rs2 := true })
  | "mulh" =>
    (pure { high := true
            signed_rs1 := true
            signed_rs2 := true })
  | "mulhsu" =>
    (pure { high := true
            signed_rs1 := true
            signed_rs2 := false })
  | "mulhu" =>
    (pure { high := true
            signed_rs1 := false
            signed_rs2 := false })
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def mul_mnemonic_forwards_matches (arg_ : mul_op) : Bool :=
  match arg_ with
  | { high := false, signed_rs1 := true, signed_rs2 := true } => true
  | { high := true, signed_rs1 := true, signed_rs2 := true } => true
  | { high := true, signed_rs1 := true, signed_rs2 := false } => true
  | { high := true, signed_rs1 := false, signed_rs2 := false } => true
  | _ => false

def mul_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "mul" => true
  | "mulh" => true
  | "mulhsu" => true
  | "mulhu" => true
  | _ => false

