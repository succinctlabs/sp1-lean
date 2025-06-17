import LeanRV32D.RiscvInstsBase

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

def amo_width_valid (size : word_width) : SailM Bool := do
  match size with
  | BYTE => (currentlyEnabled Ext_Zabha)
  | HALF => (currentlyEnabled Ext_Zabha)
  | WORD => (pure true)
  | DOUBLE => (pure (xlen ≥b 64))

def encdec_amoop_forwards (arg_ : amoop) : (BitVec 5) :=
  match arg_ with
  | AMOSWAP => (0b00001 : (BitVec 5))
  | AMOADD => (0b00000 : (BitVec 5))
  | AMOXOR => (0b00100 : (BitVec 5))
  | AMOAND => (0b01100 : (BitVec 5))
  | AMOOR => (0b01000 : (BitVec 5))
  | AMOMIN => (0b10000 : (BitVec 5))
  | AMOMAX => (0b10100 : (BitVec 5))
  | AMOMINU => (0b11000 : (BitVec 5))
  | AMOMAXU => (0b11100 : (BitVec 5))

def encdec_amoop_backwards (arg_ : (BitVec 5)) : SailM amoop := do
  let b__0 := arg_
  bif (b__0 == (0b00001 : (BitVec 5)))
  then (pure AMOSWAP)
  else
    (do
      bif (b__0 == (0b00000 : (BitVec 5)))
      then (pure AMOADD)
      else
        (do
          bif (b__0 == (0b00100 : (BitVec 5)))
          then (pure AMOXOR)
          else
            (do
              bif (b__0 == (0b01100 : (BitVec 5)))
              then (pure AMOAND)
              else
                (do
                  bif (b__0 == (0b01000 : (BitVec 5)))
                  then (pure AMOOR)
                  else
                    (do
                      bif (b__0 == (0b10000 : (BitVec 5)))
                      then (pure AMOMIN)
                      else
                        (do
                          bif (b__0 == (0b10100 : (BitVec 5)))
                          then (pure AMOMAX)
                          else
                            (do
                              bif (b__0 == (0b11000 : (BitVec 5)))
                              then (pure AMOMINU)
                              else
                                (do
                                  bif (b__0 == (0b11100 : (BitVec 5)))
                                  then (pure AMOMAXU)
                                  else
                                    (do
                                      assert false "Pattern match failure at unknown location"
                                      throw Error.Exit)))))))))

def encdec_amoop_forwards_matches (arg_ : amoop) : Bool :=
  match arg_ with
  | AMOSWAP => true
  | AMOADD => true
  | AMOXOR => true
  | AMOAND => true
  | AMOOR => true
  | AMOMIN => true
  | AMOMAX => true
  | AMOMINU => true
  | AMOMAXU => true

def encdec_amoop_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  let b__0 := arg_
  bif (b__0 == (0b00001 : (BitVec 5)))
  then true
  else
    (bif (b__0 == (0b00000 : (BitVec 5)))
    then true
    else
      (bif (b__0 == (0b00100 : (BitVec 5)))
      then true
      else
        (bif (b__0 == (0b01100 : (BitVec 5)))
        then true
        else
          (bif (b__0 == (0b01000 : (BitVec 5)))
          then true
          else
            (bif (b__0 == (0b10000 : (BitVec 5)))
            then true
            else
              (bif (b__0 == (0b10100 : (BitVec 5)))
              then true
              else
                (bif (b__0 == (0b11000 : (BitVec 5)))
                then true
                else
                  (bif (b__0 == (0b11100 : (BitVec 5)))
                  then true
                  else false))))))))

def amo_mnemonic_backwards (arg_ : String) : SailM amoop := do
  match arg_ with
  | "amoswap" => (pure AMOSWAP)
  | "amoadd" => (pure AMOADD)
  | "amoxor" => (pure AMOXOR)
  | "amoand" => (pure AMOAND)
  | "amoor" => (pure AMOOR)
  | "amomin" => (pure AMOMIN)
  | "amomax" => (pure AMOMAX)
  | "amominu" => (pure AMOMINU)
  | "amomaxu" => (pure AMOMAXU)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def amo_mnemonic_forwards_matches (arg_ : amoop) : Bool :=
  match arg_ with
  | AMOSWAP => true
  | AMOADD => true
  | AMOXOR => true
  | AMOAND => true
  | AMOOR => true
  | AMOMIN => true
  | AMOMAX => true
  | AMOMINU => true
  | AMOMAXU => true

def amo_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "amoswap" => true
  | "amoadd" => true
  | "amoxor" => true
  | "amoand" => true
  | "amoor" => true
  | "amomin" => true
  | "amomax" => true
  | "amominu" => true
  | "amomaxu" => true
  | _ => false

