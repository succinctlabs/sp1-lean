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

def encdec_rivvfunct6_forwards (arg_ : rivvfunct6) : (BitVec 6) :=
  match arg_ with
  | IVV_VWREDSUMU => (0b110000 : (BitVec 6))
  | IVV_VWREDSUM => (0b110001 : (BitVec 6))

def encdec_rivvfunct6_backwards (arg_ : (BitVec 6)) : SailM rivvfunct6 := do
  let b__0 := arg_
  if ((b__0 == (0b110000 : (BitVec 6))) : Bool)
  then (pure IVV_VWREDSUMU)
  else
    (do
      if ((b__0 == (0b110001 : (BitVec 6))) : Bool)
      then (pure IVV_VWREDSUM)
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def encdec_rivvfunct6_forwards_matches (arg_ : rivvfunct6) : Bool :=
  match arg_ with
  | IVV_VWREDSUMU => true
  | IVV_VWREDSUM => true

def encdec_rivvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b110000 : (BitVec 6))) : Bool)
  then true
  else
    (if ((b__0 == (0b110001 : (BitVec 6))) : Bool)
    then true
    else false)

def rivvtype_mnemonic_backwards (arg_ : String) : SailM rivvfunct6 := do
  match arg_ with
  | "vwredsumu.vs" => (pure IVV_VWREDSUMU)
  | "vwredsum.vs" => (pure IVV_VWREDSUM)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rivvtype_mnemonic_forwards_matches (arg_ : rivvfunct6) : Bool :=
  match arg_ with
  | IVV_VWREDSUMU => true
  | IVV_VWREDSUM => true

def rivvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwredsumu.vs" => true
  | "vwredsum.vs" => true
  | _ => false

def encdec_rmvvfunct6_forwards (arg_ : rmvvfunct6) : (BitVec 6) :=
  match arg_ with
  | MVV_VREDSUM => (0b000000 : (BitVec 6))
  | MVV_VREDAND => (0b000001 : (BitVec 6))
  | MVV_VREDOR => (0b000010 : (BitVec 6))
  | MVV_VREDXOR => (0b000011 : (BitVec 6))
  | MVV_VREDMINU => (0b000100 : (BitVec 6))
  | MVV_VREDMIN => (0b000101 : (BitVec 6))
  | MVV_VREDMAXU => (0b000110 : (BitVec 6))
  | MVV_VREDMAX => (0b000111 : (BitVec 6))

def encdec_rmvvfunct6_backwards (arg_ : (BitVec 6)) : SailM rmvvfunct6 := do
  let b__0 := arg_
  if ((b__0 == (0b000000 : (BitVec 6))) : Bool)
  then (pure MVV_VREDSUM)
  else
    (do
      if ((b__0 == (0b000001 : (BitVec 6))) : Bool)
      then (pure MVV_VREDAND)
      else
        (do
          if ((b__0 == (0b000010 : (BitVec 6))) : Bool)
          then (pure MVV_VREDOR)
          else
            (do
              if ((b__0 == (0b000011 : (BitVec 6))) : Bool)
              then (pure MVV_VREDXOR)
              else
                (do
                  if ((b__0 == (0b000100 : (BitVec 6))) : Bool)
                  then (pure MVV_VREDMINU)
                  else
                    (do
                      if ((b__0 == (0b000101 : (BitVec 6))) : Bool)
                      then (pure MVV_VREDMIN)
                      else
                        (do
                          if ((b__0 == (0b000110 : (BitVec 6))) : Bool)
                          then (pure MVV_VREDMAXU)
                          else
                            (do
                              if ((b__0 == (0b000111 : (BitVec 6))) : Bool)
                              then (pure MVV_VREDMAX)
                              else
                                (do
                                  assert false "Pattern match failure at unknown location"
                                  throw Error.Exit))))))))

def encdec_rmvvfunct6_forwards_matches (arg_ : rmvvfunct6) : Bool :=
  match arg_ with
  | MVV_VREDSUM => true
  | MVV_VREDAND => true
  | MVV_VREDOR => true
  | MVV_VREDXOR => true
  | MVV_VREDMINU => true
  | MVV_VREDMIN => true
  | MVV_VREDMAXU => true
  | MVV_VREDMAX => true

def encdec_rmvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000000 : (BitVec 6))) : Bool)
  then true
  else
    (if ((b__0 == (0b000001 : (BitVec 6))) : Bool)
    then true
    else
      (if ((b__0 == (0b000010 : (BitVec 6))) : Bool)
      then true
      else
        (if ((b__0 == (0b000011 : (BitVec 6))) : Bool)
        then true
        else
          (if ((b__0 == (0b000100 : (BitVec 6))) : Bool)
          then true
          else
            (if ((b__0 == (0b000101 : (BitVec 6))) : Bool)
            then true
            else
              (if ((b__0 == (0b000110 : (BitVec 6))) : Bool)
              then true
              else
                (if ((b__0 == (0b000111 : (BitVec 6))) : Bool)
                then true
                else false)))))))

def rmvvtype_mnemonic_backwards (arg_ : String) : SailM rmvvfunct6 := do
  match arg_ with
  | "vredsum.vs" => (pure MVV_VREDSUM)
  | "vredand.vs" => (pure MVV_VREDAND)
  | "vredor.vs" => (pure MVV_VREDOR)
  | "vredxor.vs" => (pure MVV_VREDXOR)
  | "vredminu.vs" => (pure MVV_VREDMINU)
  | "vredmin.vs" => (pure MVV_VREDMIN)
  | "vredmaxu.vs" => (pure MVV_VREDMAXU)
  | "vredmax.vs" => (pure MVV_VREDMAX)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rmvvtype_mnemonic_forwards_matches (arg_ : rmvvfunct6) : Bool :=
  match arg_ with
  | MVV_VREDSUM => true
  | MVV_VREDAND => true
  | MVV_VREDOR => true
  | MVV_VREDXOR => true
  | MVV_VREDMINU => true
  | MVV_VREDMIN => true
  | MVV_VREDMAXU => true
  | MVV_VREDMAX => true

def rmvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vredsum.vs" => true
  | "vredand.vs" => true
  | "vredor.vs" => true
  | "vredxor.vs" => true
  | "vredminu.vs" => true
  | "vredmin.vs" => true
  | "vredmaxu.vs" => true
  | "vredmax.vs" => true
  | _ => false

