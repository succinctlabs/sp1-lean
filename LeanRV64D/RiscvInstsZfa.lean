import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvInstsFext
import LeanRV64D.RiscvInstsDext

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

def fcvtmod_helper (x64 : (BitVec 64)) : ((BitVec 5) × (BitVec 32)) :=
  let (sign, exp, mant) := (fsplit_D x64)
  let is_subnorm := ((exp == (zeros (n := 11))) && (mant != (zeros (n := 52))))
  let is_zero := ((exp == (zeros (n := 11))) && (mant == (zeros (n := 52))))
  let is_nan_or_inf := (exp == (ones (n := 11)))
  let true_mant := ((0b1 : (BitVec 1)) ++ mant)
  let true_exp := ((BitVec.toNat exp) -i 1023)
  let is_too_large := (true_exp ≥b 84)
  let is_too_small := (true_exp <b 0)
  if (is_zero : Bool)
  then ((zeros (n := 5)), (zeros (n := 32)))
  else
    (if (is_subnorm : Bool)
    then ((nxFlag ()), (zeros (n := 32)))
    else
      (if (is_nan_or_inf : Bool)
      then ((nvFlag ()), (zeros (n := 32)))
      else
        (if (is_too_large : Bool)
        then ((nvFlag ()), (zeros (n := 32)))
        else
          (if (is_too_small : Bool)
          then ((nxFlag ()), (zeros (n := 32)))
          else
            (let fixedpoint : (BitVec 84) := (shiftl (zero_extend (m := 84) true_mant) true_exp)
            let integer := (Sail.BitVec.extractLsb fixedpoint 83 52)
            let fractional := (Sail.BitVec.extractLsb fixedpoint 51 0)
            let result :=
              if ((sign == (0b1 : (BitVec 1))) : Bool)
              then (BitVec.addInt (Complement.complement integer) 1)
              else integer
            let max_integer :=
              if ((sign == (0b1 : (BitVec 1))) : Bool)
              then (BitVec.toNat (0x80000000 : (BitVec 32)))
              else (BitVec.toNat (0x7FFFFFFF : (BitVec 32)))
            let flags : (BitVec 5) :=
              if ((true_exp >b 31) : Bool)
              then (nvFlag ())
              else
                (if (((BitVec.toNat integer) >b max_integer) : Bool)
                then (nvFlag ())
                else
                  (if ((fractional != (zeros (n := ((51 -i 0) +i 1)))) : Bool)
                  then (nxFlag ())
                  else (zeros (n := 5))))
            (flags, result))))))

