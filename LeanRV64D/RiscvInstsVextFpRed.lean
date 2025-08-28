import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvErrors
import LeanRV64D.RiscvFdextRegs
import LeanRV64D.RiscvVextRegs
import LeanRV64D.RiscvVextControl
import LeanRV64D.RiscvInstRetire
import LeanRV64D.RiscvInstsVextUtils
import LeanRV64D.RiscvInstsVextFpUtils

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

def encdec_rfvvfunct6_forwards (arg_ : rfvvfunct6) : (BitVec 6) :=
  match arg_ with
  | FVV_VFREDOSUM => (0b000011 : (BitVec 6))
  | FVV_VFREDUSUM => (0b000001 : (BitVec 6))
  | FVV_VFREDMAX => (0b000111 : (BitVec 6))
  | FVV_VFREDMIN => (0b000101 : (BitVec 6))
  | FVV_VFWREDOSUM => (0b110011 : (BitVec 6))
  | FVV_VFWREDUSUM => (0b110001 : (BitVec 6))

def encdec_rfvvfunct6_backwards (arg_ : (BitVec 6)) : SailM rfvvfunct6 := do
  let b__0 := arg_
  if ((b__0 == (0b000011 : (BitVec 6))) : Bool)
  then (pure FVV_VFREDOSUM)
  else
    (do
      if ((b__0 == (0b000001 : (BitVec 6))) : Bool)
      then (pure FVV_VFREDUSUM)
      else
        (do
          if ((b__0 == (0b000111 : (BitVec 6))) : Bool)
          then (pure FVV_VFREDMAX)
          else
            (do
              if ((b__0 == (0b000101 : (BitVec 6))) : Bool)
              then (pure FVV_VFREDMIN)
              else
                (do
                  if ((b__0 == (0b110011 : (BitVec 6))) : Bool)
                  then (pure FVV_VFWREDOSUM)
                  else
                    (do
                      if ((b__0 == (0b110001 : (BitVec 6))) : Bool)
                      then (pure FVV_VFWREDUSUM)
                      else
                        (do
                          assert false "Pattern match failure at unknown location"
                          throw Error.Exit))))))

def encdec_rfvvfunct6_forwards_matches (arg_ : rfvvfunct6) : Bool :=
  match arg_ with
  | FVV_VFREDOSUM => true
  | FVV_VFREDUSUM => true
  | FVV_VFREDMAX => true
  | FVV_VFREDMIN => true
  | FVV_VFWREDOSUM => true
  | FVV_VFWREDUSUM => true

def encdec_rfvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000011 : (BitVec 6))) : Bool)
  then true
  else
    (if ((b__0 == (0b000001 : (BitVec 6))) : Bool)
    then true
    else
      (if ((b__0 == (0b000111 : (BitVec 6))) : Bool)
      then true
      else
        (if ((b__0 == (0b000101 : (BitVec 6))) : Bool)
        then true
        else
          (if ((b__0 == (0b110011 : (BitVec 6))) : Bool)
          then true
          else
            (if ((b__0 == (0b110001 : (BitVec 6))) : Bool)
            then true
            else false)))))

/-- Type quantifiers: LMUL_pow : Int, SEW : Nat, num_elem_vs : Nat, num_elem_vs > 0, SEW ∈
  {8, 16, 32, 64}, (-3) ≤ LMUL_pow ∧ LMUL_pow ≤ 3 -/
def process_rfvv_single (funct6 : rfvvfunct6) (vm : (BitVec 1)) (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) (num_elem_vs : Nat) (SEW : Nat) (LMUL_pow : Int) : SailM ExecutionResult := SailME.run do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let num_elem_vd ← do (get_num_elem 0 SEW)
  if ((← (illegal_fp_reduction SEW rm_3b)) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      assert (SEW != 8) "riscv_insts_vext_fp_red.sail:36.17-36.18"
      if (((BitVec.toNat (← readReg vl)) == 0) : Bool)
      then (pure RETIRE_SUCCESS)
      else
        (do
          let n := num_elem_vs
          let d := num_elem_vd
          let m := SEW
          let vm_val ← (( do (read_vmask num_elem_vs vm zvreg) ) : SailME ExecutionResult
            (BitVec n) )
          let vd_val ← (( do (read_vreg num_elem_vd SEW 0 vd) ) : SailME ExecutionResult
            (Vector (BitVec m) d) )
          let vs2_val ← (( do (read_vreg num_elem_vs SEW LMUL_pow vs2) ) : SailME ExecutionResult
            (Vector (BitVec m) n) )
          let mask ← (( do
            match (← (init_masked_source num_elem_vs LMUL_pow vm_val)) with
            | .Ok v => (pure v)
            | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
            ExecutionResult (BitVec n) )
          let sum ← (( do (read_single_element SEW 0 vs1) ) : SailME ExecutionResult (BitVec m) )
          let sum ← (( do
            let loop_i_lower := 0
            let loop_i_upper := (num_elem_vs -i 1)
            let mut loop_vars := sum
            for i in [loop_i_lower:loop_i_upper:1]i do
              let sum := loop_vars
              loop_vars ← do
                if (((BitVec.access mask i) == 1#1) : Bool)
                then
                  (do
                    match funct6 with
                    | FVV_VFREDOSUM => (fp_add rm_3b sum (GetElem?.getElem! vs2_val i))
                    | FVV_VFREDUSUM => (fp_add rm_3b sum (GetElem?.getElem! vs2_val i))
                    | FVV_VFREDMAX => (fp_max sum (GetElem?.getElem! vs2_val i))
                    | FVV_VFREDMIN => (fp_min sum (GetElem?.getElem! vs2_val i))
                    | _ =>
                      (internal_error "riscv_insts_vext_fp_red.sail" 61 "Widening op unexpected"))
                else (pure sum)
            (pure loop_vars) ) : SailME ExecutionResult (BitVec m) )
          (write_single_element SEW 0 vd sum)
          (set_vstart (zeros (n := 16)))
          (pure RETIRE_SUCCESS)))

/-- Type quantifiers: LMUL_pow : Int, SEW : Nat, num_elem_vs : Nat, num_elem_vs > 0, SEW ∈
  {8, 16, 32, 64}, (-3) ≤ LMUL_pow ∧ LMUL_pow ≤ 3 -/
def process_rfvv_widening_reduction (funct6 : rfvvfunct6) (vm : (BitVec 1)) (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) (num_elem_vs : Nat) (SEW : Nat) (LMUL_pow : Int) : SailM ExecutionResult := SailME.run do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let SEW_widen := (SEW *i 2)
  if ((← (illegal_fp_widening_reduction SEW rm_3b SEW_widen)) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      assert ((SEW ≥b 16) && (SEW_widen ≤b 64)) "riscv_insts_vext_fp_red.sail:79.36-79.37"
      let num_elem_vd ← do (get_num_elem 0 SEW_widen)
      if (((BitVec.toNat (← readReg vl)) == 0) : Bool)
      then (pure RETIRE_SUCCESS)
      else
        (do
          let n := num_elem_vs
          let d := num_elem_vd
          let m := SEW
          let o := SEW_widen
          let vm_val ← (( do (read_vmask num_elem_vs vm zvreg) ) : SailME ExecutionResult
            (BitVec n) )
          let vd_val ← (( do (read_vreg num_elem_vd SEW_widen 0 vd) ) : SailME ExecutionResult
            (Vector (BitVec o) d) )
          let vs2_val ← (( do (read_vreg num_elem_vs SEW LMUL_pow vs2) ) : SailME ExecutionResult
            (Vector (BitVec m) n) )
          let mask ← (( do
            match (← (init_masked_source num_elem_vs LMUL_pow vm_val)) with
            | .Ok v => (pure v)
            | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
            ExecutionResult (BitVec n) )
          let sum ← (( do (read_single_element SEW_widen 0 vs1) ) : SailME ExecutionResult
            (BitVec o) )
          let sum ← (( do
            let loop_i_lower := 0
            let loop_i_upper := (num_elem_vs -i 1)
            let mut loop_vars := sum
            for i in [loop_i_lower:loop_i_upper:1]i do
              let sum := loop_vars
              loop_vars ← do
                if (((BitVec.access mask i) == 1#1) : Bool)
                then
                  (do
                    (fp_add rm_3b sum (← (fp_widen (GetElem?.getElem! vs2_val i)))))
                else (pure sum)
            (pure loop_vars) ) : SailME ExecutionResult (BitVec o) )
          (write_single_element SEW_widen 0 vd sum)
          (set_vstart (zeros (n := 16)))
          (pure RETIRE_SUCCESS)))

def rfvvtype_mnemonic_backwards (arg_ : String) : SailM rfvvfunct6 := do
  match arg_ with
  | "vfredosum.vs" => (pure FVV_VFREDOSUM)
  | "vfredusum.vs" => (pure FVV_VFREDUSUM)
  | "vfredmax.vs" => (pure FVV_VFREDMAX)
  | "vfredmin.vs" => (pure FVV_VFREDMIN)
  | "vfwredosum.vs" => (pure FVV_VFWREDOSUM)
  | "vfwredusum.vs" => (pure FVV_VFWREDUSUM)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rfvvtype_mnemonic_forwards_matches (arg_ : rfvvfunct6) : Bool :=
  match arg_ with
  | FVV_VFREDOSUM => true
  | FVV_VFREDUSUM => true
  | FVV_VFREDMAX => true
  | FVV_VFREDMIN => true
  | FVV_VFWREDOSUM => true
  | FVV_VFWREDUSUM => true

def rfvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfredosum.vs" => true
  | "vfredusum.vs" => true
  | "vfredmax.vs" => true
  | "vfredmin.vs" => true
  | "vfwredosum.vs" => true
  | "vfwredusum.vs" => true
  | _ => false

