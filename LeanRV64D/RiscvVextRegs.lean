import LeanRV64D.Prelude
import LeanRV64D.RiscvVlen
import LeanRV64D.RiscvExtensions
import LeanRV64D.RiscvTypes
import LeanRV64D.RiscvCallbacks
import LeanRV64D.RiscvSysRegs

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
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def vregidx_to_vregno (app_0 : vregidx) : vregno :=
  let .Vregidx b := app_0
  (Vregno (BitVec.toNat b))

def vregno_to_vregidx (app_0 : vregno) : vregidx :=
  let .Vregno b := app_0
  (Vregidx (to_bits (l := 5) b))

def vregidx_bits (app_0 : vregidx) : (BitVec 5) :=
  let .Vregidx b := app_0
  b

def encdec_vreg_forwards (arg_ : vregidx) : (BitVec 5) :=
  match arg_ with
  | .Vregidx r => r

def encdec_vreg_backwards (arg_ : (BitVec 5)) : vregidx :=
  match arg_ with
  | r => (Vregidx r)

def encdec_vreg_forwards_matches (arg_ : vregidx) : Bool :=
  match arg_ with
  | .Vregidx r => true

def encdec_vreg_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | r => true

def vreg_write_callback (x_0 : vregidx) (x_1 : (BitVec (2 ^ 8))) : Unit :=
  ()

def zvreg : vregidx := (Vregidx (0b00000 : (BitVec 5)))

def vreg_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "v0" => (pure (0b00000 : (BitVec 5)))
  | "v1" => (pure (0b00001 : (BitVec 5)))
  | "v2" => (pure (0b00010 : (BitVec 5)))
  | "v3" => (pure (0b00011 : (BitVec 5)))
  | "v4" => (pure (0b00100 : (BitVec 5)))
  | "v5" => (pure (0b00101 : (BitVec 5)))
  | "v6" => (pure (0b00110 : (BitVec 5)))
  | "v7" => (pure (0b00111 : (BitVec 5)))
  | "v8" => (pure (0b01000 : (BitVec 5)))
  | "v9" => (pure (0b01001 : (BitVec 5)))
  | "v10" => (pure (0b01010 : (BitVec 5)))
  | "v11" => (pure (0b01011 : (BitVec 5)))
  | "v12" => (pure (0b01100 : (BitVec 5)))
  | "v13" => (pure (0b01101 : (BitVec 5)))
  | "v14" => (pure (0b01110 : (BitVec 5)))
  | "v15" => (pure (0b01111 : (BitVec 5)))
  | "v16" => (pure (0b10000 : (BitVec 5)))
  | "v17" => (pure (0b10001 : (BitVec 5)))
  | "v18" => (pure (0b10010 : (BitVec 5)))
  | "v19" => (pure (0b10011 : (BitVec 5)))
  | "v20" => (pure (0b10100 : (BitVec 5)))
  | "v21" => (pure (0b10101 : (BitVec 5)))
  | "v22" => (pure (0b10110 : (BitVec 5)))
  | "v23" => (pure (0b10111 : (BitVec 5)))
  | "v24" => (pure (0b11000 : (BitVec 5)))
  | "v25" => (pure (0b11001 : (BitVec 5)))
  | "v26" => (pure (0b11010 : (BitVec 5)))
  | "v27" => (pure (0b11011 : (BitVec 5)))
  | "v28" => (pure (0b11100 : (BitVec 5)))
  | "v29" => (pure (0b11101 : (BitVec 5)))
  | "v30" => (pure (0b11110 : (BitVec 5)))
  | "v31" => (pure (0b11111 : (BitVec 5)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vreg_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b00000 : (BitVec 5))) : Bool)
  then true
  else
    (if ((b__0 == (0b00001 : (BitVec 5))) : Bool)
    then true
    else
      (if ((b__0 == (0b00010 : (BitVec 5))) : Bool)
      then true
      else
        (if ((b__0 == (0b00011 : (BitVec 5))) : Bool)
        then true
        else
          (if ((b__0 == (0b00100 : (BitVec 5))) : Bool)
          then true
          else
            (if ((b__0 == (0b00101 : (BitVec 5))) : Bool)
            then true
            else
              (if ((b__0 == (0b00110 : (BitVec 5))) : Bool)
              then true
              else
                (if ((b__0 == (0b00111 : (BitVec 5))) : Bool)
                then true
                else
                  (if ((b__0 == (0b01000 : (BitVec 5))) : Bool)
                  then true
                  else
                    (if ((b__0 == (0b01001 : (BitVec 5))) : Bool)
                    then true
                    else
                      (if ((b__0 == (0b01010 : (BitVec 5))) : Bool)
                      then true
                      else
                        (if ((b__0 == (0b01011 : (BitVec 5))) : Bool)
                        then true
                        else
                          (if ((b__0 == (0b01100 : (BitVec 5))) : Bool)
                          then true
                          else
                            (if ((b__0 == (0b01101 : (BitVec 5))) : Bool)
                            then true
                            else
                              (if ((b__0 == (0b01110 : (BitVec 5))) : Bool)
                              then true
                              else
                                (if ((b__0 == (0b01111 : (BitVec 5))) : Bool)
                                then true
                                else
                                  (if ((b__0 == (0b10000 : (BitVec 5))) : Bool)
                                  then true
                                  else
                                    (if ((b__0 == (0b10001 : (BitVec 5))) : Bool)
                                    then true
                                    else
                                      (if ((b__0 == (0b10010 : (BitVec 5))) : Bool)
                                      then true
                                      else
                                        (if ((b__0 == (0b10011 : (BitVec 5))) : Bool)
                                        then true
                                        else
                                          (if ((b__0 == (0b10100 : (BitVec 5))) : Bool)
                                          then true
                                          else
                                            (if ((b__0 == (0b10101 : (BitVec 5))) : Bool)
                                            then true
                                            else
                                              (if ((b__0 == (0b10110 : (BitVec 5))) : Bool)
                                              then true
                                              else
                                                (if ((b__0 == (0b10111 : (BitVec 5))) : Bool)
                                                then true
                                                else
                                                  (if ((b__0 == (0b11000 : (BitVec 5))) : Bool)
                                                  then true
                                                  else
                                                    (if ((b__0 == (0b11001 : (BitVec 5))) : Bool)
                                                    then true
                                                    else
                                                      (if ((b__0 == (0b11010 : (BitVec 5))) : Bool)
                                                      then true
                                                      else
                                                        (if ((b__0 == (0b11011 : (BitVec 5))) : Bool)
                                                        then true
                                                        else
                                                          (if ((b__0 == (0b11100 : (BitVec 5))) : Bool)
                                                          then true
                                                          else
                                                            (if ((b__0 == (0b11101 : (BitVec 5))) : Bool)
                                                            then true
                                                            else
                                                              (if ((b__0 == (0b11110 : (BitVec 5))) : Bool)
                                                              then true
                                                              else
                                                                (if ((b__0 == (0b11111 : (BitVec 5))) : Bool)
                                                                then true
                                                                else false)))))))))))))))))))))))))))))))

def vreg_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "v0" => true
  | "v1" => true
  | "v2" => true
  | "v3" => true
  | "v4" => true
  | "v5" => true
  | "v6" => true
  | "v7" => true
  | "v8" => true
  | "v9" => true
  | "v10" => true
  | "v11" => true
  | "v12" => true
  | "v13" => true
  | "v14" => true
  | "v15" => true
  | "v16" => true
  | "v17" => true
  | "v18" => true
  | "v19" => true
  | "v20" => true
  | "v21" => true
  | "v22" => true
  | "v23" => true
  | "v24" => true
  | "v25" => true
  | "v26" => true
  | "v27" => true
  | "v28" => true
  | "v29" => true
  | "v30" => true
  | "v31" => true
  | _ => false

def vreg_name_backwards (arg_ : String) : SailM vregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((vreg_name_raw_backwards_matches mapping0_) : Bool)
    then
      (do
        match (← (vreg_name_raw_backwards mapping0_)) with
        | i => (pure (some (Vregidx i))))
    else (pure none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vreg_name_forwards_matches (arg_ : vregidx) : Bool :=
  match arg_ with
  | .Vregidx i => true

def vreg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((vreg_name_raw_backwards_matches mapping0_) : Bool)
    then
      (do
        match (← (vreg_name_raw_backwards mapping0_)) with
        | i => (pure (some true)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def rV (app_0 : vregno) : SailM (BitVec (2 ^ 8)) := do
  let .Vregno r := app_0
  match r with
  | 0 => readReg vr0
  | 1 => readReg vr1
  | 2 => readReg vr2
  | 3 => readReg vr3
  | 4 => readReg vr4
  | 5 => readReg vr5
  | 6 => readReg vr6
  | 7 => readReg vr7
  | 8 => readReg vr8
  | 9 => readReg vr9
  | 10 => readReg vr10
  | 11 => readReg vr11
  | 12 => readReg vr12
  | 13 => readReg vr13
  | 14 => readReg vr14
  | 15 => readReg vr15
  | 16 => readReg vr16
  | 17 => readReg vr17
  | 18 => readReg vr18
  | 19 => readReg vr19
  | 20 => readReg vr20
  | 21 => readReg vr21
  | 22 => readReg vr22
  | 23 => readReg vr23
  | 24 => readReg vr24
  | 25 => readReg vr25
  | 26 => readReg vr26
  | 27 => readReg vr27
  | 28 => readReg vr28
  | 29 => readReg vr29
  | 30 => readReg vr30
  | _ => readReg vr31

def dirty_v_context (_ : Unit) : SailM Unit := do
  assert (hartSupports Ext_V) "riscv_vext_regs.sail:138.28-138.29"
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 10 9 (extStatus_to_bits Dirty))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) (64 -i 1) (64 -i 1)
    (0b1 : (BitVec 1)))
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))

def wV (typ_0 : vregno) (v : (BitVec (2 ^ 8))) : SailM Unit := do
  let .Vregno r : vregno := typ_0
  match r with
  | 0 => writeReg vr0 v
  | 1 => writeReg vr1 v
  | 2 => writeReg vr2 v
  | 3 => writeReg vr3 v
  | 4 => writeReg vr4 v
  | 5 => writeReg vr5 v
  | 6 => writeReg vr6 v
  | 7 => writeReg vr7 v
  | 8 => writeReg vr8 v
  | 9 => writeReg vr9 v
  | 10 => writeReg vr10 v
  | 11 => writeReg vr11 v
  | 12 => writeReg vr12 v
  | 13 => writeReg vr13 v
  | 14 => writeReg vr14 v
  | 15 => writeReg vr15 v
  | 16 => writeReg vr16 v
  | 17 => writeReg vr17 v
  | 18 => writeReg vr18 v
  | 19 => writeReg vr19 v
  | 20 => writeReg vr20 v
  | 21 => writeReg vr21 v
  | 22 => writeReg vr22 v
  | 23 => writeReg vr23 v
  | 24 => writeReg vr24 v
  | 25 => writeReg vr25 v
  | 26 => writeReg vr26 v
  | 27 => writeReg vr27 v
  | 28 => writeReg vr28 v
  | 29 => writeReg vr29 v
  | 30 => writeReg vr30 v
  | _ => writeReg vr31 v
  (dirty_v_context ())
  (pure (vreg_write_callback (vregno_to_vregidx (Vregno r)) v))

def rV_bits (i : vregidx) : SailM (BitVec (2 ^ 8)) := do
  (rV (vregidx_to_vregno i))

def wV_bits (i : vregidx) (data : (BitVec (2 ^ 8))) : SailM Unit := do
  (wV (vregidx_to_vregno i) data)

def init_vregs (_ : Unit) : SailM Unit := do
  let zero_vreg : vlenbits := (zeros (n := (2 ^i 8)))
  writeReg vr0 zero_vreg
  writeReg vr1 zero_vreg
  writeReg vr2 zero_vreg
  writeReg vr3 zero_vreg
  writeReg vr4 zero_vreg
  writeReg vr5 zero_vreg
  writeReg vr6 zero_vreg
  writeReg vr7 zero_vreg
  writeReg vr8 zero_vreg
  writeReg vr9 zero_vreg
  writeReg vr10 zero_vreg
  writeReg vr11 zero_vreg
  writeReg vr12 zero_vreg
  writeReg vr13 zero_vreg
  writeReg vr14 zero_vreg
  writeReg vr15 zero_vreg
  writeReg vr16 zero_vreg
  writeReg vr17 zero_vreg
  writeReg vr18 zero_vreg
  writeReg vr19 zero_vreg
  writeReg vr20 zero_vreg
  writeReg vr21 zero_vreg
  writeReg vr22 zero_vreg
  writeReg vr23 zero_vreg
  writeReg vr24 zero_vreg
  writeReg vr25 zero_vreg
  writeReg vr26 zero_vreg
  writeReg vr27 zero_vreg
  writeReg vr28 zero_vreg
  writeReg vr29 zero_vreg
  writeReg vr30 zero_vreg
  writeReg vr31 zero_vreg

def VLENB : xlenbits := (to_bits (l := 64) (Int.tdiv vlen 8))

def undefined_Vtype (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Vtype (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Vtype_reserved (v : (BitVec 64)) : (BitVec (64 - 9)) :=
  (Sail.BitVec.extractLsb v (64 -i 2) 8)

def _update_Vtype_reserved (v : (BitVec 64)) (x : (BitVec (64 - 9))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 2) 8 x)

def _update_PTE_Ext_reserved (v : (BitVec 10)) (x : (BitVec 7)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 6 0 x)

def _set_Vtype_reserved (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 9))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_reserved r v)

def _get_PTE_Ext_reserved (v : (BitVec 10)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 6 0)

def _set_PTE_Ext_reserved (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 7)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_reserved r v)

def _get_Vtype_vill (v : (BitVec 64)) : (BitVec (64 - 1 - (64 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (64 -i 1) (64 -i 1))

def _update_Vtype_vill (v : (BitVec 64)) (x : (BitVec (64 - 1 - (64 - 1) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) (64 -i 1) x)

def _set_Vtype_vill (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (64 - 1 - (64 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vill r v)

def _get_Vtype_vlmul (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_Vtype_vlmul (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _set_Vtype_vlmul (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vlmul r v)

def _get_Vtype_vma (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Vtype_vma (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Vtype_vma (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vma r v)

def _get_Vtype_vsew (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def _update_Vtype_vsew (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 3 x)

def _set_Vtype_vsew (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vsew r v)

def _get_Vtype_vta (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Vtype_vta (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Vtype_vta (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vta r v)

def sew_pow_val_forwards (arg_ : (BitVec 3)) : SailM Nat := do
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then (pure 3)
  else
    (do
      if ((b__0 == (0b001 : (BitVec 3))) : Bool)
      then (pure 4)
      else
        (do
          if ((b__0 == (0b010 : (BitVec 3))) : Bool)
          then (pure 5)
          else
            (do
              if ((b__0 == (0b011 : (BitVec 3))) : Bool)
              then (pure 6)
              else
                (do
                  assert false "Pattern match failure at unknown location"
                  throw Error.Exit))))

/-- Type quantifiers: arg_ : Nat, 3 ≤ arg_ ∧ arg_ ≤ 6 -/
def sew_pow_val_backwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 3 => (0b000 : (BitVec 3))
  | 4 => (0b001 : (BitVec 3))
  | 5 => (0b010 : (BitVec 3))
  | _ => (0b011 : (BitVec 3))

def sew_pow_val_forwards_matches (arg_ : (BitVec 3)) : Bool :=
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
        else false)))

/-- Type quantifiers: arg_ : Nat, 3 ≤ arg_ ∧ arg_ ≤ 6 -/
def sew_pow_val_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | _ => false

def lmul_pow_val_forwards (arg_ : (BitVec 3)) : SailM Int := do
  let b__0 := arg_
  if ((b__0 == (0b101 : (BitVec 3))) : Bool)
  then (pure (-3))
  else
    (do
      if ((b__0 == (0b110 : (BitVec 3))) : Bool)
      then (pure (-2))
      else
        (do
          if ((b__0 == (0b111 : (BitVec 3))) : Bool)
          then (pure (-1))
          else
            (do
              if ((b__0 == (0b000 : (BitVec 3))) : Bool)
              then (pure 0)
              else
                (do
                  if ((b__0 == (0b001 : (BitVec 3))) : Bool)
                  then (pure 1)
                  else
                    (do
                      if ((b__0 == (0b010 : (BitVec 3))) : Bool)
                      then (pure 2)
                      else
                        (do
                          if ((b__0 == (0b011 : (BitVec 3))) : Bool)
                          then (pure 3)
                          else
                            (do
                              assert false "Pattern match failure at unknown location"
                              throw Error.Exit)))))))

/-- Type quantifiers: arg_ : Int, (-3) ≤ arg_ ∧ arg_ ≤ 3 -/
def lmul_pow_val_backwards (arg_ : Int) : (BitVec 3) :=
  match arg_ with
  | (-3) => (0b101 : (BitVec 3))
  | (-2) => (0b110 : (BitVec 3))
  | (-1) => (0b111 : (BitVec 3))
  | 0 => (0b000 : (BitVec 3))
  | 1 => (0b001 : (BitVec 3))
  | 2 => (0b010 : (BitVec 3))
  | _ => (0b011 : (BitVec 3))

def lmul_pow_val_forwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b101 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b110 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b111 : (BitVec 3))) : Bool)
      then true
      else
        (if ((b__0 == (0b000 : (BitVec 3))) : Bool)
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
              else false))))))

/-- Type quantifiers: arg_ : Int, (-3) ≤ arg_ ∧ arg_ ≤ 3 -/
def lmul_pow_val_backwards_matches (arg_ : Int) : Bool :=
  match arg_ with
  | (-3) => true
  | (-2) => true
  | (-1) => true
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | _ => false

def is_invalid_sew_pow (v : (BitVec 3)) : Bool :=
  (zopz0zK_u v (0b011 : (BitVec 3)))

def is_invalid_lmul_pow (v : (BitVec 3)) : Bool :=
  (v == (0b100 : (BitVec 3)))

def get_sew_pow (_ : Unit) : SailM Nat := do
  let sew_pow ← do (pure (_get_Vtype_vsew (← readReg vtype)))
  (sew_pow_val_forwards sew_pow)

def get_sew (_ : Unit) : SailM Int := do
  (pure (2 ^i (← (get_sew_pow ()))))

def get_sew_bytes (_ : Unit) : SailM Int := do
  (pure (Int.tdiv (← (get_sew ())) 8))

def get_lmul_pow (_ : Unit) : SailM Int := do
  let lmul_pow ← do (pure (_get_Vtype_vlmul (← readReg vtype)))
  (lmul_pow_val_forwards lmul_pow)

def undefined_agtype (_ : Unit) : SailM agtype := do
  (internal_pick [UNDISTURBED, AGNOSTIC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def agtype_of_num (arg_ : Nat) : agtype :=
  match arg_ with
  | 0 => UNDISTURBED
  | _ => AGNOSTIC

def num_of_agtype (arg_ : agtype) : Int :=
  match arg_ with
  | UNDISTURBED => 0
  | AGNOSTIC => 1

def decode_agtype (ag : (BitVec 1)) : agtype :=
  let b__0 := ag
  if ((b__0 == (0b0 : (BitVec 1))) : Bool)
  then UNDISTURBED
  else AGNOSTIC

def get_vtype_vma (_ : Unit) : SailM agtype := do
  (pure (decode_agtype (_get_Vtype_vma (← readReg vtype))))

def get_vtype_vta (_ : Unit) : SailM agtype := do
  (pure (decode_agtype (_get_Vtype_vta (← readReg vtype))))

def undefined_Vcsr (_ : Unit) : SailM (BitVec 3) := do
  (undefined_bitvector 3)

def Mk_Vcsr (v : (BitVec 3)) : (BitVec 3) :=
  v

def _get_Vcsr_vxrm (v : (BitVec 3)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)

def _update_Vcsr_vxrm (v : (BitVec 3)) (x : (BitVec 2)) : (BitVec 3) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _set_Vcsr_vxrm (r_ref : (RegisterRef (BitVec 3))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vcsr_vxrm r v)

def _get_Vcsr_vxsat (v : (BitVec 3)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Vcsr_vxsat (v : (BitVec 3)) (x : (BitVec 1)) : (BitVec 3) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Vcsr_vxsat (r_ref : (RegisterRef (BitVec 3))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vcsr_vxsat r v)

def set_vstart (value : (BitVec 16)) : SailM Unit := do
  (dirty_v_context ())
  writeReg vstart (zero_extend (m := 64) (Sail.BitVec.extractLsb value (vlen_exp -i 1) 0))
  (csr_name_write_callback "vstart" (← readReg vstart))

def ext_write_vcsr (vxrm_val : (BitVec 2)) (vxsat_val : (BitVec 1)) : SailM Unit := do
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 vxrm_val)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 vxsat_val)
  (dirty_v_context ())

