import LeanRV64IM.Flow
import LeanRV64IM.Prelude
import LeanRV64IM.RiscvVlen
import LeanRV64IM.RiscvExtensions
import LeanRV64IM.RiscvTypes
import LeanRV64IM.RiscvCallbacks
import LeanRV64IM.RiscvSysRegs

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV64IM.Functions

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
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
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

def vregidx_to_vregno (app_0 : vregidx) : vregno :=
  let .Vregidx b := app_0
  (Vregno (BitVec.toNat b))

def vregno_to_vregidx (app_0 : vregno) : vregidx :=
  let .Vregno b := app_0
  (Vregidx (to_bits (l := 5) b))

def vregidx_offset (typ_0 : vregidx) (o : (BitVec 5)) : vregidx :=
  let .Vregidx r : vregidx := typ_0
  (Vregidx (r + o))

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

def vreg_write_callback (x_0 : vregidx) (x_1 : (BitVec 65536)) : Unit :=
  ()

def zvreg : vregidx := (Vregidx (0b00000 : (BitVec 5)))

def vreg_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  let b__0 := arg_
  if ((b__0 == (0b00000 : (BitVec 5))) : Bool)
  then "v0"
  else
    (if ((b__0 == (0b00001 : (BitVec 5))) : Bool)
    then "v1"
    else
      (if ((b__0 == (0b00010 : (BitVec 5))) : Bool)
      then "v2"
      else
        (if ((b__0 == (0b00011 : (BitVec 5))) : Bool)
        then "v3"
        else
          (if ((b__0 == (0b00100 : (BitVec 5))) : Bool)
          then "v4"
          else
            (if ((b__0 == (0b00101 : (BitVec 5))) : Bool)
            then "v5"
            else
              (if ((b__0 == (0b00110 : (BitVec 5))) : Bool)
              then "v6"
              else
                (if ((b__0 == (0b00111 : (BitVec 5))) : Bool)
                then "v7"
                else
                  (if ((b__0 == (0b01000 : (BitVec 5))) : Bool)
                  then "v8"
                  else
                    (if ((b__0 == (0b01001 : (BitVec 5))) : Bool)
                    then "v9"
                    else
                      (if ((b__0 == (0b01010 : (BitVec 5))) : Bool)
                      then "v10"
                      else
                        (if ((b__0 == (0b01011 : (BitVec 5))) : Bool)
                        then "v11"
                        else
                          (if ((b__0 == (0b01100 : (BitVec 5))) : Bool)
                          then "v12"
                          else
                            (if ((b__0 == (0b01101 : (BitVec 5))) : Bool)
                            then "v13"
                            else
                              (if ((b__0 == (0b01110 : (BitVec 5))) : Bool)
                              then "v14"
                              else
                                (if ((b__0 == (0b01111 : (BitVec 5))) : Bool)
                                then "v15"
                                else
                                  (if ((b__0 == (0b10000 : (BitVec 5))) : Bool)
                                  then "v16"
                                  else
                                    (if ((b__0 == (0b10001 : (BitVec 5))) : Bool)
                                    then "v17"
                                    else
                                      (if ((b__0 == (0b10010 : (BitVec 5))) : Bool)
                                      then "v18"
                                      else
                                        (if ((b__0 == (0b10011 : (BitVec 5))) : Bool)
                                        then "v19"
                                        else
                                          (if ((b__0 == (0b10100 : (BitVec 5))) : Bool)
                                          then "v20"
                                          else
                                            (if ((b__0 == (0b10101 : (BitVec 5))) : Bool)
                                            then "v21"
                                            else
                                              (if ((b__0 == (0b10110 : (BitVec 5))) : Bool)
                                              then "v22"
                                              else
                                                (if ((b__0 == (0b10111 : (BitVec 5))) : Bool)
                                                then "v23"
                                                else
                                                  (if ((b__0 == (0b11000 : (BitVec 5))) : Bool)
                                                  then "v24"
                                                  else
                                                    (if ((b__0 == (0b11001 : (BitVec 5))) : Bool)
                                                    then "v25"
                                                    else
                                                      (if ((b__0 == (0b11010 : (BitVec 5))) : Bool)
                                                      then "v26"
                                                      else
                                                        (if ((b__0 == (0b11011 : (BitVec 5))) : Bool)
                                                        then "v27"
                                                        else
                                                          (if ((b__0 == (0b11100 : (BitVec 5))) : Bool)
                                                          then "v28"
                                                          else
                                                            (if ((b__0 == (0b11101 : (BitVec 5))) : Bool)
                                                            then "v29"
                                                            else
                                                              (if ((b__0 == (0b11110 : (BitVec 5))) : Bool)
                                                              then "v30"
                                                              else "v31"))))))))))))))))))))))))))))))

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

def vreg_name_forwards (arg_ : vregidx) : String :=
  match arg_ with
  | .Vregidx i => (vreg_name_raw_forwards i)

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

def dirty_v_context (_ : Unit) : SailM Unit := do
  assert (hartSupports Ext_V) "model/riscv_vext_regs.sail:95.28-95.29"
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 10 9 (extStatus_to_bits Dirty))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) (64 -i 1) (64 -i 1)
    (0b1 : (BitVec 1)))
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))

def rV (app_0 : vregno) : SailM (BitVec 65536) := do
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

def wV (typ_0 : vregno) (v : (BitVec 65536)) : SailM Unit := do
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
  assert ((0 <b VLEN) && (VLEN ≤b 65536)) "model/riscv_vext_regs.sail:176.43-176.44"
  (pure (vreg_write_callback (vregno_to_vregidx (Vregno r)) v))

def rV_bits (i : vregidx) : SailM (BitVec 65536) := do
  (rV (vregidx_to_vregno i))

def wV_bits (i : vregidx) (data : (BitVec 65536)) : SailM Unit := do
  (wV (vregidx_to_vregno i) data)

def init_vregs (_ : Unit) : SailM Unit := do
  let zero_vreg : vregtype := (zeros (n := 65536))
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

def ext_write_vcsr (vxrm_val : (BitVec 2)) (vxsat_val : (BitVec 1)) : SailM Unit := do
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 vxrm_val)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 vxsat_val)
  (dirty_v_context ())

/-- Type quantifiers: SEW : Nat, LMUL_pow : Int, SEW ∈ {8, 16, 32, 64} -/
def get_num_elem (LMUL_pow : Int) (SEW : Nat) : SailM Int := do
  let LMUL_pow_reg :=
    if ((LMUL_pow <b 0) : Bool)
    then 0
    else LMUL_pow
  let num_elem := (Int.tdiv ((2 ^i LMUL_pow_reg) *i VLEN) SEW)
  assert (num_elem >b 0) "model/riscv_vext_regs.sail:246.21-246.22"
  (pure num_elem)

/-- Type quantifiers: num_elem : Nat, SEW : Nat, num_elem ≥ 0 ∧ is_sew_bitsize(SEW) -/
def read_single_vreg (num_elem : Nat) (SEW : Nat) (vrid : vregidx) : SailM (Vector (BitVec SEW) num_elem) := do
  let bv ← (( do (rV_bits vrid) ) : SailM vregtype )
  let result : (Vector (BitVec SEW) num_elem) := (vectorInit (zeros (n := SEW)))
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      let start_index := (i *i SEW)
      (vectorUpdate result i (BitVec.slice bv start_index SEW))
  (pure loop_vars)

/-- Type quantifiers: num_elem : Nat, SEW : Nat, num_elem ≥ 0 ∧ is_sew_bitsize(SEW) -/
def write_single_vreg (num_elem : Nat) (SEW : Nat) (vrid : vregidx) (v : (Vector (BitVec SEW) num_elem)) : SailM Unit := do
  let r : vregtype := (zeros (n := 65536))
  let r ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := r
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let r := loop_vars
      loop_vars :=
        let r : vregtype := (shiftl r SEW)
        (r ||| (zero_extend (m := 65536) (GetElem?.getElem! v i)))
    (pure loop_vars) ) : SailM (BitVec 65536) )
  (wV_bits vrid r)

/-- Type quantifiers: num_elem : Nat, SEW : Nat, LMUL_pow : Int, num_elem ≥ 0 ∧
  is_sew_bitsize(SEW) -/
def read_vreg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (vrid : vregidx) : SailM (Vector (BitVec SEW) num_elem) := do
  let vrid_val := (BitVec.toNat (vregidx_bits vrid))
  let result : (Vector (BitVec SEW) num_elem) := (vectorInit (zeros (n := SEW)))
  let LMUL_pow_reg :=
    if ((LMUL_pow <b 0) : Bool)
    then 0
    else LMUL_pow
  if (((vrid_val +i (2 ^i LMUL_pow_reg)) >b 32) : Bool)
  then
    (do
      assert false "invalid register group: vrid overflow the largest number"
      throw Error.Exit)
  else
    (do
      if (((Int.tmod vrid_val (2 ^i LMUL_pow_reg)) != 0) : Bool)
      then
        (do
          assert false "invalid register group: vrid is not a multiple of EMUL"
          throw Error.Exit)
      else
        (do
          if ((LMUL_pow <b 0) : Bool)
          then
            (do
              (read_single_vreg (Vector.length result) SEW vrid))
          else
            (do
              let num_elem_single := (Int.tdiv VLEN SEW)
              assert (num_elem_single ≥b 0) "model/riscv_vext_regs.sail:296.34-296.35"
              let loop_i_lmul_lower := 0
              let loop_i_lmul_upper := ((2 ^i LMUL_pow_reg) -i 1)
              let mut loop_vars := result
              for i_lmul in [loop_i_lmul_lower:loop_i_lmul_upper:1]i do
                let result := loop_vars
                loop_vars ← do
                  let r_start_i : Int := (i_lmul *i num_elem_single)
                  let r_end_i : Int := ((r_start_i +i num_elem_single) -i 1)
                  let vrid_lmul : vregidx := (vregidx_offset vrid (to_bits_unsafe (l := 5) i_lmul))
                  let single_result ← (( do (read_single_vreg num_elem_single SEW vrid_lmul) ) :
                    SailM (Vector (BitVec SEW) num_elem_single) )
                  let loop_r_i_lower := r_start_i
                  let loop_r_i_upper := r_end_i
                  let mut loop_vars_1 := result
                  for r_i in [loop_r_i_lower:loop_r_i_upper:1]i do
                    let result := loop_vars_1
                    loop_vars_1 ← do
                      let s_i : Int := (r_i -i r_start_i)
                      assert ((0 ≤b r_i) && (r_i <b num_elem)) "model/riscv_vext_regs.sail:304.42-304.43"
                      assert ((0 ≤b s_i) && (s_i <b num_elem_single)) "model/riscv_vext_regs.sail:305.50-305.51"
                      (pure (vectorUpdate result r_i (GetElem?.getElem! single_result s_i)))
                  (pure loop_vars_1)
              (pure loop_vars))))

/-- Type quantifiers: index : Nat, EEW : Nat, is_sew_bitsize(EEW), 0 ≤ index -/
def read_single_element (EEW : Nat) (index : Nat) (vrid : vregidx) : SailM (BitVec EEW) := do
  assert (VLEN ≥b EEW) "model/riscv_vext_regs.sail:318.20-318.21"
  let elem_per_reg := (Int.tdiv VLEN EEW)
  assert (elem_per_reg >b 0) "model/riscv_vext_regs.sail:320.26-320.27"
  let real_vrid : vregidx :=
    (vregidx_offset vrid (to_bits_unsafe (l := 5) (Int.tdiv index elem_per_reg)))
  let real_index : Int := (Int.tmod index elem_per_reg)
  let vrid_val ← (( do (read_single_vreg elem_per_reg EEW real_vrid) ) : SailM
    (Vector (BitVec EEW) elem_per_reg) )
  assert ((0 ≤b real_index) && (real_index <b elem_per_reg)) "model/riscv_vext_regs.sail:324.53-324.54"
  (pure (GetElem?.getElem! vrid_val real_index))

/-- Type quantifiers: num_elem : Nat, SEW : Nat, LMUL_pow : Int, num_elem ≥ 0 ∧
  is_sew_bitsize(SEW) -/
def write_vreg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (vrid : vregidx) (vec : (Vector (BitVec SEW) num_elem)) : SailM Unit := do
  let LMUL_pow_reg :=
    if ((LMUL_pow <b 0) : Bool)
    then 0
    else LMUL_pow
  let num_elem_single : Int := (Int.tdiv VLEN SEW)
  assert (num_elem_single ≥b 0) "model/riscv_vext_regs.sail:334.30-334.31"
  let loop_i_lmul_lower := 0
  let loop_i_lmul_upper := ((2 ^i LMUL_pow_reg) -i 1)
  let mut loop_vars := ()
  for i_lmul in [loop_i_lmul_lower:loop_i_lmul_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let single_vec : (Vector (BitVec SEW) num_elem_single) := (vectorInit (zeros (n := SEW)))
      let vrid_lmul : vregidx := (vregidx_offset vrid (to_bits_unsafe (l := 5) i_lmul))
      let r_start_i : Int := (i_lmul *i num_elem_single)
      let r_end_i : Int := ((r_start_i +i num_elem_single) -i 1)
      let single_vec ← (( do
        let loop_r_i_lower := r_start_i
        let loop_r_i_upper := r_end_i
        let mut loop_vars_1 := single_vec
        for r_i in [loop_r_i_lower:loop_r_i_upper:1]i do
          let single_vec := loop_vars_1
          loop_vars_1 ← do
            let s_i : Int := (r_i -i r_start_i)
            assert ((0 ≤b r_i) && (r_i <b num_elem)) "model/riscv_vext_regs.sail:342.38-342.39"
            assert ((0 ≤b s_i) && (s_i <b num_elem_single)) "model/riscv_vext_regs.sail:343.46-343.47"
            (pure (vectorUpdate single_vec s_i (GetElem?.getElem! vec r_i)))
        (pure loop_vars_1) ) : SailM (Vector (BitVec SEW) num_elem_single) )
      (write_single_vreg num_elem_single SEW vrid_lmul single_vec)
  (pure loop_vars)

/-- Type quantifiers: index : Nat, EEW : Nat, is_sew_bitsize(EEW), 0 ≤ index -/
def write_single_element (EEW : Nat) (index : Nat) (vrid : vregidx) (value : (BitVec EEW)) : SailM Unit := do
  let elem_per_reg := (Int.tdiv VLEN EEW)
  assert (elem_per_reg >b 0) "model/riscv_vext_regs.sail:354.26-354.27"
  let real_vrid : vregidx :=
    (vregidx_offset vrid (to_bits_unsafe (l := 5) (Int.tdiv index elem_per_reg)))
  let real_index : Int := (Int.tmod index elem_per_reg)
  let vrid_val ← (( do (read_single_vreg elem_per_reg EEW real_vrid) ) : SailM
    (Vector (BitVec EEW) elem_per_reg) )
  let r : vregtype := (zeros (n := 65536))
  let r ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (elem_per_reg -i 1)
    let mut loop_vars := r
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let r := loop_vars
      loop_vars :=
        let r : vregtype := (shiftl r EEW)
        if ((i == real_index) : Bool)
        then (r ||| (zero_extend (m := 65536) value))
        else (r ||| (zero_extend (m := 65536) (GetElem?.getElem! vrid_val i)))
    (pure loop_vars) ) : SailM (BitVec 65536) )
  (wV_bits real_vrid r)

/-- Type quantifiers: num_elem : Nat, num_elem > 0 -/
def read_vmask (num_elem : Nat) (vm : (BitVec 1)) (vrid : vregidx) : SailM (BitVec num_elem) := do
  assert (num_elem ≤b 65536) "model/riscv_vext_regs.sail:374.36-374.37"
  let vreg_val ← (( do (rV_bits vrid) ) : SailM vregtype )
  let result : (BitVec num_elem) := (ones (n := num_elem))
  if ((vm == (0b1 : (BitVec 1))) : Bool)
  then (pure result)
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_elem -i 1)
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars := (BitVec.update result i (BitVec.access vreg_val i))
      (pure loop_vars))

/-- Type quantifiers: num_elem : Nat, num_elem > 0 -/
def read_vmask_carry (num_elem : Nat) (vm : (BitVec 1)) (vrid : vregidx) : SailM (BitVec num_elem) := do
  assert (num_elem ≤b 65536) "model/riscv_vext_regs.sail:392.36-392.37"
  let vreg_val ← (( do (rV_bits vrid) ) : SailM vregtype )
  let result : (BitVec num_elem) := (zeros (n := num_elem))
  if ((vm == (0b1 : (BitVec 1))) : Bool)
  then (pure result)
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_elem -i 1)
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars := (BitVec.update result i (BitVec.access vreg_val i))
      (pure loop_vars))

/-- Type quantifiers: num_elem : Nat, num_elem > 0 -/
def write_vmask (num_elem : Nat) (vrid : vregidx) (v : (BitVec num_elem)) : SailM Unit := do
  assert ((0 <b VLEN) && (VLEN ≤b 65536)) "model/riscv_vext_regs.sail:410.43-410.44"
  assert ((0 <b num_elem) && (num_elem ≤b VLEN)) "model/riscv_vext_regs.sail:411.40-411.41"
  let vreg_val ← (( do (rV_bits vrid) ) : SailM vregtype )
  let result ← (( do (undefined_bitvector 65536) ) : SailM vregtype )
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars := (BitVec.update result i (BitVec.access v i))
    (pure loop_vars) ) : SailM (BitVec 65536) )
  let result ← (( do
    let loop_i_lower := num_elem
    let loop_i_upper := (VLEN -i 1)
    let mut loop_vars_1 := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 := (BitVec.update result i (BitVec.access vreg_val i))
    (pure loop_vars_1) ) : SailM (BitVec 65536) )
  (wV_bits vrid result)

