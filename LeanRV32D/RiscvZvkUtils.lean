import LeanRV32D.RiscvTypesKext

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

/-- Type quantifiers: emul_pow : Int -/
def zvk_valid_reg_overlap (rs : vregidx) (rd : vregidx) (emul_pow : Int) : Bool :=
  let reg_group_size :=
    bif (emul_pow >b 0)
    then (2 ^i emul_pow)
    else 1
  let rs_int := (BitVec.toNat (vregidx_bits rs))
  let rd_int := (BitVec.toNat (vregidx_bits rd))
  (((rs_int +i reg_group_size) ≤b rd_int) || ((rd_int +i reg_group_size) ≤b rs_int))

/-- Type quantifiers: EGS : Int, EGW : Int -/
def zvk_check_encdec (EGW : Int) (EGS : Int) : SailM Bool := do
  (pure (((Int.emod (BitVec.toNat (← readReg vl)) EGS) == 0) && (← do
        (pure (((Int.emod (BitVec.toNat (← readReg vstart)) EGS) == 0) && (← do
              (pure (((2 ^i (← (get_lmul_pow ()))) *i VLEN) ≥b EGW))))))))

def undefined_zvkfunct6 (_ : Unit) : SailM zvkfunct6 := do
  (internal_pick [ZVK_VSHA2CH, ZVK_VSHA2CL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvkfunct6_of_num (arg_ : Nat) : zvkfunct6 :=
  match arg_ with
  | 0 => ZVK_VSHA2CH
  | _ => ZVK_VSHA2CL

def num_of_zvkfunct6 (arg_ : zvkfunct6) : Int :=
  match arg_ with
  | ZVK_VSHA2CH => 0
  | ZVK_VSHA2CL => 1

def zvknhab_check_encdec (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) : SailM Bool := do
  let SEW ← do (get_sew ())
  let LMUL_pow ← do (get_lmul_pow ())
  (pure ((← (zvk_check_encdec SEW 4)) && ((zvk_valid_reg_overlap vs1 vd LMUL_pow) && (zvk_valid_reg_overlap
          vs2 vd LMUL_pow))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {32, 64} -/
def zvk_sig0 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 7) ^^^ ((rotater x 18) ^^^ (shiftr x 3)))
  | _ => ((rotater x 1) ^^^ ((rotater x 8) ^^^ (shiftr x 7)))

/-- Type quantifiers: SEW : Nat, SEW ∈ {32, 64} -/
def zvk_sig1 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 17) ^^^ ((rotater x 19) ^^^ (shiftr x 10)))
  | _ => ((rotater x 19) ^^^ ((rotater x 61) ^^^ (shiftr x 6)))

/-- Type quantifiers: SEW : Nat, SEW ∈ {32, 64} -/
def zvk_sum0 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 2) ^^^ ((rotater x 13) ^^^ (rotater x 22)))
  | _ => ((rotater x 28) ^^^ ((rotater x 34) ^^^ (rotater x 39)))

/-- Type quantifiers: SEW : Nat, SEW ∈ {32, 64} -/
def zvk_sum1 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 6) ^^^ ((rotater x 11) ^^^ (rotater x 25)))
  | _ => ((rotater x 14) ^^^ ((rotater x 18) ^^^ (rotater x 41)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zvk_ch (x : (BitVec k_n)) (y : (BitVec k_n)) (z : (BitVec k_n)) : (BitVec k_n) :=
  ((x &&& y) ^^^ ((Complement.complement x) &&& z))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zvk_maj (x : (BitVec k_n)) (y : (BitVec k_n)) (z : (BitVec k_n)) : (BitVec k_n) :=
  ((x &&& y) ^^^ ((x &&& z) ^^^ (y &&& z)))

def zvk_p0 (X : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ ((rotatel X 9) ^^^ (rotatel X 17)))

def zvk_p1 (X : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ ((rotatel X 15) ^^^ (rotatel X 23)))

def zvk_sh_w (A : (BitVec 32)) (B : (BitVec 32)) (C : (BitVec 32)) (D : (BitVec 32)) (E : (BitVec 32)) : (BitVec 32) :=
  ((zvk_p1 (A ^^^ (B ^^^ (rotatel C 15)))) ^^^ ((rotatel D 7) ^^^ E))

def zvk_ff1 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ (Y ^^^ Z))

def zvk_ff2 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  ((X &&& Y) ||| ((X &&& Z) ||| (Y &&& Z)))

/-- Type quantifiers: J : Int -/
def zvk_ff_j (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) (J : Int) : (BitVec 32) :=
  bif (J ≤b 15)
  then (zvk_ff1 X Y Z)
  else (zvk_ff2 X Y Z)

def zvk_gg1 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ (Y ^^^ Z))

def zvk_gg2 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  ((X &&& Y) ||| ((Complement.complement X) &&& Z))

/-- Type quantifiers: J : Int -/
def zvk_gg_j (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) (J : Int) : (BitVec 32) :=
  bif (J ≤b 15)
  then (zvk_gg1 X Y Z)
  else (zvk_gg2 X Y Z)

/-- Type quantifiers: J : Int -/
def zvk_t_j (J : Int) : (BitVec 32) :=
  bif (J ≤b 15)
  then (0x79CC4519 : (BitVec 32))
  else (0x7A879D8A : (BitVec 32))

/-- Type quantifiers: j : Int -/
def zvk_sm3_round (A_H : (Vector (BitVec 32) 8)) (w : (BitVec 32)) (x : (BitVec 32)) (j : Int) : (Vector (BitVec 32) 8) :=
  let t_j := (rotatel (zvk_t_j j) (Int.emod j 32))
  let ss1 :=
    (rotatel (((rotatel (GetElem?.getElem! A_H 0) 12) + (GetElem?.getElem! A_H 4)) + t_j) 7)
  let ss2 := (ss1 ^^^ (rotatel (GetElem?.getElem! A_H 0) 12))
  let tt1 :=
    ((((zvk_ff_j (GetElem?.getElem! A_H 0) (GetElem?.getElem! A_H 1) (GetElem?.getElem! A_H 2) j) + (GetElem?.getElem!
            A_H 3)) + ss2) + x)
  let tt2 :=
    ((((zvk_gg_j (GetElem?.getElem! A_H 4) (GetElem?.getElem! A_H 5) (GetElem?.getElem! A_H 6) j) + (GetElem?.getElem!
            A_H 7)) + ss1) + w)
  let A1 := tt1
  let C1 := (rotatel (GetElem?.getElem! A_H 1) 9)
  let E1 := (zvk_p0 tt2)
  let G1 := (rotatel (GetElem?.getElem! A_H 5) 19)
  #v[A1, (GetElem?.getElem! A_H 0), C1, (GetElem?.getElem! A_H 2), E1, (GetElem?.getElem! A_H 4), G1, (GetElem?.getElem!
      A_H 6)]

def undefined_zvk_vaesdf_funct6 (_ : Unit) : SailM zvk_vaesdf_funct6 := do
  (internal_pick [ZVK_VAESDF_VV, ZVK_VAESDF_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesdf_funct6_of_num (arg_ : Nat) : zvk_vaesdf_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESDF_VV
  | _ => ZVK_VAESDF_VS

def num_of_zvk_vaesdf_funct6 (arg_ : zvk_vaesdf_funct6) : Int :=
  match arg_ with
  | ZVK_VAESDF_VV => 0
  | ZVK_VAESDF_VS => 1

def undefined_zvk_vaesdm_funct6 (_ : Unit) : SailM zvk_vaesdm_funct6 := do
  (internal_pick [ZVK_VAESDM_VV, ZVK_VAESDM_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesdm_funct6_of_num (arg_ : Nat) : zvk_vaesdm_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESDM_VV
  | _ => ZVK_VAESDM_VS

def num_of_zvk_vaesdm_funct6 (arg_ : zvk_vaesdm_funct6) : Int :=
  match arg_ with
  | ZVK_VAESDM_VV => 0
  | ZVK_VAESDM_VS => 1

def undefined_zvk_vaesef_funct6 (_ : Unit) : SailM zvk_vaesef_funct6 := do
  (internal_pick [ZVK_VAESEF_VV, ZVK_VAESEF_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesef_funct6_of_num (arg_ : Nat) : zvk_vaesef_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESEF_VV
  | _ => ZVK_VAESEF_VS

def num_of_zvk_vaesef_funct6 (arg_ : zvk_vaesef_funct6) : Int :=
  match arg_ with
  | ZVK_VAESEF_VV => 0
  | ZVK_VAESEF_VS => 1

def undefined_zvk_vaesem_funct6 (_ : Unit) : SailM zvk_vaesem_funct6 := do
  (internal_pick [ZVK_VAESEM_VV, ZVK_VAESEM_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesem_funct6_of_num (arg_ : Nat) : zvk_vaesem_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESEM_VV
  | _ => ZVK_VAESEM_VS

def num_of_zvk_vaesem_funct6 (arg_ : zvk_vaesem_funct6) : Int :=
  match arg_ with
  | ZVK_VAESEM_VV => 0
  | ZVK_VAESEM_VS => 1

