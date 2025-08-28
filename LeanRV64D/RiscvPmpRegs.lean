import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvXlen
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
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def sys_pmp_count : Int := 16

def sys_pmp_grain : Nat := 0

def undefined_PmpAddrMatchType (_ : Unit) : SailM PmpAddrMatchType := do
  (internal_pick [OFF, TOR, NA4, NAPOT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PmpAddrMatchType_of_num (arg_ : Nat) : PmpAddrMatchType :=
  match arg_ with
  | 0 => OFF
  | 1 => TOR
  | 2 => NA4
  | _ => NAPOT

def num_of_PmpAddrMatchType (arg_ : PmpAddrMatchType) : Int :=
  match arg_ with
  | OFF => 0
  | TOR => 1
  | NA4 => 2
  | NAPOT => 3

def pmpAddrMatchType_encdec_forwards (arg_ : PmpAddrMatchType) : (BitVec 2) :=
  match arg_ with
  | OFF => (0b00 : (BitVec 2))
  | TOR => (0b01 : (BitVec 2))
  | NA4 => (0b10 : (BitVec 2))
  | NAPOT => (0b11 : (BitVec 2))

def pmpAddrMatchType_encdec_backwards (arg_ : (BitVec 2)) : PmpAddrMatchType :=
  let b__0 := arg_
  if ((b__0 == (0b00 : (BitVec 2))) : Bool)
  then OFF
  else
    (if ((b__0 == (0b01 : (BitVec 2))) : Bool)
    then TOR
    else
      (if ((b__0 == (0b10 : (BitVec 2))) : Bool)
      then NA4
      else NAPOT))

def pmpAddrMatchType_encdec_forwards_matches (arg_ : PmpAddrMatchType) : Bool :=
  match arg_ with
  | OFF => true
  | TOR => true
  | NA4 => true
  | NAPOT => true

def pmpAddrMatchType_encdec_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b00 : (BitVec 2))) : Bool)
  then true
  else
    (if ((b__0 == (0b01 : (BitVec 2))) : Bool)
    then true
    else
      (if ((b__0 == (0b10 : (BitVec 2))) : Bool)
      then true
      else
        (if ((b__0 == (0b11 : (BitVec 2))) : Bool)
        then true
        else false)))

def undefined_Pmpcfg_ent (_ : Unit) : SailM (BitVec 8) := do
  (undefined_bitvector 8)

def Mk_Pmpcfg_ent (v : (BitVec 8)) : (BitVec 8) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def pmpReadCfgReg (n : Nat) : SailM (BitVec 64) := do
  assert ((Int.tmod n 2) == 0) "Unexpected pmp config reg read"
  (pure ((GetElem?.getElem! (← readReg pmpcfg_n) ((n *i 4) +i 7)) ++ ((GetElem?.getElem!
          (← readReg pmpcfg_n) ((n *i 4) +i 6)) ++ ((GetElem?.getElem! (← readReg pmpcfg_n)
            ((n *i 4) +i 5)) ++ ((GetElem?.getElem! (← readReg pmpcfg_n) ((n *i 4) +i 4)) ++ ((GetElem?.getElem!
                (← readReg pmpcfg_n) ((n *i 4) +i 3)) ++ ((GetElem?.getElem!
                  (← readReg pmpcfg_n) ((n *i 4) +i 2)) ++ ((GetElem?.getElem!
                    (← readReg pmpcfg_n) ((n *i 4) +i 1)) ++ (GetElem?.getElem!
                    (← readReg pmpcfg_n) ((n *i 4) +i 0))))))))))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 63 -/
def pmpReadAddrReg (n : Nat) : SailM (BitVec 64) := do
  let G := sys_pmp_grain
  let match_type ← do (pure (_get_Pmpcfg_ent_A (GetElem?.getElem! (← readReg pmpcfg_n) n)))
  let addr ← do (pure (GetElem?.getElem! (← readReg pmpaddr_n) n))
  match (BitVec.access match_type 1) with
  | 1#1 =>
    (if ((G ≥b 2) : Bool)
    then
      (let mask : xlenbits := (zero_extend (m := 64) (ones (n := (Min.min (G -i 1) xlen))))
      (pure (addr ||| mask)))
    else (pure addr))
  | 0#1 =>
    (if ((G ≥b 1) : Bool)
    then
      (let mask : xlenbits := (zero_extend (m := 64) (ones (n := (Min.min G xlen))))
      (pure (addr &&& (Complement.complement mask))))
    else (pure addr))
  | _ => (pure addr)

def pmpLocked (cfg : (BitVec 8)) : Bool :=
  ((_get_Pmpcfg_ent_L cfg) == (0b1 : (BitVec 1)))

def pmpTORLocked (cfg : (BitVec 8)) : Bool :=
  (((_get_Pmpcfg_ent_L cfg) == (0b1 : (BitVec 1))) && ((pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A cfg)) == TOR))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 63 -/
def pmpWriteCfg (n : Nat) (cfg : (BitVec 8)) (v : (BitVec 8)) : (BitVec 8) :=
  if ((pmpLocked cfg) : Bool)
  then cfg
  else
    (let cfg := (Mk_Pmpcfg_ent (v &&& (0x9F : (BitVec 8))))
    let cfg :=
      if ((((_get_Pmpcfg_ent_W cfg) == (0b1 : (BitVec 1))) && ((_get_Pmpcfg_ent_R cfg) == (0b0 : (BitVec 1)))) : Bool)
      then
        (_update_Pmpcfg_ent_R
          (_update_Pmpcfg_ent_W (_update_Pmpcfg_ent_X cfg (0b0 : (BitVec 1))) (0b0 : (BitVec 1)))
          (0b0 : (BitVec 1)))
      else cfg
    let mode_supported : Bool :=
      match (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A cfg)) with
      | OFF => true
      | TOR => true
      | NA4 => ((true : Bool) && (sys_pmp_grain == 0))
      | NAPOT => true
    if (mode_supported : Bool)
    then cfg
    else (_update_Pmpcfg_ent_A cfg (pmpAddrMatchType_encdec_forwards OFF)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def pmpWriteCfgReg (n : Nat) (v : (BitVec 64)) : SailM Unit := do
  assert ((Int.tmod n 2) == 0) "Unexpected pmp config reg write"
  let loop_i_lower := 0
  let loop_i_upper := 7
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let idx := ((n *i 4) +i i)
      writeReg pmpcfg_n (vectorUpdate (← readReg pmpcfg_n) idx
        (pmpWriteCfg idx (GetElem?.getElem! (← readReg pmpcfg_n) idx)
          (Sail.BitVec.extractLsb v ((8 *i i) +i 7) (8 *i i))))
  (pure loop_vars)

/-- Type quantifiers: k_ex372197# : Bool, k_ex372196# : Bool -/
def pmpWriteAddr (locked : Bool) (tor_locked : Bool) (reg : (BitVec 64)) (v : (BitVec 64)) : (BitVec 64) :=
  if ((locked || tor_locked) : Bool)
  then reg
  else (zero_extend (m := 64) (Sail.BitVec.extractLsb v 53 0))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 63 -/
def pmpWriteAddrReg (n : Nat) (v : (BitVec 64)) : SailM Unit := do
  writeReg pmpaddr_n (vectorUpdate (← readReg pmpaddr_n) n
    (pmpWriteAddr (pmpLocked (GetElem?.getElem! (← readReg pmpcfg_n) n))
      (← do
        if (((n +i 1) <b 64) : Bool)
        then (pure (pmpTORLocked (GetElem?.getElem! (← readReg pmpcfg_n) (n +i 1))))
        else (pure false)) (GetElem?.getElem! (← readReg pmpaddr_n) n) v))

