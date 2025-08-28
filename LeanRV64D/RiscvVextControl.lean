import LeanRV64D.Flow
import LeanRV64D.Arith
import LeanRV64D.Prelude
import LeanRV64D.RiscvVlen
import LeanRV64D.RiscvVextRegs

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

/-- Type quantifiers: SEW : Nat, LMUL_pow : Int, SEW ∈ {8, 16, 32, 64} -/
def get_num_elem (LMUL_pow : Int) (SEW : Nat) : SailM Int := do
  let LMUL_pow_reg :=
    if ((LMUL_pow <b 0) : Bool)
    then 0
    else LMUL_pow
  let num_elem := (Int.tdiv ((2 ^i LMUL_pow_reg) *i vlen) SEW)
  assert (num_elem >b 0) "riscv_vext_control.sail:18.21-18.22"
  (pure num_elem)

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, SEW ≥ 0, num_elem ≥ 0 ∧
  is_sew_bitsize(SEW) -/
def read_single_vreg (num_elem : Nat) (SEW : Nat) (vrid : vregidx) : SailM (Vector (BitVec SEW) num_elem) := do
  assert ((num_elem *i SEW) ≤b vlen) "riscv_vext_control.sail:26.31-26.32"
  let bv ← do (rV_bits vrid)
  let result : (Vector (BitVec SEW) num_elem) := (vectorInit (zeros (n := SEW)))
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      let start_index := (i *i SEW)
      (vectorUpdate result i (Sail.BitVec.extractLsb bv ((start_index +i SEW) -i 1) start_index))
  (pure loop_vars)

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, SEW ≥ 0, num_elem ≥ 0 ∧
  is_sew_bitsize(SEW) -/
def write_single_vreg (num_elem : Nat) (SEW : Nat) (vrid : vregidx) (v : (Vector (BitVec SEW) num_elem)) : SailM Unit := do
  let r : vlenbits := (zeros (n := (2 ^i 8)))
  assert (SEW ≤b vlen) "riscv_vext_control.sail:44.20-44.21"
  let r ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := r
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let r := loop_vars
      loop_vars :=
        let r : vlenbits := (shiftl r SEW)
        (r ||| (zero_extend (m := (2 ^i 8)) (GetElem?.getElem! v i)))
    (pure loop_vars) ) : SailM (BitVec (2 ^ 8)) )
  (wV_bits vrid r)

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, SEW ≥ 0, LMUL_pow : Int, num_elem
  ≥ 0 ∧ is_sew_bitsize(SEW) -/
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
          if (((num_elem *i SEW) <b vlen) : Bool)
          then
            (do
              (read_single_vreg (Vector.length result) SEW vrid))
          else
            (do
              let num_elem_single := (Int.tdiv vlen SEW)
              assert (num_elem_single ≥b 0) "riscv_vext_control.sail:74.34-74.35"
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
                      assert ((0 ≤b r_i) && (r_i <b num_elem)) "riscv_vext_control.sail:82.42-82.43"
                      assert ((0 ≤b s_i) && (s_i <b num_elem_single)) "riscv_vext_control.sail:83.50-83.51"
                      (pure (vectorUpdate result r_i (GetElem?.getElem! single_result s_i)))
                  (pure loop_vars_1)
              (pure loop_vars))))

/-- Type quantifiers: index : Nat, EEW : Nat, EEW ≥ 0, is_sew_bitsize(EEW), 0 ≤ index -/
def read_single_element (EEW : Nat) (index : Nat) (vrid : vregidx) : SailM (BitVec EEW) := do
  assert (EEW ≤b vlen) "riscv_vext_control.sail:96.20-96.21"
  let elem_per_reg := (Int.tdiv vlen EEW)
  let reg_in_group := (Int.tdiv index elem_per_reg)
  assert (reg_in_group <b 8) "riscv_vext_control.sail:103.25-103.26"
  let vrid := (vregidx_offset_range vrid reg_in_group)
  let index := (Int.tmod index elem_per_reg)
  let offset := (index *i EEW)
  (pure (Sail.BitVec.extractLsb (← (rV_bits vrid)) ((offset +i EEW) -i 1) offset))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, SEW ≥ 0, LMUL_pow : Int, num_elem
  ≥ 0 ∧ is_sew_bitsize(SEW) -/
def write_vreg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (vrid : vregidx) (vec : (Vector (BitVec SEW) num_elem)) : SailM Unit := do
  let LMUL_pow_reg :=
    if ((LMUL_pow <b 0) : Bool)
    then 0
    else LMUL_pow
  let num_elem_single := (Int.tdiv vlen SEW)
  assert (num_elem_single ≥b 0) "riscv_vext_control.sail:120.30-120.31"
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
            assert ((0 ≤b r_i) && (r_i <b num_elem)) "riscv_vext_control.sail:128.38-128.39"
            assert ((0 ≤b s_i) && (s_i <b num_elem_single)) "riscv_vext_control.sail:129.46-129.47"
            (pure (vectorUpdate single_vec s_i (GetElem?.getElem! vec r_i)))
        (pure loop_vars_1) ) : SailM (Vector (BitVec SEW) num_elem_single) )
      (write_single_vreg num_elem_single SEW vrid_lmul single_vec)
  (pure loop_vars)

/-- Type quantifiers: index : Nat, EEW : Nat, EEW ≥ 0, is_sew_bitsize(EEW), 0 ≤ index -/
def write_single_element (EEW : Nat) (index : Nat) (vrid : vregidx) (value : (BitVec EEW)) : SailM Unit := do
  assert (EEW ≤b vlen) "riscv_vext_control.sail:140.20-140.21"
  let elem_per_reg := (Int.tdiv vlen EEW)
  let reg_in_group := (Int.tdiv index elem_per_reg)
  assert (reg_in_group <b 8) "riscv_vext_control.sail:147.25-147.26"
  let vrid := (vregidx_offset_range vrid reg_in_group)
  let index := (Int.tmod index elem_per_reg)
  let offset := (index *i EEW)
  (wV_bits vrid
    (Sail.BitVec.updateSubrange (← (rV_bits vrid)) ((offset +i EEW) -i 1) offset value))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, num_elem > 0 -/
def read_vmask (num_elem : Nat) (vm : (BitVec 1)) (vrid : vregidx) : SailM (BitVec num_elem) := do
  assert (num_elem ≤b vlen) "riscv_vext_control.sail:161.25-161.26"
  let vreg_val ← do (rV_bits vrid)
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

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, num_elem > 0 -/
def read_vmask_carry (num_elem : Nat) (vm : (BitVec 1)) (vrid : vregidx) : SailM (BitVec num_elem) := do
  assert (num_elem ≤b vlen) "riscv_vext_control.sail:180.25-180.26"
  let vreg_val ← do (rV_bits vrid)
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

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, num_elem > 0 -/
def write_vmask (num_elem : Nat) (vrid : vregidx) (v : (BitVec num_elem)) : SailM Unit := do
  assert ((0 <b num_elem) && (num_elem ≤b vlen)) "riscv_vext_control.sail:199.40-199.41"
  let vreg_val ← do (rV_bits vrid)
  let result ← (( do (undefined_bitvector (2 ^i 8)) ) : SailM vlenbits )
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars := (BitVec.update result i (BitVec.access v i))
    (pure loop_vars) ) : SailM (BitVec (2 ^ 8)) )
  let result ← (( do
    let loop_i_lower := num_elem
    let loop_i_upper := (vlen -i 1)
    let mut loop_vars_1 := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 := (BitVec.update result i (BitVec.access vreg_val i))
    (pure loop_vars_1) ) : SailM (BitVec (2 ^ 8)) )
  (wV_bits vrid result)

