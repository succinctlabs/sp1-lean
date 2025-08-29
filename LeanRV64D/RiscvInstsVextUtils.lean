import LeanRV64D.Flow
import LeanRV64D.Arith
import LeanRV64D.Prelude
import LeanRV64D.RiscvXlen
import LeanRV64D.RiscvVlen
import LeanRV64D.Arithmetic
import LeanRV64D.RiscvRegs
import LeanRV64D.RiscvVextRegs
import LeanRV64D.RiscvVextControl

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

def maybe_vmask_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "" => (pure (0b1 : (BitVec 1)))
  | _ => throw Error.Exit

def maybe_vmask_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | "" => (pure true)
  | _ => throw Error.Exit

def maybe_vmask_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else
    (if ((b__0 == (0b0 : (BitVec 1))) : Bool)
    then true
    else false)

/-- Type quantifiers: EMUL_pow : Int, EEW : Int -/
def valid_eew_emul (EEW : Int) (EMUL_pow : Int) : Bool :=
  ((EEW ≥b 8) && ((EEW ≤b elen) && ((EMUL_pow ≥b (-3)) && (EMUL_pow ≤b 3))))

def valid_vtype (_ : Unit) : SailM Bool := do
  (pure ((_get_Vtype_vill (← readReg vtype)) == (0b0 : (BitVec 1))))

/-- Type quantifiers: i : Int -/
def assert_vstart (i : Int) : SailM Bool := do
  (pure ((BitVec.toNat (← readReg vstart)) == i))

def valid_rd_mask (rd : vregidx) (vm : (BitVec 1)) : Bool :=
  ((vm != (0b0 : (BitVec 1))) || (bne rd zvreg))

/-- Type quantifiers: EMUL_pow_rd : Int, EMUL_pow_rs : Int -/
def valid_reg_overlap (rs : vregidx) (rd : vregidx) (EMUL_pow_rs : Int) (EMUL_pow_rd : Int) : Bool :=
  let rs_group :=
    if ((EMUL_pow_rs >b 0) : Bool)
    then (2 ^i EMUL_pow_rs)
    else 1
  let rd_group :=
    if ((EMUL_pow_rd >b 0) : Bool)
    then (2 ^i EMUL_pow_rd)
    else 1
  let rs_int := (BitVec.toNat (vregidx_bits rs))
  let rd_int := (BitVec.toNat (vregidx_bits rd))
  if ((EMUL_pow_rs <b EMUL_pow_rd) : Bool)
  then
    (((rs_int +i rs_group) ≤b rd_int) || ((rs_int ≥b (rd_int +i rd_group)) || (((rs_int +i rs_group) == (rd_int +i rd_group)) && (EMUL_pow_rs ≥b 0))))
  else
    (if ((EMUL_pow_rs >b EMUL_pow_rd) : Bool)
    then ((rd_int ≤b rs_int) || (rd_int ≥b (rs_int +i rs_group)))
    else true)

/-- Type quantifiers: EMUL_pow : Int, nf : Nat, nf > 0 ∧ nf ≤ 8 -/
def valid_segment (nf : Nat) (EMUL_pow : Int) : Bool :=
  if ((EMUL_pow <b 0) : Bool)
  then ((Int.tdiv nf (2 ^i (0 -i EMUL_pow))) ≤b 8)
  else ((nf *i (2 ^i EMUL_pow)) ≤b 8)

def illegal_normal (vd : vregidx) (vm : (BitVec 1)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (not (valid_rd_mask vd vm))))

def illegal_vd_masked (vd : vregidx) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (vd == zvreg)))

def illegal_vd_unmasked (_ : Unit) : SailM Bool := do
  (pure (not (← (valid_vtype ()))))

/-- Type quantifiers: LMUL_pow_new : Int, SEW_new : Int -/
def illegal_variable_width (vd : vregidx) (vm : (BitVec 1)) (SEW_new : Int) (LMUL_pow_new : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || (not
          (valid_eew_emul SEW_new LMUL_pow_new)))))

def illegal_reduction (_ : Unit) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (not (← (assert_vstart 0)))))

/-- Type quantifiers: EEW : Int -/
def illegal_widening_reduction (EEW : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (← (assert_vstart 0))) || (not
          ((EEW ≥b 8) && (EEW ≤b elen))))))

/-- Type quantifiers: EMUL_pow : Int, EEW : Int, nf : Nat, nf > 0 ∧ nf ≤ 8 -/
def illegal_load (vd : vregidx) (vm : (BitVec 1)) (nf : Nat) (EEW : Int) (EMUL_pow : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || ((not
            (valid_eew_emul EEW EMUL_pow)) || (not (valid_segment nf EMUL_pow))))))

/-- Type quantifiers: EMUL_pow : Int, EEW : Int, nf : Nat, nf > 0 ∧ nf ≤ 8 -/
def illegal_store (nf : Nat) (EEW : Int) (EMUL_pow : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_eew_emul EEW EMUL_pow)) || (not
          (valid_segment nf EMUL_pow)))))

/-- Type quantifiers: EMUL_pow_data : Int, EMUL_pow_index : Int, EEW_index : Int, nf : Nat, nf > 0
  ∧ nf ≤ 8 -/
def illegal_indexed_load (vd : vregidx) (vm : (BitVec 1)) (nf : Nat) (EEW_index : Int) (EMUL_pow_index : Int) (EMUL_pow_data : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || ((not
            (valid_eew_emul EEW_index EMUL_pow_index)) || (not (valid_segment nf EMUL_pow_data))))))

/-- Type quantifiers: EMUL_pow_data : Int, EMUL_pow_index : Int, EEW_index : Int, nf : Nat, nf > 0
  ∧ nf ≤ 8 -/
def illegal_indexed_store (nf : Nat) (EEW_index : Int) (EMUL_pow_index : Int) (EMUL_pow_data : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_eew_emul EEW_index EMUL_pow_index)) || (not
          (valid_segment nf EMUL_pow_data)))))

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, SEW ≥ 8 -/
def get_scalar (rs1 : regidx) (SEW : Nat) : SailM (BitVec SEW) := do
  if ((SEW ≤b xlen) : Bool)
  then (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) (SEW -i 1) 0))
  else (pure (sign_extend (m := SEW) (← (rX_bits rs1))))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_m : Nat, k_m ≥ 0, i : Nat, k_n > 0 ∧
  k_m > 0 ∧ i ≥ 0 ∧ (4 * i + 3) < k_n -/
def get_velem_quad (v : (Vector (BitVec k_m) k_n)) (i : Nat) : (BitVec (4 * k_m)) :=
  ((GetElem?.getElem! v ((4 *i i) +i 3)) ++ ((GetElem?.getElem! v ((4 *i i) +i 2)) ++ ((GetElem?.getElem!
          v ((4 *i i) +i 1)) ++ (GetElem?.getElem! v (4 *i i)))))

/-- Type quantifiers: i : Nat, SEW : Nat, k_n : Nat, k_n ≥ 0, k_n > 0, SEW ∈ {8, 16, 32, 64}, 0
  ≤ i -/
def write_velem_quad (vd : vregidx) (SEW : Nat) (input : (BitVec k_n)) (i : Nat) : SailM Unit := do
  let loop_j_lower := 0
  let loop_j_upper := 3
  let mut loop_vars := ()
  for j in [loop_j_lower:loop_j_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      assert (((j +i 1) *i SEW) ≤b (Sail.BitVec.length input)) "riscv_insts_vext_utils.sail:184.30-184.31"
      (write_single_element SEW ((4 *i i) +i j) vd
        (Sail.BitVec.extractLsb input (((j +i 1) *i SEW) -i 1) (j *i SEW)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n ≥ 0, k_m : Nat, k_m ≥ 0, i : Nat, n > 0 ∧
  8 ≤ k_m ∧ k_m ≤ 64 ∧ i ≥ 0 ∧ (8 * i + 7) < n -/
def get_velem_oct_vec {n : _} (v : (Vector (BitVec k_m) n)) (i : Nat) : (Vector (BitVec k_m) 8) :=
  #v[(GetElem?.getElem! v (8 *i i)), (GetElem?.getElem! v ((8 *i i) +i 1)), (GetElem?.getElem! v
      ((8 *i i) +i 2)), (GetElem?.getElem! v ((8 *i i) +i 3)), (GetElem?.getElem! v ((8 *i i) +i 4)), (GetElem?.getElem!
      v ((8 *i i) +i 5)), (GetElem?.getElem! v ((8 *i i) +i 6)), (GetElem?.getElem! v
      ((8 *i i) +i 7))]

/-- Type quantifiers: i : Nat, SEW : Nat, SEW ≥ 0, is_sew_bitsize(SEW), 0 ≤ i -/
def write_velem_oct_vec (vd : vregidx) (SEW : Nat) (input : (Vector (BitVec SEW) 8)) (i : Nat) : SailM Unit := do
  let loop_j_lower := 0
  let loop_j_upper := 7
  let mut loop_vars := ()
  for j in [loop_j_lower:loop_j_upper:1]i do
    let () := loop_vars
    loop_vars ← do (write_single_element SEW ((8 *i i) +i j) vd (GetElem?.getElem! input j))
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_m : Nat, k_m ≥ 0, i : Nat, k_n > 0 ∧
  8 ≤ k_m ∧ k_m ≤ 64 ∧ i ≥ 0 ∧ (4 * i + 3) < k_n -/
def get_velem_quad_vec (v : (Vector (BitVec k_m) k_n)) (i : Nat) : (Vector (BitVec k_m) 4) :=
  #v[(GetElem?.getElem! v (4 *i i)), (GetElem?.getElem! v ((4 *i i) +i 1)), (GetElem?.getElem! v
      ((4 *i i) +i 2)), (GetElem?.getElem! v ((4 *i i) +i 3))]

/-- Type quantifiers: i : Nat, SEW : Nat, SEW ≥ 0, is_sew_bitsize(SEW) ∧ i ≥ 0 -/
def write_velem_quad_vec (vd : vregidx) (SEW : Nat) (input : (Vector (BitVec SEW) 4)) (i : Nat) : SailM Unit := do
  let loop_j_lower := 0
  let loop_j_upper := 3
  let mut loop_vars := ()
  for j in [loop_j_lower:loop_j_upper:1]i do
    let () := loop_vars
    loop_vars ← do (write_single_element SEW ((4 *i i) +i j) vd (GetElem?.getElem! input j))
  (pure loop_vars)

def get_start_element (_ : Unit) : SailM (Result Nat Unit) := do
  let start_element ← do (pure (BitVec.toNat (← readReg vstart)))
  let SEW_pow ← do (get_sew_pow ())
  if ((start_element >b ((2 ^i ((3 +i vlen_exp) -i SEW_pow)) -i 1)) : Bool)
  then (pure (Err ()))
  else (pure (Ok start_element))

def get_end_element (_ : Unit) : SailM Int := do
  (pure ((BitVec.toNat (← readReg vl)) -i 1))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, EEW : Nat, EEW ≥ 0, LMUL_pow : Int, num_elem
  ≥ 0 -/
def init_masked_result (num_elem : Nat) (EEW : Nat) (LMUL_pow : Int) (vd_val : (Vector (BitVec EEW) num_elem)) (vm_val : (BitVec num_elem)) : SailM (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit) := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () =>
      SailME.throw ((Err ()) : (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit))
    ) : SailME (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit) Nat )
  let end_element ← do (get_end_element ())
  let tail_ag ← (( do (get_vtype_vta ()) ) : SailME
    (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit) agtype )
  let mask_ag ← (( do (get_vtype_vma ()) ) : SailME
    (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit) agtype )
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailME
    (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit) (BitVec num_elem) )
  let result ← (( do
    (undefined_vector (Sail.BitVec.length vm_val) (← (undefined_bitvector EEW))) ) : SailME
    (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit)
    (Vector (BitVec EEW) num_elem) )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  assert (num_elem ≥b real_num_elem) "riscv_insts_vext_utils.sail:255.34-255.35"
  let (mask, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := (mask, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mask, result) := loop_vars
      loop_vars :=
        let (mask, result) : ((BitVec num_elem) × (Vector (BitVec EEW) num_elem)) :=
          if ((i <b start_element) : Bool)
          then
            (let result : (Vector (BitVec EEW) num_elem) :=
              (vectorUpdate result i (GetElem?.getElem! vd_val i))
            let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
            (mask, result))
          else
            (let (mask, result) : ((BitVec num_elem) × (Vector (BitVec EEW) num_elem)) :=
              if ((i >b end_element) : Bool)
              then
                (let result : (Vector (BitVec EEW) num_elem) :=
                  (vectorUpdate result i
                    (match tail_ag with
                    | UNDISTURBED => (GetElem?.getElem! vd_val i)
                    | AGNOSTIC => (GetElem?.getElem! vd_val i)))
                let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                (mask, result))
              else
                (let (mask, result) : ((BitVec num_elem) × (Vector (BitVec EEW) num_elem)) :=
                  if ((i ≥b real_num_elem) : Bool)
                  then
                    (let result : (Vector (BitVec EEW) num_elem) :=
                      (vectorUpdate result i
                        (match tail_ag with
                        | UNDISTURBED => (GetElem?.getElem! vd_val i)
                        | AGNOSTIC => (GetElem?.getElem! vd_val i)))
                    let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                    (mask, result))
                  else
                    (let (mask, result) : ((BitVec num_elem) × (Vector (BitVec EEW) num_elem)) :=
                      if (((BitVec.access vm_val i) == 0#1) : Bool)
                      then
                        (let result : (Vector (BitVec EEW) num_elem) :=
                          (vectorUpdate result i
                            (match mask_ag with
                            | UNDISTURBED => (GetElem?.getElem! vd_val i)
                            | AGNOSTIC => (GetElem?.getElem! vd_val i)))
                        let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                        (mask, result))
                      else
                        (let mask : (BitVec num_elem) := (BitVec.update mask i 1#1)
                        (mask, result))
                    (mask, result))
                (mask, result))
            (mask, result))
        (mask, result)
    (pure loop_vars) ) : SailME (Result ((Vector (BitVec EEW) num_elem) × (BitVec num_elem)) Unit)
    ((BitVec num_elem) × (Vector (BitVec EEW) num_elem)) )
  (pure (Ok (result, mask)))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, LMUL_pow : Int, num_elem > 0 -/
def init_masked_source (num_elem : Nat) (LMUL_pow : Int) (vm_val : (BitVec num_elem)) : SailM (Result (BitVec num_elem) Unit) := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Err ()) : (Result (BitVec num_elem) Unit)) ) : SailME
    (Result (BitVec num_elem) Unit) Nat )
  let end_element ← do (get_end_element ())
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailME
    (Result (BitVec num_elem) Unit) (BitVec num_elem) )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  assert (num_elem ≥b real_num_elem) "riscv_insts_vext_utils.sail:308.34-308.35"
  let mask ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := mask
    for i in [loop_i_lower:loop_i_upper:1]i do
      let mask := loop_vars
      loop_vars :=
        if ((i <b start_element) : Bool)
        then (BitVec.update mask i 0#1)
        else
          (if ((i >b end_element) : Bool)
          then (BitVec.update mask i 0#1)
          else
            (if ((i ≥b real_num_elem) : Bool)
            then (BitVec.update mask i 0#1)
            else
              (if (((BitVec.access vm_val i) == 0#1) : Bool)
              then (BitVec.update mask i 0#1)
              else (BitVec.update mask i 1#1))))
    (pure loop_vars) ) : SailME (Result (BitVec num_elem) Unit) (BitVec num_elem) )
  (pure (Ok mask))

/-- Type quantifiers: LMUL_pow : Int, EEW : Nat, num_elem : Nat, num_elem ≥ 0, num_elem ≥ 0, EEW
  ∈ {8, 16, 32, 64} -/
def init_masked_result_carry (num_elem : Nat) (EEW : Nat) (LMUL_pow : Int) (vd_val : (BitVec num_elem)) : SailM (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Err ()) : (Result ((BitVec num_elem) × (BitVec num_elem)) Unit)) )
    : SailME (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) Nat )
  let end_element ← do (get_end_element ())
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vd_val)) ) : SailME
    (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) (BitVec num_elem) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length vd_val)) ) : SailME
    (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) (BitVec num_elem) )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  assert (num_elem ≥b real_num_elem) "riscv_insts_vext_utils.sail:346.34-346.35"
  let (mask, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := (mask, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mask, result) := loop_vars
      loop_vars :=
        let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
          if ((i <b start_element) : Bool)
          then
            (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
            let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
            (mask, result))
          else
            (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
              if ((i >b end_element) : Bool)
              then
                (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
                let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                (mask, result))
              else
                (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
                  if ((i ≥b real_num_elem) : Bool)
                  then
                    (let result : (BitVec num_elem) :=
                      (BitVec.update result i (BitVec.access vd_val i))
                    let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                    (mask, result))
                  else
                    (let mask : (BitVec num_elem) := (BitVec.update mask i 1#1)
                    (mask, result))
                (mask, result))
            (mask, result))
        (mask, result)
    (pure loop_vars) ) : SailME (Result ((BitVec num_elem) × (BitVec num_elem)) Unit)
    ((BitVec num_elem) × (BitVec num_elem)) )
  (pure (Ok (result, mask)))

/-- Type quantifiers: LMUL_pow : Int, EEW : Nat, num_elem : Nat, num_elem ≥ 0, num_elem ≥ 0, EEW
  ∈ {8, 16, 32, 64} -/
def init_masked_result_cmp (num_elem : Nat) (EEW : Nat) (LMUL_pow : Int) (vd_val : (BitVec num_elem)) (vm_val : (BitVec num_elem)) : SailM (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Err ()) : (Result ((BitVec num_elem) × (BitVec num_elem)) Unit)) )
    : SailME (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) Nat )
  let end_element ← do (get_end_element ())
  let mask_ag ← (( do (get_vtype_vma ()) ) : SailME
    (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) agtype )
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailME
    (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) (BitVec num_elem) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailME
    (Result ((BitVec num_elem) × (BitVec num_elem)) Unit) (BitVec num_elem) )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  assert (num_elem ≥b real_num_elem) "riscv_insts_vext_utils.sail:386.34-386.35"
  let (mask, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := (mask, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mask, result) := loop_vars
      loop_vars :=
        let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
          if ((i <b start_element) : Bool)
          then
            (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
            let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
            (mask, result))
          else
            (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
              if ((i >b end_element) : Bool)
              then
                (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
                let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                (mask, result))
              else
                (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
                  if ((i ≥b real_num_elem) : Bool)
                  then
                    (let result : (BitVec num_elem) :=
                      (BitVec.update result i (BitVec.access vd_val i))
                    let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                    (mask, result))
                  else
                    (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
                      if (((BitVec.access vm_val i) == 0#1) : Bool)
                      then
                        (let result : (BitVec num_elem) :=
                          (BitVec.update result i
                            (match mask_ag with
                            | UNDISTURBED => (BitVec.access vd_val i)
                            | AGNOSTIC => (BitVec.access vd_val i)))
                        let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                        (mask, result))
                      else
                        (let mask : (BitVec num_elem) := (BitVec.update mask i 1#1)
                        (mask, result))
                    (mask, result))
                (mask, result))
            (mask, result))
        (mask, result)
    (pure loop_vars) ) : SailME (Result ((BitVec num_elem) × (BitVec num_elem)) Unit)
    ((BitVec num_elem) × (BitVec num_elem)) )
  (pure (Ok (result, mask)))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, LMUL_pow : Int, nf : Nat, num_elem
  ≥ 0 ∧ is_sew_bitsize(SEW) ∧ nfields_range(nf) -/
def read_vreg_seg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (nf : Nat) (vrid : vregidx) : SailM (Vector (BitVec (nf * SEW)) num_elem) := do
  let LMUL_reg : Int :=
    if ((LMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i LMUL_pow)
  let vreg_list : (Vector (Vector (BitVec SEW) num_elem) nf) :=
    (vectorInit (vectorInit (zeros (n := SEW))))
  let result : (Vector (BitVec (nf * SEW)) num_elem) :=
    (vectorInit (zeros (n := ((Vector.length vreg_list) *i SEW))))
  let vreg_list ← (( do
    let loop_j_lower := 0
    let loop_j_upper := (nf -i 1)
    let mut loop_vars := vreg_list
    for j in [loop_j_lower:loop_j_upper:1]i do
      let vreg_list := loop_vars
      loop_vars ← do
        (pure (vectorUpdate vreg_list j
            (← (read_vreg num_elem SEW LMUL_pow
                (vregidx_offset vrid (to_bits_unsafe (l := 5) (j *i LMUL_reg)))))))
    (pure loop_vars) ) : SailM (Vector (Vector (BitVec SEW) num_elem) nf) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars_1 := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars_1
    loop_vars_1 ← do
      let result : (Vector (BitVec (nf * SEW)) num_elem) :=
        (vectorUpdate result i (zeros (n := ((Vector.length vreg_list) *i SEW))))
      let loop_j_lower := 0
      let loop_j_upper := (nf -i 1)
      let mut loop_vars_2 := result
      for j in [loop_j_lower:loop_j_upper:1]i do
        let result := loop_vars_2
        loop_vars_2 :=
          (vectorUpdate result i
            ((GetElem?.getElem! result i) ||| (shiftl
                (zero_extend (m := ((Vector.length vreg_list) *i SEW))
                  (GetElem?.getElem! (GetElem?.getElem! vreg_list j) i)) (j *i SEW))))
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: SEW : Nat, k_n : Nat, k_n ≥ 0, 0 ≤ k_n, SEW ∈ {8, 16, 32, 64} -/
def get_shift_amount (bit_val : (BitVec k_n)) (SEW : Nat) : SailM Nat := do
  let lowlog2bits := (log2 SEW)
  assert ((0 <b lowlog2bits) && (lowlog2bits <b (Sail.BitVec.length bit_val))) "riscv_insts_vext_utils.sail:444.43-444.44"
  (pure (BitVec.toNat (Sail.BitVec.extractLsb bit_val (lowlog2bits -i 1) 0)))

/-- Type quantifiers: k_m : Nat, shift_amount : Nat, k_m > 0 ∧ shift_amount ≥ 0 -/
def get_fixed_rounding_incr (vec_elem : (BitVec k_m)) (shift_amount : Nat) : SailM (BitVec 1) := do
  if ((shift_amount == 0) : Bool)
  then (pure (0b0 : (BitVec 1)))
  else
    (do
      let rounding_mode ← do (pure (_get_Vcsr_vxrm (← readReg vcsr)))
      assert (shift_amount <b (Sail.BitVec.length vec_elem)) "riscv_insts_vext_utils.sail:455.28-455.29"
      let b__0 := rounding_mode
      if ((b__0 == (0b00 : (BitVec 2))) : Bool)
      then (bit_to_bits (BitVec.access vec_elem (shift_amount -i 1)))
      else
        (if ((b__0 == (0b01 : (BitVec 2))) : Bool)
        then
          (pure (bool_to_bits
              (((BitVec.access vec_elem (shift_amount -i 1)) == 1#1) && ((if ((shift_amount == 1) : Bool)
                  then false
                  else
                    ((Sail.BitVec.extractLsb vec_elem (shift_amount -i 2) 0) != (zeros
                        (n := (((shift_amount -i 2) -i 0) +i 1))))) || ((BitVec.access vec_elem
                      shift_amount) == 1#1)))))
        else
          (if ((b__0 == (0b10 : (BitVec 2))) : Bool)
          then (pure (0b0 : (BitVec 1)))
          else
            (pure (bool_to_bits
                ((bne (BitVec.access vec_elem shift_amount) 1#1) && ((Sail.BitVec.extractLsb
                      vec_elem (shift_amount -i 1) 0) != (zeros
                      (n := (((shift_amount -i 1) -i 0) +i 1))))))))))

/-- Type quantifiers: len : Nat, k_n : Nat, k_n ≥ len ∧ len > 1 -/
def unsigned_saturation (len : Nat) (elem : (BitVec k_n)) : SailM (BitVec len) := do
  if (((BitVec.toNat elem) >b (BitVec.toNat (ones (n := len)))) : Bool)
  then
    (do
      writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 (0b1 : (BitVec 1)))
      (pure (ones (n := len))))
  else (pure (Sail.BitVec.extractLsb elem (len -i 1) 0))

/-- Type quantifiers: len : Nat, k_n : Nat, k_n ≥ len ∧ len > 1 -/
def signed_saturation (len : Nat) (elem : (BitVec k_n)) : SailM (BitVec len) := do
  if (((BitVec.toInt elem) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := (len -i 1)))))) : Bool)
  then
    (do
      writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 (0b1 : (BitVec 1)))
      (pure ((0b0 : (BitVec 1)) ++ (ones (n := (len -i 1))))))
  else
    (do
      if (((BitVec.toInt elem) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros (n := (len -i 1)))))) : Bool)
      then
        (do
          writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 (0b1 : (BitVec 1)))
          (pure ((0b1 : (BitVec 1)) ++ (zeros (n := (len -i 1))))))
      else (pure (Sail.BitVec.extractLsb elem (len -i 1) 0)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, k_n ≥ 0 ∧ m ≥ 0 -/
def vrev8 {m : _} (input : (Vector (BitVec (m * 8)) k_n)) : (Vector (BitVec (m * 8)) k_n) := Id.run do
  let output : (Vector (BitVec (m * 8)) k_n) := input
  let loop_i_lower := 0
  let loop_i_upper := ((Vector.length output) -i 1)
  let mut loop_vars := output
  for i in [loop_i_lower:loop_i_upper:1]i do
    let output := loop_vars
    loop_vars := (vectorUpdate output i (rev8 (GetElem?.getElem! input i)))
  (pure loop_vars)

