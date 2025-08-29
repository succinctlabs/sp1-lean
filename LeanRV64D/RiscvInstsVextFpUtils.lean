import LeanRV64D.Prelude
import LeanRV64D.RiscvFlen
import LeanRV64D.RiscvVlen
import LeanRV64D.RiscvSoftfloatInterface
import LeanRV64D.RiscvFdextRegs
import LeanRV64D.RiscvVextRegs
import LeanRV64D.RiscvInstsFext
import LeanRV64D.RiscvInstsDext
import LeanRV64D.RiscvInstsZfh
import LeanRV64D.RiscvInstsVextUtils

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

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def valid_fp_op (SEW : Nat) (rm_3b : (BitVec 3)) : Bool :=
  let valid_sew := ((SEW ≥b 16) && (SEW ≤b 128))
  let valid_rm :=
    (not
      ((rm_3b == (0b101 : (BitVec 3))) || ((rm_3b == (0b110 : (BitVec 3))) || (rm_3b == (0b111 : (BitVec 3))))))
  (valid_sew && valid_rm)

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_normal (vd : vregidx) (vm : (BitVec 1)) (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || (not
          (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_vd_masked (vd : vregidx) (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((vd == zvreg) || (not (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_vd_unmasked (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (not (valid_fp_op SEW rm_3b))))

/-- Type quantifiers: LMUL_pow_new : Int, SEW_new : Int, SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_variable_width (vd : vregidx) (vm : (BitVec 1)) (SEW : Nat) (rm_3b : (BitVec 3)) (SEW_new : Int) (LMUL_pow_new : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || ((not
            (valid_fp_op SEW rm_3b)) || (not (valid_eew_emul SEW_new LMUL_pow_new))))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_reduction (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (← (assert_vstart 0))) || (not
          (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: EEW : Int, SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_widening_reduction (SEW : Nat) (rm_3b : (BitVec 3)) (EEW : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (← (assert_vstart 0))) || ((not
            (valid_fp_op SEW rm_3b)) || (not ((EEW ≥b 8) && (EEW ≤b elen)))))))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_neg_inf (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_inf_H xf)
  | 32 => (f_is_neg_inf_S xf)
  | _ => (f_is_neg_inf_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_neg_norm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_norm_H xf)
  | 32 => (f_is_neg_norm_S xf)
  | _ => (f_is_neg_norm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_neg_subnorm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_subnorm_H xf)
  | 32 => (f_is_neg_subnorm_S xf)
  | _ => (f_is_neg_subnorm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_neg_zero (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_zero_H xf)
  | 32 => (f_is_neg_zero_S xf)
  | _ => (f_is_neg_zero_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_pos_zero (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_zero_H xf)
  | 32 => (f_is_pos_zero_S xf)
  | _ => (f_is_pos_zero_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_pos_subnorm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_subnorm_H xf)
  | 32 => (f_is_pos_subnorm_S xf)
  | _ => (f_is_pos_subnorm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_pos_norm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_norm_H xf)
  | 32 => (f_is_pos_norm_S xf)
  | _ => (f_is_pos_norm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_pos_inf (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_inf_H xf)
  | 32 => (f_is_pos_inf_S xf)
  | _ => (f_is_pos_inf_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_SNaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_SNaN_H xf)
  | 32 => (f_is_SNaN_S xf)
  | _ => (f_is_SNaN_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_QNaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_QNaN_H xf)
  | 32 => (f_is_QNaN_S xf)
  | _ => (f_is_QNaN_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def f_is_NaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_NaN_H xf)
  | 32 => (f_is_NaN_S xf)
  | _ => (f_is_NaN_D xf)

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, SEW ∈ {16, 32, 64} -/
def get_scalar_fp (rs1 : fregidx) (SEW : Nat) : SailM (BitVec SEW) := do
  assert (flen ≥b SEW) "invalid vector floating-point type width: FLEN < SEW"
  match SEW with
  | 16 => (rF_H rs1)
  | 32 => (rF_S rs1)
  | _ => (rF_D rs1)

def get_fp_rounding_mode (_ : Unit) : SailM rounding_mode := do
  (encdec_rounding_mode_backwards (_get_Fcsr_FRM (← readReg fcsr)))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def negate_fp (xf : (BitVec k_m)) : (BitVec k_m) :=
  match (Sail.BitVec.length xf) with
  | 16 => (negate_H xf)
  | 32 => (negate_S xf)
  | _ => (negate_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_add (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Add rm_3b op1 op2)
    | 32 => (riscv_f32Add rm_3b op1 op2)
    | _ => (riscv_f64Add rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_sub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Sub rm_3b op1 op2)
    | 32 => (riscv_f32Sub rm_3b op1 op2)
    | _ => (riscv_f64Sub rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_min (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, op1_lt_op2) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt_quiet op1 op2)
    | 32 => (riscv_f32Lt_quiet op1 op2)
    | _ => (riscv_f64Lt_quiet op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if (((f_is_NaN op1) && (f_is_NaN op2)) : Bool)
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      (if ((f_is_NaN op1) : Bool)
      then op2
      else
        (if ((f_is_NaN op2) : Bool)
        then op1
        else
          (if (((f_is_neg_zero op1) && (f_is_pos_zero op2)) : Bool)
          then op1
          else
            (if (((f_is_neg_zero op2) && (f_is_pos_zero op1)) : Bool)
            then op2
            else
              (if (op1_lt_op2 : Bool)
              then op1
              else op2)))))
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_max (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, op1_lt_op2) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt_quiet op1 op2)
    | 32 => (riscv_f32Lt_quiet op1 op2)
    | _ => (riscv_f64Lt_quiet op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if (((f_is_NaN op1) && (f_is_NaN op2)) : Bool)
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      (if ((f_is_NaN op1) : Bool)
      then op2
      else
        (if ((f_is_NaN op2) : Bool)
        then op1
        else
          (if (((f_is_neg_zero op1) && (f_is_pos_zero op2)) : Bool)
          then op2
          else
            (if (((f_is_neg_zero op2) && (f_is_pos_zero op1)) : Bool)
            then op1
            else
              (if (op1_lt_op2 : Bool)
              then op2
              else op1)))))
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_eq (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Eq op1 op2)
    | 32 => (riscv_f32Eq op1 op2)
    | _ => (riscv_f64Eq op1 op2) ) : SailM (bits_fflags × Bool) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_gt (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, temp_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Le op1 op2)
    | 32 => (riscv_f32Le op1 op2)
    | _ => (riscv_f64Le op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if ((fflags == (0b10000 : (BitVec 5))) : Bool)
    then false
    else (not temp_val)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_ge (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, temp_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt op1 op2)
    | 32 => (riscv_f32Lt op1 op2)
    | _ => (riscv_f64Lt op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if ((fflags == (0b10000 : (BitVec 5))) : Bool)
    then false
    else (not temp_val)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_lt (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt op1 op2)
    | 32 => (riscv_f32Lt op1 op2)
    | _ => (riscv_f64Lt op1 op2) ) : SailM (bits_fflags × Bool) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_le (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Le op1 op2)
    | 32 => (riscv_f32Le op1 op2)
    | _ => (riscv_f64Le op1 op2) ) : SailM (bits_fflags × Bool) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_mul (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Mul rm_3b op1 op2)
    | 32 => (riscv_f32Mul rm_3b op1 op2)
    | _ => (riscv_f64Mul rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_div (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Div rm_3b op1 op2)
    | 32 => (riscv_f32Div rm_3b op1 op2)
    | _ => (riscv_f64Div rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_muladd (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opadd : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opadd) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opadd)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opadd)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opadd) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_nmuladd (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opadd : (BitVec k_m)) : SailM (BitVec k_m) := do
  let op1 := (negate_fp op1)
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opadd) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opadd)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opadd)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opadd) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_mulsub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opsub : (BitVec k_m)) : SailM (BitVec k_m) := do
  let opsub := (negate_fp opsub)
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opsub) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opsub)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opsub)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opsub) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_nmulsub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opsub : (BitVec k_m)) : SailM (BitVec k_m) := do
  let opsub := (negate_fp opsub)
  let op1 := (negate_fp op1)
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opsub) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opsub)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opsub)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opsub) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def fp_class (xf : (BitVec k_m)) : (BitVec k_m) :=
  let result_val_10b : (BitVec 10) :=
    if ((f_is_neg_inf xf) : Bool)
    then (0b0000000001 : (BitVec 10))
    else
      (if ((f_is_neg_norm xf) : Bool)
      then (0b0000000010 : (BitVec 10))
      else
        (if ((f_is_neg_subnorm xf) : Bool)
        then (0b0000000100 : (BitVec 10))
        else
          (if ((f_is_neg_zero xf) : Bool)
          then (0b0000001000 : (BitVec 10))
          else
            (if ((f_is_pos_zero xf) : Bool)
            then (0b0000010000 : (BitVec 10))
            else
              (if ((f_is_pos_subnorm xf) : Bool)
              then (0b0000100000 : (BitVec 10))
              else
                (if ((f_is_pos_norm xf) : Bool)
                then (0b0001000000 : (BitVec 10))
                else
                  (if ((f_is_pos_inf xf) : Bool)
                  then (0b0010000000 : (BitVec 10))
                  else
                    (if ((f_is_SNaN xf) : Bool)
                    then (0b0100000000 : (BitVec 10))
                    else
                      (if ((f_is_QNaN xf) : Bool)
                      then (0b1000000000 : (BitVec 10))
                      else (zeros (n := 10)))))))))))
  (zero_extend (m := (Sail.BitVec.length xf)) result_val_10b)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32} -/
def fp_widen (nval : (BitVec k_m)) : SailM (BitVec (k_m * 2)) := do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let (fflags, wval) ← (( do
    match (Sail.BitVec.length nval) with
    | 16 => (riscv_f16ToF32 rm_3b nval)
    | _ => (riscv_f32ToF64 rm_3b nval) ) : SailM (bits_fflags × (BitVec (k_m * 2))) )
  (accrue_fflags fflags)
  (pure wval)

def riscv_f16ToI16 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (flag, sig32) ← do (riscv_f16ToI32 rm v)
  if (((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 15))))) : Bool)
  then (pure ((nvFlag ()), ((0b0 : (BitVec 1)) ++ (ones (n := 15)))))
  else
    (if (((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros (n := 15))))) : Bool)
    then (pure ((nvFlag ()), ((0b1 : (BitVec 1)) ++ (zeros (n := 15)))))
    else (pure (flag, (Sail.BitVec.extractLsb sig32 15 0))))

def riscv_f16ToI8 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 8)) := do
  let (flag, sig32) ← do (riscv_f16ToI32 rm v)
  if (((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 7))))) : Bool)
  then (pure ((nvFlag ()), ((0b0 : (BitVec 1)) ++ (ones (n := 7)))))
  else
    (if (((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros (n := 7))))) : Bool)
    then (pure ((nvFlag ()), ((0b1 : (BitVec 1)) ++ (zeros (n := 7)))))
    else (pure (flag, (Sail.BitVec.extractLsb sig32 7 0))))

def riscv_f32ToI16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (flag, sig32) ← do (riscv_f32ToI32 rm v)
  if (((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 15))))) : Bool)
  then (pure ((nvFlag ()), ((0b0 : (BitVec 1)) ++ (ones (n := 15)))))
  else
    (if (((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros (n := 15))))) : Bool)
    then (pure ((nvFlag ()), ((0b1 : (BitVec 1)) ++ (zeros (n := 15)))))
    else (pure (flag, (Sail.BitVec.extractLsb sig32 15 0))))

def riscv_f16ToUi16 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (flag, sig32) ← do (riscv_f16ToUi32 rm v)
  if (((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 16)))) : Bool)
  then (pure ((nvFlag ()), (ones (n := 16))))
  else (pure (flag, (Sail.BitVec.extractLsb sig32 15 0)))

def riscv_f16ToUi8 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 8)) := do
  let (flag, sig32) ← do (riscv_f16ToUi32 rm v)
  if (((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 8)))) : Bool)
  then (pure ((nvFlag ()), (ones (n := 8))))
  else (pure (flag, (Sail.BitVec.extractLsb sig32 7 0)))

def riscv_f32ToUi16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (flag, sig32) ← do (riscv_f32ToUi32 rm v)
  if (((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 16)))) : Bool)
  then (pure ((nvFlag ()), (ones (n := 16))))
  else (pure (flag, (Sail.BitVec.extractLsb sig32 15 0)))

/-- Type quantifiers: k_ex378742# : Bool, k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def rsqrt7 (v : (BitVec k_m)) (sub : Bool) : SailM (BitVec 64) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Int × Int) :=
    match (Sail.BitVec.length v) with
    | 16 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 14 10)), (BitVec.join1 [(BitVec.access v 15)]), 5, 10)
    | 32 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 30 23)), (BitVec.join1 [(BitVec.access v 31)]), 8, 23)
    | _ =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 62 52)), (BitVec.join1 [(BitVec.access v 63)]), 11, 52)
  let table : (Vector Int 128) :=
    #v[53, 54, 55, 56, 56, 57, 58, 59, 59, 60, 61, 62, 63, 63, 64, 65, 66, 67, 68, 69, 70, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 99, 100, 102, 103, 105, 106, 108, 109, 111, 113, 114, 116, 118, 119, 121, 123, 125, 127, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10, 11, 12, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 22, 23, 23, 24, 25, 26, 27, 28, 29, 30, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 50, 51, 52]
  let (normalized_exp, normalized_sig) ← do
    if (sub : Bool)
    then
      (do
        let nr_leadingzeros := (BitVec.countLeadingZeros (Sail.BitVec.extractLsb sig (s -i 1) 0))
        assert (nr_leadingzeros ≥b 0) "riscv_insts_vext_fp_utils.sail:479.35-479.36"
        (pure ((to_bits_unsafe (l := 64) (0 -i nr_leadingzeros)), (zero_extend (m := 64)
            (shiftl (Sail.BitVec.extractLsb sig (s -i 1) 0) (1 +i nr_leadingzeros))))))
    else (pure (exp, sig))
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 =>
      (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            9 4)))
    | 32 =>
      (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            22 17)))
    | _ =>
      (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            51 46)))
  assert ((idx ≥b 0) && (idx <b 128)) "riscv_insts_vext_fp_utils.sail:490.29-490.30"
  let out_sig := (shiftl (to_bits_unsafe (l := s) (GetElem?.getElem! table (127 -i idx))) (s -i 7))
  let out_exp :=
    (to_bits_unsafe (l := e)
      (Int.tdiv (((3 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)) 2))
  (pure (zero_extend (m := 64) (sign ++ (out_exp ++ out_sig))))

def riscv_f16Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let b__0 := (fp_class v)
  if ((b__0 == (0x0001 : (BitVec 16))) : Bool)
  then (pure ((nvFlag ()), (0x7E00 : (BitVec 16))))
  else
    (do
      if ((b__0 == (0x0002 : (BitVec 16))) : Bool)
      then (pure ((nvFlag ()), (0x7E00 : (BitVec 16))))
      else
        (do
          if ((b__0 == (0x0004 : (BitVec 16))) : Bool)
          then (pure ((nvFlag ()), (0x7E00 : (BitVec 16))))
          else
            (do
              if ((b__0 == (0x0100 : (BitVec 16))) : Bool)
              then (pure ((nvFlag ()), (0x7E00 : (BitVec 16))))
              else
                (do
                  if ((b__0 == (0x0200 : (BitVec 16))) : Bool)
                  then (pure ((zeros (n := 5)), (0x7E00 : (BitVec 16))))
                  else
                    (do
                      if ((b__0 == (0x0008 : (BitVec 16))) : Bool)
                      then (pure ((dzFlag ()), (0xFC00 : (BitVec 16))))
                      else
                        (do
                          if ((b__0 == (0x0010 : (BitVec 16))) : Bool)
                          then (pure ((dzFlag ()), (0x7C00 : (BitVec 16))))
                          else
                            (do
                              if ((b__0 == (0x0080 : (BitVec 16))) : Bool)
                              then (pure ((zeros (n := 5)), (0x0000 : (BitVec 16))))
                              else
                                (do
                                  if ((b__0 == (0x0020 : (BitVec 16))) : Bool)
                                  then
                                    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb
                                        (← (rsqrt7 v true)) 15 0)))
                                  else
                                    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb
                                        (← (rsqrt7 v false)) 15 0)))))))))))

def riscv_f32Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if ((b__0 == (0x0001 : (BitVec 16))) : Bool)
  then (pure ((nvFlag ()), (0x7FC00000 : (BitVec 32))))
  else
    (do
      if ((b__0 == (0x0002 : (BitVec 16))) : Bool)
      then (pure ((nvFlag ()), (0x7FC00000 : (BitVec 32))))
      else
        (do
          if ((b__0 == (0x0004 : (BitVec 16))) : Bool)
          then (pure ((nvFlag ()), (0x7FC00000 : (BitVec 32))))
          else
            (do
              if ((b__0 == (0x0100 : (BitVec 16))) : Bool)
              then (pure ((nvFlag ()), (0x7FC00000 : (BitVec 32))))
              else
                (do
                  if ((b__0 == (0x0200 : (BitVec 16))) : Bool)
                  then (pure ((zeros (n := 5)), (0x7FC00000 : (BitVec 32))))
                  else
                    (do
                      if ((b__0 == (0x0008 : (BitVec 16))) : Bool)
                      then (pure ((dzFlag ()), (0xFF800000 : (BitVec 32))))
                      else
                        (do
                          if ((b__0 == (0x0010 : (BitVec 16))) : Bool)
                          then (pure ((dzFlag ()), (0x7F800000 : (BitVec 32))))
                          else
                            (do
                              if ((b__0 == (0x0080 : (BitVec 16))) : Bool)
                              then (pure ((zeros (n := 5)), (0x00000000 : (BitVec 32))))
                              else
                                (do
                                  if ((b__0 == (0x0020 : (BitVec 16))) : Bool)
                                  then
                                    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb
                                        (← (rsqrt7 v true)) 31 0)))
                                  else
                                    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb
                                        (← (rsqrt7 v false)) 31 0)))))))))))

def riscv_f64Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if ((b__0 == (0x0001 : (BitVec 16))) : Bool)
  then (pure ((nvFlag ()), (0x7FF8000000000000 : (BitVec 64))))
  else
    (do
      if ((b__0 == (0x0002 : (BitVec 16))) : Bool)
      then (pure ((nvFlag ()), (0x7FF8000000000000 : (BitVec 64))))
      else
        (do
          if ((b__0 == (0x0004 : (BitVec 16))) : Bool)
          then (pure ((nvFlag ()), (0x7FF8000000000000 : (BitVec 64))))
          else
            (do
              if ((b__0 == (0x0100 : (BitVec 16))) : Bool)
              then (pure ((nvFlag ()), (0x7FF8000000000000 : (BitVec 64))))
              else
                (do
                  if ((b__0 == (0x0200 : (BitVec 16))) : Bool)
                  then (pure ((zeros (n := 5)), (0x7FF8000000000000 : (BitVec 64))))
                  else
                    (do
                      if ((b__0 == (0x0008 : (BitVec 16))) : Bool)
                      then (pure ((dzFlag ()), (0xFFF0000000000000 : (BitVec 64))))
                      else
                        (do
                          if ((b__0 == (0x0010 : (BitVec 16))) : Bool)
                          then (pure ((dzFlag ()), (0x7FF0000000000000 : (BitVec 64))))
                          else
                            (do
                              if ((b__0 == (0x0080 : (BitVec 16))) : Bool)
                              then (pure ((zeros (n := 5)), (zeros (n := 64))))
                              else
                                (do
                                  if ((b__0 == (0x0020 : (BitVec 16))) : Bool)
                                  then
                                    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb
                                        (← (rsqrt7 v true)) 63 0)))
                                  else
                                    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb
                                        (← (rsqrt7 v false)) 63 0)))))))))))

/-- Type quantifiers: k_ex378978# : Bool, k_m : Nat, k_m ≥ 0, k_m ∈ {16, 32, 64} -/
def recip7 (v : (BitVec k_m)) (rm_3b : (BitVec 3)) (sub : Bool) : SailM (Bool × (BitVec 64)) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Int × Int) :=
    match (Sail.BitVec.length v) with
    | 16 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 14 10)), (BitVec.join1 [(BitVec.access v 15)]), 5, 10)
    | 32 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 30 23)), (BitVec.join1 [(BitVec.access v 31)]), 8, 23)
    | _ =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 62 52)), (BitVec.join1 [(BitVec.access v 63)]), 11, 52)
  let table : (Vector Int 128) :=
    #v[0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 15, 16, 17, 17, 18, 19, 19, 20, 21, 21, 22, 23, 23, 24, 25, 25, 26, 27, 28, 28, 29, 30, 31, 31, 32, 33, 34, 35, 35, 36, 37, 38, 39, 40, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 74, 75, 76, 77, 79, 80, 81, 83, 84, 85, 87, 88, 90, 91, 93, 94, 96, 97, 99, 100, 102, 104, 105, 107, 109, 110, 112, 114, 116, 117, 119, 121, 123, 125, 127]
  let nr_leadingzeros := (BitVec.countLeadingZeros (Sail.BitVec.extractLsb sig (s -i 1) 0))
  assert (nr_leadingzeros ≥b 0) "riscv_insts_vext_fp_utils.sail:570.29-570.30"
  let (normalized_exp, normalized_sig) :=
    if (sub : Bool)
    then
      ((to_bits_unsafe (l := 64) (0 -i nr_leadingzeros)), (zero_extend (m := 64)
        (shiftl (Sail.BitVec.extractLsb sig (s -i 1) 0) (1 +i nr_leadingzeros))))
    else (exp, sig)
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 => (BitVec.toNat (Sail.BitVec.extractLsb normalized_sig 9 3))
    | 32 => (BitVec.toNat (Sail.BitVec.extractLsb normalized_sig 22 16))
    | _ => (BitVec.toNat (Sail.BitVec.extractLsb normalized_sig 51 45))
  assert ((idx ≥b 0) && (idx <b 128)) "riscv_insts_vext_fp_utils.sail:583.29-583.30"
  let mid_exp :=
    (to_bits_unsafe (l := e) (((2 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)))
  let mid_sig := (shiftl (to_bits_unsafe (l := s) (GetElem?.getElem! table (127 -i idx))) (s -i 7))
  let (out_exp, out_sig) :=
    if ((mid_exp == (zeros (n := e))) : Bool)
    then (mid_exp, ((shiftr mid_sig 1) ||| ((0b1 : (BitVec 1)) ++ (zeros (n := (s -i 1))))))
    else
      (if ((mid_exp == (ones (n := e))) : Bool)
      then
        ((zeros (n := e)), ((shiftr mid_sig 2) ||| ((0b01 : (BitVec 2)) ++ (zeros (n := (s -i 2))))))
      else (mid_exp, mid_sig))
  if ((sub && (nr_leadingzeros >b 1)) : Bool)
  then
    (if (((rm_3b == (0b001 : (BitVec 3))) || (((rm_3b == (0b010 : (BitVec 3))) && (sign == (0b0 : (BitVec 1)))) || ((rm_3b == (0b011 : (BitVec 3))) && (sign == (0b1 : (BitVec 1)))))) : Bool)
    then
      (pure (true, (zero_extend (m := 64)
          (sign ++ ((ones (n := (e -i 1))) ++ ((0b0 : (BitVec 1)) ++ (ones (n := s))))))))
    else (pure (true, (zero_extend (m := 64) (sign ++ ((ones (n := e)) ++ (zeros (n := s))))))))
  else (pure (false, (zero_extend (m := 64) (sign ++ (out_exp ++ out_sig)))))

def riscv_f16Recip7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (fp_class v)
  if ((b__0 == (0x0001 : (BitVec 16))) : Bool)
  then (pure ((zeros (n := 5)), (0x8000 : (BitVec 16))))
  else
    (if ((b__0 == (0x0080 : (BitVec 16))) : Bool)
    then (pure ((zeros (n := 5)), (0x0000 : (BitVec 16))))
    else
      (if ((b__0 == (0x0008 : (BitVec 16))) : Bool)
      then (pure ((dzFlag ()), (0xFC00 : (BitVec 16))))
      else
        (if ((b__0 == (0x0010 : (BitVec 16))) : Bool)
        then (pure ((dzFlag ()), (0x7C00 : (BitVec 16))))
        else
          (if ((b__0 == (0x0100 : (BitVec 16))) : Bool)
          then (pure ((nvFlag ()), (0x7E00 : (BitVec 16))))
          else
            (if ((b__0 == (0x0200 : (BitVec 16))) : Bool)
            then (pure ((zeros (n := 5)), (0x7E00 : (BitVec 16))))
            else
              (if ((b__0 == (0x0004 : (BitVec 16))) : Bool)
              then
                (if (round_abnormal_true : Bool)
                then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 15 0)))
                else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 15 0))))
              else
                (if ((b__0 == (0x0020 : (BitVec 16))) : Bool)
                then
                  (if (round_abnormal_true : Bool)
                  then
                    (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 15 0)))
                  else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 15 0))))
                else
                  (if (round_abnormal_false : Bool)
                  then
                    (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_false 15 0)))
                  else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_false 15 0)))))))))))

def riscv_f32Recip7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if ((b__0 == (0x0001 : (BitVec 16))) : Bool)
  then (pure ((zeros (n := 5)), (0x80000000 : (BitVec 32))))
  else
    (if ((b__0 == (0x0080 : (BitVec 16))) : Bool)
    then (pure ((zeros (n := 5)), (0x00000000 : (BitVec 32))))
    else
      (if ((b__0 == (0x0008 : (BitVec 16))) : Bool)
      then (pure ((dzFlag ()), (0xFF800000 : (BitVec 32))))
      else
        (if ((b__0 == (0x0010 : (BitVec 16))) : Bool)
        then (pure ((dzFlag ()), (0x7F800000 : (BitVec 32))))
        else
          (if ((b__0 == (0x0100 : (BitVec 16))) : Bool)
          then (pure ((nvFlag ()), (0x7FC00000 : (BitVec 32))))
          else
            (if ((b__0 == (0x0200 : (BitVec 16))) : Bool)
            then (pure ((zeros (n := 5)), (0x7FC00000 : (BitVec 32))))
            else
              (if ((b__0 == (0x0004 : (BitVec 16))) : Bool)
              then
                (if (round_abnormal_true : Bool)
                then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 31 0)))
                else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 31 0))))
              else
                (if ((b__0 == (0x0020 : (BitVec 16))) : Bool)
                then
                  (if (round_abnormal_true : Bool)
                  then
                    (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 31 0)))
                  else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 31 0))))
                else
                  (if (round_abnormal_false : Bool)
                  then
                    (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_false 31 0)))
                  else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_false 31 0)))))))))))

def riscv_f64Recip7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if ((b__0 == (0x0001 : (BitVec 16))) : Bool)
  then (pure ((zeros (n := 5)), (0x8000000000000000 : (BitVec 64))))
  else
    (if ((b__0 == (0x0080 : (BitVec 16))) : Bool)
    then (pure ((zeros (n := 5)), (0x0000000000000000 : (BitVec 64))))
    else
      (if ((b__0 == (0x0008 : (BitVec 16))) : Bool)
      then (pure ((dzFlag ()), (0xFFF0000000000000 : (BitVec 64))))
      else
        (if ((b__0 == (0x0010 : (BitVec 16))) : Bool)
        then (pure ((dzFlag ()), (0x7FF0000000000000 : (BitVec 64))))
        else
          (if ((b__0 == (0x0100 : (BitVec 16))) : Bool)
          then (pure ((nvFlag ()), (0x7FF8000000000000 : (BitVec 64))))
          else
            (if ((b__0 == (0x0200 : (BitVec 16))) : Bool)
            then (pure ((zeros (n := 5)), (0x7FF8000000000000 : (BitVec 64))))
            else
              (if ((b__0 == (0x0004 : (BitVec 16))) : Bool)
              then
                (if (round_abnormal_true : Bool)
                then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 63 0)))
                else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 63 0))))
              else
                (if ((b__0 == (0x0020 : (BitVec 16))) : Bool)
                then
                  (if (round_abnormal_true : Bool)
                  then
                    (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 63 0)))
                  else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 63 0))))
                else
                  (if (round_abnormal_false : Bool)
                  then
                    (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_false 63 0)))
                  else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_false 63 0)))))))))))

