import LeanRV64D.Prelude

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

def riscv_f16Add (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Add rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f16Sub (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Sub rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f16Mul (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Mul rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f16Div (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Div rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f32Add (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Add rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f32Sub (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Sub rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f32Mul (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Mul rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f32Div (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Div rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f64Add (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Add rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f64Sub (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Sub rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f64Mul (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Mul rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f64Div (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Div rm v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f16MulAdd (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) (v3 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16MulAdd rm v1 v2 v3)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f32MulAdd (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) (v3 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32MulAdd rm v1 v2 v3)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f64MulAdd (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) (v3 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64MulAdd rm v1 v2 v3)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f16Sqrt (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Sqrt rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f32Sqrt (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Sqrt rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f64Sqrt (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Sqrt rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f16ToI32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToI32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f16ToUi32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToUi32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_i32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_i32ToF16 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_ui32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_ui32ToF16 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f16ToI64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToI64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f16ToUi64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToUi64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_i64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_i64ToF16 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_ui64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_ui64ToF16 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f32ToI32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32ToI32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f32ToUi32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32ToUi32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_i32ToF32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_i32ToF32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_ui32ToF32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_ui32ToF32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f32ToI64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToI64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f32ToUi64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToUi64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_i64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_i64ToF32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_ui64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_ui64ToF32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f64ToI32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToI32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f64ToUi32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToUi32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_i32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_i32ToF64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_ui32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_ui32ToF64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f64ToI64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64ToI64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f64ToUi64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64ToUi64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_i64ToF64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_i64ToF64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_ui64ToF64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_ui64ToF64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f16ToF32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToF32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f16ToF64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToF64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToF64 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

def riscv_f32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f32ToF16 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f64ToF16 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

def riscv_f64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToF32 rm v)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

def riscv_f16Lt (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Lt v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f16Lt_quiet (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Lt_quiet v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f16Le (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Le v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f16Le_quiet (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Le_quiet v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f16Eq (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Eq v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f32Lt (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Lt v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f32Lt_quiet (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Lt_quiet v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f32Le (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Le v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f32Le_quiet (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Le_quiet v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f32Eq (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Eq v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f64Lt (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Lt v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f64Lt_quiet (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Lt_quiet v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f64Le (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Le v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f64Le_quiet (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Le_quiet v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

def riscv_f64Eq (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Eq v1 v2)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← (bit_to_bool
        (BitVec.access (← readReg float_result) 0)))))

/-- Type quantifiers: k_ex371994# : Bool -/
def riscv_f16roundToInt (rm : (BitVec 3)) (v : (BitVec 16)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16roundToInt rm v exact)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 15 0)))

/-- Type quantifiers: k_ex371998# : Bool -/
def riscv_f32roundToInt (rm : (BitVec 3)) (v : (BitVec 32)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32roundToInt rm v exact)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (Sail.BitVec.extractLsb
      (← readReg float_result) 31 0)))

/-- Type quantifiers: k_ex372002# : Bool -/
def riscv_f64roundToInt (rm : (BitVec 3)) (v : (BitVec 64)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64roundToInt rm v exact)
  (pure ((Sail.BitVec.extractLsb (← readReg float_fflags) 4 0), (← readReg float_result)))

