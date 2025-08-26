import LeanRV64D.Flow
import LeanRV64D.Arith
import LeanRV64D.Prelude
import LeanRV64D.RiscvErrors
import LeanRV64D.RiscvXlen
import LeanRV64D.RiscvVmemTypes
import LeanRV64D.RiscvCallbacks
import LeanRV64D.RiscvVextRegs
import LeanRV64D.RiscvVextControl
import LeanRV64D.RiscvInstRetire
import LeanRV64D.RiscvVmemUtils
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

def vlewidth_bitsnumberstr_backwards (arg_ : String) : SailM vlewidth := do
  match arg_ with
  | "8" => (pure VLE8)
  | "16" => (pure VLE16)
  | "32" => (pure VLE32)
  | "64" => (pure VLE64)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vlewidth_bitsnumberstr_forwards_matches (arg_ : vlewidth) : Bool :=
  match arg_ with
  | VLE8 => true
  | VLE16 => true
  | VLE32 => true
  | VLE64 => true

def vlewidth_bitsnumberstr_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "8" => true
  | "16" => true
  | "32" => true
  | "64" => true
  | _ => false

def encdec_vlewidth_forwards (arg_ : vlewidth) : (BitVec 3) :=
  match arg_ with
  | VLE8 => (0b000 : (BitVec 3))
  | VLE16 => (0b101 : (BitVec 3))
  | VLE32 => (0b110 : (BitVec 3))
  | VLE64 => (0b111 : (BitVec 3))

def encdec_vlewidth_backwards (arg_ : (BitVec 3)) : SailM vlewidth := do
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then (pure VLE8)
  else
    (do
      if ((b__0 == (0b101 : (BitVec 3))) : Bool)
      then (pure VLE16)
      else
        (do
          if ((b__0 == (0b110 : (BitVec 3))) : Bool)
          then (pure VLE32)
          else
            (do
              if ((b__0 == (0b111 : (BitVec 3))) : Bool)
              then (pure VLE64)
              else
                (do
                  assert false "Pattern match failure at unknown location"
                  throw Error.Exit))))

def encdec_vlewidth_forwards_matches (arg_ : vlewidth) : Bool :=
  match arg_ with
  | VLE8 => true
  | VLE16 => true
  | VLE32 => true
  | VLE64 => true

def encdec_vlewidth_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b101 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b110 : (BitVec 3))) : Bool)
      then true
      else
        (if ((b__0 == (0b111 : (BitVec 3))) : Bool)
        then true
        else false)))

def vlewidth_bytesnumber_forwards (arg_ : vlewidth) : Int :=
  match arg_ with
  | VLE8 => 1
  | VLE16 => 2
  | VLE32 => 4
  | VLE64 => 8

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def vlewidth_bytesnumber_backwards (arg_ : Nat) : vlewidth :=
  match arg_ with
  | 1 => VLE8
  | 2 => VLE16
  | 4 => VLE32
  | _ => VLE64

def vlewidth_bytesnumber_forwards_matches (arg_ : vlewidth) : Bool :=
  match arg_ with
  | VLE8 => true
  | VLE16 => true
  | VLE32 => true
  | VLE64 => true

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def vlewidth_bytesnumber_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def vlewidth_pow_forwards (arg_ : vlewidth) : Int :=
  match arg_ with
  | VLE8 => 3
  | VLE16 => 4
  | VLE32 => 5
  | VLE64 => 6

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {3, 4, 5, 6} -/
def vlewidth_pow_backwards (arg_ : Nat) : vlewidth :=
  match arg_ with
  | 3 => VLE8
  | 4 => VLE16
  | 5 => VLE32
  | _ => VLE64

def vlewidth_pow_forwards_matches (arg_ : vlewidth) : Bool :=
  match arg_ with
  | VLE8 => true
  | VLE16 => true
  | VLE32 => true
  | VLE64 => true

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {3, 4, 5, 6} -/
def vlewidth_pow_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | _ => false

/-- Type quantifiers: num_elem : Nat, EMUL_pow : Int, load_width_bytes : Nat, nf : Nat, nf > 0 ∧
  nf ≤ 8, load_width_bytes ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vlseg (nf : Nat) (vm : (BitVec 1)) (vd : vregidx) (load_width_bytes : Nat) (rs1 : regidx) (EMUL_pow : Int) (num_elem : Nat) : SailM ExecutionResult := SailME.run do
  let EMUL_reg :=
    if ((EMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vd_seg ← do (read_vreg_seg num_elem (load_width_bytes *i 8) EMUL_pow nf vd)
  let m := ((nf *i load_width_bytes) *i 8)
  let n := num_elem
  let (result, mask) ← (( do
    match (← (init_masked_result num_elem m EMUL_pow vd_seg vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult ((Vector (BitVec m) n) × (BitVec n)) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access mask i) == 1#1) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_2 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_2
            loop_vars_2 ← do
              let elem_offset := (((i *i nf) +i j) *i load_width_bytes)
              match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) elem_offset) load_width_bytes
                  (Read Data) false false false)) with
              | .Ok elem =>
                (write_single_element (load_width_bytes *i 8) i
                  (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) elem)
              | .Err e => SailME.throw (e : ExecutionResult)
          (pure loop_vars_2))
      else
        (do
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_1 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let skipped_elem :=
                (Sail.BitVec.extractLsb
                  (shiftr (GetElem?.getElem! result i) ((j *i load_width_bytes) *i 8))
                  ((load_width_bytes *i 8) -i 1) 0)
              (write_single_element (load_width_bytes *i 8) i
                (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) skipped_elem)
          (pure loop_vars_1))
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: num_elem : Nat, EMUL_pow : Int, load_width_bytes : Nat, nf : Nat, nf > 0 ∧
  nf ≤ 8, load_width_bytes ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vlsegff (nf : Nat) (vm : (BitVec 1)) (vd : vregidx) (load_width_bytes : Nat) (rs1 : regidx) (EMUL_pow : Int) (num_elem : Nat) : SailM ExecutionResult := SailME.run do
  let EMUL_reg :=
    if ((EMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vd_seg ← do (read_vreg_seg num_elem (load_width_bytes *i 8) EMUL_pow nf vd)
  let tail_ag ← do (get_vtype_vta ())
  let m := ((nf *i load_width_bytes) *i 8)
  let n := num_elem
  let (result, mask) ← (( do
    match (← (init_masked_result num_elem ((nf *i load_width_bytes) *i 8) EMUL_pow vd_seg vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult ((Vector (BitVec m) n) × (BitVec n)) )
  let trimmed : Bool := false
  let trimmed ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := trimmed
    for i in [loop_i_lower:loop_i_upper:1]i do
      let trimmed := loop_vars
      loop_vars ← do
        if ((not trimmed) : Bool)
        then
          (do
            if (((BitVec.access mask i) == 1#1) : Bool)
            then
              (do
                let loop_j_lower := 0
                let loop_j_upper := (nf -i 1)
                let mut loop_vars_3 := trimmed
                for j in [loop_j_lower:loop_j_upper:1]i do
                  let trimmed := loop_vars_3
                  loop_vars_3 ← do
                    let elem_offset := (((i *i nf) +i j) *i load_width_bytes)
                    match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) elem_offset)
                        load_width_bytes (Read Data) false false false)) with
                    | .Ok elem =>
                      (do
                        (write_single_element (load_width_bytes *i 8) i
                          (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) elem)
                        (pure trimmed))
                    | .Err e =>
                      (do
                        if ((i == 0) : Bool)
                        then SailME.throw (e : ExecutionResult)
                        else
                          (do
                            writeReg vl (to_bits_unsafe (l := xlen) i)
                            (csr_name_write_callback "vl" (← readReg vl))
                            (pure true)))
                (pure loop_vars_3))
            else
              (do
                let loop_j_lower := 0
                let loop_j_upper := (nf -i 1)
                let mut loop_vars_2 := ()
                for j in [loop_j_lower:loop_j_upper:1]i do
                  let () := loop_vars_2
                  loop_vars_2 ← do
                    let skipped_elem :=
                      (Sail.BitVec.extractLsb
                        (shiftr (GetElem?.getElem! result i) ((j *i load_width_bytes) *i 8))
                        ((load_width_bytes *i 8) -i 1) 0)
                    (write_single_element (load_width_bytes *i 8) i
                      (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) skipped_elem)
                (pure loop_vars_2)
                (pure trimmed)))
        else
          (do
            if ((tail_ag == AGNOSTIC) : Bool)
            then
              (do
                let loop_j_lower := 0
                let loop_j_upper := (nf -i 1)
                let mut loop_vars_1 := ()
                for j in [loop_j_lower:loop_j_upper:1]i do
                  let () := loop_vars_1
                  loop_vars_1 ← do
                    let skipped_elem :=
                      (Sail.BitVec.extractLsb
                        (shiftr (GetElem?.getElem! vd_seg i) ((j *i load_width_bytes) *i 8))
                        ((load_width_bytes *i 8) -i 1) 0)
                    (write_single_element (load_width_bytes *i 8) i
                      (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) skipped_elem)
                (pure loop_vars_1))
            else (pure ())
            (pure trimmed))
    (pure loop_vars) ) : SailME ExecutionResult Bool )
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: num_elem : Nat, EMUL_pow : Int, load_width_bytes : Nat, nf : Nat, nf > 0 ∧
  nf ≤ 8, load_width_bytes ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vsseg (nf : Nat) (vm : (BitVec 1)) (vs3 : vregidx) (load_width_bytes : Nat) (rs1 : regidx) (EMUL_pow : Int) (num_elem : Nat) : SailM ExecutionResult := SailME.run do
  let EMUL_reg :=
    if ((EMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vs3_seg ← do (read_vreg_seg num_elem (load_width_bytes *i 8) EMUL_pow nf vs3)
  let n := num_elem
  let mask ← (( do
    match (← (init_masked_source num_elem EMUL_pow vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult (BitVec n) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access mask i) == 1#1) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_1 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let elem_offset := (((i *i nf) +i j) *i load_width_bytes)
              let vs := (vregidx_offset vs3 (to_bits_unsafe (l := 5) (j *i EMUL_reg)))
              let data ← do (read_single_element (load_width_bytes *i 8) i vs)
              match (← (vmem_write rs1 (to_bits_unsafe (l := xlen) elem_offset) load_width_bytes
                  data (Write Data) false false false)) with
              | .Ok true => (pure ())
              | .Ok false =>
                (internal_error "riscv_insts_vext_mem.sail" 209 "store got false from vmem_write")
              | .Err e => SailME.throw (e : ExecutionResult)
          (pure loop_vars_1))
      else (pure ())
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: num_elem : Nat, EMUL_pow : Int, load_width_bytes : Nat, nf : Nat, nf > 0 ∧
  nf ≤ 8, load_width_bytes ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vlsseg (nf : Nat) (vm : (BitVec 1)) (vd : vregidx) (load_width_bytes : Nat) (rs1 : regidx) (rs2 : regidx) (EMUL_pow : Int) (num_elem : Nat) : SailM ExecutionResult := SailME.run do
  let EMUL_reg :=
    if ((EMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vd_seg ← do (read_vreg_seg num_elem (load_width_bytes *i 8) EMUL_pow nf vd)
  let rs2_val ← do (pure (BitVec.toNat (← (get_scalar rs2 xlen))))
  let m := ((nf *i load_width_bytes) *i 8)
  let n := num_elem
  let (result, mask) ← (( do
    match (← (init_masked_result num_elem ((nf *i load_width_bytes) *i 8) EMUL_pow vd_seg vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult ((Vector (BitVec m) n) × (BitVec n)) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access mask i) == 1#1) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_2 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_2
            loop_vars_2 ← do
              let elem_offset := ((i *i rs2_val) +i (j *i load_width_bytes))
              match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) elem_offset) load_width_bytes
                  (Read Data) false false false)) with
              | .Ok elem =>
                (write_single_element (load_width_bytes *i 8) i
                  (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) elem)
              | .Err e => SailME.throw (e : ExecutionResult)
          (pure loop_vars_2))
      else
        (do
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_1 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let skipped_elem :=
                (Sail.BitVec.extractLsb
                  (shiftr (GetElem?.getElem! result i) ((j *i load_width_bytes) *i 8))
                  ((load_width_bytes *i 8) -i 1) 0)
              (write_single_element (load_width_bytes *i 8) i
                (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_reg))) skipped_elem)
          (pure loop_vars_1))
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: num_elem : Nat, EMUL_pow : Int, load_width_bytes : Nat, nf : Nat, nf > 0 ∧
  nf ≤ 8, load_width_bytes ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vssseg (nf : Nat) (vm : (BitVec 1)) (vs3 : vregidx) (load_width_bytes : Nat) (rs1 : regidx) (rs2 : regidx) (EMUL_pow : Int) (num_elem : Nat) : SailM ExecutionResult := SailME.run do
  let EMUL_reg :=
    if ((EMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vs3_seg ← do (read_vreg_seg num_elem (load_width_bytes *i 8) EMUL_pow nf vs3)
  let rs2_val ← do (pure (BitVec.toNat (← (get_scalar rs2 xlen))))
  let n := num_elem
  let mask ← (( do
    match (← (init_masked_source num_elem EMUL_pow vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult (BitVec n) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access mask i) == 1#1) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_1 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let elem_offset := ((i *i rs2_val) +i (j *i load_width_bytes))
              let vs := (vregidx_offset vs3 (to_bits_unsafe (l := 5) (j *i EMUL_reg)))
              let data ← do (read_single_element (load_width_bytes *i 8) i vs)
              match (← (vmem_write rs1 (to_bits_unsafe (l := xlen) elem_offset) load_width_bytes
                  data (Write Data) false false false)) with
              | .Ok true => (pure ())
              | .Ok false =>
                (internal_error "riscv_insts_vext_mem.sail" 330 "store got false from vmem_write")
              | .Err e => SailME.throw (e : ExecutionResult)
          (pure loop_vars_1))
      else (pure ())
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: mop : Int, num_elem : Nat, EMUL_data_pow : Int, EMUL_index_pow : Int, EEW_data_bytes
  : Nat, EEW_index_bytes : Nat, nf : Nat, nf > 0 ∧ nf ≤ 8, EEW_index_bytes ∈ {1, 2, 4, 8}, EEW_data_bytes
  ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vlxseg (nf : Nat) (vm : (BitVec 1)) (vd : vregidx) (EEW_index_bytes : Nat) (EEW_data_bytes : Nat) (EMUL_index_pow : Int) (EMUL_data_pow : Int) (rs1 : regidx) (vs2 : vregidx) (num_elem : Nat) (mop : Int) : SailM ExecutionResult := SailME.run do
  let EMUL_data_reg :=
    if ((EMUL_data_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_data_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vd_seg ← do (read_vreg_seg num_elem (EEW_data_bytes *i 8) EMUL_data_pow nf vd)
  let vs2_val ← do (read_vreg num_elem (EEW_index_bytes *i 8) EMUL_index_pow vs2)
  let m := ((nf *i EEW_data_bytes) *i 8)
  let n := num_elem
  let (result, mask) ← (( do
    match (← (init_masked_result num_elem ((nf *i EEW_data_bytes) *i 8) EMUL_data_pow vd_seg
        vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult ((Vector (BitVec m) n) × (BitVec n)) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access mask i) == 1#1) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_2 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_2
            loop_vars_2 ← do
              let elem_offset : Int :=
                ((BitVec.toNat (GetElem?.getElem! vs2_val i)) +i (j *i EEW_data_bytes))
              match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) elem_offset) EEW_data_bytes
                  (Read Data) false false false)) with
              | .Ok elem =>
                (write_single_element (EEW_data_bytes *i 8) i
                  (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_data_reg))) elem)
              | .Err e => SailME.throw (e : ExecutionResult)
          (pure loop_vars_2))
      else
        (do
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_1 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let skipped_elem :=
                (Sail.BitVec.extractLsb
                  (shiftr (GetElem?.getElem! result i) ((j *i EEW_data_bytes) *i 8))
                  ((EEW_data_bytes *i 8) -i 1) 0)
              (write_single_element (EEW_data_bytes *i 8) i
                (vregidx_offset vd (to_bits_unsafe (l := 5) (j *i EMUL_data_reg))) skipped_elem)
          (pure loop_vars_1))
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: mop : Int, num_elem : Nat, EMUL_data_pow : Int, EMUL_index_pow : Int, EEW_data_bytes
  : Nat, EEW_index_bytes : Nat, nf : Nat, nf > 0 ∧ nf ≤ 8, EEW_index_bytes ∈ {1, 2, 4, 8}, EEW_data_bytes
  ∈ {1, 2, 4, 8}, num_elem > 0 -/
def process_vsxseg (nf : Nat) (vm : (BitVec 1)) (vs3 : vregidx) (EEW_index_bytes : Nat) (EEW_data_bytes : Nat) (EMUL_index_pow : Int) (EMUL_data_pow : Int) (rs1 : regidx) (vs2 : vregidx) (num_elem : Nat) (mop : Int) : SailM ExecutionResult := SailME.run do
  let EMUL_data_reg :=
    if ((EMUL_data_pow ≤b 0) : Bool)
    then 1
    else (2 ^i EMUL_data_pow)
  let vm_val ← do (read_vmask num_elem vm zvreg)
  let vs3_seg ← do (read_vreg_seg num_elem (EEW_data_bytes *i 8) EMUL_data_pow nf vs3)
  let vs2_val ← do (read_vreg num_elem (EEW_index_bytes *i 8) EMUL_index_pow vs2)
  let n := num_elem
  let mask ← (( do
    match (← (init_masked_source num_elem EMUL_data_pow vm_val)) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult (BitVec n) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access mask i) == 1#1) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          let loop_j_lower := 0
          let loop_j_upper := (nf -i 1)
          let mut loop_vars_1 := ()
          for j in [loop_j_lower:loop_j_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let elem_offset : Int :=
                ((BitVec.toNat (GetElem?.getElem! vs2_val i)) +i (j *i EEW_data_bytes))
              let vs := (vregidx_offset vs3 (to_bits_unsafe (l := 5) (j *i EMUL_data_reg)))
              let data ← do (read_single_element (EEW_data_bytes *i 8) i vs)
              match (← (vmem_write rs1 (to_bits_unsafe (l := xlen) elem_offset) EEW_data_bytes
                  data (Write Data) false false false)) with
              | .Ok true => (pure ())
              | .Ok false =>
                (internal_error "riscv_insts_vext_mem.sail" 481 "store got false from vmem_write")
              | .Err e => SailME.throw (e : ExecutionResult)
          (pure loop_vars_1))
      else (pure ())
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: elem_per_reg : Nat, load_width_bytes : Nat, nf : Nat, nf ∈ {1, 2, 4, 8}, load_width_bytes
  ∈ {1, 2, 4, 8}, 0 ≤ elem_per_reg -/
def process_vlre (nf : Nat) (vd : vregidx) (load_width_bytes : Nat) (rs1 : regidx) (elem_per_reg : Nat) : SailM ExecutionResult := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult Nat )
  if ((start_element ≥b (nf *i elem_per_reg)) : Bool)
  then (pure RETIRE_SUCCESS)
  else
    (do
      let elem_to_align : Int := (Int.tmod start_element elem_per_reg)
      let cur_field : Int := (Int.tdiv start_element elem_per_reg)
      let cur_elem : Int := start_element
      let (cur_elem, cur_field) ← (( do
        if ((elem_to_align >b 0) : Bool)
        then
          (do
            let cur_elem ← (( do
              let loop_i_lower := elem_to_align
              let loop_i_upper := (elem_per_reg -i 1)
              let mut loop_vars := cur_elem
              for i in [loop_i_lower:loop_i_upper:1]i do
                let cur_elem := loop_vars
                loop_vars ← do
                  (set_vstart (to_bits_unsafe (l := 16) cur_elem))
                  let elem_offset := (cur_elem *i load_width_bytes)
                  match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) elem_offset)
                      load_width_bytes (Read Data) false false false)) with
                  | .Ok elem =>
                    (write_single_element (load_width_bytes *i 8) i
                      (vregidx_offset vd (to_bits_unsafe (l := 5) cur_field)) elem)
                  | .Err e => SailME.throw (e : ExecutionResult)
                  (pure (cur_elem +i 1))
              (pure loop_vars) ) : SailME ExecutionResult Int )
            let cur_field : Int := (cur_field +i 1)
            (pure (cur_elem, cur_field)))
        else (pure (cur_elem, cur_field)) ) : SailME ExecutionResult (Int × Int) )
      let cur_elem ← (( do
        let loop_j_lower := cur_field
        let loop_j_upper := (nf -i 1)
        let mut loop_vars_1 := cur_elem
        for j in [loop_j_lower:loop_j_upper:1]i do
          let cur_elem := loop_vars_1
          loop_vars_1 ← do
            let loop_i_lower := 0
            let loop_i_upper := (elem_per_reg -i 1)
            let mut loop_vars_2 := cur_elem
            for i in [loop_i_lower:loop_i_upper:1]i do
              let cur_elem := loop_vars_2
              loop_vars_2 ← do
                (set_vstart (to_bits_unsafe (l := 16) cur_elem))
                let elem_offset := (cur_elem *i load_width_bytes)
                match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) elem_offset) load_width_bytes
                    (Read Data) false false false)) with
                | .Ok elem =>
                  (write_single_element (load_width_bytes *i 8) i
                    (vregidx_offset vd (to_bits_unsafe (l := 5) j)) elem)
                | .Err e => SailME.throw (e : ExecutionResult)
                (pure (cur_elem +i 1))
            (pure loop_vars_2)
        (pure loop_vars_1) ) : SailME ExecutionResult Int )
      (set_vstart (zeros (n := 16)))
      (pure RETIRE_SUCCESS))

/-- Type quantifiers: elem_per_reg : Nat, load_width_bytes : Nat, nf : Nat, nf ∈ {1, 2, 4, 8}, load_width_bytes
  ∈ {1, 2, 4, 8}, 0 ≤ elem_per_reg -/
def process_vsre (nf : Nat) (load_width_bytes : Nat) (rs1 : regidx) (vs3 : vregidx) (elem_per_reg : Nat) : SailM ExecutionResult := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult Nat )
  if ((start_element ≥b (nf *i elem_per_reg)) : Bool)
  then (pure RETIRE_SUCCESS)
  else
    (do
      let elem_to_align : Int := (Int.tmod start_element elem_per_reg)
      let cur_field : Int := (Int.tdiv start_element elem_per_reg)
      let cur_elem : Int := start_element
      let (cur_elem, cur_field) ← (( do
        if ((elem_to_align >b 0) : Bool)
        then
          (do
            let cur_elem ← (( do
              let loop_i_lower := elem_to_align
              let loop_i_upper := (elem_per_reg -i 1)
              let mut loop_vars := cur_elem
              for i in [loop_i_lower:loop_i_upper:1]i do
                let cur_elem := loop_vars
                loop_vars ← do
                  (set_vstart (to_bits_unsafe (l := 16) cur_elem))
                  let elem_offset : Int := (cur_elem *i load_width_bytes)
                  let vs := (vregidx_offset vs3 (to_bits_unsafe (l := 5) cur_field))
                  let data ← do (read_single_element (load_width_bytes *i 8) i vs)
                  match (← (vmem_write rs1 (to_bits_unsafe (l := xlen) elem_offset)
                      load_width_bytes data (Write Data) false false false)) with
                  | .Ok true => (pure ())
                  | .Ok false =>
                    (internal_error "riscv_insts_vext_mem.sail" 625
                      "store got false from vmem_write")
                  | .Err e => SailME.throw (e : ExecutionResult)
                  (pure (cur_elem +i 1))
              (pure loop_vars) ) : SailME ExecutionResult Int )
            let cur_field : Int := (cur_field +i 1)
            (pure (cur_elem, cur_field)))
        else (pure (cur_elem, cur_field)) ) : SailME ExecutionResult (Int × Int) )
      let cur_elem ← (( do
        let loop_j_lower := cur_field
        let loop_j_upper := (nf -i 1)
        let mut loop_vars_1 := cur_elem
        for j in [loop_j_lower:loop_j_upper:1]i do
          let cur_elem := loop_vars_1
          loop_vars_1 ← do
            let vs3_val ← do
              (read_vreg elem_per_reg (load_width_bytes *i 8) 0
                (vregidx_offset vs3 (to_bits_unsafe (l := 5) j)))
            let loop_i_lower := 0
            let loop_i_upper := (elem_per_reg -i 1)
            let mut loop_vars_2 := cur_elem
            for i in [loop_i_lower:loop_i_upper:1]i do
              let cur_elem := loop_vars_2
              loop_vars_2 ← do
                (set_vstart (to_bits_unsafe (l := 16) cur_elem))
                let elem_offset := (cur_elem *i load_width_bytes)
                match (← (vmem_write rs1 (to_bits_unsafe (l := xlen) elem_offset) load_width_bytes
                    (GetElem?.getElem! vs3_val i) (Write Data) false false false)) with
                | .Ok true => (pure ())
                | .Ok false =>
                  (internal_error "riscv_insts_vext_mem.sail" 640 "store got false from vmem_write")
                | .Err e => SailME.throw (e : ExecutionResult)
                (pure (cur_elem +i 1))
            (pure loop_vars_2)
        (pure loop_vars_1) ) : SailME ExecutionResult Int )
      (set_vstart (zeros (n := 16)))
      (pure RETIRE_SUCCESS))

def encdec_lsop_forwards (arg_ : vmlsop) : (BitVec 7) :=
  match arg_ with
  | VLM => (0b0000111 : (BitVec 7))
  | VSM => (0b0100111 : (BitVec 7))

def encdec_lsop_backwards (arg_ : (BitVec 7)) : SailM vmlsop := do
  let b__0 := arg_
  if ((b__0 == (0b0000111 : (BitVec 7))) : Bool)
  then (pure VLM)
  else
    (do
      if ((b__0 == (0b0100111 : (BitVec 7))) : Bool)
      then (pure VSM)
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def encdec_lsop_forwards_matches (arg_ : vmlsop) : Bool :=
  match arg_ with
  | VLM => true
  | VSM => true

def encdec_lsop_backwards_matches (arg_ : (BitVec 7)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b0000111 : (BitVec 7))) : Bool)
  then true
  else
    (if ((b__0 == (0b0100111 : (BitVec 7))) : Bool)
    then true
    else false)

/-- Type quantifiers: evl : Nat, num_elem : Nat, 0 ≤ num_elem, 0 ≤ evl -/
def process_vm (vd_or_vs3 : vregidx) (rs1 : regidx) (num_elem : Nat) (evl : Nat) (op : vmlsop) : SailM ExecutionResult := SailME.run do
  let start_element ← (( do
    match (← (get_start_element ())) with
    | .Ok v => (pure v)
    | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) : SailME
    ExecutionResult Nat )
  let n := num_elem
  let vd_or_vs3_val ← (( do (read_vreg num_elem 8 0 vd_or_vs3) ) : SailME ExecutionResult
    (Vector (BitVec 8) n) )
  let loop_i_lower := start_element
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((i <b evl) : Bool)
      then
        (do
          (set_vstart (to_bits_unsafe (l := 16) i))
          if ((op == VLM) : Bool)
          then
            (do
              match (← (vmem_read rs1 (to_bits_unsafe (l := xlen) i) 1 (Read Data) false false
                  false)) with
              | .Ok elem => (write_single_element 8 i vd_or_vs3 elem)
              | .Err e => SailME.throw (e : ExecutionResult))
          else
            (do
              if ((op == VSM) : Bool)
              then
                (do
                  match (← (vmem_write rs1 (to_bits_unsafe (l := xlen) i) 1
                      (GetElem?.getElem! vd_or_vs3_val i) (Write Data) false false false)) with
                  | .Ok true => (pure ())
                  | .Ok false =>
                    (internal_error "riscv_insts_vext_mem.sail" 696
                      "store got false from vmem_write")
                  | .Err e => SailME.throw (e : ExecutionResult))
              else (pure ())))
      else
        (do
          if ((op == VLM) : Bool)
          then (write_single_element 8 i vd_or_vs3 (GetElem?.getElem! vd_or_vs3_val i))
          else (pure ()))
  (pure loop_vars)
  (set_vstart (zeros (n := 16)))
  (pure RETIRE_SUCCESS)

def vmtype_mnemonic_backwards (arg_ : String) : SailM vmlsop := do
  match arg_ with
  | "vlm.v" => (pure VLM)
  | "vsm.v" => (pure VSM)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vmtype_mnemonic_forwards_matches (arg_ : vmlsop) : Bool :=
  match arg_ with
  | VLM => true
  | VSM => true

def vmtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vlm.v" => true
  | "vsm.v" => true
  | _ => false

