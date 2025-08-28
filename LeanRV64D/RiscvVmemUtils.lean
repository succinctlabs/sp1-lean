import LeanRV64D.Prelude
import LeanRV64D.PreludeMemAddrtype
import LeanRV64D.RiscvAddrChecks
import LeanRV64D.RiscvPlatform
import LeanRV64D.RiscvMem
import LeanRV64D.RiscvVmem

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

def sys_misaligned_order_decreasing : Bool := false

def sys_misaligned_byte_by_byte : Bool := false

def sys_misaligned_allowed_within_exp : Nat := 0

/-- Type quantifiers: k_width : Nat, k_width ≥ 0, bytes : Nat, region_width_exp : Nat, region_width_exp
  ≥ 0, region_width_exp ≤ k_width ∧ 1 ≤ bytes ∧ bytes ≤ (2 ^ region_width_exp) -/
def access_within (addr : (BitVec k_width)) (bytes : Nat) (region_width_exp : Nat) : Bool :=
  let mask : (BitVec k_width) :=
    (Complement.complement
      (zero_extend (m := (Sail.BitVec.length addr)) (ones (n := region_width_exp))))
  ((addr &&& mask) == ((BitVec.addInt addr (bytes -i 1)) &&& mask))

def prop_access_within_is_aligned (addr : (BitVec 32)) (region_width_exp : (BitVec 4)) : Bool :=
  let region_width_exp := (BitVec.toNat region_width_exp)
  let bytes := (2 ^i region_width_exp)
  ((access_within addr bytes region_width_exp) == ((Int.tmod (BitVec.toNat addr) bytes) == 0))

def prop_access_within_single (addr : (BitVec 32)) : Bool :=
  (access_within addr 1 0)

/-- Type quantifiers: width : Nat, width > 0 -/
def allowed_misaligned (vaddr : (BitVec 64)) (width : Nat) : Bool :=
  let region_width_exp := sys_misaligned_allowed_within_exp
  let region_width := (2 ^i region_width_exp)
  if ((width >b region_width) : Bool)
  then false
  else (access_within vaddr width region_width_exp)

/-- Type quantifiers: width : Nat, width > 0 -/
def split_misaligned (vaddr : virtaddr) (width : Nat) : SailM (Int × Int) := do
  let vaddr_bits := (bits_of_virtaddr vaddr)
  if (((is_aligned_vaddr vaddr width) || (allowed_misaligned vaddr_bits width)) : Bool)
  then (pure (1, width))
  else
    (do
      if (sys_misaligned_byte_by_byte : Bool)
      then (pure (width, 1))
      else
        (do
          let bytes_per_access := (2 ^i (BitVec.countTrailingZeros vaddr_bits))
          let num_accesses := (Int.tdiv width bytes_per_access)
          assert (width == (num_accesses *i bytes_per_access)) "riscv_vmem_utils.sail:94.51-94.52"
          (pure (num_accesses, bytes_per_access))))

/-- Type quantifiers: n : Int -/
def misaligned_order (n : Int) : (Int × Int × Int) :=
  if (sys_misaligned_order_decreasing : Bool)
  then ((n -i 1), 0, (-1))
  else (0, (n -i 1), 1)

/-- Type quantifiers: k_ex376049# : Bool, k_ex376048# : Bool, k_ex376047# : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_write_addr (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width))) (acc : (AccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  let (n, bytes) ← do (split_misaligned vaddr width)
  let (first, last, step) := (misaligned_order n)
  let i : Nat := first
  let finished : Bool := false
  let write_success : Bool := true
  let vaddr := (bits_of_virtaddr vaddr)
  let (finished, i, write_success) ← (( do
    let mut loop_vars := (finished, i, write_success)
    repeat
      let (finished, i, write_success) := loop_vars
      loop_vars ← do
        let offset := i
        let vaddr := (BitVec.addInt vaddr (offset *i bytes))
        let write_success ← (( do
          match (← (translateAddr (Virtaddr vaddr) acc)) with
          | .Err (e, _) =>
            SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result Bool ExecutionResult))
          | .Ok (paddr, _) =>
            (do
              if ((res && (not (match_reservation (bits_of_physaddr paddr)))) : Bool)
              then (pure false)
              else
                (do
                  match (← (mem_write_ea paddr bytes aq rl res)) with
                  | .Err e =>
                    SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result Bool ExecutionResult))
                  | .Ok () =>
                    (do
                      let write_value :=
                        (Sail.BitVec.extractLsb data (((8 *i (offset +i 1)) *i bytes) -i 1)
                          ((8 *i offset) *i bytes))
                      match (← (mem_write_value paddr bytes write_value aq rl res)) with
                      | .Err e =>
                        SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result Bool ExecutionResult))
                      | .Ok s => (pure (write_success && s))))) ) : SailME
          (Result Bool ExecutionResult) Bool )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (finished, i, write_success))
    until (λ (finished, i, write_success) => finished) loop_vars
    (pure loop_vars) ) : SailME (Result Bool ExecutionResult) (Bool × Nat × Bool) )
  (pure (Ok write_success))

/-- Type quantifiers: width : Nat, width ∈ {1, 2, 4, 8} -/
def check_misaligned (vaddr : virtaddr) (width : Nat) : Bool :=
  if (plat_enable_misaligned_access : Bool)
  then false
  else (not (is_aligned_vaddr vaddr width))

/-- Type quantifiers: k_ex376100# : Bool, k_ex376099# : Bool, k_ex376098# : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_read (rs : regidx) (offset : (BitVec 64)) (width : Nat) (acc : (AccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (ext_data_get_addr rs offset acc width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result (BitVec (8 * width)) ExecutionResult))
    ) : SailME (Result (BitVec (8 * width)) ExecutionResult) virtaddr )
  if (res : Bool)
  then
    (do
      if ((not (is_aligned_vaddr vaddr width)) : Bool)
      then
        SailME.throw ((Err (Memory_Exception (vaddr, (E_Load_Addr_Align ())))) : (Result (BitVec (8 * width)) ExecutionResult))
      else (pure ()))
  else
    (do
      if ((check_misaligned vaddr width) : Bool)
      then
        SailME.throw ((Err (Memory_Exception (vaddr, (E_Load_Addr_Align ())))) : (Result (BitVec (8 * width)) ExecutionResult))
      else (pure ()))
  let (n, bytes) ← do (split_misaligned vaddr width)
  let data := (zeros (n := ((8 *i n) *i bytes)))
  let (first, last, step) := (misaligned_order n)
  let i : Nat := first
  let finished : Bool := false
  let vaddr := (bits_of_virtaddr vaddr)
  let (data, finished, i) ← (( do
    let mut loop_vars := (data, finished, i)
    repeat
      let (data, finished, i) := loop_vars
      loop_vars ← do
        let offset := i
        let vaddr := (BitVec.addInt vaddr (offset *i bytes))
        let data ← (( do
          match (← (translateAddr (Virtaddr vaddr) acc)) with
          | .Err (e, _) =>
            SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result (BitVec (8 * width)) ExecutionResult))
          | .Ok (paddr, _) =>
            (do
              match (← (mem_read acc paddr bytes aq rl res)) with
              | .Err e =>
                SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result (BitVec (8 * width)) ExecutionResult))
              | .Ok v =>
                (do
                  if (res : Bool)
                  then (load_reservation (bits_of_physaddr paddr))
                  else (pure ())
                  (pure (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i bytes) -i 1)
                      ((8 *i offset) *i bytes) v)))) ) : SailME
          (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * n * bytes)) )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (data, finished, i))
    until (λ (data, finished, i) => finished) loop_vars
    (pure loop_vars) ) : SailME (Result (BitVec (8 * width)) ExecutionResult)
    ((BitVec (8 * n * bytes)) × Bool × Nat) )
  (pure (Ok data))

/-- Type quantifiers: k_ex376135# : Bool, k_ex376134# : Bool, k_ex376133# : Bool, width : Nat, width
  ≥ 0, is_mem_width(width) -/
def vmem_write (rs_addr : regidx) (offset : (BitVec 64)) (width : Nat) (data : (BitVec (8 * width))) (acc : (AccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (ext_data_get_addr rs_addr offset acc width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result Bool ExecutionResult)) ) : SailME
    (Result Bool ExecutionResult) virtaddr )
  if ((check_misaligned vaddr width) : Bool)
  then (pure (Err (Memory_Exception (vaddr, (E_SAMO_Addr_Align ())))))
  else (vmem_write_addr vaddr width data acc aq rl res)

