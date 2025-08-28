import LeanRV64D.Flow
import LeanRV64D.Vector

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

def not_bit (b : (BitVec 1)) : (BitVec 1) :=
  if ((b == 1#1) : Bool)
  then 0#1
  else 1#1

/-- Type quantifiers: k_p : Bool -/
def not (b : Bool) : Bool :=
  (! b)

def print_log_instr (message : String) (pc : (BitVec 64)) : Unit :=
  (print_endline message)

def print_step (_ : Unit) : Unit :=
  ()

def get_config_print_instr (_ : Unit) : Bool :=
  false

def get_config_print_platform (_ : Unit) : Bool :=
  false

def get_config_rvfi (_ : Unit) : Bool :=
  false

def get_config_use_abi_names (_ : Unit) : Bool :=
  false

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, m ≥ k_n -/
def sign_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.signExtend v m)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, m ≥ k_n -/
def zero_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

/-- Type quantifiers: n : Nat, n ≥ 0, n ≥ 0 -/
def zeros {n : _} : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: n : Nat, n ≥ 0, n ≥ 0 -/
def ones {n : _} : (BitVec n) :=
  (sail_ones n)

/-- Type quantifiers: m : Nat, m ≥ 0, k_n : Nat, k_n ≥ 0, m ≥ 0 ∧ m ≤ k_n -/
def trunc {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.truncate v m)

/-- Type quantifiers: k_ex369025# : Bool -/
def bool_bit_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => 1#1
  | false => 0#1

def bool_bit_backwards (arg_ : (BitVec 1)) : SailM Bool := do
  match arg_ with
  | 1#1 => (pure true)
  | 0#1 => (pure false)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex369026# : Bool -/
def bool_bit_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true

def bool_bit_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1#1 => true
  | 0#1 => true
  | g__10 => false

/-- Type quantifiers: k_ex369027# : Bool -/
def bool_bits_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => (0b1 : (BitVec 1))
  | false => (0b0 : (BitVec 1))

def bool_bits_backwards (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else false

/-- Type quantifiers: k_ex369029# : Bool -/
def bool_bits_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true

def bool_bits_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else
    (if ((b__0 == (0b0 : (BitVec 1))) : Bool)
    then true
    else false)

/-- Type quantifiers: k_ex369032# : Bool -/
def bool_to_bit (x : Bool) : (BitVec 1) :=
  (bool_bit_forwards x)

def bit_to_bool (x : (BitVec 1)) : SailM Bool := do
  (bool_bit_backwards x)

/-- Type quantifiers: k_ex369034# : Bool -/
def bool_to_bits (x : Bool) : (BitVec 1) :=
  (bool_bits_forwards x)

def bits_to_bool (x : (BitVec 1)) : Bool :=
  (bool_bits_backwards x)

def bit_to_bits (x : (BitVec 1)) : SailM (BitVec 1) := do
  (pure (bool_bits_forwards (← (bit_to_bool x))))

def bits_to_bit (x : (BitVec 1)) : (BitVec 1) :=
  (bool_to_bit (bits_to_bool x))

/-- Type quantifiers: l : Nat, l ≥ 0, n : Nat, l ≥ 0 ∧ 0 ≤ n ∧ n < (2 ^ l) -/
def to_bits {l : _} (n : Nat) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_checked {l : _} (n : Int) : SailM (BitVec l) := do
  let bv := (get_slice_int l n 0)
  assert ((BitVec.toNat bv) == n) (HAppend.hAppend "Couldn't convert integer "
    (HAppend.hAppend (Int.repr n)
      (HAppend.hAppend " to " (HAppend.hAppend (Int.repr l) " bits without overflow."))))
  (pure bv)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_truncate {l : _} (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_unsafe {l : _} (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zI_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) <b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zK_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) >b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zIzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≤b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zKzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≥b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zI_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) <b (BitVec.toNat y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zK_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) >b (BitVec.toNat y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zIzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) ≤b (BitVec.toNat y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zKzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) ≥b (BitVec.toNat y))

/-- Type quantifiers: shift : Nat, k_n : Nat, k_n ≥ 0, k_n ≥ 1 ∧ shift ≥ 0 -/
def shift_right_arith (value : (BitVec k_n)) (shift : Nat) : (BitVec k_n) :=
  (Sail.BitVec.extractLsb (sign_extend (m := ((Sail.BitVec.length value) +i shift)) value)
    (((Sail.BitVec.length value) -i 1) +i shift) shift)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 1 -/
def shift_bits_right_arith (value : (BitVec k_n)) (shift : (BitVec k_m)) : (BitVec k_n) :=
  (shift_right_arith value (BitVec.toNat shift))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, shift : Nat, k_m ≥ shift ∧ shift ≥ 0 -/
def rotater (value : (BitVec k_m)) (shift : Nat) : (BitVec k_m) :=
  ((shiftr value shift) ||| (shiftl value ((Sail.BitVec.length value) -i shift)))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, shift : Nat, k_m ≥ shift ∧ shift ≥ 0 -/
def rotatel (value : (BitVec k_m)) (shift : Nat) : (BitVec k_m) :=
  ((shiftl value shift) ||| (shiftr value ((Sail.BitVec.length value) -i shift)))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 0 ∧ k_m ≥ (2 ^ k_n) -/
def rotate_bits_right (value : (BitVec k_m)) (shift : (BitVec k_n)) : (BitVec k_m) :=
  (rotater value (BitVec.toNat shift))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 0 ∧ k_m ≥ (2 ^ k_n) -/
def rotate_bits_left (value : (BitVec k_m)) (shift : (BitVec k_n)) : (BitVec k_m) :=
  (rotatel value (BitVec.toNat shift))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def reverse_bits (xs : (BitVec k_n)) : (BitVec k_n) := Id.run do
  let ys : (BitVec k_n) := (zeros (n := (Sail.BitVec.length xs)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length ys) -i 1)
  let mut loop_vars := ys
  for i in [loop_i_lower:loop_i_upper:1]i do
    let ys := loop_vars
    loop_vars := (BitVec.update ys i (BitVec.access xs (((Sail.BitVec.length ys) -i 1) -i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n ∈ {1, 2, 4, 8, 16, 32, 64} -/
def log2 (n : Nat) : Int :=
  match n with
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | 8 => 3
  | 16 => 4
  | 32 => 5
  | _ => 6

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def hex_bits_str (x : (BitVec k_n)) : String :=
  (BitVec.toFormatted
    (zero_extend
      (m := ((3 -i (Int.tmod ((Sail.BitVec.length x) +i 3) 4)) +i (Sail.BitVec.length x))) x))

