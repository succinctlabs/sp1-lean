import LeanRV64D.Prelude
import LeanRV64D.RiscvXlen
import LeanRV64D.PreludeMemAddrtype
import LeanRV64D.RiscvPcAccess
import LeanRV64D.RiscvSysRegs
import LeanRV64D.RiscvAddrChecks
import LeanRV64D.RiscvInstRetire

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

def encdec_uop_forwards (arg_ : uop) : (BitVec 7) :=
  match arg_ with
  | LUI => (0b0110111 : (BitVec 7))
  | AUIPC => (0b0010111 : (BitVec 7))

def encdec_uop_backwards (arg_ : (BitVec 7)) : SailM uop := do
  let b__0 := arg_
  if ((b__0 == (0b0110111 : (BitVec 7))) : Bool)
  then (pure LUI)
  else
    (do
      if ((b__0 == (0b0010111 : (BitVec 7))) : Bool)
      then (pure AUIPC)
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def encdec_uop_forwards_matches (arg_ : uop) : Bool :=
  match arg_ with
  | LUI => true
  | AUIPC => true

def encdec_uop_backwards_matches (arg_ : (BitVec 7)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b0110111 : (BitVec 7))) : Bool)
  then true
  else
    (if ((b__0 == (0b0010111 : (BitVec 7))) : Bool)
    then true
    else false)

def utype_mnemonic_backwards (arg_ : String) : SailM uop := do
  match arg_ with
  | "lui" => (pure LUI)
  | "auipc" => (pure AUIPC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def utype_mnemonic_forwards_matches (arg_ : uop) : Bool :=
  match arg_ with
  | LUI => true
  | AUIPC => true

def utype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "lui" => true
  | "auipc" => true
  | _ => false

def jump_to (target : (BitVec 64)) : SailM ExecutionResult := do
  match (ext_control_check_pc target) with
  | .Ext_ControlAddr_Error e => (pure (Ext_ControlAddr_Check_Failure e))
  | .Ext_ControlAddr_OK target =>
    (do
      let target_bits := (bits_of_virtaddr target)
      assert ((BitVec.access target_bits 0) == 0#1) "riscv_insts_base.sail:57.38-57.39"
      if (((← (bit_to_bool (BitVec.access target_bits 1))) && (not
             (← (currentlyEnabled Ext_Zca)))) : Bool)
      then (pure (Memory_Exception (target, (E_Fetch_Addr_Align ()))))
      else
        (do
          (set_next_pc target_bits)
          (pure RETIRE_SUCCESS)))

def encdec_bop_forwards (arg_ : bop) : (BitVec 3) :=
  match arg_ with
  | BEQ => (0b000 : (BitVec 3))
  | BNE => (0b001 : (BitVec 3))
  | BLT => (0b100 : (BitVec 3))
  | BGE => (0b101 : (BitVec 3))
  | BLTU => (0b110 : (BitVec 3))
  | BGEU => (0b111 : (BitVec 3))

def encdec_bop_backwards (arg_ : (BitVec 3)) : SailM bop := do
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then (pure BEQ)
  else
    (do
      if ((b__0 == (0b001 : (BitVec 3))) : Bool)
      then (pure BNE)
      else
        (do
          if ((b__0 == (0b100 : (BitVec 3))) : Bool)
          then (pure BLT)
          else
            (do
              if ((b__0 == (0b101 : (BitVec 3))) : Bool)
              then (pure BGE)
              else
                (do
                  if ((b__0 == (0b110 : (BitVec 3))) : Bool)
                  then (pure BLTU)
                  else
                    (do
                      if ((b__0 == (0b111 : (BitVec 3))) : Bool)
                      then (pure BGEU)
                      else
                        (do
                          assert false "Pattern match failure at unknown location"
                          throw Error.Exit))))))

def encdec_bop_forwards_matches (arg_ : bop) : Bool :=
  match arg_ with
  | BEQ => true
  | BNE => true
  | BLT => true
  | BGE => true
  | BLTU => true
  | BGEU => true

def encdec_bop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b001 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b100 : (BitVec 3))) : Bool)
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
            else false)))))

def btype_mnemonic_backwards (arg_ : String) : SailM bop := do
  match arg_ with
  | "beq" => (pure BEQ)
  | "bne" => (pure BNE)
  | "blt" => (pure BLT)
  | "bge" => (pure BGE)
  | "bltu" => (pure BLTU)
  | "bgeu" => (pure BGEU)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def btype_mnemonic_forwards_matches (arg_ : bop) : Bool :=
  match arg_ with
  | BEQ => true
  | BNE => true
  | BLT => true
  | BGE => true
  | BLTU => true
  | BGEU => true

def btype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "beq" => true
  | "bne" => true
  | "blt" => true
  | "bge" => true
  | "bltu" => true
  | "bgeu" => true
  | _ => false

def encdec_iop_forwards (arg_ : iop) : (BitVec 3) :=
  match arg_ with
  | ADDI => (0b000 : (BitVec 3))
  | SLTI => (0b010 : (BitVec 3))
  | SLTIU => (0b011 : (BitVec 3))
  | ANDI => (0b111 : (BitVec 3))
  | ORI => (0b110 : (BitVec 3))
  | XORI => (0b100 : (BitVec 3))

def encdec_iop_backwards (arg_ : (BitVec 3)) : SailM iop := do
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then (pure ADDI)
  else
    (do
      if ((b__0 == (0b010 : (BitVec 3))) : Bool)
      then (pure SLTI)
      else
        (do
          if ((b__0 == (0b011 : (BitVec 3))) : Bool)
          then (pure SLTIU)
          else
            (do
              if ((b__0 == (0b111 : (BitVec 3))) : Bool)
              then (pure ANDI)
              else
                (do
                  if ((b__0 == (0b110 : (BitVec 3))) : Bool)
                  then (pure ORI)
                  else
                    (do
                      if ((b__0 == (0b100 : (BitVec 3))) : Bool)
                      then (pure XORI)
                      else
                        (do
                          assert false "Pattern match failure at unknown location"
                          throw Error.Exit))))))

def encdec_iop_forwards_matches (arg_ : iop) : Bool :=
  match arg_ with
  | ADDI => true
  | SLTI => true
  | SLTIU => true
  | ANDI => true
  | ORI => true
  | XORI => true

def encdec_iop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b000 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b010 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b011 : (BitVec 3))) : Bool)
      then true
      else
        (if ((b__0 == (0b111 : (BitVec 3))) : Bool)
        then true
        else
          (if ((b__0 == (0b110 : (BitVec 3))) : Bool)
          then true
          else
            (if ((b__0 == (0b100 : (BitVec 3))) : Bool)
            then true
            else false)))))

def itype_mnemonic_backwards (arg_ : String) : SailM iop := do
  match arg_ with
  | "addi" => (pure ADDI)
  | "slti" => (pure SLTI)
  | "sltiu" => (pure SLTIU)
  | "xori" => (pure XORI)
  | "ori" => (pure ORI)
  | "andi" => (pure ANDI)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def itype_mnemonic_forwards_matches (arg_ : iop) : Bool :=
  match arg_ with
  | ADDI => true
  | SLTI => true
  | SLTIU => true
  | XORI => true
  | ORI => true
  | ANDI => true

def itype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "addi" => true
  | "slti" => true
  | "sltiu" => true
  | "xori" => true
  | "ori" => true
  | "andi" => true
  | _ => false

def encdec_sop_forwards (arg_ : sop) : (BitVec 3) :=
  match arg_ with
  | SLLI => (0b001 : (BitVec 3))
  | SRLI => (0b101 : (BitVec 3))
  | SRAI => (0b101 : (BitVec 3))

def encdec_sop_backwards (arg_ : (BitVec 3)) : SailM sop := do
  let b__0 := arg_
  if ((b__0 == (0b001 : (BitVec 3))) : Bool)
  then (pure SLLI)
  else
    (do
      if ((b__0 == (0b101 : (BitVec 3))) : Bool)
      then (pure SRLI)
      else
        (do
          if ((b__0 == (0b101 : (BitVec 3))) : Bool)
          then (pure SRAI)
          else
            (do
              assert false "Pattern match failure at unknown location"
              throw Error.Exit)))

def encdec_sop_forwards_matches (arg_ : sop) : Bool :=
  match arg_ with
  | SLLI => true
  | SRLI => true
  | SRAI => true

def encdec_sop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b001 : (BitVec 3))) : Bool)
  then true
  else
    (if ((b__0 == (0b101 : (BitVec 3))) : Bool)
    then true
    else
      (if ((b__0 == (0b101 : (BitVec 3))) : Bool)
      then true
      else false))

def shiftiop_mnemonic_backwards (arg_ : String) : SailM sop := do
  match arg_ with
  | "slli" => (pure SLLI)
  | "srli" => (pure SRLI)
  | "srai" => (pure SRAI)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def shiftiop_mnemonic_forwards_matches (arg_ : sop) : Bool :=
  match arg_ with
  | SLLI => true
  | SRLI => true
  | SRAI => true

def shiftiop_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "slli" => true
  | "srli" => true
  | "srai" => true
  | _ => false

def rtype_mnemonic_backwards (arg_ : String) : SailM rop := do
  match arg_ with
  | "add" => (pure ADD)
  | "slt" => (pure SLT)
  | "sltu" => (pure SLTU)
  | "and" => (pure AND)
  | "or" => (pure OR)
  | "xor" => (pure XOR)
  | "sll" => (pure SLL)
  | "srl" => (pure SRL)
  | "sub" => (pure SUB)
  | "sra" => (pure SRA)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rtype_mnemonic_forwards_matches (arg_ : rop) : Bool :=
  match arg_ with
  | ADD => true
  | SLT => true
  | SLTU => true
  | AND => true
  | OR => true
  | XOR => true
  | SLL => true
  | SRL => true
  | SUB => true
  | SRA => true

def rtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "add" => true
  | "slt" => true
  | "sltu" => true
  | "and" => true
  | "or" => true
  | "xor" => true
  | "sll" => true
  | "srl" => true
  | "sub" => true
  | "sra" => true
  | _ => false

/-- Type quantifiers: k_ex376188# : Bool, width : Nat, width ∈ {1, 2, 4, 8} -/
def valid_load_encdec (width : Nat) (is_unsigned : Bool) : Bool :=
  ((width <b xlen_bytes) || ((not is_unsigned) && (width ≤b xlen_bytes)))

/-- Type quantifiers: k_ex376191# : Bool, k_n : Nat, k_n ≥ 0, 0 < k_n ∧ k_n ≤ xlen -/
def extend_value (is_unsigned : Bool) (value : (BitVec k_n)) : (BitVec 64) :=
  if (is_unsigned : Bool)
  then (zero_extend (m := 64) value)
  else (sign_extend (m := 64) value)

def maybe_u_backwards (arg_ : String) : SailM Bool := do
  match arg_ with
  | "u" => (pure true)
  | "" => (pure false)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex376192# : Bool -/
def maybe_u_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true

def maybe_u_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "u" => true
  | "" => true
  | _ => false

def rtypew_mnemonic_backwards (arg_ : String) : SailM ropw := do
  match arg_ with
  | "addw" => (pure ADDW)
  | "subw" => (pure SUBW)
  | "sllw" => (pure SLLW)
  | "srlw" => (pure SRLW)
  | "sraw" => (pure SRAW)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rtypew_mnemonic_forwards_matches (arg_ : ropw) : Bool :=
  match arg_ with
  | ADDW => true
  | SUBW => true
  | SLLW => true
  | SRLW => true
  | SRAW => true

def rtypew_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "addw" => true
  | "subw" => true
  | "sllw" => true
  | "srlw" => true
  | "sraw" => true
  | _ => false

def shiftiwop_mnemonic_backwards (arg_ : String) : SailM sopw := do
  match arg_ with
  | "slliw" => (pure SLLIW)
  | "srliw" => (pure SRLIW)
  | "sraiw" => (pure SRAIW)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def shiftiwop_mnemonic_forwards_matches (arg_ : sopw) : Bool :=
  match arg_ with
  | SLLIW => true
  | SRLIW => true
  | SRAIW => true

def shiftiwop_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "slliw" => true
  | "srliw" => true
  | "sraiw" => true
  | _ => false

/-- Type quantifiers: k_ex376193# : Bool -/
def effective_fence_set (set : (BitVec 4)) (fiom : Bool) : (BitVec 4) :=
  if (fiom : Bool)
  then
    ((Sail.BitVec.extractLsb set 3 2) ++ ((Sail.BitVec.extractLsb set 1 0) ||| (Sail.BitVec.extractLsb
          set 3 2)))
  else set

def bit_maybe_r_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "r" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_r_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else
    (if ((b__0 == (0b0 : (BitVec 1))) : Bool)
    then true
    else false)

def bit_maybe_r_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "r" => true
  | "" => true
  | _ => false

def bit_maybe_w_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "w" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_w_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else
    (if ((b__0 == (0b0 : (BitVec 1))) : Bool)
    then true
    else false)

def bit_maybe_w_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "w" => true
  | "" => true
  | _ => false

def bit_maybe_i_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "i" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_i_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else
    (if ((b__0 == (0b0 : (BitVec 1))) : Bool)
    then true
    else false)

def bit_maybe_i_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "i" => true
  | "" => true
  | _ => false

def bit_maybe_o_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "o" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_o_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0b1 : (BitVec 1))) : Bool)
  then true
  else
    (if ((b__0 == (0b0 : (BitVec 1))) : Bool)
    then true
    else false)

def bit_maybe_o_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "o" => true
  | "" => true
  | _ => false

def fence_bits_backwards (arg_ : String) : SailM (BitVec 4) := do
  match arg_ with
  | "0" => (pure (0x0 : (BitVec 4)))
  | _ => throw Error.Exit

def fence_bits_forwards_matches (arg_ : (BitVec 4)) : Bool :=
  let b__0 := arg_
  if ((b__0 == (0x0 : (BitVec 4))) : Bool)
  then true
  else true

def fence_bits_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | "0" => (pure true)
  | _ => throw Error.Exit

