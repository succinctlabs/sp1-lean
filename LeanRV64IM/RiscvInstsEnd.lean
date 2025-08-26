import LeanRV64IM.Flow
import LeanRV64IM.Prelude
import LeanRV64IM.RiscvXlen
import LeanRV64IM.PreludeMemAddrtype
import LeanRV64IM.RiscvTypes
import LeanRV64IM.RiscvVmemTypes
import LeanRV64IM.RiscvRegs
import LeanRV64IM.RiscvPcAccess
import LeanRV64IM.RiscvSysRegs
import LeanRV64IM.RiscvAddrChecks
import LeanRV64IM.RiscvSysExceptions
import LeanRV64IM.RiscvSysControl
import LeanRV64IM.RiscvInstRetire
import LeanRV64IM.RiscvVmemTlb
import LeanRV64IM.RiscvVmemUtils
import LeanRV64IM.RiscvInstsBase
import LeanRV64IM.RiscvInstsMext

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV64IM.Functions

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
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open cbop_zicbom
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open WaitReason
open TrapVectorMode
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def encdec_forwards (arg_ : instruction) : SailM (BitVec 32) := do
  match arg_ with
  | .UTYPE (imm, rd, op) =>
    (pure ((imm : (BitVec 20)) ++ ((encdec_reg_forwards rd) ++ (encdec_uop_forwards op))))
  | .JAL (v__68, rd) =>
    (do
      bif ((Sail.BitVec.extractLsb v__68 0 0) == (0b0 : (BitVec 1)))
      then
        (let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__68 20 20)
        let imm_8 : (BitVec 1) := (Sail.BitVec.extractLsb v__68 11 11)
        let imm_7_0 : (BitVec 8) := (Sail.BitVec.extractLsb v__68 19 12)
        let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__68 20 20)
        let imm_18_13 : (BitVec 6) := (Sail.BitVec.extractLsb v__68 10 5)
        let imm_12_9 : (BitVec 4) := (Sail.BitVec.extractLsb v__68 4 1)
        (pure ((imm_19 : (BitVec 1)) ++ ((imm_18_13 : (BitVec 6)) ++ ((imm_12_9 : (BitVec 4)) ++ ((imm_8 : (BitVec 1)) ++ ((imm_7_0 : (BitVec 8)) ++ ((encdec_reg_forwards
                        rd) ++ (0b1101111 : (BitVec 7))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .JALR (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                rd) ++ (0b1100111 : (BitVec 7)))))))
  | .BTYPE (v__70, rs2, rs1, op) =>
    (do
      bif ((Sail.BitVec.extractLsb v__70 0 0) == (0b0 : (BitVec 1)))
      then
        (let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__70 12 12)
        let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__70 12 12)
        let imm7_5_0 : (BitVec 6) := (Sail.BitVec.extractLsb v__70 10 5)
        let imm5_4_1 : (BitVec 4) := (Sail.BitVec.extractLsb v__70 4 1)
        let imm5_0 : (BitVec 1) := (Sail.BitVec.extractLsb v__70 11 11)
        (pure ((imm7_6 : (BitVec 1)) ++ ((imm7_5_0 : (BitVec 6)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards
                    rs1) ++ ((encdec_bop_forwards op) ++ ((imm5_4_1 : (BitVec 4)) ++ ((imm5_0 : (BitVec 1)) ++ (0b1100011 : (BitVec 7)))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((encdec_iop_forwards op) ++ ((encdec_reg_forwards
                rd) ++ (0b0010011 : (BitVec 7)))))))
  | .SHIFTIOP (shamt, rs1, rd, SLLI) =>
    (do
      bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
      then
        (pure ((0b000000 : (BitVec 6)) ++ ((shamt : (BitVec 6)) ++ ((encdec_reg_forwards rs1) ++ ((0b001 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0010011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIOP (shamt, rs1, rd, SRLI) =>
    (do
      bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
      then
        (pure ((0b000000 : (BitVec 6)) ++ ((shamt : (BitVec 6)) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0010011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIOP (shamt, rs1, rd, SRAI) =>
    (do
      bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
      then
        (pure ((0b010000 : (BitVec 6)) ++ ((shamt : (BitVec 6)) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0010011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPE (rs2, rs1, rd, ADD) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, SLT) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b010 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, SLTU) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b011 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, AND) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b111 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, OR) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b110 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, XOR) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b100 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, SLL) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b001 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, SRL) =>
    (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, SUB) =>
    (pure ((0b0100000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .RTYPE (rs2, rs1, rd, SRA) =>
    (pure ((0b0100000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                  rd) ++ (0b0110011 : (BitVec 7))))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (do
      bif (valid_load_encdec width is_unsigned)
      then
        (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((bool_bits_forwards is_unsigned) ++ ((size_enc_forwards
                    width) ++ ((encdec_reg_forwards rd) ++ (0b0000011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORE (v__72, rs2, rs1, width) =>
    (do
      bif (width ≤b xlen_bytes)
      then
        (let imm7 : (BitVec 7) := (Sail.BitVec.extractLsb v__72 11 5)
        let imm7 : (BitVec 7) := (Sail.BitVec.extractLsb v__72 11 5)
        let imm5 : (BitVec 5) := (Sail.BitVec.extractLsb v__72 4 0)
        (pure ((imm7 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b0 : (BitVec 1)) ++ ((size_enc_forwards
                      width) ++ ((imm5 : (BitVec 5)) ++ (0b0100011 : (BitVec 7))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE (pred, succ) =>
    (pure ((0x0 : (BitVec 4)) ++ ((pred : (BitVec 4)) ++ ((succ : (BitVec 4)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b0001111 : (BitVec 7)))))))))
  | .FENCE_TSO () =>
    (pure ((0x8 : (BitVec 4)) ++ ((0x3 : (BitVec 4)) ++ ((0x3 : (BitVec 4)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b0001111 : (BitVec 7)))))))))
  | .ECALL () =>
    (pure ((0x000 : (BitVec 12)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b1110011 : (BitVec 7)))))))
  | .MRET () =>
    (pure ((0b0011000 : (BitVec 7)) ++ ((0b00010 : (BitVec 5)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b1110011 : (BitVec 7))))))))
  | .SRET () =>
    (pure ((0b0001000 : (BitVec 7)) ++ ((0b00010 : (BitVec 5)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b1110011 : (BitVec 7))))))))
  | .EBREAK () =>
    (pure ((0x001 : (BitVec 12)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b1110011 : (BitVec 7)))))))
  | .WFI () =>
    (pure ((0x105 : (BitVec 12)) ++ ((0b00000 : (BitVec 5)) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b1110011 : (BitVec 7)))))))
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      bif ((← (virtual_memory_supported ())) || (not (false : Bool)))
      then
        (pure ((0b0001001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((0b00000 : (BitVec 5)) ++ (0b1110011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ADDIW (imm, rs1, rd) =>
    (do
      bif (xlen == 64)
      then
        (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                    rd) ++ (0b0011011 : (BitVec 7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, ADDW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0111011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SUBW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0100000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0111011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SLLW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b001 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0111011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SRLW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0000000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0111011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SRAW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0100000 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0111011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, SLLIW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0000000 : (BitVec 7)) ++ ((shamt : (BitVec 5)) ++ ((encdec_reg_forwards rs1) ++ ((0b001 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0011011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, SRLIW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0000000 : (BitVec 7)) ++ ((shamt : (BitVec 5)) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0011011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, SRAIW) =>
    (do
      bif (xlen == 64)
      then
        (pure ((0b0100000 : (BitVec 7)) ++ ((shamt : (BitVec 5)) ++ ((encdec_reg_forwards rs1) ++ ((0b101 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0011011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      bif ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))
      then
        (pure ((0b0000001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((← (encdec_mul_op_forwards
                      mul_op)) ++ ((encdec_reg_forwards rd) ++ (0b0110011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      bif (← (currentlyEnabled Ext_M))
      then
        (pure ((0b0000001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b10 : (BitVec 2)) ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ (0b0110011 : (BitVec 7)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      bif (← (currentlyEnabled Ext_M))
      then
        (pure ((0b0000001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b11 : (BitVec 2)) ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ (0b0110011 : (BitVec 7)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MULW (rs2, rs1, rd) =>
    (do
      bif ((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))))
      then
        (pure ((0b0000001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                      rd) ++ (0b0111011 : (BitVec 7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      bif ((xlen == 64) && (← (currentlyEnabled Ext_M)))
      then
        (pure ((0b0000001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b10 : (BitVec 2)) ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ (0b0111011 : (BitVec 7)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      bif ((xlen == 64) && (← (currentlyEnabled Ext_M)))
      then
        (pure ((0b0000001 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((0b11 : (BitVec 2)) ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ (0b0111011 : (BitVec 7)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__248 := head_exp_
    bif (let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__248 6 0)
       let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__248 11 7)
       ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_)))
    then
      (do
        let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__248 31 12)
        let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__248 6 0)
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__248 11 7)
        let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__248 31 12)
        match ((encdec_reg_backwards mapping0_), (← (encdec_uop_backwards mapping1_))) with
        | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (let v__246 := head_exp_
      bif ((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__246 11 7)
           (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__246 6 0) == (0b1101111 : (BitVec 7))))
      then
        (let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__246 31 31)
        let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__246 11 7)
        let imm_8 : (BitVec 1) := (Sail.BitVec.extractLsb v__246 20 20)
        let imm_7_0 : (BitVec 8) := (Sail.BitVec.extractLsb v__246 19 12)
        let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__246 31 31)
        let imm_18_13 : (BitVec 6) := (Sail.BitVec.extractLsb v__246 30 25)
        let imm_12_9 : (BitVec 4) := (Sail.BitVec.extractLsb v__246 24 21)
        match (encdec_reg_backwards mapping2_) with
        | rd =>
          (some
            (JAL
              (((imm_19 : (BitVec 1)) ++ ((imm_7_0 : (BitVec 8)) ++ ((imm_8 : (BitVec 1)) ++ ((imm_18_13 : (BitVec 6)) ++ ((imm_12_9 : (BitVec 4)) ++ (0b0 : (BitVec 1))))))), rd))))
      else none) with
      | .some result => (pure result)
      | none =>
        (do
          match (let v__243 := head_exp_
          bif ((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__243 11 7)
               let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__243 19 15)
               ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches mapping4_))) && (((Sail.BitVec.extractLsb
                     v__243 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__243 6 0) == (0b1100111 : (BitVec 7)))))
          then
            (let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__243 31 20)
            let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__243 11 7)
            let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__243 19 15)
            let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__243 31 20)
            match ((encdec_reg_backwards mapping3_), (encdec_reg_backwards mapping4_)) with
            | (rs1, rd) => (some (JALR (imm, rs1, rd))))
          else none) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__241 := head_exp_
                bif ((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__241 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__241 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__241 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__241 6 0) == (0b1100011 : (BitVec 7))))
                then
                  (do
                    let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__241 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__241 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__241 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__241 24 20)
                    let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__241 31 31)
                    let imm7_5_0 : (BitVec 6) := (Sail.BitVec.extractLsb v__241 30 25)
                    let imm5_4_1 : (BitVec 4) := (Sail.BitVec.extractLsb v__241 11 8)
                    let imm5_0 : (BitVec 1) := (Sail.BitVec.extractLsb v__241 7 7)
                    match ((encdec_reg_backwards mapping5_), (encdec_reg_backwards mapping6_), (← (encdec_bop_backwards
                        mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (BTYPE
                            (((imm7_6 : (BitVec 1)) ++ ((imm5_0 : (BitVec 1)) ++ ((imm7_5_0 : (BitVec 6)) ++ ((imm5_4_1 : (BitVec 4)) ++ (0b0 : (BitVec 1)))))), rs2, rs1, op)))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__239 := head_exp_
                    bif ((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__239 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__239 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__239 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__239 6 0) == (0b0010011 : (BitVec 7))))
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__239 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__239 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__239 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__239 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__239 31 20)
                        match ((encdec_reg_backwards mapping8_), (← (encdec_iop_backwards
                            mapping9_)), (encdec_reg_backwards mapping10_)) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (let v__235 := head_exp_
                      bif ((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__235 11 7)
                           let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__235 19 15)
                           ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                               mapping12_))) && (((Sail.BitVec.extractLsb v__235 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                   v__235 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__235 6 0) == (0b0010011 : (BitVec 7))))))
                      then
                        (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__235 25 20)
                        let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__235 11 7)
                        let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__235 19 15)
                        match ((encdec_reg_backwards mapping11_), (encdec_reg_backwards mapping12_)) with
                        | (rs1, rd) =>
                          (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                          then (some (SHIFTIOP (shamt, rs1, rd, SLLI)))
                          else none))
                      else none) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (let v__231 := head_exp_
                          bif ((let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__231 11 7)
                               let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__231 19 15)
                               ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                   mapping14_))) && (((Sail.BitVec.extractLsb v__231 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                       v__231 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__231 6 0) == (0b0010011 : (BitVec 7))))))
                          then
                            (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__231 25 20)
                            let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__231 11 7)
                            let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__231 19 15)
                            match ((encdec_reg_backwards mapping13_), (encdec_reg_backwards
                              mapping14_)) with
                            | (rs1, rd) =>
                              (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                              then (some (SHIFTIOP (shamt, rs1, rd, SRLI)))
                              else none))
                          else none) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (let v__227 := head_exp_
                              bif ((let mapping16_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__227 11 7)
                                   let mapping15_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__227 19 15)
                                   ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                       mapping16_))) && (((Sail.BitVec.extractLsb v__227 31 26) == (0b010000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                           v__227 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__227 6 0) == (0b0010011 : (BitVec 7))))))
                              then
                                (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__227 25 20)
                                let mapping16_ : (BitVec 5) := (Sail.BitVec.extractLsb v__227 11 7)
                                let mapping15_ : (BitVec 5) := (Sail.BitVec.extractLsb v__227 19 15)
                                match ((encdec_reg_backwards mapping15_), (encdec_reg_backwards
                                  mapping16_)) with
                                | (rs1, rd) =>
                                  (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                                  then (some (SHIFTIOP (shamt, rs1, rd, SRAI)))
                                  else none))
                              else none) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (let v__223 := head_exp_
                                  bif ((let mapping19_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__223 11 7)
                                       let mapping18_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__223 19 15)
                                       let mapping17_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__223 24 20)
                                       ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                             mapping18_) && (encdec_reg_backwards_matches mapping19_)))) && (((Sail.BitVec.extractLsb
                                             v__223 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                               v__223 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                               v__223 6 0) == (0b0110011 : (BitVec 7))))))
                                  then
                                    (let mapping19_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__223 11 7)
                                    let mapping18_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__223 19 15)
                                    let mapping17_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__223 24 20)
                                    match ((encdec_reg_backwards mapping17_), (encdec_reg_backwards
                                      mapping18_), (encdec_reg_backwards mapping19_)) with
                                    | (rs2, rs1, rd) => (some (RTYPE (rs2, rs1, rd, ADD))))
                                  else none) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (let v__219 := head_exp_
                                      bif ((let mapping22_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__219 11 7)
                                           let mapping21_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__219 19 15)
                                           let mapping20_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__219 24 20)
                                           ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                 mapping21_) && (encdec_reg_backwards_matches
                                                 mapping22_)))) && (((Sail.BitVec.extractLsb v__219
                                                 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                   v__219 14 12) == (0b010 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__219 6 0) == (0b0110011 : (BitVec 7))))))
                                      then
                                        (let mapping22_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__219 11 7)
                                        let mapping21_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__219 19 15)
                                        let mapping20_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__219 24 20)
                                        match ((encdec_reg_backwards mapping20_), (encdec_reg_backwards
                                          mapping21_), (encdec_reg_backwards mapping22_)) with
                                        | (rs2, rs1, rd) => (some (RTYPE (rs2, rs1, rd, SLT))))
                                      else none) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (let v__215 := head_exp_
                                          bif ((let mapping25_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__215 11 7)
                                               let mapping24_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__215 19 15)
                                               let mapping23_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__215 24 20)
                                               ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                     mapping24_) && (encdec_reg_backwards_matches
                                                     mapping25_)))) && (((Sail.BitVec.extractLsb
                                                     v__215 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                       v__215 14 12) == (0b011 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                       v__215 6 0) == (0b0110011 : (BitVec 7))))))
                                          then
                                            (let mapping25_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__215 11 7)
                                            let mapping24_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__215 19 15)
                                            let mapping23_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__215 24 20)
                                            match ((encdec_reg_backwards mapping23_), (encdec_reg_backwards
                                              mapping24_), (encdec_reg_backwards mapping25_)) with
                                            | (rs2, rs1, rd) => (some (RTYPE (rs2, rs1, rd, SLTU))))
                                          else none) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (let v__211 := head_exp_
                                              bif ((let mapping28_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__211 11 7)
                                                   let mapping27_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__211 19 15)
                                                   let mapping26_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__211 24 20)
                                                   ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                         mapping27_) && (encdec_reg_backwards_matches
                                                         mapping28_)))) && (((Sail.BitVec.extractLsb
                                                         v__211 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                           v__211 14 12) == (0b111 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                           v__211 6 0) == (0b0110011 : (BitVec 7))))))
                                              then
                                                (let mapping28_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__211 11 7)
                                                let mapping27_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__211 19 15)
                                                let mapping26_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__211 24 20)
                                                match ((encdec_reg_backwards mapping26_), (encdec_reg_backwards
                                                  mapping27_), (encdec_reg_backwards mapping28_)) with
                                                | (rs2, rs1, rd) =>
                                                  (some (RTYPE (rs2, rs1, rd, AND))))
                                              else none) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (let v__207 := head_exp_
                                                  bif ((let mapping31_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__207 11 7)
                                                       let mapping30_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__207 19 15)
                                                       let mapping29_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__207 24 20)
                                                       ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                             mapping30_) && (encdec_reg_backwards_matches
                                                             mapping31_)))) && (((Sail.BitVec.extractLsb
                                                             v__207 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                               v__207 14 12) == (0b110 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                               v__207 6 0) == (0b0110011 : (BitVec 7))))))
                                                  then
                                                    (let mapping31_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__207 11 7)
                                                    let mapping30_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__207 19 15)
                                                    let mapping29_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__207 24 20)
                                                    match ((encdec_reg_backwards mapping29_), (encdec_reg_backwards
                                                      mapping30_), (encdec_reg_backwards mapping31_)) with
                                                    | (rs2, rs1, rd) =>
                                                      (some (RTYPE (rs2, rs1, rd, OR))))
                                                  else none) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (let v__203 := head_exp_
                                                      bif ((let mapping34_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__203 11 7)
                                                           let mapping33_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__203 19 15)
                                                           let mapping32_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__203 24 20)
                                                           ((encdec_reg_backwards_matches mapping32_) && ((encdec_reg_backwards_matches
                                                                 mapping33_) && (encdec_reg_backwards_matches
                                                                 mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                 v__203 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                   v__203 14 12) == (0b100 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                   v__203 6 0) == (0b0110011 : (BitVec 7))))))
                                                      then
                                                        (let mapping34_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__203 11 7)
                                                        let mapping33_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__203 19 15)
                                                        let mapping32_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__203 24 20)
                                                        match ((encdec_reg_backwards mapping32_), (encdec_reg_backwards
                                                          mapping33_), (encdec_reg_backwards
                                                          mapping34_)) with
                                                        | (rs2, rs1, rd) =>
                                                          (some (RTYPE (rs2, rs1, rd, XOR))))
                                                      else none) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (let v__199 := head_exp_
                                                          bif ((let mapping37_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__199 11 7)
                                                               let mapping36_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__199 19
                                                                   15)
                                                               let mapping35_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__199 24
                                                                   20)
                                                               ((encdec_reg_backwards_matches
                                                                   mapping35_) && ((encdec_reg_backwards_matches
                                                                     mapping36_) && (encdec_reg_backwards_matches
                                                                     mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                     v__199 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                       v__199 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                       v__199 6 0) == (0b0110011 : (BitVec 7))))))
                                                          then
                                                            (let mapping37_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__199 11 7)
                                                            let mapping36_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__199 19 15)
                                                            let mapping35_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__199 24 20)
                                                            match ((encdec_reg_backwards mapping35_), (encdec_reg_backwards
                                                              mapping36_), (encdec_reg_backwards
                                                              mapping37_)) with
                                                            | (rs2, rs1, rd) =>
                                                              (some (RTYPE (rs2, rs1, rd, SLL))))
                                                          else none) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (let v__195 := head_exp_
                                                              bif ((let mapping40_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__195
                                                                       11 7)
                                                                   let mapping39_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__195
                                                                       19 15)
                                                                   let mapping38_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__195
                                                                       24 20)
                                                                   ((encdec_reg_backwards_matches
                                                                       mapping38_) && ((encdec_reg_backwards_matches
                                                                         mapping39_) && (encdec_reg_backwards_matches
                                                                         mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                         v__195 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                           v__195 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                           v__195 6 0) == (0b0110011 : (BitVec 7))))))
                                                              then
                                                                (let mapping40_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__195 11
                                                                    7)
                                                                let mapping39_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__195 19
                                                                    15)
                                                                let mapping38_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__195 24
                                                                    20)
                                                                match ((encdec_reg_backwards
                                                                  mapping38_), (encdec_reg_backwards
                                                                  mapping39_), (encdec_reg_backwards
                                                                  mapping40_)) with
                                                                | (rs2, rs1, rd) =>
                                                                  (some (RTYPE (rs2, rs1, rd, SRL))))
                                                              else none) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (let v__191 := head_exp_
                                                                  bif ((let mapping43_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__191 11 7)
                                                                       let mapping42_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__191 19 15)
                                                                       let mapping41_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__191 24 20)
                                                                       ((encdec_reg_backwards_matches
                                                                           mapping41_) && ((encdec_reg_backwards_matches
                                                                             mapping42_) && (encdec_reg_backwards_matches
                                                                             mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                             v__191 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                               v__191 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                               v__191 6 0) == (0b0110011 : (BitVec 7))))))
                                                                  then
                                                                    (let mapping43_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__191
                                                                        11 7)
                                                                    let mapping42_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__191
                                                                        19 15)
                                                                    let mapping41_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__191
                                                                        24 20)
                                                                    match ((encdec_reg_backwards
                                                                      mapping41_), (encdec_reg_backwards
                                                                      mapping42_), (encdec_reg_backwards
                                                                      mapping43_)) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (some
                                                                        (RTYPE (rs2, rs1, rd, SUB))))
                                                                  else none) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (let v__187 := head_exp_
                                                                      bif ((let mapping46_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__187 11 7)
                                                                           let mapping45_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__187 19 15)
                                                                           let mapping44_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__187 24 20)
                                                                           ((encdec_reg_backwards_matches
                                                                               mapping44_) && ((encdec_reg_backwards_matches
                                                                                 mapping45_) && (encdec_reg_backwards_matches
                                                                                 mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                 v__187 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                   v__187 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                   v__187 6 0) == (0b0110011 : (BitVec 7))))))
                                                                      then
                                                                        (let mapping46_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__187 11 7)
                                                                        let mapping45_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__187 19 15)
                                                                        let mapping44_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__187 24 20)
                                                                        match ((encdec_reg_backwards
                                                                          mapping44_), (encdec_reg_backwards
                                                                          mapping45_), (encdec_reg_backwards
                                                                          mapping46_)) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (some
                                                                            (RTYPE
                                                                              (rs2, rs1, rd, SRA))))
                                                                      else none) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (let v__185 :=
                                                                            head_exp_
                                                                          bif ((let mapping50_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__185 11 7)
                                                                               let mapping49_ : (BitVec 2) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__185 13 12)
                                                                               let mapping48_ : (BitVec 1) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__185 14 14)
                                                                               let mapping47_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__185 19 15)
                                                                               ((encdec_reg_backwards_matches
                                                                                   mapping47_) && ((bool_bits_backwards_matches
                                                                                     mapping48_) && ((size_enc_backwards_matches
                                                                                       mapping49_) && (encdec_reg_backwards_matches
                                                                                       mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                   v__185 6 0) == (0b0000011 : (BitVec 7))))
                                                                          then
                                                                            (let imm : (BitVec 12) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__185 31 20)
                                                                            let mapping50_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__185 11 7)
                                                                            let mapping49_ : (BitVec 2) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__185 13 12)
                                                                            let mapping48_ : (BitVec 1) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__185 14 14)
                                                                            let mapping47_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__185 19 15)
                                                                            let imm : (BitVec 12) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__185 31 20)
                                                                            match ((encdec_reg_backwards
                                                                              mapping47_), (bool_bits_backwards
                                                                              mapping48_), (size_enc_backwards
                                                                              mapping49_), (encdec_reg_backwards
                                                                              mapping50_)) with
                                                                            | (rs1, is_unsigned, width, rd) =>
                                                                              (bif (valid_load_encdec
                                                                                   width is_unsigned)
                                                                              then
                                                                                (some
                                                                                  (LOAD
                                                                                    (imm, rs1, rd, is_unsigned, width)))
                                                                              else none))
                                                                          else none) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (let v__182 :=
                                                                                head_exp_
                                                                              bif ((let mapping53_ : (BitVec 2) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__182 13 12)
                                                                                   let mapping52_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__182 19 15)
                                                                                   let mapping51_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__182 24 20)
                                                                                   ((encdec_reg_backwards_matches
                                                                                       mapping51_) && ((encdec_reg_backwards_matches
                                                                                         mapping52_) && (size_enc_backwards_matches
                                                                                         mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                         v__182 14
                                                                                         14) == (0b0 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                         v__182 6 0) == (0b0100011 : (BitVec 7)))))
                                                                              then
                                                                                (let imm7 : (BitVec 7) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__182 31 25)
                                                                                let mapping53_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__182 13 12)
                                                                                let mapping52_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__182 19 15)
                                                                                let mapping51_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__182 24 20)
                                                                                let imm7 : (BitVec 7) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__182 31 25)
                                                                                let imm5 : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__182 11 7)
                                                                                match ((encdec_reg_backwards
                                                                                  mapping51_), (encdec_reg_backwards
                                                                                  mapping52_), (size_enc_backwards
                                                                                  mapping53_)) with
                                                                                | (rs2, rs1, width) =>
                                                                                  (bif (width ≤b xlen_bytes)
                                                                                  then
                                                                                    (some
                                                                                      (STORE
                                                                                        (((imm7 : (BitVec 7)) ++ (imm5 : (BitVec 5))), rs2, rs1, width)))
                                                                                  else none))
                                                                              else none) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__131 :=
                                                                                      head_exp_
                                                                                    bif (((Sail.BitVec.extractLsb
                                                                                             v__131
                                                                                             31 28) == (0x0 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                             v__131
                                                                                             19 0) == (0x0000F : (BitVec 20))))
                                                                                    then
                                                                                      (let succ : (BitVec 4) :=
                                                                                        (Sail.BitVec.extractLsb
                                                                                          v__131 23
                                                                                          20)
                                                                                      let pred : (BitVec 4) :=
                                                                                        (Sail.BitVec.extractLsb
                                                                                          v__131 27
                                                                                          24)
                                                                                      (pure (some
                                                                                          (FENCE
                                                                                            (pred, succ)))))
                                                                                    else
                                                                                      (do
                                                                                        bif (v__131 == (0x8330000F : (BitVec 32)))
                                                                                        then
                                                                                          (pure (some
                                                                                              (FENCE_TSO
                                                                                                ())))
                                                                                        else
                                                                                          (do
                                                                                            bif (v__131 == (0x00000073 : (BitVec 32)))
                                                                                            then
                                                                                              (pure (some
                                                                                                  (ECALL
                                                                                                    ())))
                                                                                            else
                                                                                              (do
                                                                                                bif (v__131 == (0x30200073 : (BitVec 32)))
                                                                                                then
                                                                                                  (pure (some
                                                                                                      (MRET
                                                                                                        ())))
                                                                                                else
                                                                                                  (do
                                                                                                    bif (v__131 == (0x10200073 : (BitVec 32)))
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          (SRET
                                                                                                            ())))
                                                                                                    else
                                                                                                      (do
                                                                                                        bif (v__131 == (0x00100073 : (BitVec 32)))
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              (EBREAK
                                                                                                                ())))
                                                                                                        else
                                                                                                          (do
                                                                                                            bif (v__131 == (0x10500073 : (BitVec 32)))
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  (WFI
                                                                                                                    ())))
                                                                                                            else
                                                                                                              (do
                                                                                                                bif ((let mapping55_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__131
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     let mapping54_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__131
                                                                                                                         24
                                                                                                                         20)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping54_) && (encdec_reg_backwards_matches
                                                                                                                         mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__131
                                                                                                                           31
                                                                                                                           25) == (0b0001001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__131
                                                                                                                           14
                                                                                                                           0) == (0b000000001110011 : (BitVec 15)))))
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping55_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__131
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    let mapping54_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__131
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    match ((encdec_reg_backwards
                                                                                                                      mapping54_), (encdec_reg_backwards
                                                                                                                      mapping55_)) with
                                                                                                                    | (rs2, rs1) =>
                                                                                                                      (do
                                                                                                                        bif ((← (virtual_memory_supported
                                                                                                                                 ())) || (not
                                                                                                                               (false : Bool)))
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (SFENCE_VMA
                                                                                                                                (rs1, rs2))))
                                                                                                                        else
                                                                                                                          (pure none)))
                                                                                                                else
                                                                                                                  (pure none))))))))) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (let v__128 :=
                                                                                        head_exp_
                                                                                      bif ((let mapping57_ : (BitVec 5) :=
                                                                                             (Sail.BitVec.extractLsb
                                                                                               v__128
                                                                                               11 7)
                                                                                           let mapping56_ : (BitVec 5) :=
                                                                                             (Sail.BitVec.extractLsb
                                                                                               v__128
                                                                                               19 15)
                                                                                           ((encdec_reg_backwards_matches
                                                                                               mapping56_) && (encdec_reg_backwards_matches
                                                                                               mapping57_))) && (((Sail.BitVec.extractLsb
                                                                                                 v__128
                                                                                                 14
                                                                                                 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                 v__128
                                                                                                 6 0) == (0b0011011 : (BitVec 7)))))
                                                                                      then
                                                                                        (let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__128
                                                                                            31 20)
                                                                                        let mapping57_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__128
                                                                                            11 7)
                                                                                        let mapping56_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__128
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__128
                                                                                            31 20)
                                                                                        match ((encdec_reg_backwards
                                                                                          mapping56_), (encdec_reg_backwards
                                                                                          mapping57_)) with
                                                                                        | (rs1, rd) =>
                                                                                          (bif (xlen == 64)
                                                                                          then
                                                                                            (some
                                                                                              (ADDIW
                                                                                                (imm, rs1, rd)))
                                                                                          else none))
                                                                                      else none) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (let v__124 :=
                                                                                            head_exp_
                                                                                          bif ((let mapping60_ : (BitVec 5) :=
                                                                                                 (Sail.BitVec.extractLsb
                                                                                                   v__124
                                                                                                   11
                                                                                                   7)
                                                                                               let mapping59_ : (BitVec 5) :=
                                                                                                 (Sail.BitVec.extractLsb
                                                                                                   v__124
                                                                                                   19
                                                                                                   15)
                                                                                               let mapping58_ : (BitVec 5) :=
                                                                                                 (Sail.BitVec.extractLsb
                                                                                                   v__124
                                                                                                   24
                                                                                                   20)
                                                                                               ((encdec_reg_backwards_matches
                                                                                                   mapping58_) && ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && (encdec_reg_backwards_matches
                                                                                                     mapping60_)))) && (((Sail.BitVec.extractLsb
                                                                                                     v__124
                                                                                                     31
                                                                                                     25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                       v__124
                                                                                                       14
                                                                                                       12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                       v__124
                                                                                                       6
                                                                                                       0) == (0b0111011 : (BitVec 7))))))
                                                                                          then
                                                                                            (let mapping60_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__124
                                                                                                11 7)
                                                                                            let mapping59_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__124
                                                                                                19
                                                                                                15)
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__124
                                                                                                24
                                                                                                20)
                                                                                            match ((encdec_reg_backwards
                                                                                              mapping58_), (encdec_reg_backwards
                                                                                              mapping59_), (encdec_reg_backwards
                                                                                              mapping60_)) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (bif (xlen == 64)
                                                                                              then
                                                                                                (some
                                                                                                  (RTYPEW
                                                                                                    (rs2, rs1, rd, ADDW)))
                                                                                              else
                                                                                                none))
                                                                                          else none) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (let v__120 :=
                                                                                                head_exp_
                                                                                              bif ((let mapping63_ : (BitVec 5) :=
                                                                                                     (Sail.BitVec.extractLsb
                                                                                                       v__120
                                                                                                       11
                                                                                                       7)
                                                                                                   let mapping62_ : (BitVec 5) :=
                                                                                                     (Sail.BitVec.extractLsb
                                                                                                       v__120
                                                                                                       19
                                                                                                       15)
                                                                                                   let mapping61_ : (BitVec 5) :=
                                                                                                     (Sail.BitVec.extractLsb
                                                                                                       v__120
                                                                                                       24
                                                                                                       20)
                                                                                                   ((encdec_reg_backwards_matches
                                                                                                       mapping61_) && ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && (encdec_reg_backwards_matches
                                                                                                         mapping63_)))) && (((Sail.BitVec.extractLsb
                                                                                                         v__120
                                                                                                         31
                                                                                                         25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                           v__120
                                                                                                           14
                                                                                                           12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                           v__120
                                                                                                           6
                                                                                                           0) == (0b0111011 : (BitVec 7))))))
                                                                                              then
                                                                                                (let mapping63_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__120
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping62_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__120
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__120
                                                                                                    24
                                                                                                    20)
                                                                                                match ((encdec_reg_backwards
                                                                                                  mapping61_), (encdec_reg_backwards
                                                                                                  mapping62_), (encdec_reg_backwards
                                                                                                  mapping63_)) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (bif (xlen == 64)
                                                                                                  then
                                                                                                    (some
                                                                                                      (RTYPEW
                                                                                                        (rs2, rs1, rd, SUBW)))
                                                                                                  else
                                                                                                    none))
                                                                                              else
                                                                                                none) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (let v__116 :=
                                                                                                    head_exp_
                                                                                                  bif ((let mapping66_ : (BitVec 5) :=
                                                                                                         (Sail.BitVec.extractLsb
                                                                                                           v__116
                                                                                                           11
                                                                                                           7)
                                                                                                       let mapping65_ : (BitVec 5) :=
                                                                                                         (Sail.BitVec.extractLsb
                                                                                                           v__116
                                                                                                           19
                                                                                                           15)
                                                                                                       let mapping64_ : (BitVec 5) :=
                                                                                                         (Sail.BitVec.extractLsb
                                                                                                           v__116
                                                                                                           24
                                                                                                           20)
                                                                                                       ((encdec_reg_backwards_matches
                                                                                                           mapping64_) && ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && (encdec_reg_backwards_matches
                                                                                                             mapping66_)))) && (((Sail.BitVec.extractLsb
                                                                                                             v__116
                                                                                                             31
                                                                                                             25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                               v__116
                                                                                                               14
                                                                                                               12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                               v__116
                                                                                                               6
                                                                                                               0) == (0b0111011 : (BitVec 7))))))
                                                                                                  then
                                                                                                    (let mapping66_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__116
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping65_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__116
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__116
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((encdec_reg_backwards
                                                                                                      mapping64_), (encdec_reg_backwards
                                                                                                      mapping65_), (encdec_reg_backwards
                                                                                                      mapping66_)) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (bif (xlen == 64)
                                                                                                      then
                                                                                                        (some
                                                                                                          (RTYPEW
                                                                                                            (rs2, rs1, rd, SLLW)))
                                                                                                      else
                                                                                                        none))
                                                                                                  else
                                                                                                    none) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (let v__112 :=
                                                                                                        head_exp_
                                                                                                      bif ((let mapping69_ : (BitVec 5) :=
                                                                                                             (Sail.BitVec.extractLsb
                                                                                                               v__112
                                                                                                               11
                                                                                                               7)
                                                                                                           let mapping68_ : (BitVec 5) :=
                                                                                                             (Sail.BitVec.extractLsb
                                                                                                               v__112
                                                                                                               19
                                                                                                               15)
                                                                                                           let mapping67_ : (BitVec 5) :=
                                                                                                             (Sail.BitVec.extractLsb
                                                                                                               v__112
                                                                                                               24
                                                                                                               20)
                                                                                                           ((encdec_reg_backwards_matches
                                                                                                               mapping67_) && ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && (encdec_reg_backwards_matches
                                                                                                                 mapping69_)))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__112
                                                                                                                 31
                                                                                                                 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__112
                                                                                                                   14
                                                                                                                   12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                   v__112
                                                                                                                   6
                                                                                                                   0) == (0b0111011 : (BitVec 7))))))
                                                                                                      then
                                                                                                        (let mapping69_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__112
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping68_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__112
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__112
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((encdec_reg_backwards
                                                                                                          mapping67_), (encdec_reg_backwards
                                                                                                          mapping68_), (encdec_reg_backwards
                                                                                                          mapping69_)) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (bif (xlen == 64)
                                                                                                          then
                                                                                                            (some
                                                                                                              (RTYPEW
                                                                                                                (rs2, rs1, rd, SRLW)))
                                                                                                          else
                                                                                                            none))
                                                                                                      else
                                                                                                        none) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (let v__108 :=
                                                                                                            head_exp_
                                                                                                          bif ((let mapping72_ : (BitVec 5) :=
                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                   v__108
                                                                                                                   11
                                                                                                                   7)
                                                                                                               let mapping71_ : (BitVec 5) :=
                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                   v__108
                                                                                                                   19
                                                                                                                   15)
                                                                                                               let mapping70_ : (BitVec 5) :=
                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                   v__108
                                                                                                                   24
                                                                                                                   20)
                                                                                                               ((encdec_reg_backwards_matches
                                                                                                                   mapping70_) && ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_)))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__108
                                                                                                                     31
                                                                                                                     25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__108
                                                                                                                       14
                                                                                                                       12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                       v__108
                                                                                                                       6
                                                                                                                       0) == (0b0111011 : (BitVec 7))))))
                                                                                                          then
                                                                                                            (let mapping72_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__108
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping71_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__108
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__108
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((encdec_reg_backwards
                                                                                                              mapping70_), (encdec_reg_backwards
                                                                                                              mapping71_), (encdec_reg_backwards
                                                                                                              mapping72_)) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (bif (xlen == 64)
                                                                                                              then
                                                                                                                (some
                                                                                                                  (RTYPEW
                                                                                                                    (rs2, rs1, rd, SRAW)))
                                                                                                              else
                                                                                                                none))
                                                                                                          else
                                                                                                            none) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (let v__104 :=
                                                                                                                head_exp_
                                                                                                              bif ((let mapping74_ : (BitVec 5) :=
                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                       v__104
                                                                                                                       11
                                                                                                                       7)
                                                                                                                   let mapping73_ : (BitVec 5) :=
                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                       v__104
                                                                                                                       19
                                                                                                                       15)
                                                                                                                   ((encdec_reg_backwards_matches
                                                                                                                       mapping73_) && (encdec_reg_backwards_matches
                                                                                                                       mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__104
                                                                                                                         31
                                                                                                                         25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__104
                                                                                                                           14
                                                                                                                           12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__104
                                                                                                                           6
                                                                                                                           0) == (0b0011011 : (BitVec 7))))))
                                                                                                              then
                                                                                                                (let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__104
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping74_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__104
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping73_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__104
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((encdec_reg_backwards
                                                                                                                  mapping73_), (encdec_reg_backwards
                                                                                                                  mapping74_)) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (bif (xlen == 64)
                                                                                                                  then
                                                                                                                    (some
                                                                                                                      (SHIFTIWOP
                                                                                                                        (shamt, rs1, rd, SLLIW)))
                                                                                                                  else
                                                                                                                    none))
                                                                                                              else
                                                                                                                none) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (let v__100 :=
                                                                                                                    head_exp_
                                                                                                                  bif ((let mapping76_ : (BitVec 5) :=
                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                           v__100
                                                                                                                           11
                                                                                                                           7)
                                                                                                                       let mapping75_ : (BitVec 5) :=
                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                           v__100
                                                                                                                           19
                                                                                                                           15)
                                                                                                                       ((encdec_reg_backwards_matches
                                                                                                                           mapping75_) && (encdec_reg_backwards_matches
                                                                                                                           mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__100
                                                                                                                             31
                                                                                                                             25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__100
                                                                                                                               14
                                                                                                                               12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                               v__100
                                                                                                                               6
                                                                                                                               0) == (0b0011011 : (BitVec 7))))))
                                                                                                                  then
                                                                                                                    (let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__100
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping76_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__100
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping75_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__100
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((encdec_reg_backwards
                                                                                                                      mapping75_), (encdec_reg_backwards
                                                                                                                      mapping76_)) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (bif (xlen == 64)
                                                                                                                      then
                                                                                                                        (some
                                                                                                                          (SHIFTIWOP
                                                                                                                            (shamt, rs1, rd, SRLIW)))
                                                                                                                      else
                                                                                                                        none))
                                                                                                                  else
                                                                                                                    none) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (let v__96 :=
                                                                                                                        head_exp_
                                                                                                                      bif ((let mapping78_ : (BitVec 5) :=
                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                               v__96
                                                                                                                               11
                                                                                                                               7)
                                                                                                                           let mapping77_ : (BitVec 5) :=
                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                               v__96
                                                                                                                               19
                                                                                                                               15)
                                                                                                                           ((encdec_reg_backwards_matches
                                                                                                                               mapping77_) && (encdec_reg_backwards_matches
                                                                                                                               mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__96
                                                                                                                                 31
                                                                                                                                 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                   v__96
                                                                                                                                   14
                                                                                                                                   12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                   v__96
                                                                                                                                   6
                                                                                                                                   0) == (0b0011011 : (BitVec 7))))))
                                                                                                                      then
                                                                                                                        (let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__96
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping78_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__96
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping77_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__96
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((encdec_reg_backwards
                                                                                                                          mapping77_), (encdec_reg_backwards
                                                                                                                          mapping78_)) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (bif (xlen == 64)
                                                                                                                          then
                                                                                                                            (some
                                                                                                                              (SHIFTIWOP
                                                                                                                                (shamt, rs1, rd, SRAIW)))
                                                                                                                          else
                                                                                                                            none))
                                                                                                                      else
                                                                                                                        none) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__93 :=
                                                                                                                              head_exp_
                                                                                                                            bif ((let mapping82_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__93
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping81_ : (BitVec 3) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__93
                                                                                                                                     14
                                                                                                                                     12)
                                                                                                                                 let mapping80_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__93
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 let mapping79_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__93
                                                                                                                                     24
                                                                                                                                     20)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping79_) && ((encdec_reg_backwards_matches
                                                                                                                                       mapping80_) && ((encdec_mul_op_backwards_matches
                                                                                                                                         mapping81_) && (encdec_reg_backwards_matches
                                                                                                                                         mapping82_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__93
                                                                                                                                       31
                                                                                                                                       25) == (0b0000001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__93
                                                                                                                                       6
                                                                                                                                       0) == (0b0110011 : (BitVec 7)))))
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let mapping82_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__93
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping81_ : (BitVec 3) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__93
                                                                                                                                    14
                                                                                                                                    12)
                                                                                                                                let mapping80_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__93
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let mapping79_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__93
                                                                                                                                    24
                                                                                                                                    20)
                                                                                                                                match ((encdec_reg_backwards
                                                                                                                                  mapping79_), (encdec_reg_backwards
                                                                                                                                  mapping80_), (← (encdec_mul_op_backwards
                                                                                                                                    mapping81_)), (encdec_reg_backwards
                                                                                                                                  mapping82_)) with
                                                                                                                                | (rs2, rs1, mul_op, rd) =>
                                                                                                                                  (do
                                                                                                                                    bif ((← (currentlyEnabled
                                                                                                                                             Ext_M)) || (← (currentlyEnabled
                                                                                                                                             Ext_Zmmul)))
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (MUL
                                                                                                                                            (rs2, rs1, rd, mul_op))))
                                                                                                                                    else
                                                                                                                                      (pure none)))
                                                                                                                            else
                                                                                                                              (pure none)) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__89 :=
                                                                                                                                  head_exp_
                                                                                                                                bif ((let mapping86_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__89
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping85_ : (BitVec 1) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__89
                                                                                                                                         12
                                                                                                                                         12)
                                                                                                                                     let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__89
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping83_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__89
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping83_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping84_) && ((bool_bits_backwards_matches
                                                                                                                                             mapping85_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping86_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__89
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                             v__89
                                                                                                                                             14
                                                                                                                                             13) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                             v__89
                                                                                                                                             6
                                                                                                                                             0) == (0b0110011 : (BitVec 7))))))
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping86_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__89
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping85_ : (BitVec 1) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__89
                                                                                                                                        12
                                                                                                                                        12)
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__89
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping83_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__89
                                                                                                                                        24
                                                                                                                                        20)
                                                                                                                                    match ((encdec_reg_backwards
                                                                                                                                      mapping83_), (encdec_reg_backwards
                                                                                                                                      mapping84_), (bool_bits_backwards
                                                                                                                                      mapping85_), (encdec_reg_backwards
                                                                                                                                      mapping86_)) with
                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                      (do
                                                                                                                                        bif (← (currentlyEnabled
                                                                                                                                               Ext_M))
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (DIV
                                                                                                                                                (rs2, rs1, rd, is_unsigned))))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__85 :=
                                                                                                                                      head_exp_
                                                                                                                                    bif ((let mapping90_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__85
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping89_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__85
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__85
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping87_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__85
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping87_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping88_) && ((bool_bits_backwards_matches
                                                                                                                                                 mapping89_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping90_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__85
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__85
                                                                                                                                                 14
                                                                                                                                                 13) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__85
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011 : (BitVec 7))))))
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping90_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__85
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping89_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__85
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__85
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping87_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__85
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((encdec_reg_backwards
                                                                                                                                          mapping87_), (encdec_reg_backwards
                                                                                                                                          mapping88_), (bool_bits_backwards
                                                                                                                                          mapping89_), (encdec_reg_backwards
                                                                                                                                          mapping90_)) with
                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                          (do
                                                                                                                                            bif (← (currentlyEnabled
                                                                                                                                                   Ext_M))
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (REM
                                                                                                                                                    (rs2, rs1, rd, is_unsigned))))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__81 :=
                                                                                                                                          head_exp_
                                                                                                                                        bif ((let mapping93_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__81
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__81
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping91_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__81
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping91_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping92_) && (encdec_reg_backwards_matches
                                                                                                                                                   mapping93_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__81
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__81
                                                                                                                                                     14
                                                                                                                                                     12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__81
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0111011 : (BitVec 7))))))
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping93_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__81
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__81
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping91_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__81
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((encdec_reg_backwards
                                                                                                                                              mapping91_), (encdec_reg_backwards
                                                                                                                                              mapping92_), (encdec_reg_backwards
                                                                                                                                              mapping93_)) with
                                                                                                                                            | (rs2, rs1, rd) =>
                                                                                                                                              (do
                                                                                                                                                bif ((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                           Ext_M)) || (← (currentlyEnabled
                                                                                                                                                           Ext_Zmmul))))
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (MULW
                                                                                                                                                        (rs2, rs1, rd))))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__77 :=
                                                                                                                                              head_exp_
                                                                                                                                            bif ((let mapping97_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__77
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping96_ : (BitVec 1) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__77
                                                                                                                                                     12
                                                                                                                                                     12)
                                                                                                                                                 let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__77
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__77
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping94_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping95_) && ((bool_bits_backwards_matches
                                                                                                                                                         mapping96_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping97_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__77
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__77
                                                                                                                                                         14
                                                                                                                                                         13) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__77
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011 : (BitVec 7))))))
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping97_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__77
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping96_ : (BitVec 1) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__77
                                                                                                                                                    12
                                                                                                                                                    12)
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__77
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__77
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((encdec_reg_backwards
                                                                                                                                                  mapping94_), (encdec_reg_backwards
                                                                                                                                                  mapping95_), (bool_bits_backwards
                                                                                                                                                  mapping96_), (encdec_reg_backwards
                                                                                                                                                  mapping97_)) with
                                                                                                                                                | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    bif ((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                             Ext_M)))
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          (DIVW
                                                                                                                                                            (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__73 :=
                                                                                                                                                  head_exp_
                                                                                                                                                bif ((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__73
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping98_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__73
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     let mapping101_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__73
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping100_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__73
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping98_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping99_) && ((bool_bits_backwards_matches
                                                                                                                                                             mapping100_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping101_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__73
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__73
                                                                                                                                                             14
                                                                                                                                                             13) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__73
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011 : (BitVec 7))))))
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__73
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping98_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__73
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    let mapping101_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__73
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping100_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__73
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    match ((encdec_reg_backwards
                                                                                                                                                      mapping98_), (encdec_reg_backwards
                                                                                                                                                      mapping99_), (bool_bits_backwards
                                                                                                                                                      mapping100_), (encdec_reg_backwards
                                                                                                                                                      mapping101_)) with
                                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        bif ((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                 Ext_M)))
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (REMW
                                                                                                                                                                (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (match head_exp_ with
                                                                                                                                                | s =>
                                                                                                                                                  (pure (ILLEGAL
                                                                                                                                                      s))))))))))))))))))))))))))))))))))))))

def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__249, rd) =>
    (bif ((Sail.BitVec.extractLsb v__249 0 0) == (0b0 : (BitVec 1)))
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__251, rs2, rs1, op) =>
    (bif ((Sail.BitVec.extractLsb v__251 0 0) == (0b0 : (BitVec 1)))
    then (pure true)
    else (pure false))
  | .ITYPE (imm, rs1, rd, op) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, SLLI) =>
    (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
    then (pure true)
    else (pure false))
  | .SHIFTIOP (shamt, rs1, rd, SRLI) =>
    (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
    then (pure true)
    else (pure false))
  | .SHIFTIOP (shamt, rs1, rd, SRAI) =>
    (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
    then (pure true)
    else (pure false))
  | .RTYPE (rs2, rs1, rd, ADD) => (pure true)
  | .RTYPE (rs2, rs1, rd, SLT) => (pure true)
  | .RTYPE (rs2, rs1, rd, SLTU) => (pure true)
  | .RTYPE (rs2, rs1, rd, AND) => (pure true)
  | .RTYPE (rs2, rs1, rd, OR) => (pure true)
  | .RTYPE (rs2, rs1, rd, XOR) => (pure true)
  | .RTYPE (rs2, rs1, rd, SLL) => (pure true)
  | .RTYPE (rs2, rs1, rd, SRL) => (pure true)
  | .RTYPE (rs2, rs1, rd, SUB) => (pure true)
  | .RTYPE (rs2, rs1, rd, SRA) => (pure true)
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (bif (valid_load_encdec width is_unsigned)
    then (pure true)
    else (pure false))
  | .STORE (v__253, rs2, rs1, width) =>
    (bif (width ≤b xlen_bytes)
    then (pure true)
    else (pure false))
  | .FENCE (pred, succ) => (pure true)
  | .FENCE_TSO () => (pure true)
  | .ECALL () => (pure true)
  | .MRET () => (pure true)
  | .SRET () => (pure true)
  | .EBREAK () => (pure true)
  | .WFI () => (pure true)
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      bif ((← (virtual_memory_supported ())) || (not (false : Bool)))
      then (pure true)
      else (pure false))
  | .ADDIW (imm, rs1, rd) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, ADDW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SUBW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SLLW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SRLW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SRAW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .SHIFTIWOP (shamt, rs1, rd, SLLIW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .SHIFTIWOP (shamt, rs1, rd, SRLIW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .SHIFTIWOP (shamt, rs1, rd, SRAIW) =>
    (bif (xlen == 64)
    then (pure true)
    else (pure false))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      bif ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))
      then (pure true)
      else (pure false))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      bif (← (currentlyEnabled Ext_M))
      then (pure true)
      else (pure false))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      bif (← (currentlyEnabled Ext_M))
      then (pure true)
      else (pure false))
  | .MULW (rs2, rs1, rd) =>
    (do
      bif ((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))))
      then (pure true)
      else (pure false))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      bif ((xlen == 64) && (← (currentlyEnabled Ext_M)))
      then (pure true)
      else (pure false))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      bif ((xlen == 64) && (← (currentlyEnabled Ext_M)))
      then (pure true)
      else (pure false))
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__429 := head_exp_
    bif (let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__429 6 0)
       let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__429 11 7)
       ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_)))
    then
      (do
        let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__429 6 0)
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__429 11 7)
        match ((encdec_reg_backwards mapping0_), (← (encdec_uop_backwards mapping1_))) with
        | (rd, op) => (pure (some true)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (let v__427 := head_exp_
      bif ((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__427 11 7)
           (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__427 6 0) == (0b1101111 : (BitVec 7))))
      then
        (let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__427 11 7)
        match (encdec_reg_backwards mapping2_) with
        | rd => (some true))
      else none) with
      | .some result => (pure result)
      | none =>
        (do
          match (let v__424 := head_exp_
          bif ((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__424 11 7)
               let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__424 19 15)
               ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches mapping4_))) && (((Sail.BitVec.extractLsb
                     v__424 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__424 6 0) == (0b1100111 : (BitVec 7)))))
          then
            (let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__424 11 7)
            let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__424 19 15)
            match ((encdec_reg_backwards mapping3_), (encdec_reg_backwards mapping4_)) with
            | (rs1, rd) => (some true))
          else none) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__422 := head_exp_
                bif ((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__422 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__422 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__422 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__422 6 0) == (0b1100011 : (BitVec 7))))
                then
                  (do
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__422 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__422 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__422 24 20)
                    match ((encdec_reg_backwards mapping5_), (encdec_reg_backwards mapping6_), (← (encdec_bop_backwards
                        mapping7_))) with
                    | (rs2, rs1, op) => (pure (some true)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__420 := head_exp_
                    bif ((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__420 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__420 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__420 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__420 6 0) == (0b0010011 : (BitVec 7))))
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__420 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__420 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__420 11 7)
                        match ((encdec_reg_backwards mapping8_), (← (encdec_iop_backwards
                            mapping9_)), (encdec_reg_backwards mapping10_)) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (let v__416 := head_exp_
                      bif ((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__416 11 7)
                           let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__416 19 15)
                           ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                               mapping12_))) && (((Sail.BitVec.extractLsb v__416 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                   v__416 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__416 6 0) == (0b0010011 : (BitVec 7))))))
                      then
                        (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__416 25 20)
                        let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__416 11 7)
                        let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__416 19 15)
                        match ((encdec_reg_backwards mapping11_), (encdec_reg_backwards mapping12_)) with
                        | (rs1, rd) =>
                          (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                          then (some true)
                          else none))
                      else none) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (let v__412 := head_exp_
                          bif ((let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__412 11 7)
                               let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__412 19 15)
                               ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                   mapping14_))) && (((Sail.BitVec.extractLsb v__412 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                       v__412 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__412 6 0) == (0b0010011 : (BitVec 7))))))
                          then
                            (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__412 25 20)
                            let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__412 11 7)
                            let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__412 19 15)
                            match ((encdec_reg_backwards mapping13_), (encdec_reg_backwards
                              mapping14_)) with
                            | (rs1, rd) =>
                              (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                              then (some true)
                              else none))
                          else none) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (let v__408 := head_exp_
                              bif ((let mapping16_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__408 11 7)
                                   let mapping15_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__408 19 15)
                                   ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                       mapping16_))) && (((Sail.BitVec.extractLsb v__408 31 26) == (0b010000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                           v__408 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__408 6 0) == (0b0010011 : (BitVec 7))))))
                              then
                                (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__408 25 20)
                                let mapping16_ : (BitVec 5) := (Sail.BitVec.extractLsb v__408 11 7)
                                let mapping15_ : (BitVec 5) := (Sail.BitVec.extractLsb v__408 19 15)
                                match ((encdec_reg_backwards mapping15_), (encdec_reg_backwards
                                  mapping16_)) with
                                | (rs1, rd) =>
                                  (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                                  then (some true)
                                  else none))
                              else none) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (let v__404 := head_exp_
                                  bif ((let mapping19_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__404 11 7)
                                       let mapping18_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__404 19 15)
                                       let mapping17_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__404 24 20)
                                       ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                             mapping18_) && (encdec_reg_backwards_matches mapping19_)))) && (((Sail.BitVec.extractLsb
                                             v__404 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                               v__404 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                               v__404 6 0) == (0b0110011 : (BitVec 7))))))
                                  then
                                    (let mapping19_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__404 11 7)
                                    let mapping18_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__404 19 15)
                                    let mapping17_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__404 24 20)
                                    match ((encdec_reg_backwards mapping17_), (encdec_reg_backwards
                                      mapping18_), (encdec_reg_backwards mapping19_)) with
                                    | (rs2, rs1, rd) => (some true))
                                  else none) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (let v__400 := head_exp_
                                      bif ((let mapping22_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__400 11 7)
                                           let mapping21_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__400 19 15)
                                           let mapping20_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__400 24 20)
                                           ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                 mapping21_) && (encdec_reg_backwards_matches
                                                 mapping22_)))) && (((Sail.BitVec.extractLsb v__400
                                                 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                   v__400 14 12) == (0b010 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__400 6 0) == (0b0110011 : (BitVec 7))))))
                                      then
                                        (let mapping22_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__400 11 7)
                                        let mapping21_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__400 19 15)
                                        let mapping20_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__400 24 20)
                                        match ((encdec_reg_backwards mapping20_), (encdec_reg_backwards
                                          mapping21_), (encdec_reg_backwards mapping22_)) with
                                        | (rs2, rs1, rd) => (some true))
                                      else none) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (let v__396 := head_exp_
                                          bif ((let mapping25_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__396 11 7)
                                               let mapping24_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__396 19 15)
                                               let mapping23_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__396 24 20)
                                               ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                     mapping24_) && (encdec_reg_backwards_matches
                                                     mapping25_)))) && (((Sail.BitVec.extractLsb
                                                     v__396 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                       v__396 14 12) == (0b011 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                       v__396 6 0) == (0b0110011 : (BitVec 7))))))
                                          then
                                            (let mapping25_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__396 11 7)
                                            let mapping24_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__396 19 15)
                                            let mapping23_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__396 24 20)
                                            match ((encdec_reg_backwards mapping23_), (encdec_reg_backwards
                                              mapping24_), (encdec_reg_backwards mapping25_)) with
                                            | (rs2, rs1, rd) => (some true))
                                          else none) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (let v__392 := head_exp_
                                              bif ((let mapping28_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__392 11 7)
                                                   let mapping27_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__392 19 15)
                                                   let mapping26_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__392 24 20)
                                                   ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                         mapping27_) && (encdec_reg_backwards_matches
                                                         mapping28_)))) && (((Sail.BitVec.extractLsb
                                                         v__392 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                           v__392 14 12) == (0b111 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                           v__392 6 0) == (0b0110011 : (BitVec 7))))))
                                              then
                                                (let mapping28_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__392 11 7)
                                                let mapping27_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__392 19 15)
                                                let mapping26_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__392 24 20)
                                                match ((encdec_reg_backwards mapping26_), (encdec_reg_backwards
                                                  mapping27_), (encdec_reg_backwards mapping28_)) with
                                                | (rs2, rs1, rd) => (some true))
                                              else none) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (let v__388 := head_exp_
                                                  bif ((let mapping31_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__388 11 7)
                                                       let mapping30_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__388 19 15)
                                                       let mapping29_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__388 24 20)
                                                       ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                             mapping30_) && (encdec_reg_backwards_matches
                                                             mapping31_)))) && (((Sail.BitVec.extractLsb
                                                             v__388 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                               v__388 14 12) == (0b110 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                               v__388 6 0) == (0b0110011 : (BitVec 7))))))
                                                  then
                                                    (let mapping31_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__388 11 7)
                                                    let mapping30_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__388 19 15)
                                                    let mapping29_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__388 24 20)
                                                    match ((encdec_reg_backwards mapping29_), (encdec_reg_backwards
                                                      mapping30_), (encdec_reg_backwards mapping31_)) with
                                                    | (rs2, rs1, rd) => (some true))
                                                  else none) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (let v__384 := head_exp_
                                                      bif ((let mapping34_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__384 11 7)
                                                           let mapping33_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__384 19 15)
                                                           let mapping32_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__384 24 20)
                                                           ((encdec_reg_backwards_matches mapping32_) && ((encdec_reg_backwards_matches
                                                                 mapping33_) && (encdec_reg_backwards_matches
                                                                 mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                 v__384 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                   v__384 14 12) == (0b100 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                   v__384 6 0) == (0b0110011 : (BitVec 7))))))
                                                      then
                                                        (let mapping34_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__384 11 7)
                                                        let mapping33_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__384 19 15)
                                                        let mapping32_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__384 24 20)
                                                        match ((encdec_reg_backwards mapping32_), (encdec_reg_backwards
                                                          mapping33_), (encdec_reg_backwards
                                                          mapping34_)) with
                                                        | (rs2, rs1, rd) => (some true))
                                                      else none) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (let v__380 := head_exp_
                                                          bif ((let mapping37_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__380 11 7)
                                                               let mapping36_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__380 19
                                                                   15)
                                                               let mapping35_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__380 24
                                                                   20)
                                                               ((encdec_reg_backwards_matches
                                                                   mapping35_) && ((encdec_reg_backwards_matches
                                                                     mapping36_) && (encdec_reg_backwards_matches
                                                                     mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                     v__380 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                       v__380 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                       v__380 6 0) == (0b0110011 : (BitVec 7))))))
                                                          then
                                                            (let mapping37_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__380 11 7)
                                                            let mapping36_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__380 19 15)
                                                            let mapping35_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__380 24 20)
                                                            match ((encdec_reg_backwards mapping35_), (encdec_reg_backwards
                                                              mapping36_), (encdec_reg_backwards
                                                              mapping37_)) with
                                                            | (rs2, rs1, rd) => (some true))
                                                          else none) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (let v__376 := head_exp_
                                                              bif ((let mapping40_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__376
                                                                       11 7)
                                                                   let mapping39_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__376
                                                                       19 15)
                                                                   let mapping38_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__376
                                                                       24 20)
                                                                   ((encdec_reg_backwards_matches
                                                                       mapping38_) && ((encdec_reg_backwards_matches
                                                                         mapping39_) && (encdec_reg_backwards_matches
                                                                         mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                         v__376 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                           v__376 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                           v__376 6 0) == (0b0110011 : (BitVec 7))))))
                                                              then
                                                                (let mapping40_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__376 11
                                                                    7)
                                                                let mapping39_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__376 19
                                                                    15)
                                                                let mapping38_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__376 24
                                                                    20)
                                                                match ((encdec_reg_backwards
                                                                  mapping38_), (encdec_reg_backwards
                                                                  mapping39_), (encdec_reg_backwards
                                                                  mapping40_)) with
                                                                | (rs2, rs1, rd) => (some true))
                                                              else none) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (let v__372 := head_exp_
                                                                  bif ((let mapping43_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__372 11 7)
                                                                       let mapping42_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__372 19 15)
                                                                       let mapping41_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__372 24 20)
                                                                       ((encdec_reg_backwards_matches
                                                                           mapping41_) && ((encdec_reg_backwards_matches
                                                                             mapping42_) && (encdec_reg_backwards_matches
                                                                             mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                             v__372 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                               v__372 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                               v__372 6 0) == (0b0110011 : (BitVec 7))))))
                                                                  then
                                                                    (let mapping43_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__372
                                                                        11 7)
                                                                    let mapping42_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__372
                                                                        19 15)
                                                                    let mapping41_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__372
                                                                        24 20)
                                                                    match ((encdec_reg_backwards
                                                                      mapping41_), (encdec_reg_backwards
                                                                      mapping42_), (encdec_reg_backwards
                                                                      mapping43_)) with
                                                                    | (rs2, rs1, rd) => (some true))
                                                                  else none) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (let v__368 := head_exp_
                                                                      bif ((let mapping46_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__368 11 7)
                                                                           let mapping45_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__368 19 15)
                                                                           let mapping44_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__368 24 20)
                                                                           ((encdec_reg_backwards_matches
                                                                               mapping44_) && ((encdec_reg_backwards_matches
                                                                                 mapping45_) && (encdec_reg_backwards_matches
                                                                                 mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                 v__368 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                   v__368 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                   v__368 6 0) == (0b0110011 : (BitVec 7))))))
                                                                      then
                                                                        (let mapping46_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__368 11 7)
                                                                        let mapping45_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__368 19 15)
                                                                        let mapping44_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__368 24 20)
                                                                        match ((encdec_reg_backwards
                                                                          mapping44_), (encdec_reg_backwards
                                                                          mapping45_), (encdec_reg_backwards
                                                                          mapping46_)) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (some true))
                                                                      else none) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (let v__366 :=
                                                                            head_exp_
                                                                          bif ((let mapping50_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__366 11 7)
                                                                               let mapping49_ : (BitVec 2) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__366 13 12)
                                                                               let mapping48_ : (BitVec 1) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__366 14 14)
                                                                               let mapping47_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__366 19 15)
                                                                               ((encdec_reg_backwards_matches
                                                                                   mapping47_) && ((bool_bits_backwards_matches
                                                                                     mapping48_) && ((size_enc_backwards_matches
                                                                                       mapping49_) && (encdec_reg_backwards_matches
                                                                                       mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                   v__366 6 0) == (0b0000011 : (BitVec 7))))
                                                                          then
                                                                            (let mapping50_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__366 11 7)
                                                                            let mapping49_ : (BitVec 2) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__366 13 12)
                                                                            let mapping48_ : (BitVec 1) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__366 14 14)
                                                                            let mapping47_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__366 19 15)
                                                                            match ((encdec_reg_backwards
                                                                              mapping47_), (bool_bits_backwards
                                                                              mapping48_), (size_enc_backwards
                                                                              mapping49_), (encdec_reg_backwards
                                                                              mapping50_)) with
                                                                            | (rs1, is_unsigned, width, rd) =>
                                                                              (bif (valid_load_encdec
                                                                                   width is_unsigned)
                                                                              then (some true)
                                                                              else none))
                                                                          else none) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (let v__363 :=
                                                                                head_exp_
                                                                              bif ((let mapping53_ : (BitVec 2) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__363 13 12)
                                                                                   let mapping52_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__363 19 15)
                                                                                   let mapping51_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__363 24 20)
                                                                                   ((encdec_reg_backwards_matches
                                                                                       mapping51_) && ((encdec_reg_backwards_matches
                                                                                         mapping52_) && (size_enc_backwards_matches
                                                                                         mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                         v__363 14
                                                                                         14) == (0b0 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                         v__363 6 0) == (0b0100011 : (BitVec 7)))))
                                                                              then
                                                                                (let mapping53_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__363 13 12)
                                                                                let mapping52_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__363 19 15)
                                                                                let mapping51_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__363 24 20)
                                                                                match ((encdec_reg_backwards
                                                                                  mapping51_), (encdec_reg_backwards
                                                                                  mapping52_), (size_enc_backwards
                                                                                  mapping53_)) with
                                                                                | (rs2, rs1, width) =>
                                                                                  (bif (width ≤b xlen_bytes)
                                                                                  then (some true)
                                                                                  else none))
                                                                              else none) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__312 :=
                                                                                      head_exp_
                                                                                    bif (((Sail.BitVec.extractLsb
                                                                                             v__312
                                                                                             31 28) == (0x0 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                             v__312
                                                                                             19 0) == (0x0000F : (BitVec 20))))
                                                                                    then
                                                                                      (pure (some
                                                                                          true))
                                                                                    else
                                                                                      (do
                                                                                        bif (v__312 == (0x8330000F : (BitVec 32)))
                                                                                        then
                                                                                          (pure (some
                                                                                              true))
                                                                                        else
                                                                                          (do
                                                                                            bif (v__312 == (0x00000073 : (BitVec 32)))
                                                                                            then
                                                                                              (pure (some
                                                                                                  true))
                                                                                            else
                                                                                              (do
                                                                                                bif (v__312 == (0x30200073 : (BitVec 32)))
                                                                                                then
                                                                                                  (pure (some
                                                                                                      true))
                                                                                                else
                                                                                                  (do
                                                                                                    bif (v__312 == (0x10200073 : (BitVec 32)))
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          true))
                                                                                                    else
                                                                                                      (do
                                                                                                        bif (v__312 == (0x00100073 : (BitVec 32)))
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              true))
                                                                                                        else
                                                                                                          (do
                                                                                                            bif (v__312 == (0x10500073 : (BitVec 32)))
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  true))
                                                                                                            else
                                                                                                              (do
                                                                                                                bif ((let mapping55_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__312
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     let mapping54_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__312
                                                                                                                         24
                                                                                                                         20)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping54_) && (encdec_reg_backwards_matches
                                                                                                                         mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__312
                                                                                                                           31
                                                                                                                           25) == (0b0001001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__312
                                                                                                                           14
                                                                                                                           0) == (0b000000001110011 : (BitVec 15)))))
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping55_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__312
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    let mapping54_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__312
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    match ((encdec_reg_backwards
                                                                                                                      mapping54_), (encdec_reg_backwards
                                                                                                                      mapping55_)) with
                                                                                                                    | (rs2, rs1) =>
                                                                                                                      (do
                                                                                                                        bif ((← (virtual_memory_supported
                                                                                                                                 ())) || (not
                                                                                                                               (false : Bool)))
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (pure none)))
                                                                                                                else
                                                                                                                  (pure none))))))))) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (let v__309 :=
                                                                                        head_exp_
                                                                                      bif ((let mapping57_ : (BitVec 5) :=
                                                                                             (Sail.BitVec.extractLsb
                                                                                               v__309
                                                                                               11 7)
                                                                                           let mapping56_ : (BitVec 5) :=
                                                                                             (Sail.BitVec.extractLsb
                                                                                               v__309
                                                                                               19 15)
                                                                                           ((encdec_reg_backwards_matches
                                                                                               mapping56_) && (encdec_reg_backwards_matches
                                                                                               mapping57_))) && (((Sail.BitVec.extractLsb
                                                                                                 v__309
                                                                                                 14
                                                                                                 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                 v__309
                                                                                                 6 0) == (0b0011011 : (BitVec 7)))))
                                                                                      then
                                                                                        (let mapping57_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__309
                                                                                            11 7)
                                                                                        let mapping56_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__309
                                                                                            19 15)
                                                                                        match ((encdec_reg_backwards
                                                                                          mapping56_), (encdec_reg_backwards
                                                                                          mapping57_)) with
                                                                                        | (rs1, rd) =>
                                                                                          (bif (xlen == 64)
                                                                                          then
                                                                                            (some
                                                                                              true)
                                                                                          else none))
                                                                                      else none) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (let v__305 :=
                                                                                            head_exp_
                                                                                          bif ((let mapping60_ : (BitVec 5) :=
                                                                                                 (Sail.BitVec.extractLsb
                                                                                                   v__305
                                                                                                   11
                                                                                                   7)
                                                                                               let mapping59_ : (BitVec 5) :=
                                                                                                 (Sail.BitVec.extractLsb
                                                                                                   v__305
                                                                                                   19
                                                                                                   15)
                                                                                               let mapping58_ : (BitVec 5) :=
                                                                                                 (Sail.BitVec.extractLsb
                                                                                                   v__305
                                                                                                   24
                                                                                                   20)
                                                                                               ((encdec_reg_backwards_matches
                                                                                                   mapping58_) && ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && (encdec_reg_backwards_matches
                                                                                                     mapping60_)))) && (((Sail.BitVec.extractLsb
                                                                                                     v__305
                                                                                                     31
                                                                                                     25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                       v__305
                                                                                                       14
                                                                                                       12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                       v__305
                                                                                                       6
                                                                                                       0) == (0b0111011 : (BitVec 7))))))
                                                                                          then
                                                                                            (let mapping60_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__305
                                                                                                11 7)
                                                                                            let mapping59_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__305
                                                                                                19
                                                                                                15)
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__305
                                                                                                24
                                                                                                20)
                                                                                            match ((encdec_reg_backwards
                                                                                              mapping58_), (encdec_reg_backwards
                                                                                              mapping59_), (encdec_reg_backwards
                                                                                              mapping60_)) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (bif (xlen == 64)
                                                                                              then
                                                                                                (some
                                                                                                  true)
                                                                                              else
                                                                                                none))
                                                                                          else none) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (let v__301 :=
                                                                                                head_exp_
                                                                                              bif ((let mapping63_ : (BitVec 5) :=
                                                                                                     (Sail.BitVec.extractLsb
                                                                                                       v__301
                                                                                                       11
                                                                                                       7)
                                                                                                   let mapping62_ : (BitVec 5) :=
                                                                                                     (Sail.BitVec.extractLsb
                                                                                                       v__301
                                                                                                       19
                                                                                                       15)
                                                                                                   let mapping61_ : (BitVec 5) :=
                                                                                                     (Sail.BitVec.extractLsb
                                                                                                       v__301
                                                                                                       24
                                                                                                       20)
                                                                                                   ((encdec_reg_backwards_matches
                                                                                                       mapping61_) && ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && (encdec_reg_backwards_matches
                                                                                                         mapping63_)))) && (((Sail.BitVec.extractLsb
                                                                                                         v__301
                                                                                                         31
                                                                                                         25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                           v__301
                                                                                                           14
                                                                                                           12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                           v__301
                                                                                                           6
                                                                                                           0) == (0b0111011 : (BitVec 7))))))
                                                                                              then
                                                                                                (let mapping63_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__301
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping62_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__301
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__301
                                                                                                    24
                                                                                                    20)
                                                                                                match ((encdec_reg_backwards
                                                                                                  mapping61_), (encdec_reg_backwards
                                                                                                  mapping62_), (encdec_reg_backwards
                                                                                                  mapping63_)) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (bif (xlen == 64)
                                                                                                  then
                                                                                                    (some
                                                                                                      true)
                                                                                                  else
                                                                                                    none))
                                                                                              else
                                                                                                none) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (let v__297 :=
                                                                                                    head_exp_
                                                                                                  bif ((let mapping66_ : (BitVec 5) :=
                                                                                                         (Sail.BitVec.extractLsb
                                                                                                           v__297
                                                                                                           11
                                                                                                           7)
                                                                                                       let mapping65_ : (BitVec 5) :=
                                                                                                         (Sail.BitVec.extractLsb
                                                                                                           v__297
                                                                                                           19
                                                                                                           15)
                                                                                                       let mapping64_ : (BitVec 5) :=
                                                                                                         (Sail.BitVec.extractLsb
                                                                                                           v__297
                                                                                                           24
                                                                                                           20)
                                                                                                       ((encdec_reg_backwards_matches
                                                                                                           mapping64_) && ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && (encdec_reg_backwards_matches
                                                                                                             mapping66_)))) && (((Sail.BitVec.extractLsb
                                                                                                             v__297
                                                                                                             31
                                                                                                             25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                               v__297
                                                                                                               14
                                                                                                               12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                               v__297
                                                                                                               6
                                                                                                               0) == (0b0111011 : (BitVec 7))))))
                                                                                                  then
                                                                                                    (let mapping66_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__297
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping65_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__297
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__297
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((encdec_reg_backwards
                                                                                                      mapping64_), (encdec_reg_backwards
                                                                                                      mapping65_), (encdec_reg_backwards
                                                                                                      mapping66_)) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (bif (xlen == 64)
                                                                                                      then
                                                                                                        (some
                                                                                                          true)
                                                                                                      else
                                                                                                        none))
                                                                                                  else
                                                                                                    none) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (let v__293 :=
                                                                                                        head_exp_
                                                                                                      bif ((let mapping69_ : (BitVec 5) :=
                                                                                                             (Sail.BitVec.extractLsb
                                                                                                               v__293
                                                                                                               11
                                                                                                               7)
                                                                                                           let mapping68_ : (BitVec 5) :=
                                                                                                             (Sail.BitVec.extractLsb
                                                                                                               v__293
                                                                                                               19
                                                                                                               15)
                                                                                                           let mapping67_ : (BitVec 5) :=
                                                                                                             (Sail.BitVec.extractLsb
                                                                                                               v__293
                                                                                                               24
                                                                                                               20)
                                                                                                           ((encdec_reg_backwards_matches
                                                                                                               mapping67_) && ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && (encdec_reg_backwards_matches
                                                                                                                 mapping69_)))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__293
                                                                                                                 31
                                                                                                                 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__293
                                                                                                                   14
                                                                                                                   12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                   v__293
                                                                                                                   6
                                                                                                                   0) == (0b0111011 : (BitVec 7))))))
                                                                                                      then
                                                                                                        (let mapping69_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__293
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping68_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__293
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__293
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((encdec_reg_backwards
                                                                                                          mapping67_), (encdec_reg_backwards
                                                                                                          mapping68_), (encdec_reg_backwards
                                                                                                          mapping69_)) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (bif (xlen == 64)
                                                                                                          then
                                                                                                            (some
                                                                                                              true)
                                                                                                          else
                                                                                                            none))
                                                                                                      else
                                                                                                        none) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (let v__289 :=
                                                                                                            head_exp_
                                                                                                          bif ((let mapping72_ : (BitVec 5) :=
                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                   v__289
                                                                                                                   11
                                                                                                                   7)
                                                                                                               let mapping71_ : (BitVec 5) :=
                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                   v__289
                                                                                                                   19
                                                                                                                   15)
                                                                                                               let mapping70_ : (BitVec 5) :=
                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                   v__289
                                                                                                                   24
                                                                                                                   20)
                                                                                                               ((encdec_reg_backwards_matches
                                                                                                                   mapping70_) && ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_)))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__289
                                                                                                                     31
                                                                                                                     25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__289
                                                                                                                       14
                                                                                                                       12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                       v__289
                                                                                                                       6
                                                                                                                       0) == (0b0111011 : (BitVec 7))))))
                                                                                                          then
                                                                                                            (let mapping72_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__289
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping71_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__289
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__289
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((encdec_reg_backwards
                                                                                                              mapping70_), (encdec_reg_backwards
                                                                                                              mapping71_), (encdec_reg_backwards
                                                                                                              mapping72_)) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (bif (xlen == 64)
                                                                                                              then
                                                                                                                (some
                                                                                                                  true)
                                                                                                              else
                                                                                                                none))
                                                                                                          else
                                                                                                            none) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (let v__285 :=
                                                                                                                head_exp_
                                                                                                              bif ((let mapping74_ : (BitVec 5) :=
                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                       v__285
                                                                                                                       11
                                                                                                                       7)
                                                                                                                   let mapping73_ : (BitVec 5) :=
                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                       v__285
                                                                                                                       19
                                                                                                                       15)
                                                                                                                   ((encdec_reg_backwards_matches
                                                                                                                       mapping73_) && (encdec_reg_backwards_matches
                                                                                                                       mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__285
                                                                                                                         31
                                                                                                                         25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__285
                                                                                                                           14
                                                                                                                           12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__285
                                                                                                                           6
                                                                                                                           0) == (0b0011011 : (BitVec 7))))))
                                                                                                              then
                                                                                                                (let mapping74_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__285
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping73_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__285
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((encdec_reg_backwards
                                                                                                                  mapping73_), (encdec_reg_backwards
                                                                                                                  mapping74_)) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (bif (xlen == 64)
                                                                                                                  then
                                                                                                                    (some
                                                                                                                      true)
                                                                                                                  else
                                                                                                                    none))
                                                                                                              else
                                                                                                                none) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (let v__281 :=
                                                                                                                    head_exp_
                                                                                                                  bif ((let mapping76_ : (BitVec 5) :=
                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                           v__281
                                                                                                                           11
                                                                                                                           7)
                                                                                                                       let mapping75_ : (BitVec 5) :=
                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                           v__281
                                                                                                                           19
                                                                                                                           15)
                                                                                                                       ((encdec_reg_backwards_matches
                                                                                                                           mapping75_) && (encdec_reg_backwards_matches
                                                                                                                           mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__281
                                                                                                                             31
                                                                                                                             25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__281
                                                                                                                               14
                                                                                                                               12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                               v__281
                                                                                                                               6
                                                                                                                               0) == (0b0011011 : (BitVec 7))))))
                                                                                                                  then
                                                                                                                    (let mapping76_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__281
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping75_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__281
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((encdec_reg_backwards
                                                                                                                      mapping75_), (encdec_reg_backwards
                                                                                                                      mapping76_)) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (bif (xlen == 64)
                                                                                                                      then
                                                                                                                        (some
                                                                                                                          true)
                                                                                                                      else
                                                                                                                        none))
                                                                                                                  else
                                                                                                                    none) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (let v__277 :=
                                                                                                                        head_exp_
                                                                                                                      bif ((let mapping78_ : (BitVec 5) :=
                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                               v__277
                                                                                                                               11
                                                                                                                               7)
                                                                                                                           let mapping77_ : (BitVec 5) :=
                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                               v__277
                                                                                                                               19
                                                                                                                               15)
                                                                                                                           ((encdec_reg_backwards_matches
                                                                                                                               mapping77_) && (encdec_reg_backwards_matches
                                                                                                                               mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__277
                                                                                                                                 31
                                                                                                                                 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                   v__277
                                                                                                                                   14
                                                                                                                                   12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                   v__277
                                                                                                                                   6
                                                                                                                                   0) == (0b0011011 : (BitVec 7))))))
                                                                                                                      then
                                                                                                                        (let mapping78_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__277
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping77_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__277
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((encdec_reg_backwards
                                                                                                                          mapping77_), (encdec_reg_backwards
                                                                                                                          mapping78_)) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (bif (xlen == 64)
                                                                                                                          then
                                                                                                                            (some
                                                                                                                              true)
                                                                                                                          else
                                                                                                                            none))
                                                                                                                      else
                                                                                                                        none) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__274 :=
                                                                                                                              head_exp_
                                                                                                                            bif ((let mapping82_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__274
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping81_ : (BitVec 3) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__274
                                                                                                                                     14
                                                                                                                                     12)
                                                                                                                                 let mapping80_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__274
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 let mapping79_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__274
                                                                                                                                     24
                                                                                                                                     20)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping79_) && ((encdec_reg_backwards_matches
                                                                                                                                       mapping80_) && ((encdec_mul_op_backwards_matches
                                                                                                                                         mapping81_) && (encdec_reg_backwards_matches
                                                                                                                                         mapping82_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__274
                                                                                                                                       31
                                                                                                                                       25) == (0b0000001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__274
                                                                                                                                       6
                                                                                                                                       0) == (0b0110011 : (BitVec 7)))))
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let mapping82_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__274
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping81_ : (BitVec 3) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__274
                                                                                                                                    14
                                                                                                                                    12)
                                                                                                                                let mapping80_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__274
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let mapping79_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__274
                                                                                                                                    24
                                                                                                                                    20)
                                                                                                                                match ((encdec_reg_backwards
                                                                                                                                  mapping79_), (encdec_reg_backwards
                                                                                                                                  mapping80_), (← (encdec_mul_op_backwards
                                                                                                                                    mapping81_)), (encdec_reg_backwards
                                                                                                                                  mapping82_)) with
                                                                                                                                | (rs2, rs1, mul_op, rd) =>
                                                                                                                                  (do
                                                                                                                                    bif ((← (currentlyEnabled
                                                                                                                                             Ext_M)) || (← (currentlyEnabled
                                                                                                                                             Ext_Zmmul)))
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          true))
                                                                                                                                    else
                                                                                                                                      (pure none)))
                                                                                                                            else
                                                                                                                              (pure none)) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__270 :=
                                                                                                                                  head_exp_
                                                                                                                                bif ((let mapping86_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__270
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping85_ : (BitVec 1) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__270
                                                                                                                                         12
                                                                                                                                         12)
                                                                                                                                     let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__270
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping83_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__270
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping83_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping84_) && ((bool_bits_backwards_matches
                                                                                                                                             mapping85_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping86_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__270
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                             v__270
                                                                                                                                             14
                                                                                                                                             13) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                             v__270
                                                                                                                                             6
                                                                                                                                             0) == (0b0110011 : (BitVec 7))))))
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping86_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__270
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping85_ : (BitVec 1) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__270
                                                                                                                                        12
                                                                                                                                        12)
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__270
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping83_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__270
                                                                                                                                        24
                                                                                                                                        20)
                                                                                                                                    match ((encdec_reg_backwards
                                                                                                                                      mapping83_), (encdec_reg_backwards
                                                                                                                                      mapping84_), (bool_bits_backwards
                                                                                                                                      mapping85_), (encdec_reg_backwards
                                                                                                                                      mapping86_)) with
                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                      (do
                                                                                                                                        bif (← (currentlyEnabled
                                                                                                                                               Ext_M))
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__266 :=
                                                                                                                                      head_exp_
                                                                                                                                    bif ((let mapping90_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__266
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping89_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__266
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__266
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping87_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__266
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping87_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping88_) && ((bool_bits_backwards_matches
                                                                                                                                                 mapping89_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping90_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__266
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__266
                                                                                                                                                 14
                                                                                                                                                 13) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__266
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011 : (BitVec 7))))))
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping90_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__266
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping89_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__266
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__266
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping87_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__266
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((encdec_reg_backwards
                                                                                                                                          mapping87_), (encdec_reg_backwards
                                                                                                                                          mapping88_), (bool_bits_backwards
                                                                                                                                          mapping89_), (encdec_reg_backwards
                                                                                                                                          mapping90_)) with
                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                          (do
                                                                                                                                            bif (← (currentlyEnabled
                                                                                                                                                   Ext_M))
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__262 :=
                                                                                                                                          head_exp_
                                                                                                                                        bif ((let mapping93_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__262
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__262
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping91_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__262
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping91_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping92_) && (encdec_reg_backwards_matches
                                                                                                                                                   mapping93_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__262
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__262
                                                                                                                                                     14
                                                                                                                                                     12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__262
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0111011 : (BitVec 7))))))
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping93_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__262
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__262
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping91_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__262
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((encdec_reg_backwards
                                                                                                                                              mapping91_), (encdec_reg_backwards
                                                                                                                                              mapping92_), (encdec_reg_backwards
                                                                                                                                              mapping93_)) with
                                                                                                                                            | (rs2, rs1, rd) =>
                                                                                                                                              (do
                                                                                                                                                bif ((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                           Ext_M)) || (← (currentlyEnabled
                                                                                                                                                           Ext_Zmmul))))
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      true))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__258 :=
                                                                                                                                              head_exp_
                                                                                                                                            bif ((let mapping97_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__258
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping96_ : (BitVec 1) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__258
                                                                                                                                                     12
                                                                                                                                                     12)
                                                                                                                                                 let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__258
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__258
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping94_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping95_) && ((bool_bits_backwards_matches
                                                                                                                                                         mapping96_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping97_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__258
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__258
                                                                                                                                                         14
                                                                                                                                                         13) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__258
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011 : (BitVec 7))))))
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping97_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__258
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping96_ : (BitVec 1) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__258
                                                                                                                                                    12
                                                                                                                                                    12)
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__258
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__258
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((encdec_reg_backwards
                                                                                                                                                  mapping94_), (encdec_reg_backwards
                                                                                                                                                  mapping95_), (bool_bits_backwards
                                                                                                                                                  mapping96_), (encdec_reg_backwards
                                                                                                                                                  mapping97_)) with
                                                                                                                                                | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    bif ((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                             Ext_M)))
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          true))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__254 :=
                                                                                                                                                  head_exp_
                                                                                                                                                bif ((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__254
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping98_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__254
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     let mapping101_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__254
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping100_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__254
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping98_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping99_) && ((bool_bits_backwards_matches
                                                                                                                                                             mapping100_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping101_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__254
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__254
                                                                                                                                                             14
                                                                                                                                                             13) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__254
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011 : (BitVec 7))))))
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__254
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping98_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__254
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    let mapping101_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__254
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping100_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__254
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    match ((encdec_reg_backwards
                                                                                                                                                      mapping98_), (encdec_reg_backwards
                                                                                                                                                      mapping99_), (bool_bits_backwards
                                                                                                                                                      mapping100_), (encdec_reg_backwards
                                                                                                                                                      mapping101_)) with
                                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        bif ((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                 Ext_M)))
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              true))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (match head_exp_ with
                                                                                                                                                | s =>
                                                                                                                                                  (pure true)))))))))))))))))))))))))))))))))))))

def encdec_compressed_forwards (arg_ : instruction) : SailM (BitVec 16) := do
  match arg_ with
  | .C_ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_compressed_backwards (arg_ : (BitVec 16)) : instruction :=
  match arg_ with
  | s => (C_ILLEGAL s)

def encdec_compressed_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .C_ILLEGAL s => true
  | _ => false

def encdec_compressed_backwards_matches (arg_ : (BitVec 16)) : Bool :=
  match arg_ with
  | s => true

def execute_WFI (_ : Unit) : SailM ExecutionResult := do
  match (← readReg cur_privilege) with
  | Machine => (pure (Enter_Wait WAIT_WFI))
  | Supervisor =>
    (do
      bif ((_get_Mstatus_TW (← readReg mstatus)) == (0b1 : (BitVec 1)))
      then (pure (Illegal_Instruction ()))
      else (pure (Enter_Wait WAIT_WFI)))
  | User => (pure (Illegal_Instruction ()))

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 64) (imm ++ (0x000 : (BitVec 12))))
  (wX_bits rd
    (← do
      match op with
      | LUI => (pure off)
      | AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, width ∈ {1, 2, 4, 8} -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  assert (width ≤b xlen_bytes) "model/riscv_insts_base.sail:323.28-323.29"
  let data ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) ((width *i 8) -i 1) 0))
  match (← (vmem_write rs1 offset width data (Write Data) false false false)) with
  | .Ok _ => (pure RETIRE_SUCCESS)
  | .Err e => (pure e)

def execute_SRET (_ : Unit) : SailM ExecutionResult := do
  let sret_illegal ← (( do
    match (← readReg cur_privilege) with
    | User => (pure true)
    | Supervisor =>
      (pure ((not (← (currentlyEnabled Ext_S))) || ((_get_Mstatus_TSR (← readReg mstatus)) == (0b1 : (BitVec 1)))))
    | Machine => (pure (not (← (currentlyEnabled Ext_S)))) ) : SailM Bool )
  bif sret_illegal
  then (pure (Illegal_Instruction ()))
  else
    (do
      bif (not (ext_check_xret_priv Supervisor))
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          (set_next_pc
            (← (exception_handler (← readReg cur_privilege) (CTL_SRET ()) (← readReg PC))))
          (pure RETIRE_SUCCESS)))

def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | SLLIW => (shift_bits_left rs1_val shamt)
    | SRLIW => (shift_bits_right rs1_val shamt)
    | SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

def execute_SFENCE_VMA (rs1 : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  let addr ← do
    bif (bne rs1 zreg)
    then (pure (some (← (rX_bits rs1))))
    else (pure none)
  let asid ← do
    bif (bne rs2 zreg)
    then (pure (some (Sail.BitVec.extractLsb (← (rX_bits rs2)) (asidlen -i 1) 0)))
    else (pure none)
  match (← readReg cur_privilege) with
  | User => (pure (Illegal_Instruction ()))
  | Supervisor =>
    (do
      let b__0 ← do (pure (_get_Mstatus_TVM (← readReg mstatus)))
      bif (b__0 == (0b1 : (BitVec 1)))
      then (pure (Illegal_Instruction ()))
      else
        (do
          (flush_TLB asid addr)
          (pure RETIRE_SUCCESS)))
  | Machine =>
    (do
      (flush_TLB asid addr)
      (pure RETIRE_SUCCESS))

def execute_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | ADDW => (rs1_val + rs2_val)
    | SUBW => (rs1_val - rs2_val)
    | SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | SLT =>
        (pure (zero_extend (m := 64)
            (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | SLTU =>
        (pure (zero_extend (m := 64)
            (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex72252# : Bool -/
def execute_REMW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    bif (rs2_int == 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex72261# : Bool -/
def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    bif (rs2_int == 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits_truncate (l := 64) remainder))
  (pure RETIRE_SUCCESS)

def execute_MULW (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int := (BitVec.toInt rs1_bits)
  let rs2_int := (BitVec.toInt rs2_bits)
  let result32 : (BitVec 32) := (to_bits_truncate (l := 32) (rs1_int *i rs2_int))
  (wX_bits rd (sign_extend (m := 64) result32))
  (pure RETIRE_SUCCESS)

def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    bif mul_op.signed_rs1
    then (BitVec.toInt rs1_bits)
    else (BitVec.toNat rs1_bits)
  let rs2_int :=
    bif mul_op.signed_rs2
    then (BitVec.toInt rs2_bits)
    else (BitVec.toNat rs2_bits)
  let result_wide := (to_bits_truncate (l := (2 *i xlen)) (rs1_int *i rs2_int))
  (wX_bits rd
    (bif mul_op.high
    then (Sail.BitVec.extractLsb result_wide ((2 *i xlen) -i 1) xlen)
    else (Sail.BitVec.extractLsb result_wide (xlen -i 1) 0)))
  (pure RETIRE_SUCCESS)

def execute_MRET (_ : Unit) : SailM ExecutionResult := do
  bif (bne (← readReg cur_privilege) Machine)
  then (pure (Illegal_Instruction ()))
  else
    (do
      bif (not (ext_check_xret_priv Machine))
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          (set_next_pc
            (← (exception_handler (← readReg cur_privilege) (CTL_MRET ()) (← readReg PC))))
          (pure RETIRE_SUCCESS)))

/-- Type quantifiers: width : Nat, k_ex72292# : Bool, width ∈ {1, 2, 4, 8} -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  assert (width ≤b xlen_bytes) "model/riscv_insts_base.sail:293.28-293.29"
  match (← (vmem_read rs1 offset width (Read Data) false false false)) with
  | .Ok data =>
    (do
      (wX_bits rd (extend_value is_unsigned data))
      (pure RETIRE_SUCCESS))
  | .Err e => (pure e)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let t ← (( do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm))) ) : SailM xlenbits )
  match (ext_control_check_addr t) with
  | .Ext_ControlAddr_Error e => (pure (Ext_ControlAddr_Check_Failure e))
  | .Ext_ControlAddr_OK addr =>
    (do
      let target := (BitVec.update (bits_of_virtaddr addr) 0 0#1)
      bif ((← (bit_to_bool (BitVec.access target 1))) && (not (← (currentlyEnabled Ext_Zca))))
      then (pure (Memory_Exception (addr, (E_Fetch_Addr_Align ()))))
      else
        (do
          (wX_bits rd (← (get_next_pc ())))
          (set_next_pc target)
          (pure RETIRE_SUCCESS)))

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let target ← do (pure ((← readReg PC) + (sign_extend (m := 64) imm)))
  match (ext_control_check_pc target) with
  | .Ext_ControlAddr_Error e => (pure (Ext_ControlAddr_Check_Failure e))
  | .Ext_ControlAddr_OK target =>
    (do
      let target_bits := (bits_of_virtaddr target)
      bif ((← (bit_to_bool (BitVec.access target_bits 1))) && (not
             (← (currentlyEnabled Ext_Zca))))
      then (pure (Memory_Exception (target, (E_Fetch_Addr_Align ()))))
      else
        (do
          (wX_bits rd (← (get_next_pc ())))
          (set_next_pc target_bits)
          (pure RETIRE_SUCCESS)))

def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 64) imm)
  (wX_bits rd
    (← do
      match op with
      | ADDI => (pure ((← (rX_bits rs1)) + immext))
      | SLTI => (pure (zero_extend (m := 64) (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) immext))))
      | SLTIU =>
        (pure (zero_extend (m := 64) (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) immext))))
      | ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)

def execute_ILLEGAL (s : (BitVec 32)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_FENCE_TSO (_ : Unit) : SailM ExecutionResult := do
  (sail_barrier Barrier_RISCV_tso)
  (pure RETIRE_SUCCESS)

def execute_FENCE (pred : (BitVec 4)) (succ : (BitVec 4)) : SailM ExecutionResult := do
  let fiom ← do (is_fiom_active ())
  let pred := (effective_fence_set pred fiom)
  let succ := (effective_fence_set succ fiom)
  match (pred, succ) with
  | (v__430, v__431) =>
    (do
      bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
               v__431 1 0) == (0b11 : (BitVec 2))))
      then (sail_barrier Barrier_RISCV_rw_rw)
      else
        (do
          bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                   v__431 1 0) == (0b11 : (BitVec 2))))
          then (sail_barrier Barrier_RISCV_r_rw)
          else
            (do
              bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                       v__431 1 0) == (0b10 : (BitVec 2))))
              then (sail_barrier Barrier_RISCV_r_r)
              else
                (do
                  bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                           v__431 1 0) == (0b01 : (BitVec 2))))
                  then (sail_barrier Barrier_RISCV_rw_w)
                  else
                    (do
                      bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b01 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                               v__431 1 0) == (0b01 : (BitVec 2))))
                      then (sail_barrier Barrier_RISCV_w_w)
                      else
                        (do
                          bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b01 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                   v__431 1 0) == (0b11 : (BitVec 2))))
                          then (sail_barrier Barrier_RISCV_w_rw)
                          else
                            (do
                              bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                       v__431 1 0) == (0b10 : (BitVec 2))))
                              then (sail_barrier Barrier_RISCV_rw_r)
                              else
                                (do
                                  bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                           v__431 1 0) == (0b01 : (BitVec 2))))
                                  then (sail_barrier Barrier_RISCV_r_w)
                                  else
                                    (do
                                      bif (((Sail.BitVec.extractLsb v__430 1 0) == (0b01 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                               v__431 1 0) == (0b10 : (BitVec 2))))
                                      then (sail_barrier Barrier_RISCV_w_r)
                                      else
                                        (bif ((Sail.BitVec.extractLsb v__431 1 0) == (0b00 : (BitVec 2)))
                                        then (pure ())
                                        else
                                          (bif ((Sail.BitVec.extractLsb v__430 1 0) == (0b00 : (BitVec 2)))
                                          then (pure ())
                                          else
                                            (let _ : Unit := (print "FIXME: unsupported fence")
                                            (pure ())))))))))))))
  (pure RETIRE_SUCCESS)

def execute_ECALL (_ : Unit) : SailM ExecutionResult := do
  let t ← (( do
    (pure { trap := match (← readReg cur_privilege) with
            | User => (E_U_EnvCall ())
            | Supervisor => (E_S_EnvCall ())
            | Machine => (E_M_EnvCall ())
            excinfo := (none : (Option xlenbits))
            ext := none }) ) : SailM sync_exception )
  (pure (Trap ((← readReg cur_privilege), (CTL_TRAP t), (← readReg PC))))

def execute_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (pure (Memory_Exception ((Virtaddr (← readReg PC)), (E_Breakpoint ()))))

/-- Type quantifiers: k_ex72361# : Bool -/
def execute_DIVW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    bif (rs2_int == 0)
    then (-1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    bif ((not is_unsigned) && (quotient ≥b (2 ^i 31)))
    then (Neg.neg (2 ^i 31))
    else quotient
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex72370# : Bool -/
def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int : Int :=
    bif is_unsigned
    then (BitVec.toNat rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    bif (rs2_int == 0)
    then (-1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    bif ((not is_unsigned) && (quotient ≥b (2 ^i (xlen -i 1))))
    then (Neg.neg (2 ^i (xlen -i 1)))
    else quotient
  (wX_bits rd (to_bits_truncate (l := 64) quotient))
  (pure RETIRE_SUCCESS)

def execute_C_ILLEGAL (s : (BitVec 16)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  bif taken
  then
    (do
      let target ← do (pure ((← readReg PC) + (sign_extend (m := 64) imm)))
      match (ext_control_check_pc target) with
      | .Ext_ControlAddr_Error e => (pure (Ext_ControlAddr_Check_Failure e))
      | .Ext_ControlAddr_OK target =>
        (do
          let target_bits := (bits_of_virtaddr target)
          bif ((← (bit_to_bool (BitVec.access target_bits 1))) && (not
                 (← (currentlyEnabled Ext_Zca))))
          then (pure (Memory_Exception (target, (E_Fetch_Addr_Align ()))))
          else
            (do
              (set_next_pc target_bits)
              (pure RETIRE_SUCCESS))))
  else (pure RETIRE_SUCCESS)

def execute_ADDIW (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let result ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS)

def execute (merge_var : instruction) : SailM ExecutionResult := do
  match merge_var with
  | .UTYPE (imm, rd, op) => (execute_UTYPE imm rd op)
  | .JAL (imm, rd) => (execute_JAL imm rd)
  | .BTYPE (imm, rs2, rs1, op) => (execute_BTYPE imm rs2 rs1 op)
  | .ITYPE (imm, rs1, rd, op) => (execute_ITYPE imm rs1 rd op)
  | .SHIFTIOP (shamt, rs1, rd, op) => (execute_SHIFTIOP shamt rs1 rd op)
  | .RTYPE (rs2, rs1, rd, op) => (execute_RTYPE rs2 rs1 rd op)
  | .LOAD (imm, rs1, rd, is_unsigned, width) => (execute_LOAD imm rs1 rd is_unsigned width)
  | .STORE (imm, rs2, rs1, width) => (execute_STORE imm rs2 rs1 width)
  | .FENCE (pred, succ) => (execute_FENCE pred succ)
  | .FENCE_TSO arg0 => (execute_FENCE_TSO arg0)
  | .ECALL arg0 => (execute_ECALL arg0)
  | .MRET arg0 => (execute_MRET arg0)
  | .SRET arg0 => (execute_SRET arg0)
  | .EBREAK arg0 => (execute_EBREAK arg0)
  | .WFI arg0 => (execute_WFI arg0)
  | .SFENCE_VMA (rs1, rs2) => (execute_SFENCE_VMA rs1 rs2)
  | .ADDIW (imm, rs1, rd) => (execute_ADDIW imm rs1 rd)
  | .RTYPEW (rs2, rs1, rd, op) => (execute_RTYPEW rs2 rs1 rd op)
  | .SHIFTIWOP (shamt, rs1, rd, op) => (execute_SHIFTIWOP shamt rs1 rd op)
  | .JALR (imm, rs1, rd) => (execute_JALR imm rs1 rd)
  | .MUL (rs2, rs1, rd, mul_op) => (execute_MUL rs2 rs1 rd mul_op)
  | .DIV (rs2, rs1, rd, is_unsigned) => (execute_DIV rs2 rs1 rd is_unsigned)
  | .REM (rs2, rs1, rd, is_unsigned) => (execute_REM rs2 rs1 rd is_unsigned)
  | .MULW (rs2, rs1, rd) => (execute_MULW rs2 rs1 rd)
  | .DIVW (rs2, rs1, rd, is_unsigned) => (execute_DIVW rs2 rs1 rd is_unsigned)
  | .REMW (rs2, rs1, rd, is_unsigned) => (execute_REMW rs2 rs1 rd is_unsigned)
  | .ILLEGAL s => (pure (execute_ILLEGAL s))
  | .C_ILLEGAL s => (pure (execute_C_ILLEGAL s))

def assembly_backwards (arg_ : String) : SailM instruction := do
  match arg_ with
  | _ => throw Error.Exit

def assembly_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .UTYPE (imm, rd, op) => true
  | .JAL (imm, rd) => true
  | .JALR (imm, rs1, rd) => true
  | .BTYPE (imm, rs2, rs1, op) => true
  | .ITYPE (imm, rs1, rd, op) => true
  | .SHIFTIOP (shamt, rs1, rd, op) => true
  | .RTYPE (rs2, rs1, rd, op) => true
  | .LOAD (imm, rs1, rd, is_unsigned, width) => true
  | .STORE (imm, rs2, rs1, width) => true
  | .FENCE (pred, succ) => true
  | .FENCE_TSO () => true
  | .ECALL () => true
  | .MRET () => true
  | .SRET () => true
  | .EBREAK () => true
  | .WFI () => true
  | .SFENCE_VMA (rs1, rs2) => true
  | .ADDIW (imm, rs1, rd) =>
    (bif (xlen == 64)
    then true
    else false)
  | .RTYPEW (rs2, rs1, rd, op) =>
    (bif (xlen == 64)
    then true
    else false)
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (bif (xlen == 64)
    then true
    else false)
  | .MUL (rs2, rs1, rd, mul_op) => true
  | .DIV (rs2, rs1, rd, is_unsigned) => true
  | .REM (rs2, rs1, rd, is_unsigned) => true
  | .MULW (rs2, rs1, rd) =>
    (bif (xlen == 64)
    then true
    else false)
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (bif (xlen == 64)
    then true
    else false)
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (bif (xlen == 64)
    then true
    else false)
  | .ILLEGAL s => true
  | .C_ILLEGAL s => true

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit
