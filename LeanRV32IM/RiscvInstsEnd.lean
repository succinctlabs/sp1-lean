import LeanRV32IM.Flow
import LeanRV32IM.Prelude
import LeanRV32IM.RiscvXlen
import LeanRV32IM.PreludeMemAddrtype
import LeanRV32IM.RiscvTypes
import LeanRV32IM.RiscvVmemTypes
import LeanRV32IM.RiscvRegs
import LeanRV32IM.RiscvPcAccess
import LeanRV32IM.RiscvSysRegs
import LeanRV32IM.RiscvAddrChecks
import LeanRV32IM.RiscvSysExceptions
import LeanRV32IM.RiscvSysControl
import LeanRV32IM.RiscvInstRetire
import LeanRV32IM.RiscvVmemTlb
import LeanRV32IM.RiscvVmemUtils
import LeanRV32IM.RiscvInstsBase
import LeanRV32IM.RiscvInstsMext

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV32IM.Functions

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
open cfregidx
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
  | .JAL (v__72, rd) =>
    (do
      bif ((Sail.BitVec.extractLsb v__72 0 0) == (0b0 : (BitVec 1)))
      then
        (let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__72 20 20)
        let imm_8 : (BitVec 1) := (Sail.BitVec.extractLsb v__72 11 11)
        let imm_7_0 : (BitVec 8) := (Sail.BitVec.extractLsb v__72 19 12)
        let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__72 20 20)
        let imm_18_13 : (BitVec 6) := (Sail.BitVec.extractLsb v__72 10 5)
        let imm_12_9 : (BitVec 4) := (Sail.BitVec.extractLsb v__72 4 1)
        (pure ((imm_19 : (BitVec 1)) ++ ((imm_18_13 : (BitVec 6)) ++ ((imm_12_9 : (BitVec 4)) ++ ((imm_8 : (BitVec 1)) ++ ((imm_7_0 : (BitVec 8)) ++ ((encdec_reg_forwards
                        rd) ++ (0b1101111 : (BitVec 7))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .JALR (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((0b000 : (BitVec 3)) ++ ((encdec_reg_forwards
                rd) ++ (0b1100111 : (BitVec 7)))))))
  | .BTYPE (v__74, rs2, rs1, op) =>
    (do
      bif ((Sail.BitVec.extractLsb v__74 0 0) == (0b0 : (BitVec 1)))
      then
        (let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__74 12 12)
        let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__74 12 12)
        let imm7_5_0 : (BitVec 6) := (Sail.BitVec.extractLsb v__74 10 5)
        let imm5_4_1 : (BitVec 4) := (Sail.BitVec.extractLsb v__74 4 1)
        let imm5_0 : (BitVec 1) := (Sail.BitVec.extractLsb v__74 11 11)
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
  | .STORE (v__76, rs2, rs1, width) =>
    (do
      bif (width ≤b xlen_bytes)
      then
        (let imm7 : (BitVec 7) := (Sail.BitVec.extractLsb v__76 11 5)
        let imm7 : (BitVec 7) := (Sail.BitVec.extractLsb v__76 11 5)
        let imm5 : (BitVec 5) := (Sail.BitVec.extractLsb v__76 4 0)
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
  | .ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__205 := head_exp_
    bif (let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__205 6 0)
       let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__205 11 7)
       ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_)))
    then
      (do
        let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__205 31 12)
        let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__205 6 0)
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__205 11 7)
        let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__205 31 12)
        match ((encdec_reg_backwards mapping0_), (← (encdec_uop_backwards mapping1_))) with
        | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (let v__203 := head_exp_
      bif ((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__203 11 7)
           (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__203 6 0) == (0b1101111 : (BitVec 7))))
      then
        (let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__203 31 31)
        let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__203 11 7)
        let imm_8 : (BitVec 1) := (Sail.BitVec.extractLsb v__203 20 20)
        let imm_7_0 : (BitVec 8) := (Sail.BitVec.extractLsb v__203 19 12)
        let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__203 31 31)
        let imm_18_13 : (BitVec 6) := (Sail.BitVec.extractLsb v__203 30 25)
        let imm_12_9 : (BitVec 4) := (Sail.BitVec.extractLsb v__203 24 21)
        match (encdec_reg_backwards mapping2_) with
        | rd =>
          (some
            (JAL
              (((imm_19 : (BitVec 1)) ++ ((imm_7_0 : (BitVec 8)) ++ ((imm_8 : (BitVec 1)) ++ ((imm_18_13 : (BitVec 6)) ++ ((imm_12_9 : (BitVec 4)) ++ (0b0 : (BitVec 1))))))), rd))))
      else none) with
      | .some result => (pure result)
      | none =>
        (do
          match (let v__200 := head_exp_
          bif ((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__200 11 7)
               let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__200 19 15)
               ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches mapping4_))) && (((Sail.BitVec.extractLsb
                     v__200 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__200 6 0) == (0b1100111 : (BitVec 7)))))
          then
            (let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__200 31 20)
            let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__200 11 7)
            let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__200 19 15)
            let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__200 31 20)
            match ((encdec_reg_backwards mapping3_), (encdec_reg_backwards mapping4_)) with
            | (rs1, rd) => (some (JALR (imm, rs1, rd))))
          else none) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__198 := head_exp_
                bif ((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__198 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__198 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__198 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__198 6 0) == (0b1100011 : (BitVec 7))))
                then
                  (do
                    let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__198 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__198 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__198 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__198 24 20)
                    let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__198 31 31)
                    let imm7_5_0 : (BitVec 6) := (Sail.BitVec.extractLsb v__198 30 25)
                    let imm5_4_1 : (BitVec 4) := (Sail.BitVec.extractLsb v__198 11 8)
                    let imm5_0 : (BitVec 1) := (Sail.BitVec.extractLsb v__198 7 7)
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
                    let v__196 := head_exp_
                    bif ((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__196 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__196 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__196 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__196 6 0) == (0b0010011 : (BitVec 7))))
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__196 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__196 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__196 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__196 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__196 31 20)
                        match ((encdec_reg_backwards mapping8_), (← (encdec_iop_backwards
                            mapping9_)), (encdec_reg_backwards mapping10_)) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (let v__192 := head_exp_
                      bif ((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__192 11 7)
                           let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__192 19 15)
                           ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                               mapping12_))) && (((Sail.BitVec.extractLsb v__192 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                   v__192 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__192 6 0) == (0b0010011 : (BitVec 7))))))
                      then
                        (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__192 25 20)
                        let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__192 11 7)
                        let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__192 19 15)
                        match ((encdec_reg_backwards mapping11_), (encdec_reg_backwards mapping12_)) with
                        | (rs1, rd) =>
                          (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                          then (some (SHIFTIOP (shamt, rs1, rd, SLLI)))
                          else none))
                      else none) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (let v__188 := head_exp_
                          bif ((let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__188 11 7)
                               let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__188 19 15)
                               ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                   mapping14_))) && (((Sail.BitVec.extractLsb v__188 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                       v__188 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__188 6 0) == (0b0010011 : (BitVec 7))))))
                          then
                            (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__188 25 20)
                            let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__188 11 7)
                            let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__188 19 15)
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
                              match (let v__184 := head_exp_
                              bif ((let mapping16_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__184 11 7)
                                   let mapping15_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__184 19 15)
                                   ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                       mapping16_))) && (((Sail.BitVec.extractLsb v__184 31 26) == (0b010000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                           v__184 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__184 6 0) == (0b0010011 : (BitVec 7))))))
                              then
                                (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__184 25 20)
                                let mapping16_ : (BitVec 5) := (Sail.BitVec.extractLsb v__184 11 7)
                                let mapping15_ : (BitVec 5) := (Sail.BitVec.extractLsb v__184 19 15)
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
                                  match (let v__180 := head_exp_
                                  bif ((let mapping19_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__180 11 7)
                                       let mapping18_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__180 19 15)
                                       let mapping17_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__180 24 20)
                                       ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                             mapping18_) && (encdec_reg_backwards_matches mapping19_)))) && (((Sail.BitVec.extractLsb
                                             v__180 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                               v__180 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                               v__180 6 0) == (0b0110011 : (BitVec 7))))))
                                  then
                                    (let mapping19_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__180 11 7)
                                    let mapping18_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__180 19 15)
                                    let mapping17_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__180 24 20)
                                    match ((encdec_reg_backwards mapping17_), (encdec_reg_backwards
                                      mapping18_), (encdec_reg_backwards mapping19_)) with
                                    | (rs2, rs1, rd) => (some (RTYPE (rs2, rs1, rd, ADD))))
                                  else none) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (let v__176 := head_exp_
                                      bif ((let mapping22_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__176 11 7)
                                           let mapping21_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__176 19 15)
                                           let mapping20_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__176 24 20)
                                           ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                 mapping21_) && (encdec_reg_backwards_matches
                                                 mapping22_)))) && (((Sail.BitVec.extractLsb v__176
                                                 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                   v__176 14 12) == (0b010 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__176 6 0) == (0b0110011 : (BitVec 7))))))
                                      then
                                        (let mapping22_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__176 11 7)
                                        let mapping21_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__176 19 15)
                                        let mapping20_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__176 24 20)
                                        match ((encdec_reg_backwards mapping20_), (encdec_reg_backwards
                                          mapping21_), (encdec_reg_backwards mapping22_)) with
                                        | (rs2, rs1, rd) => (some (RTYPE (rs2, rs1, rd, SLT))))
                                      else none) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (let v__172 := head_exp_
                                          bif ((let mapping25_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__172 11 7)
                                               let mapping24_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__172 19 15)
                                               let mapping23_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__172 24 20)
                                               ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                     mapping24_) && (encdec_reg_backwards_matches
                                                     mapping25_)))) && (((Sail.BitVec.extractLsb
                                                     v__172 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                       v__172 14 12) == (0b011 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                       v__172 6 0) == (0b0110011 : (BitVec 7))))))
                                          then
                                            (let mapping25_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__172 11 7)
                                            let mapping24_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__172 19 15)
                                            let mapping23_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__172 24 20)
                                            match ((encdec_reg_backwards mapping23_), (encdec_reg_backwards
                                              mapping24_), (encdec_reg_backwards mapping25_)) with
                                            | (rs2, rs1, rd) => (some (RTYPE (rs2, rs1, rd, SLTU))))
                                          else none) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (let v__168 := head_exp_
                                              bif ((let mapping28_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__168 11 7)
                                                   let mapping27_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__168 19 15)
                                                   let mapping26_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__168 24 20)
                                                   ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                         mapping27_) && (encdec_reg_backwards_matches
                                                         mapping28_)))) && (((Sail.BitVec.extractLsb
                                                         v__168 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                           v__168 14 12) == (0b111 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                           v__168 6 0) == (0b0110011 : (BitVec 7))))))
                                              then
                                                (let mapping28_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__168 11 7)
                                                let mapping27_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__168 19 15)
                                                let mapping26_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__168 24 20)
                                                match ((encdec_reg_backwards mapping26_), (encdec_reg_backwards
                                                  mapping27_), (encdec_reg_backwards mapping28_)) with
                                                | (rs2, rs1, rd) =>
                                                  (some (RTYPE (rs2, rs1, rd, AND))))
                                              else none) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (let v__164 := head_exp_
                                                  bif ((let mapping31_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__164 11 7)
                                                       let mapping30_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__164 19 15)
                                                       let mapping29_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__164 24 20)
                                                       ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                             mapping30_) && (encdec_reg_backwards_matches
                                                             mapping31_)))) && (((Sail.BitVec.extractLsb
                                                             v__164 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                               v__164 14 12) == (0b110 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                               v__164 6 0) == (0b0110011 : (BitVec 7))))))
                                                  then
                                                    (let mapping31_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__164 11 7)
                                                    let mapping30_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__164 19 15)
                                                    let mapping29_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__164 24 20)
                                                    match ((encdec_reg_backwards mapping29_), (encdec_reg_backwards
                                                      mapping30_), (encdec_reg_backwards mapping31_)) with
                                                    | (rs2, rs1, rd) =>
                                                      (some (RTYPE (rs2, rs1, rd, OR))))
                                                  else none) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (let v__160 := head_exp_
                                                      bif ((let mapping34_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__160 11 7)
                                                           let mapping33_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__160 19 15)
                                                           let mapping32_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__160 24 20)
                                                           ((encdec_reg_backwards_matches mapping32_) && ((encdec_reg_backwards_matches
                                                                 mapping33_) && (encdec_reg_backwards_matches
                                                                 mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                 v__160 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                   v__160 14 12) == (0b100 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                   v__160 6 0) == (0b0110011 : (BitVec 7))))))
                                                      then
                                                        (let mapping34_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__160 11 7)
                                                        let mapping33_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__160 19 15)
                                                        let mapping32_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__160 24 20)
                                                        match ((encdec_reg_backwards mapping32_), (encdec_reg_backwards
                                                          mapping33_), (encdec_reg_backwards
                                                          mapping34_)) with
                                                        | (rs2, rs1, rd) =>
                                                          (some (RTYPE (rs2, rs1, rd, XOR))))
                                                      else none) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (let v__156 := head_exp_
                                                          bif ((let mapping37_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__156 11 7)
                                                               let mapping36_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__156 19
                                                                   15)
                                                               let mapping35_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__156 24
                                                                   20)
                                                               ((encdec_reg_backwards_matches
                                                                   mapping35_) && ((encdec_reg_backwards_matches
                                                                     mapping36_) && (encdec_reg_backwards_matches
                                                                     mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                     v__156 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                       v__156 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                       v__156 6 0) == (0b0110011 : (BitVec 7))))))
                                                          then
                                                            (let mapping37_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__156 11 7)
                                                            let mapping36_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__156 19 15)
                                                            let mapping35_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__156 24 20)
                                                            match ((encdec_reg_backwards mapping35_), (encdec_reg_backwards
                                                              mapping36_), (encdec_reg_backwards
                                                              mapping37_)) with
                                                            | (rs2, rs1, rd) =>
                                                              (some (RTYPE (rs2, rs1, rd, SLL))))
                                                          else none) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (let v__152 := head_exp_
                                                              bif ((let mapping40_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__152
                                                                       11 7)
                                                                   let mapping39_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__152
                                                                       19 15)
                                                                   let mapping38_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__152
                                                                       24 20)
                                                                   ((encdec_reg_backwards_matches
                                                                       mapping38_) && ((encdec_reg_backwards_matches
                                                                         mapping39_) && (encdec_reg_backwards_matches
                                                                         mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                         v__152 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                           v__152 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                           v__152 6 0) == (0b0110011 : (BitVec 7))))))
                                                              then
                                                                (let mapping40_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__152 11
                                                                    7)
                                                                let mapping39_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__152 19
                                                                    15)
                                                                let mapping38_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__152 24
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
                                                                  match (let v__148 := head_exp_
                                                                  bif ((let mapping43_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__148 11 7)
                                                                       let mapping42_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__148 19 15)
                                                                       let mapping41_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__148 24 20)
                                                                       ((encdec_reg_backwards_matches
                                                                           mapping41_) && ((encdec_reg_backwards_matches
                                                                             mapping42_) && (encdec_reg_backwards_matches
                                                                             mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                             v__148 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                               v__148 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                               v__148 6 0) == (0b0110011 : (BitVec 7))))))
                                                                  then
                                                                    (let mapping43_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__148
                                                                        11 7)
                                                                    let mapping42_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__148
                                                                        19 15)
                                                                    let mapping41_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__148
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
                                                                      match (let v__144 := head_exp_
                                                                      bif ((let mapping46_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__144 11 7)
                                                                           let mapping45_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__144 19 15)
                                                                           let mapping44_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__144 24 20)
                                                                           ((encdec_reg_backwards_matches
                                                                               mapping44_) && ((encdec_reg_backwards_matches
                                                                                 mapping45_) && (encdec_reg_backwards_matches
                                                                                 mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                 v__144 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                   v__144 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                   v__144 6 0) == (0b0110011 : (BitVec 7))))))
                                                                      then
                                                                        (let mapping46_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__144 11 7)
                                                                        let mapping45_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__144 19 15)
                                                                        let mapping44_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__144 24 20)
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
                                                                          match (let v__142 :=
                                                                            head_exp_
                                                                          bif ((let mapping50_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__142 11 7)
                                                                               let mapping49_ : (BitVec 2) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__142 13 12)
                                                                               let mapping48_ : (BitVec 1) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__142 14 14)
                                                                               let mapping47_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__142 19 15)
                                                                               ((encdec_reg_backwards_matches
                                                                                   mapping47_) && ((bool_bits_backwards_matches
                                                                                     mapping48_) && ((size_enc_backwards_matches
                                                                                       mapping49_) && (encdec_reg_backwards_matches
                                                                                       mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                   v__142 6 0) == (0b0000011 : (BitVec 7))))
                                                                          then
                                                                            (let imm : (BitVec 12) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__142 31 20)
                                                                            let mapping50_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__142 11 7)
                                                                            let mapping49_ : (BitVec 2) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__142 13 12)
                                                                            let mapping48_ : (BitVec 1) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__142 14 14)
                                                                            let mapping47_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__142 19 15)
                                                                            let imm : (BitVec 12) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__142 31 20)
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
                                                                              match (let v__139 :=
                                                                                head_exp_
                                                                              bif ((let mapping53_ : (BitVec 2) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__139 13 12)
                                                                                   let mapping52_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__139 19 15)
                                                                                   let mapping51_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__139 24 20)
                                                                                   ((encdec_reg_backwards_matches
                                                                                       mapping51_) && ((encdec_reg_backwards_matches
                                                                                         mapping52_) && (size_enc_backwards_matches
                                                                                         mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                         v__139 14
                                                                                         14) == (0b0 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                         v__139 6 0) == (0b0100011 : (BitVec 7)))))
                                                                              then
                                                                                (let imm7 : (BitVec 7) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__139 31 25)
                                                                                let mapping53_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__139 13 12)
                                                                                let mapping52_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__139 19 15)
                                                                                let mapping51_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__139 24 20)
                                                                                let imm7 : (BitVec 7) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__139 31 25)
                                                                                let imm5 : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__139 11 7)
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
                                                                                    let v__88 :=
                                                                                      head_exp_
                                                                                    bif (((Sail.BitVec.extractLsb
                                                                                             v__88
                                                                                             31 28) == (0x0 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                             v__88
                                                                                             19 0) == (0x0000F : (BitVec 20))))
                                                                                    then
                                                                                      (let succ : (BitVec 4) :=
                                                                                        (Sail.BitVec.extractLsb
                                                                                          v__88 23
                                                                                          20)
                                                                                      let pred : (BitVec 4) :=
                                                                                        (Sail.BitVec.extractLsb
                                                                                          v__88 27
                                                                                          24)
                                                                                      (pure (some
                                                                                          (FENCE
                                                                                            (pred, succ)))))
                                                                                    else
                                                                                      (do
                                                                                        bif (v__88 == (0x8330000F : (BitVec 32)))
                                                                                        then
                                                                                          (pure (some
                                                                                              (FENCE_TSO
                                                                                                ())))
                                                                                        else
                                                                                          (do
                                                                                            bif (v__88 == (0x00000073 : (BitVec 32)))
                                                                                            then
                                                                                              (pure (some
                                                                                                  (ECALL
                                                                                                    ())))
                                                                                            else
                                                                                              (do
                                                                                                bif (v__88 == (0x30200073 : (BitVec 32)))
                                                                                                then
                                                                                                  (pure (some
                                                                                                      (MRET
                                                                                                        ())))
                                                                                                else
                                                                                                  (do
                                                                                                    bif (v__88 == (0x10200073 : (BitVec 32)))
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          (SRET
                                                                                                            ())))
                                                                                                    else
                                                                                                      (do
                                                                                                        bif (v__88 == (0x00100073 : (BitVec 32)))
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              (EBREAK
                                                                                                                ())))
                                                                                                        else
                                                                                                          (do
                                                                                                            bif (v__88 == (0x10500073 : (BitVec 32)))
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  (WFI
                                                                                                                    ())))
                                                                                                            else
                                                                                                              (do
                                                                                                                bif ((let mapping55_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__88
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     let mapping54_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__88
                                                                                                                         24
                                                                                                                         20)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping54_) && (encdec_reg_backwards_matches
                                                                                                                         mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__88
                                                                                                                           31
                                                                                                                           25) == (0b0001001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__88
                                                                                                                           14
                                                                                                                           0) == (0b000000001110011 : (BitVec 15)))))
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping55_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__88
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    let mapping54_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__88
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
                                                                                      match (← do
                                                                                        let v__85 :=
                                                                                          head_exp_
                                                                                        bif ((let mapping59_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__85
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping58_ : (BitVec 3) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__85
                                                                                                 14
                                                                                                 12)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__85
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__85
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && ((encdec_mul_op_backwards_matches
                                                                                                     mapping58_) && (encdec_reg_backwards_matches
                                                                                                     mapping59_))))) && (((Sail.BitVec.extractLsb
                                                                                                   v__85
                                                                                                   31
                                                                                                   25) == (0b0000001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                   v__85
                                                                                                   6
                                                                                                   0) == (0b0110011 : (BitVec 7)))))
                                                                                        then
                                                                                          (do
                                                                                            let mapping59_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__85
                                                                                                11 7)
                                                                                            let mapping58_ : (BitVec 3) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__85
                                                                                                14
                                                                                                12)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__85
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__85
                                                                                                24
                                                                                                20)
                                                                                            match ((encdec_reg_backwards
                                                                                              mapping56_), (encdec_reg_backwards
                                                                                              mapping57_), (← (encdec_mul_op_backwards
                                                                                                mapping58_)), (encdec_reg_backwards
                                                                                              mapping59_)) with
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
                                                                                            let v__81 :=
                                                                                              head_exp_
                                                                                            bif ((let mapping63_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__81
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping62_ : (BitVec 1) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__81
                                                                                                     12
                                                                                                     12)
                                                                                                 let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__81
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__81
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping60_) && ((encdec_reg_backwards_matches
                                                                                                       mapping61_) && ((bool_bits_backwards_matches
                                                                                                         mapping62_) && (encdec_reg_backwards_matches
                                                                                                         mapping63_))))) && (((Sail.BitVec.extractLsb
                                                                                                       v__81
                                                                                                       31
                                                                                                       25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__81
                                                                                                         14
                                                                                                         13) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                         v__81
                                                                                                         6
                                                                                                         0) == (0b0110011 : (BitVec 7))))))
                                                                                            then
                                                                                              (do
                                                                                                let mapping63_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__81
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping62_ : (BitVec 1) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__81
                                                                                                    12
                                                                                                    12)
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__81
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__81
                                                                                                    24
                                                                                                    20)
                                                                                                match ((encdec_reg_backwards
                                                                                                  mapping60_), (encdec_reg_backwards
                                                                                                  mapping61_), (bool_bits_backwards
                                                                                                  mapping62_), (encdec_reg_backwards
                                                                                                  mapping63_)) with
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
                                                                                                let v__77 :=
                                                                                                  head_exp_
                                                                                                bif ((let mapping67_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__77
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping66_ : (BitVec 1) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__77
                                                                                                         12
                                                                                                         12)
                                                                                                     let mapping65_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__77
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__77
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping64_) && ((encdec_reg_backwards_matches
                                                                                                           mapping65_) && ((bool_bits_backwards_matches
                                                                                                             mapping66_) && (encdec_reg_backwards_matches
                                                                                                             mapping67_))))) && (((Sail.BitVec.extractLsb
                                                                                                           v__77
                                                                                                           31
                                                                                                           25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__77
                                                                                                             14
                                                                                                             13) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                             v__77
                                                                                                             6
                                                                                                             0) == (0b0110011 : (BitVec 7))))))
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping67_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__77
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping66_ : (BitVec 1) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__77
                                                                                                        12
                                                                                                        12)
                                                                                                    let mapping65_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__77
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__77
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((encdec_reg_backwards
                                                                                                      mapping64_), (encdec_reg_backwards
                                                                                                      mapping65_), (bool_bits_backwards
                                                                                                      mapping66_), (encdec_reg_backwards
                                                                                                      mapping67_)) with
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
                                                                                                (match head_exp_ with
                                                                                                | s =>
                                                                                                  (pure (ILLEGAL
                                                                                                      s))))))))))))))))))))))))))

def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__206, rd) =>
    (bif ((Sail.BitVec.extractLsb v__206 0 0) == (0b0 : (BitVec 1)))
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__208, rs2, rs1, op) =>
    (bif ((Sail.BitVec.extractLsb v__208 0 0) == (0b0 : (BitVec 1)))
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
  | .STORE (v__210, rs2, rs1, width) =>
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
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__339 := head_exp_
    bif (let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__339 6 0)
       let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__339 11 7)
       ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_)))
    then
      (do
        let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__339 6 0)
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__339 11 7)
        match ((encdec_reg_backwards mapping0_), (← (encdec_uop_backwards mapping1_))) with
        | (rd, op) => (pure (some true)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (let v__337 := head_exp_
      bif ((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 11 7)
           (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__337 6 0) == (0b1101111 : (BitVec 7))))
      then
        (let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 11 7)
        match (encdec_reg_backwards mapping2_) with
        | rd => (some true))
      else none) with
      | .some result => (pure result)
      | none =>
        (do
          match (let v__334 := head_exp_
          bif ((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__334 11 7)
               let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__334 19 15)
               ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches mapping4_))) && (((Sail.BitVec.extractLsb
                     v__334 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__334 6 0) == (0b1100111 : (BitVec 7)))))
          then
            (let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__334 11 7)
            let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__334 19 15)
            match ((encdec_reg_backwards mapping3_), (encdec_reg_backwards mapping4_)) with
            | (rs1, rd) => (some true))
          else none) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__332 := head_exp_
                bif ((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__332 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__332 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__332 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__332 6 0) == (0b1100011 : (BitVec 7))))
                then
                  (do
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__332 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__332 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__332 24 20)
                    match ((encdec_reg_backwards mapping5_), (encdec_reg_backwards mapping6_), (← (encdec_bop_backwards
                        mapping7_))) with
                    | (rs2, rs1, op) => (pure (some true)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__330 := head_exp_
                    bif ((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__330 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__330 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__330 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__330 6 0) == (0b0010011 : (BitVec 7))))
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__330 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__330 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__330 11 7)
                        match ((encdec_reg_backwards mapping8_), (← (encdec_iop_backwards
                            mapping9_)), (encdec_reg_backwards mapping10_)) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (let v__326 := head_exp_
                      bif ((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__326 11 7)
                           let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__326 19 15)
                           ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                               mapping12_))) && (((Sail.BitVec.extractLsb v__326 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                   v__326 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__326 6 0) == (0b0010011 : (BitVec 7))))))
                      then
                        (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__326 25 20)
                        let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__326 11 7)
                        let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__326 19 15)
                        match ((encdec_reg_backwards mapping11_), (encdec_reg_backwards mapping12_)) with
                        | (rs1, rd) =>
                          (bif ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))
                          then (some true)
                          else none))
                      else none) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (let v__322 := head_exp_
                          bif ((let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__322 11 7)
                               let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__322 19 15)
                               ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                   mapping14_))) && (((Sail.BitVec.extractLsb v__322 31 26) == (0b000000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                       v__322 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__322 6 0) == (0b0010011 : (BitVec 7))))))
                          then
                            (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__322 25 20)
                            let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__322 11 7)
                            let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__322 19 15)
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
                              match (let v__318 := head_exp_
                              bif ((let mapping16_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__318 11 7)
                                   let mapping15_ : (BitVec 5) :=
                                     (Sail.BitVec.extractLsb v__318 19 15)
                                   ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                       mapping16_))) && (((Sail.BitVec.extractLsb v__318 31 26) == (0b010000 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                           v__318 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__318 6 0) == (0b0010011 : (BitVec 7))))))
                              then
                                (let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__318 25 20)
                                let mapping16_ : (BitVec 5) := (Sail.BitVec.extractLsb v__318 11 7)
                                let mapping15_ : (BitVec 5) := (Sail.BitVec.extractLsb v__318 19 15)
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
                                  match (let v__314 := head_exp_
                                  bif ((let mapping19_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__314 11 7)
                                       let mapping18_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__314 19 15)
                                       let mapping17_ : (BitVec 5) :=
                                         (Sail.BitVec.extractLsb v__314 24 20)
                                       ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                             mapping18_) && (encdec_reg_backwards_matches mapping19_)))) && (((Sail.BitVec.extractLsb
                                             v__314 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                               v__314 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                               v__314 6 0) == (0b0110011 : (BitVec 7))))))
                                  then
                                    (let mapping19_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__314 11 7)
                                    let mapping18_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__314 19 15)
                                    let mapping17_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__314 24 20)
                                    match ((encdec_reg_backwards mapping17_), (encdec_reg_backwards
                                      mapping18_), (encdec_reg_backwards mapping19_)) with
                                    | (rs2, rs1, rd) => (some true))
                                  else none) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (let v__310 := head_exp_
                                      bif ((let mapping22_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__310 11 7)
                                           let mapping21_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__310 19 15)
                                           let mapping20_ : (BitVec 5) :=
                                             (Sail.BitVec.extractLsb v__310 24 20)
                                           ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                 mapping21_) && (encdec_reg_backwards_matches
                                                 mapping22_)))) && (((Sail.BitVec.extractLsb v__310
                                                 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                   v__310 14 12) == (0b010 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__310 6 0) == (0b0110011 : (BitVec 7))))))
                                      then
                                        (let mapping22_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__310 11 7)
                                        let mapping21_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__310 19 15)
                                        let mapping20_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__310 24 20)
                                        match ((encdec_reg_backwards mapping20_), (encdec_reg_backwards
                                          mapping21_), (encdec_reg_backwards mapping22_)) with
                                        | (rs2, rs1, rd) => (some true))
                                      else none) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (let v__306 := head_exp_
                                          bif ((let mapping25_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__306 11 7)
                                               let mapping24_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__306 19 15)
                                               let mapping23_ : (BitVec 5) :=
                                                 (Sail.BitVec.extractLsb v__306 24 20)
                                               ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                     mapping24_) && (encdec_reg_backwards_matches
                                                     mapping25_)))) && (((Sail.BitVec.extractLsb
                                                     v__306 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                       v__306 14 12) == (0b011 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                       v__306 6 0) == (0b0110011 : (BitVec 7))))))
                                          then
                                            (let mapping25_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__306 11 7)
                                            let mapping24_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__306 19 15)
                                            let mapping23_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__306 24 20)
                                            match ((encdec_reg_backwards mapping23_), (encdec_reg_backwards
                                              mapping24_), (encdec_reg_backwards mapping25_)) with
                                            | (rs2, rs1, rd) => (some true))
                                          else none) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (let v__302 := head_exp_
                                              bif ((let mapping28_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__302 11 7)
                                                   let mapping27_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__302 19 15)
                                                   let mapping26_ : (BitVec 5) :=
                                                     (Sail.BitVec.extractLsb v__302 24 20)
                                                   ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                         mapping27_) && (encdec_reg_backwards_matches
                                                         mapping28_)))) && (((Sail.BitVec.extractLsb
                                                         v__302 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                           v__302 14 12) == (0b111 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                           v__302 6 0) == (0b0110011 : (BitVec 7))))))
                                              then
                                                (let mapping28_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__302 11 7)
                                                let mapping27_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__302 19 15)
                                                let mapping26_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__302 24 20)
                                                match ((encdec_reg_backwards mapping26_), (encdec_reg_backwards
                                                  mapping27_), (encdec_reg_backwards mapping28_)) with
                                                | (rs2, rs1, rd) => (some true))
                                              else none) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (let v__298 := head_exp_
                                                  bif ((let mapping31_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__298 11 7)
                                                       let mapping30_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__298 19 15)
                                                       let mapping29_ : (BitVec 5) :=
                                                         (Sail.BitVec.extractLsb v__298 24 20)
                                                       ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                             mapping30_) && (encdec_reg_backwards_matches
                                                             mapping31_)))) && (((Sail.BitVec.extractLsb
                                                             v__298 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                               v__298 14 12) == (0b110 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                               v__298 6 0) == (0b0110011 : (BitVec 7))))))
                                                  then
                                                    (let mapping31_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__298 11 7)
                                                    let mapping30_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__298 19 15)
                                                    let mapping29_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__298 24 20)
                                                    match ((encdec_reg_backwards mapping29_), (encdec_reg_backwards
                                                      mapping30_), (encdec_reg_backwards mapping31_)) with
                                                    | (rs2, rs1, rd) => (some true))
                                                  else none) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (let v__294 := head_exp_
                                                      bif ((let mapping34_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__294 11 7)
                                                           let mapping33_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__294 19 15)
                                                           let mapping32_ : (BitVec 5) :=
                                                             (Sail.BitVec.extractLsb v__294 24 20)
                                                           ((encdec_reg_backwards_matches mapping32_) && ((encdec_reg_backwards_matches
                                                                 mapping33_) && (encdec_reg_backwards_matches
                                                                 mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                 v__294 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                   v__294 14 12) == (0b100 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                   v__294 6 0) == (0b0110011 : (BitVec 7))))))
                                                      then
                                                        (let mapping34_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__294 11 7)
                                                        let mapping33_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__294 19 15)
                                                        let mapping32_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__294 24 20)
                                                        match ((encdec_reg_backwards mapping32_), (encdec_reg_backwards
                                                          mapping33_), (encdec_reg_backwards
                                                          mapping34_)) with
                                                        | (rs2, rs1, rd) => (some true))
                                                      else none) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (let v__290 := head_exp_
                                                          bif ((let mapping37_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__290 11 7)
                                                               let mapping36_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__290 19
                                                                   15)
                                                               let mapping35_ : (BitVec 5) :=
                                                                 (Sail.BitVec.extractLsb v__290 24
                                                                   20)
                                                               ((encdec_reg_backwards_matches
                                                                   mapping35_) && ((encdec_reg_backwards_matches
                                                                     mapping36_) && (encdec_reg_backwards_matches
                                                                     mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                     v__290 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                       v__290 14 12) == (0b001 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                       v__290 6 0) == (0b0110011 : (BitVec 7))))))
                                                          then
                                                            (let mapping37_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__290 11 7)
                                                            let mapping36_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__290 19 15)
                                                            let mapping35_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__290 24 20)
                                                            match ((encdec_reg_backwards mapping35_), (encdec_reg_backwards
                                                              mapping36_), (encdec_reg_backwards
                                                              mapping37_)) with
                                                            | (rs2, rs1, rd) => (some true))
                                                          else none) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (let v__286 := head_exp_
                                                              bif ((let mapping40_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__286
                                                                       11 7)
                                                                   let mapping39_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__286
                                                                       19 15)
                                                                   let mapping38_ : (BitVec 5) :=
                                                                     (Sail.BitVec.extractLsb v__286
                                                                       24 20)
                                                                   ((encdec_reg_backwards_matches
                                                                       mapping38_) && ((encdec_reg_backwards_matches
                                                                         mapping39_) && (encdec_reg_backwards_matches
                                                                         mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                         v__286 31 25) == (0b0000000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                           v__286 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                           v__286 6 0) == (0b0110011 : (BitVec 7))))))
                                                              then
                                                                (let mapping40_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__286 11
                                                                    7)
                                                                let mapping39_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__286 19
                                                                    15)
                                                                let mapping38_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__286 24
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
                                                                  match (let v__282 := head_exp_
                                                                  bif ((let mapping43_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__282 11 7)
                                                                       let mapping42_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__282 19 15)
                                                                       let mapping41_ : (BitVec 5) :=
                                                                         (Sail.BitVec.extractLsb
                                                                           v__282 24 20)
                                                                       ((encdec_reg_backwards_matches
                                                                           mapping41_) && ((encdec_reg_backwards_matches
                                                                             mapping42_) && (encdec_reg_backwards_matches
                                                                             mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                             v__282 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                               v__282 14 12) == (0b000 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                               v__282 6 0) == (0b0110011 : (BitVec 7))))))
                                                                  then
                                                                    (let mapping43_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__282
                                                                        11 7)
                                                                    let mapping42_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__282
                                                                        19 15)
                                                                    let mapping41_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__282
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
                                                                      match (let v__278 := head_exp_
                                                                      bif ((let mapping46_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__278 11 7)
                                                                           let mapping45_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__278 19 15)
                                                                           let mapping44_ : (BitVec 5) :=
                                                                             (Sail.BitVec.extractLsb
                                                                               v__278 24 20)
                                                                           ((encdec_reg_backwards_matches
                                                                               mapping44_) && ((encdec_reg_backwards_matches
                                                                                 mapping45_) && (encdec_reg_backwards_matches
                                                                                 mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                 v__278 31 25) == (0b0100000 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                   v__278 14 12) == (0b101 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                   v__278 6 0) == (0b0110011 : (BitVec 7))))))
                                                                      then
                                                                        (let mapping46_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__278 11 7)
                                                                        let mapping45_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__278 19 15)
                                                                        let mapping44_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__278 24 20)
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
                                                                          match (let v__276 :=
                                                                            head_exp_
                                                                          bif ((let mapping50_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__276 11 7)
                                                                               let mapping49_ : (BitVec 2) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__276 13 12)
                                                                               let mapping48_ : (BitVec 1) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__276 14 14)
                                                                               let mapping47_ : (BitVec 5) :=
                                                                                 (Sail.BitVec.extractLsb
                                                                                   v__276 19 15)
                                                                               ((encdec_reg_backwards_matches
                                                                                   mapping47_) && ((bool_bits_backwards_matches
                                                                                     mapping48_) && ((size_enc_backwards_matches
                                                                                       mapping49_) && (encdec_reg_backwards_matches
                                                                                       mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                   v__276 6 0) == (0b0000011 : (BitVec 7))))
                                                                          then
                                                                            (let mapping50_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__276 11 7)
                                                                            let mapping49_ : (BitVec 2) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__276 13 12)
                                                                            let mapping48_ : (BitVec 1) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__276 14 14)
                                                                            let mapping47_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__276 19 15)
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
                                                                              match (let v__273 :=
                                                                                head_exp_
                                                                              bif ((let mapping53_ : (BitVec 2) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__273 13 12)
                                                                                   let mapping52_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__273 19 15)
                                                                                   let mapping51_ : (BitVec 5) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__273 24 20)
                                                                                   ((encdec_reg_backwards_matches
                                                                                       mapping51_) && ((encdec_reg_backwards_matches
                                                                                         mapping52_) && (size_enc_backwards_matches
                                                                                         mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                         v__273 14
                                                                                         14) == (0b0 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                         v__273 6 0) == (0b0100011 : (BitVec 7)))))
                                                                              then
                                                                                (let mapping53_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__273 13 12)
                                                                                let mapping52_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__273 19 15)
                                                                                let mapping51_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__273 24 20)
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
                                                                                    let v__222 :=
                                                                                      head_exp_
                                                                                    bif (((Sail.BitVec.extractLsb
                                                                                             v__222
                                                                                             31 28) == (0x0 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                             v__222
                                                                                             19 0) == (0x0000F : (BitVec 20))))
                                                                                    then
                                                                                      (pure (some
                                                                                          true))
                                                                                    else
                                                                                      (do
                                                                                        bif (v__222 == (0x8330000F : (BitVec 32)))
                                                                                        then
                                                                                          (pure (some
                                                                                              true))
                                                                                        else
                                                                                          (do
                                                                                            bif (v__222 == (0x00000073 : (BitVec 32)))
                                                                                            then
                                                                                              (pure (some
                                                                                                  true))
                                                                                            else
                                                                                              (do
                                                                                                bif (v__222 == (0x30200073 : (BitVec 32)))
                                                                                                then
                                                                                                  (pure (some
                                                                                                      true))
                                                                                                else
                                                                                                  (do
                                                                                                    bif (v__222 == (0x10200073 : (BitVec 32)))
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          true))
                                                                                                    else
                                                                                                      (do
                                                                                                        bif (v__222 == (0x00100073 : (BitVec 32)))
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              true))
                                                                                                        else
                                                                                                          (do
                                                                                                            bif (v__222 == (0x10500073 : (BitVec 32)))
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  true))
                                                                                                            else
                                                                                                              (do
                                                                                                                bif ((let mapping55_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__222
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     let mapping54_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__222
                                                                                                                         24
                                                                                                                         20)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping54_) && (encdec_reg_backwards_matches
                                                                                                                         mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__222
                                                                                                                           31
                                                                                                                           25) == (0b0001001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__222
                                                                                                                           14
                                                                                                                           0) == (0b000000001110011 : (BitVec 15)))))
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping55_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__222
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    let mapping54_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__222
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
                                                                                      match (← do
                                                                                        let v__219 :=
                                                                                          head_exp_
                                                                                        bif ((let mapping59_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__219
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping58_ : (BitVec 3) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__219
                                                                                                 14
                                                                                                 12)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__219
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__219
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && ((encdec_mul_op_backwards_matches
                                                                                                     mapping58_) && (encdec_reg_backwards_matches
                                                                                                     mapping59_))))) && (((Sail.BitVec.extractLsb
                                                                                                   v__219
                                                                                                   31
                                                                                                   25) == (0b0000001 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                   v__219
                                                                                                   6
                                                                                                   0) == (0b0110011 : (BitVec 7)))))
                                                                                        then
                                                                                          (do
                                                                                            let mapping59_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__219
                                                                                                11 7)
                                                                                            let mapping58_ : (BitVec 3) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__219
                                                                                                14
                                                                                                12)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__219
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__219
                                                                                                24
                                                                                                20)
                                                                                            match ((encdec_reg_backwards
                                                                                              mapping56_), (encdec_reg_backwards
                                                                                              mapping57_), (← (encdec_mul_op_backwards
                                                                                                mapping58_)), (encdec_reg_backwards
                                                                                              mapping59_)) with
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
                                                                                            let v__215 :=
                                                                                              head_exp_
                                                                                            bif ((let mapping63_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__215
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping62_ : (BitVec 1) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__215
                                                                                                     12
                                                                                                     12)
                                                                                                 let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__215
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__215
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping60_) && ((encdec_reg_backwards_matches
                                                                                                       mapping61_) && ((bool_bits_backwards_matches
                                                                                                         mapping62_) && (encdec_reg_backwards_matches
                                                                                                         mapping63_))))) && (((Sail.BitVec.extractLsb
                                                                                                       v__215
                                                                                                       31
                                                                                                       25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__215
                                                                                                         14
                                                                                                         13) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                         v__215
                                                                                                         6
                                                                                                         0) == (0b0110011 : (BitVec 7))))))
                                                                                            then
                                                                                              (do
                                                                                                let mapping63_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__215
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping62_ : (BitVec 1) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__215
                                                                                                    12
                                                                                                    12)
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__215
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__215
                                                                                                    24
                                                                                                    20)
                                                                                                match ((encdec_reg_backwards
                                                                                                  mapping60_), (encdec_reg_backwards
                                                                                                  mapping61_), (bool_bits_backwards
                                                                                                  mapping62_), (encdec_reg_backwards
                                                                                                  mapping63_)) with
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
                                                                                                let v__211 :=
                                                                                                  head_exp_
                                                                                                bif ((let mapping67_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__211
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping66_ : (BitVec 1) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__211
                                                                                                         12
                                                                                                         12)
                                                                                                     let mapping65_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__211
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__211
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping64_) && ((encdec_reg_backwards_matches
                                                                                                           mapping65_) && ((bool_bits_backwards_matches
                                                                                                             mapping66_) && (encdec_reg_backwards_matches
                                                                                                             mapping67_))))) && (((Sail.BitVec.extractLsb
                                                                                                           v__211
                                                                                                           31
                                                                                                           25) == (0b0000001 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__211
                                                                                                             14
                                                                                                             13) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                             v__211
                                                                                                             6
                                                                                                             0) == (0b0110011 : (BitVec 7))))))
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping67_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__211
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping66_ : (BitVec 1) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__211
                                                                                                        12
                                                                                                        12)
                                                                                                    let mapping65_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__211
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__211
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((encdec_reg_backwards
                                                                                                      mapping64_), (encdec_reg_backwards
                                                                                                      mapping65_), (bool_bits_backwards
                                                                                                      mapping66_), (encdec_reg_backwards
                                                                                                      mapping67_)) with
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
                                                                                                (match head_exp_ with
                                                                                                | s =>
                                                                                                  (pure true)))))))))))))))))))))))))

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
  let off : xlenbits := (sign_extend (m := 32) (imm ++ (0x000 : (BitVec 12))))
  (wX_bits rd
    (← do
      match op with
      | LUI => (pure off)
      | AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, width ∈ {1, 2, 4, 8} -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 32) imm)
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

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | SLT =>
        (pure (zero_extend (m := 32)
            (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | SLTU =>
        (pure (zero_extend (m := 32)
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

/-- Type quantifiers: k_ex71529# : Bool -/
def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    bif is_unsigned
    then (BitVec.toNat rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    bif is_unsigned
    then (BitVec.toNat rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    bif (rs2_int == 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits_truncate (l := 32) remainder))
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

/-- Type quantifiers: width : Nat, k_ex71549# : Bool, width ∈ {1, 2, 4, 8} -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 32) imm)
  assert (width ≤b xlen_bytes) "model/riscv_insts_base.sail:293.28-293.29"
  match (← (vmem_read rs1 offset width (Read Data) false false false)) with
  | .Ok data =>
    (do
      (wX_bits rd (extend_value is_unsigned data))
      (pure RETIRE_SUCCESS))
  | .Err e => (pure e)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let t ← (( do (pure ((← (rX_bits rs1)) + (sign_extend (m := 32) imm))) ) : SailM xlenbits )
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
  let target ← do (pure ((← readReg PC) + (sign_extend (m := 32) imm)))
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
  let immext : xlenbits := (sign_extend (m := 32) imm)
  (wX_bits rd
    (← do
      match op with
      | ADDI => (pure ((← (rX_bits rs1)) + immext))
      | SLTI => (pure (zero_extend (m := 32) (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) immext))))
      | SLTIU =>
        (pure (zero_extend (m := 32) (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) immext))))
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
  | (v__340, v__341) =>
    (do
      bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
               v__341 1 0) == (0b11 : (BitVec 2))))
      then (sail_barrier Barrier_RISCV_rw_rw)
      else
        (do
          bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                   v__341 1 0) == (0b11 : (BitVec 2))))
          then (sail_barrier Barrier_RISCV_r_rw)
          else
            (do
              bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                       v__341 1 0) == (0b10 : (BitVec 2))))
              then (sail_barrier Barrier_RISCV_r_r)
              else
                (do
                  bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                           v__341 1 0) == (0b01 : (BitVec 2))))
                  then (sail_barrier Barrier_RISCV_rw_w)
                  else
                    (do
                      bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b01 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                               v__341 1 0) == (0b01 : (BitVec 2))))
                      then (sail_barrier Barrier_RISCV_w_w)
                      else
                        (do
                          bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b01 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                   v__341 1 0) == (0b11 : (BitVec 2))))
                          then (sail_barrier Barrier_RISCV_w_rw)
                          else
                            (do
                              bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b11 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                       v__341 1 0) == (0b10 : (BitVec 2))))
                              then (sail_barrier Barrier_RISCV_rw_r)
                              else
                                (do
                                  bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b10 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                           v__341 1 0) == (0b01 : (BitVec 2))))
                                  then (sail_barrier Barrier_RISCV_r_w)
                                  else
                                    (do
                                      bif (((Sail.BitVec.extractLsb v__340 1 0) == (0b01 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                               v__341 1 0) == (0b10 : (BitVec 2))))
                                      then (sail_barrier Barrier_RISCV_w_r)
                                      else
                                        (bif ((Sail.BitVec.extractLsb v__341 1 0) == (0b00 : (BitVec 2)))
                                        then (pure ())
                                        else
                                          (bif ((Sail.BitVec.extractLsb v__340 1 0) == (0b00 : (BitVec 2)))
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

/-- Type quantifiers: k_ex71618# : Bool -/
def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    bif is_unsigned
    then (BitVec.toNat rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
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
  (wX_bits rd (to_bits_truncate (l := 32) quotient))
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
      let target ← do (pure ((← readReg PC) + (sign_extend (m := 32) imm)))
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
  | .JALR (imm, rs1, rd) => (execute_JALR imm rs1 rd)
  | .MUL (rs2, rs1, rd, mul_op) => (execute_MUL rs2 rs1 rd mul_op)
  | .DIV (rs2, rs1, rd, is_unsigned) => (execute_DIV rs2 rs1 rd is_unsigned)
  | .REM (rs2, rs1, rd, is_unsigned) => (execute_REM rs2 rs1 rd is_unsigned)
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
  | .MUL (rs2, rs1, rd, mul_op) => true
  | .DIV (rs2, rs1, rd, is_unsigned) => true
  | .REM (rs2, rs1, rd, is_unsigned) => true
  | .ILLEGAL s => true
  | .C_ILLEGAL s => true

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

