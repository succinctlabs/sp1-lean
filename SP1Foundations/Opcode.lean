import SP1Foundations.Field
import SP1Foundations.SailM
import SP1Foundations.Word

inductive Opcode where
  | ADD
  | ADDI
  | SUB
  | XOR
  | OR
  | AND
  | SLL
  | SRL
  | SRA
  | SLT
  | SLTU
  | MUl
  | MULH
  | MULHU
  | MULHSU
  | DIV
  | DIVU
  | REM
  | REMU
  | LB
  | LH
  | LW
  | LBU
  | LHU
  | SB
  | SH
  | SW
  | BEQ
  | BNE
  | BLT
  | BGE
  | BLTU
  | BGEU
  | JAL
  | JALR
  | AUIPC
  | LUI
  | ECALL
  | EBREAK
  | ADDW
  | SUBW
  | SLLW
  | SRLW
  | SRAW
  | LWU
  | LD
  | SD
  | MULW
  | DIVW
  | DIVUW
  | REMW
  | REMUW
  | UNIMP
  deriving DecidableEq

namespace Opcode

@[simp]
def trusted_instr
  (opcode : Opcode)
  (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 : Fin BB)
  : Prop :=
  match opcode with
  | ADD
  | ADDW =>
      op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0 ∧
      op_c_0 < 32 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0
  | JAL =>
      (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0) ∧
      Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)
  | JALR =>
      (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0) ∧
      Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)
  | _ => True

@[simp]
def trusted_instr_state
  (s : SailState)
  (opcode : Opcode)
  (_op_a op_b_0 _op_b_1 _op_b_2 _op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 : Fin BB)
  : Prop :=
  match opcode with
  | JALR =>
      -- let new_pc : BitVec 64 := (s.get_reg? (BitVec.ofNat 5 op_b_0.val)).get! + BitVec.signExtend 64 (BitVec.ofNat 12 (Word.toNat #v[op_c_0, op_c_1, op_c_2, op_c_3]))
      -- new_pc[1] = 0
      ((s.get_reg? (BitVec.ofNat 5 op_b_0.val)).get! + Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3]) % 4 = 0
  | _ => True

end Opcode
