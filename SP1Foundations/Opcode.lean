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
def i_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 : Fin BB) : Prop :=
  op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)

@[simp]
def trusted_instr
  (opcode : Opcode)
  (op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB)
  : Prop :=
  match opcode with
  | ADD =>
      op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0
      ∧ op_c_0 < 32 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0
  | ADDI =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3
  | ADDW =>
      imm_b = 0 
      ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
      ∧ (imm_c = 0 → op_c_0 < 65536 ∧ op_c_1 < 65536 ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 32 (op_c_0.val + op_c_1.val * 65536)))
      ∧ (imm_c = 1 → op_c_0 < 2^12 ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0))
  | JAL =>
      (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
      -- 2^12 = 4096
      ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)
  | JALR =>
      (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
      -- sign_extend is being calculated correctly
      ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)
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
