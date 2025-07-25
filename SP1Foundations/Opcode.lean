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
def i_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)

@[simp]
def shift_i_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 2^5 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def w_shift_i_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 2^6 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def r_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB) : Prop :=
  (imm_b = 0 ∧ imm_c = 0)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 32 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def b_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 13 op_c_0)

@[simp]
def trusted_instr
  (opcode : Opcode)
  (op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin BB)
  : Prop :=
  match opcode with
  | ADD | SUB | SUBW =>
      r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | ADDI | JALR =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | AND | OR | XOR | SLT | SLTU =>
      -- We can actually just do `r_type_constraints ∨ i_type_constraints` to
      -- save the duplicate `imm_c = (0|1)` constraints, but for simplicity of
      -- proving (i.e. casing) and readability, let's be redundant.
      (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | BEQ | BNE | BLT | BGE | BLTU | BGEU =>
      b_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SLL | SRL | SRA =>
      (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → shift_i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | LUI | AUIPC =>
      (imm_b = 1 ∧ imm_c = 1)
      ∧ op_b_0 >= 2^12
      ∧ BitVec.signExtend 64 (BitVec.ofNat 32 (op_b_0.val + op_b_1.val * 65536)) = Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3]
  | JAL =>
      (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
      -- 2^12 = 4096
      ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 21 (op_c_0.val + op_c_1.val * 65536))
  | LB | LH | LW | LD | LBU | LHU =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SB | SH | SW | SD =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | ADDW =>
      -- ADDW
      (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      -- ADDIW
      ∧ (imm_c = 1 → op_c_0 < 2^12 ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0))
  | SLLW | SRLW | SRAW =>
      imm_b = 0
      ∧ (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → w_shift_i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | UNIMP | ECALL | EBREAK => True
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
