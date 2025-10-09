import SP1Foundations.Field

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
  | MUL
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

@[simp] lemma ofNat_33 : Opcode.ofNat 33 = Opcode.JAL := rfl

@[simp] lemma ofNat_34 : Opcode.ofNat 34 = Opcode.JALR := rfl

end Opcode
