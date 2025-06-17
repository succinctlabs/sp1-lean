import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open Sail
open LeanRV32D.Functions

--- A Reader that only accesses values of type `T`.
structure JTypeReader (T : Type) where
  op_a : T
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : T
  op_b_imm : Word T
  op_c_imm : Word T

namespace JTypeReader

def b {T : Type} (cols : JTypeReader T) : Word T := cols.op_b_imm

def c {T : Type} (cols : JTypeReader T) : Word T := cols.op_c_imm

def read_jal_b_fun
  (cols : JTypeReader U16)
  (imm : BitVec 21)
  /- : Prop := (· + sign_extend imm) <$> (readReg Register.PC) = pure cols.b.toBV32_U16 -/
  : Prop := (do
    let pc ← readReg Register.PC
    pure (pc + sign_extend imm)
  ) = pure cols.b.toBV32_U16

def read_jal_c_fun
  (cols : JTypeReader U16)
  : Prop := (BitVec.addInt · 4) <$> (readReg Register.PC) = pure cols.c.toBV32_U16

end JTypeReader
