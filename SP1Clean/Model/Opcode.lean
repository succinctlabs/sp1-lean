import Mathlib.Tactic

/-! # `Opcode` — the RISC-V instruction alphabet (a faithful mirror of SP1's `Opcode`)

A local enum mirroring SP1's `Opcode` (`$SP1_DIR/crates/core/executor/src/opcode.rs`),
variant-for-variant and **with the same `#[repr(u8)]` discriminants** (`Opcode.toNat`). It is the
full instruction alphabet — covered and uncovered alike — over which `Soundness/Coverage.lean`
defines the instruction → chip routing (mirroring `$SP1_DIR/crates/core/executor/src/tracing.rs`).

The discriminant is exactly the value each chip commits on the Program bus
(`Trace.RowView.opcode`, e.g. Add commits `0`, Jal `46`, StoreByte `36`), so `Opcode.toNat` is the
bridge from this enum to the in-circuit opcode column — and, transitively, to the chip's Sail op
(each covered opcode's chip reaches its `spec_<op>` via `ChipKind.advance`). -/

namespace SP1Clean.Soundness

/-- RISC-V opcodes, mirroring SP1's `Opcode` enum order and `#[repr(u8)]` discriminants `0..52`. -/
inductive Opcode where
  | ADD | ADDI | SUB | XOR | OR | AND | SLL | SRL | SRA | SLT | SLTU
  | MUL | MULH | MULHU | MULHSU | DIV | DIVU | REM | REMU
  | ADDW | SUBW | SLLW | SRLW | SRAW | MULW | DIVW | DIVUW | REMW | REMUW
  | LB | LH | LW | LBU | LHU | LWU | LD
  | SB | SH | SW | SD
  | BEQ | BNE | BLT | BGE | BLTU | BGEU
  | JAL | JALR | AUIPC | LUI
  | ECALL | EBREAK | UNIMP
  deriving DecidableEq, Repr, Inhabited

namespace Opcode

/-- The SP1 `#[repr(u8)]` discriminant — the value committed on the Program bus
(`Trace.RowView.opcode`). -/
def toNat : Opcode → ℕ
  | ADD => 0 | ADDI => 1 | SUB => 2 | XOR => 3 | OR => 4 | AND => 5
  | SLL => 6 | SRL => 7 | SRA => 8 | SLT => 9 | SLTU => 10
  | MUL => 11 | MULH => 12 | MULHU => 13 | MULHSU => 14
  | DIV => 15 | DIVU => 16 | REM => 17 | REMU => 18
  | ADDW => 19 | SUBW => 20 | SLLW => 21 | SRLW => 22 | SRAW => 23
  | MULW => 24 | DIVW => 25 | DIVUW => 26 | REMW => 27 | REMUW => 28
  | LB => 29 | LH => 30 | LW => 31 | LBU => 32 | LHU => 33 | LWU => 34 | LD => 35
  | SB => 36 | SH => 37 | SW => 38 | SD => 39
  | BEQ => 40 | BNE => 41 | BLT => 42 | BGE => 43 | BLTU => 44 | BGEU => 45
  | JAL => 46 | JALR => 47 | AUIPC => 48 | LUI => 49
  | ECALL => 50 | EBREAK => 51 | UNIMP => 52

/-- Every opcode in discriminant order — the `EnumIter` analog the coverage ledger audits
against. -/
def all : List Opcode :=
  [ADD, ADDI, SUB, XOR, OR, AND, SLL, SRL, SRA, SLT, SLTU,
   MUL, MULH, MULHU, MULHSU, DIV, DIVU, REM, REMU,
   ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, DIVUW, REMW, REMUW,
   LB, LH, LW, LBU, LHU, LWU, LD,
   SB, SH, SW, SD,
   BEQ, BNE, BLT, BGE, BLTU, BGEU,
   JAL, JALR, AUIPC, LUI,
   ECALL, EBREAK, UNIMP]

/-- Audit guard: the alphabet has all 53 SP1 opcodes. -/
theorem all_length : all.length = 53 := rfl

/-- Audit guard: `all` is in strict discriminant order `0, 1, …, 52` (so it mirrors SP1's
`EnumIter`). -/
theorem all_toNat : all.map toNat = List.range 53 := rfl

end Opcode

end SP1Clean.Soundness
