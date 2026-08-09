import SP1Clean.Extracted.OpcodeTable
import SP1Clean.Model.Opcode

/-! # Opcode-table cross-check: the hand mirror against the extracted enum

`Model/Opcode.lean` hand-mirrors SP1's `Opcode` enum (`crates/core/executor/src/opcode.rs`) —
variant names, order, and `#[repr(u8)]` discriminants. `Extracted/OpcodeTable.lean` is the same
table parsed mechanically out of the pinned semantic revision by `update_extracted.py`. This module
closes the loop: `opcodeTable_matchesExtracted` compares the mirror with the extracted table by
kernel `decide`, so a drifted variant name, a dropped variant, or a renumbered discriminant in
either artifact fails the build.

`Opcode.name` exists for this check alone. Lean cannot kernel-evaluate a derived `Repr` (its
`Format` rendering does not reduce under `decide`), so the constructor-name strings are stated once
here, adjacent to the theorem, and audited by eye against the constructor list — the name↔
discriminant pairing, count, and ordering are then fully machine-checked. -/

namespace SP1Clean.Soundness.Opcode

/-- Each variant's Rust source name (`Opcode.name .ADD = "ADD"`) — the string `opcode.rs` declares
the variant with. Used only by `CoreProfile.opcodeTable_matchesExtracted`. -/
def name : Opcode → String
  | ADD => "ADD" | ADDI => "ADDI" | SUB => "SUB" | XOR => "XOR" | OR => "OR" | AND => "AND"
  | SLL => "SLL" | SRL => "SRL" | SRA => "SRA" | SLT => "SLT" | SLTU => "SLTU"
  | MUL => "MUL" | MULH => "MULH" | MULHU => "MULHU" | MULHSU => "MULHSU"
  | DIV => "DIV" | DIVU => "DIVU" | REM => "REM" | REMU => "REMU"
  | ADDW => "ADDW" | SUBW => "SUBW" | SLLW => "SLLW" | SRLW => "SRLW" | SRAW => "SRAW"
  | MULW => "MULW" | DIVW => "DIVW" | DIVUW => "DIVUW" | REMW => "REMW" | REMUW => "REMUW"
  | LB => "LB" | LH => "LH" | LW => "LW" | LBU => "LBU" | LHU => "LHU" | LWU => "LWU" | LD => "LD"
  | SB => "SB" | SH => "SH" | SW => "SW" | SD => "SD"
  | BEQ => "BEQ" | BNE => "BNE" | BLT => "BLT" | BGE => "BGE" | BLTU => "BLTU" | BGEU => "BGEU"
  | JAL => "JAL" | JALR => "JALR" | AUIPC => "AUIPC" | LUI => "LUI"
  | ECALL => "ECALL" | EBREAK => "EBREAK" | UNIMP => "UNIMP"

end SP1Clean.Soundness.Opcode

namespace SP1Clean.CoreProfile

open SP1Clean.Soundness

/-- The hand-maintained `Opcode` mirror agrees with the mechanically extracted enum table: the
same variant names paired with the same `#[repr(u8)]` discriminants, in the same order, all
53 rows. -/
theorem opcodeTable_matchesExtracted :
    SP1Clean.Extracted.currentOpcodeTable
      = Opcode.all.map (fun op => ⟨op.name, op.toNat⟩) := by decide

end SP1Clean.CoreProfile
