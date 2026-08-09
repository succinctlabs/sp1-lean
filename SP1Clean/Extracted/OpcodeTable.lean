import SP1Clean.Extracted.Provenance

/-! # AUTO-GENERATED SP1 `Opcode` discriminant table — do not edit by hand.

Parsed by `update_extracted.py` out of `crates/core/executor/src/opcode.rs` at the pinned
semantic revision (`checkedInProvenance.semanticRevision`, read via `git show`): the
variant name → `#[repr(u8)]` discriminant table, i.e. the opcode value each chip commits
on the Program bus. The hand-maintained mirror (`SP1Clean/Model/Opcode.lean`) is
cross-checked against this table by `opcodeTable_matchesExtracted`
(`SP1Clean/FormalModel/OpcodeTable.lean`). -/

set_option linter.all false  -- auto-generated: skip linters

namespace SP1Clean.Extracted

/-- One SP1 `Opcode` enum row: variant name and `#[repr(u8)]` discriminant. -/
structure OpcodeRow where
  name : String
  discriminant : Nat
deriving DecidableEq, Repr

/-- The exact `Opcode` table at `checkedInProvenance.semanticRevision`: 53 variants,
discriminants `0..52` in declaration order. -/
def currentOpcodeTable : List OpcodeRow := [
  ⟨"ADD", 0⟩,
  ⟨"ADDI", 1⟩,
  ⟨"SUB", 2⟩,
  ⟨"XOR", 3⟩,
  ⟨"OR", 4⟩,
  ⟨"AND", 5⟩,
  ⟨"SLL", 6⟩,
  ⟨"SRL", 7⟩,
  ⟨"SRA", 8⟩,
  ⟨"SLT", 9⟩,
  ⟨"SLTU", 10⟩,
  ⟨"MUL", 11⟩,
  ⟨"MULH", 12⟩,
  ⟨"MULHU", 13⟩,
  ⟨"MULHSU", 14⟩,
  ⟨"DIV", 15⟩,
  ⟨"DIVU", 16⟩,
  ⟨"REM", 17⟩,
  ⟨"REMU", 18⟩,
  ⟨"ADDW", 19⟩,
  ⟨"SUBW", 20⟩,
  ⟨"SLLW", 21⟩,
  ⟨"SRLW", 22⟩,
  ⟨"SRAW", 23⟩,
  ⟨"MULW", 24⟩,
  ⟨"DIVW", 25⟩,
  ⟨"DIVUW", 26⟩,
  ⟨"REMW", 27⟩,
  ⟨"REMUW", 28⟩,
  ⟨"LB", 29⟩,
  ⟨"LH", 30⟩,
  ⟨"LW", 31⟩,
  ⟨"LBU", 32⟩,
  ⟨"LHU", 33⟩,
  ⟨"LWU", 34⟩,
  ⟨"LD", 35⟩,
  ⟨"SB", 36⟩,
  ⟨"SH", 37⟩,
  ⟨"SW", 38⟩,
  ⟨"SD", 39⟩,
  ⟨"BEQ", 40⟩,
  ⟨"BNE", 41⟩,
  ⟨"BLT", 42⟩,
  ⟨"BGE", 43⟩,
  ⟨"BLTU", 44⟩,
  ⟨"BGEU", 45⟩,
  ⟨"JAL", 46⟩,
  ⟨"JALR", 47⟩,
  ⟨"AUIPC", 48⟩,
  ⟨"LUI", 49⟩,
  ⟨"ECALL", 50⟩,
  ⟨"EBREAK", 51⟩,
  ⟨"UNIMP", 52⟩,
]

end SP1Clean.Extracted
