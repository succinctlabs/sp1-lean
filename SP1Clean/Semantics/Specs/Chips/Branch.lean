module

public import SP1Clean.Circuits.Types.BranchChip
public import SP1Clean.FormalModel.Contracts.Readers

/-! # Conditional-branch semantics

The six RV64 branch conditions, their selected next program counter and immutable
reader obligations. Comparison witnesses and circuit proofs stay outside this boundary.
-/

@[expose] public section

namespace SP1Clean.BranchChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The rs1 register value as a 4-limb word — the `op_a` source read's prior value, the `a`/`b` operand of
the compare (`a < b`, with `a ↦ rs1`). -/
def rs1Word (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_a_memory.prev_value[0], cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2], cols.adapter.op_a_memory.prev_value[3]]

/-- The rs2 register value as a 4-limb word — the `op_b` source read's prior value. -/
def rs2Word (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand both of the chip's `AddOperation`s add to (`pc + imm = taken target`, `pc + 4 = fall-through`). -/
def pcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- The committed `next_pc` (three 16-bit limbs) padded to a 4-limb word. -/
def nextPcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2], 0]

/-- The reconstructed branch opcode `Σ is_b* · k` (BEQ 40 … BGEU 45), fed to the program-bus read. -/
def branchOpcode (cols : Columns (ZMod p)) : ZMod p :=
  cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 + cols.is_bge * 43
    + cols.is_bltu * 44 + cols.is_bgeu * 45

/-- The six opcode flags and the `is_branching` decision are all binary. -/
def flagsBinary (cols : Columns (ZMod p)) : Prop :=
  (cols.is_beq = 0 ∨ cols.is_beq = 1) ∧ (cols.is_bne = 0 ∨ cols.is_bne = 1) ∧
  (cols.is_blt = 0 ∨ cols.is_blt = 1) ∧ (cols.is_bge = 0 ∨ cols.is_bge = 1) ∧
  (cols.is_bltu = 0 ∨ cols.is_bltu = 1) ∧ (cols.is_bgeu = 0 ∨ cols.is_bgeu = 1) ∧
  (cols.is_branching = 0 ∨ cols.is_branching = 1)

/-- The active branch-opcode selector is exactly one-hot.  This is semantic row information:
the six physical flag gates and `is_real = Σ flags` establish it in the chip soundness proof, and
the Sail bridge consumes it to select the unique B-type instruction. -/
def flagsOneHot (cols : Columns (ZMod p)) : Prop :=
  (cols.is_beq = 1 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧ cols.is_bge = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bne = 1 ∧ cols.is_beq = 0 ∧ cols.is_blt = 0 ∧ cols.is_bge = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_blt = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_bge = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bge = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bltu = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧
      cols.is_bge = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bgeu = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧
      cols.is_bge = 0 ∧ cols.is_bltu = 0)

/-- Immutable reader obligations, binary selectors and RV64 branch semantics.

On active rows the selected comparison determines whether the next PC is the taken
target or the fall-through address. The selected PC is four-byte aligned. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ITypeReaderImmutable.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := branchOpcode cols } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  flagsBinary cols ∧
  (input.is_real = 1 → flagsOneHot cols) ∧
  (input.is_real = 1 → cols.is_branching = 1 →
    Word.toBitVec64 (nextPcWord cols)
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 cols.adapter.op_c_imm) ∧
  (input.is_real = 1 → cols.is_branching = 0 →
    Word.toBitVec64 (nextPcWord cols)
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod p))) ∧
  (input.is_real = 1 →
    (cols.is_beq = 1 →
      (cols.is_branching = 1 ↔ Word.toBitVec64 (rs1Word cols) = Word.toBitVec64 (rs2Word cols))) ∧
    (cols.is_bne = 1 →
      (cols.is_branching = 1 ↔ Word.toBitVec64 (rs1Word cols) ≠ Word.toBitVec64 (rs2Word cols))) ∧
    (cols.is_blt = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).slt (Word.toBitVec64 (rs2Word cols)) = true)) ∧
    (cols.is_bge = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).slt (Word.toBitVec64 (rs2Word cols)) = false)) ∧
    (cols.is_bltu = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).ult (Word.toBitVec64 (rs2Word cols)) = true)) ∧
    (cols.is_bgeu = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).ult (Word.toBitVec64 (rs2Word cols)) = false))) ∧
  (input.is_real = 1 → (cols.next_pc[0]).val % 4 = 0)

end SP1Clean.BranchChip
