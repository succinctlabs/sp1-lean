import SP1Clean.Native.Chips.BranchChip.Defs

/-! # Branch chip proof assumptions

The verifier-side operand assumptions and honest-prover witness contract for the exact SP1 Branch
row. These live separately from the circuit proof so `Formal.lean` remains a small packaging and
channel-exposure surface.
-/

namespace SP1Clean.BranchChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands `isU64`; `is_real` and the flag/branch bits are proven from AIR gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64
    (#v[input.adapter.op_a_memory.prev_value[0],
      input.adapter.op_a_memory.prev_value[1],
      input.adapter.op_a_memory.prev_value[2],
      input.adapter.op_a_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64
    (#v[input.adapter.op_b_memory.prev_value[0],
      input.adapter.op_b_memory.prev_value[1],
      input.adapter.op_b_memory.prev_value[2],
      input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64
    (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] :
      Word (ZMod p))

/-- Honest witness-generation assumptions for the exact Rust-shaped Branch row.

The two pure `AddOperation.populate` targets are proof-level witness calculations, not AIR
subcircuits. Their high-limb-zero hypotheses justify the three-limb PC representation used by SP1's
inline carry equations. Complete output ranges are supplied for the three real-row byte pulls.
-/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  let br := hintBranching hint
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (rs1WordInput input) ∧
  Word.isU64 (rs2WordInput input) ∧
  Word.isU64
    (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] :
      Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8,
      is_real := input.is_real } ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 0⟩ ∧
  (branchTargetWord input)[3] = 0 ∧
  (fallThroughWord input)[3] = 0 ∧
  (f[0] = 0 ∨ f[0] = 1) ∧
  (f[1] = 0 ∨ f[1] = 1) ∧
  (f[2] = 0 ∨ f[2] = 1) ∧
  (f[3] = 0 ∨ f[3] = 1) ∧
  (f[4] = 0 ∨ f[4] = 1) ∧
  (f[5] = 0 ∨ f[5] = 1) ∧
  (input.is_real = f[0] + f[1] + f[2] + f[3] + f[4] + f[5]) ∧
  (br = 0 ∨ br = 1) ∧
  (input.is_real = 0 → br = 0) ∧
  (input.is_real = 1 →
    (f[0] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) =
        Word.toBitVec64 (rs2WordInput input))) ∧
    (f[1] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) ≠
        Word.toBitVec64 (rs2WordInput input))) ∧
    (f[2] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt
        (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[3] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt
        (Word.toBitVec64 (rs2WordInput input)) = false)) ∧
    (f[4] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult
        (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[5] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult
        (Word.toBitVec64 (rs2WordInput input)) = false))) ∧
  (input.is_real = 1 →
    ((committedNextPc input br)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
    (committedNextPc input br)[1].val < 2 ^ 16 ∧
    (committedNextPc input br)[2].val < 2 ^ 16)

end SP1Clean.BranchChip
