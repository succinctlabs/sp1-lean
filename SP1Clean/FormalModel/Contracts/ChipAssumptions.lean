import SP1Clean.FormalModel.Contracts.Chips

/-! # Chip prover-side contracts — `Assumptions` / `ProverAssumptions` (audit surface)

The soundness-side `Assumptions` and completeness-side `ProverAssumptions` for the chip rows, lifted
here next to their `Spec`s (`Contracts/Chips.lean`) so the full per-chip contract surface lives under
`FormalModel/Contracts/`. `ProverSpec` is uniformly `fun _ _ _ => True` (kept inline in each chip's
`circuit` bundle). Each declaration keeps its original `SP1Clean.<Op>Chip` namespace, so the chip's
proof file resolves it unchanged after `import SP1Clean.FormalModel.Contracts.ChipAssumptions`.

Covers the clean ALU chips whose contracts reference only the contract layer (operand `isU64`s, reader
`Spec`s, `is_real`). The helper-dependent chips (Jal/Jalr/Branch/DivRem/ShiftLeft/ShiftRight) and the
split-`Spec` chips (Lt/Bitwise) keep their `Assumptions` in their proof files (their preconditions
reference `Defs`-layer / `populate` helpers that do not belong on the contract surface). -/

namespace SP1Clean.AddChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- No soundness-side assumption (Option B memory flip): the operand `isU64`s are now **derived** in
soundness from the `RTypeReader` reader sub-`Spec`'s memory read-prior pull guarantees, not assumed here —
which is what breaks the old reader-circularity. `is_real`-binary is likewise *proved* from the in-circuit
gate; only completeness needs the row well-formedness (see `ProverAssumptions`). -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

/-- Prover-side row well-formedness: operand `isU64`s (the prover still needs them to witness the
operation, and to discharge the `RegisterWrite` op_a write push's `isU64 value`), the op_a read-prior
`isU64` (for the reader's op_a memory pull completeness), `is_real` binary, `op_a_0 = 0`, and the
`is_real`-gated CPUState clock bounds + per-operand register-access timestamp bounds. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

end SP1Clean.AddChip

namespace SP1Clean.AddiChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Only the **immediate** `op_c` is assumed 64-bit (it is decoded, not on the memory bus); the register
source `op_b`'s `isU64` is *derived* in soundness from the `ITypeReader` memory read-prior pull (Option B
memory flip). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_c_val

/-- Prover-side row well-formedness: operand `isU64`s, the op_a read-prior `isU64`, `is_real` binary,
`op_a_0 = 0`, CPUState clock bounds, and the two register-access timestamp bounds (op_a write `clk_low + 4`,
op_b read `clk_low + 3`; no op_c access — it is the immediate). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

end SP1Clean.AddiChip

namespace SP1Clean.AddwChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Only the `op_c` source `isU64` is assumed: `AddwOperation` has an **ungated** `isU64 a ∧ isU64 b`
precondition, and while `op_b`'s `isU64` is derived in soundness from the `ALUTypeReader` `is_real`-gated
memory read-prior pull (usable inside the `is_real = 1` branch where the operation result is needed),
`op_c`'s reader guarantee is gated by `is_real - imm_c` — and `imm_c = 0` is NOT enforced in-circuit for
`Addw` (it is a decode/Program-ROM fact). So `op_c`'s `isU64` cannot be derived locally and is assumed (cf.
`AddiChip`, which assumes its immediate `op_c`'s `isU64`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_c_val

/-- Prover-side row well-formedness: operand `isU64`s, the op_a read-prior `isU64`, `is_real` binary,
`op_a_0 = 0`, `imm_c = 0` (register-register op), CPUState clock bounds, and three timestamp `Spec`s (op_c
gated by `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧ input.adapter.imm_c = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

end SP1Clean.AddwChip

namespace SP1Clean.SubChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- No soundness-side assumption (Option B memory flip): operand `isU64`s are derived in soundness from the
`RTypeReader` memory read-prior pulls, not assumed (mirrors `AddChip`). -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

/-- Prover-side row well-formedness: operand `isU64`s (still needed by the prover for the operation +
`RegisterWrite` op_a write), the op_a read-prior `isU64`, `is_real` binary, `op_a_0 = 0`, and the
`is_real`-gated CPUState clock bounds + per-operand timestamp bounds. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

end SP1Clean.SubChip

namespace SP1Clean.SubwChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- No soundness-side assumption (Option B memory flip): operand `isU64`s are derived in soundness from the
`RTypeReader` memory read-prior pulls, not assumed (mirrors `AddChip`). -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

/-- Prover-side row well-formedness: operand `isU64`s (still needed by the prover for the operation +
`RegisterWrite` op_a write), the op_a read-prior `isU64`, `is_real` binary, `op_a_0 = 0`, and the
`is_real`-gated CPUState clock bounds + per-operand timestamp bounds. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

end SP1Clean.SubwChip
