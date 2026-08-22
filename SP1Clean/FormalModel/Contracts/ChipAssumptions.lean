import SP1Clean.FormalModel.Contracts.Chips

/-! # Chip prover-side contracts — `Assumptions` / `ProverAssumptions` (audit surface)

The soundness-side `Assumptions` and completeness-side `ProverAssumptions` for the chip rows, lifted
here next to their `Spec`s (`Contracts/Chips.lean`) so the full per-chip contract surface lives under
`FormalModel/Contracts/`. `ProverSpec` is uniformly `fun _ _ _ => True` (kept inline in each chip's
`circuit` bundle). Each declaration keeps its original `SP1Clean.<Op>Chip` namespace, so the chip's
proof file resolves it unchanged after `import SP1Clean.FormalModel.Contracts.ChipAssumptions`.

Covers the chips whose contracts reference only the contract layer (operand `isU64`s, reader
`Spec`s, `is_real`, and `Contracts/Chips.lean`-resident decode helpers): the five clean ALU chips
plus UType. The rest keep their `Assumptions`/`ProverAssumptions` in their proof files, for one of
two structural reasons (also recorded in `docs/architecture.md` § deliberate layering exceptions):

- **hint/helper-dependent** — the `ProverAssumptions` references `Defs`-layer witness plumbing
  that does not belong on the contract surface (`hintFlags` for Mul/Bitwise/Lt/Branch and the
  shift/DivRem populate layers; Jal/Jalr's jump helpers). Lifting them would drag `Native`/proof
  internals below the contract layer.
- **Native-resident contract block** — the nine memory chips (the five loads, LoadX0 among
  them, and the four stores) and AluX0 define their `Inputs` (and `Spec`) in
  `Native/Chips/<X>Chip/Defs.lean`, so their `Assumptions` cannot move here without inverting
  the FormalModel → Native layering. They follow when the "Spec homing" backlog item
  (`docs/roadmap.md`) moves those contract blocks onto this surface. -/

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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the
  -- clock half of the memory channel's `Guarantees`). A pull's completeness must exhibit the
  -- guarantee it consumes; in a real trace each prior access sits at a genuine `< 2^24` timestamp.
  -- Soundness does *not* assume these — they are derived there from the pulls themselves.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the two pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`). A pull's completeness must exhibit the guarantee it
  -- consumes; in a real trace each prior access sits at a genuine `< 2^24` timestamp. Soundness does
  -- *not* assume these — they are derived there from the pulls themselves.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24)

end SP1Clean.AddiChip

namespace SP1Clean.AddwChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Only the `op_c` source `isU64` is assumed: `AddwOperation` has an **ungated** `isU64 a ∧ isU64 b`
precondition, and while `op_b`'s `isU64` is derived in soundness from the `ALUTypeReader` `is_real`-gated
memory read-prior pull (usable inside the `is_real = 1` branch where the operation result is needed),
`op_c`'s reader guarantee is gated by `is_real - imm_c`. On an immediate row that gate is off, so the
decoded immediate's `isU64` remains an explicit chip assumption (cf. `AddiChip`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_c_val

/-- Prover-side row well-formedness for both ADDW and ADDIW: operand `isU64`s, the op_a read-prior
`isU64`, `is_real` binary, `op_a_0 = 0`, and the exact ALU-row form invariant
`imm_c = 0 ∨ (is_real = 1 ∧ imm_c = 1)`. The latter admits real immediate rows while forcing padding
to the register-form zero convention. The four gated copy equations are the constructive evidence that
an immediate row's synthetic `op_c_memory.prev_value` is the committed immediate. The remaining clauses
are the CPUState clock bounds and the three timestamp `Spec`s (op_c gated by `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  (input.adapter.imm_c = 0 ∨ (input.is_real = 1 ∧ input.adapter.imm_c = 1)) ∧
  (input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[0] - input.adapter.op_c[0]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[1] - input.adapter.op_c[1]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[2] - input.adapter.op_c[2]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[3] - input.adapter.op_c[3]) = 0) ∧
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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`) — see `AddChip.ProverAssumptions`. The op_c
  -- component is harmlessly stronger than its access gate on immediate rows (the honest builder puts
  -- literal zero there). Soundness does *not* assume these; there they are derived from the pulls.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`) — see `AddChip.ProverAssumptions`. Soundness does *not*
  -- assume these; there they are derived from the pulls themselves.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`) — see `AddChip.ProverAssumptions`. Soundness does *not*
  -- assume these; there they are derived from the pulls themselves.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

end SP1Clean.SubwChip

namespace SP1Clean.UTypeChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands `isU64`; the decode fact `op_b_imm = RV64.lui (immOf adapter)` (the committed immediate
is `sign_extend (imm << 12)`) is a trace/program-ROM guarantee. `is_real`/`is_auipc` booleanity and
the padding convention `is_real = 0 → op_a_0 = 0` are proven from the pinned Rust AIR gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  Word.toBitVec64 input.adapter.op_b_imm = RV64.lui (immOf input.adapter)

/-- Honest prover-side row well-formedness. The immediate + program-counter words `isU64`, `is_real`/
`is_auipc` binary, and the exact destination form
`op_a_0 = 0 ∨ (is_real = 1 ∧ op_a_0 = 1)` (including real `rd = x0` rows while forcing padding's
zero convention), the CPUState clock bounds + op_a register-access timestamp bounds, and the decode
fact. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  -- (Option B pure-read JTypeReader) the op_a read-prior `isU64`, for the reader's op_a memory pull
  -- completeness (its `Spec` now derives + owes the read-prior `isU64`).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_auipc = 0 ∨ input.is_auipc = 1) ∧
  (input.adapter.op_a_0 = 0 ∨ (input.is_real = 1 ∧ input.adapter.op_a_0 = 1)) ∧
  Readers.CPUState.Spec
    { cols := input.state,
      next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Word.toBitVec64 input.adapter.op_b_imm = RV64.lui (immOf input.adapter) ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16 ∧
    input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the pulled prior record's 24-bit access clock (`Channels.MemoryMsg.ClkBound`, the clock half of
  -- the memory channel's `Guarantees`) — the `JTypeReader` op_a read-prior pull's completeness must
  -- exhibit the guarantee it consumes. Soundness *derives* it there from the pull itself.
  (input.is_real = 1 → input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24)

end SP1Clean.UTypeChip
