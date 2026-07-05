import SP1Clean.Math.Word
import SP1Clean.Model.BusMessages
import SP1Clean.Extracted.CPUState
import SP1Clean.Extracted.RTypeReader
import SP1Clean.Extracted.ALUTypeReader
import SP1Clean.Extracted.ITypeReader
import SP1Clean.Extracted.JTypeReader
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Consolidated specs — reader circuits

The `Inputs` structs and semantic `Spec`s for the register-adapter / state readers
(`CPUState`, `RTypeReader`, `RegisterAccessCols`, `RegisterAccessTimestamp`). First file in the
`Specs/` sequence (`Reader → Operation → Chip`); depends only on `Foundations/` + `Extracted/`.
Each declaration keeps its original namespace, so the reader proof files resolve them unchanged
after `import SP1Clean.FormalModel.Contracts.Readers`. -/

namespace SP1Clean.Readers.RegisterAccessTimestamp
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs: the **chip-owned** timestamp column block `cols`, the row selector `is_real`,
and the operand's access clock `clk_target` (`clk_low + 4/3/2`). As a `FormalAssertion` the block is an
*input* (the composing chip witnesses it), so the two byte checks are over `cols.*`. -/
structure Inputs (F : Type) where
  cols : Extracted.RegisterAccessTimestamp F
  is_real : F
  clk_target : F
deriving ProvableStruct

/-- Semantic contract: the two timestamp byte bounds, **`is_real`-gated** — the 16-bit `Range` on
`diff_low_limb` and the `U8Range` (`< 256`) on the scaled high part. Soundness *derives* them from the
byte-bus pull `Guarantees`; completeness *consumes* them. Mirrors `CPUState.Spec`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    input.cols.diff_low_limb.val < 2 ^ 16 ∧
      ((input.clk_target - input.cols.prev_low - 1 - input.cols.diff_low_limb)
        * (65536 : ZMod p)⁻¹).val < 2 ^ 8

end SP1Clean.Readers.RegisterAccessTimestamp

namespace SP1Clean.Readers.RegisterAccessCols

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs: the **chip-owned** register-access block `cols` (a `prev_value : Word` plus the
nested `access_timestamp`), the row selector `is_real`, and the operand's access clock `clk_target`. -/
structure Inputs (F : Type) where
  cols : Extracted.RegisterAccessCols F
  is_real : F
  clk_target : F
deriving ProvableStruct

/-- Semantic contract: just the composed timestamp sub-assertion's two byte bounds (over
`cols.access_timestamp`). SP1's register-access read imposes no local well-formedness on `prev_value`
(`crates/core/machine/src/air/memory.rs`): the operand's `isU64` is *received* from the writer via the
offline-memory balance, not established here. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  RegisterAccessTimestamp.Spec
    { cols := input.cols.access_timestamp, is_real := input.is_real, clk_target := input.clk_target }
end SP1Clean.Readers.RegisterAccessCols

namespace SP1Clean.Readers.RTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs. Field order is fixed (the composing chip builds this positionally):
`is_real` (row selector), `is_trusted` (the instruction-fetch gate, `= is_real` on the Add chip),
`clk_high`/`clk_low` (the clock limbs, for the Memory bus), `pc` (the 3-limb program counter) and
`opcode` (both for the Program bus), and the four `op_a_write_value` limbs `wv*` (the ALU result, for the
`op_a_0` zeroing gates + the `op_a` write interaction). Everything else (the register indices,
prev-values, and access timestamps) is **witnessed** (the scalars) or **sub-circuit output** (the
register-access blocks). -/
structure Inputs (F : Type) where
  cols : Extracted.RTypeReader F
  is_real : F
  is_trusted : F
  clk_high : F
  clk_low : F
  pc : fields 3 F
  opcode : F
  wv0 : F
  wv1 : F
  wv2 : F
  wv3 : F
deriving ProvableStruct

/-- Semantic contract: the four `op_a_0` zeroing gates
(`op_a_0 * wv_i = 0`, the `rd = x0 ⇒ write 0` rule) and the `op_a_0` binary fact — genuine local
`assertZero` constraints, derived in soundness from the imposed gates — plus, per operand, the composed
`RegisterAccessCols` byte bounds (`is_real`-gated, access clocks `clk_low + 4/3/2`), derived from the byte
bus. The register **index** bounds stay non-local (received facts; trace level). The **operand `isU64`**
(W11 memory flip) is now *derived* here, on real rows, from the three memory **read-prior pulls**' guarantees
(`MemoryMsg.isU64`): the consuming chip reads `op_b`/`op_c`'s `isU64` straight out of this `Spec` instead of
assuming it; the `op_a` (old `rd`) one round-trips the pull/push discharge in completeness. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.op_a_0 * input.wv0 = 0 ∧ input.cols.op_a_0 * input.wv1 = 0 ∧
      input.cols.op_a_0 * input.wv2 = 0 ∧ input.cols.op_a_0 * input.wv3 = 0) ∧
    (input.cols.op_a_0 = 0 ∨ input.cols.op_a_0 = 1) ∧
    RegisterAccessCols.Spec ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_c_memory, input.is_real, input.clk_low + 2⟩ ∧
    -- (W11 flip) the decode bounds **derived** from the program bus's `ProgramMsg.RowSpec` pull guarantee
    -- (destination index `< 32`, pc limbs `< 2^16`, on real `is_trusted` rows) — no longer trace-level.
    (input.is_trusted = 1 → input.cols.op_a.val < 32 ∧
      input.pc[0].val < 2 ^ 16 ∧ input.pc[1].val < 2 ^ 16 ∧ input.pc[2].val < 2 ^ 16) ∧
    -- (W11 memory flip) operand `isU64` derived from the three memory read-prior pulls (real rows).
    (input.is_real = 1 → Word.isU64 input.cols.op_a_memory.prev_value ∧
      Word.isU64 input.cols.op_b_memory.prev_value ∧ Word.isU64 input.cols.op_c_memory.prev_value)

end SP1Clean.Readers.RTypeReader

namespace SP1Clean.Readers.ALUTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs for the *ALU-type* register adapter (op_c may be an **immediate**). Same shape
as `RTypeReader.Inputs` but `cols : Extracted.ALUTypeReader` (whose `op_c` is a `Word` and which carries
the `imm_c` flag). Field order is fixed (the composing chip builds it positionally). -/
structure Inputs (F : Type) where
  cols : Extracted.ALUTypeReader F
  is_real : F
  is_trusted : F
  clk_high : F
  clk_low : F
  pc : fields 3 F
  opcode : F
  wv0 : F
  wv1 : F
  wv2 : F
  wv3 : F
deriving ProvableStruct

/-- Semantic contract for the ALU-type adapter. The `RTypeReader` content (the four `op_a_0` zeroing
gates, the `op_a_0` binary fact, and the op_a/op_b timestamp byte bounds, `is_real`-gated) **plus** the
immediate machinery: `imm_c` is boolean off padding (`(is_real - 1) * imm_c = 0`), the op_c access
multiplicity `is_real - imm_c` is boolean, when `imm_c = 1` the op_c "read" is pinned to the immediate
(`imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0`), and the op_c timestamp byte bounds are gated by
`is_real - imm_c` (no register read for an immediate). Mirrors `Faithful/ALUTypeReader.lean`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.op_a_0 * input.wv0 = 0 ∧ input.cols.op_a_0 * input.wv1 = 0 ∧
      input.cols.op_a_0 * input.wv2 = 0 ∧ input.cols.op_a_0 * input.wv3 = 0) ∧
    (input.cols.op_a_0 = 0 ∨ input.cols.op_a_0 = 1) ∧
    (input.is_real - 1) * input.cols.imm_c = 0 ∧
    (input.is_real - input.cols.imm_c = 0 ∨ input.is_real - input.cols.imm_c = 1) ∧
    (input.cols.imm_c * (input.cols.op_c_memory.prev_value[0] - input.cols.op_c[0]) = 0 ∧
      input.cols.imm_c * (input.cols.op_c_memory.prev_value[1] - input.cols.op_c[1]) = 0 ∧
      input.cols.imm_c * (input.cols.op_c_memory.prev_value[2] - input.cols.op_c[2]) = 0 ∧
      input.cols.imm_c * (input.cols.op_c_memory.prev_value[3] - input.cols.op_c[3]) = 0) ∧
    RegisterAccessCols.Spec ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_c_memory, input.is_real - input.cols.imm_c, input.clk_low + 2⟩ ∧
    -- (W11 flip) decode bounds derived from the program-bus `ProgramMsg.RowSpec` pull.
    (input.is_trusted = 1 → input.cols.op_a.val < 32 ∧
      input.pc[0].val < 2 ^ 16 ∧ input.pc[1].val < 2 ^ 16 ∧ input.pc[2].val < 2 ^ 16) ∧
    -- (W11 memory flip) op_a/op_b operand `isU64` derived from the two `is_real`-gated memory read-prior
    -- pulls, and op_c's from the `is_real - imm_c`-gated read-prior pull (no register read for an immediate).
    (input.is_real = 1 → Word.isU64 input.cols.op_a_memory.prev_value ∧
      Word.isU64 input.cols.op_b_memory.prev_value) ∧
    (input.is_real - input.cols.imm_c = 1 → Word.isU64 input.cols.op_c_memory.prev_value)

end SP1Clean.Readers.ALUTypeReader

namespace SP1Clean.Readers.ALUTypeReaderImmutable

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs for the *immutable ALU-type* register adapter — op_a is a source **read**
(written 0 to `x0`, the result discarded), not a destination write, so there is **no** `wv*` write value.
Reuses the `Extracted.ALUTypeReader` column struct (op_c a `Word`, the `imm_c` flag). Mirrors SP1's
`ALUTypeReader::eval_op_a_immutable` (used by `AluX0Chip`). -/
structure Inputs (F : Type) where
  cols : Extracted.ALUTypeReader F
  is_real : F
  is_trusted : F
  clk_high : F
  clk_low : F
  pc : fields 3 F
  opcode : F
deriving ProvableStruct

/-- Semantic contract for the immutable ALU-type adapter. The four `op_a_0` zeroing gates pin the **read**
value of `x0` to `0` (`op_a_0 * op_a_memory.prev_value_i = 0`, vs the mutable reader's `op_a_0 * wv_i = 0`),
the `op_a_0` binary fact, **plus** the immediate machinery (mirrors `ALUTypeReader.Spec`): `imm_c` boolean
off padding, the op_c access multiplicity `is_real - imm_c` boolean, the immediate-consistency gates
(`imm_c * (op_c_memory.prev_value_i - op_c_i) = 0`), and the op_a/op_b/op_c timestamp byte bounds (op_c
gated `is_real - imm_c`). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.op_a_0 * input.cols.op_a_memory.prev_value[0] = 0 ∧
      input.cols.op_a_0 * input.cols.op_a_memory.prev_value[1] = 0 ∧
      input.cols.op_a_0 * input.cols.op_a_memory.prev_value[2] = 0 ∧
      input.cols.op_a_0 * input.cols.op_a_memory.prev_value[3] = 0) ∧
    (input.cols.op_a_0 = 0 ∨ input.cols.op_a_0 = 1) ∧
    (input.is_real - 1) * input.cols.imm_c = 0 ∧
    (input.is_real - input.cols.imm_c = 0 ∨ input.is_real - input.cols.imm_c = 1) ∧
    (input.cols.imm_c * (input.cols.op_c_memory.prev_value[0] - input.cols.op_c[0]) = 0 ∧
      input.cols.imm_c * (input.cols.op_c_memory.prev_value[1] - input.cols.op_c[1]) = 0 ∧
      input.cols.imm_c * (input.cols.op_c_memory.prev_value[2] - input.cols.op_c[2]) = 0 ∧
      input.cols.imm_c * (input.cols.op_c_memory.prev_value[3] - input.cols.op_c[3]) = 0) ∧
    RegisterAccessCols.Spec ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_c_memory, input.is_real - input.cols.imm_c, input.clk_low + 2⟩ ∧
    -- (W11 flip) decode bounds derived from the program-bus `ProgramMsg.RowSpec` pull.
    (input.is_trusted = 1 → input.cols.op_a.val < 32 ∧
      input.pc[0].val < 2 ^ 16 ∧ input.pc[1].val < 2 ^ 16 ∧ input.pc[2].val < 2 ^ 16) ∧
    -- (W11 memory flip) op_a/op_b operand `isU64` derived from the two `is_real`-gated memory read-prior
    -- pulls, and op_c's from the `is_real - imm_c`-gated read-prior pull (no register read for an immediate).
    (input.is_real = 1 → Word.isU64 input.cols.op_a_memory.prev_value ∧
      Word.isU64 input.cols.op_b_memory.prev_value) ∧
    (input.is_real - input.cols.imm_c = 1 → Word.isU64 input.cols.op_c_memory.prev_value)

end SP1Clean.Readers.ALUTypeReaderImmutable

namespace SP1Clean.Readers.ITypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs for the *I-type* register adapter (op_c is an **immediate** `op_c_imm`, not a
register read). Same shape as `RTypeReader.Inputs` but `cols : Extracted.ITypeReader` (which has
`op_a`/`op_b` register reads and `op_c_imm : Word`), and op_a is the destination **write** (`wv*` is the
written value, e.g. the loaded word for a Load). Only two register accesses (op_a write, op_b read).
Field order is fixed (the composing chip builds it positionally). -/
structure Inputs (F : Type) where
  cols : Extracted.ITypeReader F
  is_real : F
  is_trusted : F
  clk_high : F
  clk_low : F
  pc : fields 3 F
  opcode : F
  wv0 : F
  wv1 : F
  wv2 : F
  wv3 : F
deriving ProvableStruct

/-- Semantic contract for the I-type adapter (op_a a destination write). The four `op_a_0` zeroing gates
(`op_a_0 * wv_i = 0`, the `rd = x0 ⇒ write 0` rule), the `op_a_0` binary fact, and the op_a/op_b timestamp
byte bounds (`is_real`-gated, access clocks `clk_low + 4/3`). No op_c register access (it is the immediate).
The register index bounds + value `isU64` stay non-local (received facts; trace level). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.op_a_0 * input.wv0 = 0 ∧ input.cols.op_a_0 * input.wv1 = 0 ∧
      input.cols.op_a_0 * input.wv2 = 0 ∧ input.cols.op_a_0 * input.wv3 = 0) ∧
    (input.cols.op_a_0 = 0 ∨ input.cols.op_a_0 = 1) ∧
    RegisterAccessCols.Spec ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩ ∧
    -- (W11 flip) decode bounds derived from the program-bus `ProgramMsg.RowSpec` pull.
    (input.is_trusted = 1 → input.cols.op_a.val < 32 ∧
      input.pc[0].val < 2 ^ 16 ∧ input.pc[1].val < 2 ^ 16 ∧ input.pc[2].val < 2 ^ 16) ∧
    -- (W11 memory flip) op_a/op_b operand `isU64` derived from the two memory read-prior pulls (real rows).
    (input.is_real = 1 → Word.isU64 input.cols.op_a_memory.prev_value ∧
      Word.isU64 input.cols.op_b_memory.prev_value)

end SP1Clean.Readers.ITypeReader

namespace SP1Clean.Readers.ITypeReaderImmutable

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs for the *immutable I-type* register adapter — op_a is a source **read**
(e.g. rs2 for a Store), not a write, so there is **no** `wv*` write value. Reuses the
`Extracted.ITypeReader` column struct. Two register reads (op_a, op_b); op_c is the immediate. -/
structure Inputs (F : Type) where
  cols : Extracted.ITypeReader F
  is_real : F
  is_trusted : F
  clk_high : F
  clk_low : F
  pc : fields 3 F
  opcode : F
deriving ProvableStruct

/-- Semantic contract for the immutable I-type adapter. The four `op_a_0` zeroing gates pin the **read**
value of `x0` to `0` (`op_a_0 * op_a_memory.prev_value_i = 0`), the `op_a_0` binary fact, and the op_a/op_b
timestamp byte bounds (`is_real`-gated, access clocks `clk_low + 4/3`). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.op_a_0 * input.cols.op_a_memory.prev_value[0] = 0 ∧
      input.cols.op_a_0 * input.cols.op_a_memory.prev_value[1] = 0 ∧
      input.cols.op_a_0 * input.cols.op_a_memory.prev_value[2] = 0 ∧
      input.cols.op_a_0 * input.cols.op_a_memory.prev_value[3] = 0) ∧
    (input.cols.op_a_0 = 0 ∨ input.cols.op_a_0 = 1) ∧
    RegisterAccessCols.Spec ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩ ∧
    RegisterAccessCols.Spec ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩ ∧
    -- (W11 flip) decode bounds derived from the program-bus `ProgramMsg.RowSpec` pull.
    (input.is_trusted = 1 → input.cols.op_a.val < 32 ∧
      input.pc[0].val < 2 ^ 16 ∧ input.pc[1].val < 2 ^ 16 ∧ input.pc[2].val < 2 ^ 16) ∧
    -- (W11 memory flip) op_a/op_b operand `isU64` derived from the two memory read-prior pulls (real rows).
    (input.is_real = 1 → Word.isU64 input.cols.op_a_memory.prev_value ∧
      Word.isU64 input.cols.op_b_memory.prev_value)

end SP1Clean.Readers.ITypeReaderImmutable

namespace SP1Clean.Readers.JTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cross-block inputs for the *J-type* register adapter (used by JAL / AUIPC): a destination write
`op_a` (= rd) plus **two immediates** `op_b_imm`/`op_c_imm` (no second register read). `cols :
Extracted.JTypeReader`. Only **one** register access (op_a write at `clk_low + 4`); `wv*` is the written
value (e.g. the return address `pc + 4`). Field order is fixed (the composing chip builds it positionally). -/
structure Inputs (F : Type) where
  cols : Extracted.JTypeReader F
  is_real : F
  is_trusted : F
  clk_high : F
  clk_low : F
  pc : fields 3 F
  opcode : F
  wv0 : F
  wv1 : F
  wv2 : F
  wv3 : F
deriving ProvableStruct

/-- Semantic contract for the J-type adapter (op_a a destination write, op_b/op_c immediates). The four
`op_a_0` zeroing gates (`op_a_0 * wv_i = 0`, the `rd = x0 ⇒ write 0` rule), the `op_a_0` binary fact, and
the op_a timestamp byte bounds (`is_real`-gated, access clock `clk_low + 4`). No op_b/op_c register access
(both are immediates). The register index bounds + value `isU64` stay non-local (received facts; trace level). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.op_a_0 * input.wv0 = 0 ∧ input.cols.op_a_0 * input.wv1 = 0 ∧
      input.cols.op_a_0 * input.wv2 = 0 ∧ input.cols.op_a_0 * input.wv3 = 0) ∧
    (input.cols.op_a_0 = 0 ∨ input.cols.op_a_0 = 1) ∧
    RegisterAccessCols.Spec ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩ ∧
    -- (W11 flip) decode bounds derived from the program-bus `ProgramMsg.RowSpec` pull.
    (input.is_trusted = 1 → input.cols.op_a.val < 32 ∧
      input.pc[0].val < 2 ^ 16 ∧ input.pc[1].val < 2 ^ 16 ∧ input.pc[2].val < 2 ^ 16) ∧
    -- (W11 memory flip) op_a operand `isU64` derived from the memory read-prior pull (real rows).
    (input.is_real = 1 → Word.isU64 input.cols.op_a_memory.prev_value)

end SP1Clean.Readers.JTypeReader

namespace SP1Clean.Readers.CPUState

variable {p : ℕ} [Fact p.Prime]

/-- The cross-block inputs, **mirroring SP1's `CPUState::eval(cols, next_pc, clk_increment, is_real)`**
(`crates/core/machine/src/adapter/state.rs`): the committed CPUState column block `cols` (clk limbs +
`pc`, owned by the composing chip), the `next_pc` the row transitions to (a full 3-limb expression — for a
straight-line ALU chip the chip passes `[pc[0] + 4, pc[1], pc[2]]`, for a branch a dedicated `next_pc`
column block), the clock increment `clk_inc` (SP1's `CLK_INC = 8`), and the row selector `is_real`.
Faithful to the Rust: `next_pc`/`clk_inc` are genuine inputs (not baked-in literals), and the chip — which
owns `cols` — forms `next_pc` from its own `cols.pc`. -/
structure Inputs (F : Type) where
  cols : Extracted.CPUState F
  next_pc : fields 3 F
  clk_inc : F
  is_real : F
deriving ProvableStruct

/-- Semantic contract: the two clock byte-range bounds, **`is_real`-gated** — exactly the content of
`Faithful/CPUState.lean`'s `cpustate_constraints_faithful` (under `is_real = 1`). Soundness *derives* these
from the byte-bus pull `Guarantees` (`ByteRowSpec`); completeness *consumes* them to discharge the pulls.
The composing chip, which witnesses the `cols` block with a padding-safe clock, establishes them on real
rows. The cross-row PC chain stays at the trace level (`Soundness/StateConsistency.lean`). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    ((input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ input.cols.clk_16_24.val < 2 ^ 8

/-- The State-bus **pull** message a CPUState block emits: the current `(clk, pc)` (clk recombined from
the two byte limbs). Shared by the reader (its `pullIf` receives this message's `StateTruth`) and every
composing chip (whose `ProverAssumptions` must supply that same `StateTruth`) — defined on the contract
surface so both reference the identical message. -/
def stateMsgOf (cols : Extracted.CPUState (ZMod p)) : SP1Clean.Channels.StateMsg (ZMod p) :=
  ⟨cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536, cols.pc[0], cols.pc[1], cols.pc[2]⟩

end SP1Clean.Readers.CPUState
