import SP1Clean.Specs.Reader
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Channels
import SP1Clean.Readers.RegisterAccessCols
import SP1Clean.Extracted.RTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `RTypeReader` reader — the register-adapter per-row checks as a Clean `FormalCircuit`

The second real reader (sibling of `Readers/CPUState.lean`). SP1's `RTypeReader::eval`
(`crates/core/machine/src/adapter/register/r_type.rs`, mirrored in `Extracted/RTypeReader.lean`) emits
three kinds of bus interaction per ALU row:

- the **program** send (instruction fetch), gated by `is_trusted`;
- per operand (rs1 read / rs2 read / rd write), two **memory** interactions (read prev-state, write
  new-state), gated by `is_real`; and
- per operand, two **byte** timestamp checks, gated by `is_real`.

The `.program`/`.memory` interactions are trivial- or off-chip-membership (their meaning is the
trace-level multiset balance — `Soundness/ProgramConsistency.lean`, `Soundness/MemoryConsistency.lean`),
so this reader emits no Clean lookup for them. The genuine per-row constraints it imposes are:

- per operand, the two timestamp byte checks — **factored into `Readers/RegisterAccessCols.lean`**
  and composed here as three `subcircuit`s (the idiomatic fix for the inline-22-column
  `circuit_proof_start` blow-up: each sub-circuit is a `circuit_norm` black box, à la KeccakRound); and
- the four `op_a_0 * op_a_write_value[i] = 0` gates (the `rd = x0` zeroing rule).

It is a `FormalCircuit` whose **output is the `Extracted.RTypeReader` column struct** (mirroring
`AddOperation`/`CPUState`): the reader witnesses the four scalar columns (`op_a`, `op_a_0`, `op_b`,
`op_c`) and composes a `RegisterAccessCols.circuit` per operand for the six register-access columns,
returning the assembled struct so the chip composes it as a true `subcircuit` and reads the `adapter`
block straight out of the output. The cross-block inputs: `clk_low` (the recombined low clock, from the
CPUState block) and the four `op_a_write_value` limbs (`wv0..wv3`, the ALU result, for the `op_a_0`
zeroing gates). Each operand's `RegisterAccessCols.circuit` receives its access clock
`clk_low + 4/3/2` and witnesses its timestamps from it, which is what makes completeness hold for any
`clk_low`. The `is_real` binary gate stays on the chip. -/

namespace SP1Clean.Readers.RTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files (see `RegisterAccessTimestamp`).
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Witness the four scalar adapter columns (`op_a`, `op_a_0`, `op_b`, `op_c`, all `0`) and compose a
`RegisterAccessCols.circuit` per operand (access clocks `clk_low + 4/3/2`) — emitting columns in the
`Extracted.RTypeReader` field order so the assembled output's offsets line up. Then impose the four
`op_a_0` zeroing gates (unconditional `assertZero`, matching SP1's bare gates). Returns the assembled
`Extracted.RTypeReader` column struct. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  -- The adapter block `cols` is an **input** (the composing chip witnesses it); this reader witnesses
  -- nothing. Compose a `RegisterAccessCols` sub-assertion per operand on the input's nested blocks (access
  -- clocks `clk_low + 4/3/2`) for the timestamp byte checks.
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_c_memory, input.is_real, input.clk_low + 2⟩
  -- No local range checks on the register **indices** `op_a`/`op_b`/`op_c`: SP1's R-type adapter
  -- (`crates/core/machine/src/adapter/register/r_type.rs:100-126`) does not range-check them — the index
  -- bounds (`op_a < 32`, `op_b0`/`op_c0 < 2^16`) come from the instruction *decode* / Program ROM on the
  -- receive side, not a local send. So they are *received* facts (threaded `TraceProgramLink` until the
  -- decode/ProgramChip lands), not part of the send-proven `ProgramMsg.Spec`. The `op_a_0` binary gate stays
  -- — a genuine local `assertZero` (SP1's `op_a_0` flag), and is the one index-side fact the send can prove.
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  -- The Program-bus instruction fetch this row emits (SP1's `send (.program …) is_trusted`,
  -- `Extracted/RTypeReader.lean:84`), gated by the SP1-faithful `is_trusted` multiplicity (= `is_real`
  -- on Add). Arity-16 tuple: pc, opcode, then the operands `op_a`/`op_b`/`op_c` as register indices
  -- (R-type ⇒ the higher word limbs and the `imm_b`/`imm_c` flags are `0`) and the `op_a_0` flag. Matches
  -- the trace-level `programLookups` shadow (`Soundness/ProgramConsistency.lean`).
  programChannel.emit input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b, 0, 0, 0, cols.op_c, 0, 0, 0, cols.op_a_0, 0, 0⟩ :
      ProgramMsg (Expression (ZMod p)))
  cols.op_a_0 * input.wv0 === 0
  cols.op_a_0 * input.wv1 === 0
  cols.op_a_0 * input.wv2 === 0
  cols.op_a_0 * input.wv3 === 0
  -- The six Memory-bus interactions (SP1's per-operand `send` prior-state / `receive` new-state, both gated
  -- by `is_real`): op_a is the `rd` **write** (new value = the ALU result `wv*`), op_b/op_c are the `rs1`/`rs2`
  -- **reads** (value = the read-back `prev_value`). The memory bus is **just the balance** here
  -- (`memoryChannel.Guarantees := True`); the value's `isU64` is *not* a per-row channel fact — operand
  -- well-formedness is a chip-level `Assumptions` precondition discharged from the offline-memory balance
  -- (`docs/bus-model.md` §7). Multiplicity is SP1-faithful `±is_real` (via `emit`), so padding emits `mult 0`.
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 4, cols.op_a, 0, 0,
      input.wv0, input.wv1, input.wv2, input.wv3⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_c_memory.access_timestamp.prev_low, cols.op_c, 0, 0,
      cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 2, cols.op_c, 0, 0,
      cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- `byteChannel` (from the composed `RegisterAccessCols` timestamp checks) gives guarantees + a (padding)
  -- requirement, so it is in BOTH lists. The Memory + Program buses are plain gated `emit`s (requirements-only,
  -- `Guarantees := True` for memory ⇒ trivial; `ProgramMsg.Spec` for program).
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements := [byteChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

-- Expose this reader's own declared channel lists + `localLength` as `@[circuit_norm]` rfl-lemmas so the
-- composing `AddChip`'s `channelsLawful` / `circuit_proof_start` is discharged automatically.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl


/-- `is_real` is binary — the precondition for the genuinely `is_real`-gated byte receives (and threaded
down to the three composed `RegisterAccessCols`). Discharged by the chip's `is_real` binary gate. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- After `simp`: the Memory emits are trivial (`Guarantees := True`), the Program R-type-shape conjuncts are
  -- literal `0`s; what remains is the four zeroing gates + the `op_a_0` binary gate, and the three composed
  -- `RegisterAccessCols` sub-assertions (each `is_real`-binary `Assumptions → Spec`).
  simp only [circuit_norm, memoryChannel, programChannel, ProgramMsg.Spec] at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, z0, z1, z2, z3⟩ := h_holds
  exact ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin,
      h_rac_a h_assumptions, h_rac_b h_assumptions, h_rac_c h_assumptions⟩,
    Or.inr h_assumptions, Or.inr h_assumptions, Or.inr h_assumptions, fun _ => bool_of_mul_pred hbin⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- `Spec` supplies: the four zeroing gates `z*`, the `op_a_0` binary `hbin`, and the three
  -- `RegisterAccessCols` sub-`Spec`s `hrac_*`. Discharge the sub-assertions' ⟨Assumptions, Spec⟩, the binary
  -- gate (from `hbin`), the zeroing gates (`z*`), and the trivial Memory/Program emit obligations.
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hrac_b, hrac_c⟩ := h_spec
  refine ⟨⟨h_assumptions, hrac_a⟩, ⟨h_assumptions, hrac_b⟩, ⟨h_assumptions, hrac_c⟩,
    ?_, z0, z1, z2, z3⟩
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The native RTypeReader reader as a Clean `FormalAssertion`: takes the chip-owned `cols` adapter block,
composes a `RegisterAccessCols` sub-assertion per operand for the timestamp byte checks, imposes the
`op_a_0` binary + zeroing gates, and emits the Program/Memory buses, with a semantic spec. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.RTypeReader
