import SP1Clean.Specs.Reader
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Channels
import SP1Clean.Readers.RegisterAccessCols
import SP1Clean.Extracted.ITypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ITypeReader` reader — the I-type register-adapter per-row checks as a Clean `FormalAssertion`

The register adapter for **I-type** instructions (loads and reg-reg-imm ops): a destination write `op_a`
(= rd), a source read `op_b` (= rs1), and an **immediate** `op_c_imm` (no op_c register read). SP1's
`ITypeReader::eval` (`crates/core/machine/src/adapter/register/i_type.rs`, mirrored in
`Extracted/ITypeReader.lean`) emits per row:

- the **program** send (instruction fetch), gated by `is_trusted`, carrying `op_c_imm` with `imm_c = 1`;
- per operand (rd write / rs1 read), two **memory** interactions, gated by `is_real`; and
- per operand, two **byte** timestamp checks, gated by `is_real`.

The genuine per-row constraints are the two `RegisterAccessCols` timestamp checks (composed as
`subcircuit`s) and the `op_a_0` binary + the four `op_a_0 * op_a_write_value_i = 0` zeroing gates
(`rd = x0 ⇒ write 0`). The `.program`/`.memory` interactions' meaning is the trace-level multiset balance. -/

namespace SP1Clean.Readers.ITypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` per operand (op_a write at `clk_low + 4`, op_b read at `clk_low + 3`)
for the timestamp byte checks; impose the `op_a_0` binary + four zeroing gates; emit the Program bus
(`imm_c = 1`, op_c = `op_c_imm`) and the four Memory interactions (op_a write, op_b read). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  -- The Program-bus instruction fetch (SP1's `send (.program …) is_trusted`); the operand-`c` slots carry
  -- the immediate word `op_c_imm` and `imm_c = 1` (vs the R-type `0`). `op_b` is the rs1 register index.
  programChannel.emit input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b, 0, 0, 0,
      cols.op_c_imm[0], cols.op_c_imm[1], cols.op_c_imm[2], cols.op_c_imm[3],
      cols.op_a_0, 0, 1⟩ : ProgramMsg (Expression (ZMod p)))
  cols.op_a_0 * input.wv0 === 0
  cols.op_a_0 * input.wv1 === 0
  cols.op_a_0 * input.wv2 === 0
  cols.op_a_0 * input.wv3 === 0
  -- op_a (rd write): send prior value at prev timestamp, receive the written value `wv*` at `clk_low + 4`.
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 4, cols.op_a, 0, 0,
      input.wv0, input.wv1, input.wv2, input.wv3⟩ : MemoryMsg (Expression (ZMod p)))
  -- op_b (rs1 read): send prior value, receive the (unchanged) prior value at `clk_low + 3`.
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements := [byteChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the `is_real`-gated byte receives (threaded into the two
composed `RegisterAccessCols`). Discharged by the chip's `is_real` binary gate. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, programChannel, ProgramMsg.Spec] at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, hbin, z0, z1, z2, z3⟩ := h_holds
  exact ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin,
      h_rac_a h_assumptions, h_rac_b h_assumptions⟩,
    Or.inr h_assumptions, Or.inr h_assumptions, fun _ _ => bool_of_mul_pred hbin⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hrac_b⟩ := h_spec
  refine ⟨⟨h_assumptions, hrac_a⟩, ⟨h_assumptions, hrac_b⟩, ?_, z0, z1, z2, z3⟩
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The native I-type reader as a Clean `FormalAssertion`: composes a `RegisterAccessCols` per operand
(op_a write, op_b read), imposes the `op_a_0` binary + zeroing gates, and emits the Program/Memory buses. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.ITypeReader
