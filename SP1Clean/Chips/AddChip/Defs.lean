import SP1Clean.Specs.Chip
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.RTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.AddChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Add chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Composes **all three** column blocks as Clean `subcircuit`s that each return their extracted column
struct — `Readers.CPUState.circuit`, `AddOperation.circuit`, `Readers.RTypeReader.circuit` — gates the
row with the `is_real` selector, and **returns the extracted chip column struct** `Extracted.AddCols`
assembled directly from those subcircuit outputs (no `witnessVector`/`fromElements` plumbing). So the
chip's column layout is the single source of truth shared with SP1's extraction.

Layout: `add_operation` is the witnessed add gadget's output, `state` is the `Readers.CPUState` output
(its two clock byte-range checks, `is_real`-gated), `adapter` is the `Readers.RTypeReader` output (its
timestamp byte checks `is_real`-gated + the unconditional `op_a_0` zeroing gates), and `is_real` is the
input selector (threaded into both readers). The chip `Spec` is the **composition of the sub-circuits'
own `Spec`s** + the *proven* `is_real`-binary fact + the `is_real`-gated add identity (mirrors
sp1-lean's `SP1Chips` `allHold_constraints_iff`). The buses' *cross-row* meaning (PC chain, memory
permutation) lives at the trace level in `Soundness/{State,Program,Memory}Consistency.lean`.

Note (deferred): the readers still *witness* their column blocks with fixed padding-safe values, so
completeness fills padding-shaped rows; representing arbitrary real rows (real clocks/timestamps) is the
separate step where those columns get threaded from the trace/Sail layer. The `is_real` gating added
here is what makes that compatible with genuine `is_real = 0` padding.

(`main` + the `ElaboratedCircuit` instance; the `Assumptions`/`Spec`/soundness/completeness/`circuit`
live in the sibling `Formal` module, the Sail bridge in `Bridge`.) -/

namespace SP1Clean.AddChip

open Circuit
open Extracted (AddCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the three column blocks as true Clean `subcircuit`s that each **return their extracted
column struct** — the `Readers.CPUState`/`Readers.RTypeReader` readers and the witnessed `AddOperation`
gadget — then gate `is_real` and assemble the extracted `AddCols` struct directly from the subcircuit
outputs. The `CPUState` reader takes no input (it owns + witnesses its clock block); the `RTypeReader`
reader takes the row selectors (`is_real`, and `is_trusted := is_real` — Add is trusted), the clock
(`clk_high` + the recombined low clock `clk_0_16 + clk_16_24 * 65536`, both from the state block), the
program counter `state.pc` and `opcode := 0` (Add's fixed opcode, for the Program bus), and the four
`op_a_write_value` limbs (the ALU result `add_op.value`). Because every block is a subcircuit output, the
chip needs no `witnessVector`/`fromElements` plumbing and the soundness `Spec` reads `cols.state.*`
straight out of the reader output. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (AddCols) (ZMod p)) := do
  -- The `state`/`adapter` column blocks are now **threaded inputs** (the committed reader columns the chip
  -- reads — real clocks/timestamps/pc, not self-witnessed padding). `main` composes the CPUState and
  -- RTypeReader constraint operations as Clean `assertion`s over `input.state`/`input.adapter`, forming
  -- `next_pc = [pc[0] + 4, pc[1], pc[2]]` from the input `pc` and passing `clk_inc = 8` — exactly
  -- `add.rs:eval`'s `CPUStateInput::new(local.state, [pc[0]+PC_INC, …], CLK_INC, …)`. Only the `AddOperation`
  -- gadget still witnesses (the ALU result `add_op.value` is genuinely existentially determined).
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- The chip now **witnesses the ALU result itself** via the operation's `populate`, then composes the
  -- demoted `AddOperation` gadget as a Clean `assertion` over the whole `⟨a, b, value, is_real⟩` column
  -- struct (SP1's `AddOperation::eval`). This mirrors SP1's chip = row-populate (calls the operation
  -- populates) + eval (calls the operation evals); `WitnessTests/AddOperationWitness.lean` anchors `populate`
  -- to SP1's real `populate`.
  let value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  assertion AddOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  assertion Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 0,
     value[0], value[1], value[2], value[3]⟩
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs AddCols main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit]
  -- The chip witnesses only the 4 result limbs now (via `populate`); `AddOperation` is a `FormalAssertion`
  -- whose limb range checks are byte-bus pulls (no witnessed bits), and `CPUState`/`RTypeReader` are
  -- `assertion`s over the threaded `input.state`/`input.adapter` blocks (`localLength 0` each). The binary
  -- gate adds no witnesses.
  localLength _ := 4
  -- Propagated from the subcircuits' `channelsWith*`. `byteChannel` (gated receives) is in BOTH lists; State
  -- (gated emit, `toRawGated`), Memory and Program (plain gated `emit`s) are requirements-only.
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.AddChip
