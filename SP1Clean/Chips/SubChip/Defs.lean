import SP1Clean.Specs.Chip
import SP1Clean.Operations.SubOperation.Formal
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.RTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.SubChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Sub chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Composes **all three** column blocks as Clean `subcircuit`s that each return their extracted column
struct — `Readers.CPUState.circuit`, `SubOperation.circuit`, `Readers.RTypeReader.circuit` — gates the
row with the `is_real` selector, and **returns the extracted chip column struct** `Extracted.SubCols`
assembled directly from those subcircuit outputs (no `witnessVector`/`fromElements` plumbing). Direct
mirror of `Chips/AddChip.lean`, so a Sub row emits the same four buses (State, Byte, Memory, Program)
and slots into the heterogeneous trace alongside Add.

Layout: `sub_operation` is the witnessed sub gadget's output, `state` is the `Readers.CPUState` output
(its two clock byte-range checks, `is_real`-gated), `adapter` is the `Readers.RTypeReader` output (its
timestamp byte checks `is_real`-gated + the unconditional `op_a_0` zeroing gates), and `is_real` is the
input selector (threaded into both readers). The chip `Spec` is the **composition of the sub-circuits'
own `Spec`s** + the *proven* `is_real`-binary fact + the `is_real`-gated sub identity. The buses'
*cross-row* meaning (PC chain, memory permutation) lives at the trace level in
`Soundness/{State,Program,Memory}Consistency.lean`.

Unlike Add, SUB is **not commutative**, so the operand order `op_b_val - op_c_val` (= `rX(rs1) - rX(rs2)`)
is load-bearing and must match the Sail bridge's `execute_RTYPE rs2 rs1 rd .SUB`. The Program-bus opcode
is `2` (Sub's fixed opcode, mirroring `Extracted/SubChip.lean`'s CS2 call `RTypeReader.constraints … 2 …`;
Add uses `0`).

Note (deferred): the readers still *witness* their column blocks with fixed padding-safe values, so
completeness fills padding-shaped rows; threading real clocks/timestamps is the separate Sail-layer step.
The `is_real` gating here is what makes that compatible with genuine `is_real = 0` padding. -/

namespace SP1Clean.SubChip

open Circuit
open Extracted (SubCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the three column blocks as true Clean `subcircuit`s that each **return their extracted
column struct** — the `Readers.CPUState`/`Readers.RTypeReader` readers and the witnessed `SubOperation`
gadget — then gate `is_real` and assemble the extracted `SubCols` struct directly from the subcircuit
outputs. The `CPUState` reader takes the `is_real` selector (it owns + witnesses its clock block); the
`RTypeReader` reader takes the row selectors (`is_real`, and `is_trusted := is_real` — Sub is trusted),
the clock (`clk_high` + the recombined low clock `clk_0_16 + clk_16_24 * 65536`, both from the state
block), the program counter `state.pc` and `opcode := 2` (Sub's fixed opcode, for the Program bus), and
the four `op_a_write_value` limbs (the ALU result `sub_op.value`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (SubCols) (ZMod p)) := do
  -- The `state`/`adapter` column blocks are **threaded inputs** (real clocks/timestamps/pc, not padding);
  -- `main` composes the CPUState + RTypeReader constraint operations as `assertion`s over
  -- `input.state`/`input.adapter`, forming `next_pc = [pc[0]+4, pc[1], pc[2]]` from the input `pc` and
  -- passing `clk_inc = 8`. Only the `SubOperation` gadget still witnesses (the ALU result `sub_op.value`).
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- The chip now **witnesses the ALU result itself** via the operation's `populate`, then composes the
  -- demoted `SubOperation` gadget as a Clean `assertion` over the whole `⟨a, b, value, is_real⟩` column
  -- struct (SP1's `SubOperation::eval`). `WitnessTests/SubOperationWitness.lean` anchors `populate` to SP1's.
  let value ← witnessVector 4 (fun env =>
    SubOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  assertion SubOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  assertion Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 2,
     value[0], value[1], value[2], value[3]⟩
  input.is_real * (input.is_real - 1) === 0
  return ⟨input.state, input.adapter, ⟨value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs SubCols main where
  channelsLawful := by simp [circuit_norm, main, Readers.CPUState.circuit, Readers.RTypeReader.circuit, SubOperation.circuit]
  -- The chip witnesses only the 4 result limbs now (via `populate`); `SubOperation` is a `FormalAssertion`
  -- whose limb range checks are byte-bus pulls (no witnessed bits), and `CPUState`/`RTypeReader` are
  -- `assertion`s over the threaded `input.state`/`input.adapter` blocks (`localLength 0` each). The binary
  -- gate adds no witnesses.
  localLength _ := 4
  -- Propagated from the subcircuits' `channelsWith*`. `byteChannel` (gated receives) is in BOTH lists; State
  -- (gated emit, `toRawGated`), Memory and Program (plain gated `emit`s) are requirements-only.
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements :=
    [byteChannel.toRawGated, stateChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.SubChip
