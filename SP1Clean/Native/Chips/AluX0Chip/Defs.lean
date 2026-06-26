import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReaderImmutable
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.Extracted.AluX0Chip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `AluX0` chip row as a `GeneralFormalCircuit`

Fast path for ALU instructions writing to `x0` (result discarded). Validates program/register accesses
and advances state only; a single dynamic `opcode` column (range-checked `< 29`) covers every ALU opcode.
Composes `CPUState` and `ALUTypeReaderImmutable` (op_a reads writing 0 to `x0`, op_c gated by
`is_real - imm_c`), plus the LTU byte-range send and `op_a_0 = is_real` forcing gates. -/

namespace SP1Clean.AluX0Chip

open Circuit
open Extracted (AluX0Cols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The threaded reader column blocks + the committed `opcode`/`is_real`. `state`/`adapter` are the
committed CPUState / ALU-type-adapter columns; `opcode` is the dynamic ALU opcode (range-checked `< 29`),
`is_real` the padding gate. Nothing is witnessed — every field is a threaded input. -/
structure Inputs (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
  opcode : F
  is_real : F
deriving ProvableStruct

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The umbrella `is_real` selector (a single column for `AluX0`, vs `LoadX0`'s seven-flag sum). -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_real

/-- The committed ALU opcode fed to the reader's Program bus (a single dynamic column). -/
@[reducible] def opcodeVal (input : Inputs (ZMod p)) : ZMod p := input.opcode

/-- Compose the `CPUState` reader (pc+4 / clk+8), the LTU `opcode < 29` range check, and the
`ALUTypeReaderImmutable` adapter (op_a/op_b/op_c reads, op_c gated by `is_real - imm_c`), then impose the
`is_real` binary gate and the two `op_a_0` forcing gates (`op_a = x0` on real rows). The opcode fed to the
reader is the committed `opcode` column. Assembles the extracted `AluX0Cols`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var AluX0Cols (ZMod p)) := do
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  byteChannel.pullIf input.is_real (⟨4, 1, input.opcode, 29⟩ : ByteRow (Expression (ZMod p)))
  assertion Readers.ALUTypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, input.opcode⟩
  input.is_real * (input.is_real - 1) === 0
  input.is_real * (input.adapter.op_a_0 - 1) === 0
  (input.is_real - 1) * input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, input.opcode, input.is_real⟩

set_option maxHeartbeats 4000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs AluX0Cols main where
  -- Nothing is witnessed: the state/adapter/opcode/is_real are threaded inputs, the readers are
  -- `FormalAssertion`s (localLength 0), and the LTU send + gates witness nothing.
  localLength _ := 0
  localLength_eq := by intro input n; simp only [circuit_norm, main, Readers.CPUState.circuit, Readers.ALUTypeReaderImmutable.circuit]
  output input _ := ⟨input.state, input.adapter, input.opcode, input.is_real⟩
  output_eq := by intro input n; simp only [circuit_norm, main, Readers.CPUState.circuit, Readers.ALUTypeReaderImmutable.circuit]
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, Readers.CPUState.circuit, Readers.ALUTypeReaderImmutable.circuit]

/-- Semantic contract, composed from the sub-circuit `Spec`s. The `ALUTypeReaderImmutable` adapter facts
(op_a/op_b/op_c reads + the `op_a_0` read-zeroing — the discarded write), the `is_real`-binary fact, and the
two `op_a_0` forcing gates (which pin `op_a = x0` on real rows). The CPUState advance is threaded but, like
`LoadX0`, not surfaced in the contract (the Sail bridge derives the `pc + 4` step itself). -/
def Spec (input : Inputs (ZMod p)) (_cols : AluX0Cols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ALUTypeReaderImmutable.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, opcodeVal input⟩ ∧
  (isReal input = 0 ∨ isReal input = 1) ∧
  isReal input * (input.adapter.op_a_0 - 1) = 0 ∧
  (isReal input - 1) * input.adapter.op_a_0 = 0

end SP1Clean.AluX0Chip
