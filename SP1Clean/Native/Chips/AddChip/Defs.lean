import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.AddChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Add chip row as a `GeneralFormalCircuit`

Composes the three column blocks as Clean `subcircuit`s — `Readers.CPUState.circuit`,
`AddOperation.circuit`, `Readers.RTypeReader.circuit` — gates the row by the `is_real` selector, and
returns the extracted `Extracted.AddCols` struct assembled from their outputs, so the chip's column
layout is the single source of truth shared with SP1's extraction. The `Spec` composes the
sub-circuits' own `Spec`s plus the proven `is_real`-binary fact and the `is_real`-gated add identity;
the buses' cross-row meaning (PC chain, memory permutation) lives at the trace level in
`Soundness/{State,Program,Memory}Consistency.lean`.

Deferred: the readers witness their column blocks with padding-safe values, so completeness covers
padding-shaped rows; threading real clocks/timestamps from the trace/Sail layer is a separate step that
the `is_real` gating already makes compatible with `is_real = 0` padding.

(`main` + `ElaboratedCircuit` here; `Assumptions`/`Spec`/soundness/completeness/`circuit` in `Formal`,
the Sail bridge in `Bridge`.) -/

namespace SP1Clean.AddChip

open Circuit
open Extracted (AddCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Composes the `CPUState` and `RTypeReader` readers and the witnessed `AddOperation` gadget, gates
`is_real`, and assembles the extracted `AddCols` struct from their outputs. `RTypeReader` reads Add's
fixed `opcode := 0`, `is_trusted := is_real`, the low clock recombined from the state block, and the
ALU result `add_op.value` as `op_a_write_value`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (AddCols) (ZMod p)) := do
  -- `CPUState` is now a `GeneralFormalCircuit` (SC Phase 2c — the State semantic flip): composed via the
  -- GFC `CoeFun`, discarding its `unit` output. Its State pull now receives `StateTruth`.
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVectorNative 4 (fun env =>
    AddOperation.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  assertion AddOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 0,
     value[0], value[1], value[2], value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `AddOperation`, so `isU64 value` (the ALU result range-check) discharges its requirement — breaking the
  -- old reader-circularity. The write access clock is the recombined low clock `+ 4` (matching the old reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, value, input.is_real⟩
  -- The `is_real` boolean gate is kept **inline** (`assertZero`, not `=== 0` which composes the deep
  -- Equality subcircuit) so it is visible to `ConstraintsHold.Shallow` — required for the chip to be a
  -- `VmTables` table (`tables_channel`'s `enabled` booleanity reads the shallow constraints). W11.
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, ⟨value⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs AddCols main where
  channelsLawful := by
    simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit,
      Readers.RegisterWrite.circuit]
  localLength _ := 4
  -- `programChannel` joins the byte guarantee propagated up from `RTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `RTypeReader`'s memory read **pulls** (W11 memory flip); `stateChannel`
  -- joins from `CPUState`'s State **pull** (SC Phase 2c — it now receives `StateTruth`). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.AddChip
