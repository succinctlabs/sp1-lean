import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.JTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.UTypeChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The U-type chip row (`LUI` / `AUIPC`) as a `GeneralFormalCircuit`

Witnesses the addend (`is_auipc · pc`, 0 for LUI) and the add result; composes `CPUState` (straight-line
`next_pc = pc + 4`), `AddOperation` (gate `is_real - op_a_0`), and `JTypeReader` (opcode
`is_auipc·48 + (1-is_auipc)·49`). The addend is pinned per-limb by `addend[i] = is_auipc * pc[i]`.
Implements SP1's `UType` `air.rs:eval`. -/

namespace SP1Clean.UTypeChip

open Circuit
open Extracted (UTypeColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Witness the addend (3 limbs = `is_auipc * pc`) and add result (4 limbs), then compose `CPUState`,
`AddOperation` (gate `is_real - op_a_0`), and `JTypeReader`. Pin the addend per-limb with
`addend[i] = is_auipc * pc[i]` gates. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var UTypeColumns (ZMod p)) := do
  let addend ← witnessVector 3 (fun env =>
    #v[env input.is_auipc * env input.state.pc[0],
       env input.is_auipc * env input.state.pc[1],
       env input.is_auipc * env input.state.pc[2]])
  let add_value ← witnessVector 4 (fun env =>
    AddOperation.populate
      #v[env input.is_auipc * env input.state.pc[0],
         env input.is_auipc * env input.state.pc[1],
         env input.is_auipc * env input.state.pc[2], 0]
      #v[env input.adapter.op_b_imm[0], env input.adapter.op_b_imm[1],
         env input.adapter.op_b_imm[2], env input.adapter.op_b_imm[3]])
  let addendV : Word (Expression (ZMod p)) := #v[addend[0], addend[1], addend[2], 0]
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  assertion AddOperation.circuit
    ⟨addendV, input.adapter.op_b_imm, { value := add_value }, input.is_real - input.adapter.op_a_0⟩
  -- `JTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.JTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     input.is_auipc * 48 + (1 - input.is_auipc) * 49,
     add_value[0], add_value[1], add_value[2], add_value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `AddOperation`, so `isU64 add_value` (the LUI/AUIPC result / zeroing-gate range-check) discharges its
  -- requirement. The write access clock is the recombined low clock `+ 4` (matching the reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, add_value, input.is_real⟩
  addend[0] - input.is_auipc * input.state.pc[0] === 0
  addend[1] - input.is_auipc * input.state.pc[1] === 0
  addend[2] - input.is_auipc * input.state.pc[2] === 0
  input.is_auipc * (input.is_auipc - 1) === 0
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, addend, ⟨add_value⟩, input.is_auipc, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs UTypeColumns main where
  channelsLawful := by simp [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit,
    Readers.JTypeReader.circuit, Readers.RegisterWrite.circuit]
  -- 3 addend limbs + 4 add-result limbs; readers/operation are assertions (localLength 0).
  localLength _ := 7
  -- `programChannel` joins the byte guarantee propagated up from `JTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `JTypeReader`'s op_a memory read **pull** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.UTypeChip
