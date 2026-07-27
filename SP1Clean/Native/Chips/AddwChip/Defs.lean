import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddwOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.AddwChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The ADDW chip row as a `GeneralFormalCircuit`, output = the extracted column struct

Composes `Readers.CPUState.circuit`, the witnessed `AddwOperation.circuit`, and
`Readers.ALUTypeReader.circuit` as Clean subcircuits/assertions, gates `is_real`, and returns the
extracted `AddwCols` struct (emitting all four buses: State, Byte, Memory, Program).

W-instruction: result is 2 limbs + sign bit (`addw_operation.value`/`addw_operation.msb.msb`); the
64-bit `op_a` write is the sign-extended word `[v0, v1, msb·65535, msb·65535]`. Adapter is the
immediate-capable `ALUTypeReader` (unlike SUBW's `RTypeReader`); Program-bus opcode is `19`. -/

namespace SP1Clean.AddwChip

open Circuit
open Extracted (AddwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the `CPUState`/`AddwOperation`/`ALUTypeReader` column blocks as Clean subcircuits/assertions
and assemble the extracted `AddwCols` struct. The chip witnesses the result low limbs + sign bit via the
operation's `populate` (`addwValueWitness`/`addwMsbWitness`), then composes the demoted `AddwOperation`
gadget as a Clean `assertion`. The `ALUTypeReader`'s four `op_a_write_value` limbs are the
**sign-extended** W result `[value[0], value[1], msb·65535, msb·65535]` (mirroring `Extracted/AddwChip.lean`'s
`ALUTypeReader.asserts … 19 #v[…value[0], …value[1], msb·65535, msb·65535] …`); the Program-bus opcode is
`19`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (AddwCols) (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVectorNative 2 (fun env =>
    AddwOperation.addwValueWitness
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]])
  let msb ← witnessVectorNative 1 (fun env =>
    #v[AddwOperation.addwMsbWitness
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]])
  assertion AddwOperation.circuit ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩
  -- `ALUTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 19,
     value[0], value[1], msb[0] * 65535, msb[0] * 65535⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `AddwOperation`, so `isU64 (resultWord)` (the sign-extended W result, range-checked by the operation)
  -- discharges its requirement. The written value is the sign-extended W word
  -- `#v[value[0], value[1], msb·65535, msb·65535]`; the write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[value[0], value[1], msb[0] * 65535, msb[0] * 65535], input.is_real⟩
  -- Rust routes ADDW rows only when the decoded destination is not x0.  Keep the extracted AIR's
  -- chip-owned `op_a_0 = 0` assertion in the native verifier as well.
  input.adapter.op_a_0 === 0
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs AddwCols main where
  output input offset :=
    ⟨input.state, input.adapter,
      ⟨Vector.mapRange 2 fun i => var { index := offset + i },
        ⟨var { index := offset + 2 }⟩⟩,
      input.is_real⟩
  output_eq := by
    intro input offset
    simp only [main, circuit_norm]
  channelsLawful := by
    simp [circuit_norm, main, AddwOperation.circuit, Readers.ALUTypeReader.circuit,
      Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  -- 2 result limbs + 1 sign bit; readers are `assertion`s (`localLength 0`).
  localLength _ := 3
  -- `programChannel` joins the byte guarantee propagated up from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The explicit completed Addw row, kept folded for chip-boundary proofs. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        ⟨Vector.mapRange 2 fun i => var { index := offset + i },
          ⟨var { index := offset + 2 }⟩⟩,
        input.is_real⟩ : Var AddwCols (ZMod p)) := rfl

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : AddwCols (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         addw_operation := Eval.eval env cols.addw_operation,
         is_real := Eval.eval env cols.is_real } : AddwCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_inputAdapter {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [eval_inputs]

end SP1Clean.AddwChip
