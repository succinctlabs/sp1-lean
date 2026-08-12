import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.SubwOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Native.WitnessCombinator
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The native SUBW chip row as a `GeneralFormalCircuit`

Composes `Readers.CPUState.circuit`, the witnessed `SubwOperation.circuit`, and
`Readers.RTypeReader.circuit` as Clean subcircuits/assertions, gates `is_real`, and returns the
native `Columns` struct (emitting all four buses). Its relationship to Rust is stated only by the
whole-chip reconfiguration.

W-instruction: result is 2 limbs + sign bit (`subw_operation.value`/`subw_operation.msb.msb`); the
64-bit `op_a` write is the sign-extended word `[v0, v1, msb·65535, msb·65535]`. Adapter is the
`RTypeReader` (unlike ADDW's `ALUTypeReader`); Program-bus opcode `20`. SUBW is **not commutative**:
operand order `op_b_val - op_c_val` must match `execute_RTYPEW rs2 rs1 rd .SUBW`. -/

namespace SP1Clean.SubwChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the three column blocks as Clean subcircuits/assertions and assemble the native `Columns`
struct. The `RTypeReader`'s four `op_a_write_value` limbs are the **sign-extended** W result
`[value[0], value[1], msb·65535, msb·65535]`; the Program-bus opcode is `20`. Only the
`SubwOperation` gadget witnesses; the two readers are `assertion`s over the threaded `state`/`adapter`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- The chip witnesses the result low limbs + sign bit via the operation's witness IR, then composes the
  -- demoted `SubwOperation` gadget as a Clean `assertion`.
  let value ← witnessVectorIR 2 (SubwOperation.valueIR input.op_b_val input.op_c_val)
  let msb ← witnessVectorIR 1 (SubwOperation.msbIR input.op_b_val input.op_c_val)
  assertion SubwOperation.circuit ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb[0]⟩⟩, input.is_real⟩
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
     value[0], value[1], msb[0] * 65535, msb[0] * 65535⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `SubwOperation`, so `isU64` of the sign-extended result word discharges its requirement. The op_a write
  -- value is the W result `[v0, v1, msb·65535, msb·65535]` (= `SubwOperation.resultWord`); clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[value[0], value[1], msb[0] * 65535, msb[0] * 65535], input.is_real⟩
  -- Rust routes SUBW rows only when the decoded destination is not x0.  Keep the extracted AIR's
  -- chip-owned `op_a_0 = 0` assertion in the native verifier as well.
  input.adapter.op_a_0 === 0
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` as a chip-owned constraint (the `VmTables` re-base that motivated
  -- this was investigated and deferred — roadmap W11).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, ⟨value, ⟨msb[0]⟩⟩⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.is_real, input.state, input.adapter,
      ⟨Vector.mapRange 2 fun i => var { index := offset + i },
        ⟨var { index := offset + 2 }⟩⟩⟩
  channelsLawful := by
    simp only [circuit_norm, main, Readers.CPUState.circuit, Readers.RTypeReader.circuit,
      Readers.RegisterWrite.circuit, SubwOperation.circuit]
  -- 2 result limbs + 1 sign bit; readers are `assertion`s (`localLength 0`).
  localLength _ := 3
  -- `programChannel` joins the structural `RowSpec` propagated from `RTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `RTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The explicit row returned by the elaborated circuit.  Consumers rewrite this symbolic boundary
instead of unfolding the complete witnessed SUBW circuit at a concrete environment. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
        ⟨Vector.mapRange 2 fun i => var { index := offset + i },
          ⟨var { index := offset + 2 }⟩⟩⟩ : Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of SUBW's independent input row. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ is_real := Eval.eval env cols.is_real, state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         subw_operation := Eval.eval env cols.subw_operation } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.SubwChip
