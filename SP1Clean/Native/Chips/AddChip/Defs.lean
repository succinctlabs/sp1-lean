import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The Add chip row as a `GeneralFormalCircuit`

Composes the three column blocks as Clean `subcircuit`s — `Readers.CPUState.circuit`,
`AddOperation.circuit`, `Readers.RTypeReader.circuit` — gates the row by the `is_real` selector, and
returns the native `Columns` struct assembled from their outputs.  Its relationship to SP1's extracted
row is stated once by the chip-level reconfiguration in `Faithful/AddChip.lean`. The `Spec` composes the
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
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Composes the `CPUState` and `RTypeReader` readers and the witnessed `AddOperation` gadget, gates
`is_real`, and assembles the native `Columns` struct from their outputs. `RTypeReader` reads Add's
fixed `opcode := 0`, `is_trusted := is_real`, the low clock recombined from the state block, and the
ALU result `add_op.value` as `op_a_write_value`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  -- `CPUState` is a `GeneralFormalCircuit`, composed via the GFC `CoeFun` while discarding its `unit`
  -- output. Its State pull is structural; reachability is proved only by the global grounding engine.
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
  -- Add's Rust AIR only routes rows whose decoded destination is not x0.  This chip-owned assertion
  -- used to appear only in the extracted oracle and in the prover assumptions; keeping it in `main`
  -- makes the native verifier enforce the same routing fact.
  input.adapter.op_a_0 === 0
  -- The `is_real` boolean gate is kept **inline** (`assertZero`, not `=== 0` which composes the deep
  -- Equality subcircuit) so it is visible to `ConstraintsHold.Shallow` — required for the chip to be a
  -- `VmTables` table (`tables_channel`'s `enabled` booleanity reads the shallow constraints). W11.
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, ⟨value⟩⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.is_real, input.state, input.adapter,
      ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩
  channelsLawful := by
    simp only [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit,
      Readers.RTypeReader.circuit, Readers.RegisterWrite.circuit]
  localLength _ := 4
  -- `programChannel` joins the structural `RowSpec` propagated from `RTypeReader`'s program **pull**;
  -- `memoryChannel` joins from `RTypeReader`'s memory read **pulls** (W11 memory flip); `stateChannel`
  -- joins from `CPUState`'s structural State **pull**. The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The explicit row returned by the elaborated circuit, exposed for chip-boundary proofs without
unfolding the full composed `main`. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
         ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of Add's independent native input row.  This is a performance
boundary: consumers rewrite this lemma instead of asking unification to unfold the derived
`ProvableStruct` evaluator through the nested reader blocks. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Component-wise evaluation of Add's independent native output row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ is_real := Eval.eval env cols.is_real, state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         add_operation := Eval.eval env cols.add_operation } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_inputState {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).state = Eval.eval env input.state := by
  rw [eval_inputs]

@[circuit_norm] theorem eval_inputAdapter {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [eval_inputs]

end SP1Clean.AddChip
