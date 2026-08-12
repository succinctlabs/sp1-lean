import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import ToClean.Circuit.WitnessCombinator
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `Addi` chip row as a `GeneralFormalCircuit`

`ADDI`: the `AddOperation` gadget over an I-type adapter (second summand is the immediate `op_c_imm`,
not a register read); reader is `Readers.ITypeReader.circuit` with opcode `1`.
The `is_real`-gated semantic `Spec` (RV64 `add` identity on `cols.add_operation.value`) lives in
`FormalModel/Contracts/Chips.lean`; soundness and completeness are fully proven. -/

namespace SP1Clean.AddiChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Assertion half** — the literal meaning of SP1's `AddiCols.asserts` *own* (inline) assertZero tail
(everything past the composed `AddOperation`/`CPUState`/`ITypeReader` sub-lists), in extracted order
(`Extracted/ChipOracle/Addi.lean`: `E1, op_a_0`): the `is_real` binary gate and the `op_a_0` zeroing flag. -/
def AssertSpec (cols : Columns (ZMod p)) : Prop :=
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — SP1's `AddiCols.interactions` *own* tail is **empty**
(`Extracted/ChipOracle/Addi.lean` ends `… ++ [ ]`): every byte-range pull lives inside the composed
`AddOperation`/`CPUState`/`ITypeReader` sub-lists, anchored there. So the chip's own interaction meaning
is trivial. -/
def InteractSpec (_cols : Columns (ZMod p)) : Prop := True

/-- Compose the `CPUState`/`AddOperation`/`ITypeReader` sub-circuits, witness the ALU result word via
`AddOperation.populateIR` (the exportable witness IR; `populate` remains its value-level anchor), gate `is_real`, and assemble the native `Columns` struct. The `ITypeReader`
carries opcode `1` and the four `op_a_write_value` limbs. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVectorIR 4 (AddOperation.populateIR input.op_b_val input.op_c_val)
  assertion AddOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  -- `ITypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ITypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 1,
     value[0], value[1], value[2], value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `AddOperation`, so `isU64 value` (the ALU result range-check) discharges its requirement — breaking the
  -- old reader-circularity. The write access clock is the recombined low clock `+ 4` (matching the reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, value, input.is_real⟩
  -- Rust routes ADDI rows only when the decoded destination is not x0.  This is the second assertion
  -- in the extracted chip tail and must be verifier-enforced rather than merely prover-supplied.
  input.adapter.op_a_0 === 0
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` as a chip-owned constraint (the `VmTables` re-base that motivated
  -- this was investigated and deferred — roadmap W11).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, ⟨value⟩⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.is_real, input.state, input.adapter,
      ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩
  channelsLawful := by
    simp only [circuit_norm, main, AddOperation.circuit, Readers.CPUState.circuit,
      Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit]
  localLength _ := 4
  -- `programChannel` joins the structural `RowSpec` propagated from `ITypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ITypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The explicit completed row, used by chip-boundary proofs without unfolding the composed `main`. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
        ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of Addi's independent input row. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Component-wise evaluation of Addi's completed output row. -/
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

end SP1Clean.AddiChip
