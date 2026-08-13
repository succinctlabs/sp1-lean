import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.SubOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import ToClean.Circuit.WitnessCombinator
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The native Sub chip row as a `GeneralFormalCircuit`

Composes `Readers.CPUState.circuit`, `SubOperation.circuit`, and `Readers.RTypeReader.circuit` as Clean
subcircuits/assertions, gates `is_real`, and returns the native `Columns` struct (emitting all four
buses). Its relationship to Rust is stated only by the whole-chip reconfiguration. SUB is **not
commutative**: operand order `op_b_val - op_c_val` (= `rX(rs1) - rX(rs2)`) must
match the Sail bridge's `execute_RTYPE rs2 rs1 rd .SUB`. Program-bus opcode `2`. -/

namespace SP1Clean.SubChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the `CPUState`/`SubOperation`/`RTypeReader` sub-circuits, witness the ALU result word via
`SubOperation.populateIR` (the exportable witness IR; `populate` remains its value-level anchor), gate `is_real`, and assemble the native `Columns` struct. `RTypeReader`
carries opcode `2` and the four `op_a_write_value` limbs. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let value ← witnessVectorIR 4 (SubOperation.populateIR input.op_b_val input.op_c_val)
  assertion SubOperation.circuit ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 2,
     value[0], value[1], value[2], value[3]⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `SubOperation`, so `isU64 value` (the ALU result range-check) discharges its requirement — breaking the
  -- old reader-circularity. The write access clock is the recombined low clock `+ 4` (matching the old reader).
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, value, input.is_real⟩
  -- Rust routes Sub rows only when the decoded destination is not x0. Keep that chip-owned fact in
  -- the native verifier rather than in a prover-only assumption.
  input.adapter.op_a_0 === 0
  -- Inline `assertZero` (not `=== 0`, the deep Equality subcircuit) so the `is_real` booleanity is visible
  -- to `ConstraintsHold.Shallow` as a chip-owned constraint (the `VmTables` re-base that motivated
  -- this was investigated and deferred — roadmap W11).
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.is_real, input.state, input.adapter, ⟨value⟩⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output input offset :=
    ⟨input.is_real, input.state, input.adapter,
      ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩
  channelsLawful := by
    simp only [circuit_norm, main, Readers.CPUState.circuit, Readers.RTypeReader.circuit,
      Readers.RegisterWrite.circuit, SubOperation.circuit]
  localLength _ := 4
  -- `programChannel` joins the structural `RowSpec` propagated from `RTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `RTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- The explicit row returned by the elaborated circuit, exposed for chip-boundary proofs without
unfolding the full composed `main`. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
        ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of Sub's independent native input row. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_inputState {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).state = Eval.eval env input.state := by
  rw [eval_inputs]

@[circuit_norm] theorem eval_inputAdapter {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [eval_inputs]

/-! ### Operand words, in `circuit_norm`'s own orientation

The `eval_*` lemmas above push evaluation *down* into components, which is the opposite of
`circuit_norm`'s normal form (it pulls projections *up* out of `eval`), so they are inert under it.
These two state the operand words the other way round — projection outside, right-hand side inert —
which is directly usable by any proof holding struct-level input agreement, chiefly
`ComputableWitnesses`. Vector operands only; a scalar field is already in normal form and restating
one loops. See `AddChip/Defs.lean` for the full rationale. -/

@[circuit_norm] theorem eval_opBVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_b_val
      = Vector.map (Expression.eval env) input.op_b_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_b_val, eval_inputs, Readers.RTypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

@[circuit_norm] theorem eval_opCVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_c_val
      = Vector.map (Expression.eval env) input.op_c_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_c_val, eval_inputs, Readers.RTypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

end SP1Clean.SubChip
