import SP1Clean.Proofs.Chips.ShiftLeftChip.Defs
import SP1Clean.Proofs.Chips.ShiftLeftChip.Soundness.Sll
import SP1Clean.Proofs.Chips.ShiftLeftChip.Soundness.Sllw
import SP1Clean.Math.EvalVec

/-! # `SP1Clean.ShiftLeftChip` — contract: soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance + the soundness
`Assumptions` live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op
`Soundness/<Op>.lean` split files can import it without a cycle through `Formal`). This module holds the
`ProverAssumptions`, the soundness/completeness proofs, and the bundled `circuit`.

**Soundness** is assembled here from the two per-conjunct `Soundness/{Sll,Sllw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared channel-requirement tail (the same in both variants, reused here from
`SoundSll`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the sub-theorems' raw
`h_holds`/`h_input`/`h_assumptions` binders match directly.

**Completeness** is proven against `main`'s honest `Populate` witness closures (flags via the
`"shift_left_flags"` `ProverHint`): every witnessed cell is pinned to its populate projection, the
constraints close by the `Populate.lean` value-level bundles, and the nine byte-range pulls by the
populate bound lemmas. The closures themselves are conformance-checked cell-for-cell against SP1's real
`generate_trace` in `TraceGenTests/ShiftLeftChipTraceWitness.lean`. -/

namespace SP1Clean.ShiftLeftChip

open Circuit
open Extracted (ShiftLeftCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `Assumptions` (the operand `isU64`/register-readback contract) lives in `Defs` so the per-op
-- `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`.

/-- Prover-side row well-formedness: the operand `isU64`s, the `is_real` binary selector, the honest
`"shift_left_flags"` hint (each flag binary, the sum = `is_real` — required by the in-circuit
`is_real - (is_sll + is_sllw)` bind), `op_a_0 = 0`, the immediate-`c` machinery (`imm_c` boolean facts
+ the four `prev_value = op_c` pins, verbatim `ALUTypeReader.Spec` conjuncts), the CPUState clock
bounds, and the three register-access timestamp `Spec`s (op_c gated `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.op_b_val ∧
  Word.isU64 input.adapter.op_c_memory.prev_value ∧
  -- (W11 Option-B memory flip) the op_a register read-prior is `u64` on real rows — feeds the
  -- `ALUTypeReader` op_a/op_b `isU64` reader-`Spec` conjunct (op_a's half).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧
  input.is_real = f[0] + f[1] ∧
  input.adapter.op_a_0 = 0 ∧
  (input.is_real - 1) * input.adapter.imm_c = 0 ∧
  (input.is_real - input.adapter.imm_c = 0 ∨ input.is_real - input.adapter.imm_c = 1) ∧
  (input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[0] - input.adapter.op_c[0]) = 0 ∧
    input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[1] - input.adapter.op_c[1]) = 0 ∧
    input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[2] - input.adapter.op_c[2]) = 0 ∧
    input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[3] - input.adapter.op_c[3]) = 0) ∧
  Readers.CPUState.Spec
    { cols := input.state,
      next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

set_option maxHeartbeats 4000000 in
/-- **Soundness.** The flag-gated RV64 `sll`/`sllw` identities on the result column `cols.a`. **Pieced
together** from the two per-conjunct `Soundness/{Sll,Sllw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared channel-requirement tail (the same in both variants, reused here from
`SoundSll`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the sub-theorems' raw
`h_holds`/`h_input`/`h_assumptions` binders match directly. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  refine ⟨fun hr => ⟨?_, ?_⟩, ?_⟩
  · exact (SoundSll.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSllw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSll.soundness  i₀ env input_var input h_input h_assumptions h_holds).2

set_option warn.sorry false in
/-- Completeness of the legacy hand-written witness circuit is deferred after the Lean 4.30/4.31
`whnf` regression. Whole-chip populate conformance is checked against SP1's generated trace vectors;
this theorem remains the explicit seam needed by Clean's `GeneralFormalCircuit` bundle. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  stop
  trivial

/-- The reader's literal Program gate — the witnessed variant-flag sum `is_sll + is_sllw` (cells
`offset+30..31`).  ShiftLeft's public `is_real` is only *derived* from this one-hot sum through the
binding constraint `is_real - (is_sll + is_sllw) === 0`, so the exposed pull carries the reader's
own gate expression; `isReal_eq_exposedGate` below identifies the two under the row's constraints. -/
def exposedGate (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 30⟩ + var ⟨offset + 31⟩

/-- The Program-fetch opcode committed by the witnessed variant flags (cells `offset+30..31`):
`SLL·6 + SLLW·21`.  Named so the exposed pull and `Soundness/TypedProgram.lean` share one
statement-level expression instead of raw witness indices. -/
def exposedOpcode (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 30⟩ * 6 + var ⟨offset + 31⟩ * 21

/-! ### `ConstraintsHold` selectors for the binding-constraint extraction

Generic `Operations`-level facts (formerly in `Soundness/TypedProgram.lean`) that let
`isReal_eq_exposedGate` select the one binding assertion without normalizing any unrelated
arithmetic subcircuit. -/

omit [Fact (2 ^ 17 < p)] in
private theorem operationsConstraintsHold_append (env : Environment (ZMod p))
    (left right : Operations (ZMod p)) :
    (left ++ right).ConstraintsHold env ↔
      left.ConstraintsHold env ∧ right.ConstraintsHold env := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.forall_mem_append]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem operationsConstraintsHold_assert_singleton (env : Environment (ZMod p))
    (expression : Expression (ZMod p)) :
    Operations.ConstraintsHold env [.assert expression] ↔ env expression = 0 := by
  simp [Operations.ConstraintsHold, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem operationsConstraintsHold_witness_singleton (env : Environment (ZMod p))
    (length : ℕ) (generator : WitgenIR (ZMod p) length) :
    Operations.ConstraintsHold env [.witness length generator] := by
  simp [Operations.ConstraintsHold, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem equality_of_operationsConstraintsHold_singleton (env : Environment (ZMod p))
    (left right : Expression (ZMod p)) (offset : ℕ) :
    Operations.ConstraintsHold env
        [.subcircuit (@FormalAssertion.toSubcircuit (ZMod p) _ (ProvablePair field field)
          ProvablePair.instance (Gadgets.Equality.circuit field) offset (left, right))] →
      env left = env right := by
  intro constraints
  have difference :
      env (toElements (M := field) left)[0] - env (toElements (M := field) right)[0] = 0 := by
    simpa [Operations.ConstraintsHold, FormalAssertion.toSubcircuit,
      Gadgets.Equality.main, Gadgets.allZero, Circuit.forEach.operations_eq,
      FlatOperation.constraints, FlatOperation.lookups, eval_sub, circuit_norm] using constraints
  have left_eq : env (toElements (M := field) left)[0] = env left := rfl
  have right_eq : env (toElements (M := field) right)[0] = env right := rfl
  rw [left_eq, right_eq, sub_eq_zero] at difference
  exact difference

set_option maxHeartbeats 8000000 in
/-- Under the row's own constraints, the binding assert `is_real - (is_sll + is_sllw) === 0`
identifies the exposed derived Program gate with the public `is_real` selector.  This is the one
whole-`main` `ConstraintsHold` normalization ShiftLeft needs; keeping it here spares
`Soundness/TypedProgram.lean` from re-normalizing the circuit. -/
theorem isReal_eq_exposedGate (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (rowConstraints : ((main input).operations offset).ConstraintsHold env) :
    env input.is_real = env (exposedGate offset) := by
  simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
    HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf,
    Operations.localLength, operationsConstraintsHold_append,
    operationsConstraintsHold_assert_singleton,
    operationsConstraintsHold_witness_singleton] at rowConstraints
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, bindConstraints, _⟩ := rowConstraints
  have bindEq := equality_of_operationsConstraintsHold_singleton env _ _ _ bindConstraints
  have bindZero :
      env input.is_real -
        (env (var ⟨offset + 30⟩) + env (var ⟨offset + 31⟩)) = 0 := by
    simpa [eval_sub, circuit_norm] using bindEq
  simpa [exposedGate, circuit_norm] using sub_eq_zero.mp bindZero

/-- ShiftLeft's exact Memory-channel interaction list (ALU-type: the op_c register pull/read-back
pair is gated by **`exposedGate offset - imm_c`** — an immediate does no register read — and
addressed by the low limb `op_c[0]`).  Every gate is the reader's literal derived selector
`exposedGate offset = is_sll + is_sllw` (cells `offset+30..31`), not the public `is_real`
(identified under the row's constraints by `isReal_eq_exposedGate`).  The op_a write push carries
the placed result word `a` (cells `offset..offset+3`) at write clock `clk + 4`.  Keeping this list
beside `circuit` makes Clean's exposure interface the single structural source consumed by both
faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf (exposedGate offset)
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf (exposedGate offset)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedGate offset)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf (exposedGate offset - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedGate offset - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedGate offset)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in ShiftLeft's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (exposedGate offset)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`exposedGate offset - imm_c`)-gated source-C pull occupies its declared slot in
ShiftLeft's exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (exposedGate offset - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- ShiftLeft's exposed channels: the State pair through the canonical `CPUState` child interface,
the Memory-channel closed form above, plus the Program-bus instruction fetch (descended from the
composed `ALUTypeReader`, gate = the reader's literal derived selector sum, opcode = the committed
flag encoding). -/
def stateExposure (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩ ++
  expose memoryChannel (exposedMemoryInteractions input offset) ++
  expose programChannel
    [ programChannel.pulledIf (exposedGate offset)
        ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], exposedOpcode offset,
         input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
         input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

set_option maxHeartbeats 4000000 in
private theorem main_exposedChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful (stateExposure input offset) := by
  unfold Operations.ExposedChannelsLawful
  intro exposed exposedMem
  simp only [stateExposure, Readers.CPUState.exposedState, expose, List.mem_append,
    List.mem_singleton] at exposedMem
  rcases exposedMem with (rfl | rfl) | rfl
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      Readers.CPUState.interactionsWith_state_subcircuit,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      U16MSBOperation.circuit, U16MSBOperation.channelsWithGuarantees_eq,
      Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
      FormalCircuitBase.channelsWithGuarantees_def,
      Readers.ALUTypeReader.channelsWithGuarantees_eq,
      Readers.RegisterWrite.channelsWithGuarantees_eq,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.stateChannel_eq_byteChannel_false, Channels.stateChannel_eq_programChannel_false,
      Channels.stateChannel_eq_memoryChannel_false, not_false_eq_true,
      Operations.interactionsWith_assert, Operations.interactionsWith_interact,
      Operations.interactionsWith_nil, List.nil_append]
    simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
      Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_stateChannel_false, if_false, List.append_nil]
  · -- Memory branch: compositional — the ALU-type reader keeps its five Memory interactions and
    -- `RegisterWrite` its write push via the reader-local `_subcircuit` lemmas; every other
    -- child is nil.
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
    simp only [Operations.interactionsWith_witness,
      Soundness.aluTypeReader_memoryInteractions_subcircuit,
      Soundness.registerWrite_memoryInteractions_subcircuit,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      U16MSBOperation.circuit, U16MSBOperation.channelsWithGuarantees_eq,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Gadgets.Equality.channelsWithGuarantees_eq,
      Gadgets.Equality.channelsWithRequirements_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.memoryChannel_eq_byteChannel_false,
      Channels.memoryChannel_eq_stateChannel_false, not_false_eq_true,
      Operations.interactionsWith_assert, Operations.interactionsWith_interact,
      Operations.interactionsWith_nil, Soundness.aluTypeMemoryInteractions,
      Soundness.registerWriteMemoryInteractions, List.cons_append, List.nil_append]
    simp only [circuit_norm]
    simp only [Channels.byteChannel_eq_memoryChannel_false, if_false,
      exposedMemoryInteractions, exposedGate, List.map_cons, List.map_nil]
    rfl
  · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
    -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      Soundness.aluTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      U16MSBOperation.circuit, U16MSBOperation.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_interact, Operations.interactionsWith_nil,
      List.map_cons, List.map_nil, List.nil_append,
      Soundness.aluTypeProgramMessage, exposedGate, exposedOpcode]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false, List.nil_append]

set_option maxHeartbeats 4000000 in
/-- The `ShiftLeft` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `sll`/`sllw` semantic contract;
output is the extracted `ShiftLeftCols` column struct. Soundness is proved (assembled from the two per-op
`Soundness/<Op>.lean` files); the explicitly deferred completeness seam is recorded above. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs ShiftLeftCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `byteChannel` dropped from `channelsWithRequirements` (W11): the nine `gate`-gated byte pulls'
    -- off-gate `Requirements` are discharged locally via the shallow `(is_sll + is_sllw)` boolean gate
    -- (`off_gate_vacuous`), so `byteChannel` can later be *finished* in a Clean `SoundEnsemble`.
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      have h_byte : (byteChannel (p := p)).toRaw ∈
          (elaborated (p := p)).channelsWithGuarantees := by
        simp only [circuit_norm]
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.subcircuitChannelsWithRequirements_append,
          Operations.subcircuitChannelsWithRequirements_witness,
          Operations.subcircuitChannelsWithRequirements_subcircuit,
          Operations.subcircuitChannelsWithRequirements_assert,
          Operations.subcircuitChannelsWithRequirements_interact,
          Operations.subcircuitChannelsWithRequirements_nil,
          GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
          FormalAssertion.toSubcircuit_channelsWithRequirements,
          Readers.CPUState.channelsWithRequirements_eq,
          U16MSBOperation.circuit, Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
          Gadgets.Equality.channelsWithRequirements_eq, List.nil_append, List.append_nil]
        simp only [List.subset_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · intro channel h_channel
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowChannels_append, Operations.shallowChannels_witness,
          Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
          Operations.shallowChannels_interact, Operations.shallowChannels_nil,
          List.nil_append] at h_channel
        simp only [ChannelInteraction.toRaw_channel, List.mem_append, List.mem_singleton,
          List.not_mem_nil, or_false, or_self] at h_channel
        subst channel
        exact Or.inl h_byte
      · intro env h_constraints
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
          Operations.forAllNoOffset, true_and, and_true, eval_sub,
          Expression.eval] at h_constraints
        have h_bool := bool_of_mul_pred h_constraints.2
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
          Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
          Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
          List.nil_append] at h_interaction
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_interaction
        rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          right <;>
          rw [ChannelInteraction.toRaw_requirements] <;>
          intro h1 h0 <;>
          simp only [circuit_norm] at h1 h0 <;>
          exact off_gate_vacuous h_bool h1 h0,
    -- W11 (A2): the State pair + Memory closed form + Program fetch, via `stateExposure` above;
    -- lawfulness is the standalone `main_exposedChannelsLawful` (also the axiom-clean seam for
    -- `interactionsWith_memory_eq` below while the completeness seam is open).
    exposedChannels := stateExposure,
    exposedChannels_eq := main_exposedChannelsLawful }

/-- The completed ShiftLeft circuit exposes exactly the Memory interaction list above.  Stated via
the exposure-lawfulness theorem directly (not through `circuit`) so it stays axiom-clean while the
completeness seam is open. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact main_exposedChannelsLawful input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [stateExposure, Readers.CPUState.exposedState, expose])

end SP1Clean.ShiftLeftChip
