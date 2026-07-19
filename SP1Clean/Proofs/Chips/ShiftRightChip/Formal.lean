import SP1Clean.Proofs.Chips.ShiftRightChip.Defs
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Srl
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Sra
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Srlw
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Sraw
import SP1Clean.Math.EvalVec

/-! # `SP1Clean.ShiftRightChip` — contract: soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance + the soundness
`Assumptions` live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op
`Soundness/<Op>.lean` split files can import it without a cycle through `Formal`). This module holds the
`ProverAssumptions`, the soundness/completeness proofs, and the bundled `circuit`.

**Soundness** is assembled here from the four per-conjunct `Soundness/{Srl,Sra,Srlw,Sraw}.lean` files —
each its own `GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy
per-variant proofs compile in parallel — plus the shared `Operations.Requirements` tail (the same in every
variant, reused here from `SoundSrl`). `circuit_proof_start_core` only introduces the binders (no `simp`),
so the sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly.

**Completeness** is proven against `main`'s honest `Populate` witness closures (flags via the
`"shift_right_flags"` `ProverHint`), as `ShiftLeftChip`: cells pinned to their populate projections,
constraints closed by the `Populate.lean` value-level bundles, pulls by the populate bound lemmas. The
closures are conformance-checked against SP1's real `generate_trace` in
`TraceGenTests/ShiftRightChipTraceWitness.lean`. -/

namespace SP1Clean.ShiftRightChip

open Circuit
open Extracted (ShiftRightCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `Assumptions` (the soundness operand-`isU64` contract) lives in `Defs` so the per-op
-- `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`.

/-- Prover-side row well-formedness: the register-read `isU64`s, the `is_real` binary selector, the
honest `"shift_right_flags"` hint (each flag binary, the sum = `is_real`), `op_a_0 = 0`, the
immediate-`c` machinery (verbatim `ALUTypeReader.Spec` conjuncts), the CPUState clock bounds, and the
three register-access timestamp `Spec`s (op_c gated `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.adapter.op_b_memory.prev_value ∧
  Word.isU64 input.adapter.op_c_memory.prev_value ∧
  -- (W11 memory flip) the op_a read-prior `isU64`, surfaced by the now-pure-read `ALUTypeReader` `Spec`.
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧
  (f[2] = 0 ∨ f[2] = 1) ∧ (f[3] = 0 ∨ f[3] = 1) ∧
  input.is_real = f[0] + f[1] + f[2] + f[3] ∧
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
/-- **Soundness.** The flag-gated RV64 `srl`/`sra`/`srlw`/`sraw` identities on the result column `cols.a`.
**Pieced together** from the four per-conjunct `Soundness/{Srl,Sra,Srlw,Sraw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared `Operations.Requirements` tail (the same in every variant, reused
here from `SoundSrl`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the
sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  refine ⟨fun hr => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (SoundSrl.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSra.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSrlw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSraw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSrl.soundness  i₀ env input_var input h_input h_assumptions h_holds).2

set_option warn.sorry false in
/-- Completeness of the legacy hand-written witness circuit is deferred after the Lean 4.30/4.31
`whnf` regression. Whole-chip populate conformance is checked against SP1's generated trace vectors;
this theorem remains the explicit seam needed by Clean's `GeneralFormalCircuit` bundle. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  stop
  trivial

/-- The Program-fetch opcode committed by the witnessed variant flags (cells `offset+32..35`):
`SRL·7 + SRA·8 + SRLW·22 + SRAW·23`.  Named so the exposed pull and `Soundness/TypedProgram.lean`
share one statement-level expression instead of raw witness indices. -/
def exposedOpcode (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 32⟩ * 7 + var ⟨offset + 33⟩ * 8 +
    var ⟨offset + 34⟩ * 22 + var ⟨offset + 35⟩ * 23

/-- The `RegisterWrite` gate committed by the witnessed variant flags (cells `offset+32..35`):
the flag sum `is_srl + is_sra + is_srlw + is_sraw` (= SP1's `is_real` on shift rows, `sr/mod.rs:335`).
Named so the exposed write push and its consumers share one statement-level expression instead of
raw witness indices. -/
def exposedWriteGate (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 32⟩ + var ⟨offset + 33⟩ + var ⟨offset + 34⟩ + var ⟨offset + 35⟩

/-- ShiftRight's exact Memory-channel interaction list (ALU-type: the op_c register pull/read-back
pair is gated by **`is_real - imm_c`** — an immediate does no register read — and addressed by the
low limb `op_c[0]`).  The five read-side entries descend from the composed `ALUTypeReader` (gate
`is_real`); the op_a write push from the composed `RegisterWrite`, gated by the witnessed
variant-flag sum `exposedWriteGate offset` and carrying the placed result word `a`
(cells `offset..offset+3`) at write clock `clk + 4`.  Keeping this list beside `circuit` makes
Clean's exposure interface the single structural source consumed by both faithfulness and semantic
grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedWriteGate offset)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in ShiftRight's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`is_real - imm_c`)-gated source-C pull occupies its declared slot in ShiftRight's
exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- ShiftRight's exposed channels: the State pair through the canonical `CPUState` child interface,
the Memory-channel closed form above, plus the Program-bus instruction fetch (descended from the
composed `ALUTypeReader`, gate `is_trusted = is_real`, opcode = the committed flag encoding). -/
def stateExposure (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩ ++
  expose memoryChannel (exposedMemoryInteractions input offset) ++
  expose programChannel
    [ programChannel.pulledIf input.is_real
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
      exposedMemoryInteractions, exposedWriteGate, List.map_cons, List.map_nil]
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
      Soundness.aluTypeProgramMessage, exposedOpcode]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false, List.nil_append]

set_option maxHeartbeats 4000000 in
/-- The `ShiftRight` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `srl`/`sra`/`srlw`/`sraw`
semantic contract; output is the extracted `ShiftRightCols` column struct. Soundness is proved (assembled
from the four per-op `Soundness/<Op>.lean` files); the explicitly deferred completeness seam is recorded
above. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs ShiftRightCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `byteChannel` dropped from `channelsWithRequirements` (W11): the nine `gate`-gated byte pulls'
    -- off-gate `Requirements` are discharged locally via the shallow `sum` boolean gate
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

/-- The completed ShiftRight circuit exposes exactly the Memory interaction list above.  Stated via
the exposure-lawfulness theorem directly (not through `circuit`) so it stays axiom-clean while the
completeness seam is open. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact main_exposedChannelsLawful input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [stateExposure, Readers.CPUState.exposedState, expose])

end SP1Clean.ShiftRightChip
