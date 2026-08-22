import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Cases
import SP1Clean.Proofs.Chips.DivRemChip.Evidence
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.Driver
import Clean.Air.Circuit

/-! # `SP1Clean.DivRemChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the chip skeleton: `main` + the `ElaboratedCircuit` instance + the soundness `Assumptions`
live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op `Soundness/<Op>.lean`
split files can import it without a cycle through `Formal`). This module holds the `ProverAssumptions`,
the soundness/completeness proofs, and the bundled `circuit`.

**Status.** The public `Spec` is the stable `DivRemContract.RowSpec` plus the R-type reader contract.
Whole-chip conformance is the single explicit `contractSoundness` seam below. The previous monolithic
per-op circuit proofs were retired; their reusable arithmetic was retained in `Math.lean`, `Soundness.lean`,
and `Assembly.lean`, while `Cases.lean` is now the isolated proof-development interface. Completeness
is proved in `Completeness/Driver.lean` (relocated there for proof isolation, not deferred). -/

namespace SP1Clean.DivRemChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

-- `2 ^ 24` (subsuming `2 ^ 17`): the chip composes `MulOperation` — see `Defs`.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Strong, proof-oriented chip contract.  Unlike the public `Spec`, this exposes the arithmetic
evidence that must be extracted from the generated constraints before the lightweight case layer
turns it into ISA semantics. -/
def EvidenceContract (input : Inputs (ZMod p)) (cols : Columns (ZMod p))
    (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := DivRemContract.encodedOpcode cols,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  Cases.RowEvidence input.is_real input.op_b_val input.op_c_val cols.a cols

set_option linter.unusedSectionVars false in
/-- Evaluation commutes with the comparison cluster's projection from the committed chip row. -/
private theorem eval_compareInput_ofCols (env : Environment (ZMod p))
    (cols : Var Columns (ZMod p)) :
    Eval.eval env (DivRemCompare.Inputs.ofCols cols) =
      DivRemCompare.Inputs.ofCols (Eval.eval env cols) := by
  rw [DivRemCompare.eval_inputs, eval_divRemCols_verifier]
  simp only [DivRemCompare.Inputs.ofCols]
  simp only [Readers.RTypeReader.eval_cols, Readers.RTypeReader.eval_registerAccessCols]

/-- The R-type reader projection in the expression layer.  Keeping this constructor folded gives
the parent proof one small evaluator boundary instead of eight independent row-field rewrites. -/
private def readerInputExpr (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) : Var Readers.RTypeReader.Inputs (ZMod p) :=
  { cols := input.adapter, is_real := input.is_real, is_trusted := input.is_real,
    clk_high := input.state.clk_high,
    clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    pc := input.state.pc,
    opcode := cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
      + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
    wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] }

/-- Value-level spelling of `readerInputExpr`. -/
private def readerInputValue (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) :
    Readers.RTypeReader.Inputs (ZMod p) :=
  { cols := input.adapter, is_real := input.is_real, is_trusted := input.is_real,
    clk_high := input.state.clk_high,
    clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    pc := input.state.pc, opcode := DivRemContract.encodedOpcode cols,
    wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] }

set_option linter.unusedSectionVars false in
/-- Verifier evaluation commutes with the folded R-type reader projection. -/
private theorem eval_readerInputExpr (env : Environment (ZMod p))
    (input : Var Inputs (ZMod p)) (cols : Var Columns (ZMod p)) :
    Eval.eval env (readerInputExpr input cols) =
      readerInputValue (Eval.eval env input) (Eval.eval env cols) := by
  simp only [readerInputExpr, readerInputValue, DivRemContract.encodedOpcode]
  provable_struct_simp
  simp only [Expression.eval, true_and]

/-- The destination-write projection in the expression layer. -/
private def writeInputExpr (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) : Var Readers.RegisterWrite.Inputs (ZMod p) :=
  { clk_high := input.state.clk_high,
    clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
    op_a := input.adapter.op_a, value := cols.a, is_real := input.is_real }

/-- Value-level spelling of `writeInputExpr`. -/
private def writeInputValue (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) :
    Readers.RegisterWrite.Inputs (ZMod p) :=
  { clk_high := input.state.clk_high,
    clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
    op_a := input.adapter.op_a, value := cols.a, is_real := input.is_real }

set_option linter.unusedSectionVars false in
/-- Verifier evaluation commutes with the folded destination-write projection. -/
private theorem eval_writeInputExpr (env : Environment (ZMod p))
    (input : Var Inputs (ZMod p)) (cols : Var Columns (ZMod p)) :
    Eval.eval env (writeInputExpr input cols) =
      writeInputValue (Eval.eval env input) (Eval.eval env cols) := by
  simp only [writeInputExpr, writeInputValue]
  provable_struct_simp
  simp only [Expression.eval, true_and]

/-- The five folded semantic implications contributed by `constrainRow`.  This is deliberately
stated over opaque value rows: the parent soundness proof can rewrite its evaluated witness prefix
to one fresh `cols` variable before applying any arithmetic theorem. -/
private def ConstrainRowSpecs (data : ProverData (ZMod p)) (input : Inputs (ZMod p))
    (cols : Columns (ZMod p)) : Prop :=
  let cpuInput : Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let readerInput := readerInputValue input cols
  let compareInput := DivRemCompare.Inputs.ofCols cols
  let writeInput := writeInputValue input cols
  (Readers.CPUState.circuit.Assumptions cpuInput data →
    Readers.CPUState.circuit.Spec cpuInput () data) ∧
  (Readers.RTypeReader.circuit.Assumptions readerInput data →
    Readers.RTypeReader.circuit.Spec readerInput () data) ∧
  (DivRemCompare.circuit.Assumptions compareInput → DivRemCompare.circuit.Spec compareInput) ∧
  (DivRemCore.circuit.Assumptions cols → DivRemCore.circuit.Spec cols) ∧
  (Readers.RegisterWrite.circuit.Assumptions writeInput →
    Readers.RegisterWrite.circuit.Spec writeInput)

/-- Normalize the constraint-only suffix once, while its input and row are still opaque. -/
private theorem constrainRow_specs (env : Environment (ZMod p))
    (input : Var Inputs (ZMod p)) (cols : Var Columns (ZMod p)) (offset : ℕ)
    (h : ConstraintsHold.Soundness env ((constrainRow input cols).operations offset)) :
    ConstrainRowSpecs env.data (Eval.eval env input) (Eval.eval env cols) := by
  simp only [constrainRow, ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset,
    Circuit.pure_def, Circuit.operations, Operations.forAllNoOffset] at h
  obtain ⟨hcpu, hreader, hcompare, hcore, hwrite⟩ := h
  simp only [subcircuitWithAssertion, Operations.forAllNoOffset,
    GeneralFormalCircuit.toSubcircuit_assumptions,
    GeneralFormalCircuit.toSubcircuit_soundness, and_true] at hcpu hreader
  simp only [assertion, Operations.forAllNoOffset, FormalAssertion.toSubcircuit_assumptions,
    FormalAssertion.toSubcircuit_soundness, and_true] at hcompare hcore hwrite
  rw [eval_compareInput_ofCols] at hcompare
  provable_struct_simp
  simp only [ConstrainRowSpecs]
  refine ⟨hcpu, hreader, ?_, hcore, hwrite⟩
  simpa only [DivRemCompare.Inputs.ofCols] using hcompare

/-- The one heavy-duty verification target: SP1's full generated DivRem row yields reader behavior,
selection, and isolated arithmetic evidence, while discharging all channel requirements.

The statement is stronger than the public contract: every semantic result passes through one of the
explicit Euclidean/exceptional-case evidence constructors in `Cases.lean`. -/
theorem evidenceSoundness :
    GeneralFormalCircuit.Soundness (ZMod p) main Assumptions EvidenceContract := by
  circuit_proof_start_core
  change ConstraintsHold.Soundness env
    ((populateRow input_var >>= constrainRow input_var).operations i₀) at h_holds
  simp only [ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset] at h_holds
  obtain ⟨cols, hcols⟩ : ∃ cols : Columns (ZMod p),
      Eval.eval env ((populateRow input_var).output i₀) = cols := ⟨_, rfl⟩
  have hconstrain := constrainRow_specs env input_var ((populateRow input_var).output i₀)
    (i₀ + (populateRow input_var).localLength i₀) h_holds.2
  clear h_holds
  rw [h_input, hcols] at hconstrain
  rw [populateRow_output_eq] at hcols
  have hinputRealEval : Eval.eval env input_var.is_real = input.is_real := by
    have h := congrArg Inputs.is_real h_input; rwa [eval_inputs] at h
  have hinputAdapterEval : Eval.eval env input_var.adapter = input.adapter := by
    have h := congrArg Inputs.adapter h_input; rwa [eval_inputs] at h
  have hinputStateEval : Eval.eval env input_var.state = input.state := by
    have h := congrArg Inputs.state h_input; rwa [eval_inputs] at h
  have hcolsRealEval : Eval.eval env input_var.is_real = cols.is_real := by
    have h := congrArg Columns.is_real hcols
    rwa [eval_divRemCols_verifier, populatedRowAt_isReal_eq] at h
  have hcolsAdapterEval : Eval.eval env input_var.adapter = cols.adapter := by
    have h := congrArg Columns.adapter hcols
    rwa [eval_divRemCols_verifier, populatedRowAt_adapter_eq] at h
  have hcolsStateEval : Eval.eval env input_var.state = cols.state := by
    have h := congrArg Columns.state hcols
    rwa [eval_divRemCols_verifier, populatedRowAt_state_eq] at h
  have hinputReal : cols.is_real = input.is_real := hcolsRealEval.symm.trans hinputRealEval
  have hadapter : cols.adapter = input.adapter := hcolsAdapterEval.symm.trans hinputAdapterEval
  have hstate : cols.state = input.state := hcolsStateEval.symm.trans hinputStateEval
  obtain ⟨hcpu, hreader, hcompare, hcore, hwrite⟩ := hconstrain
  obtain ⟨hbU, hcU⟩ := h_assumptions
  have hcoreSpec := hcore trivial
  have hrealBinary : input.is_real = 0 ∨ input.is_real = 1 := by
    simpa only [hinputReal] using hcoreSpec.2.2.1.1
  have hcpuSpec := hcpu hrealBinary
  have hclk := Readers.ClkDiscipline.of_cpuState_spec hcpuSpec
  have hreaderAssumptions : Readers.RTypeReader.Assumptions (readerInputValue input cols) :=
    ⟨hrealBinary, hrealBinary, hclk⟩
  have hreaderSpec := hreader hreaderAssumptions
  have hrow := rowEvidenceOfSpecs hbU hcU hcoreSpec hcompare hinputReal hadapter
  have hwriteAssumptions : Readers.RegisterWrite.Assumptions (writeInputValue input cols) :=
    ⟨hrealBinary, fun hr => resultIsU64OfCore hcoreSpec (hinputReal.trans hr), hclk.at_four⟩
  have houtput : Eval.eval env (ElaboratedCircuit.output main input_var i₀) = cols := by
    rw [← elaborated.output_eq, main_output_eq_populateRow, populateRow_output_eq]
    exact hcols
  change EvidenceContract input (Eval.eval env (ElaboratedCircuit.output main input_var i₀))
      env.data ∧ Operations.Requirements env ((main input_var).operations i₀)
  rw [houtput]
  refine ⟨⟨?_, hrow⟩, ?_⟩
  · simpa only [hstate, hadapter, DivRemContract.encodedOpcode,
      readerInputValue, Readers.RTypeReader.circuit, Readers.RTypeReader.SpecD] using hreaderSpec
  · change Operations.Requirements env
      ((populateRow input_var >>= constrainRow input_var).operations i₀)
    simp only [Operations.Requirements, Circuit.bind_forAllNoOffset]
    refine ⟨?_, ?_⟩
    · simp only [populateRow, Circuit.bind_forAllNoOffset, witnessVectorIR, Witnessable.witness_provable, witnessIR, Circuit.pure_def, Circuit.operations,
        Operations.forAllNoOffset, and_true]
    · simp only [constrainRow, Circuit.bind_forAllNoOffset, subcircuitWithAssertion,
        assertion, Circuit.pure_def, Circuit.operations, Operations.forAllNoOffset,
        GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
        GeneralFormalCircuit.toSubcircuit_assumptions,
        FormalAssertion.toSubcircuit_channelsWithRequirements,
        FormalAssertion.toSubcircuit_assumptions, and_true]
      refine ⟨Or.inl (Readers.CPUState.channelsWithRequirements_eq (p := p)), ?_,
        Or.inl (DivRemCompare.channelsWithRequirements_eq (p := p)),
        Or.inl (DivRemCore.channelsWithRequirements_eq (p := p)), ?_⟩
      · right
        change Readers.RTypeReader.Assumptions
          (Eval.eval env (readerInputExpr input_var ((populateRow input_var).output i₀)))
        rw [eval_readerInputExpr, h_input, populateRow_output_eq, hcols]
        exact hreaderAssumptions
      · right
        change Readers.RegisterWrite.Assumptions
          (Eval.eval env (writeInputExpr input_var ((populateRow input_var).output i₀)))
        rw [eval_writeInputExpr, h_input, populateRow_output_eq, hcols]
        exact hwriteAssumptions

/-- SP1's generated DivRem row implements the stable public reader/selection/eight-case contract.
The proof after `evidenceSoundness` is intentionally small and independent of circuit elaboration. -/
theorem contractSoundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  intro offset env input_var input hinput hassumptions hconstraints
  obtain ⟨hevidence, hrequirements⟩ :=
    evidenceSoundness offset env input_var input hinput hassumptions hconstraints
  exact ⟨⟨hevidence.1, hevidence.2.sound⟩, hrequirements⟩

/-- Public soundness name used by the `GeneralFormalCircuit` bundle. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec :=
  contractSoundness

omit [Fact (2 ^ 24 < p)] in
/-- The witness-only prefix has no interactions on any channel.  This is the sole structural
normalization of the 217-cell witness program used below; clients rewrite this folded theorem. -/
private theorem populateRow_interactionsWith_eq_nil (channel : RawChannel (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith channel ((populateRow input).operations offset) = [] := by
  simp only [populateRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness_provable, witnessIR, Operations.localLength,
    Operations.interactionsWith_append, Operations.interactionsWith_witness,
    Operations.interactionsWith_nil, List.nil_append]

/-- The constraint suffix's only State traffic is the canonical `CPUState` pull/push pair. -/
private theorem constrainRow_interactionsWith_state (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith stateChannel.toRaw ((constrainRow input cols).operations offset) =
      (Readers.CPUState.stateInteractions
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).map ChannelInteraction.toRaw := by
  simp only [constrainRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion, Operations.localLength,
    Operations.interactionsWith_append, Readers.CPUState.interactionsWith_state_subcircuit,
    InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
    InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil, DivRemCompare.circuit,
    DivRemCompare.channelsWithGuarantees_eq, DivRemCore.circuit,
    DivRemCore.channelsWithGuarantees_eq, Readers.RTypeReader.circuit,
    Readers.RTypeReader.channelsWithGuarantees_eq, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.channelsWithGuarantees_eq, FormalCircuitBase.channelsWithGuarantees_def,
    List.mem_cons, List.not_mem_nil, or_false, Channels.stateChannel_eq_byteChannel_false,
    Channels.stateChannel_eq_programChannel_false, Channels.stateChannel_eq_memoryChannel_false,
    not_false_eq_true, Operations.interactionsWith_nil, List.append_nil]

/-- The committed Program fetch denoted by the generated DivRem row.  The opcode is the exact
one-hot encoding constrained by the chip; the remaining fields are the R-type reader payload. -/
def exposedProgramMessage (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Channels.ProgramMsg (Expression (ZMod p)) :=
  let cols := populatedRowAt input offset
  ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
    cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
      + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
    input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
    #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩

/-! ### Per-child interaction projections

`constrainRow` composes five children; on any one channel most of them are silent.  The two helpers
below state that silence once, over a loose channel, so the Program and Memory projections below
each cite them instead of re-deriving four `interactionsWith … = []` facts inline. -/

omit [Fact (2 ^ 24 < p)] in
/-- A composed general subcircuit declaring the channel neither as a guarantee nor as a requirement
contributes no interaction on it. -/
private theorem generalChild_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output) (channel : RawChannel (ZMod p))
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements)
    (input : Var Input (ZMod p)) (n : ℕ) :
    Operations.interactionsWith channel
      [Operation.subcircuit (circuit.toSubcircuit n input)] = [] := by
  simpa only [Operations.interactionsWith_nil] using
    InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil circuit channel input
      ([] : Operations (ZMod p)) h_g h_r

omit [Fact (2 ^ 24 < p)] in
/-- Formal-assertion companion to `generalChild_nil`. -/
private theorem assertionChild_nil {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion (ZMod p) Input) (channel : RawChannel (ZMod p))
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements)
    (input : Var Input (ZMod p)) (n : ℕ) :
    Operations.interactionsWith channel
      [Operation.subcircuit (circuit.toSubcircuit n input)] = [] := by
  simpa only [Operations.interactionsWith_nil] using
    InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil circuit channel input
      ([] : Operations (ZMod p)) h_g h_r

/-- The constraint suffix's only Program traffic is the R-type reader's canonical fetch.  Keeping
this projection next to `main` prevents whole-machine proofs from unfolding the witness program. -/
private theorem constrainRow_interactionsWith_program (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith programChannel.toRaw
        ((constrainRow input cols).operations offset) =
      [(programChannel.pulledIf input.is_real
        (Soundness.rTypeProgramMessage (readerInputExpr input cols))).toRaw] := by
  have cpuNil := generalChild_nil (Readers.CPUState.circuit (p := p)) programChannel.toRaw
    (by
      change programChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
      simp [Channels.programChannel_eq_byteChannel_false,
        Channels.programChannel_eq_stateChannel_false])
    (by change programChannel.toRaw ∉ []; exact List.not_mem_nil)
  have readerExact (readerInput : Var Readers.RTypeReader.Inputs (ZMod p)) (n : ℕ) :
      Operations.interactionsWith programChannel.toRaw
        [Operation.subcircuit (Readers.RTypeReader.circuit.toSubcircuit n readerInput)] =
          [(programChannel.pulledIf readerInput.is_trusted
            (Soundness.rTypeProgramMessage readerInput)).toRaw] := by
    simpa only [Operations.interactionsWith_nil, List.append_nil] using
      Soundness.rTypeReader_programInteractions_subcircuit
        readerInput n ([] : Operations (ZMod p))
  have compareNil := assertionChild_nil (DivRemCompare.circuit (p := p)) programChannel.toRaw
    (by change programChannel.toRaw ∉ [byteChannel.toRaw]
        simp [Channels.programChannel_eq_byteChannel_false])
    (by change programChannel.toRaw ∉ []; exact List.not_mem_nil)
  have coreNil := assertionChild_nil (DivRemCore.circuit (p := p)) programChannel.toRaw
    (by change programChannel.toRaw ∉ [byteChannel.toRaw]
        simp [Channels.programChannel_eq_byteChannel_false])
    (by change programChannel.toRaw ∉ []; exact List.not_mem_nil)
  have writeNil := assertionChild_nil (Readers.RegisterWrite.circuit (p := p)) programChannel.toRaw
    (by
      simp only [Readers.RegisterWrite.circuit, FormalCircuitBase.channelsWithGuarantees_def,
        Readers.RegisterWrite.channelsWithGuarantees_eq, List.not_mem_nil, not_false_eq_true])
    (by
      change (programChannel (p := p)).toRaw ∉ [(memoryChannel (p := p)).toRaw]
      simp [Channels.programChannel_eq_memoryChannel_false])
  simp only [constrainRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion, Operations.localLength,
    Operations.interactionsWith_append]
  rw [cpuNil, readerExact, compareNil, coreNil, writeNil]
  simp only [Operations.interactionsWith_nil, List.nil_append, List.append_nil, readerInputExpr]

/-- The complete chip's exact Program projection, phrased through the folded witness layout. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith programChannel.toRaw ((main input).operations offset) =
      [(programChannel.pulledIf input.is_real
        (exposedProgramMessage input offset)).toRaw] := by
  simp only [main, Circuit.operations, Circuit.bind_def, Operations.interactionsWith_append,
    populateRow_interactionsWith_eq_nil, constrainRow_interactionsWith_program, List.nil_append,
    populateRow_output_eq, readerInputExpr, Soundness.rTypeProgramMessage, exposedProgramMessage]

/-- DivRem's exact six-entry Memory traffic: the R-type reader's destination prior plus two source
read pairs, followed by the result write at micro-time four.  The list is stated at the chip boundary
so whole-machine proofs never need to normalize the 217-cell witness program. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  let cols := populatedRowAt input offset
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, cols.a⟩ ]

/-- The constraint suffix's Memory traffic is exactly the reader list followed by the destination
write.  Arithmetic and comparison assertions declare no Memory channel. -/
private theorem constrainRow_interactionsWith_memory (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith memoryChannel.toRaw ((constrainRow input cols).operations offset) =
      Soundness.rTypeMemoryInteractions (readerInputExpr input cols) ++
        Soundness.registerWriteMemoryInteractions (writeInputExpr input cols) := by
  have cpuNil := generalChild_nil (Readers.CPUState.circuit (p := p)) memoryChannel.toRaw
    (by
      change memoryChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
      simp [Channels.memoryChannel_eq_byteChannel_false,
        Channels.memoryChannel_eq_stateChannel_false])
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
  have readerExact (readerInput : Var Readers.RTypeReader.Inputs (ZMod p)) (n : ℕ) :
      Operations.interactionsWith memoryChannel.toRaw
        [Operation.subcircuit (Readers.RTypeReader.circuit.toSubcircuit n readerInput)] =
          Soundness.rTypeMemoryInteractions readerInput := by
    simpa only [Operations.interactionsWith_nil, List.append_nil] using
      Soundness.rTypeReader_memoryInteractions_subcircuit readerInput n ([] : Operations (ZMod p))
  have compareNil := assertionChild_nil (DivRemCompare.circuit (p := p)) memoryChannel.toRaw
    (by change memoryChannel.toRaw ∉ [byteChannel.toRaw]
        simp [Channels.memoryChannel_eq_byteChannel_false])
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
  have coreNil := assertionChild_nil (DivRemCore.circuit (p := p)) memoryChannel.toRaw
    (by change memoryChannel.toRaw ∉ [byteChannel.toRaw]
        simp [Channels.memoryChannel_eq_byteChannel_false])
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
  have writeExact (writeInput : Var Readers.RegisterWrite.Inputs (ZMod p)) (n : ℕ) :
      Operations.interactionsWith memoryChannel.toRaw
        [Operation.subcircuit (Readers.RegisterWrite.circuit.toSubcircuit n writeInput)] =
          Soundness.registerWriteMemoryInteractions writeInput := by
    simpa only [Operations.interactionsWith_nil, List.append_nil] using
      Soundness.registerWrite_memoryInteractions_subcircuit writeInput n ([] : Operations (ZMod p))
  simp only [constrainRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion, Operations.localLength,
    Operations.interactionsWith_append]
  rw [cpuNil, readerExact, compareNil, coreNil, writeExact]
  simp only [Operations.interactionsWith_nil, List.nil_append, List.append_nil,
    readerInputExpr, writeInputExpr]

/-- The complete chip's Memory projection, phrased only through the folded witness-layout theorem. -/
private theorem main_interactionsWith_memory (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith memoryChannel.toRaw ((main input).operations offset) =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  simp only [main, Circuit.operations, Circuit.bind_def, Operations.interactionsWith_append,
    populateRow_interactionsWith_eq_nil, constrainRow_interactionsWith_memory, List.nil_append,
    populateRow_output_eq, readerInputExpr, writeInputExpr, Soundness.rTypeMemoryInteractions,
    Soundness.registerWriteMemoryInteractions, exposedMemoryInteractions, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]

/-- DivRem's State exposure is the ordinary CPU-state transition already composed by `main`.
Publishing it is required by whole-machine grounding even though DivRem is itself a top-level AIR
table rather than a child circuit. -/
def stateExposure (input : Var Inputs (ZMod p)) (_offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩

/-- DivRem's complete top-level exposure: the State edge followed by the six Memory interactions. -/
def exposedChannels (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  stateExposure input offset ++ expose memoryChannel (exposedMemoryInteractions input offset)

private theorem main_exposedChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful (exposedChannels input offset) := by
  unfold Operations.ExposedChannelsLawful
  intro exposed exposedMem
  simp only [exposedChannels, List.mem_append] at exposedMem
  rcases exposedMem with stateMem | memoryMem
  · simp only [stateExposure, Readers.CPUState.exposedState, expose, List.mem_singleton]
      at stateMem
    subst exposed
    simp only [main, Circuit.operations, Circuit.bind_def, Operations.interactionsWith_append,
      populateRow_interactionsWith_eq_nil, constrainRow_interactionsWith_state, List.nil_append]
  · simp only [expose, List.mem_singleton] at memoryMem
    subst exposed
    exact main_interactionsWith_memory input offset

omit [Fact (2 ^ 24 < p)] in
/-- The witness-only prefix contains no child circuit and hence declares no child requirements. -/
private theorem populateRow_subcircuitRequirements_eq_nil (input : Var Inputs (ZMod p))
    (offset : ℕ) :
    Operations.subcircuitChannelsWithRequirements ((populateRow input).operations offset) = [] := by
  simp only [populateRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness_provable, witnessIR, Operations.localLength,
    Operations.subcircuitChannelsWithRequirements_append,
    Operations.subcircuitChannelsWithRequirements_witness,
    Operations.subcircuitChannelsWithRequirements_nil, List.nil_append]

/-- Exactly the R-type reader and destination write contribute child Memory requirements. -/
private theorem constrainRow_subcircuitRequirements_eq (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) (offset : ℕ) :
    Operations.subcircuitChannelsWithRequirements ((constrainRow input cols).operations offset) =
      [memoryChannel.toRaw, memoryChannel.toRaw] := by
  simp only [constrainRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion, Operations.localLength,
    Operations.subcircuitChannelsWithRequirements_append,
    Operations.subcircuitChannelsWithRequirements_subcircuit,
    Operations.subcircuitChannelsWithRequirements_nil,
    GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
    FormalAssertion.toSubcircuit_channelsWithRequirements,
    Readers.CPUState.channelsWithRequirements_eq, DivRemCompare.channelsWithRequirements_eq,
    DivRemCore.channelsWithRequirements_eq, Readers.RTypeReader.circuit,
    Readers.RegisterWrite.circuit, List.nil_append, List.append_nil]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- Neither half emits a shallow interaction; all channel traffic belongs to composed children. -/
private theorem populateRow_shallowChannels_eq_nil (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Operations.shallowChannels ((populateRow input).operations offset) = [] := by
  simp only [populateRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness_provable, witnessIR, Operations.localLength,
    Operations.shallowChannels_append, Operations.shallowChannels_witness,
    Operations.shallowChannels_nil, List.nil_append]

private theorem constrainRow_shallowChannels_eq_nil (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) (offset : ℕ) :
    Operations.shallowChannels ((constrainRow input cols).operations offset) = [] := by
  simp only [constrainRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion, Operations.localLength, Operations.shallowChannels_append,
    Operations.shallowChannels_subcircuit, Operations.shallowChannels_nil, List.nil_append]

omit [Fact (2 ^ 24 < p)] in
private theorem populateRow_shallowInteractions_eq_nil (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Operations.shallowInteractions ((populateRow input).operations offset) = [] := by
  simp only [populateRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness_provable, witnessIR, Operations.localLength,
    Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
    Operations.shallowInteractions_nil, List.nil_append]

private theorem constrainRow_shallowInteractions_eq_nil (input : Var Inputs (ZMod p))
    (cols : Var Columns (ZMod p)) (offset : ℕ) :
    Operations.shallowInteractions ((constrainRow input cols).operations offset) = [] := by
  simp only [constrainRow, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion, Operations.localLength,
    Operations.shallowInteractions_append, Operations.shallowInteractions_subcircuit,
    Operations.shallowInteractions_nil, List.nil_append]

/-- The complete requirements metadata law: both genuine requirements are Memory-channel child
requirements, and the top-level chip has no shallow interactions of its own. -/
theorem requirementsChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).RequirementsChannelsLawful
      (ElaboratedCircuit.channelsWithGuarantees main)
      [stateChannel.toRaw, memoryChannel.toRaw] := by
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · simp only [main, Circuit.operations, Circuit.bind_def,
      Operations.subcircuitChannelsWithRequirements_append,
      populateRow_subcircuitRequirements_eq_nil,
      constrainRow_subcircuitRequirements_eq, List.nil_append]
    simp only [List.subset_def, List.mem_cons, List.not_mem_nil, or_false]
    intro channel hChannel
    rcases hChannel with hChannel | hChannel
    · exact Or.inr hChannel
    · exact Or.inr hChannel
  · intro channel hChannel
    simp only [main, Circuit.operations, Circuit.bind_def, Operations.shallowChannels_append,
      populateRow_shallowChannels_eq_nil, constrainRow_shallowChannels_eq_nil,
      List.nil_append] at hChannel
    exact (List.not_mem_nil hChannel).elim
  · intro env _hConstraints
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro interaction hInteraction
    simp only [main, Circuit.operations, Circuit.bind_def, Operations.shallowInteractions_append,
      populateRow_shallowInteractions_eq_nil, constrainRow_shallowInteractions_eq_nil,
      List.nil_append] at hInteraction
    exact (List.not_mem_nil hInteraction).elim

/-- The `DivRem` chip row as a `GeneralFormalCircuit`: the generated `Columns` row checked against
the public reader/selection/eight-case contract. The disclosed whole-chip seams are
`evidenceSoundness`, `completeness`, and the requirements-channel law below. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `byteChannel` dropped from `channelsWithRequirements` (W11): the core's 32 byte pulls are gated
    -- by the shallow `is_real` gate `E355`; the word-gated pulls live in `DivRemCompare`'s
    -- `U16MSBOperation` subcircuits. Their `Requirements` are discharged locally via
    -- `off_gate_vacuous`, so this circuit needs no `byteChannel` entry in
    -- `channelsWithRequirements`; the assembled provider ledger handles the active multiplicities
    -- globally. The gate is already shallow (emitted via `assertZeros (ownAsserts cols)`), so `main`
    -- is unchanged.
    -- (W11 flip) `programChannel` also dropped: `RTypeReader` now **pulls** the program fetch (a
    -- guarantee, not a requirement) with its off-gate `Requirements` discharged inside the reader, so the
    -- chip owes no program requirement and `programChannel` moves to `channelsWithGuarantees` (`Defs`).
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    requirementsChannelsLawful := requirementsChannelsLawful,
    -- The exact State pull/push pair already emitted by the composed CPUState reader.  This public
    -- interface lets the typed whole-machine grounding proof consume DivRem uniformly with the other
    -- 24 supported instruction tables.
    exposedChannels := exposedChannels,
    exposedChannels_eq := main_exposedChannelsLawful }

/-- Folded circuit projections used by the whole-chip row codec. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 217 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 217 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed DivRem circuit exposes exactly its six-entry Memory list. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw :=
  main_interactionsWith_memory input offset

/-- The completed DivRem circuit's State projection is exactly the canonical CPU-state edge.
Published alongside the Program and Memory projections so whole-chip faithfulness clients need not
unfold the 217-cell witness program or the five-subcircuit constraint suffix. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (Readers.CPUState.stateInteractions
        ⟨input.state,
          #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).map ChannelInteraction.toRaw := by
  simp only [main, Circuit.operations, Circuit.bind_def, Operations.interactionsWith_append,
    populateRow_interactionsWith_eq_nil, constrainRow_interactionsWith_state, List.nil_append]

end SP1Clean.DivRemChip
