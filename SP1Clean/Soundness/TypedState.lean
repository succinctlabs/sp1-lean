import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.RankedGrounding
import SP1Clean.Soundness.TypedSelectors
import SP1Clean.Model.Semantics.MicroTime

/-! # Typed State transitions emitted by instruction rows

The State edge of a row is read from the actual Clean interaction pair.  `RowView` remains only the
semantic projection consumed by the existing Sail bridge; the lemmas in this module identify that
projection with the emitted messages.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The State pull payload determined by a chip's shared CPU-state block. -/
def cpuStatePullMessage {R : Type} [Add R] [Mul R] [OfNat R 65536]
    (state : Extracted.CPUState R) : StateMsg R :=
  ⟨state.clk_high, state.clk_0_16 + state.clk_16_24 * 65536,
    state.pc[0], state.pc[1], state.pc[2]⟩

/-- A State push payload with an explicit successor PC and clock increment. -/
def cpuStateNextMessage {R : Type} [Add R] [Mul R] [OfNat R 65536]
    (state : Extracted.CPUState R) (nextPc : Vector R 3) (clkInc : R) : StateMsg R :=
  ⟨state.clk_high, state.clk_0_16 + state.clk_16_24 * 65536 + clkInc,
    nextPc[0], nextPc[1], nextPc[2]⟩

/-- The ordinary `pc + 4`, `clk + 8` specialization used by every non-control-flow core chip. -/
def cpuStatePushMessage {R : Type} [Add R] [Mul R] [OfNat R 65536]
    [OfNat R 8] [OfNat R 4] (state : Extracted.CPUState R) : StateMsg R :=
  ⟨state.clk_high, state.clk_0_16 + state.clk_16_24 * 65536 + 8,
    state.pc[0] + 4, state.pc[1], state.pc[2]⟩

/-- Current-state message denoted by a semantic row view. -/
def statePullOfView (view : Trace.RowView (ZMod p)) : StateMsg (ZMod p) :=
  let access := stateAccess view
  ⟨access.clk_high, access.clk_low, access.pc[0], access.pc[1], access.pc[2]⟩

/-- Successor-state message denoted by a semantic row view. -/
def statePushOfView (view : Trace.RowView (ZMod p)) : StateMsg (ZMod p) :=
  let access := stateAccess view
  ⟨access.clk_high, access.clk_low + access.clk_inc,
    access.next_pc[0], access.next_pc[1], access.next_pc[2]⟩

/-- Current-state message denoted by the existing semantic row view. -/
def statePullMessage (row : ChipRow p) : StateMsg (ZMod p) := statePullOfView row.view

/-- Successor-state message denoted by the existing semantic row view. -/
def statePushMessage (row : ChipRow p) : StateMsg (ZMod p) := statePushOfView row.view

/-- Public initial State message emitted by the boundary verifier. -/
def initialBoundaryStateMessage (publicInput : SP1PublicIO (ZMod p)) : StateMsg (ZMod p) :=
  ⟨publicInput.init_clk_high, publicInput.init_clk_low, publicInput.init_pc0,
    publicInput.init_pc1, publicInput.init_pc2⟩

/-- Public final State message consumed by the boundary verifier. -/
def finalBoundaryStateMessage (publicInput : SP1PublicIO (ZMod p)) : StateMsg (ZMod p) :=
  ⟨publicInput.final_clk_high, publicInput.final_clk_low, publicInput.final_pc0,
    publicInput.final_pc1, publicInput.final_pc2⟩

@[simp] theorem statePullMessage_pcBits (row : ChipRow p) :
    Semantics.StateMsg.pcBits (statePullMessage row) =
      Target.rcvPcOf (stateAccess row.view) := by
  simp only [Semantics.StateMsg.pcBits, Semantics.pcBits, statePullMessage, statePullOfView,
    Target.rcvPcOf, Target.pcBitsOfVals, stateAccess]

@[simp] theorem statePushMessage_pcBits (row : ChipRow p) :
    Semantics.StateMsg.pcBits (statePushMessage row) =
      Target.sndPcOf (stateAccess row.view) := by
  simp [Semantics.StateMsg.pcBits, Semantics.pcBits, statePushMessage, statePushOfView,
    Target.sndPcOf, Target.pcBitsOfVals, stateAccess]

/-- Exact State emissions for a typed circuit and its semantic row view.  This circuit-level form is
the chip-local audit surface: it avoids dependent projections through `SupportedChip`, while the
descriptor-level `StateEmissionShape` below remains the statement consumed by witness decoding. -/
def CircuitStateEmissionShape {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ data physical,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    let rowView := view (component.rowInput env) (component.rowOutput env)
    component.operations.interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledIfValue rowView.is_real (statePullOfView rowView),
       stateChannel.pushedIfValue rowView.is_real (statePushOfView rowView)]

/-- The raw State emission shape expected of one supported instruction row. -/
def StateEmissionShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    let row := chip.decodeRow data physical
    chip.table.operations.interactionValuesWith stateChannel.toRaw
        (Environment.fromArray physical data) =
      [stateChannel.pulledIfValue row.is_real (statePullMessage row),
       stateChannel.pushedIfValue row.is_real (statePushMessage row)]

/-- The small circuit-local interface needed to identify actual Clean State interactions with the
semantic row view.  Keeping `Input`, `Output`, `circuit`, and `view` explicit prevents Lean from
unfolding an entire dependent `SupportedChip` descriptor for each field equation. -/
def CircuitStateExposureContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  ∃ (gate : Var Input (ZMod p) → ℕ → Expression (ZMod p))
      (pullMessage pushMessage :
        Var Input (ZMod p) → ℕ → StateMsg (Expression (ZMod p))),
    (∀ input offset,
      ⟨stateChannel.toRaw,
        [stateChannel.pulledIf (gate input offset) (pullMessage input offset),
         stateChannel.pushedIf (gate input offset) (pushMessage input offset)].map
          ChannelInteraction.toRaw⟩ ∈ circuit.exposedChannels input offset) ∧
    (∀ env : Environment (ZMod p), Eval.eval env (gate inputVar offset) =
      (view (Eval.eval env inputVar)
        (Eval.eval env (circuit.output inputVar offset))).is_real) ∧
    (∀ env : Environment (ZMod p), Eval.eval env (pullMessage inputVar offset) =
      statePullOfView (view (Eval.eval env inputVar)
        (Eval.eval env (circuit.output inputVar offset)))) ∧
    (∀ env : Environment (ZMod p), Eval.eval env (pushMessage inputVar offset) =
      statePushOfView (view (Eval.eval env inputVar)
        (Eval.eval env (circuit.output inputVar offset))))

/-- Transport a circuit-local emission theorem to the corresponding supported-chip descriptor without
unfolding that descriptor.  This matters for large chips: definitional `change` through a dependent
`SupportedChip` can otherwise normalize the entire circuit before discovering the same equality. -/
theorem stateEmissionShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (shape : @CircuitStateEmissionShape p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    StateEmissionShape ⟨kind, circuit, spec_eq, opcodes, rdGuard⟩ := by
  exact shape

omit [Fact (2 ^ 24 < p)] in
/-- Reduce a chip's State-emission contract to its public Clean exposed-channel interface and three
evaluation facts.  This is the reusable boundary between circuit construction and the semantic row
view: callers never unfold the chip's subcircuit tree, and the theorem still talks about the exact
`Operations.interactionValuesWith` list evaluated by Clean. -/
theorem circuitStateEmissionShape_of_exposure {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitStateExposureContract circuit view) :
    CircuitStateEmissionShape circuit view := by
  obtain ⟨gate, pullMessage, pushMessage, exposure, gate_eval, pull_eval, push_eval⟩ := contract
  intro data physical
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  change component.operations.interactionValuesWith stateChannel.toRaw env =
    [stateChannel.pulledIfValue rowView.is_real (statePullOfView rowView),
     stateChannel.pushedIfValue rowView.is_real (statePushOfView rowView)]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((circuit.main inputVar).operations offset).interactionsWith stateChannel.toRaw) = _
  rw [circuit.interactionsWith_eq_of_mem_exposedChannels inputVar offset _
    (exposure inputVar offset)]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, Channel.eval_pushedIf]
  rw [gate_eval env, pull_eval env, push_eval env]
  have inputEq : Eval.eval env inputVar = component.rowInput env := by
    exact eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  rw [inputEq, outputEq]

/-- One-step descriptor transport for chip-local exposure proofs.  All dependent typeclass evidence
is taken from `kind` explicitly, so applying this theorem never asks typeclass search to reduce a
concrete `ChipKind` record. -/
theorem stateEmissionShape_of_circuitExposure (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (contract : @CircuitStateExposureContract p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    StateEmissionShape ⟨kind, circuit, spec_eq, opcodes, rdGuard⟩ := by
  apply stateEmissionShape_of_circuit
  exact @circuitStateEmissionShape_of_exposure p _ kind.Inputs kind.Cols
    kind.provableInputs kind.provableCols circuit kind.view contract

/-- Lift a chip's raw emission contract to the proof-carrying typed decoder. -/
theorem DecodedInstructionRow.stateInteractions_eq
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (contract : StateEmissionShape decoded.chip) :
    decoded.interactionsWith data stateChannel =
      [TypedInteraction.pulledIfValue stateChannel (decoded.toChipRow data).is_real
        (statePullMessage (decoded.toChipRow data)),
       TypedInteraction.pushedIfValue stateChannel (decoded.toChipRow data).is_real
        (statePushMessage (decoded.toChipRow data))] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw, DecodedInstructionRow.environment,
    DecodedInstructionRow.toChipRow] using contract data decoded.physical

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- One active State pair contributes exactly its successor to the produced-message list. -/
theorem producedMessages_statePair_one [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (source target : StateMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue stateChannel 1 source,
       TypedInteraction.pushedIfValue stateChannel 1 target] = [target] := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have pullSigned : signedVal
      (TypedInteraction.pulledIfValue stateChannel 1 source).mult = -1 := by
    calc
      _ = signedVal (-(1 : ZMod p)) := rfl
      _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
      _ = -1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        norm_num
  have pushSigned : signedVal
      (TypedInteraction.pushedIfValue stateChannel 1 target).mult = 1 := by
    calc
      _ = signedVal (1 : ZMod p) := rfl
      _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
      _ = 1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        norm_num
  have filtered : List.filter (fun interaction => signedVal interaction.mult = 1)
      [TypedInteraction.pulledIfValue stateChannel 1 source,
       TypedInteraction.pushedIfValue stateChannel 1 target] =
        [TypedInteraction.pushedIfValue stateChannel 1 target] := by
    simp only [List.filter_cons, List.filter_nil]
    rw [pullSigned, pushSigned]
    norm_num
  rw [producedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- One active State pair contributes exactly its current state to the consumed-message list. -/
theorem consumedMessages_statePair_one [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (source target : StateMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue stateChannel 1 source,
       TypedInteraction.pushedIfValue stateChannel 1 target] = [source] := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have pullSigned : signedVal
      (TypedInteraction.pulledIfValue stateChannel 1 source).mult = -1 := by
    calc
      _ = signedVal (-(1 : ZMod p)) := rfl
      _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
      _ = -1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        norm_num
  have pushSigned : signedVal
      (TypedInteraction.pushedIfValue stateChannel 1 target).mult = 1 := by
    calc
      _ = signedVal (1 : ZMod p) := rfl
      _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
      _ = 1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        norm_num
  have filtered : List.filter (fun interaction => signedVal interaction.mult = -1)
      [TypedInteraction.pulledIfValue stateChannel 1 source,
       TypedInteraction.pushedIfValue stateChannel 1 target] =
        [TypedInteraction.pulledIfValue stateChannel 1 source] := by
    simp only [List.filter_cons, List.filter_nil]
    rw [pullSigned, pushSigned]
    norm_num
  rw [consumedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- A disabled State pair contributes no produced message. -/
theorem producedMessages_statePair_zero [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (source target : StateMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue stateChannel 0 source,
       TypedInteraction.pushedIfValue stateChannel 0 target] = [] := by
  simp [producedMessages, signedVal]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- A disabled State pair contributes no consumed message. -/
theorem consumedMessages_statePair_zero [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (source target : StateMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue stateChannel 0 source,
       TypedInteraction.pushedIfValue stateChannel 0 target] = [] := by
  simp [consumedMessages, signedVal]

/-- Produced messages of flattened decoded State pairs are precisely the successor messages of the
active rows. -/
theorem producedMessages_decodedStatePairs
    (data : ProverData (ZMod p)) (rows : List (DecodedInstructionRow p))
    (binary : ∀ decoded ∈ rows, (decoded.toChipRow data).is_real = 0 ∨
      (decoded.toChipRow data).is_real = 1) :
    producedMessages (rows.flatMap fun decoded =>
      [TypedInteraction.pulledIfValue stateChannel (decoded.toChipRow data).is_real
        (statePullMessage (decoded.toChipRow data)),
       TypedInteraction.pushedIfValue stateChannel (decoded.toChipRow data).is_real
        (statePushMessage (decoded.toChipRow data))]) =
      (rows.filter fun decoded => (decoded.toChipRow data).is_real = 1).map
        fun decoded => statePushMessage (decoded.toChipRow data) := by
  induction rows with
  | nil => rfl
  | cons decoded rows ih =>
      have headBinary := binary decoded List.mem_cons_self
      have tailBinary : ∀ row ∈ rows, (row.toChipRow data).is_real = 0 ∨
          (row.toChipRow data).is_real = 1 :=
        fun row rowMem => binary row (List.mem_cons_of_mem decoded rowMem)
      simp only [List.flatMap_cons, producedMessages_append]
      rw [ih tailBinary]
      rcases headBinary with zero | one
      · rw [zero, producedMessages_statePair_zero]
        simp [zero]
      · rw [one, producedMessages_statePair_one]
        simp [one]

/-- Consumed messages of flattened decoded State pairs are precisely the current messages of the
active rows. -/
theorem consumedMessages_decodedStatePairs
    (data : ProverData (ZMod p)) (rows : List (DecodedInstructionRow p))
    (binary : ∀ decoded ∈ rows, (decoded.toChipRow data).is_real = 0 ∨
      (decoded.toChipRow data).is_real = 1) :
    consumedMessages (rows.flatMap fun decoded =>
      [TypedInteraction.pulledIfValue stateChannel (decoded.toChipRow data).is_real
        (statePullMessage (decoded.toChipRow data)),
       TypedInteraction.pushedIfValue stateChannel (decoded.toChipRow data).is_real
        (statePushMessage (decoded.toChipRow data))]) =
      (rows.filter fun decoded => (decoded.toChipRow data).is_real = 1).map
        fun decoded => statePullMessage (decoded.toChipRow data) := by
  induction rows with
  | nil => rfl
  | cons decoded rows ih =>
      have headBinary := binary decoded List.mem_cons_self
      have tailBinary : ∀ row ∈ rows, (row.toChipRow data).is_real = 0 ∨
          (row.toChipRow data).is_real = 1 :=
        fun row rowMem => binary row (List.mem_cons_of_mem decoded rowMem)
      simp only [List.flatMap_cons, consumedMessages_append]
      rw [ih tailBinary]
      rcases headBinary with zero | one
      · rw [zero, consumedMessages_statePair_zero]
        simp [zero]
      · rw [one, consumedMessages_statePair_one]
        simp [one]

/-- An active decoded row contributes exactly its semantic successor State message. -/
theorem DecodedInstructionRow.producedStateMessages_of_real
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (contract : StateEmissionShape decoded.chip)
    (real : (decoded.toChipRow data).is_real = 1) :
    producedMessages (decoded.interactionsWith data stateChannel) =
      [statePushMessage (decoded.toChipRow data)] := by
  rw [decoded.stateInteractions_eq data contract, real]
  exact producedMessages_statePair_one _ _

/-- An active decoded row consumes exactly its semantic current State message. -/
theorem DecodedInstructionRow.consumedStateMessages_of_real
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (contract : StateEmissionShape decoded.chip)
    (real : (decoded.toChipRow data).is_real = 1) :
    consumedMessages (decoded.interactionsWith data stateChannel) =
      [statePullMessage (decoded.toChipRow data)] := by
  rw [decoded.stateInteractions_eq data contract, real]
  exact consumedMessages_statePair_one _ _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- A gated pull/push State pair has the exact integer multiplicity range needed by typed balance. -/
theorem statePair_signed_binary [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (gate : ZMod p) (binary : gate = 0 ∨ gate = 1) (source target : StateMsg (ZMod p)) :
    ∀ interaction ∈
      [TypedInteraction.pulledIfValue stateChannel gate source,
       TypedInteraction.pushedIfValue stateChannel gate target],
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  intro interaction member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [TypedInteraction.pulledIfValue_mult, signedVal_neg_is_real hp binary]
    rcases val_of_binary hp binary with value | value <;> rw [value] <;> omega
  · rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp binary]
    rcases val_of_binary hp binary with value | value <;> rw [value] <;> omega

/-- The typed State interactions of a decoded row inherit binary multiplicities from its selector. -/
theorem DecodedInstructionRow.stateInteractions_signed_binary
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (contract : StateEmissionShape decoded.chip)
    (binary : (decoded.toChipRow data).is_real = 0 ∨
      (decoded.toChipRow data).is_real = 1) :
    ∀ interaction ∈ decoded.interactionsWith data stateChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1 := by
  rw [decoded.stateInteractions_eq data contract]
  exact statePair_signed_binary _ binary _ _

/- Add is the first concrete check of the shared State-emission contract. -/
theorem addChip_stateEmissionShape : StateEmissionShape
    (⟨AddChip.kind, AddChip.circuit, rfl, [.ADD], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (AddChip.circuit (p := p)) AddChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [AddChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, AddChip.rowView, circuit_norm]

theorem addiChip_stateEmissionShape : StateEmissionShape
    (⟨AddiChip.kind, AddiChip.circuit, rfl, [.ADDI], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (AddiChip.circuit (p := p)) AddiChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [AddiChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, AddiChip.rowView, circuit_norm]

theorem addwChip_stateEmissionShape : StateEmissionShape
    (⟨AddwChip.kind, AddwChip.circuit, rfl, [.ADDW], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (AddwChip.circuit (p := p)) AddwChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [AddwChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, AddwChip.rowView, circuit_norm]

theorem subChip_stateEmissionShape : StateEmissionShape
    (⟨SubChip.kind, SubChip.circuit, rfl, [.SUB], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (SubChip.circuit (p := p)) SubChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [SubChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, SubChip.rowView, circuit_norm]

theorem subwChip_stateEmissionShape : StateEmissionShape
    (⟨SubwChip.kind, SubwChip.circuit, rfl, [.SUBW], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (SubwChip.circuit (p := p)) SubwChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [SubwChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, SubwChip.rowView, circuit_norm]

theorem bitwiseChip_stateEmissionShape : StateEmissionShape
    (⟨BitwiseChip.kind, BitwiseChip.circuit, rfl, [.XOR, .OR, .AND], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (BitwiseChip.circuit (p := p))
    BitwiseChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  · intros
    simp [BitwiseChip.circuit, expose, BitwiseChip.exposedStateInteractions,
      cpuStatePullMessage, cpuStatePushMessage]
  all_goals
    intros
    simp only [BitwiseChip.circuit, statePullOfView, statePushOfView,
      stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, BitwiseChip.rowView, circuit_norm]

theorem ltChip_stateEmissionShape : StateEmissionShape
    (⟨LtChip.kind, LtChip.circuit, rfl, [.SLT, .SLTU], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (LtChip.circuit (p := p)) LtChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  · intros
    simp [LtChip.circuit, expose, LtChip.exposedStateInteractions,
      cpuStatePullMessage, cpuStatePushMessage]
  all_goals
    intros
    simp only [LtChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, LtChip.rowView, circuit_norm]

theorem shiftLeftChip_stateEmissionShape : StateEmissionShape
    (⟨ShiftLeftChip.kind, ShiftLeftChip.circuit, rfl, [.SLL, .SLLW], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (ShiftLeftChip.circuit (p := p))
    ShiftLeftChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp [ShiftLeftChip.circuit, ShiftLeftChip.stateExposure, Readers.CPUState.exposedState,
      Readers.CPUState.stateInteractions, Readers.CPUState.currentMsg, Readers.CPUState.nextMsg,
      statePullOfView, statePushOfView, stateAccess, cpuStatePullMessage, cpuStatePushMessage,
      ShiftLeftChip.rowView, circuit_norm]

theorem shiftRightChip_stateEmissionShape : StateEmissionShape
    (⟨ShiftRightChip.kind, ShiftRightChip.circuit, rfl, [.SRL, .SRA, .SRLW, .SRAW], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (ShiftRightChip.circuit (p := p))
    ShiftRightChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp [ShiftRightChip.circuit, ShiftRightChip.stateExposure, Readers.CPUState.exposedState,
      Readers.CPUState.stateInteractions, Readers.CPUState.currentMsg, Readers.CPUState.nextMsg,
      statePullOfView, statePushOfView, stateAccess, cpuStatePullMessage, cpuStatePushMessage,
      ShiftRightChip.rowView, circuit_norm]

theorem jalChip_stateEmissionShape : StateEmissionShape
    (⟨JalChip.kind, JalChip.circuit, rfl, [.JAL], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (JalChip.circuit (p := p)) JalChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input offset => cpuStateNextMessage input.state
      #v[var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩] 8, ?_, ?_, ?_, ?_⟩
  · intros
    simp [JalChip.circuit, expose, JalChip.exposedStateInteractions,
      cpuStatePullMessage, cpuStateNextMessage]
  all_goals
    intros
    simp [JalChip.circuit, statePullOfView,
      statePushOfView, stateAccess, cpuStatePullMessage, cpuStateNextMessage,
      JalChip.rowView, circuit_norm]

theorem jalrChip_stateEmissionShape : StateEmissionShape
    (⟨JalrChip.kind, JalrChip.circuit, rfl, [.JALR], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (JalrChip.circuit (p := p)) JalrChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input offset => cpuStateNextMessage input.state
      #v[var ⟨offset⟩ - var ⟨offset + 8⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩] 8,
    ?_, ?_, ?_, ?_⟩
  · intros
    simp [JalrChip.circuit, expose, JalrChip.exposedStateInteractions,
      cpuStatePullMessage, cpuStateNextMessage]
  all_goals
    intros
    simp [JalrChip.circuit, statePullOfView,
      statePushOfView, stateAccess, cpuStatePullMessage, cpuStateNextMessage,
      JalrChip.rowView, circuit_norm]

theorem branchChip_stateEmissionShape : StateEmissionShape
    (⟨BranchChip.kind, BranchChip.circuit, rfl,
      [.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (BranchChip.circuit (p := p))
    BranchChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input offset => cpuStateNextMessage input.state
      #v[var ⟨offset + 7⟩, var ⟨offset + 8⟩,
        var ⟨offset + 9⟩] 8, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp [BranchChip.circuit,
      BranchChip.stateExposure, Readers.CPUState.exposedState,
      Readers.CPUState.stateInteractions, Readers.CPUState.currentMsg,
      Readers.CPUState.nextMsg, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStateNextMessage, BranchChip.rowView,
      circuit_norm]

theorem uTypeChip_stateEmissionShape : StateEmissionShape
    (⟨UTypeChip.kind, UTypeChip.circuit, rfl, [.AUIPC, .LUI], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (UTypeChip.circuit (p := p)) UTypeChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  · intros
    simp [UTypeChip.circuit, expose, UTypeChip.exposedStateInteractions,
      cpuStatePullMessage, cpuStatePushMessage]
  all_goals
    intros
    simp [UTypeChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, UTypeChip.rowView, circuit_norm]

theorem loadDoubleChip_stateEmissionShape : StateEmissionShape
    (⟨LoadDoubleChip.kind, LoadDoubleChip.circuit, rfl, [.LD], .nonX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (LoadDoubleChip.circuit (p := p))
    LoadDoubleChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [LoadDoubleChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, LoadDoubleChip.rowView, circuit_norm]

theorem loadByteChip_stateEmissionShape : StateEmissionShape
    (⟨LoadByteChip.kind, LoadByteChip.circuit, rfl, [.LB, .LBU], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (LoadByteChip.circuit (p := p))
    LoadByteChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_lb + input.is_lbu,
    fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [LoadByteChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, LoadByteChip.rowView, LoadByteChip.isReal,
      circuit_norm]

theorem loadHalfChip_stateEmissionShape : StateEmissionShape
    (⟨LoadHalfChip.kind, LoadHalfChip.circuit, rfl, [.LH, .LHU], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (LoadHalfChip.circuit (p := p))
    LoadHalfChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_lh + input.is_lhu,
    fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [LoadHalfChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, LoadHalfChip.rowView, LoadHalfChip.isReal,
      circuit_norm]

theorem loadWordChip_stateEmissionShape : StateEmissionShape
    (⟨LoadWordChip.kind, LoadWordChip.circuit, rfl, [.LW, .LWU], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (LoadWordChip.circuit (p := p))
    LoadWordChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_lw + input.is_lwu,
    fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [LoadWordChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, LoadWordChip.rowView, LoadWordChip.isReal,
      circuit_norm]

theorem loadX0Chip_stateEmissionShape : StateEmissionShape
    (⟨LoadX0Chip.kind, LoadX0Chip.circuit, rfl,
      [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD], .onlyX0⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (LoadX0Chip.circuit (p := p)) LoadX0Chip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
      + input.is_lw + input.is_lwu + input.is_ld,
    fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [LoadX0Chip.circuit, statePullOfView, statePushOfView,
      stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, LoadX0Chip.rowView, LoadX0Chip.isReal,
      circuit_norm]

theorem storeByteChip_stateEmissionShape : StateEmissionShape
    (⟨StoreByteChip.kind, StoreByteChip.circuit, rfl, [.SB], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (StoreByteChip.circuit (p := p))
    StoreByteChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [StoreByteChip.circuit, statePullOfView,
      statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, StoreByteChip.rowView, circuit_norm]

theorem storeHalfChip_stateEmissionShape : StateEmissionShape
    (⟨StoreHalfChip.kind, StoreHalfChip.circuit, rfl, [.SH], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (StoreHalfChip.circuit (p := p))
    StoreHalfChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [StoreHalfChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, StoreHalfChip.rowView, circuit_norm]

theorem storeWordChip_stateEmissionShape : StateEmissionShape
    (⟨StoreWordChip.kind, StoreWordChip.circuit, rfl, [.SW], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (StoreWordChip.circuit (p := p))
    StoreWordChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [StoreWordChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, StoreWordChip.rowView, circuit_norm]

theorem storeDoubleChip_stateEmissionShape : StateEmissionShape
    (⟨StoreDoubleChip.kind, StoreDoubleChip.circuit, rfl, [.SD], .any⟩ : SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (StoreDoubleChip.circuit (p := p))
    StoreDoubleChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [StoreDoubleChip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, StoreDoubleChip.rowView, circuit_norm]

theorem mulChip_stateEmissionShape : StateEmissionShape
    (⟨MulChip.kind, MulChip.circuit, rfl, [.MUL, .MULH, .MULHU, .MULHSU, .MULW], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (MulChip.circuit (p := p)) MulChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp [MulChip.circuit, MulChip.exposedStateInteractions,
      MulChip.exposedMemoryInteractions, MulChip.exposedProgramInteractions,
      expose, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, MulChip.rowView, circuit_norm]

set_option maxHeartbeats 16000000 in
theorem divRemChip_stateEmissionShape : StateEmissionShape
    (⟨DivRemChip.kind, DivRemChip.circuit, rfl,
      [.DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .nonX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (DivRemChip.circuit (p := p))
    DivRemChip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp [DivRemChip.circuit, DivRemChip.exposedChannels, DivRemChip.stateExposure,
      Readers.CPUState.exposedState,
      Readers.CPUState.stateInteractions, Readers.CPUState.currentMsg, Readers.CPUState.nextMsg,
      statePullOfView, statePushOfView, stateAccess, cpuStatePullMessage, cpuStatePushMessage,
      DivRemChip.rowView, circuit_norm]

theorem aluX0Chip_stateEmissionShape : StateEmissionShape
    (⟨AluX0Chip.kind, AluX0Chip.circuit, rfl,
      [.ADD, .ADDI, .ADDW, .SUB, .SUBW, .XOR, .OR, .AND, .SLT, .SLTU,
       .SLL, .SLLW, .SRL, .SRA, .SRLW, .SRAW,
       .MUL, .MULH, .MULHU, .MULHSU, .MULW,
       .DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .onlyX0⟩ :
      SupportedChip p) := by
  apply stateEmissionShape_of_circuitExposure
  change CircuitStateExposureContract (p := p) (AluX0Chip.circuit (p := p)) AluX0Chip.rowView
  unfold CircuitStateExposureContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ => cpuStatePullMessage input.state,
    fun input _ => cpuStatePushMessage input.state, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [AluX0Chip.circuit, statePullOfView, statePushOfView, stateAccess,
      cpuStatePullMessage, cpuStatePushMessage, AluX0Chip.rowView,
      AluX0Chip.exposedStateInteractions, expose, List.mem_singleton,
      true_or, circuit_norm]

set_option maxHeartbeats 1000000 in
/-- Every descriptor in the single supported-machine registry emits exactly one gated State pull and
one gated State push, with payloads equal to its semantic `RowView`.  This is the registry-level
contract consumed by deterministic witness decoding. -/
theorem supportedChip_stateEmissionShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : StateEmissionShape chip := by
  fin_cases chipMem
  · exact addChip_stateEmissionShape
  · exact addiChip_stateEmissionShape
  · exact addwChip_stateEmissionShape
  · exact subChip_stateEmissionShape
  · exact subwChip_stateEmissionShape
  · exact bitwiseChip_stateEmissionShape
  · exact ltChip_stateEmissionShape
  · exact shiftLeftChip_stateEmissionShape
  · exact shiftRightChip_stateEmissionShape
  · exact jalChip_stateEmissionShape
  · exact jalrChip_stateEmissionShape
  · exact branchChip_stateEmissionShape
  · exact uTypeChip_stateEmissionShape
  · exact loadByteChip_stateEmissionShape
  · exact loadHalfChip_stateEmissionShape
  · exact loadWordChip_stateEmissionShape
  · exact loadDoubleChip_stateEmissionShape
  · exact loadX0Chip_stateEmissionShape
  · exact storeByteChip_stateEmissionShape
  · exact storeHalfChip_stateEmissionShape
  · exact storeWordChip_stateEmissionShape
  · exact storeDoubleChip_stateEmissionShape
  · exact mulChip_stateEmissionShape
  · exact divRemChip_stateEmissionShape
  · exact aluX0Chip_stateEmissionShape

/-- Every row produced by the canonical typed decoder inherits the exact State-emission contract from
its retained supported-chip descriptor. -/
theorem DecodedInstructionRow.stateEmissionShape_of_mem
    (decoded : DecodedInstructionRow p) (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables) :
    StateEmissionShape decoded.chip :=
  supportedChip_stateEmissionShape decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem)

/-- Canonically decoded rows expose their actual Clean State interactions as the semantic pull/push
pair, without an existential trace or a hand-written interaction shadow. -/
theorem DecodedInstructionRow.stateInteractions_eq_of_mem
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables) :
    decoded.interactionsWith data stateChannel =
      [TypedInteraction.pulledIfValue stateChannel (decoded.toChipRow data).is_real
        (statePullMessage (decoded.toChipRow data)),
       TypedInteraction.pushedIfValue stateChannel (decoded.toChipRow data).is_real
        (statePushMessage (decoded.toChipRow data))] :=
  decoded.stateInteractions_eq data (decoded.stateEmissionShape_of_mem tables decodedMem)

/-- The eleven provider/boundary tables contribute no State interactions.  This follows from their
declared circuit channels, so it is independent of their physical row contents. -/
theorem witness_providerStateInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (witness.tables.drop 25).flatMap
        (typedTableInteractionsWith · stateChannel) = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro table tableMem
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  exact sp1ProviderTables_stateChannel_not_mem table.component
    (witness_providerTable_component_mem witness table tableMem)

omit [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the final-boundary State projection. -/
theorem eval_finalBoundaryStateMessage (env : Environment (ZMod p))
    (input : Var SP1PublicIO (ZMod p)) :
    Eval.eval env
      (⟨input.final_clk_high, input.final_clk_low, input.final_pc0, input.final_pc1,
        input.final_pc2⟩ : StateMsg (Expression (ZMod p))) =
      ⟨(Eval.eval env input).final_clk_high, (Eval.eval env input).final_clk_low,
        (Eval.eval env input).final_pc0, (Eval.eval env input).final_pc1,
        (Eval.eval env input).final_pc2⟩ := by
  simp only [circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the initial-boundary State projection. -/
theorem eval_initialBoundaryStateMessage (env : Environment (ZMod p))
    (input : Var SP1PublicIO (ZMod p)) :
    Eval.eval env
      (⟨input.init_clk_high, input.init_clk_low, input.init_pc0, input.init_pc1,
        input.init_pc2⟩ : StateMsg (Expression (ZMod p))) =
      ⟨(Eval.eval env input).init_clk_high, (Eval.eval env input).init_clk_low,
        (Eval.eval env input).init_pc0, (Eval.eval env input).init_pc1,
        (Eval.eval env input).init_pc2⟩ := by
  simp only [circuit_norm]

set_option maxHeartbeats 1000000 in
/-- The verifier table contributes exactly the public final pull followed by the public initial push. -/
theorem witness_verifierStateInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith witness.verifierTable stateChannel =
      [TypedInteraction.pulledIfValue stateChannel 1
        ⟨witness.publicInput.final_clk_high, witness.publicInput.final_clk_low,
          witness.publicInput.final_pc0, witness.publicInput.final_pc1,
          witness.publicInput.final_pc2⟩,
       TypedInteraction.pushedIfValue stateChannel 1
        ⟨witness.publicInput.init_clk_high, witness.publicInput.init_clk_low,
          witness.publicInput.init_pc0, witness.publicInput.init_pc1,
          witness.publicInput.init_pc2⟩] := by
  have inputEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)) = witness.publicInput :=
    ProvableType.eval_fromInput_varFromOffset_zero witness.publicInput witness.data
  have finalEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_clk_high,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_clk_low,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_pc0,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_pc1,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_pc2⟩ :
        StateMsg (Expression (ZMod p))) =
      (⟨witness.publicInput.final_clk_high, witness.publicInput.final_clk_low,
        witness.publicInput.final_pc0, witness.publicInput.final_pc1,
        witness.publicInput.final_pc2⟩ : StateMsg (ZMod p)) := by
    rw [eval_finalBoundaryStateMessage, inputEval]
  have initialEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_clk_high,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_clk_low,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_pc0,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_pc1,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_pc2⟩ :
        StateMsg (Expression (ZMod p))) =
      (⟨witness.publicInput.init_clk_high, witness.publicInput.init_clk_low,
        witness.publicInput.init_pc0, witness.publicInput.init_pc1,
        witness.publicInput.init_pc2⟩ : StateMsg (ZMod p)) := by
    rw [eval_initialBoundaryStateMessage, inputEval]
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedTableInteractionsWith_raw]
  unfold Table.interactionsWith
  rw [EnsembleWitness.verifierTable_flatMap]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromInput witness.publicInput witness.data))
      (((sp1StateVerifierMain
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p))).operations
          (size SP1PublicIO)).interactionsWith stateChannel.toRaw) = _
  rw [sp1StateVerifierMain_stateInteractions]
  simp only [List.map_cons, List.map_nil]
  rw [Channel.eval_pulled, Channel.eval_pushed, finalEval, initialEval]
  rfl

/-- The decoded instruction prefix's State interactions are exactly the flattened semantic row pairs. -/
theorem decodedWitnessStateInteractions_eq
    (data : ProverData (ZMod p)) (tables : List (Table (ZMod p))) :
    decodedWitnessInstructionInteractionsWith data tables stateChannel =
      (decodedInstructionRows (p := p) tables).flatMap fun decoded =>
        [TypedInteraction.pulledIfValue stateChannel (decoded.toChipRow data).is_real
          (statePullMessage (decoded.toChipRow data)),
         TypedInteraction.pushedIfValue stateChannel (decoded.toChipRow data).is_real
          (statePushMessage (decoded.toChipRow data))] := by
  unfold decodedWitnessInstructionInteractionsWith decodedInstructionInteractionsWith
  apply List.flatMap_congr
  intro decoded decodedMem
  exact decoded.stateInteractions_eq_of_mem data tables decodedMem

/-- Exact State-channel decomposition of the whole ensemble witness: public boundary pair followed
by the deterministic decoder's per-instruction pairs. -/
theorem typedEnsembleStateInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedEnsembleInteractionsWith witness stateChannel =
      [TypedInteraction.pulledIfValue stateChannel 1
        ⟨witness.publicInput.final_clk_high, witness.publicInput.final_clk_low,
          witness.publicInput.final_pc0, witness.publicInput.final_pc1,
          witness.publicInput.final_pc2⟩,
       TypedInteraction.pushedIfValue stateChannel 1
        ⟨witness.publicInput.init_clk_high, witness.publicInput.init_clk_low,
          witness.publicInput.init_pc0, witness.publicInput.init_pc1,
          witness.publicInput.init_pc2⟩] ++
        (decodedInstructionRows (p := p) witness.tables).flatMap fun decoded =>
          [TypedInteraction.pulledIfValue stateChannel
            (decoded.toChipRow witness.data).is_real
            (statePullMessage (decoded.toChipRow witness.data)),
           TypedInteraction.pushedIfValue stateChannel
            (decoded.toChipRow witness.data).is_real
            (statePushMessage (decoded.toChipRow witness.data))] := by
  rw [typedEnsembleInteractionsWith_partition, witness_verifierStateInteractions_eq,
    decodedWitnessStateInteractions_eq, witness_providerStateInteractions_eq_nil,
    List.append_nil]

/-- Produced State messages of the whole witness are the public initial boundary followed by every
active decoded row's successor. -/
theorem producedMessages_typedEnsembleState_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (binary : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1) :
    producedMessages (typedEnsembleInteractionsWith witness stateChannel) =
      initialBoundaryStateMessage witness.publicInput ::
        (realDecodedInstructionRows witness.data witness.tables).map
          fun decoded => statePushMessage (decoded.toChipRow witness.data) := by
  rw [typedEnsembleStateInteractions_eq, producedMessages_append,
    producedMessages_statePair_one,
    producedMessages_decodedStatePairs witness.data _ binary]
  rfl

/-- Consumed State messages of the whole witness are the public final boundary followed by every
active decoded row's current state. -/
theorem consumedMessages_typedEnsembleState_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (binary : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1) :
    consumedMessages (typedEnsembleInteractionsWith witness stateChannel) =
      finalBoundaryStateMessage witness.publicInput ::
        (realDecodedInstructionRows witness.data witness.tables).map
          fun decoded => statePullMessage (decoded.toChipRow witness.data) := by
  rw [typedEnsembleStateInteractions_eq, consumedMessages_append,
    consumedMessages_statePair_one,
    consumedMessages_decodedStatePairs witness.data _ binary]
  rfl

/-- Binary decoded selectors imply `{-1,0,1}` signed multiplicities for the whole State channel;
the verifier boundary is the constant active pair and providers contribute nothing. -/
theorem typedEnsembleStateInteractions_signed_binary
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (binary : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness stateChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1 := by
  rw [typedEnsembleStateInteractions_eq]
  intro interaction interactionMem
  rcases List.mem_append.mp interactionMem with boundaryMem | rowMem
  · exact statePair_signed_binary 1 (Or.inr rfl) _ _ interaction boundaryMem
  · obtain ⟨decoded, decodedMem, interactionMem⟩ := List.mem_flatMap.mp rowMem
    exact statePair_signed_binary _ (binary decoded decodedMem) _ _ interaction interactionMem

/-- Clean State balance is now an exact typed endpoint permutation over all active deterministically
decoded rows.  No `LookupAccess` shadow or existential row list appears in the statement. -/
theorem realDecodedStateMessages_perm
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (binary : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1) :
    (initialBoundaryStateMessage witness.publicInput ::
      (realDecodedInstructionRows witness.data witness.tables).map
        fun decoded => statePushMessage (decoded.toChipRow witness.data)).Perm
    (finalBoundaryStateMessage witness.publicInput ::
      (realDecodedInstructionRows witness.data witness.tables).map
        fun decoded => statePullMessage (decoded.toChipRow witness.data)) := by
  classical
  have channelBalanced := typedInteractions_balanced witness balanced stateChannel
    (by simp [sp1Ensemble_channels])
  have messagePerm := producedMessages_perm_consumedMessages
    (typedEnsembleInteractionsWith witness stateChannel) channelBalanced
      (typedEnsembleStateInteractions_signed_binary witness binary)
  rw [producedMessages_typedEnsembleState_eq witness binary,
    consumedMessages_typedEnsembleState_eq witness binary] at messagePerm
  exact messagePerm

/-- The semantic State edge carried by one deterministically decoded instruction row. -/
noncomputable def decodedStateEdge (data : ProverData (ZMod p))
    (decoded : DecodedInstructionRow p) : StateMsg (ZMod p) × StateMsg (ZMod p) :=
  (statePullMessage (decoded.toChipRow data), statePushMessage (decoded.toChipRow data))

/-- The exact typed State-channel permutation in the endpoint-multiset form consumed by the generic
ordering theorem. -/
theorem realDecodedState_endpointBalanced
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (binary : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1) :
    RankedGrounding.EndpointBalanced
      (↑(realDecodedInstructionRows witness.data witness.tables) :
        Multiset (DecodedInstructionRow p))
      (decodedStateEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) := by
  change
    (↑(initialBoundaryStateMessage witness.publicInput ::
      (realDecodedInstructionRows witness.data witness.tables).map fun decoded =>
        statePushMessage (decoded.toChipRow witness.data)) : Multiset (StateMsg (ZMod p))) =
    ↑(finalBoundaryStateMessage witness.publicInput ::
      (realDecodedInstructionRows witness.data witness.tables).map fun decoded =>
        statePullMessage (decoded.toChipRow witness.data))
  exact Multiset.coe_eq_coe.mpr (realDecodedStateMessages_perm witness balanced binary)

/-- Physical witness constraints discharge the selector premise of the typed State endpoint
balance.  This is the capstone-facing form: selector booleanity is an AIR fact, not an extra
machine-level assumption. -/
theorem realDecodedState_endpointBalanced_of_constraints
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    RankedGrounding.EndpointBalanced
      (↑(realDecodedInstructionRows witness.data witness.tables) :
        Multiset (DecodedInstructionRow p))
      (decodedStateEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) :=
  realDecodedState_endpointBalanced witness balanced
    (witness_decodedInstructionRows_selectorBinary witness constraints)

/-- State balance plus strict decoded-clock growth orders every active instruction row exactly once.
The clock-growth premise is deliberately exposed: it is the remaining row-local AIR fact, not an
extra global execution assumption or an opaque decoding seam. -/
theorem realDecodedState_exhaustiveTrail
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (binary : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1)
    (increases : ∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).1 <
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).2) :
    RankedGrounding.ExhaustiveTrail
      (↑(realDecodedInstructionRows witness.data witness.tables) :
        Multiset (DecodedInstructionRow p))
      (decodedStateEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) := by
  classical
  apply RankedGrounding.exists_exhaustiveTrail_of_endpointBalanced
    (rank := Semantics.StateMsg.timeNat)
    (balanced := realDecodedState_endpointBalanced witness balanced binary)
  intro decoded decodedMem
  exact increases decoded (by simpa using decodedMem)

/-- Constraint satisfaction and State balance reduce exhaustive instruction ordering to the one
remaining row-local fact: every active decoded State edge strictly advances its clock. -/
theorem realDecodedState_exhaustiveTrail_of_constraints
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    (increases : ∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).1 <
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).2) :
    RankedGrounding.ExhaustiveTrail
      (↑(realDecodedInstructionRows witness.data witness.tables) :
        Multiset (DecodedInstructionRow p))
      (decodedStateEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) :=
  realDecodedState_exhaustiveTrail witness balanced
    (witness_decodedInstructionRows_selectorBinary witness constraints) increases

end SP1Clean.Soundness
