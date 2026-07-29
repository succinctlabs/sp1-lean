import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.LocalExecution
import SP1Clean.Soundness.TypedMemory

/-! # The decoded-row circuit soundness boundary

`GeneralFormalCircuit.weakSoundness` is the one legitimate route from a physical AIR row to its
semantic chip `Spec`.  This module names that boundary for the deterministic instruction decoder and
separates what global grounding must still supply:

* constraints come directly from the aligned physical witness table;
* Byte and Program guarantees are already finished by provider balance;
* State guarantees are vacuous in the current structural channel;
* Memory guarantees and the chip's soundness `Assumptions` are the dynamic, timed obligations.

The resulting API prevents the capstone from assuming `ChipRow.chipSpec` directly or rebuilding a
second operation-level semantics beside the chip circuit.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Channel guarantees for one exact decoded physical row.  This is intentionally phrased against
the circuit's real `Operations`; it is not a shadow interaction model. -/
structure DecodedRowChannelGuarantees (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : Prop where
  state : decoded.chip.table.operations.ChannelGuarantees stateChannel.toRaw
    (decoded.environment data)
  byte : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
    (decoded.environment data)
  program : decoded.chip.table.operations.ChannelGuarantees programChannel.toRaw
    (decoded.environment data)
  memory : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
    (decoded.environment data)

/-- Every interaction in a supported instruction circuit must use one of the four declared SP1
buses.  Keeping this structural condition explicit catches an accidentally unregistered channel. -/
def UsesSupportedBusChannels (decoded : DecodedInstructionRow p) : Prop :=
  decoded.chip.table.operations.channels ⊆
    [stateChannel.toRaw, byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- Descriptor-level form of the same four-bus invariant.  It talks only about the circuit's declared
channel lists, so the generic `FormalCircuitBase.channels_subset` theorem can transport it to the
flattened component operations. -/
def SupportedChipUsesSupportedBusChannels (chip : SupportedChip p) : Prop :=
  chip.table.circuit.channels ⊆
    [stateChannel.toRaw, byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

local macro "busRegistryCase " circuit:term ", " elaborated:term : tactic =>
  `(tactic| (
    change ($elaborated:term).channelsWithGuarantees ⊆ _ ∧
      ($circuit:term).channelsWithRequirements ⊆ _
    simp only [$circuit:term, $elaborated:term, circuit_norm]))

set_option maxHeartbeats 800000 in
/-- Every descriptor in the single supported-machine registry declares only the four SP1 buses. -/
theorem supportedChip_usesSupportedBusChannels (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) :
    SupportedChipUsesSupportedBusChannels chip := by
  unfold SupportedChipUsesSupportedBusChannels
  change chip.table.circuit.channelsWithGuarantees ++
      chip.table.circuit.channelsWithRequirements ⊆ _
  rw [List.append_subset]
  fin_cases chipMem
  · busRegistryCase AddChip.circuit, AddChip.elaborated
  · busRegistryCase AddiChip.circuit, AddiChip.elaborated
  · busRegistryCase AddwChip.circuit, AddwChip.elaborated
  · busRegistryCase SubChip.circuit, SubChip.elaborated
  · busRegistryCase SubwChip.circuit, SubwChip.elaborated
  · busRegistryCase BitwiseChip.circuit, BitwiseChip.elaborated
  · busRegistryCase LtChip.circuit, LtChip.elaborated
  · busRegistryCase ShiftLeftChip.circuit, ShiftLeftChip.elaborated
  · busRegistryCase ShiftRightChip.circuit, ShiftRightChip.elaborated
  · busRegistryCase JalChip.circuit, JalChip.elaborated
  · busRegistryCase JalrChip.circuit, JalrChip.elaborated
  · busRegistryCase BranchChip.circuit, BranchChip.elaborated
  · busRegistryCase UTypeChip.circuit, UTypeChip.elaborated
  · busRegistryCase LoadByteChip.circuit, LoadByteChip.elaborated
  · busRegistryCase LoadHalfChip.circuit, LoadHalfChip.elaborated
  · busRegistryCase LoadWordChip.circuit, LoadWordChip.elaborated
  · busRegistryCase LoadDoubleChip.circuit, LoadDoubleChip.elaborated
  · busRegistryCase LoadX0Chip.circuit, LoadX0Chip.elaborated
  · busRegistryCase StoreByteChip.circuit, StoreByteChip.elaborated
  · busRegistryCase StoreHalfChip.circuit, StoreHalfChip.elaborated
  · busRegistryCase StoreWordChip.circuit, StoreWordChip.elaborated
  · busRegistryCase StoreDoubleChip.circuit, StoreDoubleChip.elaborated
  · busRegistryCase MulChip.circuit, MulChip.elaborated
  · busRegistryCase DivRemChip.circuit, DivRemChip.elaborated
  · busRegistryCase AluX0Chip.circuit, AluX0Chip.elaborated

/-- The operation list of every canonical decoded row therefore uses only the four supported buses. -/
theorem DecodedInstructionRow.usesSupportedBusChannels_of_mem
    (decoded : DecodedInstructionRow p) (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables) :
    UsesSupportedBusChannels decoded := by
  have declared := supportedChip_usesSupportedBusChannels decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem)
  intro channel channelMem
  apply declared
  apply decoded.chip.table.circuit.channels_subset
  simpa only [Operations.channels, Component.interactions_eq, Component.rowOperations] using
    channelMem

/-- Four per-channel guarantees assemble into Clean's `FullGuarantees` once the actual operation list
is known to use only those channels. -/
theorem DecodedRowChannelGuarantees.full
    {decoded : DecodedInstructionRow p} {data : ProverData (ZMod p)}
    (guarantees : DecodedRowChannelGuarantees decoded data)
    (channels : UsesSupportedBusChannels decoded) :
    decoded.chip.table.operations.FullGuarantees (decoded.environment data) := by
  intro interaction interactionMem
  have channelMem : interaction.channel ∈ decoded.chip.table.operations.channels :=
    List.mem_map_of_mem interactionMem
  have supported := channels channelMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with state | byte | program | memory
  · exact guarantees.state interaction interactionMem state
  · exact guarantees.byte interaction interactionMem byte
  · exact guarantees.program interaction interactionMem program
  · exact guarantees.memory interaction interactionMem memory

omit [Fact (2 ^ 24 < p)] in
/-- A raw channel identified with the structural State channel has a vacuous guarantee.  Isolating
the dependent equality here avoids casting each interaction's arity-indexed message by hand. -/
theorem rawChannel_guarantees_of_eq_state (channel : RawChannel (ZMod p))
    (channelEq : channel = stateChannel.toRaw) (mult : ZMod p)
    (message : Vector (ZMod p) channel.arity) (data : ProverData (ZMod p)) :
    channel.Guarantees mult message data := by
  subst channel
  simp [stateChannel, Channel.toRaw]

/-- The current structural State channel therefore needs no input from global grounding. -/
theorem decodedRow_stateChannelGuarantees (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    decoded.chip.table.operations.ChannelGuarantees stateChannel.toRaw
      (decoded.environment data) := by
  intro interaction _ channelEq _
  exact rawChannel_guarantees_of_eq_state interaction.channel channelEq
    (Expression.eval (decoded.environment data) interaction.mult)
    (Vector.map (Expression.eval (decoded.environment data)) interaction.msg)
    (decoded.environment data).data

/-- Byte and Program are the finished part of a decoded row's guarantee bundle.  Both facts come
from the exact aligned table and Clean's provider/balance theorem. -/
theorem witness_decodedRow_finishedChannelGuarantees
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables) :
    decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
        (decoded.environment witness.data) ∧
      decoded.chip.table.operations.ChannelGuarantees programChannel.toRaw
        (decoded.environment witness.data) := by
  have finished := sp1_finishedChannel_guarantees witness constraints balanced
  constructor
  · apply channelGuarantees_of_mem_decodeInstructionTables witness.data byteChannel.toRaw
      (witness_instructionTables_aligned witness)
    · intro table tableMem
      exact (finished table
        (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take tableMem))).1
    · exact decodedMem
  · apply channelGuarantees_of_mem_decodeInstructionTables witness.data programChannel.toRaw
      (witness_instructionTables_aligned witness)
    · intro table tableMem
      exact (finished table
        (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take tableMem))).2
    · exact decodedMem

/-- An active decoded row inherits the structural well-formedness of its exact Program fetch.
This is deliberately separate from committed-ROM membership: the finished Program channel supplies
the limb/index bounds, while `decodedInROM` supplies instruction semantics. -/
theorem decodedInstructionRow_programRowSpec
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (real : (decoded.toChipRow witness.data).is_real = 1) :
    ProgramMsg.RowSpec (programMessageOfView (decoded.toChipRow witness.data).view) := by
  have rowConstraints := decodedInstructionRow_constraints witness constraints decoded decodedMem
  have interactions := decoded.programInteractions_eq_of_mem witness.data witness.tables decodedMem
    rowConstraints
  let target := TypedInteraction.pulledIfValue programChannel
    (decoded.toChipRow witness.data).is_real
    (programMessageOfView (decoded.toChipRow witness.data).view)
  have targetMem : target ∈ decoded.interactionsWith witness.data programChannel := by
    rw [interactions]
    exact List.mem_cons_self
  have targetNegative : target.mult = -1 := by
    simp only [target, TypedInteraction.pulledIfValue_mult, real]
  have programGuarantees :=
    (witness_decodedRow_finishedChannelGuarantees witness constraints balanced decoded decodedMem).2
  have guarantee := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations programChannel (decoded.environment witness.data) target targetMem
    programGuarantees (by rfl) targetNegative
  simpa only [target, TypedInteraction.pulledIfValue_message, programChannel] using guarantee

/-- The exact hypotheses Clean's circuit theorem consumes for one decoded physical row.  In the
capstone these are assembled dynamically: Memory truth supplies the remaining guarantees and helps
discharge the chip-specific assumptions at the row's execution position. -/
structure DecodedRowSoundnessInputs (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : Prop where
  assumptions : decoded.chip.table.Assumptions (decoded.environment data)
  guarantees : decoded.chip.table.operations.FullGuarantees (decoded.environment data)

/-- What remains open after the finished Byte/Program theorem and the vacuous State channel.  This is
the precise dynamic contract the timed Memory/readiness layer must establish per execution row. -/
structure DecodedRowOpenSoundnessInputs (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : Prop where
  assumptions : decoded.chip.table.Assumptions (decoded.environment data)
  memory : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
    (decoded.environment data)

/-- The complete position-dependent input expected from the timed semantic layer.  Circuit
assumptions and Memory guarantees are exactly what remains before Clean's weak soundness theorem;
operand currency and `advanceReady` are the independent premises consumed by the Sail bridge. -/
structure DecodedRowDynamicInputs (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (program : Target.GuestProgram) (state : SailState) : Prop where
  circuit : DecodedRowOpenSoundnessInputs decoded data
  ready : (decoded.toChipRow data).kind.advanceReady
    (decoded.toChipRow data).inputs (decoded.toChipRow data).cols program state
  operands : Target.ValueOperandsBound (decoded.toChipRow data).view state

/-- Timed grounding supplies the open Memory half of circuit soundness. The only remaining circuit
premise is the chip's explicit semantic `Assumptions`, kept separate because it also contains decode,
address-validity, and immediate facts that do not all come from Memory currency. -/
theorem DecodedInstructionRow.openSoundnessInputs_of_grounded
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (program : Target.GuestProgram) (initial : SailState) (initialClock : ℕ)
    (assumptions : decoded.chip.table.Assumptions (decoded.environment data))
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts data)) :
    DecodedRowOpenSoundnessInputs decoded data :=
  { assumptions
    memory := decoded.memoryChannelGuarantees_of_grounded data program initial initialClock grounded }

/-- Package the exact position-dependent contract consumed by the physical-row soundness bridge.
This keeps the three independent sources visible: timed grounding for Memory, static/decode facts for
the chip assumptions and readiness bundle, and the live-state operand relation. -/
theorem DecodedInstructionRow.dynamicInputs_of_grounded
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (program : Target.GuestProgram) (initial state : SailState) (initialClock : ℕ)
    (assumptions : decoded.chip.table.Assumptions (decoded.environment data))
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts data))
    (ready : (decoded.toChipRow data).kind.advanceReady
      (decoded.toChipRow data).inputs (decoded.toChipRow data).cols program state)
    (operands : Target.ValueOperandsBound (decoded.toChipRow data).view state) :
    DecodedRowDynamicInputs decoded data program state :=
  { circuit := decoded.openSoundnessInputs_of_grounded data program initial initialClock assumptions
      grounded
    ready
    operands }

/-- The canonical physical-row-to-semantic-row bridge.  No operation-level faithfulness theorem is
involved: this is precisely the `GeneralFormalCircuit` soundness field retained by `SupportedChip`. -/
theorem DecodedInstructionRow.chipSpec_of_weakSoundness
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (inputs : DecodedRowSoundnessInputs decoded data) :
    (decoded.toChipRow data).chipSpec data := by
  change (decoded.chip.decodeRow data decoded.physical).chipSpec data
  rw [SupportedChip.decodeRow_chipSpec_iff]
  exact (Component.weakSoundness inputs.assumptions constraints inputs.guarantees).1

/-- Witness-level specialization: once the timed layer proves the chip assumptions and Memory
guarantees for this row, its semantic `chipSpec` follows.  Constraints, bus coverage, State, Byte, and
Program are all discharged here from the canonical witness and registry. -/
theorem DecodedInstructionRow.chipSpec_of_openSoundnessInputs
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (openInputs : DecodedRowOpenSoundnessInputs decoded witness.data) :
    (decoded.toChipRow witness.data).chipSpec witness.data := by
  have finished := witness_decodedRow_finishedChannelGuarantees witness constraints balanced
    decoded decodedMem
  apply decoded.chipSpec_of_weakSoundness witness.data
    (decodedInstructionRow_constraints witness constraints decoded decodedMem)
  refine { assumptions := openInputs.assumptions, guarantees := ?_ }
  apply (DecodedRowChannelGuarantees.mk
    (decodedRow_stateChannelGuarantees decoded witness.data)
    finished.1 finished.2 openInputs.memory).full
  exact decoded.usesSupportedBusChannels_of_mem witness.tables decodedMem

/-- Assemble the semantic row consumed by local execution.  This theorem makes the dependency
direction explicit: the timed layer never assumes `chipSpec`; it supplies the open circuit inputs,
and the retained chip's own `GeneralFormalCircuit.weakSoundness` derives the spec. -/
theorem DecodedInstructionRow.dynamicGrounded_of_inputs
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (program : Target.GuestProgram) (state : SailState)
    (inputs : DecodedRowDynamicInputs decoded witness.data program state) :
    DynamicGroundedRow witness.data program (decoded.toChipRow witness.data) state :=
  { spec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem
      inputs.circuit
    ready := inputs.ready
    operands := inputs.operands }

/-- Capstone-facing specialization: once the global engine grounds this row's exact typed Memory
records, the remaining position facts feed the chip circuit and Sail bridge through one proved path. -/
theorem DecodedInstructionRow.dynamicGrounded_of_grounded
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (program : Target.GuestProgram) (initial state : SailState) (initialClock : ℕ)
    (assumptions : decoded.chip.table.Assumptions (decoded.environment witness.data))
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts witness.data))
    (ready : (decoded.toChipRow witness.data).kind.advanceReady
      (decoded.toChipRow witness.data).inputs (decoded.toChipRow witness.data).cols program state)
    (operands : Target.ValueOperandsBound (decoded.toChipRow witness.data).view state) :
    DynamicGroundedRow witness.data program (decoded.toChipRow witness.data) state :=
  decoded.dynamicGrounded_of_inputs witness constraints balanced decodedMem program state
    (decoded.dynamicInputs_of_grounded witness.data program initial state initialClock assumptions
      grounded ready operands)

/-- Capstone form with register operands discharged from the chip's exact Memory pulls. The caller
retains only the per-chip interaction-shape theorem, the ordered prefix, and the row's clock position. -/
theorem DecodedInstructionRow.dynamicGrounded_of_timedInputs
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (program : Target.GuestProgram) (initial state : SailState)
    (initialClock steps : ℕ)
    (assumptions : decoded.chip.table.Assumptions (decoded.environment witness.data))
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts witness.data))
    (ready : (decoded.toChipRow witness.data).kind.advanceReady
      (decoded.toChipRow witness.data).inputs (decoded.toChipRow witness.data).cols program state)
    (pulls : decoded.RegisterOperandPulls witness.data)
    (chain : Target.SailChain steps initial state)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (rowTime : Semantics.StateMsg.timeNat
      (statePullMessage (decoded.toChipRow witness.data)) = initialClock + 8 * steps) :
    DynamicGroundedRow witness.data program (decoded.toChipRow witness.data) state := by
  apply decoded.dynamicGrounded_of_grounded witness constraints balanced decodedMem program initial
    state initialClock assumptions grounded ready
  exact decoded.valueOperandsBound_of_grounded witness.data program initial state initialClock steps
    grounded chain real rowTime pulls

end SP1Clean.Soundness
