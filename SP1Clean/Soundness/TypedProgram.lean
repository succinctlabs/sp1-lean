import SP1Clean.Soundness.ProviderBindings
import SP1Clean.Soundness.TypedSelectors

/-! # Typed Program fetches emitted by instruction rows

The Program bus is structural in the Clean circuit: instruction rows pull one decoded fetch and the
preprocessed Program table pushes matching rows.  This module keeps that exact typed interaction and
grounds it against the program committed in `ProverData`; no `LookupAccess` projection is introduced.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The Program message denoted by the chip-agnostic semantic row view. -/
def programMessageOfView (view : Trace.RowView (ZMod p)) : ProgramMsg (ZMod p) :=
  ⟨view.state.pc[0], view.state.pc[1], view.state.pc[2], view.opcode,
    view.adapter.op_a, view.adapter.op_b, view.adapter.op_c, view.adapter.op_a_0,
    view.adapter.imm_b, view.adapter.imm_c⟩

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
@[simp] theorem rowOfMsg_programMessageOfView (view : Trace.RowView (ZMod p)) :
    rowOfMsg (programMessageOfView view) = (programAccess view).toRow := rfl

/-- Exact Program emission for a typed circuit and its semantic row view.  There is one gated pull;
all committed-ROM meaning is established globally from the provider and channel balance. -/
def CircuitProgramEmissionShape {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ data physical,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    let rowView := view (component.rowInput env) (component.rowOutput env)
    component.operations.ConstraintsHold env →
      component.operations.interactionValuesWith programChannel.toRaw env =
        [programChannel.pulledIfValue rowView.is_real (programMessageOfView rowView)]

/-- Descriptor-level Program contract consumed by the deterministic witness decoder.  The physical
row must satisfy its own circuit constraints because some chips derive the public active selector
from an internal one-hot gate before emitting the fetch. -/
def ProgramEmissionShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    let row := chip.decodeRow data physical
    let env := Environment.fromArray physical data
    chip.table.operations.ConstraintsHold env →
      chip.table.operations.interactionValuesWith programChannel.toRaw env =
        [programChannel.pulledIfValue row.is_real (programMessageOfView row.view)]

/-! ## Reader-local fetch interfaces -/

/-- The R-type reader's Program payload, named once for compositional chip proofs. -/
def rTypeProgramMessage (input : Var Readers.RTypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], #v[input.cols.op_c, 0, 0, 0], input.cols.op_a_0, 0, 0⟩

/-- Exact Program interaction of the R-type reader, before it is composed by a chip. -/
theorem rTypeReader_programInteractions (input : Var Readers.RTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.RTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (rTypeProgramMessage input)).toRaw] := by
  simp only [Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append,
    rTypeProgramMessage]

omit [Fact (2 ^ 24 < p)] in
/-- Turn an exact reader-main interaction into the compositional subcircuit form used by chips. -/
theorem programInteractions_subcircuit_of_main {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ) (ops : Operations (ZMod p))
    (interaction : ChannelInteraction programChannel)
    (exact : ((circuit.main input).operations offset).interactionsWith programChannel.toRaw =
      [interaction.toRaw]) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interaction.toRaw ::
        Operations.interactionsWith programChannel.toRaw ops := by
  rw [Operations.interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change Operations.interactionsWith programChannel.toRaw ((circuit.main input).operations offset) ++
      Operations.interactionsWith programChannel.toRaw ops = _
  rw [exact]
  rfl

/-- Compositional R-type form: retain the reader's fetch and append the surrounding operations. -/
theorem rTypeReader_programInteractions_subcircuit
    (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.RTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (rTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  programInteractions_subcircuit_of_main Readers.RTypeReader.circuit input offset ops _
    (rTypeReader_programInteractions input offset)

/-- The immediate-capable ALU reader's Program payload. -/
def aluTypeProgramMessage (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c, input.cols.op_a_0, 0, input.cols.imm_c⟩

theorem aluTypeReader_programInteractions (input : Var Readers.ALUTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.ALUTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (aluTypeProgramMessage input)).toRaw] := by
  simp only [Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, aluTypeProgramMessage]

theorem aluTypeReader_programInteractions_subcircuit
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ALUTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (aluTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  programInteractions_subcircuit_of_main Readers.ALUTypeReader.circuit input offset ops _
    (aluTypeReader_programInteractions input offset)

/-- The immutable ALU reader emits the same fetch shape as its mutable sibling. -/
def aluTypeImmutableProgramMessage
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c, input.cols.op_a_0, 0, input.cols.imm_c⟩

theorem aluTypeReaderImmutable_programInteractions
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ALUTypeReaderImmutable.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted
        (aluTypeImmutableProgramMessage input)).toRaw] := by
  simp only [Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, aluTypeImmutableProgramMessage]

theorem aluTypeReaderImmutable_programInteractions_subcircuit
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ALUTypeReaderImmutable.circuit (p := p)).toSubcircuit offset input) ::
          ops) =
      (programChannel.pulledIf input.is_trusted
        (aluTypeImmutableProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  programInteractions_subcircuit_of_main Readers.ALUTypeReaderImmutable.circuit input offset ops _
    (aluTypeReaderImmutable_programInteractions input offset)

/-- I-type reader payload: scalar `rs1`, immediate `op_c`, and `imm_c = 1`. -/
def iTypeProgramMessage (input : Var Readers.ITypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c_imm, input.cols.op_a_0, 0, 1⟩

theorem iTypeReader_programInteractions (input : Var Readers.ITypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.ITypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (iTypeProgramMessage input)).toRaw] := by
  simp only [Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, iTypeProgramMessage]

theorem iTypeReader_programInteractions_subcircuit
    (input : Var Readers.ITypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ITypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (iTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  programInteractions_subcircuit_of_main Readers.ITypeReader.circuit input offset ops _
    (iTypeReader_programInteractions input offset)

/-- Immutable I-type reader payload. -/
def iTypeImmutableProgramMessage (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c_imm, input.cols.op_a_0, 0, 1⟩

theorem iTypeReaderImmutable_programInteractions
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted
        (iTypeImmutableProgramMessage input)).toRaw] := by
  simp only [Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, iTypeImmutableProgramMessage]

theorem iTypeReaderImmutable_programInteractions_subcircuit
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit offset input) ::
          ops) =
      (programChannel.pulledIf input.is_trusted
        (iTypeImmutableProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  programInteractions_subcircuit_of_main Readers.ITypeReaderImmutable.circuit input offset ops _
    (iTypeReaderImmutable_programInteractions input offset)

/-- J-type reader payload: both operand words are immediates. -/
def jTypeProgramMessage (input : Var Readers.JTypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    input.cols.op_b_imm, input.cols.op_c_imm, input.cols.op_a_0, 1, 1⟩

theorem jTypeReader_programInteractions (input : Var Readers.JTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.JTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (jTypeProgramMessage input)).toRaw] := by
  simp only [Readers.JTypeReader.circuit, Readers.JTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, jTypeProgramMessage]

theorem jTypeReader_programInteractions_subcircuit
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.JTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (jTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  programInteractions_subcircuit_of_main Readers.JTypeReader.circuit input offset ops _
    (jTypeReader_programInteractions input offset)

/-! ## Compositional interaction projection

Large chips should not have to normalize their entire monadic circuit merely to identify one bus
interaction.  `circuitInteractionsWith` projects a circuit onto one raw channel and the lemmas below
reduce that projection one bind or primitive at a time.  Arithmetic gadgets therefore remain opaque;
only their declared channel interfaces matter. -/

noncomputable def circuitInteractionsWith {F α} [FiniteField F]
    (channel : RawChannel F) (circuit : Circuit F α) (offset : ℕ) :
    List (AbstractInteraction F) :=
  circuit.operations offset |>.interactionsWith channel

theorem circuitInteractionsWith_bind {F α β} [FiniteField F]
    (channel : RawChannel F) (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ) :
    circuitInteractionsWith channel (left >>= right) offset =
      circuitInteractionsWith channel left offset ++
        circuitInteractionsWith channel (right (left.output offset))
          (offset + left.localLength offset) := by
  change Operations.interactionsWith channel
      ((left offset).2 ++ (right (left offset).1
        (offset + Operations.localLength (left offset).2)).2) = _
  rw [Operations.interactionsWith_append]
  rfl

theorem witnessVectorNative_localLength {F} [FiniteField F] (length : ℕ)
    (compute : ProverEnvironment F → Vector F length) (offset : ℕ) :
    (witnessVectorNative length compute).localLength offset = length := by
  simp only [circuit_norm]

theorem witnessNative_localLength {F value var} [FiniteField F] [ProvableType value]
    [inst : Witnessable F value var] (compute : ProverEnvironment F → value F) (offset : ℕ) :
    (witnessNative (var := var) compute).localLength offset = size value := by
  simp only [witnessNative]
  rw [inst.witnessIR_def, Circuit.localLength, eqRec_eq_cast,
    cast_apply (by rw [inst.var_eq]), snd_cast (by rw [inst.var_eq])]
  rfl

theorem assertion_localLength {F Input} [FiniteField F] [ProvableType Input]
    (circuit : FormalAssertion F Input) (input : Var Input F) (offset : ℕ) :
    (assertion circuit input).localLength offset = circuit.localLength input := by
  simp only [circuit_norm]

theorem generalAssertion_localLength {F Input Output} [FiniteField F]
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    (subcircuitWithAssertion circuit input).localLength offset = circuit.localLength input := by
  simp only [circuit_norm]

theorem pullIf_localLength {F Message} [FiniteField F] [ProvableType Message]
    (channel : Channel F Message) (enabled : Expression F) (message : Message (Expression F))
    (offset : ℕ) :
    (channel.pullIf enabled message).localLength offset = 0 := by
  simp only [circuit_norm]

theorem circuitInteractionsWith_witnessVectorNative {F} [FiniteField F]
    (channel : RawChannel F) (length : ℕ)
    (compute : ProverEnvironment F → Vector F length) (offset : ℕ) :
    circuitInteractionsWith channel (witnessVectorNative length compute) offset = [] := by
  simp [circuitInteractionsWith, circuit_norm]

theorem circuitInteractionsWith_witnessNative {F value var} [FiniteField F]
    [ProvableType value] [inst : Witnessable F value var]
    (channel : RawChannel F) (compute : ProverEnvironment F → value F) (offset : ℕ) :
    circuitInteractionsWith channel (witnessNative (var := var) compute) offset = [] := by
  simp only [circuitInteractionsWith, witnessNative]
  rw [inst.witnessIR_def, Circuit.operations, eqRec_eq_cast,
    cast_apply (by rw [inst.var_eq]), snd_cast (by rw [inst.var_eq])]
  rfl

theorem circuitInteractionsWith_assertion_eq_nil {F Input} [FiniteField F]
    [ProvableType Input] (channel : RawChannel F) (circuit : FormalAssertion F Input)
    (input : Var Input F) (offset : ℕ)
    (hg : channel ∉ circuit.channelsWithGuarantees)
    (hr : channel ∉ circuit.channelsWithRequirements) :
    circuitInteractionsWith channel (assertion circuit input) offset = [] := by
  simpa only [circuitInteractionsWith, assertion, Circuit.operations,
    Operations.interactionsWith_nil] using
    (InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      circuit channel input ([] : Operations F) hg hr)

theorem circuitInteractionsWith_generalAssertion_eq_nil {F Input Output} [FiniteField F]
    [ProvableType Input] [ProvableType Output]
    (channel : RawChannel F) (circuit : GeneralFormalCircuit F Input Output)
    (input : Var Input F) (offset : ℕ)
    (hg : channel ∉ circuit.channelsWithGuarantees)
    (hr : channel ∉ circuit.channelsWithRequirements) :
    circuitInteractionsWith channel (subcircuitWithAssertion circuit input) offset = [] := by
  simpa only [circuitInteractionsWith, subcircuitWithAssertion, Circuit.operations,
    Operations.interactionsWith_nil] using
    (InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil
      circuit channel input ([] : Operations F) hg hr)

theorem circuitInteractionsWith_rTypeReader
    (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ) :
    circuitInteractionsWith programChannel.toRaw
        (subcircuitWithAssertion Readers.RTypeReader.circuit input) offset =
      [(programChannel.pulledIf input.is_trusted (rTypeProgramMessage input)).toRaw] := by
  simpa only [circuitInteractionsWith, subcircuitWithAssertion, Circuit.operations,
    Operations.interactionsWith_nil] using
    (rTypeReader_programInteractions_subcircuit input offset ([] : Operations (ZMod p)))

omit [Fact (2 ^ 24 < p)] in
theorem circuitInteractionsWith_assertEq
    (left right : Expression (ZMod p)) (offset : ℕ) :
    circuitInteractionsWith programChannel.toRaw (left === right) offset = [] := by
  simp only [circuitInteractionsWith, HasAssertEq.assert_eq, Expression.assertEquals,
    assertion, Circuit.operations]
  simp only [Operations.interactionsWith_subcircuit,
    FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
    List.filter_nil, List.nil_append]

omit [Fact (2 ^ 24 < p)] in
theorem assertEq_localLength (left right : Expression (ZMod p)) (offset : ℕ) :
    (left === right).localLength offset = 0 := by
  simp only [circuit_norm]

theorem circuitInteractionsWith_assertZeros (channel : RawChannel (ZMod p))
    (expressions : List (Expression (ZMod p))) (offset : ℕ) :
    circuitInteractionsWith channel (DivRemChip.assertZeros expressions) offset = [] := by
  change Operations.interactionsWith channel
    (expressions.map fun expression => Operation.assert expression) = []
  exact DivRemChip.interactionsWith_map_assert channel expressions

theorem assertZeros_localLength (expressions : List (Expression (ZMod p))) (offset : ℕ) :
    (DivRemChip.assertZeros expressions).localLength offset = 0 := by
  change Operations.localLength
    (expressions.map fun expression => Operation.assert expression) = 0
  exact DivRemChip.localLength_map_assert expressions

omit [Fact (2 ^ 24 < p)] in
theorem circuitInteractionsWith_bytePullIf (enabled : Expression (ZMod p))
    (message : ByteRow (Expression (ZMod p))) (offset : ℕ) :
    circuitInteractionsWith programChannel.toRaw (byteChannel.pullIf enabled message) offset = [] := by
  simp [circuitInteractionsWith, circuit_norm,
    Channels.byteChannel_eq_programChannel_false]

theorem circuitInteractionsWith_pure {F α} [FiniteField F]
    (channel : RawChannel F) (value : α) (offset : ℕ) :
    circuitInteractionsWith channel (pure value) offset = [] := by
  rfl

/-- Small syntactic interface identifying the circuit's unique Program pull and its semantic row
projection.  Concrete chip proofs normalize only abstract operations; evaluation is handled once by
`circuitProgramEmissionShape_of_contract`. -/
def CircuitProgramInteractionContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  ∃ (gate : Var Input (ZMod p) → ℕ → Expression (ZMod p))
      (message : Var Input (ZMod p) → ℕ → ProgramMsg (Expression (ZMod p))),
    (∀ input offset,
      ((circuit.main input).operations offset).interactionsWith programChannel.toRaw =
        [(programChannel.pulledIf (gate input offset) (message input offset)).toRaw]) ∧
    (∀ env : Environment (ZMod p),
      ((⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold env) →
        Eval.eval env (gate inputVar offset) =
          (view (Eval.eval env inputVar)
            (Eval.eval env (circuit.output inputVar offset))).is_real) ∧
    (∀ env : Environment (ZMod p), Eval.eval env (message inputVar offset) =
      programMessageOfView (view (Eval.eval env inputVar)
        (Eval.eval env (circuit.output inputVar offset))))

omit [Fact (2 ^ 24 < p)] in
/-- Evaluate a chip-local abstract Program contract into the exact typed physical-row emission. -/
theorem circuitProgramEmissionShape_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitProgramInteractionContract circuit view) :
    CircuitProgramEmissionShape circuit view := by
  obtain ⟨gate, message, interactions, gate_eval, message_eval⟩ := contract
  intro data physical
  dsimp only
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  intro constraints
  change component.operations.interactionValuesWith programChannel.toRaw env =
    [programChannel.pulledIfValue rowView.is_real (programMessageOfView rowView)]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((circuit.main inputVar).operations offset).interactionsWith programChannel.toRaw) = _
  rw [interactions inputVar offset]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf]
  rw [gate_eval env constraints, message_eval env]
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  rw [inputEq, outputEq]

/-- Transport a circuit-local Program theorem to its retained supported-chip descriptor without
normalizing the dependent descriptor. -/
theorem programEmissionShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (shape : @CircuitProgramEmissionShape p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    ProgramEmissionShape ⟨kind, circuit, spec_eq, opcodes, rdGuard⟩ := by
  exact shape

/-- Lift a descriptor's Program contract to the typed interaction decoder. -/
theorem DecodedInstructionRow.programInteractions_eq
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (contract : ProgramEmissionShape decoded.chip) :
    decoded.interactionsWith data programChannel =
      [TypedInteraction.pulledIfValue programChannel (decoded.toChipRow data).is_real
        (programMessageOfView (decoded.toChipRow data).view)] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow] using
    contract data decoded.physical constraints

omit [Fact (2 ^ 24 < p)] in
/-- Constraint satisfaction distributes over the operation append generated by circuit `bind`.
Keeping this fact at the `Operations` boundary lets local bridge proofs select one binding assertion
without normalizing every unrelated arithmetic subcircuit. -/
theorem operationsConstraintsHold_append (env : Environment (ZMod p))
    (left right : Operations (ZMod p)) :
    (left ++ right).ConstraintsHold env ↔
      left.ConstraintsHold env ∧ right.ConstraintsHold env := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.forall_mem_append]
  tauto

omit [Fact (2 ^ 24 < p)] in
theorem operationsConstraintsHold_assert_singleton (env : Environment (ZMod p))
    (expression : Expression (ZMod p)) :
    Operations.ConstraintsHold env [.assert expression] ↔ env expression = 0 := by
  simp [Operations.ConstraintsHold, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
theorem operationsConstraintsHold_witness_singleton (env : Environment (ZMod p))
    (length : ℕ) (generator : WitgenIR (ZMod p) length) :
    Operations.ConstraintsHold env [.witness length generator] := by
  simp [Operations.ConstraintsHold, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
theorem equality_of_operationsConstraintsHold_singleton (env : Environment (ZMod p))
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

set_option maxHeartbeats 4000000 in
theorem AddChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AddChip.circuit (p := p)) AddChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
  ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 0,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  · intro input offset
    simp only [AddChip.circuit, AddChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      rTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      SP1Clean.AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, rTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
  · intro env
    simp [AddChip.circuit, AddChip.rowView, circuit_norm]
  · intro env
    simp [AddChip.circuit, AddChip.rowView, Extracted.RTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem AddiChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AddiChip.circuit (p := p)) AddiChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 1,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [AddiChip.circuit, AddiChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      iTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      SP1Clean.AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, List.append_nil, iTypeProgramMessage]
  · intro env
    simp [AddiChip.circuit, AddiChip.rowView, circuit_norm]
  · intro env
    simp [AddiChip.circuit, AddiChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem AddwChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AddwChip.circuit (p := p)) AddwChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 19,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [AddwChip.circuit, AddwChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      aluTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      AddwOperation.circuit, AddwOperation.elaborated,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, List.append_nil, aluTypeProgramMessage]
  · intro env
    simp [AddwChip.circuit, AddwChip.rowView, circuit_norm]
  · intro env
    simp [AddwChip.circuit, AddwChip.rowView, Extracted.ALUTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem SubChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (SubChip.circuit (p := p)) SubChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 2,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  · intro input offset
    simp only [SubChip.circuit, SubChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      rTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      SubOperation.circuit, SubOperation.elaborated,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, rTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
  · intro env
    simp [SubChip.circuit, SubChip.rowView, circuit_norm]
  · intro env
    simp [SubChip.circuit, SubChip.rowView, Extracted.RTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem SubwChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (SubwChip.circuit (p := p)) SubwChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 20,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  · intro input offset
    simp only [SubwChip.circuit, SubwChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      rTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      SubwOperation.circuit, SubwOperation.elaborated,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, List.append_nil, rTypeProgramMessage]
  · intro env
    simp [SubwChip.circuit, SubwChip.rowView, circuit_norm]
  · intro env
    simp [SubwChip.circuit, SubwChip.rowView, Extracted.RTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 8000000 in
theorem BitwiseChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (BitwiseChip.circuit (p := p)) BitwiseChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input offset =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      var { index := offset } * 3 + var { index := offset + 1 } * 4 +
        var { index := offset + 2 } * 5,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [BitwiseChip.circuit, BitwiseChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, witnessNative, subcircuitWithAssertion, assertion,
      assertZero, HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      aluTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      BitwiseU16Operation.circuit, BitwiseU16Operation.elaborated,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, List.append_nil, aluTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
  · intro env
    simp [BitwiseChip.circuit, BitwiseChip.rowView, circuit_norm]
  · intro env
    simp [BitwiseChip.circuit, BitwiseChip.rowView, Extracted.ALUTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 8000000 in
theorem LtChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LtChip.circuit (p := p)) LtChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input offset =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      var { index := offset } * 9 + var { index := offset + 1 } * 10,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [LtChip.circuit, LtChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, witnessNative, subcircuitWithAssertion, assertion,
      assertZero, HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      aluTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      LtOperationSigned.circuit, LtOperationSigned.elaborated,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, List.append_nil, aluTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
  · intro env
    simp [LtChip.circuit, LtChip.rowView, circuit_norm]
  · intro env
    simp [LtChip.circuit, LtChip.rowView, Extracted.ALUTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem LoadDoubleChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadDoubleChip.circuit (p := p))
      LoadDoubleChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 35,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [LoadDoubleChip.circuit, LoadDoubleChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReader.circuit, Readers.ITypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [LoadDoubleChip.rowView, circuit_norm]
  · intro env
    simp [LoadDoubleChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem LoadByteChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadByteChip.circuit (p := p))
      LoadByteChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_lb + input.is_lbu, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_lb * 29 + input.is_lbu * 32, input.adapter.op_a,
      #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [LoadByteChip.circuit, LoadByteChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReader.circuit, Readers.ITypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [LoadByteChip.rowView, LoadByteChip.isReal, circuit_norm]
  · intro env
    simp [LoadByteChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem LoadHalfChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadHalfChip.circuit (p := p))
      LoadHalfChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_lh + input.is_lhu, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_lh * 30 + input.is_lhu * 33, input.adapter.op_a,
      #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [LoadHalfChip.circuit, LoadHalfChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      U16MSBOperation.circuit, U16MSBOperation.main,
      Readers.ITypeReader.circuit, Readers.ITypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [LoadHalfChip.rowView, LoadHalfChip.isReal, circuit_norm]
  · intro env
    simp [LoadHalfChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem LoadWordChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadWordChip.circuit (p := p))
      LoadWordChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_lw + input.is_lwu, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_lw * 31 + input.is_lwu * 34, input.adapter.op_a,
      #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [LoadWordChip.circuit, LoadWordChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      U16MSBOperation.circuit, U16MSBOperation.main,
      Readers.ITypeReader.circuit, Readers.ITypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [LoadWordChip.rowView, LoadWordChip.isReal, circuit_norm]
  · intro env
    simp [LoadWordChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem LoadX0Chip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadX0Chip.circuit (p := p))
      LoadX0Chip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
      input.is_lw + input.is_lwu + input.is_ld,
    fun input _ =>
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
        29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh + 33 * input.is_lhu +
          31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld,
        input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
        input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [LoadX0Chip.circuit, LoadX0Chip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [LoadX0Chip.rowView, LoadX0Chip.isReal, circuit_norm]
  · intro env
    simp [LoadX0Chip.rowView, LoadX0Chip.opcodeVal,
      Extracted.ITypeReader.toAdapterView, programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem StoreByteChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreByteChip.circuit (p := p))
      StoreByteChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 36,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [StoreByteChip.circuit, StoreByteChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [StoreByteChip.rowView, circuit_norm]
  · intro env
    simp [StoreByteChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem StoreHalfChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreHalfChip.circuit (p := p))
      StoreHalfChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 37,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [StoreHalfChip.circuit, StoreHalfChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [StoreHalfChip.rowView, circuit_norm]
  · intro env
    simp [StoreHalfChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem StoreWordChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreWordChip.circuit (p := p))
      StoreWordChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 38,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [StoreWordChip.circuit, StoreWordChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [StoreWordChip.rowView, circuit_norm]
  · intro env
    simp [StoreWordChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem StoreDoubleChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreDoubleChip.circuit (p := p))
      StoreDoubleChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 39,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [StoreDoubleChip.circuit, StoreDoubleChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      AddressOperation.circuit, AddressOperation.main,
      AddrAddOperation.circuit, AddrAddOperation.main,
      Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
      Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [StoreDoubleChip.rowView, circuit_norm]
  · intro env
    simp [StoreDoubleChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem AluX0Chip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AluX0Chip.circuit (p := p))
      AluX0Chip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], input.opcode,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [AluX0Chip.circuit, AluX0Chip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      circuit_norm, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions]
    simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
      Channels.byteChannel_eq_programChannel_false,
      Channels.stateChannel_eq_programChannel_false,
      Channels.memoryChannel_eq_programChannel_false,
      decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append]
  · intro env
    simp [AluX0Chip.circuit, AluX0Chip.rowView, circuit_norm]
  · intro env
    simp [AluX0Chip.circuit, AluX0Chip.rowView,
      Extracted.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem UTypeChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (UTypeChip.circuit (p := p)) UTypeChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_auipc * 48 + (1 - input.is_auipc) * 49,
      input.adapter.op_a, input.adapter.op_b_imm, input.adapter.op_c_imm,
      input.adapter.op_a_0, 1, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [UTypeChip.circuit, UTypeChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      jTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, jTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
  · intro env
    simp [UTypeChip.circuit, UTypeChip.rowView, circuit_norm]
  · intro env
    simp [UTypeChip.circuit, UTypeChip.rowView, Extracted.JTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem JalChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (JalChip.circuit (p := p)) JalChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 46,
      input.adapter.op_a, input.adapter.op_b_imm, input.adapter.op_c_imm,
      input.adapter.op_a_0, 1, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [JalChip.circuit, JalChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      jTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_interact, Operations.interactionsWith_nil,
      List.nil_append, jTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false]
  · intro env
    simp [JalChip.circuit, JalChip.rowView, circuit_norm]
  · intro env
    simp [JalChip.circuit, JalChip.rowView, Extracted.JTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem JalrChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (JalrChip.circuit (p := p)) JalrChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 47,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [JalrChip.circuit, JalrChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, witnessNative, subcircuitWithAssertion, assertion,
      assertZero, HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf,
      Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      iTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_interact, Operations.interactionsWith_nil,
      List.nil_append, iTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false]
  · intro env
    simp [JalrChip.circuit, JalrChip.rowView, circuit_norm]
  · intro env
    simp [JalrChip.circuit, JalrChip.rowView, Extracted.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 8000000 in
theorem BranchChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (BranchChip.circuit (p := p)) BranchChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input offset =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      var { index := offset } * 40 + var { index := offset + 1 } * 41 +
        var { index := offset + 2 } * 42 + var { index := offset + 3 } * 43 +
        var { index := offset + 4 } * 44 + var { index := offset + 5 } * 45,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [BranchChip.circuit, BranchChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      iTypeReaderImmutable_programInteractions_subcircuit,
      LtOperationSigned.circuit, LtOperationSigned.channelsWithGuarantees_eq,
      AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_interact, Operations.interactionsWith_nil,
      List.nil_append, iTypeImmutableProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false, List.nil_append]
  · intro env
    simp [BranchChip.circuit, BranchChip.rowView, circuit_norm]
  · intro env
    simp [BranchChip.circuit, BranchChip.rowView, BranchChip.branchOpcode,
      Extracted.ITypeReader.toAdapterView, programMessageOfView, circuit_norm]

set_option maxHeartbeats 8000000 in
theorem ShiftLeftChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (ShiftLeftChip.circuit (p := p))
      ShiftLeftChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun _ offset => var { index := offset + 30 } + var { index := offset + 31 },
    fun input offset =>
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
        var { index := offset + 30 } * 6 + var { index := offset + 31 } * 21,
        input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
        input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [ShiftLeftChip.circuit, ShiftLeftChip.main, Circuit.operations,
      Circuit.bind_def, Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion,
      assertion, assertZero, HasAssertEq.assert_eq, Expression.assertEquals,
      Channel.pullIf, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      aluTypeReader_programInteractions_subcircuit,
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
      List.nil_append, aluTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false, List.nil_append]
  · intro env constraints
    let input : Var ShiftLeftChip.Inputs (ZMod p) := varFromOffset ShiftLeftChip.Inputs 0
    let offset := size ShiftLeftChip.Inputs
    have rowConstraints := (Component.constraintsHold_iff env).mp constraints
    change ((ShiftLeftChip.main input).operations offset).ConstraintsHold env at rowConstraints
    simp only [ShiftLeftChip.main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
      HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf,
      Operations.localLength, operationsConstraintsHold_append,
      operationsConstraintsHold_assert_singleton,
      operationsConstraintsHold_witness_singleton] at rowConstraints
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, bindConstraints, _⟩ := rowConstraints
    have bindEq := equality_of_operationsConstraintsHold_singleton env _ _ _ bindConstraints
    have bindZero :
        env input.is_real -
          (env (var { index := offset + 30 }) + env (var { index := offset + 31 })) = 0 := by
      simpa [input, offset, eval_sub, circuit_norm] using bindEq
    have gateEq := sub_eq_zero.mp bindZero
    simpa [input, offset, ShiftLeftChip.circuit, ShiftLeftChip.rowView,
      circuit_norm] using gateEq.symm
  · intro env
    simp [ShiftLeftChip.circuit, ShiftLeftChip.rowView,
      Extracted.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

set_option maxHeartbeats 8000000 in
theorem ShiftRightChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (ShiftRightChip.circuit (p := p))
      ShiftRightChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input offset =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      var { index := offset + 32 } * 7 + var { index := offset + 33 } * 8 +
        var { index := offset + 34 } * 22 + var { index := offset + 35 } * 23,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp only [ShiftRightChip.circuit, ShiftRightChip.main, Circuit.operations,
      Circuit.bind_def, Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion,
      assertion, assertZero, HasAssertEq.assert_eq, Expression.assertEquals,
      Channel.pullIf, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      aluTypeReader_programInteractions_subcircuit,
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
      List.nil_append, aluTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, if_false, List.nil_append]
  · intro env _
    simp [ShiftRightChip.circuit, ShiftRightChip.rowView, circuit_norm]
  · intro env
    simp [ShiftRightChip.circuit, ShiftRightChip.rowView,
      Extracted.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

set_option maxHeartbeats 16000000 in
theorem MulChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (MulChip.circuit (p := p)) MulChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input offset =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      var { index := offset } * 11 + var { index := offset + 1 } * 12 +
        var { index := offset + 2 } * 13 + var { index := offset + 3 } * 14 +
        var { index := offset + 4 } * 24,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  · intro input offset
    simp only [MulChip.circuit, MulChip.main, Circuit.operations, Circuit.bind_def,
      Circuit.pure_def, witnessVectorNative, witnessNative, subcircuitWithAssertion,
      assertion, assertZero, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      rTypeReader_programInteractions_subcircuit,
      Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
      MulOperation.circuit, MulOperation.channelsWithGuarantees_eq,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, Operations.interactionsWith_assert,
      Operations.interactionsWith_nil, List.nil_append, rTypeProgramMessage]
    simp only [Operations.interactionsWith_subcircuit,
      FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
      List.filter_nil, List.nil_append]
  · intro env _
    simp [MulChip.circuit, MulChip.rowView, circuit_norm]
  · intro env
    simp [MulChip.circuit, MulChip.rowView, Extracted.RTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

set_option maxHeartbeats 4000000 in
theorem DivRemChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (DivRemChip.circuit (p := p))
      DivRemChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, fun input offset =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      var { index := offset + 1 } * 16 + var { index := offset + 3 } * 18 +
        var { index := offset } * 15 + var { index := offset + 2 } * 17 +
        var { index := offset + 4 } * 25 + var { index := offset + 5 } * 27 +
        var { index := offset + 6 } * 26 + var { index := offset + 7 } * 28,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  · intro input offset
    change circuitInteractionsWith programChannel.toRaw (DivRemChip.main input) offset = _
    -- The rewired `main` composes just five subcircuits after the witness stream: CPUState,
    -- RTypeReader (the one Program pull), the two whole-row assertion gadgets (byte-only), and
    -- RegisterWrite (memory-only).
    simp only [DivRemChip.main, circuitInteractionsWith_bind,
      witnessVectorNative_localLength, witnessNative_localLength,
      assertion_localLength, generalAssertion_localLength,
      circuitInteractionsWith_witnessVectorNative,
      circuitInteractionsWith_witnessNative,
      circuitInteractionsWith_rTypeReader,
      circuitInteractionsWith_assertion_eq_nil,
      circuitInteractionsWith_generalAssertion_eq_nil,
      circuitInteractionsWith_pure,
      Readers.RTypeReader.circuit_localLength,
      Readers.CPUState.circuit, Readers.RegisterWrite.circuit,
      Readers.CPUState.channelsWithGuarantees_eq,
      Readers.RegisterWrite.channelsWithGuarantees_eq,
      DivRemCompare.circuit, DivRemCompare.channelsWithGuarantees_eq,
      DivRemCore.circuit, DivRemCore.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false,
      Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false,
      Channels.programChannel_eq_memoryChannel_false,
      not_false_eq_true, add_zero, List.nil_append]
    simp [rTypeProgramMessage, circuit_norm]
  · intro env _
    simp [DivRemChip.circuit, DivRemChip.rowView, circuit_norm]
  · intro env
    simp [DivRemChip.circuit, DivRemChip.rowView, DivRemContract.encodedOpcode,
      Extracted.RTypeReader.toAdapterView, programMessageOfView, circuit_norm]

/-! ## Supported-machine registry -/

/-- Install a descriptor's retained dependent instances and transport its concrete circuit theorem
to the uniform supported-chip contract. -/
local macro "programRegistryCase " kind:term ", " shape:term : tactic =>
  `(tactic| (
    letI := ($kind:term).provableInputs
    letI := ($kind:term).provableCols
    apply programEmissionShape_of_circuit
    exact $shape:term))

set_option maxHeartbeats 8000000 in
/-- Every instruction chip in the stable registry emits exactly one constraint-aligned Program pull
whose payload is its semantic row view. -/
theorem supportedChip_programEmissionShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : ProgramEmissionShape chip := by
  fin_cases chipMem
  · programRegistryCase (AddChip.kind (p := p)), (AddChip.programEmissionShape (p := p))
  · programRegistryCase (AddiChip.kind (p := p)), (AddiChip.programEmissionShape (p := p))
  · programRegistryCase (AddwChip.kind (p := p)), (AddwChip.programEmissionShape (p := p))
  · programRegistryCase (SubChip.kind (p := p)), (SubChip.programEmissionShape (p := p))
  · programRegistryCase (SubwChip.kind (p := p)), (SubwChip.programEmissionShape (p := p))
  · programRegistryCase (BitwiseChip.kind (p := p)),
      (BitwiseChip.programEmissionShape (p := p))
  · programRegistryCase (LtChip.kind (p := p)), (LtChip.programEmissionShape (p := p))
  · programRegistryCase (ShiftLeftChip.kind (p := p)),
      (ShiftLeftChip.programEmissionShape (p := p))
  · programRegistryCase (ShiftRightChip.kind (p := p)),
      (ShiftRightChip.programEmissionShape (p := p))
  · programRegistryCase (JalChip.kind (p := p)), (JalChip.programEmissionShape (p := p))
  · programRegistryCase (JalrChip.kind (p := p)), (JalrChip.programEmissionShape (p := p))
  · programRegistryCase (BranchChip.kind (p := p)), (BranchChip.programEmissionShape (p := p))
  · programRegistryCase (UTypeChip.kind (p := p)), (UTypeChip.programEmissionShape (p := p))
  · programRegistryCase (LoadByteChip.kind (p := p)),
      (LoadByteChip.programEmissionShape (p := p))
  · programRegistryCase (LoadHalfChip.kind (p := p)),
      (LoadHalfChip.programEmissionShape (p := p))
  · programRegistryCase (LoadWordChip.kind (p := p)),
      (LoadWordChip.programEmissionShape (p := p))
  · programRegistryCase (LoadDoubleChip.kind (p := p)),
      (LoadDoubleChip.programEmissionShape (p := p))
  · programRegistryCase (LoadX0Chip.kind (p := p)),
      (LoadX0Chip.programEmissionShape (p := p))
  · programRegistryCase (StoreByteChip.kind (p := p)),
      (StoreByteChip.programEmissionShape (p := p))
  · programRegistryCase (StoreHalfChip.kind (p := p)),
      (StoreHalfChip.programEmissionShape (p := p))
  · programRegistryCase (StoreWordChip.kind (p := p)),
      (StoreWordChip.programEmissionShape (p := p))
  · programRegistryCase (StoreDoubleChip.kind (p := p)),
      (StoreDoubleChip.programEmissionShape (p := p))
  · programRegistryCase (MulChip.kind (p := p)), (MulChip.programEmissionShape (p := p))
  · programRegistryCase (DivRemChip.kind (p := p)),
      (DivRemChip.programEmissionShape (p := p))
  · programRegistryCase (AluX0Chip.kind (p := p)),
      (AluX0Chip.programEmissionShape (p := p))

/-- Every row retained by the canonical decoder inherits the registered Program contract. -/
theorem DecodedInstructionRow.programEmissionShape_of_mem
    (decoded : DecodedInstructionRow p) (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables) :
    ProgramEmissionShape decoded.chip :=
  supportedChip_programEmissionShape decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem)

/-- A constrained canonical row exposes its actual Program interactions as the one semantic fetch. -/
theorem DecodedInstructionRow.programInteractions_eq_of_mem
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    decoded.interactionsWith data programChannel =
      [TypedInteraction.pulledIfValue programChannel (decoded.toChipRow data).is_real
        (programMessageOfView (decoded.toChipRow data).view)] :=
  decoded.programInteractions_eq data constraints
    (decoded.programEmissionShape_of_mem tables decodedMem)

/-! ## Ensemble-level Program grounding -/

/-- The public State-boundary verifier does not participate in the Program channel. -/
theorem witness_verifierProgramInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith witness.verifierTable programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉ [stateChannel.toRaw]
  simp [Channels.programChannel_eq_stateChannel_false]

/-- Every provider-table position except the committed Program provider has no Program-channel
interactions.  This is positional on purpose: it connects the stable witness index used by
`ProgramProviderBound` to the exact Clean ensemble layout. -/
theorem witness_nonProgramProviderTable_programInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (i : ℕ)
    (lower : 25 ≤ i) (upper : i < 36) (witnessBound : i < witness.tables.length)
    (notProgram : i ≠ programProviderIndex) :
    typedTableInteractionsWith witness.tables[i] programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  have ensembleBound : i < (sp1Ensemble (p := p)).tables.length := by
    simp only [sp1Ensemble_tables, List.length_append, sp1Tables_length,
      sp1ProviderTables_length]
    omega
  have componentEq := witness.same_circuits i ensembleBound
  have providerBound : i - 25 < (sp1ProviderTables (p := p)).length := by
    simp only [sp1ProviderTables_length]
    omega
  have componentProviderEq : witness.tables[i].component =
      (sp1ProviderTables (p := p))[i - 25] := by
    rw [← componentEq]
    change (sp1Tables (p := p) ++ sp1ProviderTables (p := p))[i] = _
    rw [List.getElem_append_right (by simpa only [sp1Tables_length] using lower)]
    simp only [sp1Tables_length]
  rw [componentProviderEq]
  interval_cases i
  all_goals first
  | exact (notProgram (by rfl)).elim
  | (change programChannel.toRaw ∉ [byteChannel.toRaw];
     simp [Channels.programChannel_eq_byteChannel_false])
  | (change programChannel.toRaw ∉ [memoryChannel.toRaw];
     simp [Channels.programChannel_eq_memoryChannel_false])

/-- The whole provider suffix's Program interactions are exactly those of the physical table at the
stable Program-provider index.  No semantic property is used here; this is a structural consequence
of the ensemble table order and each component's declared channels. -/
theorem witness_providerProgramInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (table : Table (ZMod p))
    (tableAt : witness.tables[programProviderIndex]? = some table) :
    (witness.tables.drop 25).flatMap
        (typedTableInteractionsWith · programChannel) =
      typedTableInteractionsWith table programChannel := by
  have tablesLength : witness.tables.length = 36 := by
    rw [← witness.same_length]
    rfl
  have tableAt33 := tableAt
  change witness.tables[33]? = some table at tableAt33
  obtain ⟨_, tableEq33⟩ := List.getElem?_eq_some_iff.mp tableAt33
  subst table
  rw [List.drop_eq_getElem_cons (i := 25) (by omega),
    List.drop_eq_getElem_cons (i := 26) (by omega),
    List.drop_eq_getElem_cons (i := 27) (by omega),
    List.drop_eq_getElem_cons (i := 28) (by omega),
    List.drop_eq_getElem_cons (i := 29) (by omega),
    List.drop_eq_getElem_cons (i := 30) (by omega),
    List.drop_eq_getElem_cons (i := 31) (by omega),
    List.drop_eq_getElem_cons (i := 32) (by omega),
    List.drop_eq_getElem_cons (i := 33) (by omega),
    List.drop_eq_getElem_cons (i := 34) (by omega),
    List.drop_eq_getElem_cons (i := 35) (by omega),
    List.drop_eq_nil_of_le (by omega)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [witness_nonProgramProviderTable_programInteractions_eq_nil witness 25 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 26 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 27 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 28 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 29 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 30 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 31 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 32 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 34 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex]),
    witness_nonProgramProviderTable_programInteractions_eq_nil witness 35 (by omega)
      (by omega) (by omega) (by simp [programProviderIndex])]
  simp

/-- The decoded instruction prefix's Program interactions are exactly one semantic gated pull per
physical row. -/
theorem decodedWitnessProgramInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    decodedWitnessInstructionInteractionsWith witness.data witness.tables programChannel =
      (decodedInstructionRows (p := p) witness.tables).flatMap fun decoded =>
        [TypedInteraction.pulledIfValue programChannel
          (decoded.toChipRow witness.data).is_real
          (programMessageOfView (decoded.toChipRow witness.data).view)] := by
  unfold decodedWitnessInstructionInteractionsWith decodedInstructionInteractionsWith
  apply List.flatMap_congr
  intro decoded decodedMem
  exact decoded.programInteractions_eq_of_mem witness.data witness.tables decodedMem
    (decodedInstructionRow_constraints witness constraints decoded decodedMem)

set_option maxHeartbeats 2000000 in
/-- Every decoded Program interaction is a disabled row or an active pull. -/
theorem decodedWitnessProgramInteractions_pullShape
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ interaction ∈
        decodedWitnessInstructionInteractionsWith witness.data witness.tables programChannel,
      interaction.mult = 0 ∨ interaction.mult = -1 := by
  rw [decodedWitnessProgramInteractions_eq witness constraints]
  intro interaction interactionMem
  obtain ⟨decoded, decodedMem, interactionMem⟩ := List.mem_flatMap.mp interactionMem
  simp only [List.mem_singleton] at interactionMem
  subst interaction
  rcases witness_decodedInstructionRows_selectorBinary witness constraints decoded decodedMem with
    disabled | active
  · left
    rw [TypedInteraction.pulledIfValue_mult, disabled, neg_zero]
  · right
    rw [TypedInteraction.pulledIfValue_mult, active]

set_option maxHeartbeats 2000000 in
/-- Every active deterministically decoded instruction fetch is a genuine decode of the guest
program committed in `ProverData`.  This is the Program-channel grounding theorem: row constraints
identify the exact pull, Clean balance finds a matching nonzero provider contribution, and the
boundary binding supplies committed-ROM truth for that contribution. -/
theorem DecodedInstructionRow.programTruth_of_active
    (decoded : DecodedInstructionRow p)
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providerBound : ProgramProviderBound witness)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (active : (decoded.toChipRow witness.data).is_real = 1) :
    ProgTruth (programMessageOfView (decoded.toChipRow witness.data).view) witness.data := by
  let consumers :=
    decodedWitnessInstructionInteractionsWith witness.data witness.tables programChannel
  let target := TypedInteraction.pulledIfValue programChannel
    (decoded.toChipRow witness.data).is_real
    (programMessageOfView (decoded.toChipRow witness.data).view)
  have targetMem : target ∈ consumers := by
    dsimp only [consumers]
    rw [decodedWitnessProgramInteractions_eq witness constraints]
    exact List.mem_flatMap.mpr ⟨decoded, decodedMem, by simp [target]⟩
  have targetPull : target.mult = -1 := by
    simp [target, active]
  have consumerShape : ∀ interaction ∈ consumers,
      interaction.mult = 0 ∨ interaction.mult = -1 := by
    exact decodedWitnessProgramInteractions_pullShape witness constraints
  have channelBalanced := typedInteractions_balanced witness balanced programChannel
    (by simp [sp1Ensemble_channels])
  let table := programProviderTable witness
  have tableAt := programProviderTable_getElem? witness
  have ensembleShape : typedEnsembleInteractionsWith witness programChannel =
      consumers ++ typedTableInteractionsWith table programChannel := by
    rw [typedEnsembleInteractionsWith_partition,
      witness_verifierProgramInteractions_eq_nil,
      witness_providerProgramInteractions_eq witness table tableAt]
    rfl
  rw [ensembleShape] at channelBalanced
  obtain ⟨provider, providerMem, messageEq, providerNonzero⟩ :=
    provider_matches_active_pull consumers (typedTableInteractionsWith table programChannel)
      channelBalanced consumerShape target targetMem targetPull
  have rawMem : provider.raw ∈ table.interactionsWith programChannel.toRaw := by
    rw [← typedTableInteractionsWith_raw]
    exact List.mem_map_of_mem providerMem
  let rebound : TypedInteraction programChannel :=
    { raw := provider.raw
      channel_eq := table.channel_eq_of_mem_interactionsWith rawMem }
  have truth := providerBound provider.raw rawMem (by
    simpa only [TypedInteraction.mult] using providerNonzero)
  have reboundEq : rebound = provider := TypedInteraction.raw_injective rfl
  change ProgTruth rebound.message witness.data at truth
  rw [reboundEq] at truth
  rw [messageEq] at truth
  simpa only [target, TypedInteraction.pulledIfValue_message] using truth

/-- Program grounding after erasing the retained dependent descriptor: every active canonical
`ChipRow` is decoded from the program named by the semantic statement binding. -/
theorem witness_realDecodedChipRows_programDecoded
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providerBound : ProgramProviderBound witness) (program : Target.GuestProgram)
    (programCommitted : Commit.StatementFor witness.data program) :
    ∀ row ∈ realDecodedChipRows witness.data witness.tables,
      Target.decodedInROM program (programAccess row.view).toRow := by
  intro row rowMem
  rw [realDecodedChipRows, decodedChipRows, List.mem_filter] at rowMem
  simp only [decide_eq_true_eq] at rowMem
  obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem.1
  have truth := decoded.programTruth_of_active witness constraints balanced providerBound decodedMem
    rowMem.2
  have decodedTruth := truth.2
  rw [programCommitted.2] at decodedTruth
  simpa only [rowOfMsg_programMessageOfView] using decodedTruth

/-- Exhaustive reordering preserves committed-program decode truth row by row. -/
theorem witness_orderedRows_programDecoded
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providerBound : ProgramProviderBound witness) (program : Target.GuestProgram)
    (programCommitted : Commit.StatementFor witness.data program)
    (orderedRows : List (ChipRow p))
    (exhaustive : orderedRows.Perm (realDecodedChipRows witness.data witness.tables)) :
    ∀ row ∈ orderedRows,
      Target.decodedInROM program (programAccess row.view).toRow := by
  intro row rowMem
  exact witness_realDecodedChipRows_programDecoded witness constraints balanced providerBound program
    programCommitted row (exhaustive.mem_iff.mp rowMem)

end SP1Clean.Soundness
