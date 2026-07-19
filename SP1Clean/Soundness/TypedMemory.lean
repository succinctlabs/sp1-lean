import SP1Clean.Soundness.TypedState
import SP1Clean.Soundness.TypedProgram
import SP1Clean.Soundness.TimedGrounding

/-! # Typed Memory records for deterministically decoded rows

This module is the Memory analogue of `TypedState`/`TypedProgram`, but deliberately avoids another
hand-written interaction projection. A decoded physical row already retains its exact evaluated Clean
interactions. We classify those typed interactions by their signed multiplicity:

* active pulls are the prior-memory records consumed by the row;
* active pushes are the new/read-back records produced by the row; and
* every prior record is observed at the row's pre-state time.

The last choice is semantic rather than layout-specific. Register operands are unchanged until the
ordinary `+4` write slot and RAM is read before its `+1` effect slot, so the row's State-pull time is a
uniform currency point for all prior records. Later schedule generalization may replace the ordinary
`RowFacts` carrier, but it must continue to derive these records from the circuit's emitted interaction
list rather than duplicating it.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

set_option maxHeartbeats 1000000 in
omit [Fact (2 ^ 24 < p)] in
/-- Evaluate the canonical register-shaped Memory pull without unfolding a concrete chip input. -/
theorem eval_registerMemoryMessage (env : Environment (ZMod p))
    (clkHigh prevLow index : Expression (ZMod p)) (value : Word (Expression (ZMod p))) :
    Eval.eval env (⟨clkHigh, prevLow, index, 0, 0, value⟩ : MemoryMsg (Expression (ZMod p))) =
      (⟨Expression.eval env clkHigh, Expression.eval env prevLow, Expression.eval env index,
        0, 0, Eval.eval env value⟩ : MemoryMsg (ZMod p)) := by
  rw [ProvableStruct.eval_eq_eval]
  simp only [ProvableStruct.structEvalLiteralProc, Expression.eval]

/-- Package an active canonical register pull into the operand witness expected by the chip-level
contract.  Keeping this dependent-record assembly generic prevents concrete completed circuits from
being unfolded while Lean unifies the `MemoryMsg` projections. -/
theorem registerPullWitness_of_registerMessage
    (interactions : List (TypedInteraction (memoryChannel (p := p))))
    (clkHigh prevLow addr0 : ZMod p) (value expected : Word (ZMod p))
    (member : (⟨clkHigh, prevLow, addr0, 0, 0, value⟩ : MemoryMsg (ZMod p)) ∈
      consumedMessages interactions)
    (index : BitVec 5) (indexEq : (index.toNat : ZMod p) = addr0)
    (valueEq : value = expected) :
    ∃ message ∈ consumedMessages interactions,
      Semantics.MemoryMsg.locOf message = Semantics.MemLoc.reg index ∧
      message.value = expected := by
  let message : MemoryMsg (ZMod p) := ⟨clkHigh, prevLow, addr0, 0, 0, value⟩
  refine ⟨message, member, ?_, valueEq⟩
  exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl

namespace DecodedInstructionRow

/-- The active prior-memory messages consumed by this exact physical row. -/
noncomputable def consumedMemoryMessages (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : List (MemoryMsg (ZMod p)) :=
  consumedMessages (decoded.interactionsWith data memoryChannel)

/-- The active read-back/write messages produced by this exact physical row. -/
noncomputable def producedMemoryMessages (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : List (MemoryMsg (ZMod p)) :=
  producedMessages (decoded.interactionsWith data memoryChannel)

/-- The ordinary-window semantic record attached to a decoded physical row. Its bus fields are
computed from that row's actual typed interactions, while State and Program use the already-proved
canonical semantic projections of the same row. -/
noncomputable def ordinaryRowFacts (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : Semantics.RowFacts p :=
  let row := decoded.toChipRow data
  let readTime := Semantics.StateMsg.timeNat (statePullMessage row)
  { statePull := statePullMessage row
    statePush := statePushMessage row
    fetch := programMessageOfView row.view
    memPulls := (decoded.consumedMemoryMessages data).map fun message => (message, readTime)
    memPushes := decoded.producedMemoryMessages data }

@[simp] theorem ordinaryRowFacts_statePull (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (decoded.ordinaryRowFacts data).statePull = statePullMessage (decoded.toChipRow data) := rfl

@[simp] theorem ordinaryRowFacts_statePush (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (decoded.ordinaryRowFacts data).statePush = statePushMessage (decoded.toChipRow data) := rfl

@[simp] theorem ordinaryRowFacts_fetch (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (decoded.ordinaryRowFacts data).fetch =
      programMessageOfView (decoded.toChipRow data).view := rfl

@[simp] theorem ordinaryRowFacts_memPulls (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (decoded.ordinaryRowFacts data).memPulls =
      (decoded.consumedMemoryMessages data).map fun message =>
        (message, Semantics.StateMsg.timeNat (statePullMessage (decoded.toChipRow data))) := rfl

@[simp] theorem ordinaryRowFacts_memPushes (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (decoded.ordinaryRowFacts data).memPushes = decoded.producedMemoryMessages data := rfl

/-- Circuit-local exact-pull contract for one register operand.  It quantifies over the actual
flattened Clean component and its evaluated typed Memory interactions; the three accessors select
the operand gate, register index, and prior value from the common row view. -/
def CircuitRegisterOperandPullAt {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p)
    (ready : Input (ZMod p) → Output (ZMod p) → Target.GuestProgram → SailState → Prop)
    (immediate operandIndex : Trace.AdapterView (ZMod p) → ZMod p)
    (priorValue : Trace.AdapterView (ZMod p) → Word (ZMod p)) :
    Prop :=
  ∀ data physical rowView program state,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    rowView = view (component.rowInput env) (component.rowOutput env) →
      ready (component.rowInput env) (component.rowOutput env) program state →
      selector (component.rowInput env) = 1 →
      ∀ index : BitVec 5, immediate rowView.adapter = 0 →
        (index.toNat : ZMod p) = operandIndex rowView.adapter →
        ∃ message ∈ consumedMessages
          (typedInteractionValuesWith component.operations memoryChannel env),
        Semantics.MemoryMsg.locOf message = Semantics.MemLoc.reg index ∧
        message.value = priorValue rowView.adapter

/-- Circuit-local form of the exact register-source interaction contract.  Splitting the two
operand fields permits each chip to prove them independently while retaining one common interface. -/
structure CircuitRegisterOperandPullShape {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p)
    (ready : Input (ZMod p) → Output (ZMod p) → Target.GuestProgram → SailState → Prop) :
    Prop where
  opB : CircuitRegisterOperandPullAt circuit view selector ready
    (fun adapter => adapter.imm_b) (fun adapter => adapter.op_b[0])
    (fun adapter => adapter.op_b_memory.prev_value)
  opC : CircuitRegisterOperandPullAt circuit view selector ready
    (fun adapter => adapter.imm_c) (fun adapter => adapter.op_c[0])
    (fun adapter => adapter.op_c_memory.prev_value)

/-- Closed-form facts for one register source-operand pull.  Every fact is stated against the
circuit's public syntactic surface — `main`'s retained interaction list and the elaborated
`circuit.output` — never against the flattened `Component` projections (`rowOutput`/`operations`),
so per-chip instances stay cheap for the kernel; the single `rowOutput → circuit.output`
identification happens once, over abstract circuits, in the generic transport below. -/
def CircuitRegisterOperandPullContractAt {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p)
    (operandIndex : Trace.AdapterView (ZMod p) → ZMod p)
    (priorValue : Trace.AdapterView (ZMod p) → Word (ZMod p)) : Prop :=
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  ∃ (gate clkHigh prevLow indexExpr : Var Input (ZMod p) → ℕ → Expression (ZMod p))
    (valueExpr : Var Input (ZMod p) → ℕ → Word (Expression (ZMod p))),
    (∀ input offset,
      (memoryChannel.pulledIf (gate input offset)
        (⟨clkHigh input offset, prevLow input offset, indexExpr input offset, 0, 0,
          valueExpr input offset⟩ : MemoryMsg (Expression (ZMod p)))).toRaw ∈
        ((circuit.main input).operations offset).interactionsWith memoryChannel.toRaw) ∧
    (∀ env : Environment (ZMod p),
      Expression.eval env (gate inputVar offset) = selector (Eval.eval env inputVar)) ∧
    (∀ env : Environment (ZMod p),
      Expression.eval env (indexExpr inputVar offset) =
        operandIndex (view (Eval.eval env inputVar)
          (Eval.eval env (circuit.output inputVar offset))).adapter) ∧
    (∀ env : Environment (ZMod p),
      Eval.eval env (valueExpr inputVar offset) =
        priorValue (view (Eval.eval env inputVar)
          (Eval.eval env (circuit.output inputVar offset))).adapter)

/-- The per-chip bundle of closed-form source-operand pull facts (operands B and C), the sole
obligation left to each chip's `CircuitGroundingContracts` file. -/
structure CircuitRegisterOperandPullContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p) : Prop where
  opB : CircuitRegisterOperandPullContractAt circuit view selector
    (fun adapter => adapter.op_b[0]) (fun adapter => adapter.op_b_memory.prev_value)
  opC : CircuitRegisterOperandPullContractAt circuit view selector
    (fun adapter => adapter.op_c[0]) (fun adapter => adapter.op_c_memory.prev_value)

/-- Transport one closed-form operand contract to the flattened-component pull statement.  The
`rowInput`/`rowOutput` identifications happen here over an abstract circuit, so concrete chips
never force the kernel to re-normalize their composed `main`. -/
theorem circuitRegisterOperandPullAt_of_exposure {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p)
    (ready : Input (ZMod p) → Output (ZMod p) → Target.GuestProgram → SailState → Prop)
    (immediate operandIndex : Trace.AdapterView (ZMod p) → ZMod p)
    (priorValue : Trace.AdapterView (ZMod p) → Word (ZMod p))
    (contract : CircuitRegisterOperandPullContractAt circuit view selector
      operandIndex priorValue) :
    CircuitRegisterOperandPullAt circuit view selector ready immediate operandIndex priorValue := by
  obtain ⟨gate, clkHigh, prevLow, indexExpr, valueExpr, member, gate_eval, index_eval,
    value_eval⟩ := contract
  intro data physical rowView
  dsimp only
  intro program state viewEq _ready real
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  have viewEq' : rowView = view (Eval.eval env inputVar)
      (Eval.eval env (circuit.output inputVar offset)) := by
    rw [inputEq, outputEq]
    exact viewEq
  intro index _immediate indexEq
  have active : Expression.eval env (gate inputVar offset) = 1 := by
    calc
      _ = selector (Eval.eval env inputVar) := gate_eval env
      _ = selector (component.rowInput env) := by rw [inputEq]
      _ = 1 := real
  have rawMem : (memoryChannel.pulledIf (gate inputVar offset)
      (⟨clkHigh inputVar offset, prevLow inputVar offset, indexExpr inputVar offset, 0, 0,
        valueExpr inputVar offset⟩ : MemoryMsg (Expression (ZMod p)))).toRaw ∈
      component.operations.interactionsWith memoryChannel.toRaw := by
    rw [Component.interactionsWith_eq]
    exact member inputVar offset
  have hp : 2 < p := by
    have := Fact.out (p := 2 ^ 24 < p)
    omega
  have consumed := eval_pulledIf_message_mem_consumedMessages component.operations memoryChannel
    env (gate inputVar offset) _ rawMem hp active
  rw [eval_registerMemoryMessage] at consumed
  have addr0 : (index.toNat : ZMod p) = Expression.eval env (indexExpr inputVar offset) := by
    rw [index_eval env, ← viewEq']
    exact indexEq
  have valueEq : Eval.eval env (valueExpr inputVar offset) = priorValue rowView.adapter := by
    rw [value_eval env, ← viewEq']
  exact registerPullWitness_of_registerMessage _ _ _ _ _ _ consumed index addr0 valueEq

/-- Transport the per-chip closed-form contract bundle to the two-operand pull shape. -/
theorem circuitRegisterOperandPullShape_of_exposure {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p)
    (ready : Input (ZMod p) → Output (ZMod p) → Target.GuestProgram → SailState → Prop)
    (contract : CircuitRegisterOperandPullContract circuit view selector) :
    CircuitRegisterOperandPullShape circuit view selector ready :=
  ⟨circuitRegisterOperandPullAt_of_exposure circuit view selector ready _ _ _ contract.opB,
   circuitRegisterOperandPullAt_of_exposure circuit view selector ready _ _ _ contract.opC⟩

/-- Descriptor-level exact-pull contract for one register operand. -/
def RegisterOperandPullAt (chip : SupportedChip p)
    (immediate operandIndex : Trace.AdapterView (ZMod p) → ZMod p)
    (priorValue : Trace.AdapterView (ZMod p) → Word (ZMod p)) : Prop :=
  ∀ data physical program state,
    let row := chip.decodeRow data physical
    chip.kind.advanceReady row.inputs row.cols program state →
    row.is_real = 1 →
      ∀ index : BitVec 5, immediate row.view.adapter = 0 →
        (index.toNat : ZMod p) = operandIndex row.view.adapter →
        ∃ message ∈ consumedMessages
          (typedInteractionValuesWith chip.table.operations memoryChannel
            (Environment.fromArray physical data)),
        Semantics.MemoryMsg.locOf message = Semantics.MemLoc.reg index ∧
        message.value = priorValue row.view.adapter

/-- Descriptor-level transport of `CircuitRegisterOperandPullShape`. -/
structure RegisterOperandPullShape (chip : SupportedChip p) : Prop where
  opB : RegisterOperandPullAt chip
    (fun adapter => adapter.imm_b) (fun adapter => adapter.op_b[0])
    (fun adapter => adapter.op_b_memory.prev_value)
  opC : RegisterOperandPullAt chip
    (fun adapter => adapter.imm_c) (fun adapter => adapter.op_c[0])
    (fun adapter => adapter.op_c_memory.prev_value)

/-- Transport a circuit-local source-pull theorem to its retained supported-chip descriptor. -/
theorem registerOperandPullShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (selector : kind.Inputs (ZMod p) → ZMod p)
    (selector_eq : ∀ input output, (kind.view input output).is_real = selector input)
    (shape : @CircuitRegisterOperandPullShape p _ kind.Inputs kind.Cols
      kind.provableInputs kind.provableCols circuit kind.view selector kind.advanceReady) :
    RegisterOperandPullShape ⟨kind, circuit, spec_eq, opcodes, rdGuard⟩ := by
  letI : ProvableType kind.Inputs := kind.provableInputs
  letI : ProvableType kind.Cols := kind.provableCols
  constructor
  · intro data physical program state
    dsimp only
    intro ready real
    apply shape.opB data physical _ program state rfl ready
    rw [← selector_eq]
    exact real
  · intro data physical program state
    dsimp only
    intro ready real
    apply shape.opC data physical _ program state rfl ready
    rw [← selector_eq]
    exact real

/-- One-step descriptor transport for chip-local operand-pull contracts.  All dependent typeclass
evidence is taken from `kind` explicitly, so applying this theorem never asks typeclass search to
reduce a concrete `ChipKind` record. -/
theorem registerOperandPullShape_of_circuitContract (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (selector : kind.Inputs (ZMod p) → ZMod p)
    (selector_eq : ∀ input output, (kind.view input output).is_real = selector input)
    (contract : @CircuitRegisterOperandPullContract p _ kind.Inputs kind.Cols
      kind.provableInputs kind.provableCols circuit kind.view selector) :
    RegisterOperandPullShape ⟨kind, circuit, spec_eq, opcodes, rdGuard⟩ := by
  letI : ProvableType kind.Inputs := kind.provableInputs
  letI : ProvableType kind.Cols := kind.provableCols
  apply registerOperandPullShape_of_circuit kind circuit spec_eq opcodes rdGuard selector
    selector_eq
  exact circuitRegisterOperandPullShape_of_exposure circuit kind.view selector
    kind.advanceReady contract

/-- The minimal chip-level interface exposing which exact Memory pulls carry the two possible
register source operands. This is a theorem about the chip's emitted interaction list, not another
interaction representation: immediate operands impose no obligation, and the witness's existing
`RowView` supplies the values consumed by the Sail bridge. -/
structure RegisterOperandPulls (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : Prop where
  opB : ∀ index : BitVec 5,
    (decoded.toChipRow data).is_real = 1 →
    (decoded.toChipRow data).view.adapter.imm_b = 0 →
    (index.toNat : ZMod p) = (decoded.toChipRow data).view.adapter.op_b[0] →
    ∃ message ∈ decoded.consumedMemoryMessages data,
      Semantics.MemoryMsg.locOf message = Semantics.MemLoc.reg index ∧
      message.value = (decoded.toChipRow data).view.adapter.op_b_memory.prev_value
  opC : ∀ index : BitVec 5,
    (decoded.toChipRow data).is_real = 1 →
    (decoded.toChipRow data).view.adapter.imm_c = 0 →
    (index.toNat : ZMod p) = (decoded.toChipRow data).view.adapter.op_c[0] →
    ∃ message ∈ decoded.consumedMemoryMessages data,
      Semantics.MemoryMsg.locOf message = Semantics.MemLoc.reg index ∧
      message.value = (decoded.toChipRow data).view.adapter.op_c_memory.prev_value

/-- Instantiate the chip-level exact-interaction contract for one retained physical row. -/
theorem registerOperandPulls_of_shape (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (program : Target.GuestProgram) (state : SailState)
    (shape : RegisterOperandPullShape decoded.chip)
    (ready : (decoded.toChipRow data).kind.advanceReady
      (decoded.toChipRow data).inputs (decoded.toChipRow data).cols program state) :
    decoded.RegisterOperandPulls data := by
  constructor
  · intro index real immediate indexEq
    exact shape.opB data decoded.physical program state ready real index immediate indexEq
  · intro index real immediate indexEq
    exact shape.opC data decoded.physical program state ready real index immediate indexEq

/-- Timed grounding plus the chip's exact operand-pull interface identifies the row's committed
source values with the live Sail registers at this execution position. -/
theorem valueOperandsBound_of_grounded (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (program : Target.GuestProgram)
    (initial state : SailState) (initialClock steps : ℕ)
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts data))
    (chain : Target.SailChain steps initial state)
    (real : (decoded.toChipRow data).is_real = 1)
    (rowTime : Semantics.StateMsg.timeNat
      (statePullMessage (decoded.toChipRow data)) = initialClock + 8 * steps)
    (pulls : decoded.RegisterOperandPulls data) :
    Target.ValueOperandsBound (decoded.toChipRow data).view state := by
  constructor
  · intro index immediate indexEq
    obtain ⟨message, messageMem, location, value⟩ := pulls.opB index real immediate indexEq
    have pairMem :
        (message, Semantics.StateMsg.timeNat (statePullMessage (decoded.toChipRow data))) ∈
          (decoded.ordinaryRowFacts data).memPulls := by
      rw [ordinaryRowFacts_memPulls]
      exact List.mem_map.mpr ⟨message, messageMem, rfl⟩
    have current := (grounded.2 _ pairMem).2
    rw [location, value, rowTime] at current
    have live := (Semantics.localValueAt_stepStart_iff chain).mp current
    exact live
  · intro index immediate indexEq
    obtain ⟨message, messageMem, location, value⟩ := pulls.opC index real immediate indexEq
    have pairMem :
        (message, Semantics.StateMsg.timeNat (statePullMessage (decoded.toChipRow data))) ∈
          (decoded.ordinaryRowFacts data).memPulls := by
      rw [ordinaryRowFacts_memPulls]
      exact List.mem_map.mpr ⟨message, messageMem, rfl⟩
    have current := (grounded.2 _ pairMem).2
    rw [location, value, rowTime] at current
    have live := (Semantics.localValueAt_stepStart_iff chain).mp current
    exact live

/-- Timed semantic grounding of the row's exact active prior records supplies the Memory guarantees
consumed by its original Clean circuit. This is the key direction needed by chip `weakSoundness`:
grounding does not assume a circuit Spec and does not replace the circuit's interaction list. -/
theorem memoryChannelGuarantees_of_grounded (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (program : Target.GuestProgram)
    (initial : SailState) (initialClock : ℕ)
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts data)) :
    decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data) := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  apply channelGuarantees_of_consumedMessages decoded.chip.table.operations memoryChannel
    (decoded.environment data) hp
  intro message messageMem
  -- G1: the memory channel's `Guarantees` is the pair `isU64 ∧ ClkBound`, and both are conjuncts of
  -- the pulled record's `LocalMemTruth` that timed grounding supplies.
  change MemoryMsg.isU64 message ∧ MemoryMsg.ClkBound message
  have pairMem :
      (message, Semantics.StateMsg.timeNat (statePullMessage (decoded.toChipRow data))) ∈
        (decoded.ordinaryRowFacts data).memPulls := by
    rw [ordinaryRowFacts_memPulls]
    exact List.mem_map.mpr ⟨message, messageMem, rfl⟩
  have truth := (grounded.2 _ pairMem).1
  exact ⟨truth.1, truth.2.1⟩

end DecodedInstructionRow

end SP1Clean.Soundness
