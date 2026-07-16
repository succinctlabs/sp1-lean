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
  change MemoryMsg.isU64 message
  have pairMem :
      (message, Semantics.StateMsg.timeNat (statePullMessage (decoded.toChipRow data))) ∈
        (decoded.ordinaryRowFacts data).memPulls := by
    rw [ordinaryRowFacts_memPulls]
    exact List.mem_map.mpr ⟨message, messageMem, rfl⟩
  exact ((grounded.2 _ pairMem).1).1

end DecodedInstructionRow

end SP1Clean.Soundness
