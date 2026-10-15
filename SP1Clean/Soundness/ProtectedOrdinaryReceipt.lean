import SP1Clean.Soundness.OrdinaryStateReceipt
import SP1Clean.Proofs.Chips.ProtectedStore

/-! # Ordinary receipts retain the installed store protection

The four stores compose their existing byte-permission circuits before publishing a receipt.
Every other instruction composes the original registered circuit. The symbolic projection and
decoder are exactly those of `OrdinaryStateReceipt`; no execution or row inventory is duplicated.
This is the producer registry for mixed installation, not a new whole-chip Rust anchor.
-/

namespace SP1Clean.Soundness.ProtectedOrdinaryReceipt

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Reuse the registered input representation without unfolding the instruction circuit. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs
/-- Reuse the registered output representation without unfolding the instruction circuit. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

/-- The existing protected instruction circuit, with the original input/output representation. -/
def provider (id : InstructionChipId) : GeneralFormalCircuit (ZMod p)
    (supportedChipFor (p := p) id).kind.Inputs (supportedChipFor (p := p) id).kind.Cols :=
  match id with
  | .storeByte => ProtectedStore.byte
  | .storeHalf => ProtectedStore.half
  | .storeWord => ProtectedStore.word
  | .storeDouble => ProtectedStore.double
  | other => (supportedChipFor other).circuit

/-- Add the ordinary successor receipt after all original checks and write-permission requests. -/
def component (id : InstructionChipId) : Component (ZMod p) :=
  { circuit := InstructionReceipt.circuit (provider id) (OrdinaryStateReceipt.projection id) }

/-- Permission requests do not change the original output cells. -/
theorem provider_output (id : InstructionChipId) :
    (provider (p := p) id).output = (supportedChipFor (p := p) id).circuit.output := by
  cases id <;> rfl

/-- Protection preserves every original assertion. -/
theorem provider_constraints (id : InstructionChipId) :
    ({ circuit := provider (p := p) id } : Component (ZMod p)).operations.constraints =
      (supportedChipFor (p := p) id).table.operations.constraints := by
  cases id with
  | storeByte => exact ProtectedStore.byte_constraints
  | storeHalf => exact ProtectedStore.half_constraints
  | storeWord => exact ProtectedStore.word_constraints
  | storeDouble => exact ProtectedStore.double_constraints
  | _ => rfl

/-- Protection preserves every fixed lookup. -/
theorem provider_lookups (id : InstructionChipId) :
    ({ circuit := provider (p := p) id } : Component (ZMod p)).operations.lookups =
      (supportedChipFor (p := p) id).table.operations.lookups := by
  cases id with
  | storeByte => exact ProtectedStore.byte_lookups
  | storeHalf => exact ProtectedStore.half_lookups
  | storeWord => exact ProtectedStore.word_lookups
  | storeDouble => exact ProtectedStore.double_lookups
  | _ => rfl

/-- Protection changes only its dedicated byte-permission ledger. -/
theorem provider_interactions (id : InstructionChipId) (selected : RawChannel (ZMod p))
    (different : selected ≠ WritePermissionProvider.channel.toRaw) :
    ({ circuit := provider id } : Component (ZMod p)).operations.interactionsWith selected =
      (supportedChipFor (p := p) id).table.operations.interactionsWith selected := by
  cases id with
  | storeByte => exact ProtectedStore.byte_interactions selected different
  | storeHalf => exact ProtectedStore.half_interactions selected different
  | storeWord => exact ProtectedStore.word_interactions selected different
  | storeDouble => exact ProtectedStore.double_interactions selected different
  | _ => rfl

/-- The protected circuit has no existing physical receipt occurrence. -/
theorem provider_receipts (id : InstructionChipId) :
    ({ circuit := provider (p := p) id } : Component (ZMod p)).operations.interactionsWith
      InstructionReceipt.channel.toRaw = [] := by
  rw [provider_interactions id _ (by
    intro same
    have names := congrArg (fun channel => channel.name == "SP1OrdinaryStateReceipt") same
    exact Bool.noConfusion names)]
  simp only [Component.interactionsWith_eq, Component.rowOperations]
  exact InteractionRecovery.interactionsWith_main_eq_nil (supportedChipFor (p := p) id).circuit.base _
    (varFromOffset (supportedChipFor (p := p) id).kind.Inputs 0) (size (supportedChipFor (p := p) id).kind.Inputs)
    (OrdinaryStateReceipt.original_silent id)

/-- The exact same symbolic projection agrees with the protected circuit's unchanged output. -/
theorem projection_agrees (id : InstructionChipId) :
    OrdinaryStateReceipt.AgreesWith (provider (p := p) id)
      (OrdinaryStateReceipt.projection id) (supportedChipFor (p := p) id).kind.view := by
  intro input offset env
  rw [provider_output]
  exact OrdinaryStateReceipt.projection_agrees id input offset env

/-- Protected rows publish the existing decoder's exact activity and successor. -/
theorem row_receipt (id : InstructionChipId) (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (component id).operations.interactionValuesWith InstructionReceipt.channel.toRaw
      (Environment.fromArray physical data) =
        [InstructionReceipt.channel.pushedIfValue
          ((supportedChipFor (p := p) id).decodeRow data physical).is_real
          (statePushMessage ((supportedChipFor (p := p) id).decodeRow data physical))] := by
  have ledger : (component id).operations.interactionsWith InstructionReceipt.channel.toRaw =
      ({ circuit := provider id } : Component (ZMod p)).operations.interactionsWith InstructionReceipt.channel.toRaw ++
        [(InstructionReceipt.channel.pushedIf
          ((OrdinaryStateReceipt.projection id).gate (varFromOffset _ 0) (size (supportedChipFor (p := p) id).kind.Inputs))
          ((OrdinaryStateReceipt.projection id).message (varFromOffset _ 0) (size (supportedChipFor (p := p) id).kind.Inputs))).toRaw] := by
    simpa only [component, InstructionReceipt.circuit, Component.interactionsWith_eq, Component.rowOperations] using
      Receipt.receipt_interactions (provider id) InstructionReceipt.channel (fun _ _ => trivial)
      (OrdinaryStateReceipt.projection id) (varFromOffset _ 0) (size (supportedChipFor (p := p) id).kind.Inputs)
  rw [provider_receipts] at ledger
  simp only [Operations.interactionValuesWith, ledger, List.nil_append, List.map_cons, List.map_nil,
    Channel.eval_pushedIf]
  have meaning := OrdinaryStateReceipt.row_meaning (supportedChipFor (p := p) id).circuit
    (OrdinaryStateReceipt.projection id) (supportedChipFor (p := p) id).kind.view
    (OrdinaryStateReceipt.projection_agrees id) (Environment.fromArray physical data)
  rw [meaning.1, meaning.2]
  rfl

/-- The complete protected assertion list survives receipt publication. -/
theorem constraints (id : InstructionChipId) : (component (p := p) id).operations.constraints =
    ({ circuit := provider id } : Component (ZMod p)).operations.constraints := Receipt.constraints _ _ _ _

/-- The complete protected lookup list survives receipt publication. -/
theorem lookups (id : InstructionChipId) : (component (p := p) id).operations.lookups =
    ({ circuit := provider id } : Component (ZMod p)).operations.lookups := Receipt.lookups _ _ _ _

/-- Receipt publication retains every protected row's exact width. -/
theorem width (id : InstructionChipId) : (component (p := p) id).width =
    ({ circuit := provider id } : Component (ZMod p)).width := Receipt.width _ _ _ _

/-- In particular, every write-permission occurrence survives, including disabled requests. -/
theorem interactions (id : InstructionChipId) (selected : RawChannel (ZMod p))
    (different : selected ≠ InstructionReceipt.channel.toRaw) :
    (component id).operations.interactionsWith selected =
      ({ circuit := provider id } : Component (ZMod p)).operations.interactionsWith selected :=
  Receipt.interactions _ _ _ _ selected different

/-- Publish receipts on the protected table's existing rows, preserving their layout. -/
def construct (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = { circuit := provider id }) : Table (ZMod p) :=
  original.withComponent (component id) (by rw [registered]; exact width id)
    (by rw [registered]; rfl)

/-- Construction preserves all protected local checks at the same ensemble data. -/
theorem construct_constraints (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = { circuit := provider id }) (data : ProverData (ZMod p)) :
    (construct id original registered).Constraints data ↔ original.Constraints data := by
  apply Table.withComponent_constraints
  · rw [registered, constraints]
  · rw [registered, lookups]

/-- The new ledger is decoded from the existing physical rows, including padding. -/
theorem construct_receipts (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = { circuit := provider id }) (data : ProverData (ZMod p)) :
    (construct id original registered).interactionsWith data InstructionReceipt.channel.toRaw =
      original.table.map (fun physical =>
        let row := (supportedChipFor (p := p) id).decodeRow data physical
        InstructionReceipt.channel.pushedIfValue row.is_real (statePushMessage row)) := by
  simp only [construct, Table.interactionsWith, Table.withComponent, row_receipt]
  exact List.map_eq_flatMap.symm

/-- Exact cost counts one receipt per physical row, including zero multiplicity padding. -/
theorem construct_receipt_count (id : InstructionChipId) (original : Table (ZMod p))
    (registered : original.component = { circuit := provider id }) (data : ProverData (ZMod p)) :
    ((construct id original registered).interactionsWith data InstructionReceipt.channel.toRaw).length =
      original.length := by
  rw [construct_receipts, List.length_map]

end SP1Clean.Soundness.ProtectedOrdinaryReceipt
