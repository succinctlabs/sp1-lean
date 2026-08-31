import SP1Clean.Soundness.TypedTimeContracts
import SP1Clean.Proofs.Chips.BitwiseChip.Contracts
import SP1Clean.Proofs.Chips.LtChip.Contracts
import SP1Clean.Proofs.Chips.ShiftLeftChip.Contracts
import SP1Clean.Proofs.Chips.ShiftRightChip.Contracts
import SP1Clean.Proofs.Chips.BranchChip.Contracts
import SP1Clean.Proofs.Chips.LoadByteChip.Contracts
import SP1Clean.Proofs.Chips.LoadHalfChip.Contracts
import SP1Clean.Proofs.Chips.LoadWordChip.Contracts
import SP1Clean.Proofs.Chips.LoadX0Chip.Contracts
import SP1Clean.Proofs.Chips.MulChip.Contracts
import SP1Clean.Proofs.Chips.DivRemChip.Contracts
import SP1Clean.Proofs.Chips.UTypeChip.Bridge
import SP1Clean.Proofs.Chips.AluX0Chip.Bridge

/-! # The fetch discriminant: no supported instruction row pins the `ECALL` opcode

The per-chip strengthening step of the committed-fragment re-base (the halt-table wave): every
active decoded instruction row's Program-bus pull carries an opcode different from `ECALL`'s
discriminant `50`, so `committedInROM.decoded_of_opcode_ne` recovers today's decoded form from the
re-based Program provider (`Semantics.CommittedProgTruth`).

The layering mirrors `Soundness/TypedSelectors.lean`'s selector dispatch exactly: a descriptor-level
`FetchDiscriminantShape` obligation, a circuit-level `CircuitFetchDiscriminant` producer, the
definitional transport between them, and the finite 25-case registry rollout.  Twelve chips pin a
literal opcode in their `rowView` and need no constraint at all; the flag chips derive the fact from
their selector one-hot/booleanity gates (each chip's `physicalViewOpcode_ne_ecall`, proved beside
its other row-level constraint extractions), and `AluX0` from its Byte-table dynamic-opcode range
(`opcode < 29`) — the one case that consumes the Byte-channel guarantee premise. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Small distinct naturals stay distinct in a field this large. -/
private theorem natLit_ne_fifty {k : ℕ} (hk : k < 2 ^ 17) (hne : k ≠ 50) :
    ((k : ℕ) : ZMod p) ≠ (50 : ZMod p) := by
  have h17 : 2 ^ 17 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  intro h
  rw [show (50 : ZMod p) = ((50 : ℕ) : ZMod p) from by norm_cast] at h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
  exact hne hval

/-- The physical constraints (and Byte guarantees) of a circuit keep the opcode exposed by its row
view away from the `ECALL` discriminant on every live row.  Stated without `let` bindings so each
per-chip instance can be a one-line term. -/
def CircuitFetchDiscriminant {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ data physical,
    (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data) →
      (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees Channels.byteChannel.toRaw
        (Environment.fromArray physical data) →
        (view ((⟨circuit⟩ : Component (ZMod p)).rowInput (Environment.fromArray physical data))
            ((⟨circuit⟩ : Component (ZMod p)).rowOutput
              (Environment.fromArray physical data))).is_real = 1 →
          (view ((⟨circuit⟩ : Component (ZMod p)).rowInput (Environment.fromArray physical data))
              ((⟨circuit⟩ : Component (ZMod p)).rowOutput
                (Environment.fromArray physical data))).opcode ≠ (50 : ZMod p)

/-- The descriptor-level obligation collected by the registry rollout. -/
def FetchDiscriminantShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    chip.table.operations.ConstraintsHold (Environment.fromArray physical data) →
      chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
        (Environment.fromArray physical data) →
        (chip.kind.view (chip.table.rowInput (Environment.fromArray physical data))
            (chip.table.rowOutput (Environment.fromArray physical data))).is_real = 1 →
          (chip.kind.view (chip.table.rowInput (Environment.fromArray physical data))
              (chip.table.rowOutput (Environment.fromArray physical data))).opcode ≠
            (50 : ZMod p)

/-- A circuit-level discriminant theorem transports definitionally to its supported descriptor. -/
theorem fetchDiscriminantShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (id : InstructionChipId)
    (shape : @CircuitFetchDiscriminant p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    FetchDiscriminantShape ⟨id, kind, circuit, spec_eq⟩ :=
  shape

/-! ## The twelve chips that pin a literal opcode -/

private theorem addChip_fetchDiscriminant :
    CircuitFetchDiscriminant (AddChip.circuit (p := p)) AddChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 0) (by omega) (by omega)
    push_cast at h
    exact h
private theorem addiChip_fetchDiscriminant :
    CircuitFetchDiscriminant (AddiChip.circuit (p := p)) AddiChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 1) (by omega) (by omega)
    push_cast at h
    exact h
private theorem addwChip_fetchDiscriminant :
    CircuitFetchDiscriminant (AddwChip.circuit (p := p)) AddwChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 19) (by omega) (by omega)
    push_cast at h
    exact h
private theorem subChip_fetchDiscriminant :
    CircuitFetchDiscriminant (SubChip.circuit (p := p)) SubChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 2) (by omega) (by omega)
    push_cast at h
    exact h
private theorem subwChip_fetchDiscriminant :
    CircuitFetchDiscriminant (SubwChip.circuit (p := p)) SubwChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 20) (by omega) (by omega)
    push_cast at h
    exact h
private theorem jalChip_fetchDiscriminant :
    CircuitFetchDiscriminant (JalChip.circuit (p := p)) JalChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 46) (by omega) (by omega)
    push_cast at h
    exact h
private theorem jalrChip_fetchDiscriminant :
    CircuitFetchDiscriminant (JalrChip.circuit (p := p)) JalrChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 47) (by omega) (by omega)
    push_cast at h
    exact h
private theorem loadDoubleChip_fetchDiscriminant :
    CircuitFetchDiscriminant (LoadDoubleChip.circuit (p := p)) LoadDoubleChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 35) (by omega) (by omega)
    push_cast at h
    exact h
private theorem storeByteChip_fetchDiscriminant :
    CircuitFetchDiscriminant (StoreByteChip.circuit (p := p)) StoreByteChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 36) (by omega) (by omega)
    push_cast at h
    exact h
private theorem storeHalfChip_fetchDiscriminant :
    CircuitFetchDiscriminant (StoreHalfChip.circuit (p := p)) StoreHalfChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 37) (by omega) (by omega)
    push_cast at h
    exact h
private theorem storeWordChip_fetchDiscriminant :
    CircuitFetchDiscriminant (StoreWordChip.circuit (p := p)) StoreWordChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 38) (by omega) (by omega)
    push_cast at h
    exact h
private theorem storeDoubleChip_fetchDiscriminant :
    CircuitFetchDiscriminant (StoreDoubleChip.circuit (p := p)) StoreDoubleChip.rowView :=
  fun _ _ _ _ _ => by
    have h := natLit_ne_fifty (p := p) (k := 39) (by omega) (by omega)
    push_cast at h
    exact h

/-! ## The flag chips, from their own selector gates -/

private theorem bitwiseChip_fetchDiscriminant :
    CircuitFetchDiscriminant (BitwiseChip.circuit (p := p)) BitwiseChip.rowView :=
  fun _ _ constraints _ real => BitwiseChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem ltChip_fetchDiscriminant :
    CircuitFetchDiscriminant (LtChip.circuit (p := p)) LtChip.rowView :=
  fun _ _ constraints _ real => LtChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem shiftLeftChip_fetchDiscriminant :
    CircuitFetchDiscriminant (ShiftLeftChip.circuit (p := p)) ShiftLeftChip.rowView :=
  fun _ _ constraints _ real => ShiftLeftChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem shiftRightChip_fetchDiscriminant :
    CircuitFetchDiscriminant (ShiftRightChip.circuit (p := p)) ShiftRightChip.rowView :=
  fun _ _ constraints _ real => ShiftRightChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem uTypeChip_fetchDiscriminant :
    CircuitFetchDiscriminant (UTypeChip.circuit (p := p)) UTypeChip.rowView :=
  fun _ _ constraints _ real => UTypeChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem loadByteChip_fetchDiscriminant :
    CircuitFetchDiscriminant (LoadByteChip.circuit (p := p)) LoadByteChip.rowView :=
  fun _ _ constraints _ real => LoadByteChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem loadHalfChip_fetchDiscriminant :
    CircuitFetchDiscriminant (LoadHalfChip.circuit (p := p)) LoadHalfChip.rowView :=
  fun _ _ constraints _ real => LoadHalfChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem loadWordChip_fetchDiscriminant :
    CircuitFetchDiscriminant (LoadWordChip.circuit (p := p)) LoadWordChip.rowView :=
  fun _ _ constraints _ real => LoadWordChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem loadX0Chip_fetchDiscriminant :
    CircuitFetchDiscriminant (LoadX0Chip.circuit (p := p)) LoadX0Chip.rowView :=
  fun _ _ constraints _ real => LoadX0Chip.physicalViewOpcode_ne_ecall _ constraints real
private theorem mulChip_fetchDiscriminant :
    CircuitFetchDiscriminant (MulChip.circuit (p := p)) MulChip.rowView :=
  fun _ _ constraints _ real => MulChip.physicalViewOpcode_ne_ecall _ constraints real
private theorem divRemChip_fetchDiscriminant :
    CircuitFetchDiscriminant (DivRemChip.circuit (p := p)) DivRemChip.rowView :=
  fun _ _ constraints _ real => DivRemChip.physicalViewOpcode_ne_ecall _ constraints real

/-- Branch's row-level lemma is stated over the folded `main` assertion system (its documented
proof-decomposition exception keeps `circuit` out of the `Contracts` file). -/
private theorem branchChip_fetchDiscriminant :
    CircuitFetchDiscriminant (BranchChip.circuit (p := p)) BranchChip.rowView :=
  fun _ _ constraints _ real =>
    BranchChip.physicalViewOpcode_ne_ecall _ ((Component.constraintsHold_iff _).mp constraints)
      real

/-- AluX0's dynamic opcode column is bounded by its own LTU Byte pull, so this is the one case
that consumes the Byte-channel guarantee premise. -/
private theorem aluX0Chip_fetchDiscriminant :
    CircuitFetchDiscriminant (AluX0Chip.circuit (p := p)) AluX0Chip.rowView :=
  fun _ _ constraints guarantees real =>
    AluX0Chip.physicalViewOpcode_ne_ecall _ constraints guarantees real

/-- Discharge one registry case from its circuit-level discriminant theorem. -/
local macro "fetchDiscriminantCase " kind:term ", " thm:term : tactic =>
  `(tactic| (
    letI := ($kind:term).provableInputs
    letI := ($kind:term).provableCols
    apply fetchDiscriminantShape_of_circuit
    exact $thm:term))

/-- **The fetch discriminant, all 25 registered chips.** -/
theorem supportedChip_fetchDiscriminantShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : FetchDiscriminantShape chip := by
  fin_cases chipMem
  · fetchDiscriminantCase (AddChip.kind (p := p)), addChip_fetchDiscriminant
  · fetchDiscriminantCase (AddiChip.kind (p := p)), addiChip_fetchDiscriminant
  · fetchDiscriminantCase (AddwChip.kind (p := p)), addwChip_fetchDiscriminant
  · fetchDiscriminantCase (SubChip.kind (p := p)), subChip_fetchDiscriminant
  · fetchDiscriminantCase (SubwChip.kind (p := p)), subwChip_fetchDiscriminant
  · fetchDiscriminantCase (BitwiseChip.kind (p := p)), bitwiseChip_fetchDiscriminant
  · fetchDiscriminantCase (LtChip.kind (p := p)), ltChip_fetchDiscriminant
  · fetchDiscriminantCase (ShiftLeftChip.kind (p := p)), shiftLeftChip_fetchDiscriminant
  · fetchDiscriminantCase (ShiftRightChip.kind (p := p)), shiftRightChip_fetchDiscriminant
  · fetchDiscriminantCase (JalChip.kind (p := p)), jalChip_fetchDiscriminant
  · fetchDiscriminantCase (JalrChip.kind (p := p)), jalrChip_fetchDiscriminant
  · fetchDiscriminantCase (BranchChip.kind (p := p)), branchChip_fetchDiscriminant
  · fetchDiscriminantCase (UTypeChip.kind (p := p)), uTypeChip_fetchDiscriminant
  · fetchDiscriminantCase (LoadByteChip.kind (p := p)), loadByteChip_fetchDiscriminant
  · fetchDiscriminantCase (LoadHalfChip.kind (p := p)), loadHalfChip_fetchDiscriminant
  · fetchDiscriminantCase (LoadWordChip.kind (p := p)), loadWordChip_fetchDiscriminant
  · fetchDiscriminantCase (LoadDoubleChip.kind (p := p)), loadDoubleChip_fetchDiscriminant
  · fetchDiscriminantCase (LoadX0Chip.kind (p := p)), loadX0Chip_fetchDiscriminant
  · fetchDiscriminantCase (StoreByteChip.kind (p := p)), storeByteChip_fetchDiscriminant
  · fetchDiscriminantCase (StoreHalfChip.kind (p := p)), storeHalfChip_fetchDiscriminant
  · fetchDiscriminantCase (StoreWordChip.kind (p := p)), storeWordChip_fetchDiscriminant
  · fetchDiscriminantCase (StoreDoubleChip.kind (p := p)), storeDoubleChip_fetchDiscriminant
  · fetchDiscriminantCase (MulChip.kind (p := p)), mulChip_fetchDiscriminant
  · fetchDiscriminantCase (DivRemChip.kind (p := p)), divRemChip_fetchDiscriminant
  · fetchDiscriminantCase (AluX0Chip.kind (p := p)), aluX0Chip_fetchDiscriminant

/-- Every active decoded instruction row's committed Program pull pins an opcode different from
`ECALL`'s discriminant — the premise `programTruth_of_active` needs to recover the decoded form
from the committed-fragment provider binding. -/
theorem witness_realDecodedInstructionRows_opcodeNeEcall
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (real : (decoded.toChipRow witness.data).is_real = 1) :
    (programAccess (decoded.toChipRow witness.data).view).toRow.opcode ≠
      (((Opcode.ECALL).toNat : ℕ) : ZMod p) := by
  have shape := supportedChip_fetchDiscriminantShape decoded.chip
    (decodedInstructionRows_chip_mem witness.tables decodedMem) witness.data decoded.physical
    (decodedInstructionRow_constraints witness constraints decoded decodedMem)
    (decodedInstructionRow_byteGuarantees witness constraints balanced decoded decodedMem) real
  rw [show (((Opcode.ECALL).toNat : ℕ) : ZMod p) = (50 : ZMod p) from by norm_cast]
  exact shape

end SP1Clean.Soundness
