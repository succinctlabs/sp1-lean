import SP1Clean.Proofs.Chips.OrderedMemoryProvider
import SP1Clean.Proofs.Chips.SnapshotRamProvider
import SP1Clean.Proofs.Chips.SnapshotRegisterProvider

/-! # Ordered source records authenticated by an arbitrary local snapshot

The generic ordered-memory wrapper supplies address uniqueness and key binding. This module
instantiates it for the snapshot's register and RAM providers and constructs all internal columns.
The source snapshot and the ordering channel are instance parameters, independent of boot.
-/

namespace SP1Clean.OrderedSnapshotProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
abbrev Inputs := OrderedMemoryProvider.Inputs

variable {Payload : TypeMap} [ProvableType Payload]

def circuit (name : String) (snapshot : MemorySnapshot)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.SnapshotSpec snapshot output) :
    GeneralFormalCircuit (ZMod p) (Inputs Payload) MemoryMsg :=
  OrderedMemoryProvider.circuit name (MemoryBoundary.SnapshotSpec snapshot) provider binds
    (fun _ valid => valid.canonical)

def ramCircuit (name : String) (snapshot : MemorySnapshot) :
    GeneralFormalCircuit (ZMod p) (Inputs Word) MemoryMsg :=
  circuit name snapshot (SnapshotRamProvider.circuit snapshot) (fun _ _ _ valid => valid.1)

def registerCircuit (name : String) (snapshot : MemorySnapshot) :
    GeneralFormalCircuit (ZMod p) (Inputs SnapshotRegisterProvider.Inputs) MemoryMsg :=
  circuit name snapshot (SnapshotRegisterProvider.circuit snapshot) (fun _ _ _ valid => valid.1)

/-- Construct the control columns from the payload and its semantic address. -/
abbrev populate := @OrderedMemoryProvider.populate

/-- A provider that preserves its query admits the ordered wrapper's honest constructor.
In particular, the universally quantified internal output condition is discharged here rather
than left as a compiler-readiness condition on an execution. -/
theorem populate_assumptions (name : String) (snapshot : MemorySnapshot)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (query : Payload (ZMod p) → ℕ)
    (bindsAt : ∀ input output data,
      provider.Spec input output data → MemoryBoundary.SnapshotAtSpec snapshot (query input) output)
    (payload : Payload (ZMod p)) (previous : ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (prover : provider.ProverAssumptions payload data hint) (assumes : provider.Assumptions payload data)
    (bound : query payload < 2 ^ 48) (increases : previous < query payload + 1) :
    (circuit name snapshot provider (fun input output data spec => (bindsAt input output data spec).1)).ProverAssumptions
      (populate payload previous (query payload)) data hint := by
  exact OrderedMemoryProvider.populate_assumptions name (MemoryBoundary.SnapshotSpec snapshot) provider
    query bindsAt (fun _ valid => valid.canonical) payload previous data hint prover assumes bound increases

/-- The complete ordered RAM row constructor has no proof inputs or external column hints. -/
def populateRam? (previous address : ℕ) :
    Option (Inputs Word (ZMod p)) :=
  if previous < address + 1 then
    (SnapshotRamProvider.populate? address).map (fun payload => populate payload previous address)
  else none

theorem populateRam?_sound (name : String) (snapshot : MemorySnapshot) (previous address : ℕ)
    (input : Inputs Word (ZMod p))
    (found : populateRam? previous address = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (ramCircuit name snapshot).ProverAssumptions input data hint := by
  unfold populateRam? at found
  split at found
  next increases =>
    obtain ⟨payload, generated, rfl⟩ := Option.map_eq_some_iff.mp found
    have valid := SnapshotRamProvider.populate?_sound address payload generated
    have domain := (SnapshotRamProvider.populate?_isSome_iff (p := p) address).mp
      (by rw [generated]; rfl)
    have built := populate_assumptions name snapshot (SnapshotRamProvider.circuit snapshot)
      (fun input => Word.toNat input) (fun _ _ _ spec => spec)
      payload previous data hint ⟨valid.1, valid.2.1⟩ trivial
      (by rw [valid.2.2]; exact domain.2.1) (by rw [valid.2.2]; exact increases)
    simpa only [ramCircuit, valid.2.2] using built
  next invalid => contradiction

omit [Fact (2 ^ 17 < p)] in
theorem populateRam?_isSome_iff (previous address : ℕ) :
    (populateRam? (p := p) previous address).isSome = true ↔
      previous < address + 1 ∧ 2 ^ 16 ≤ address ∧ address < 2 ^ 48 ∧ address % 8 = 0 := by
  simp only [populateRam?]
  split
  next increases => simp only [Option.isSome_map, SnapshotRamProvider.populate?_isSome_iff, increases, true_and]
  next invalid => simp only [Option.isSome_none, Bool.false_eq_true, invalid, false_and]

/-- All register values come from the snapshot; only the semantic index and predecessor are supplied. -/
theorem populateRegister_assumptions (name : String) (snapshot : MemorySnapshot)
    (index : BitVec 5) (previous : ℕ) (increases : previous < index.toNat + 1)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (registerCircuit name snapshot).ProverAssumptions
      (populate (SnapshotRegisterProvider.populate snapshot index) previous index.toNat) data hint := by
  have indexEq := snapshot.registerRow_index (p := p) index
  have built := populate_assumptions name snapshot (SnapshotRegisterProvider.circuit snapshot)
    (fun input => input.index.val) (fun _ _ _ spec => spec)
    (SnapshotRegisterProvider.populate snapshot index) previous data hint
    (SnapshotRegisterProvider.populate_assumptions snapshot index data hint) trivial
    (by rw [indexEq]; have := index.isLt; omega) (by rw [indexEq]; exact increases)
  simpa only [registerCircuit, indexEq] using built

end SP1Clean.OrderedSnapshotProvider
