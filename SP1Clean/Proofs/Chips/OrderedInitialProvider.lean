import SP1Clean.FormalModel.Contracts.OrderedInitialProvider
import SP1Clean.Proofs.Chips.OrderedSnapshotProvider
import SP1Clean.Proofs.Chips.InitialRamProvider
import SP1Clean.Proofs.Chips.InitialRegisterProvider

/-! # Binding initial records to their ordered keys

This wrapper composes any proved initial-memory provider with an ordered boundary link. Its
current key is constrained to the provider's canonical address plus one. Zero is therefore
available as a fixed start sentinel, including when the first record initializes register x0.
The increment cannot wrap: canonical memory addresses fit in 48 bits.
-/

namespace SP1Clean.OrderedInitialProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
variable {Payload : TypeMap} [ProvableType Payload]

abbrev main := @OrderedMemoryProvider.main

/-- The wrapper's control interactions are precisely the checked predecessor/current pair.
The provider's interface must omit this private channel; its Memory/Byte effects remain intact. -/
theorem main_interactions (name : String) (distinct : name ≠ "SP1Byte")
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (privateChannel : (OrderedBoundary.channel name).toRaw ∉ provider.channels)
    (input : Var (Inputs Payload) (ZMod p)) (offset : ℕ) :
    ((main name provider input).operations offset).interactionsWith (OrderedBoundary.channel name).toRaw =
      [((OrderedBoundary.channel name).pulled input.link.previous).toRaw,
       ((OrderedBoundary.channel name).pushed input.link.current).toRaw] :=
  OrderedMemoryProvider.main_interactions name distinct provider privateChannel input offset

def circuit (name : String) (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.InitialSpec image output) :
    GeneralFormalCircuit (ZMod p) (Inputs Payload) MemoryMsg :=
  OrderedMemoryProvider.circuit name (MemoryBoundary.InitialSpec image) provider binds
    (fun _ valid => valid.canonical)

/-- Both classes of initial records share one address-ordering channel. -/
def channelName : String := "SP1NativeMemoryInitOrder"

def ramCircuit (image : ProgramImage) :
    GeneralFormalCircuit (ZMod p) (Inputs Word) MemoryMsg :=
  circuit channelName image (InitialRamProvider.circuit image) (fun _ _ _ valid => valid.1)

def registerCircuit (image : ProgramImage) :
    GeneralFormalCircuit (ZMod p) (Inputs field) MemoryMsg :=
  circuit channelName image (InitialRegisterProvider.circuit image) (fun _ _ _ valid => valid.1)

/-- Construct the control columns from the payload and its semantic address. -/
abbrev populate := @OrderedMemoryProvider.populate

/-- A provider that preserves its query admits the ordered wrapper's honest constructor.
In particular, the universally quantified internal output condition is discharged here rather
than left as a compiler-readiness condition on an execution. -/
theorem populate_assumptions (name : String) (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (query : Payload (ZMod p) → ℕ)
    (bindsAt : ∀ input output data,
      provider.Spec input output data → MemoryBoundary.InitialAtSpec image (query input) output)
    (payload : Payload (ZMod p)) (previous : ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (prover : provider.ProverAssumptions payload data hint) (assumes : provider.Assumptions payload data)
    (bound : query payload < 2 ^ 48) (increases : previous < query payload + 1) :
    (circuit name image provider (fun input output data spec => (bindsAt input output data spec).1)).ProverAssumptions
      (populate payload previous (query payload)) data hint := by
  exact OrderedMemoryProvider.populate_assumptions name (MemoryBoundary.InitialSpec image) provider
    query bindsAt (fun _ valid => valid.canonical) payload previous data hint prover assumes bound increases

/-- The shared address-only constructor satisfies the boot provider contract. -/
theorem populateRam?_sound (image : ProgramImage) (previous address : ℕ)
    (input : Inputs Word (ZMod p))
    (found : OrderedSnapshotProvider.populateRam? previous address = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (ramCircuit image).ProverAssumptions input data hint := by
  unfold OrderedSnapshotProvider.populateRam? at found
  split at found
  next increases =>
    obtain ⟨payload, generated, rfl⟩ := Option.map_eq_some_iff.mp found
    have valid := SnapshotRamProvider.populate?_sound address payload generated
    have domain := (SnapshotRamProvider.populate?_isSome_iff (p := p) address).mp
      (by rw [generated]; rfl)
    have built := populate_assumptions channelName image (InitialRamProvider.circuit image)
      (fun input => Word.toNat input) (fun _ _ _ spec => spec)
      payload previous data hint ⟨valid.1, valid.2.1⟩ trivial
      (by rw [valid.2.2]; exact domain.2.1) (by rw [valid.2.2]; exact increases)
    simpa only [ramCircuit, valid.2.2] using built
  next invalid => contradiction

/-- A register needs only its index and the preceding key; x0 uses current key one. -/
theorem populateRegister_assumptions (image : ProgramImage) (index : BitVec 5) (previous : ℕ)
    (increases : previous < index.toNat + 1) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (registerCircuit image).ProverAssumptions
      (populate (InitialRegisterProvider.populate index) previous index.toNat) data hint := by
  have indexP : index.toNat < p := by
    have := index.isLt; have := Fact.out (p := 2 ^ 17 < p); omega
  have indexEq : (InitialRegisterProvider.populate (p := p) index).val = index.toNat :=
    ZMod.val_natCast_of_lt indexP
  have built := populate_assumptions channelName image (InitialRegisterProvider.circuit image)
    (fun index => index.val) (fun _ _ _ spec => spec)
    (InitialRegisterProvider.populate index) previous data hint
    (InitialRegisterProvider.populate_assumptions index) trivial
    (by rw [indexEq]; have := index.isLt; omega) (by rw [indexEq]; exact increases)
  simpa only [registerCircuit, indexEq] using built

end SP1Clean.OrderedInitialProvider
