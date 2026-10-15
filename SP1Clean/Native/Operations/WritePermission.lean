import SP1Clean.FormalModel.Contracts.WritePermission
import SP1Clean.Native.Operations.AddressOrder

/-! # A native permission provider for ordinary and host memory writes

The provider authenticates an inclusive writable interval, checks the query's limbs, compares both
endpoints, and supplies one byte permission. Its only interaction is on the permission channel.
The deterministic constructor succeeds exactly for writable native addresses; all remaining local
cells come from Clean's exportable zero-test and bit-decomposition witness programs.
-/

namespace SP1Clean.WritePermissionProvider

open Circuit SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def ProverAssumptions (image : ProgramImage) (input : Inputs (ZMod p)) : Prop :=
  image.writePermissionTable.Spec input.interval ∧ Address.Bounded input.address ∧
    Address.toNat input.interval.lower ≤ Address.toNat input.address ∧
    Address.toNat input.address ≤ Address.toNat input.interval.upper

theorem ProverAssumptions.spec (image : ProgramImage) (input : Inputs (ZMod p))
    (assumptions : ProverAssumptions image input) : Spec image input :=
  ⟨assumptions.2.1, (image.writePermissionTable_sound _ assumptions.1).2.2 _
    assumptions.2.2.1 assumptions.2.2.2⟩

/-- The selector and field encoding are executable and take no proof arguments. -/
def populate? (image : ProgramImage) (address : ℕ) : Option (Inputs (ZMod p)) :=
  (image.writableIntervalAt? address).map fun interval =>
    ⟨Address.ofNat address, WritePermissionInterval.encode interval⟩

theorem populate?_sound (image : ProgramImage) (address : ℕ) (input : Inputs (ZMod p))
    (found : populate? image address = some input) :
    ProverAssumptions image input ∧ Address.toNat input.address = address := by
  obtain ⟨interval, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨member, contains⟩ := image.writableIntervalAt?_sound address interval selected
  obtain ⟨nonempty, upperBound, sound⟩ := image.writableIntervals_sound interval member
  have bounded := (sound address contains).1
  refine ⟨⟨(image.writePermissionTable_spec _).mpr ⟨interval, member, rfl⟩,
    Address.bounded_ofNat _, ?_, ?_⟩, Address.toNat_ofNat _ bounded⟩
  · change Address.toNat (Address.ofNat (p := p) interval.lower) ≤
      Address.toNat (Address.ofNat (p := p) address)
    rw [Address.toNat_ofNat _ (by omega), Address.toNat_ofNat _ bounded]
    exact contains.1
  · change Address.toNat (Address.ofNat (p := p) address) ≤
      Address.toNat (Address.ofNat (p := p) (interval.upper - 1))
    rw [Address.toNat_ofNat _ bounded, Address.toNat_ofNat _ (by omega)]
    have := contains.2
    omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem populate?_isSome_iff (image : ProgramImage) (address : ℕ) :
    (populate? (p := p) image address).isSome = true ↔
      address < 2 ^ 48 ∧ image.readOnly address = false := by
  simpa only [populate?, Option.isSome_map] using image.writableIntervalAt?_isSome_iff address

def main (image : ProgramImage) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  lookup image.writePermissionTable.toTable input.interval
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.address[0]
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.address[1]
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.address[2]
  assertion AddressOrder.circuit ⟨input.interval.lower, input.address⟩
  assertion AddressOrder.circuit ⟨input.address, input.interval.upper⟩
  channel.push input.address

instance elaborated (image : ProgramImage) :
    ElaboratedCircuit (ZMod p) Inputs unit (main image) := by elaborate_circuit

def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.write_permission"
  main := main image
  elaborated := elaborated image
  channelsWithRequirements := [channel.toRaw]
  Spec input _ _ := Spec image input
  ProverAssumptions input _ _ := ProverAssumptions image input
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, AddressOrder.circuit]
    rcases h_input with ⟨rfl, rfl, rfl⟩
    obtain ⟨member, low, middle, high, lower, upper⟩ := h_holds
    have bounded : Address.Bounded (input_var_address.map (Expression.eval env)) := by
      intro index
      fin_cases index
      · simpa using low
      · simpa using middle
      · simpa using high
    have ranges := image.writePermissionTable_sound _ member
    have permitted : Permitted image (input_var_address.map (Expression.eval env)) :=
      ⟨bounded, ranges.2.2 _ (lower ⟨ranges.1, bounded⟩) (upper ⟨bounded, ranges.2.1⟩)⟩
    exact ⟨permitted, fun _ _ => True.intro⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, AddressOrder.circuit, ProverAssumptions]
    rcases h_input with ⟨rfl, rfl, rfl⟩
    obtain ⟨member, bounded, lower, upper⟩ := h_assumptions
    have ranges := image.writePermissionTable_sound _ member
    exact ⟨member, by simpa using bounded 0, by simpa using bounded 1, by simpa using bounded 2,
      ⟨⟨ranges.1, bounded⟩, lower⟩, ⟨bounded, ranges.2.1⟩, upper⟩

end SP1Clean.WritePermissionProvider
