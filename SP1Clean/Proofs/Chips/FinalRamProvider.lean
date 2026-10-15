import SP1Clean.FormalModel.Contracts.FinalRam
import ToClean.Circuit.InteractionRecovery
import ToClean.Circuit.EmittedInteraction
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Native.Operations.AddressOperation

/-! # Canonical RAM finalization

The final record is pulled verbatim after checking its 48-bit address and eight-byte alignment.
The address gadget excludes SP1's reserved low region. The negative Memory emission assumes no
channel guarantee: values, timestamps, and last-access meaning follow from global grounding.
-/

namespace SP1Clean.FinalRamProvider

open Circuit SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def addressInput {R : Type} [Zero R] [One R] (record : MemoryMsg R) : AddressOperation.Inputs R :=
  ⟨MemoryBoundary.address record, #v[0, 0, 0, 0], 0, 0, 0, 1⟩

omit [Fact (2 ^ 17 < p)] in
private theorem zero_u64 : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;> norm_num

omit [Fact (2 ^ 17 < p)] in
theorem ram_canonical (record : MemoryMsg (ZMod p)) (bound : Word.isU64 (MemoryBoundary.address record))
    (output : Circuits.Types.AddressOperation (ZMod p))
    (checked : AddressOperation.Spec (addressInput record) output) : MemoryBoundary.RamFinalSpec record := by
  have fits : Word.toNat (MemoryBoundary.address record) < 2 ^ 64 := by
    rw [← Word.toBitVec64_toNat bound]
    exact BitVec.isLt _
  have facts := AddressOperation.validAddress_of_spec checked
  have zeroNat : Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by simp [Word.toNat]
  simp only [AddressOperation.ValidAddress, addressInput, zeroNat, add_zero,
    Nat.mod_eq_of_lt fits, ZMod.val_zero, mul_zero] at facts
  have packed : record.addr0.val + record.addr1.val * 2 ^ 16 + record.addr2.val * 2 ^ 32 =
      Word.toNat (MemoryBoundary.address record) := by
    simp [MemoryBoundary.address, Word.toNat]
  have location := MemoryBoundary.ram_location_of_key record _
    (by simpa only [Nat.mod_eq_of_lt facts.1] using facts.2.1)
    facts.1 (by simpa only [Nat.mod_eq_of_lt facts.1] using facts.2.2.symm) packed
  refine ⟨⟨location.1, bound, location.2.1⟩, ?_⟩
  rw [← location.2.1]
  simpa only [Nat.mod_eq_of_lt facts.1] using facts.2.1

omit [Fact (2 ^ 17 < p)] in
/-- Existing generic Memory consumers retain the canonical-address projection. -/
theorem canonical (record : MemoryMsg (ZMod p)) (bound : Word.isU64 (MemoryBoundary.address record))
    (output : Circuits.Types.AddressOperation (ZMod p))
    (checked : AddressOperation.Spec (addressInput record) output) : MemoryBoundary.CanonicalSpec record :=
  (ram_canonical record bound output checked).1

def main (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  assertion WordRangeCheck.circuit (MemoryBoundary.address input)
  let _ ← AddressOperation.circuit (addressInput input)
  memoryChannel.emit (-1) input
  return input

theorem main_memory_interactions (input : Var MemoryMsg (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.emitted (-1) input).toRaw] := by
  have rangeEmpty (n : ℕ) := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    WordRangeCheck.circuit memoryChannel.toRaw (MemoryBoundary.address input)
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil) (n := n)
  have addressEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    AddressOperation.circuit.base memoryChannel.toRaw (addressInput input) n (by
      simp [ AddressOperation.circuit, circuit_norm, memoryChannel, byteChannel])
  simp only [main, circuit_norm, rangeEmpty, List.nil_append]
  simp only [Operations.interactionsWith] at addressEmpty ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, addressEmpty, List.nil_append]

instance elaborated : ElaboratedCircuit (ZMod p) MemoryMsg MemoryMsg main where
  localLength _ := 68
  output input _ := input
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsLawful := by
    preserve_tactic_target
    intro input offset
    simp only [main, circuit_norm, WordRangeCheck.circuit, AddressOperation.circuit]

def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg MemoryMsg where
  name := "sp1.native.memory.final.ram"
  main
  elaborated := elaborated
  Spec input output _ := MemoryBoundary.RamFinalAtSpec (Word.toNat (MemoryBoundary.address input)) output
  ProverAssumptions input _ _ := Word.isU64 (MemoryBoundary.address input) ∧
    AddressOperation.Assumptions (addressInput input)
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, AddressOperation.circuit, addressInput,
      MemoryBoundary.address]
    have checked := (h_holds.2 ⟨h_holds.1 trivial, zero_u64, Or.inr rfl⟩).2.2.2 rfl
    exact ⟨ram_canonical ⟨input_clk_high, input_clk_low, input_addr0, input_addr1, input_addr2, input_value⟩
      (h_holds.1 trivial) _ checked, rfl⟩
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, AddressOperation.circuit, addressInput,
      MemoryBoundary.address]
    exact ⟨⟨trivial, h_assumptions.1⟩, h_assumptions.2⟩

/-- Bounded aligned guest RAM; value and timestamp currency are global obligations. -/
def Domain (record : MemoryMsg (ZMod p)) : Prop :=
  Word.isU64 (MemoryBoundary.address record) ∧
    2 ^ 16 ≤ Word.toNat (MemoryBoundary.address record) ∧
    Word.toNat (MemoryBoundary.address record) < 2 ^ 48 ∧
    Word.toNat (MemoryBoundary.address record) % 8 = 0

instance (record : MemoryMsg (ZMod p)) : Decidable (Domain record) := by
  unfold Domain Word.isU64
  infer_instance

/-- The internal address-gadget readiness condition is exactly the public semantic domain. -/
theorem proverAssumptions_iff (record : MemoryMsg (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : circuit.ProverAssumptions record data hint ↔ Domain record := by
  have zeroNat : Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by simp [Word.toNat]
  constructor
  · intro valid
    have fits : Word.toNat (MemoryBoundary.address record) < 2 ^ 64 := by
      rw [← Word.toBitVec64_toNat valid.1]
      exact BitVec.isLt _
    have address := valid.2
    simp only [AddressOperation.Assumptions, addressInput, zeroNat, add_zero,
      Nat.mod_eq_of_lt fits, ZMod.val_zero, mul_zero, true_implies] at address
    have upper := address.2.2.2.1
    refine ⟨valid.1, ?_, upper, ?_⟩
    · simpa only [Nat.mod_eq_of_lt upper] using address.2.2.2.2.2.2.2.1
    · simpa only [Nat.mod_eq_of_lt upper] using address.2.2.2.2.2.2.2.2.symm
  · intro valid
    refine ⟨valid.1, ?_⟩
    refine ⟨valid.1, zero_u64, Or.inr rfl, ?_, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_, ?_⟩ <;>
      simp only [addressInput, zeroNat, add_zero, ZMod.val_zero, mul_zero,
        Nat.mod_eq_of_lt (by have := valid.2.2.1; omega : Word.toNat (MemoryBoundary.address record) < 2 ^ 64),
        Nat.mod_eq_of_lt valid.2.2.1]
    · exact valid.2.2.1
    · exact fun _ => valid.2.1
    · exact valid.2.2.2.symm

/-- RAM finalization adds no static lookup table. -/
@[circuit_norm] theorem main_lookups (input : Var MemoryMsg (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups = [] := by
  simp [main, WordRangeCheck.circuit, AddressOperation.circuit, circuit_norm]

end SP1Clean.FinalRamProvider
