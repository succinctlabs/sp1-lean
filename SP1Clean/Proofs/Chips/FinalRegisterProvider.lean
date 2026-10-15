import ToClean.Gadgets.LookupProjection
import SP1Clean.FormalModel.Contracts.MemoryBoundary
import ToClean.Circuit.InteractionRecovery
import ToClean.Circuit.EmittedInteraction
import SP1Clean.Model.Channels
import Clean.Gadgets.Bits
import Clean.Utils.Tactics

/-! # Canonical register finalization

Each physical row consumes one final Memory record. Its address must be a five-bit register index;
the higher address limbs must vanish. The negative emission assumes no Memory guarantee, so the
shared ordering wrapper can establish uniqueness before values and clocks are grounded globally.
-/

namespace SP1Clean.FinalRegisterProvider

open Circuit SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
private theorem indexBound : 2 ^ 5 < p := by
  have := Fact.out (p := 2 ^ 17 < p)
  omega

omit [Fact (2 ^ 17 < p)] in
theorem canonical (record : MemoryMsg (ZMod p)) (small : record.addr0.val < 32)
    (one : record.addr1 = 0) (two : record.addr2 = 0) : MemoryBoundary.CanonicalSpec record := by
  have decoded : MemoryMsg.locOf record = .reg (BitVec.ofNat 5 record.addr0.val) := by
    simp only [MemoryMsg.locOf, small, one, two, and_self, if_true]
  refine ⟨by rw [decoded]; trivial, ?_, ?_⟩
  · apply Word.isU64_of_cases
    · exact lt_trans small (by norm_num)
    all_goals simp [MemoryBoundary.address, one, two]
  · rw [decoded]
    simp [MemoryBoundary.address, Word.toNat, one, two, MemLoc.busAddress,
      Nat.mod_eq_of_lt small]

def main (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  assertion (Gadgets.ToBits.rangeCheck 5 indexBound) input.addr0
  assertZero input.addr1
  assertZero input.addr2
  memoryChannel.emit (-1) input
  return input

theorem main_memory_interactions (input : Var MemoryMsg (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.emitted (-1) input).toRaw] := by
  have rangeEmpty (n : ℕ) := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck 5 indexBound) memoryChannel.toRaw input.addr0
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil) (n := n)
  simp only [main, circuit_norm, rangeEmpty, List.nil_append]

/-- The semantic domain of a register finalization row. -/
def Domain (record : MemoryMsg (ZMod p)) : Prop :=
  record.addr0.val < 32 ∧ record.addr1 = 0 ∧ record.addr2 = 0

instance (record : MemoryMsg (ZMod p)) : Decidable (Domain record) := by
  unfold Domain
  infer_instance

instance elaborated : ElaboratedCircuit (ZMod p) MemoryMsg MemoryMsg main where
  localLength _ := 5
  output input _ := input
  channelsWithGuarantees := []

def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg MemoryMsg where
  name := "sp1.native.memory.final.registers"
  main
  elaborated := elaborated
  Spec input output _ := MemoryBoundary.FinalAtSpec (Word.toNat (MemoryBoundary.address input)) output
  ProverAssumptions input _ _ := Domain input
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, MemoryBoundary.address]
    exact ⟨canonical ⟨input_clk_high, input_clk_low, input_addr0, input_addr1, input_addr2, input_value⟩
      h_holds.1 h_holds.2.1 h_holds.2.2, rfl⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact h_assumptions

/-- Register finalization adds no static lookup table. -/
@[circuit_norm] theorem main_lookups (input : Var MemoryMsg (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups = [] := by
  simp [main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]

end SP1Clean.FinalRegisterProvider
