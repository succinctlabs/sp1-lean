import SP1Clean.FormalModel.Contracts.MemoryBoundary
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Model.Channels
import Clean.Gadgets.Bits
import Clean.Utils.Tactics

/-! # Canonical zero-register initialization

Each row checks a five-bit register index and emits its zero-time, zero-value Memory record.
The value and clock are circuit constants, so a witness cannot choose its own initial registers.
Each present row has multiplicity one; global boundary ordering supplies uniqueness.
-/

namespace SP1Clean.InitialRegisterProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
private theorem indexBound : 2 ^ 5 < p := by
  have := Fact.out (p := 2 ^ 17 < p)
  omega

def message {R : Type} [Zero R] (index : R) : MemoryMsg R :=
  ⟨0, 0, index, 0, 0, #v[0, 0, 0, 0]⟩

omit [Fact (2 ^ 17 < p)] in
/-- Every checked index gives an authentic boot-register record, including x0. -/
theorem initialSpec (image : ProgramImage) (index : ZMod p) (bound : index.val < 32) :
    MemoryBoundary.InitialAtSpec image index.val (message index) := by
  refine ⟨?_, by simp [MemoryBoundary.address, message, Word.toNat]⟩
  let register := BitVec.ofNat 5 index.val
  have decoded : MemoryMsg.locOf (message index) = MemLoc.reg register := by
    simp only [MemoryMsg.locOf, message, bound, and_self, if_true, register]
  have zero : Word.toBitVec64 (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by
    simp [Word.toBitVec64, Word.toNat]
  refine ⟨?_, by simp [MemoryMsg.ClkBound, message],
    by simp [MemoryMsg.timeNat, clkNat, message], ?_, ?_, ?_⟩
  · apply Word.isU64_of_cases <;> norm_num [message]
  · rw [decoded]
    trivial
  · exact (congrArg (locContent image.initialSailState) decoded).trans
      ((image.initialSailState_registersZero register).trans (congrArg some zero.symm))
  · refine ⟨?_, ?_⟩
    · apply Word.isU64_of_cases
      · simpa only [MemoryBoundary.address, message, circuit_norm] using
          lt_trans bound (by norm_num : 32 < 2 ^ 16)
      all_goals norm_num [MemoryBoundary.address, message]
    · rw [decoded]
      simp only [MemoryBoundary.address, message, Word.toNat, circuit_norm,
        ZMod.val_zero, zero_mul, add_zero, MemLoc.busAddress, register,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

def main (index : Var field (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  assertion (Gadgets.ToBits.rangeCheck 5 indexBound) index
  let record := message index
  memoryChannel.push record
  return record

theorem main_memory_interactions (index : Var field (ZMod p)) (offset : ℕ) :
    ((main index).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pushed (message index)).toRaw] := by
  have rangeEmpty (n : ℕ) := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck 5 indexBound) memoryChannel.toRaw index
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
    (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil) (n := n)
  simp only [main, circuit_norm, rangeEmpty, List.nil_append]

def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) field MemoryMsg where
  name := "sp1.native.memory.initial.registers"
  main
  Spec index output _ := MemoryBoundary.InitialAtSpec image index.val output
  ProverAssumptions index _ _ := index.val < 32
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, message]
    have valid := initialSpec image input h_holds
    exact ⟨valid, fun _ _ => ⟨valid.1.1, valid.1.2.1⟩⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, message]
    exact h_assumptions

/-- Register-provider inputs are constructed directly from the semantic register index. -/
def populate (index : BitVec 5) : ZMod p := index.toNat

theorem populate_assumptions (index : BitVec 5) : (populate (p := p) index).val < 32 := by
  have bound : index.toNat < p := lt_trans index.isLt indexBound
  simpa only [populate, ZMod.val_natCast_of_lt bound] using index.isLt

end SP1Clean.InitialRegisterProvider
