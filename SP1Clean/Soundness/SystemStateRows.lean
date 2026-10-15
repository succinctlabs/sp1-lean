import SP1Clean.Soundness.SystemMemoryRows

/-! # Exact State pairs at physical system tables

These projections retain active row occurrences and remove only zero-multiplicity pairs. They
depend on the component carried by a physical table, independently of any ensemble layout.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- One State transition, including its exact physical selector. -/
def statePairInteractions (gate : ZMod p) (edge : StateMsg (ZMod p) × StateMsg (ZMod p)) :
    List (TypedInteraction (stateChannel (p := p))) :=
  [TypedInteraction.pulledIfValue stateChannel gate edge.1,
   TypedInteraction.pushedIfValue stateChannel gate edge.2]

/-- Removing disabled State pairs preserves the produced and consumed lists with multiplicity. -/
theorem statePairs_projection {α : Type*} (rows : List α) (gate : α → ZMod p)
    (edge : α → StateMsg (ZMod p) × StateMsg (ZMod p))
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    producedMessages (rows.flatMap (fun row => statePairInteractions (gate row) (edge row))) =
        ((rows.filter (fun row => gate row = 1)).map edge).map Prod.snd ∧
    consumedMessages (rows.flatMap (fun row => statePairInteractions (gate row) (edge row))) =
        ((rows.filter (fun row => gate row = 1)).map edge).map Prod.fst := by
  induction rows with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rows ih =>
    have tail := ih (fun r member => binary r (List.mem_cons_of_mem _ member))
    simp only [List.flatMap_cons, producedMessages_append, consumedMessages_append, tail.1, tail.2]
    rcases binary row List.mem_cons_self with zero | one
    · rw [statePairInteractions, zero, producedMessages_statePair_zero, consumedMessages_statePair_zero]
      simp [zero]
    · rw [statePairInteractions, one, producedMessages_statePair_one, consumedMessages_statePair_one]
      simp [one]

/-- Every gated State pair has signed-unit or zero multiplicities. -/
theorem statePairs_signedBinary {α : Type*} (rows : List α) (gate : α → ZMod p)
    (edge : α → StateMsg (ZMod p) × StateMsg (ZMod p))
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    ∀ interaction ∈ rows.flatMap (fun row => statePairInteractions (gate row) (edge row)),
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  intro interaction member
  obtain ⟨row, rowMem, member⟩ := List.mem_flatMap.mp member
  exact statePair_signed_binary (gate row) (binary row rowMem) (edge row).1 (edge row).2 interaction member

/-- A physical StateBump table's selector is binary from local constraints and Byte guarantees. -/
theorem stateBumpRow_binary (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := StateBumpChip.circuit }) (constraints : table.Constraints data)
    (byte : table.ChannelGuarantees data byteChannel.toRaw) (physical : Array (ZMod p))
    (member : physical ∈ table.table) :
    (stateBumpRow data physical).is_real = 0 ∨ (stateBumpRow data physical).is_real = 1 :=
  (stateBumpTable_spec_of_component table data component constraints byte physical member).1

end SP1Clean.Soundness
