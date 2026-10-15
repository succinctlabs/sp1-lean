import SP1Clean.Soundness.HostFinalMemoryByte
import SP1Clean.Soundness.FinalMemoryCheckSoundness

/-! # The installed Memory boundary as a physical proof view

The seven tables below are selected from the actual host witness. They reuse the existing
boundary assembly, contracts and decoder. Byte guarantees are inherited from the enclosing
ledger. Its canonical data is derived from these seven tables; Byte predicates transport separately. This view need not have balanced Byte or Memory channels.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalViewLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalViewClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : UniqueNames image source target others resources}

/-- The original final tables, target consumers and fixed membership providers, without reconstructed rows. -/
def boundaryTables
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :=
  [(finalSlot ⟨0, by decide⟩).table witness, (finalSlot ⟨1, by decide⟩).table witness,
   (finalSlot ⟨2, by decide⟩).table witness,
   (checkSlot ⟨0, by decide⟩).table witness, (checkSlot ⟨1, by decide⟩).table witness,
   (checkSlot ⟨2, by decide⟩).table witness, (checkSlot ⟨3, by decide⟩).table witness]

/-- Every boundary table is an unchanged physical table of the complete host assembly. -/
theorem boundaryTables_subset
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    boundaryTables witness ⊆ witness.tables := by
  intro table member
  simp only [boundaryTables, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact TableSlot.table_mem _ witness

/-- Reuse the boundary assembly with canonical data derived from its seven physical tables. -/
def boundaryWitness
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    EnsembleWitness (FinalMemoryChecks.ensemble (p := p) source.sail.memorySnapshot target [] []
      (FinalMemoryChecks.empty_unique_names target)) :=
  EnsembleWitness.ofTables _ (boundaryTables witness) () (by
    simp only [boundaryTables, List.map_cons, List.map_nil, TableSlot.table_component]
    rfl)

/-- Decode the installed final inventory through the existing ordered boundary decoder. -/
def finalRecords
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    List (MemoryMsg (ZMod p)) := FinalMemoryChecks.records (boundaryWitness witness)

/-- The proof view owns no independently supplied rows. -/
@[simp] theorem boundaryWitness_tables
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    (boundaryWitness witness).tables = boundaryTables witness := rfl

/-- Row assertions survive selection of the boundary inventory. -/
theorem boundaryWitness_constraints
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (checked : witness.Constraints) : (boundaryWitness witness).Constraints := by
  intro table member row rowMember
  apply FinalMemoryChecks.component_constraints_setData table.component
    (EnsembleWitness.mem_component_of_mem member)
  exact checked table (boundaryTables_subset witness member) row rowMember

/-- Byte predicates depend on the retained messages, not the selected canonical data map. -/
theorem boundaryWitness_byte
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (guarantees : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ table ∈ (boundaryWitness witness).tables,
      table.ChannelGuarantees (boundaryWitness witness).data byteChannel.toRaw := by
  intro table member row rowMember interaction emitted same
  have inherited := guarantees table (boundaryTables_subset witness member) row rowMember interaction emitted same
  have eval_eq : Expression.eval (Environment.fromArray row witness.data) =
      Expression.eval (Environment.fromArray row (boundaryWitness witness).data) :=
    funext fun expression => Expression.eval_congr
      (env := Environment.fromArray row witness.data)
      (env' := Environment.fromArray row (boundaryWitness witness).data) rfl expression
  rcases interaction with ⟨declared, mult, msg, assume⟩
  cases same
  simpa only [AbstractInteraction.Guarantees, eval_eq, byteChannel, Channel.toRaw] using inherited

end SP1Clean.Soundness.HostFinalMemory
