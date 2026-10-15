import SP1Clean.Soundness.FinalMemoryEnsemble
import SP1Clean.Soundness.FinalReceiptEnsemble

/-! # Receipt-bearing native finalizers

Both ordered finalizer tables publish their complete Memory records. Their physical rows,
Memory pulls, ordering interactions, Byte demand, and terminal table are unchanged. The
original `FinalMemoryEnsemble` remains the sole decoder of the combined final inventory.

Auxiliary target-value consumers close the two new channels. Installing their Byte closure
and the complete change-coverage verifier is a separate obligation of the enclosing machine.
-/

namespace SP1Clean.Soundness.FinalMemoryReceipts

open Circuit Air.Flat Channels OrderedFinalProvider

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Add the register receipts at the existing typed register slot. -/
def withRegisters (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : (((FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup) :=
  FinalReceiptEnsemble.install (FinalMemoryEnsemble.ensemble auxiliary channels names) false registerCircuit
    ⟨⟨0, by simp [FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble,
      OrderedBoundaryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.views,
      FinalMemoryEnsemble.inventory]⟩, rfl⟩

/-- Both receipt channels are registered; the original three tables keep their positions. -/
def ensemble (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : (((FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup) :=
  FinalReceiptEnsemble.install (withRegisters auxiliary channels names) true ramCircuit
    ⟨⟨1, by simp [withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
      FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble,
      OrderedBoundaryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.views,
      FinalMemoryEnsemble.inventory]⟩, rfl⟩

variable {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
variable {names : (((FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}

/-- Forget only the RAM receipt, retaining the register receipt. -/
def registerWitness (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    EnsembleWitness (withRegisters auxiliary channels names) :=
  FinalReceiptEnsemble.project witness

@[simp] theorem registerWitness_data (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (registerWitness witness).data = witness.data := FinalReceiptEnsemble.project_data witness

/-- The unchanged ordered inventory, as a physical proof view of the installed finalizers. -/
def original (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble auxiliary channels names) :=
  FinalReceiptEnsemble.project (registerWitness witness)

/-- Reuse the existing witness arrays when constructing the two receipt-bearing tables. -/
def lift (witness : EnsembleWitness (FinalMemoryEnsemble.ensemble auxiliary channels names)) :
    EnsembleWitness (ensemble auxiliary channels names) :=
  FinalReceiptEnsemble.lift (FinalReceiptEnsemble.lift witness)

/-- Forgetting both receipts keeps every physical row array of the boundary inventory. -/
theorem original_rows (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (original witness).tables.map (·.table) = witness.tables.map (·.table) :=
  (FinalReceiptEnsemble.project_rows (registerWitness witness)).trans
    (FinalReceiptEnsemble.project_rows witness)

/-- The original inventory retains the actual shared environment. -/
theorem original_data (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (original witness).data = witness.data :=
  (FinalReceiptEnsemble.project_data (registerWitness witness)).trans
    (FinalReceiptEnsemble.project_data witness)

/-- Receipt publication adds no row-construction obligation to the existing finalizers. -/
theorem lift_constraints (witness : EnsembleWitness (FinalMemoryEnsemble.ensemble auxiliary channels names))
    (constraints : witness.Constraints) : (lift witness).Constraints :=
  FinalReceiptEnsemble.lift_constraints _
    (FinalReceiptEnsemble.lift_constraints witness constraints)

/-- Both wrappers preserve the complete original assertion and lookup systems. -/
theorem original_constraints (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (original witness).Constraints ↔ witness.Constraints :=
  (FinalReceiptEnsemble.project_constraints (registerWitness witness)).trans
    (FinalReceiptEnsemble.project_constraints witness)

/-- Original channels retain their complete physical ledgers, with multiplicities unchanged. -/
theorem original_interactions (witness : EnsembleWitness (ensemble auxiliary channels names))
    (channel : RawChannel (ZMod p))
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw) :
    (original witness).interactionsWith channel = witness.interactionsWith channel :=
  (FinalReceiptEnsemble.project_interactions (registerWitness witness) channel registers).trans
    (FinalReceiptEnsemble.project_interactions witness channel ram)

/-- The physical register table, without copying or rebuilding any row. -/
def registerTable (witness : EnsembleWitness (ensemble auxiliary channels names)) : Table (ZMod p) :=
  FinalReceiptEnsemble.table (registerWitness witness)

/-- The physical RAM table, without copying or rebuilding any row. -/
def ramTable (witness : EnsembleWitness (ensemble auxiliary channels names)) : Table (ZMod p) :=
  FinalReceiptEnsemble.table witness

/-- Receipt decoding is exactly the existing ordered final inventory, in its physical order. -/
theorem records_eq (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    FinalMemoryEnsemble.records (original witness) =
      FinalReceiptEnsemble.records (registerWitness witness) ++ FinalReceiptEnsemble.records witness := by
  rw [FinalMemoryEnsemble.records_eq]
  simp only [FinalReceiptEnsemble.records, original_data witness]
  simp only [original, registerWitness, FinalReceiptEnsemble.project, EnsembleWitness.ofTables_tables,
    FinalReceiptEnsemble.table, TableSlot.table, FinalReceiptEnsemble.slot, List.getElem_set_self,
    List.getElem_set_ne (by decide : 0 ≠ 1), List.getElem_set_ne (by decide : 1 ≠ 0), Table.withComponent_rows]
  congr 1
  apply List.map_congr_left
  intro row _
  exact Component.rowOutput_congr _ rfl

/-- The receipt records are precisely the actual Memory pulls of the original three final tables. -/
theorem memory_receipts (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    ((original witness).tables.take 3).flatMap (·.interactionsWith (original witness).data memoryChannel.toRaw) =
      (FinalReceiptEnsemble.records (registerWitness witness) ++ FinalReceiptEnsemble.records witness).map
        (memoryChannel.emittedValue (-1)) := by
  rw [← records_eq]
  exact FinalMemoryEnsemble.memory_interactions_eq (original witness)

private theorem register_silent :
    (FinalMemoryValue.channel (p := p) false).toRaw ∉ registerCircuit.channels := by
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change false = true at present
  contradiction

private theorem ram_silent :
    (FinalMemoryValue.channel (p := p) true).toRaw ∉ ramCircuit.channels := by
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change false = true at present
  contradiction

/-- Exact register-receipt accounting includes every finalizer's value and private timestamp. -/
theorem register_receipts (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (registerTable witness).interactionsWith witness.data (FinalMemoryValue.channel false).toRaw =
      (FinalReceiptEnsemble.records (registerWitness witness)).map
        (FinalMemoryValue.channel false).pushedValue :=
by
  have result := FinalReceiptEnsemble.table_receipts (registerWitness witness) register_silent
  have same := congrArg (fun data : ProverData (ZMod p) =>
    (registerTable witness).interactionsWith data (FinalMemoryValue.channel false).toRaw)
    (registerWitness_data witness)
  exact same.symm.trans result

/-- Exact RAM-receipt accounting includes every finalizer's value and private timestamp. -/
theorem ram_receipts (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    (ramTable witness).interactionsWith witness.data (FinalMemoryValue.channel true).toRaw =
      (FinalReceiptEnsemble.records witness).map (FinalMemoryValue.channel true).pushedValue :=
  FinalReceiptEnsemble.table_receipts _ ram_silent

/-- The installed RAM receipts retain the actual finalizer's RAM domain. Only Byte guarantees
are needed locally; Memory values and timestamps still come from the global grounding proof. -/
theorem ram_records_spec (witness : EnsembleWitness (ensemble auxiliary channels names))
    (constraints : witness.Constraints)
    (bytes : (ramTable witness).ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ record ∈ FinalReceiptEnsemble.records witness, MemoryBoundary.RamFinalSpec record := by
  intro record member
  obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp member
  have checks := constraints (ramTable witness)
    (List.getElem_mem _) row rowMem
  have guarantees := bytes row rowMem
  change (FinalReceiptEnsemble.table witness).component.operations.ConstraintsHold _ at checks
  change (FinalReceiptEnsemble.table witness).component.operations.ChannelGuarantees _ _ at guarantees
  rw [FinalReceiptEnsemble.table_component witness] at checks guarantees
  rw [Operations.ConstraintsHold, FinalMemoryReceipt.constraints,
    FinalMemoryReceipt.lookups] at checks
  have providerBytes := Operations.channelGuarantees_of_interactionsWith_subset
    ({ circuit := ramCircuit } : Component (ZMod p)).operations
    ({ circuit := FinalMemoryReceipt.circuit true ramCircuit } : Component (ZMod p)).operations
    byteChannel.toRaw (by
      rw [FinalMemoryReceipt.interactions true ramCircuit byteChannel.toRaw (by
        intro equal
        have names := congrArg RawChannel.name equal
        change "SP1Byte" = "SP1FinalRamValue" at names
        contradiction)]
      exact List.Subset.refl _) _ guarantees
  exact (FinalMemoryEnsemble.view_spec .ram _ checks providerBytes).1

/-- The only added occurrences are one receipt for each register row and one for each RAM row. -/
theorem receipt_cost (witness : EnsembleWitness (ensemble auxiliary channels names)) :
    ((registerTable witness).interactionsWith witness.data (FinalMemoryValue.channel false).toRaw).length +
      ((ramTable witness).interactionsWith witness.data (FinalMemoryValue.channel true).toRaw).length =
      (registerTable witness).length + (ramTable witness).length := by
  rw [register_receipts, ram_receipts]
  simp only [FinalReceiptEnsemble.records, List.length_map, registerTable, ramTable, Table.length]

end SP1Clean.Soundness.FinalMemoryReceipts
