import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Soundness.FinalMemoryChecks

/-! # Complete target Memory checks in the physical host assembly

The existing host assembly keeps every CPU, host, source and final-order table. The target consumers and fixed membership providers are appended to its resource block, the original finalizers publish their
full records, and the canonical change demand runs once in the verifier. These additions use
existing circuits and typed physical slots. Receipt projection preserves every row and canonical
data; selecting a smaller inventory requires separate constraint and channel transport.
Grounding and complete endpoint agreement consume the channel facts separately.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalMemoryLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalMemoryClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The complete physical host inventory has distinct canonical names before receipt wrapping. -/
abbrev UniqueNames (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) : Prop :=
  ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: others).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ (resources ++ FinalMemoryChecks.checkTables target)))).map
      (·.circuit.name)).Nodup

/-- The concrete host registry and both target validators have distinct canonical names. -/
theorem source_unique_names (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot) :
    UniqueNames (p := p) image source target HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) := by
  let original := HostLocalCore.tables (p := p) image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ HostHintReadLocal.sourceResources source.host.io.hints))
  have split : ((HostLocalCore.tables (p := p) image source
      ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
        (HostHintReadHandoff.wordResources ++ (HostHintReadLocal.sourceResources source.host.io.hints ++
          FinalMemoryChecks.checkTables target)))).map (·.circuit.name)) =
      original.map (·.circuit.name) ++ (FinalMemoryChecks.checkTables (p := p) target).map (·.circuit.name) := by
    simp only [original, HostLocalCore.tables_names, List.map_append, List.append_assoc]
  rw [UniqueNames, split, List.nodup_append]
  refine ⟨HostHintReadLocal.source_unique_names image source source.host.io.hints,
    ?_, ?_⟩
  · simp only [FinalMemoryChecks.checkTables, List.map_cons, List.map_nil,
      StaticTable.component, StaticTable.provider, FinalRegisterValue.membership]
    exact of_decide_eq_true rfl
  · have fresh : (original.map (·.circuit.name)).all
        (fun name => !((FinalMemoryChecks.checkTables (p := p) target).map (·.circuit.name)).contains name) = true := by
      simp only [original, HostLocalCore.tables_names, ProtectedLocalCore.tables_names,
        LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
        SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
        MemorySnapshot.registerTable, StaticTable.ofRows,
        FinalMemoryChecks.checkTables, FinalRegisterValue.membership]
      rfl
    intro a old b added same
    have absent := List.all_eq_true.mp fresh a old
    rw [List.contains_iff_mem.mpr (same.symm ▸ added)] at absent
    exact Bool.noConfusion absent

/-- Install the existing target consumers in the host resource block. Their channels are
registered by the same host assembly as every other resource. -/
@[reducible] def base (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : UniqueNames image source target others resources) : Ensemble (ZMod p) SP1PublicIO :=
  HostHintQueueBoundary.ensemble image source final bankFinal others
    (resources ++ FinalMemoryChecks.checkTables target) channels names

/-- The original core and handler positions are unchanged; four resource tables are added. -/
theorem base_tables_length (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : UniqueNames image source target others resources) :
    (base image source target final bankFinal others resources channels names).tables.length =
      69 + others.length + resources.length := by
  simp only [base, HostHintQueueBoundary.ensemble, HaltPadding.install, Ensemble.replaceComponent,
    ClosedVerifier.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
    HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble, List.length_set]
  rw [HostLocalCore.tables_length]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    HostHintReadHandoff.wordResources, FinalMemoryChecks.checkTables]
  omega

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : UniqueNames image source target others resources}

private theorem base_boundary_component (index : Fin 6) :
    (base image source target final bankFinal others resources channels names).tables[index.val]'(by
      rw [base_tables_length]; omega) =
      (LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; omega) := by
  change ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: others).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ (resources ++ FinalMemoryChecks.checkTables target)))).set
        57 HaltPaddingChip.component)[index.val]'(by
          rw [List.length_set, HostLocalCore.tables_length]; have := index.isLt; omega) = _
  rw [List.getElem_set_ne (by have := index.isLt; omega : 57 ≠ index.val),
    HostLocalCore.core_component image source _ ⟨index.val, by have := index.isLt; omega⟩,
    if_neg (by have := index.isLt; omega : 58 ≠ index.val)]
  simp only [ProtectedLocalCore.tables]
  rw [List.getElem_append_left (by simp only [List.length_set, LocalCore.tables_length]; have := index.isLt; omega)]
  rw [List.getElem_set_ne (by have := index.isLt; omega : 28 ≠ index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 27 ≠ index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 26 ≠ index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 25 ≠ index.val)]

private theorem base_register_component :
    (base image source target final bankFinal others resources channels names).tables[3]'(by rw [base_tables_length]; omega) =
      { circuit := OrderedFinalProvider.registerCircuit } :=
  (base_boundary_component (index := ⟨3, by decide⟩)).trans (by rfl)

private theorem base_ram_component :
    (base image source target final bankFinal others resources channels names).tables[4]'(by rw [base_tables_length]; omega) =
      { circuit := OrderedFinalProvider.ramCircuit } :=
  (base_boundary_component (index := ⟨4, by decide⟩)).trans (by rfl)

/-- Publish complete receipts at the original register-finalizer position. -/
@[reducible] def withRegisters (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : UniqueNames image source target others resources) :=
  FinalReceiptEnsemble.install (base image source target final bankFinal others resources channels names)
    false OrderedFinalProvider.registerCircuit
    ⟨⟨3, by rw [base_tables_length]; omega⟩, base_register_component⟩

private theorem withRegisters_ram_component :
    (withRegisters image source target final bankFinal others resources channels names).tables[4]'(by
      simp only [withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
        List.length_set, base_tables_length]
      omega) =
      { circuit := OrderedFinalProvider.ramCircuit } := by
  change ((base image source target final bankFinal others resources channels names).tables.set 3
    { circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit })[4]'(by
      rw [List.length_set, base_tables_length]; omega) = _
  rw [List.getElem_set_ne (by decide : 3 ≠ 4)]
  exact base_ram_component

/-- Publish complete receipts at the original RAM-finalizer position. -/
@[reducible] def withReceipts (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : UniqueNames image source target others resources) :=
  FinalReceiptEnsemble.install (withRegisters image source target final bankFinal others resources channels names)
    true OrderedFinalProvider.ramCircuit
    ⟨⟨4, by
      simp only [withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
        List.length_set, base_tables_length]
      omega⟩, withRegisters_ram_component⟩

/-- The source-to-target change inventory is fixed by the supplied complete snapshots. -/
def ensemble (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : UniqueNames image source target others resources) : Ensemble (ZMod p) SP1PublicIO :=
  (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).install
    (withReceipts image source target final bankFinal others resources channels names)

/-- The original host table block before the target consumers and fixed membership providers, prior to the padding wrapper. -/
def beforeChecks (image : ProgramImage) (source : ExecutionSnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) :=
  HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: others).map (·.component) ++ (HostHintReadHandoff.wordResources ++ resources))

/-- The prefix contains exactly the original core, receiver registry and resource block. -/
theorem prefix_length (image : ProgramImage) (source : ExecutionSnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) :
    (beforeChecks image source others resources).length = 65 + others.length + resources.length := by
  rw [beforeChecks, HostLocalCore.tables_length]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    HostHintReadHandoff.wordResources]
  omega

/-- The target consumers are genuine appended resources in the unchanged host table layout. -/
theorem base_tables_eq : (base image source target final bankFinal others resources channels names).tables =
    (beforeChecks image source others resources ++ FinalMemoryChecks.checkTables target).set 57 HaltPaddingChip.component := by
  simp only [base, HostHintQueueBoundary.ensemble, HaltPadding.install, Ensemble.replaceComponent,
    ClosedVerifier.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
    HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble, beforeChecks,
    HostLocalCore.tables, List.append_assoc]
  rfl

/-- Both wrappers act on the original finalizers; appended targets are retained literally. -/
theorem tables_eq : (ensemble image source target final bankFinal others resources channels names).tables =
    (((beforeChecks image source others resources ++ FinalMemoryChecks.checkTables target).set 57 HaltPaddingChip.component).set 3
      { circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit }).set 4
      { circuit := FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit } := by
  simp only [ensemble, ClosedVerifier.install, withReceipts, withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, base_tables_eq]

/-- Typed registration of each target validator or fixed provider survives all three unrelated table replacements. -/
def checkSlot (index : Fin 4) : TableSlot (ensemble image source target final bankFinal others resources channels names).tables
    ((FinalMemoryChecks.checkTables (p := p) target)[index.val]'(by
      simpa only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil] using index.isLt)) := by
  let slot := (TableSlot.ofIndex (FinalMemoryChecks.checkTables (p := p) target)
    ⟨index.val, by simpa only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil] using index.isLt⟩).appendRight
      (beforeChecks image source others resources)
  have bound : 61 ≤ slot.index.val := by
    dsimp only [slot, TableSlot.appendRight, TableSlot.ofIndex]
    rw [prefix_length]
    omega
  exact (((slot.setOther 57 HaltPaddingChip.component (by omega)).setOther 3
    { circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit } (by change 3 ≠ slot.index.val; omega)).setOther 4
      { circuit := FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit } (by change 4 ≠ slot.index.val; omega)).cast tables_eq.symm

/-- The three original finalizer positions, with the two receipt wrappers installed. -/
def finalSlot (index : Fin 3) : TableSlot
    (ensemble image source target final bankFinal others resources channels names).tables
    ((FinalMemoryChecks.ensemble (p := p) source.sail.memorySnapshot target [] []
      (FinalMemoryChecks.empty_unique_names target)).tables[index.val]'(by
      rw [FinalMemoryChecks.tables_eq]; simp; omega)) := by
  refine ⟨⟨3 + index.val, by
    simp only [ensemble, ClosedVerifier.install, withReceipts, withRegisters,
      FinalReceiptEnsemble.install, Ensemble.replaceComponent, List.length_set, base_tables_length]
    omega⟩, ?_⟩
  change (((base image source target final bankFinal others resources channels names).tables.set 3
    { circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit }).set 4
    { circuit := FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit })[3 + index.val]'(by
      rw [List.length_set, List.length_set, base_tables_length]; omega) = _
  fin_cases index <;> dsimp only
  · rw [List.getElem_set_ne (by decide : 4 ≠ 3), List.getElem_set_self]
    rfl
  · rw [List.getElem_set_self]
    rfl
  · rw [List.getElem_set_ne (by decide : 4 ≠ 5), List.getElem_set_ne (by decide : 3 ≠ 5),
      base_boundary_component (index := ⟨5, by decide⟩)]
    rfl

/-- Retain all physical tables while viewing the old verifier without its new change demand. -/
def receiptWitness (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    EnsembleWitness (withReceipts image source target final bankFinal others resources channels names) :=
  (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project witness

/-- Forget only the RAM receipt, keeping its physical table and original constraints. -/
def registerWitness (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    EnsembleWitness (withRegisters image source target final bankFinal others resources channels names) :=
  FinalReceiptEnsemble.project (receiptWitness witness)

/-- The existing host proof view includes both added target consumers. No rows are removed. -/
def baseWitness (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    EnsembleWitness (base image source target final bankFinal others resources channels names) :=
  FinalReceiptEnsemble.project (registerWitness witness)

/-- Raw acceptance supplies every original host assertion and fixed lookup. -/
theorem baseWitness_constraints
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (checked : witness.Constraints) : (baseWitness witness).Constraints := by
  have raw : (receiptWitness witness).Constraints :=
    ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_constraints witness).mp checked
  unfold baseWitness
  apply (FinalReceiptEnsemble.project_constraints _).mpr
  unfold registerWitness
  exact (FinalReceiptEnsemble.project_constraints _).mpr raw

/-- Original table arrays remain byte-for-byte identical through the receipt proof views. -/
theorem baseWitness_rows
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    (baseWitness witness).tables.map (·.table) = witness.tables.map (·.table) := by
  have registers := FinalReceiptEnsemble.project_rows (registerWitness witness)
  have ram := FinalReceiptEnsemble.project_rows (receiptWitness witness)
  exact registers.trans (ram.trans (congrArg (List.map (fun physical : Table (ZMod p) => physical.table))
    ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_tables witness)))

/-- Receipt wrappers preserve the names and inputs defining canonical prover data. -/
theorem baseWitness_data
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    (baseWitness witness).data = witness.data := by
  have inner : (registerWitness witness).data = witness.data := by
    unfold registerWitness
    exact (FinalReceiptEnsemble.project_data _).trans
      ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_data witness)
  unfold baseWitness
  exact (FinalReceiptEnsemble.project_data _).trans inner

/-- The complete original header remains attached to the same physical instruction rows. -/
theorem baseWitness_publicInput
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names)) :
    (baseWitness witness).publicInput = witness.publicInput := by
  have inner : (registerWitness witness).publicInput = witness.publicInput := by
    unfold registerWitness
    exact (FinalReceiptEnsemble.project_publicInput _).trans
      ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_publicInput witness)
  unfold baseWitness
  exact (FinalReceiptEnsemble.project_publicInput _).trans inner

/-- Guarantees transfer on every original channel independently of its projected balance. -/
theorem baseWitness_channelGuarantees
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (channel : RawChannel (ZMod p))
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw)
    (guarantees : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel) :
    ∀ table ∈ (baseWitness witness).tables, table.ChannelGuarantees (baseWitness witness).data channel :=
  FinalReceiptEnsemble.project_channelGuarantees (registerWitness witness) channel registers
    (FinalReceiptEnsemble.project_channelGuarantees (receiptWitness witness) channel ram guarantees)

/-- Existing host proofs inherit Byte guarantees from the complete physical acceptance argument. -/
theorem baseWitness_byte
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (guarantees : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ table ∈ (baseWitness witness).tables, table.ChannelGuarantees (baseWitness witness).data byteChannel.toRaw :=
  baseWitness_channelGuarantees witness byteChannel.toRaw
    (by simp [byteChannel, FinalMemoryValue.channel, Channel.toRaw])
    (by simp [byteChannel, FinalMemoryValue.channel, Channel.toRaw]) guarantees

/-- Original channel occurrences survive both receipt wrappers exactly. -/
theorem baseWitness_interactions
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (channel : RawChannel (ZMod p))
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw) :
    (baseWitness witness).interactionsWith channel = (receiptWitness witness).interactionsWith channel :=
  (FinalReceiptEnsemble.project_interactions (registerWitness witness) channel registers).trans
    (FinalReceiptEnsemble.project_interactions (receiptWitness witness) channel ram)

/-- Registered channels unaffected by the three new receipts retain balance and count bounds.
Registration also separates them from the verifier's fresh assertion channel. The target
validators remain in this view, so their Byte demand is retained. -/
theorem baseWitness_balancedChannel
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (channel : RawChannel (ZMod p))
    (registered : channel ∈ (base image source target final bankFinal others resources channels names).channels)
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw)
    (changes : channel ≠ FinalMemoryChange.channel.toRaw)
    (balanced : witness.BalancedChannel channel) : (baseWitness witness).BalancedChannel channel := by
  change BalancedInteractions ((baseWitness witness).interactionsWith channel)
  rw [baseWitness_interactions witness channel registers ram]
  exact (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_balancedChannel
    witness channel (List.mem_append_left _ (List.mem_append_left _ registered))
    (by simp [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
      circuit_norm, changes]) balanced

end SP1Clean.Soundness.HostFinalMemory
