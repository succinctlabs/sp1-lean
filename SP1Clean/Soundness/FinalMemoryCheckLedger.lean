import SP1Clean.Soundness.FinalMemoryChecks

/-! # Exact ledgers of the installed target Memory validators

All inventories below are decoded from registered physical tables. Unit receipts retain the
complete final records; changed-location interactions retain zero multiplicities. Auxiliary
silence is a static interface of the installed components, never a witness premise.
-/

namespace SP1Clean.Soundness.FinalMemoryChecks

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
  {source target : MemorySnapshot} {auxiliary : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
variable {names : (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ auxiliary)).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup}

open scoped Classical

omit [Fact (2 ^ 17 < p)] in
private theorem single_interaction (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : Component (ZMod p))
    (same : table.component = component) (channel : RawChannel (ZMod p))
    (message : Environment (ZMod p) → Interaction (ZMod p))
    (row : ∀ env, component.operations.interactionValuesWith channel env = [message env]) :
    table.interactionsWith data channel = table.table.map (fun input => message (Environment.fromArray input data)) := by
  simp only [Table.interactionsWith, same, row]
  exact List.map_eq_flatMap.symm

/-- One full register receipt is consumed for every actual validation row. -/
theorem register_pulls (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    (registerSlot.table witness).interactionsWith witness.data (FinalMemoryValue.channel false).toRaw =
      (registerInputs witness).map (fun input => (FinalMemoryValue.channel false).pulledValue input.record) := by
  rw [single_interaction _ witness.data _ (registerSlot.table_component witness)
    (FinalMemoryValue.channel false).toRaw
    (fun env => (FinalMemoryValue.channel false).pulledValue
      (({ circuit := FinalRegisterCheck.circuit target } : Component (ZMod p)).rowInput env).record) ?_]
  · simp only [registerInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRegisterCheck.main target (varFromOffset FinalRegisterCheck.Inputs 0)).operations
      (size FinalRegisterCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRegisterCheck.receipt_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

/-- One full RAM receipt is consumed for every actual validation row. -/
theorem ram_pulls (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    (ramSlot.table witness).interactionsWith witness.data (FinalMemoryValue.channel true).toRaw =
      (ramInputs witness).map (fun input => (FinalMemoryValue.channel true).pulledValue input.record) := by
  rw [single_interaction _ witness.data _ (ramSlot.table_component witness)
    (FinalMemoryValue.channel true).toRaw
    (fun env => (FinalMemoryValue.channel true).pulledValue
      (({ circuit := FinalRamCheck.circuit target } : Component (ZMod p)).rowInput env).record) ?_]
  · simp only [ramInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRamCheck.main target (varFromOffset FinalRamCheck.Inputs 0)).operations
      (size FinalRamCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRamCheck.receipt_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

/-- Physical register selection occurrences, including disabled ones. -/
theorem register_changes (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    (registerSlot.table witness).interactionsWith witness.data FinalMemoryChange.channel.toRaw =
      (registerInputs witness).map (fun input => FinalMemoryChange.channel.pushedIfValue input.selected
        (FinalMemoryChange.key false input.record)) := by
  rw [single_interaction _ witness.data _ (registerSlot.table_component witness) FinalMemoryChange.channel.toRaw
    (fun env => let input := ({ circuit := FinalRegisterCheck.circuit target } : Component (ZMod p)).rowInput env
      FinalMemoryChange.channel.pushedIfValue input.selected (FinalMemoryChange.key false input.record)) ?_]
  · simp only [registerInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRegisterCheck.main target (varFromOffset FinalRegisterCheck.Inputs 0)).operations
      (size FinalRegisterCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRegisterCheck.change_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

/-- Physical RAM selection occurrences, including disabled ones. -/
theorem ram_changes (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    (ramSlot.table witness).interactionsWith witness.data FinalMemoryChange.channel.toRaw =
      (ramInputs witness).map (fun input => FinalMemoryChange.channel.pushedIfValue input.selected
        (FinalMemoryChange.key true input.record)) := by
  rw [single_interaction _ witness.data _ (ramSlot.table_component witness) FinalMemoryChange.channel.toRaw
    (fun env => let input := ({ circuit := FinalRamCheck.circuit target } : Component (ZMod p)).rowInput env
      FinalMemoryChange.channel.pushedIfValue input.selected (FinalMemoryChange.key true input.record)) ?_]
  · simp only [ramInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRamCheck.main target (varFromOffset FinalRamCheck.Inputs 0)).operations
      (size FinalRamCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRamCheck.change_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

private theorem table_silent {component : Component (ZMod p)}
    (slot : TableSlot (ensemble source target auxiliary channels names).tables component)
    (witness : EnsembleWitness (ensemble source target auxiliary channels names)) (channel : RawChannel (ZMod p))
    (absent : (component.circuit.channels.map RawChannel.name).contains channel.name = false) :
    (slot.table witness).interactionsWith witness.data channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [slot.table_component witness]
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  rw [absent] at present
  contradiction

/-- The verifier's only non-ordering interactions are the fixed complete change demand. -/
theorem verifier_values (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (channel : RawChannel (ZMod p))
    (notOrdering : channel ≠ (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) :
    witness.verifierInteractionsWith channel =
      if channel = FinalMemoryChange.channel.toRaw then
        (source.changes target).map (fun loc => FinalMemoryChange.channel.pulledValue (FinalMemoryChange.encode loc))
      else [] := by
  change ((base target auxiliary channels names).verifier.andThen
    ((FinalMemoryChangeBoundary.closed source target).program
      (base target auxiliary channels names))).circuitOperations.interactionValuesWith channel
        (Environment.fromInput witness.publicInput witness.data) = _
  rw [Verifier.Program.andThen_values]
  have original : (base target auxiliary channels names).verifierOperations.interactionValuesWith channel
      (Environment.fromInput witness.publicInput witness.data) = [] := by
    change (OrderedBoundaryVerifier.verifierProgram OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).circuitOperations.interactionValuesWith channel _ = []
    simp only [Verifier.Program.circuitOperations, Verifier.Program.operations,
      OrderedBoundaryVerifier.verifierProgram]
    rw [Verifier.ofInteractions_values]
    simp [Operations.interactionValuesWith, OrderedBoundaryVerifier.main, circuit_norm,
      Ne.symm notOrdering]
  rw [original, List.nil_append]
  have noAssertions : (FinalMemoryChangeBoundary.closed (p := p) source target).operations.constraints = [] :=
    FinalMemoryChangeBoundary.raw_constraints _ _
  simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, ClosedVerifier.program,
    Verifier.operations_bind, noAssertions, Verifier.checkZeros_operations, List.flatMap_nil, List.append_nil]
  rw [← Verifier.circuitOperations, ClosedVerifier.emit_values]
  simp only [ClosedVerifier.operations, FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
    FinalMemoryChangeBoundary.values, List.map_map, Function.comp_def]

/-- The complete register receipt ledger, in physical row order. -/
theorem register_ledger (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) :
    witness.interactionsWith (FinalMemoryValue.channel false).toRaw =
      (FinalReceiptEnsemble.records (FinalMemoryReceipts.registerWitness (receiptWitness witness))).map
          (FinalMemoryValue.channel false).pushedValue ++
        (registerInputs witness).map (fun input => (FinalMemoryValue.channel false).pulledValue input.record) := by
  rw [private_interactions witness _ (interface.receipts false), verifier_values witness _ (by
    simp [FinalMemoryValue.channel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
  rw [if_neg (by simp [FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])]
  rw [table_silent ramFinalSlot witness _ (by rfl), table_silent terminalSlot witness _ (by rfl),
    table_silent ramSlot witness _ (by rfl), table_silent membershipSlot witness _ (by rfl), table_silent ramMembershipSlot witness _ (by rfl), register_pulls]
  rw [← registerFinalTable_eq]
  simp only [List.nil_append, List.append_nil]
  exact congrArg (fun ledger => ledger ++ (registerInputs witness).map
    (fun input => (FinalMemoryValue.channel false).pulledValue input.record))
    (FinalMemoryReceipts.register_receipts (receiptWitness witness))

/-- The complete RAM receipt ledger, in physical row order. -/
theorem ram_ledger (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) :
    witness.interactionsWith (FinalMemoryValue.channel true).toRaw =
      (FinalReceiptEnsemble.records (receiptWitness witness)).map (FinalMemoryValue.channel true).pushedValue ++
        (ramInputs witness).map (fun input => (FinalMemoryValue.channel true).pulledValue input.record) := by
  rw [private_interactions witness _ (interface.receipts true), verifier_values witness _ (by
    simp [FinalMemoryValue.channel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
  rw [if_neg (by simp [FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])]
  rw [table_silent registerFinalSlot witness _ (by rfl), table_silent terminalSlot witness _ (by rfl),
    table_silent registerSlot witness _ (by rfl), table_silent membershipSlot witness _ (by rfl), table_silent ramMembershipSlot witness _ (by rfl), ram_pulls]
  rw [← ramFinalTable_eq]
  simp only [List.nil_append, List.append_nil]
  exact congrArg (fun ledger => ledger ++ (ramInputs witness).map
    (fun input => (FinalMemoryValue.channel true).pulledValue input.record))
    (FinalMemoryReceipts.ram_receipts (receiptWitness witness))

/-- Register receipt balance matches every finalizer record with exactly one validator input. -/
theorem register_receipts_perm_of_balancedChannel (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balance : witness.BalancedChannel (FinalMemoryValue.channel false).toRaw) :
    ((registerInputs witness).map (·.record)).Perm
      (FinalReceiptEnsemble.records (FinalMemoryReceipts.registerWitness (receiptWitness witness))) := by
  change BalancedInteractions (witness.interactionsWith (FinalMemoryValue.channel false).toRaw) at balance
  rw [register_ledger witness interface] at balance
  exact ((FinalMemoryValue.channel false).balanced_unit_iff _ _).mp
    (by simpa only [List.map_map, Function.comp_def] using balance) |>.2.symm

/-- RAM receipt balance preserves complete values, addresses, and timestamps. -/
theorem ram_receipts_perm_of_balancedChannel (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balance : witness.BalancedChannel (FinalMemoryValue.channel true).toRaw) :
    ((ramInputs witness).map (fun input => input.record)).Perm
      (FinalReceiptEnsemble.records (receiptWitness witness)) := by
  change BalancedInteractions (witness.interactionsWith (FinalMemoryValue.channel true).toRaw) at balance
  rw [ram_ledger witness interface] at balance
  exact ((FinalMemoryValue.channel true).balanced_unit_iff _ _).mp
    (by simpa only [List.map_map, Function.comp_def] using balance) |>.2.symm

/-- The full accepted assembly supplies the registered register receipt balance. -/
theorem register_receipts_perm (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balanced : witness.BalancedChannels) :
    ((registerInputs witness).map (·.record)).Perm
      (FinalReceiptEnsemble.records (FinalMemoryReceipts.registerWitness (receiptWitness witness))) :=
  register_receipts_perm_of_balancedChannel witness interface (balanced _ (by
    simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent]))

/-- The full accepted assembly supplies the registered RAM receipt balance. -/
theorem ram_receipts_perm (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balanced : witness.BalancedChannels) :
    ((ramInputs witness).map (fun input => input.record)).Perm
      (FinalReceiptEnsemble.records (receiptWitness witness)) :=
  ram_receipts_perm_of_balancedChannel witness interface (balanced _ (by
    simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent]))

/-- One common accounting view of the two actual validator tables. -/
def validationRows (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    List (FinalMemoryChangeCoverage.Row p) :=
  (registerInputs witness).map (fun input => (false, input)) ++
    (ramInputs witness).map (fun input => (true, ⟨input.record, input.selected⟩))

/-- Only the two full-record receipt balances identify the validated final inventory. -/
theorem receipts_perm_of_channels (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary)
    (balanced : ∀ ram, witness.BalancedChannel (FinalMemoryValue.channel ram).toRaw) :
    ((validationRows witness).map fun row => row.2.record).Perm (records witness) := by
  rw [records, FinalMemoryReceipts.records_eq (receiptWitness witness)]
  simpa only [validationRows, List.map_append, List.map_map, Function.comp_def] using
    (register_receipts_perm_of_balancedChannel witness interface (balanced false)).append
      (ram_receipts_perm_of_balancedChannel witness interface (balanced true))

/-- Complete receipt balance identifies the validated inventory with the original final decoder. -/
theorem receipts_perm (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balanced : witness.BalancedChannels) :
    ((validationRows witness).map fun row => row.2.record).Perm (records witness) := by
  apply receipts_perm_of_channels witness interface
  intro ram
  apply balanced
  cases ram <;> simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
    FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent]

/-- Every physical change occurrence is accounted for, including the verifier and disabled rows. -/
theorem changes_ledger (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) :
    (witness.interactionsWith FinalMemoryChange.channel.toRaw).Perm
      (FinalMemoryChangeCoverage.ledger source target (validationRows witness)) := by
  rw [private_interactions witness _ interface.changes, verifier_values witness _ (by
    simp [FinalMemoryChange.channel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
  rw [if_pos rfl, table_silent registerFinalSlot witness _ (by rfl),
    table_silent ramFinalSlot witness _ (by rfl), table_silent terminalSlot witness _ (by rfl),
    table_silent membershipSlot witness _ (by rfl), table_silent ramMembershipSlot witness _ (by rfl), register_changes, ram_changes]
  simp only [FinalMemoryChangeCoverage.ledger, validationRows, List.map_append,
    List.map_map, Function.comp_def, List.append_nil, List.append_assoc]
  exact List.perm_append_comm.trans (List.Perm.of_eq (List.append_assoc ..))

/-- Exact transport of the canonical change ledger needs only that channel's actual balance. -/
theorem changes_balanced_of_balancedChannel (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balanced : witness.BalancedChannel FinalMemoryChange.channel.toRaw) :
    BalancedInteractions (FinalMemoryChangeCoverage.ledger source target (validationRows witness)) :=
  balancedInteractions_of_perm balanced (changes_ledger witness interface)

/-- Actual full-ensemble balance closes the complete change ledger. -/
theorem changes_balanced (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (balanced : witness.BalancedChannels) :
    BalancedInteractions (FinalMemoryChangeCoverage.ledger source target (validationRows witness)) := by
  apply changes_balanced_of_balancedChannel witness interface (balanced _ ?_)
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self ..)))

end SP1Clean.Soundness.FinalMemoryChecks
