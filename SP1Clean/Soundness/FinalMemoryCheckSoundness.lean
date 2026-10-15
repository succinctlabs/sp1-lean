import SP1Clean.Soundness.FinalMemoryCheckLedger

/-! # Complete outgoing Memory comparison from raw boundary acceptance

The installed witness supplies all facts: fixed membership authenticates target registers,
Byte closure authenticates target RAM reads and finalizer addresses, complete-record receipt balance matches every final row, and the verifier's change
ledger covers the complete complement. The result is the existing finite `checkFinal` relation.
Connecting this boundary subsystem to mixed execution grounding remains an assembly transport,
not a new semantics or an additional caller certificate.
-/

namespace SP1Clean.Soundness.FinalMemoryChecks

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
  {source target : MemorySnapshot} {auxiliary : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
variable {names : (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ auxiliary)).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup}

private theorem register_key (record : MemoryMsg (ZMod p)) (valid : FinalRegisterValue.Spec target record) :
    FinalMemoryChange.key false record = FinalMemoryChange.encode (MemoryMsg.locOf record) := by
  have location : MemoryMsg.locOf record = .reg (BitVec.ofNat 5 record.addr0.val) := by
    simp only [MemoryMsg.locOf, valid.1, valid.2.1, valid.2.2.1, and_self, ↓reduceIte]
  apply FinalMemoryChange.key_eq_encode false record ?_ (by rw [location])
  constructor
  · apply Word.isU64_of_cases <;>
      simp only [MemoryBoundary.address, valid.2.1, valid.2.2.1, circuit_norm, ZMod.val_zero] <;>
      have := valid.1 <;> omega
  · simp only [MemoryBoundary.address, Word.toNat, location, MemLoc.busAddress,
      valid.2.1, valid.2.2.1, circuit_norm, ZMod.val_zero, zero_mul, add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt valid.1]

private theorem ram_key (record : MemoryMsg (ZMod p)) (valid : MemoryBoundary.RamFinalSpec record) :
    FinalMemoryChange.key true record = FinalMemoryChange.encode (MemoryMsg.locOf record) := by
  apply FinalMemoryChange.key_eq_encode true record valid.1.2
  have lower : 32 ≤ (MemoryMsg.locOf record).busAddress := le_trans (by decide) valid.2
  cases location : MemoryMsg.locOf record with
  | reg index =>
      rw [location] at lower
      have := index.isLt
      change 32 ≤ index.toNat at lower
      omega
  | ram cell => rfl

/-- RAM-domain provenance is inherited from the matched physical finalizer, not assumed by
the target checker or supplied independently of the receipt ledger. -/
theorem ramInputs_finalSpec_of_channels (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (checked : witness.Constraints)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (balanced : witness.BalancedChannel (FinalMemoryValue.channel true).toRaw) :
    ∀ input ∈ ramInputs witness, MemoryBoundary.RamFinalSpec input.record := by
  have bytes : (FinalMemoryReceipts.ramTable (receiptWitness witness)).ChannelGuarantees witness.data byteChannel.toRaw := by
    rw [ramFinalTable_eq]
    exact ramFinalSlot.table_channelGuarantees witness byteChannel.toRaw
      byte
  have finalized := FinalMemoryReceipts.ram_records_spec (receiptWitness witness)
    (receiptWitness_constraints witness checked) bytes
  intro input present
  exact finalized _ ((ram_receipts_perm_of_balancedChannel witness interface balanced).mem_iff.mp
    (List.mem_map_of_mem (f := fun input : FinalRamCheck.Inputs (ZMod p) => input.record) present))

/-- Target comparison uses Byte guarantees, fixed target membership and complete receipt balances.
All facts concern the original physical rows; the enclosing assembly proves them from acceptance. -/
theorem checkFinal_of_channels (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (checked : witness.Constraints)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    (receipts : ∀ ram, witness.BalancedChannel (FinalMemoryValue.channel ram).toRaw)
    (changes : witness.BalancedChannel FinalMemoryChange.channel.toRaw)
    (membership : ∀ channel ∈ membershipChannels target, witness.BalancedChannel channel) :
    source.checkFinal target
      ((records witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  have members channel known := membership_guarantees witness interface checked channel known (membership channel known)
  apply FinalMemoryChangeCoverage.checkFinal_of_balanced source target (records witness) (validationRows witness)
    (receipts_perm_of_channels witness interface receipts) ?_ ?_ ?_
    (changes_balanced_of_balancedChannel witness interface changes)
  · intro row member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp register
      exact (registerInputs_spec_of_channels witness checked byte members input present).1.2.2.2.2.symm
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp ram
      exact ((ramInputs_spec_of_channels witness checked byte members input present).1.final_snapshot target _
        (ramInputs_finalSpec_of_channels witness interface checked byte (receipts true) input present)).symm
  · intro row member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp register
      exact (registerInputs_spec_of_channels witness checked byte members input present).2
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp ram
      exact (ramInputs_spec_of_channels witness checked byte members input present).2
  · intro row member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp register
      exact register_key _ (registerInputs_spec_of_channels witness checked byte members input present).1
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp ram
      exact ram_key _ (ramInputs_finalSpec_of_channels witness interface checked byte (receipts true) input present)

/-- The full accepted assembly derives RAM address provenance from its actual finalizer. -/
theorem ramInputs_finalSpec (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ input ∈ ramInputs witness, MemoryBoundary.RamFinalSpec input.record :=
  ramInputs_finalSpec_of_channels witness interface checked (byte_guarantees witness interface checked balanced)
    (balanced _ (by simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent]))

/-- Raw constraints and complete channel balance imply complete target Memory validation.
There is no witness-supplied inventory, readiness predicate, or endpoint-comparison premise. -/
theorem checkFinal (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface target auxiliary) (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    source.checkFinal target
      ((records witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply checkFinal_of_channels witness interface checked (byte_guarantees witness interface checked balanced)
  · intro ram
    apply balanced
    cases ram <;> simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent]
  · exact balanced _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self ..))))

  · intro channel known
    apply balanced
    simp only [membershipChannels, List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl
    all_goals simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
      FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble]

end SP1Clean.Soundness.FinalMemoryChecks
