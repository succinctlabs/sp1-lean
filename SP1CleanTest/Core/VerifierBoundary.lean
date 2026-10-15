import SP1Clean.Native.Operations.HostExitBoundary
import ToClean.Air.Footprint

/-! # Public verifier boundary regressions

A stopped source cannot change its exit word, even when the receipt selector is zero. Installing
the boundary preserves the committed table and its canonical data. The disabled receipt remains
an occurrence, and the assertion contributes its own pull/push pair.
-/

namespace SP1CleanTest.VerifierBoundary
open Circuit Air.Flat
open SP1Clean

private abbrev Fp := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def physical : Table Fp where
  component := { circuit := { GeneralFormalCircuit.empty Fp (fields 1) with name := "retained" } }
  table := [#[3]]
  uniform_width := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    rfl
  fixed_rows_match := by trivial

private def base : Ensemble Fp unit where
  tables := [physical.component]
  unique_names := by simp
  channels := [HostExitBoundary.channel.toRaw]

private def original : EnsembleWitness base :=
  EnsembleWitness.ofTables base [physical] () rfl

private def candidate (source target : Option (BitVec 32)) :
    EnsembleWitness ((HostExitBoundary.closed source target).install base) :=
  EnsembleWitness.ofTables _ [physical] () rfl

/-- Installing verifier checks never adds the old synthetic singleton to physical rows. -/
theorem samePhysicalRows (source target : Option (BitVec 32)) :
    (candidate source target).tables = original.tables := rfl

/-- Canonical data remains identical at every name and arity, including the retained input row. -/
theorem sameCanonicalData (source target : Option (BitVec 32)) :
    (candidate source target).data = original.data := rfl

/-- The added assertion always contributes two occurrences, even when its value is zero. -/
theorem assertionOccurrences (source target : Option (BitVec 32)) :
    (candidate source target).channelOccurrences ((HostExitBoundary.closed source target).channel base) = 2 := by
  rw [ClosedVerifier.installed_channelOccurrences]
  simp [ClosedVerifier.operations, HostExitBoundary.closed, HostExitBoundary.circuit,
    HostExitBoundary.main, circuit_norm]

/-- Stopped-to-stopped changes fail the actual verifier balance condition, despite a zero receipt selector. -/
theorem changedStoppedStatusRejected :
    ¬ (candidate (some 1) (some 2)).BalancedChannels := by
  intro balanced
  have checked := ((HostExitBoundary.closed (p := 7) (some 1) (some 2)).balanced_iff
    (candidate (some 1) (some 2))).mp balanced |>.2.2
  norm_num [ClosedVerifier.Checks, ClosedVerifier.operations, HostExitBoundary.closed,
    HostExitBoundary.circuit, HostExitBoundary.main, circuit_norm] at checked
  exact (by decide : (1 : BitVec 32) ≠ 2) (checked (by decide))

/-- A running boundary with no exit keeps the disabled receipt in the literal ledger. -/
theorem disabledReceiptOccurrence :
    ((candidate none none).interactionsWith (HostExitBoundary.channel (p := 7)).toRaw).length = 1 := by
  have different : (HostExitBoundary.closed (p := 7) none none).channel base ≠
      HostExitBoundary.channel.toRaw := by
    intro same
    apply (HostExitBoundary.closed (p := 7) none none).channel_not_mem base
    rw [same]
    exact List.mem_append_left _ (by simp [base])
  rw [← ClosedVerifier.interactionView_interactions _ _ _ different]
  have permutation := (HostExitBoundary.closed (p := 7) none none).interactionView_interactions_perm
    (candidate none none) HostExitBoundary.channel.toRaw
  have original_empty : ((HostExitBoundary.closed (p := 7) none none).project
      (candidate none none)).interactionsWith HostExitBoundary.channel.toRaw = [] := by
    change original.interactionsWith HostExitBoundary.channel.toRaw = []
    rw [EnsembleWitness.interactionsWith_of_verifier_empty rfl]
    change physical.interactionsWith original.data HostExitBoundary.channel.toRaw ++ [] = []
    rw [List.append_nil]
    simp only [Table.interactionsWith, Operations.interactionValuesWith, Component.interactionsWith_eq]
    simp [physical, Component.rowOperations, GeneralFormalCircuit.empty, circuit_norm]
  rw [permutation.length_eq, List.length_append, original_empty, List.length_nil, Nat.zero_add,
    ClosedVerifier.singleton_interactions]
  change (((HostExitBoundary.main none none ()).operations 0).interactionValuesWith _ _).length = _
  rw [HostExitBoundary.values]
  simp

end SP1CleanTest.VerifierBoundary
