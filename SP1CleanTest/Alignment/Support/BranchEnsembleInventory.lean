import SP1CleanTest.Alignment.Support.BranchEnsembleChannels
import SP1CleanTest.Alignment.Support.BranchEnsembleLookups

/-! # Authenticated finite checking of the complete branch host assembly -/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core

/-- The five remaining legacy fixed meanings retain their original identities. -/
theorem fixed_names (target : MemorySnapshot) : (fixed target).map (·.table.name) =
    ["sp1.native.program",
      "sp1.native.syscall_code", "sp1.native.write_permission", "sp1.native.hint_source_nodes",
      "sp1.native.hint_source_words"] := by
  simp only [List.map_cons, List.map_nil, fixed, FiniteLookup.ofStatic,
    ProgramImage.programTable, SyscallKind.fixedTable, ProgramImage.writePermissionTable,
    HintQueue.sourceTable, HintQueue.sourceWordTable, StaticTable.ofRows,
    StaticTable.toTable, Table.toRaw]

/-- The checker authenticates all physical lookups and the separate verifier's complete channels. -/
def description (target : MemorySnapshot) : EnsembleCheck ((assembly target).withChannels (channels target)) where
  lookups := fixed target
  lookups_unique := by rw [fixed_names]; decide
  lookups_complete := lookups_complete target
  channels_unique := channels_unique target
  channels_complete := channels_complete target
  verifier_channels_complete := verifier_channels_complete target

/-- Check actual physical rows and all original channels after equivalent registry reindexing. -/
def checkPhysical (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed) : Bool :=
  (description target).checkWitness SP1Prime ((witness target input seeds).withChannels (channels target))

/-- The Boolean checker proves the raw predicates on the original full host assembly. -/
theorem checkPhysical_iff (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed) :
    checkPhysical target input seeds = true ↔
      (witness target input seeds).Constraints ∧ (witness target input seeds).BalancedChannels := by
  rw [checkPhysical, EnsembleCheck.checkWitness_iff]
  exact and_congr (EnsembleWitness.withChannels_constraints _ _)
    (EnsembleWitness.withChannels_balanced _ _ (channels_membership target))

/-- Reject malformed seeds before construction, then check the original complete physical witness. -/
def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (consumers : List Seed) : Bool :=
  match seeds? target input consumers with
  | none => false
  | some seeds => checkPhysical target input seeds

end SP1Clean.Audit.BranchEnsemble
