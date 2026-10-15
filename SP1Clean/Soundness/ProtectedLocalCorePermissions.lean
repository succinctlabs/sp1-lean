import SP1Clean.Soundness.ProtectedStorePermissions
import SP1Clean.Soundness.ProtectedLocalCoreProjection
import SP1Clean.Soundness.LocalCoreChannels

/-! # Authenticated byte permissions in the complete protected local AIR

The component inventory is exhaustive: only the fixed writable-interval table supplies permission;
the four store wrappers emit gated pulls; source, final, instruction and system rows, plus the
public verifier, otherwise remain silent. Consequently raw constraints and the ensemble's own count-bounded balance
authenticate every active permission request, with no separate provider-validity premise.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem old_component_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (LocalCore.ensemble image source).tables) :
    WritePermissionProvider.channel.toRaw ∉ component.circuit.channels := by
  intro used
  exact old_channel_ne_permission _
    (List.mem_append_left _ (LocalCore.component_channels_subset image source component member used)) rfl

/-- The fixed provider is the only possible positive contributor to permission balance. -/
theorem component_permission_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables) :
    component = ({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)) ∨
      WritePermission.Pulls component := by
  change component ∈ tables image source at member
  rcases List.mem_append.mp member with stores | fixed
  · right
    rcases List.mem_or_eq_of_mem_set stores with stores | rfl
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with original | rfl
          · exact WritePermission.pulls_of_silent component
              (old_component_silent image source component original)
          · exact WritePermission.byte_pulls
        · exact WritePermission.half_pulls
      · exact WritePermission.word_pulls
    · exact WritePermission.double_pulls
  · exact Or.inl (List.mem_singleton.mp fixed)

/-- The actual public verifier emits no permission traffic. Source checks keep their fresh channel. -/
theorem verifier_permission_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (env : Environment (ZMod p)) :
    (ensemble image source).verifierOperations.interactionValuesWith
      WritePermissionProvider.channel.toRaw env = [] := by
  have different := old_channel_ne_permission (p := p) (LocalCore.sourceChannel image source)
    (List.mem_append_right _ (List.mem_singleton_self _))
  change ((LocalSourceBoundary.checker image source).install
    (LocalCore.baseEnsemble image source)).verifierOperations.interactionValuesWith _ env = []
  rw [PublicVerifier.install_verifier_interactions _ _ _ _ different]
  apply LocalCore.boundaryVerifier_silent image source
  intro member
  exact old_channel_ne_permission _ (List.mem_append_left _ member) rfl

/-- Every active request in the actual 61-table ledger names a writable native byte address. -/
theorem permission_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (address : fields 3 (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : interaction.mult = -1) (payload : interaction.msg = (toElements address).toArray) :
    WritePermissionProvider.Permitted image address :=
  WritePermission.pull_permitted_of_sources image witness constraints
    (balanced _ (List.mem_cons_self ..))
    (by intro input data emitted member
        rw [verifier_permission_silent] at member
        exact (List.not_mem_nil member).elim)
    (component_permission_source image source)
    address interaction member active payload

/-- A concrete active pull in any physical row inherits its provider's byte permission. -/
theorem row_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.tables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (gate : Expression (ZMod p)) (address : Var (fields 3) (ZMod p))
    (emitted : (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
      table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : Expression.eval (Environment.fromArray physical witness.data) gate = 1) :
    WritePermissionProvider.Permitted image (eval (Environment.fromArray physical witness.data) address) := by
  apply permission_pull_permitted witness constraints balanced _
    ((WritePermissionProvider.channel.pulledIf gate address).toRaw.eval (Environment.fromArray physical witness.data))
  · apply EnsembleWitness.mem_interactionsWith.mpr
    refine Or.inr ⟨table, tableMem, List.mem_flatMap.mpr ⟨physical, physicalMem, ?_⟩⟩
    exact List.mem_map_of_mem emitted
  · simp only [Channel.eval_pulledIf, Channel.pulledIfValue, CircuitType.eval_expr, active]
  · simp only [Channel.eval_pulledIf, Channel.pulledIfValue]

end SP1Clean.Soundness.ProtectedLocalCore
