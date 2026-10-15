import SP1Clean.Soundness.HostLocalCore
import SP1Clean.Soundness.ProtectedLocalCorePermissions

/-! # Byte permission authentication with host effects installed

The host wrapper is silent on WritePermission. The retained protected store/provider inventory
therefore remains exhaustive when appended components prove that they emit only unit pulls or
padding on this channel. The extended ensemble's own balance authenticates every requested byte;
no projection of its Memory or permission balance is used.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The fixed image provider is still the only possible positive permission contributor. -/
theorem component_permission_source (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p)))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (component : Component (ZMod p)) (member : component ∈ tables image source auxiliary) :
    component = ({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)) ∨ WritePermission.Pulls component := by
  rcases List.mem_append.mp member with core | extra
  · rcases List.mem_or_eq_of_mem_set core with original | rfl
    · exact ProtectedLocalCore.component_permission_source image source component original
    · right
      apply WritePermission.pulls_of_silent
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
  · exact Or.inr (pulls component extra)

/-- The actual public verifier emits no permission traffic, including on its fresh source channel. -/
theorem verifier_permission_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : ((tables image source auxiliary).map (·.circuit.name)).Nodup)
    (env : Environment (ZMod p)) :
    (ensemble image source auxiliary channels names).verifierOperations.interactionValuesWith
      WritePermissionProvider.channel.toRaw env = [] := by
  change ((LocalSourceBoundary.checker image source).install
    (baseEnsemble image source auxiliary channels names)).verifierOperations.interactionValuesWith _ env = []
  rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _ (by simp [baseEnsemble])]
  apply LocalCore.boundaryVerifier_silent image source
  simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
    SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
    WritePermissionProvider.channel, circuit_norm]

/-- Every active request in the host-enabled assembly names a writable native byte address. -/
theorem permission_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    (address : fields 3 (ZMod p))
    (member : WritePermissionProvider.channel.pulledValue address ∈
      witness.interactionsWith WritePermissionProvider.channel.toRaw) :
    WritePermissionProvider.Permitted image address := by
  apply WritePermission.pull_permitted_of_sources image witness constraints
    balanced
    (by intro input data emitted used
        rw [verifier_permission_silent] at used
        exact (List.not_mem_nil used).elim)
    (component_permission_source image source auxiliary pulls) address
    (WritePermissionProvider.channel.pulledValue address) member rfl rfl

/-- An active physical row request is authenticated by the extended assembly's own ledger. -/
theorem row_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.tables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (gate : Expression (ZMod p)) (address : Var (fields 3) (ZMod p))
    (emitted : (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
      table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : Expression.eval (Environment.fromArray physical witness.data) gate = 1) :
    WritePermissionProvider.Permitted image (eval (Environment.fromArray physical witness.data) address) := by
  apply permission_pull_permitted witness pulls constraints balanced
  have member := EnsembleWitness.mem_interactionsWith.mpr
    (Or.inr ⟨table, tableMem, List.mem_flatMap.mpr ⟨physical, physicalMem, List.mem_map_of_mem emitted⟩⟩)
  simpa only [Channel.eval_pulledIf, Channel.pulledIfValue, Channel.pulledValue,
    CircuitType.eval_expr, active] using member

end SP1Clean.Soundness.HostLocalCore
