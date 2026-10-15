import SP1Clean.Soundness.HostLocalCore
import SP1Clean.Soundness.LocalCoreChannels

/-! # New private protocols on the complete host-enabled local ledger

The public boundary verifier and 61 non-wrapper components are silent on each new registered
private protocol. Source assertions use a channel fresh for the complete host inventory.
Their silence follows from the local channel inventory and the protected store projections.
Only the physical syscall wrapper and appended auxiliary tables can contribute. This exact
ledger split preserves padding and the original characteristic count bound.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}

def auxiliaryTables (witness : EnsembleWitness (ensemble image source auxiliary channels names)) :=
  witness.tables.drop 62

/-- Auxiliary tables retain the exact registered component inventory and order. -/
theorem auxiliaryTables_components (witness : EnsembleWitness (ensemble image source auxiliary channels names)) :
    (auxiliaryTables witness).map (·.component) = auxiliary := by
  simp only [auxiliaryTables, List.map_drop, witness.tables_map_component, ensemble, PublicVerifier.install, baseEnsemble, tables]
  rw [List.drop_left' (by simp only [List.length_set, ProtectedLocalCore.tables_length])]

private theorem prefix_length (witness : EnsembleWitness (ensemble image source auxiliary channels names)) :
    62 ≤ witness.tables.length := by
  rw [← witness.same_length]
  change 62 ≤ (tables image source auxiliary).length
  rw [tables_length]
  omega

private theorem prefixTable_silent (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (channel : RawChannel (ZMod p)) (fresh : channel ∉ (LocalCore.ensemble (p := p) image source).channels)
    (permission : channel ≠ WritePermissionProvider.channel.toRaw)
    (index : Fin 62) (notWrapper : index.val ≠ 58) :
    (witness.tables[index.val]'(by have := prefix_length witness; omega)).interactionsWith witness.data channel = [] := by
  by_cases old : index.val < 61
  · let original := (LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact old)
    have component : (witness.tables[index.val]'(by have := prefix_length witness; omega)).component =
        (ProtectedLocalCore.tables image source)[index.val]'(by rw [ProtectedLocalCore.tables_length]; exact index.isLt) := by
      rw [← witness.same_circuits]
      exact (core_component image source auxiliary ⟨index.val, old⟩).trans (if_neg (Ne.symm notWrapper))
    have width : original.width = (witness.tables[index.val]'(by have := prefix_length witness; omega)).component.width := by
      rw [component]
      exact (ProtectedLocalCore.component_layout image source ⟨index.val, old⟩).1
    have fixed : original.fixedColumns = (witness.tables[index.val]'(by have := prefix_length witness; omega)).component.fixedColumns := by
      rw [component]
      exact (ProtectedLocalCore.component_layout image source ⟨index.val, old⟩).2
    have silent := Table.interactionsWith_nil_of_channel_not_mem
      (table := (witness.tables[index.val]'(by have := prefix_length witness; omega)).withComponent original width fixed)
      (data := witness.data) (channel := channel) (fun used => fresh
        (List.mem_append_left _
          (LocalCore.component_channels_subset image source original (List.getElem_mem _) used)))
    rw [Table.withComponent_interactions _ original width fixed witness.data channel (by
      rw [component]
      exact ((ProtectedLocalCore.component_projection (p := p) image source ⟨index.val, old⟩).2.2 channel permission).symm)] at silent
    exact silent
  · have last : index.val = 61 := by omega
    have component : (witness.tables[index.val]'(by have := prefix_length witness; omega)).component = { circuit := WritePermissionProvider.circuit image } := by
      rw [← witness.same_circuits]
      change (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega) = _
      simp only [tables]
      rw [List.getElem_append_left (by simp only [List.length_set, ProtectedLocalCore.tables_length]; exact index.isLt),
        List.getElem_set_ne (Ne.symm notWrapper)]
      simp only [last]
      rfl
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [component]
    change channel ∉ [WritePermissionProvider.channel.toRaw]
    simpa only [List.mem_singleton] using permission

/-- A fresh protocol's complete ledger comes only from the installed wrapper and actual auxiliaries. -/
theorem interactions_split_new (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (channel : RawChannel (ZMod p)) (registered : channel ∈ (baseEnsemble image source auxiliary channels names).channels)
    (fresh : channel ∉ (LocalCore.ensemble (p := p) image source).channels)
    (permission : channel ≠ WritePermissionProvider.channel.toRaw) :
    witness.interactionsWith channel = (hostCallTable witness).interactionsWith witness.data channel ++
      (auxiliaryTables witness).flatMap (·.interactionsWith witness.data channel) := by
  have verifierSilent : witness.verifierInteractionsWith channel = [] := by
    change ((LocalSourceBoundary.checker image source).install
      (baseEnsemble image source auxiliary channels names)).verifierOperations.interactionValuesWith
        channel (Environment.fromInput witness.publicInput witness.data) = []
    rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _ registered]
    exact LocalCore.boundaryVerifier_silent image source channel
      (fun member => fresh (List.mem_append_left _ member)) _
  simp only [EnsembleWitness.interactionsWith, verifierSilent, List.nil_append,
    EnsembleWitness.tableContext, TableContext.interactionsWith]
  have split := List.take_append_drop 62 witness.tables
  rw [← split, List.flatMap_append]
  congr 1
  have length := prefix_length witness
  have prefixTables : witness.tables.take 62 = List.ofFn (fun index : Fin 62 =>
      witness.tables[index.val]'(by omega)) := by
    apply List.ext_getElem
    · simp only [List.length_take, Nat.min_eq_left length, List.length_ofFn]
    · intro index hi hj
      simp only [List.getElem_take, List.getElem_ofFn]
  rw [prefixTables]
  have actual : (List.ofFn fun index : Fin 62 =>
      (witness.tables[index.val]'(by omega)).interactionsWith witness.data channel) =
      List.ofFn (fun index : Fin 62 => if index.val = 58 then (hostCallTable witness).interactionsWith witness.data channel else []) := by
    apply congrArg List.ofFn
    funext index
    by_cases same : index.val = 58
    · simp only [same, ↓reduceIte, hostCallTable]
    · rw [if_neg same]
      exact prefixTable_silent witness channel fresh permission index same
  simp only [List.flatMap, List.map_ofFn, Function.comp_def]
  rw [actual]
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.reduceEqDiff,
    ↓reduceIte, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil]

/-- HostCall is a fresh private channel of the native extension. -/
theorem hostCall_fresh : HostCallChip.channel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
  intro member
  change HostCallChip.channel.toRaw ∈ (LocalCore.baseEnsemble image source).channels ++ [LocalCore.sourceChannel image source] at member
  rcases List.mem_append.mp member with member | member
  · have used := List.mem_map_of_mem (f := RawChannel.name) member
    simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, HostCallChip.channel,
      stateChannel, memoryChannel, byteChannel, programChannel, exitChannel, syscallChannel,
      publicValuesChannel, StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
      StaticTable.ofRows, Channel.toRaw] at used
  · have same := (List.mem_singleton.mp member).symm
    have heads := congrArg (fun channel : RawChannel (ZMod p) => channel.name.toList[4]?) same
    dsimp only [LocalCore.sourceChannel, PublicVerifier.channel, VerifierChannel.channel,
      Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName] at heads
    rw [String.toList_append] at heads
    simp [LocalSourceBoundary.checker, HostCallChip.channel] at heads

/-- The whole HostCall ledger, including the unique physical producer position. -/
theorem hostCall_interactions (witness : EnsembleWitness (ensemble image source auxiliary channels names)) :
    witness.interactionsWith HostCallChip.channel.toRaw =
      (hostCallTable witness).interactionsWith witness.data HostCallChip.channel.toRaw ++
        (auxiliaryTables witness).flatMap (·.interactionsWith witness.data HostCallChip.channel.toRaw) :=
  interactions_split_new witness HostCallChip.channel.toRaw (List.mem_cons_self ..) hostCall_fresh
    (by simp [HostCallChip.channel, WritePermissionProvider.channel, Channel.toRaw])

end SP1Clean.Soundness.HostLocalCore
