import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Soundness.EnsembleChannels

/-! # Physical channel inventory of the local assembly

Every physical source, final, instruction, and system component speaks only on a declared
local channel. Extensions can therefore prove silence on a new private channel uniformly,
without repeating the table inventory for each host protocol.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Model.Core Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The actual public boundary verifier speaks only on registered base channels. -/
theorem boundaryVerifier_channels_subset (image : ProgramImage) (source : ExecutionSnapshot) :
    (boundaryVerifier (p := p)).circuitOperations.interactions.map (·.channel) ⊆
      (baseEnsemble image source).channels := by
  intro channel member
  simp [boundaryVerifier, sp1StateVerifierProgram, OrderedBoundaryVerifier.verifierProgram,
    Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.ofInteractions,
    sp1StateVerifierMain, OrderedBoundaryVerifier.main, baseEnsemble,
    sp1Ensemble_channels, circuit_norm] at member ⊢
  tauto

/-- A channel outside the boundary registry has no public-verifier occurrences. -/
theorem boundaryVerifier_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (channel : RawChannel (ZMod p)) (outside : channel ∉ (baseEnsemble image source).channels)
    (env : Environment (ZMod p)) :
    (boundaryVerifier (p := p)).circuitOperations.interactionValuesWith channel env = [] := by
  have empty : (boundaryVerifier (p := p)).circuitOperations.interactionsWith channel = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro interaction member
    have registered := boundaryVerifier_channels_subset image source (List.mem_map_of_mem member)
    simpa only [decide_eq_true_eq] using (show interaction.channel ≠ channel from fun same => outside (same ▸ registered))
  simp only [Operations.interactionValuesWith, empty, List.map_nil]

/-- Physical components use the base channels, never the verifier-only assertion channel. -/
theorem component_channels_subset (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables) :
    component.circuit.channels ⊆ (baseEnsemble image source).channels := by
  have core : sp1CoreChannels (p := p) ⊆ (baseEnsemble image source).channels := by
    intro channel used
    simp only [sp1CoreChannels, List.mem_cons, List.not_mem_nil, or_false] at used
    simp only [baseEnsemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  simp only [ensemble, PublicVerifier.install, baseEnsemble, tables, afterSourceTables,
    List.mem_append] at member
  rcases member with initial | remaining | fixed
  · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp initial
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
    intro channel used
    have inside := SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    simp only [baseEnsemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · simp only [NativeCore.afterInitialTables, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at remaining
    rcases remaining with ((final | rfl) | instruction) | (before | after)
    · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp final
      obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
      intro channel used
      have inside := FinalMemoryEnsemble.view_channels_subset (p := p) id used
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      simp only [baseEnsemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · intro channel used
      change channel ∈ [programChannel.toRaw] at used
      rw [List.mem_singleton] at used
      subst channel
      simp [baseEnsemble, sp1Ensemble_channels]
    · exact fun _ used => core (sp1Tables_channels_subset component instruction used)
    all_goals
      have provider : component ∈ sp1ProviderTables (p := p) := by
        first | exact List.mem_of_mem_take before | exact List.mem_of_mem_drop after
      rcases sp1ProviderTables_channels_subset_core component provider with inside | rfl
      · exact fun _ used => core (inside used)
      · intro channel used
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (syscallInstrsProvider_channels_subset used))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    · change [source.sail.memorySnapshot.registerTable.channel.toRaw] ⊆ _
      intro channel member
      obtain rfl := List.mem_singleton.mp member
      simp [baseEnsemble]
    · change [(InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48)
        "sp1.native.initial_memory").channel.toRaw] ⊆ _
      intro channel member
      obtain rfl := List.mem_singleton.mp member
      simp [baseEnsemble]

end SP1Clean.Soundness.LocalCore
