import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Soundness.EnsembleLookups

/-! # Fixed lookup constraints in the local execution assembly

Decoded ROM and syscall-code predicates are fixed by the supplied image and profile.
Source register and RAM membership use fixed-column channel providers; native byte providers
are lookup-free. The remaining lookup predicates ignore prover data, so local constraints
survive canonical-data changes when physical row cells are retained. Channel guarantees
remain separate obligations, established from actual balance and fixed prefixes.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

attribute [local circuit_norm]
  SnapshotMemoryEnsemble.registerView SnapshotMemoryEnsemble.ramView
  SnapshotMemoryEnsemble.terminalView
  FinalMemoryEnsemble.inventory FinalMemoryEnsemble.viewFor
  FinalMemoryEnsemble.registerView FinalMemoryEnsemble.ramView
  OrderedMemoryEnsemble.Inventory.views OrderedMemoryEnsemble.providerView
  OrderedMemoryEnsemble.terminalView OrderedMemoryProvider.circuit OrderedBoundaryEnd.circuit
  SnapshotRegisterProvider.circuit SnapshotRamProvider.circuit
  FinalRegisterProvider.circuit FinalRamProvider.circuit
  ByteChip.U8Range.circuit ByteChip.MSB.circuit ByteChip.AndByte.circuit
  ByteChip.OrByte.circuit ByteChip.XorByte.circuit ByteChip.Ltu.circuit
  RangeChip.circuitFor RangeChip.circuit DecodedProgramProvider.circuit

private theorem final_lookups (component : Component (ZMod p))
    (member : component ∈ FinalMemoryEnsemble.inventory.views.map (·.component)) :
    component.operations.lookups = [] := by
  change component ∈ [(FinalMemoryEnsemble.registerView (p := p)).component,
    (FinalMemoryEnsemble.ramView (p := p)).component,
    (OrderedMemoryEnsemble.terminalView OrderedFinalProvider.channelName (by decide)).component] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [Component.lookups_eq, Component.rowOperations, circuit_norm]

private theorem source_constraints_setData (source : ExecutionSnapshot) (component : Component (ZMod p))
    (member : component ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component))
    {row : Array (ZMod p)} {data data' : ProverData (ZMod p)}
    (checked : component.operations.ConstraintsHold (Environment.fromArray row data)) :
    component.operations.ConstraintsHold (Environment.fromArray row data') := by
  simp only [SnapshotMemoryEnsemble.views_eq, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    apply Operations.constraintsHold_congr (env := Environment.fromArray row data)
      (env' := Environment.fromArray row data') rfl ?_ checked
    intro lookup used
    simp [Component.lookups_eq, Component.rowOperations, circuit_norm,
      SnapshotRegisterProvider.main, SnapshotRamProvider.main,
      InitialMemoryRead.circuit, InitialMemoryRead.circuitNamed,
      InitialMemoryRead.main, InitialMemoryLookup.circuitNamed, InitialMemoryLookup.main_lookups,
      AddOperation.circuit, AddOperation.main,
      AddressOperation.circuit] at used
/-- Fixed source/ROM lookups and native providers depend on physical cells, not generation data.
This transports local constraints across canonical projections without asserting data equality. -/
theorem component_constraints_setData (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ tables image source)
    {row : Array (ZMod p)} {data data' : ProverData (ZMod p)}
    (checked : component.operations.ConstraintsHold (Environment.fromArray row data)) :
    component.operations.ConstraintsHold (Environment.fromArray row data') := by
  rcases List.mem_append.mp member with snapshot | rest
  · exact source_constraints_setData source component snapshot checked
  rcases List.mem_append.mp rest with rest | fixed
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    all_goals apply Component.constraintsHold_setData _ ?_ checked
    all_goals simp [SnapshotMemoryEnsemble.registerMembership, SnapshotMemoryEnsemble.ramMembership, StaticTable.component, StaticTable.provider,
      Component.lookups_eq, Component.rowOperations, circuit_norm]
  rcases List.mem_append.mp rest with retained | provider
  · rcases List.mem_append.mp retained with boundary | instruction
    · rcases List.mem_append.mp boundary with final | rom
      · exact component.constraintsHold_setData (final_lookups component final) checked
      · obtain rfl := List.mem_singleton.mp rom
        apply Operations.constraintsHold_congr (env := Environment.fromArray row data)
          (env' := Environment.fromArray row data') rfl ?_ checked
        intro lookup used
        simp [Component.lookups_eq, Component.rowOperations, circuit_norm,
          FixedProgramProvider.circuit,
          ProgramProviderChip.circuit, ProgramProviderChip.main,
          Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits] at used
        subst lookup
        have eval_eq : Expression.eval (Environment.fromArray row data) =
            Expression.eval (Environment.fromArray row data') :=
          funext fun expression => Expression.eval_congr
            (env := Environment.fromArray row data) (env' := Environment.fromArray row data') rfl expression
        simp only [Lookup.Contains, eval_eq, _root_.Table.toRaw]
        exact fun h => h
    · exact component.constraintsHold_setData (sp1Tables_lookups_empty component instruction) checked
  · apply sp1Table_constraints_setData component ?_ checked
    rw [sp1Ensemble_tables]
    apply List.mem_append_right
    rcases List.mem_append.mp provider with before | after
    · exact List.mem_of_mem_take before
    · exact List.mem_of_mem_drop after

end SP1Clean.Soundness.LocalCore
