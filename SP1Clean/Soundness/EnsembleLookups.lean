import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.TableBuild

/-! # Constraint transport for the native instruction/provider inventory

The native instruction and provider components have no legacy lookups. Their physical
constraints therefore survive a change from witness-generation data to the data derived
from the committed tables.

This says nothing about data-dependent channel guarantees, semantic commitment bindings or
arbitrary ensembles with dynamic lookups; those require their own agreement proofs.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every native provider uses polynomial constraints and channel interactions only. -/
theorem providerTableFor_lookups_empty (id : ProviderTableId) :
    (providerTableFor (p := p) id).operations.lookups = [] := by
  cases id with
  | byte provider =>
    cases provider <;>
      simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
        ByteChip.U8Range.circuit, ByteChip.MSB.circuit, ByteChip.AndByte.circuit,
        ByteChip.OrByte.circuit, ByteChip.XorByte.circuit, ByteChip.Ltu.circuit,
        ByteChip.U8Range.main, ByteChip.MSB.main, ByteChip.AndByte.main,
        ByteChip.OrByte.main, ByteChip.XorByte.main, ByteChip.Ltu.main,
        Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits,
        Gadgets.BitwiseByte.circuit, circuit_norm]
  | range width =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      RangeChip.circuitFor, RangeChip.circuit, circuit_norm]
  | program =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      ProgramProviderChip.circuit, ProgramProviderChip.main,
      Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]
  | memoryInit =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      MemoryProviderChip.circuit, MemoryProviderChip.main, WordRangeCheck.circuit, circuit_norm]
  | memoryFinalize =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      MemoryFinalizeChip.circuit, MemoryFinalizeChip.main, circuit_norm]
  | memoryBump => simp [providerTableFor, MemoryBumpChip.lookups_empty]
  | stateBump => simp [providerTableFor, StateBumpChip.lookups_empty]
  | halt => simp [providerTableFor, HaltChip.lookups_empty]
  | syscallInstrs => simp [providerTableFor, SyscallInstrsChip.lookups_empty]

/-- Every native provider constraint depends on its physical cells alone. -/
theorem providerTableFor_constraints_setData (id : ProviderTableId)
    {row : Array (ZMod p)} {data data' : ProverData (ZMod p)}
    (checked : (providerTableFor id).operations.ConstraintsHold (Environment.fromArray row data)) :
    (providerTableFor id).operations.ConstraintsHold (Environment.fromArray row data') :=
  (providerTableFor id).constraintsHold_setData (providerTableFor_lookups_empty id) checked

/-- Generated rows of this inventory may be checked at the ensemble's canonical data. -/
theorem sp1Table_constraints_setData (component : Component (ZMod p))
    (member : component ∈ (sp1Ensemble (p := p)).tables)
    {row : Array (ZMod p)} {data data' : ProverData (ZMod p)}
    (checked : component.operations.ConstraintsHold (Environment.fromArray row data)) :
    component.operations.ConstraintsHold (Environment.fromArray row data') := by
  rw [sp1Ensemble_tables] at member
  rcases List.mem_append.mp member with instruction | provider
  · exact component.constraintsHold_setData (sp1Tables_lookups_empty component instruction) checked
  · obtain ⟨id, _, rfl⟩ := List.mem_map.mp provider
    exact providerTableFor_constraints_setData id checked

end SP1Clean.Soundness
