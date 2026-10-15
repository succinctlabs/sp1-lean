module

public import ToClean.Air.EnsembleBuild

/-! # Typed positions in a physical ensemble

Clean's witness stores a positional component equation, but has no typed reference to an
installed component. `TableSlot` packages that equation with its bounded position. References
compose through appended component blocks and select the original physical table, including
its rows and the canonical data derived by the whole witness. Constraints and channel guarantees are
inherited independently; selecting a table makes no claim about projected channel balance.

The intended upstream home is `Clean/Air/FlatEnsemble.lean`. The concrete consumers are
SP1's finalizer receipt installation and commitment-bank table selection.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- A bounded physical position carrying the identity of the component installed there. -/
structure TableSlot (components : List (Component F)) (component : Component F) where
  /-- The bounded position in the physical component inventory. -/
  index : Fin components.length
  /-- The component at this position is exactly the registered circuit. -/
  component_eq : components[index.val] = component

namespace TableSlot

variable {components : List (Component F)} {component : Component F}

/-- Every bounded position names its actual installed component. -/
def ofIndex (components : List (Component F)) (index : Fin components.length) :
    TableSlot components components[index.val] := ⟨index, rfl⟩

/-- Appending resources preserves the positions of an existing component block. -/
def appendLeft (slot : TableSlot components component) (suffix : List (Component F)) :
    TableSlot (components ++ suffix) component where
  index := ⟨slot.index.val, by simp only [List.length_append]; omega⟩
  component_eq := by rw [List.getElem_append_left slot.index.isLt]; exact slot.component_eq

/-- Prepending a block shifts the physical position by exactly that block's length. -/
def appendRight (slot : TableSlot components component) (before : List (Component F)) :
    TableSlot (before ++ components) component where
  index := ⟨before.length + slot.index.val, by simp only [List.length_append]; omega⟩
  component_eq := by
    simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact slot.component_eq

/-- Retyping a component inventory changes no physical position. -/
def cast {other : List (Component F)} (slot : TableSlot components component)
    (same : components = other) : TableSlot other component := same ▸ slot

/-- Inventory transport preserves the numerical physical position. -/
@[simp] theorem cast_index {other : List (Component F)} (slot : TableSlot components component)
    (same : components = other) : (slot.cast same).index.val = slot.index.val := by
  cases same
  rfl

/-- Replacing another component preserves this registration and its physical position. -/
def setOther (slot : TableSlot components component) (position : ℕ) (replacement : Component F)
    (different : position ≠ slot.index.val) : TableSlot (components.set position replacement) component where
  index := ⟨slot.index.val, by simpa only [List.length_set] using slot.index.isLt⟩
  component_eq := (List.getElem_set_ne different _).trans slot.component_eq

variable {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

/-- Read the selected table without rebuilding or decoding any physical row. -/
def table (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens) : Table F :=
  witness.tables[slot.index.val]'(by rw [← witness.same_length]; exact slot.index.isLt)

/-- The selected physical table is interpreted by the registered component. -/
theorem table_component (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens) :
    (slot.table witness).component = component := by
  rw [table, ← witness.same_circuits]
  exact slot.component_eq

/-- A selected table belongs to the original complete physical inventory. -/
theorem table_mem (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens) :
    slot.table witness ∈ witness.tables := List.getElem_mem _

/-- The selected physical table determines its entry in the witness's canonical data. -/
theorem table_data (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens) (arity : ℕ) :
    witness.data component.circuit.name arity = component.proverRows (slot.table witness).table arity := by
  have sameName := congrArg (fun component : Component F => component.circuit.name) (slot.table_component witness)
  simpa only [sameName, slot.table_component witness] using witness.data_of_mem_table (slot.table_mem witness) arity

/-- Whole-witness constraints restrict to the original selected physical table. -/
theorem table_constraints (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens)
    (checked : witness.Constraints) : (slot.table witness).Constraints witness.data :=
  checked _ (slot.table_mem witness)

/-- Individual channel guarantees restrict without claiming balance of any smaller inventory. -/
theorem table_channelGuarantees (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens)
    (channel : RawChannel F) (guarantees : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel) :
    (slot.table witness).ChannelGuarantees witness.data channel := guarantees _ (slot.table_mem witness)

/-- Every selected interaction remains an occurrence in the complete physical ledger. -/
theorem table_interactions_subset (slot : TableSlot ens.tables component) (witness : EnsembleWitness ens)
    (channel : RawChannel F) :
    (slot.table witness).interactionsWith witness.data channel ⊆ witness.interactionsWith channel := by
  intro interaction member
  exact EnsembleWitness.mem_interactionsWith.mpr
    (Or.inr ⟨slot.table witness, slot.table_mem witness, member⟩)

end TableSlot
end Air.Flat
