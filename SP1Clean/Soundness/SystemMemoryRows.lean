import SP1Clean.Soundness.TypedMemoryBalance
import SP1Clean.Soundness.SyscallGrounding

/-! # System rows as exact Memory access pairs

These projections use arbitrary physical tables carrying the named component. They do not depend
on an ensemble's table positions or boundary assumptions. Selecting active rows preserves the
entire produced/consumed message lists, including repetitions. HALT and syscall rows contribute
three register touches; MemoryBump contributes one refresh pair.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Decode exactly the active physical rows, retaining order and duplicate occurrences. -/
noncomputable def activeSystemRows {α : Type} (table : Table (ZMod p))
    (decode : Array (ZMod p) → α) (gate : α → ZMod p) : List α :=
  (table.table.map decode).filter (fun row => gate row = 1)

/-- The complete gated ledger of a list of paired prior/new Memory records. -/
def memoryPairInteractions (gate : ZMod p)
    (pairs : List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  pairs.flatMap fun pair =>
    [TypedInteraction.pulledIfValue memoryChannel gate pair.1,
     TypedInteraction.pushedIfValue memoryChannel gate pair.2]

private theorem unitSigns : signedVal (1 : ZMod p) = 1 ∧ signedVal (-1 : ZMod p) = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  constructor
  · rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  · rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num

private theorem memoryPairInteractions_active (gate : ZMod p)
    (binary : gate = 0 ∨ gate = 1) (pairs : List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))) :
    producedMessages (memoryPairInteractions gate pairs) = (if gate = 1 then pairs.map Prod.snd else []) ∧
    consumedMessages (memoryPairInteractions gate pairs) = (if gate = 1 then pairs.map Prod.fst else []) := by
  rw [memoryPairInteractions, producedMessages_flatMap, consumedMessages_flatMap]
  have zero : signedVal (0 : ZMod p) = 0 := by simp [signedVal]
  rcases binary with rfl | rfl
  · simp [producedMessages, consumedMessages, zero]
  · simp [producedMessages, consumedMessages, unitSigns.1, unitSigns.2,
      ← List.map_eq_flatMap]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem flatMap_filter_ite {α β : Type*} (items : List α) (keep : α → Bool) (f : α → List β) :
    (items.filter keep).flatMap f = items.flatMap (fun item => if keep item then f item else []) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    by_cases active : keep item <;> simp [active, ih]

private theorem activeSystemRows_projection {α : Type} (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (decode : Array (ZMod p) → α) (gate : α → ZMod p)
    (pairs : α → List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))
    (ledger : typedTableInteractionsWith table data memoryChannel =
      table.table.flatMap fun physical => memoryPairInteractions (gate (decode physical))
        (pairs (decode physical)))
    (binary : ∀ physical ∈ table.table, gate (decode physical) = 0 ∨ gate (decode physical) = 1) :
    producedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table decode gate).flatMap (fun row => (pairs row).map Prod.snd) ∧
    consumedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table decode gate).flatMap (fun row => (pairs row).map Prod.fst) := by
  rw [ledger, producedMessages_flatMap, consumedMessages_flatMap]
  have pushes : ∀ physical ∈ table.table,
      producedMessages (memoryPairInteractions (gate (decode physical)) (pairs (decode physical))) =
        if gate (decode physical) = 1 then (pairs (decode physical)).map Prod.snd else [] :=
    fun physical member => (memoryPairInteractions_active _ (binary physical member) _).1
  have pulls : ∀ physical ∈ table.table,
      consumedMessages (memoryPairInteractions (gate (decode physical)) (pairs (decode physical))) =
        if gate (decode physical) = 1 then (pairs (decode physical)).map Prod.fst else [] :=
    fun physical member => (memoryPairInteractions_active _ (binary physical member) _).2
  constructor
  · rw [List.flatMap_congr pushes]
    simp only [activeSystemRows, flatMap_filter_ite, List.flatMap_map,
      decide_eq_true_eq]
  · rw [List.flatMap_congr pulls]
    simp only [activeSystemRows, flatMap_filter_ite, List.flatMap_map,
      decide_eq_true_eq]

/-- A register refresh changes the timestamp while retaining location and value. -/
def MemoryBumpChip.memoryPairs (row : MemoryBumpChip.Inputs (ZMod p)) :
    List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) :=
  [(MemoryBumpChip.pulledMessage row, MemoryBumpChip.pushedMessage row)]

/-- HALT's three exact register read-prior/read-back pairs. -/
def HaltChip.memoryPairs (row : HaltChip.Inputs (ZMod p)) :
    List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) :=
  [(HaltChip.memPulledMessage row row.x5_memory 5, HaltChip.memPushedMessage row row.x5_memory 5 4),
   (HaltChip.memPulledMessage row row.x10_memory 10, HaltChip.memPushedMessage row row.x10_memory 10 3),
   (HaltChip.memPulledMessage row row.x11_memory 11, HaltChip.memPushedMessage row row.x11_memory 11 2)]

/-- The syscall's exact register pairs; the first push contains the written `op_a_value`. -/
def SyscallInstrsChip.memoryPairs (row : SyscallInstrsChip.Inputs (ZMod p)) :
    List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) :=
  [(SyscallInstrsChip.memPulledMessage row row.op_a_memory row.op_a,
      SyscallInstrsChip.memPushedMessage row row.op_a 4 row.op_a_value),
   (SyscallInstrsChip.memPulledMessage row row.op_b_memory row.op_b,
      SyscallInstrsChip.memPushedMessage row row.op_b 3 row.op_b_memory.prev_value),
   (SyscallInstrsChip.memPulledMessage row row.op_c_memory row.op_c,
      SyscallInstrsChip.memPushedMessage row row.op_c 2 row.op_c_memory.prev_value)]

/-- MemoryBump's physical constraints force its decoded selector binary. -/
theorem memoryBumpRow_binary (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := MemoryBumpChip.circuit }) (constraints : table.Constraints data)
    (physical : Array (ZMod p)) (member : physical ∈ table.table) :
    (memoryBumpRow data physical).is_real = 0 ∨ (memoryBumpRow data physical).is_real = 1 := by
  have checked := constraints physical member
  rw [component] at checked
  have binary := MemoryBumpChip.selectorBinary_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints MemoryBumpChip.circuit _ checked)
  simpa only [memoryBumpRow_eq, circuit_norm] using binary

/-- HALT's decoded selector is binary before any semantic Memory guarantee is available. -/
theorem haltRow_binary (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := HaltChip.circuit }) (constraints : table.Constraints data)
    (physical : Array (ZMod p)) (member : physical ∈ table.table) :
    (haltRow data physical).is_real = 0 ∨ (haltRow data physical).is_real = 1 := by
  have checked := constraints physical member
  rw [component] at checked
  have binary := HaltChip.selectorBinary_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints HaltChip.circuit _ checked)
  simpa only [haltRow_eq, circuit_norm] using binary

/-- The syscall's decoded selector is binary independently of host behavior. -/
theorem syscallRow_binary (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit }) (constraints : table.Constraints data)
    (physical : Array (ZMod p)) (member : physical ∈ table.table) :
    (syscallInstrsRow data physical).is_real = 0 ∨ (syscallInstrsRow data physical).is_real = 1 := by
  have checked := constraints physical member
  rw [component] at checked
  have binary := SyscallInstrsChip.selectorBinary_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints SyscallInstrsChip.circuit _ checked)
  simpa only [syscallInstrsRow_eq, circuit_norm] using binary

/-- Removing disabled refresh rows preserves the complete active Memory ledger. -/
theorem memoryBumpRows_projection (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := MemoryBumpChip.circuit }) (constraints : table.Constraints data) :
    producedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table (memoryBumpRow data) (·.is_real)).flatMap
          (fun row => (MemoryBumpChip.memoryPairs row).map Prod.snd) ∧
    consumedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table (memoryBumpRow data) (·.is_real)).flatMap
          (fun row => (MemoryBumpChip.memoryPairs row).map Prod.fst) :=
  activeSystemRows_projection table data (memoryBumpRow data) (·.is_real) MemoryBumpChip.memoryPairs
    (memoryBumpTable_typedMemory_of_component table data component)
    (memoryBumpRow_binary table data component constraints)

/-- Removing disabled HALT rows preserves all three register pairs of every active occurrence. -/
theorem haltRows_projection (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := HaltChip.circuit }) (constraints : table.Constraints data) :
    producedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table (haltRow data) (·.is_real)).flatMap
          (fun row => (HaltChip.memoryPairs row).map Prod.snd) ∧
    consumedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table (haltRow data) (·.is_real)).flatMap
          (fun row => (HaltChip.memoryPairs row).map Prod.fst) :=
  activeSystemRows_projection table data (haltRow data) (·.is_real) HaltChip.memoryPairs
    (haltTable_typedMemory_of_component table data component)
    (haltRow_binary table data component constraints)

/-- Removing disabled syscall rows preserves all three pairs, including the register write. -/
theorem syscallRows_projection (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit }) (constraints : table.Constraints data) :
    producedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table (syscallInstrsRow data) (·.is_real)).flatMap
          (fun row => (SyscallInstrsChip.memoryPairs row).map Prod.snd) ∧
    consumedMessages (typedTableInteractionsWith table data memoryChannel) =
        (activeSystemRows table (syscallInstrsRow data) (·.is_real)).flatMap
          (fun row => (SyscallInstrsChip.memoryPairs row).map Prod.fst) := by
  apply activeSystemRows_projection table data (syscallInstrsRow data) (·.is_real) SyscallInstrsChip.memoryPairs
    ?_ (syscallRow_binary table data component constraints)
  exact List.flatMap_congr (fun physical _ => syscallInstrsRow_typedMemory_of_component table data component physical)

/-- HALT as a timed row. Its three unchanged registers are read at the row's pre-state time;
the read-back records retain their actual access timestamps. -/
noncomputable def haltRowFacts (row : HaltChip.Inputs (ZMod p)) : RowFacts p :=
  { statePull := HaltChip.statePulledMessage row
    statePush := HaltChip.statePushedMessage row
    fetch := HaltChip.programMessage row
    memPulls := (HaltChip.memoryPairs row).map
      (fun pair => (pair.1, StateMsg.timeNat (HaltChip.statePulledMessage row)))
    memPushes := (HaltChip.memoryPairs row).map Prod.snd }

end SP1Clean.Soundness
