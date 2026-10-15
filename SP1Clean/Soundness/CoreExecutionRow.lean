import SP1Clean.Soundness.SystemMemoryRows
import SP1Clean.Soundness.SystemStateRows
import SP1Clean.Soundness.StateChronology

/-! # Shared execution-row semantics for native core assemblies

Ordinary instructions, HALT, and inline syscalls use one carrier independently of the incoming
state policy. This module fixes its Memory facts, complete State edges, event widths, and physical
system-row progress lemmas. Ledger projections and ordering reuse this same carrier for boot and
local assemblies. Host effect correctness is a separate obligation.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- All real instruction events, including the legacy terminal row and inline syscalls. -/
inductive ExecutionRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 24 < p)] where
  | instruction (row : DecodedInstructionRow p)
  | halt (row : HaltChip.Inputs (ZMod p))
  | syscall (row : SyscallInstrsChip.Inputs (ZMod p))

/-- One row's semantic carrier. Subsequent alignment chooses read currency points; refresh
elimination may replace prior records by equal-value earlier records. -/
noncomputable def ExecutionRow.facts (data : ProverData (ZMod p)) : ExecutionRow p → RowFacts p
  | .instruction row => row.ordinaryRowFacts data
  | .halt row => haltRowFacts row
  | .syscall row => syscallRowFacts row

/-- A physical row fixes its semantic facts and exact Memory occurrences in every data view. -/
theorem ExecutionRow.facts_setData (row : ExecutionRow p) (data data' : ProverData (ZMod p)) :
    row.facts data = row.facts data' := by
  cases row with
  | instruction row =>
      have interactions : row.interactionsWith data memoryChannel = row.interactionsWith data' memoryChannel := by
        apply List.map_injective_iff.mpr TypedInteraction.raw_injective
        simp only [DecodedInstructionRow.interactionsWith_raw]
        exact Operations.interactionValuesWith_congr rfl
      simp only [ExecutionRow.facts, DecodedInstructionRow.ordinaryRowFacts,
        DecodedInstructionRow.toChipRow_setData row data data',
        DecodedInstructionRow.consumedMemoryMessages, DecodedInstructionRow.producedMemoryMessages,
        interactions]
  | halt _ | syscall _ => rfl

/-- The complete State edge, before canonical re-limbing. -/
noncomputable def ExecutionRow.edge (data : ProverData (ZMod p)) :
    ExecutionRow p → StateMsg (ZMod p) × StateMsg (ZMod p)
  | .instruction row => decodedStateEdge data row
  | .halt row => (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row)
  | .syscall row => (SyscallInstrsChip.statePulledMessage row, SyscallInstrsChip.statePushedMessage row)

theorem ExecutionRow.edge_eq_facts (data : ProverData (ZMod p)) (row : ExecutionRow p) :
    row.edge data = ((row.facts data).statePull, (row.facts data).statePush) := by
  cases row <;> rfl

/-- The constrained event widths, in SP1 bus ticks. -/
def ExecutionRow.duration : ExecutionRow p → ℕ
  | .instruction _ => 8
  | .halt _ | .syscall _ => 264

/-- The State edge after canonical re-limbing. -/
noncomputable def ExecutionRow.canonEdge (data : ProverData (ZMod p)) (row : ExecutionRow p) :=
  (canonState (row.edge data).1, canonState (row.edge data).2)

/-- A decoded physical row fixes its State edge independently of the prover-data view. -/
theorem ExecutionRow.edge_setData (row : ExecutionRow p) (data data' : ProverData (ZMod p)) :
    row.edge data = row.edge data' := by
  cases row <;> simp only [ExecutionRow.edge, decodedStateEdge,
    DecodedInstructionRow.toChipRow_setData _ data data']

/-- Canonical re-limbing preserves the same independence from prover data. -/
theorem ExecutionRow.canonEdge_setData (row : ExecutionRow p) (data data' : ProverData (ZMod p)) :
    row.canonEdge data = row.canonEdge data' := by
  simp only [ExecutionRow.canonEdge, row.edge_setData data data']

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 24 < p)] [Fact (2 ^ 25 < p)] in
theorem activeSystemRows_member {α : Type} (table : Table (ZMod p))
    (decode : Array (ZMod p) → α) (gate : α → ZMod p)
    {row : α} (member : row ∈ activeSystemRows table decode gate) :
    ∃ physical ∈ table.table, decode physical = row ∧ gate row = 1 := by
  obtain ⟨mapped, active⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  exact ⟨physical, physicalMem, rfl, of_decide_eq_true active⟩

omit [Fact (2 ^ 25 < p)] in
theorem syscall_halt_binary (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit }) (constraints : table.Constraints data)
    {physical : Array (ZMod p)} (member : physical ∈ table.table) :
    (syscallInstrsRow data physical).is_halt = 0 ∨ (syscallInstrsRow data physical).is_halt = 1 := by
  have checked := constraints physical member
  rw [component] at checked
  have binary := SyscallInstrsChip.haltSelectorBinary_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints SyscallInstrsChip.circuit _ checked)
  simpa only [syscallInstrsRow_eq, circuit_norm] using binary

omit [Fact (2 ^ 24 < p)] in
theorem halt_advancing (row : HaltChip.Inputs (ZMod p))
    (bounds : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8) :
    StateChronology.Advancing (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row) ∧
      StateMsg.timeNat (HaltChip.statePushedMessage row) =
        StateMsg.timeNat (HaltChip.statePulledMessage row) + 264 := by
  have step : StateMsg.timeNat (HaltChip.statePushedMessage row) =
      StateMsg.timeNat (HaltChip.statePulledMessage row) + 264 :=
    TimeExtraction.clkNat_add_syscall_of_cpuState_bounds _ _ _ bounds.1 bounds.2
  refine ⟨⟨?_, rfl, Or.inr ?_⟩, step⟩
  · dsimp only
    rw [step]; omega
  · change (0 : ZMod p).val < 2 ^ 16 ∧ (0 : ZMod p).val < 2 ^ 16
    simp

omit [Fact (2 ^ 24 < p)] in
theorem syscall_advancing (row : SyscallInstrsChip.Inputs (ZMod p))
    (bounds : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8)
    (binary : row.is_halt = 0 ∨ row.is_halt = 1) (real : row.is_real = 1)
    (arm : (row.is_halt = 1 → row.next_pc[0] = 1 ∧ row.next_pc[1] = 0 ∧ row.next_pc[2] = 0) ∧
      (row.is_real = 1 → row.is_halt = 0 → row.next_pc[0] = row.state.pc[0] + 4 ∧
        row.next_pc[1] = row.state.pc[1] ∧ row.next_pc[2] = row.state.pc[2])) :
    StateChronology.Advancing (SyscallInstrsChip.statePulledMessage row, SyscallInstrsChip.statePushedMessage row) ∧
      StateMsg.timeNat (SyscallInstrsChip.statePushedMessage row) =
        StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 264 := by
  have step : StateMsg.timeNat (SyscallInstrsChip.statePushedMessage row) =
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 264 :=
    TimeExtraction.clkNat_add_syscall_of_cpuState_bounds _ _ _ bounds.1 bounds.2
  refine ⟨⟨?_, rfl, ?_⟩, step⟩
  · dsimp only
    rw [step]; omega
  · rcases binary with inactive | active
    · exact Or.inl (arm.2 real inactive).2
    · change (_ ∧ _) ∨ row.next_pc[1].val < 2 ^ 16 ∧ row.next_pc[2].val < 2 ^ 16
      right
      rw [(arm.1 active).2.1, (arm.1 active).2.2]
      simp

end SP1Clean.Soundness.NativeCore
