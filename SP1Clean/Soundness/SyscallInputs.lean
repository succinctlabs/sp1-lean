import SP1Clean.Soundness.SystemMemoryRows
import SP1Clean.Soundness.TypedTimeContracts

/-! # Component-local syscall inputs

Physical constraints and finished Byte/Program guarantees supply the syscall contract. The three
Memory pulls receive their value and clock bounds from the grounding engine's incoming currency.
These lemmas apply to any table carrying the syscall component, independently of ensemble layout.
They do not supply host effects or restrict the complete syscall register to a supported code.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open SP1Clean.Machine SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel programChannel)
open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance syscallInputs_fact24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallInputs_fact17 : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Rebuild the row's Memory guarantee from its three incoming records. -/
theorem syscallInstrsRow_memoryGuarantees_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (constraints : table.Constraints data)
    {row : Array (ZMod p)} (rowMem : row ∈ table.table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    table.component.operations.ChannelGuarantees memoryChannel.toRaw
      (Environment.fromArray row data) := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  have hbool := syscallRow_binary table data component constraints row rowMem
  refine channelGuarantees_of_consumedMessages _ memoryChannel _ hp fun msg msgMem => ?_
  rw [syscallInstrsRow_typedMemory_of_component table data component, consumedMessages, List.mem_map] at msgMem
  obtain ⟨i, iMem, rfl⟩ := msgMem
  rw [List.mem_filter, decide_eq_true_eq] at iMem
  obtain ⟨iList, iPull⟩ := iMem
  -- A push can never be on the consumed side: its multiplicity is the boolean gate itself.
  have pushImpossible : ∀ {m : MemoryMsg (ZMod p)},
      signedVal (TypedInteraction.pushedIfValue memoryChannel
        (syscallInstrsRow data row).is_real m).mult = -1 → False := by
    intro m h
    rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp hbool] at h
    rcases hbool with h0 | h1
    · rw [h0, ZMod.val_zero] at h; simp at h
    · rw [h1, ZMod.val_one] at h; simp at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at iList
  rcases iList with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow data row)
      (syscallInstrsRow data row).op_a_memory
      (syscallInstrsRow data row).op_a,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow data row))) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_self
  · exact absurd iPull pushImpossible
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow data row)
      (syscallInstrsRow data row).op_b_memory
      (syscallInstrsRow data row).op_b,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow data row)) + 3) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact absurd iPull pushImpossible
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow data row)
      (syscallInstrsRow data row).op_c_memory
      (syscallInstrsRow data row).op_c,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow data row)) + 2) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact absurd iPull pushImpossible

/-- Read the committed ECALL's local Program guarantee at one active physical row. -/
theorem syscallInstrsRow_programRowSpec_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (program : table.ChannelGuarantees data programChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ table.table)
    (real : (syscallInstrsRow data row).is_real = 1) :
    Channels.ProgramMsg.RowSpec (SyscallInstrsChip.programMessage (syscallInstrsRow data row)) := by
  have programGuarantees := program row rowMem
  have guarantee := TypedInteraction.guarantee_of_channelGuarantees
    table.component.operations programChannel
    (Environment.fromArray row data)
    (TypedInteraction.pulledIfValue programChannel (syscallInstrsRow data row).is_real
      (SyscallInstrsChip.programMessage (syscallInstrsRow data row)))
    (by rw [syscallInstrsRow_typedProgram_of_component table data component]; exact List.mem_cons_self)
    programGuarantees (by rfl)
    (by rw [TypedInteraction.pulledIfValue_mult, real])
  simpa only [TypedInteraction.pulledIfValue_message, programChannel] using guarantee

/-- The complete syscall contract and well-formed operand words, derived within incoming currency. -/
theorem syscallInstrsRow_contract_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (constraints : table.Constraints data)
    (byte : table.ChannelGuarantees data byteChannel.toRaw)
    (program : table.ChannelGuarantees data programChannel.toRaw)
    {row : Array (ZMod p)} (member : row ∈ table.table)
    (currency : ∀ mp ∈ (syscallRowFacts (syscallInstrsRow data row)).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec (syscallInstrsRow data row) ∧
      SyscallInstrsChip.PulledFacts (syscallInstrsRow data row) := by
  refine ⟨syscallInstrsRow_spec_of_component table data component constraints byte program
    (syscallInstrsRow_memoryGuarantees_of_component table data component constraints member currency) member, ?_⟩
  intro real
  obtain ⟨a, b, c⟩ := syscallRowFacts_currency_split _ currency
  exact SyscallInstrsChip.pulledFacts_of_buses _
    (syscallInstrsRow_programRowSpec_of_component table data component program member real) a b c
    (syscallInstrsRow_opAValue_isU64_of_component table data component byte member real) real

/-- The committed ECALL and the three incoming register values identify the semantic source.
No assumption about the next PC's limb representation or the host's effects is needed. -/
theorem syscallRow_sourceValues (row : SyscallInstrsChip.Inputs (ZMod p))
    (program : Target.GuestProgram)
    (committed : Target.committedInROM program (Semantics.rowOfMsg (SyscallInstrsChip.programMessage row)))
    {traj : Trajectory} {initial source : SailState} {tl : Timeline} {n : ℕ}
    (atSource : traj n = some source)
    (pc : source.regs.get? Register.PC = some (StateMsg.pcBits (syscallRowFacts row).statePull))
    (time : StateMsg.timeNat (syscallRowFacts row).statePull = tl.start n)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls,
      LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    AboutToExecuteEcall program source ∧
      source.regs.get? Register.PC = some (syscallEventOfRow row).pc ∧
      source.get_reg? 5#5 = some (syscallEventOfRow row).rawCode ∧
      source.get_reg? 10#5 = some (syscallEventOfRow row).arg1 ∧
      source.get_reg? 11#5 = some (syscallEventOfRow row).arg2 := by
  obtain ⟨fetch, shape⟩ := committed.ecall_of_opcode rfl
  have opA : row.op_a = 5 := congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_a) shape
  have opB : row.op_b = 10 := congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape
  have opC : row.op_c = 11 := congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape
  have locA := (syscallRow_locOf_reg row (i := 5#5) opA.symm row.op_a_memory row.op_a_value 4).1
  have locB := (syscallRow_locOf_reg row (i := 10#5) opB.symm row.op_b_memory row.op_b_memory.prev_value 3).1
  have locC := (syscallRow_locOf_reg row (i := 11#5) opC.symm row.op_c_memory row.op_c_memory.prev_value 2).1
  obtain ⟨curA, curB, curC⟩ := syscallRowFacts_currency_split_values row currency
  change StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) = tl.start n at time
  rw [locA, time] at curA
  rw [locB, time] at curB
  rw [locC, time] at curC
  exact ⟨⟨(syscallEventOfRow row).pc, pc, fetch⟩, pc,
    (TimedGrounding.localValueAtG_stepStart_iff atSource).mp curA,
    TimedGrounding.localValueAtG_regRead_of_traj (k := 3) atSource (by norm_num) curB,
    TimedGrounding.localValueAtG_regRead_of_traj (k := 2) atSource (by norm_num) curC⟩

end SP1Clean.Soundness
