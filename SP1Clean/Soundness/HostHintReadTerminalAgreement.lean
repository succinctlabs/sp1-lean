import SP1Clean.Soundness.HostTerminalLedger
import SP1Clean.Soundness.HostHintReadTerminalProjection
import SP1Clean.Soundness.HostHintReadExecutionPath
import SP1Clean.Model.Core.HostReplay

/-! # Optional terminal status agrees with the actual CPU replay

Full HostCall accounting connects terminal receipts to the carrier's syscall events. Legacy
padding contributes no event. The existing path supplies exactly the optional status checked
by the verifier, including running identities, stopped identities, and HALT with exit zero.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Model.Core NativeCore HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance terminalAgreementLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem wrapper_receipt (input : HostCallChip.Inputs (ZMod p)) (flag : ZMod p) :
    hostExitAfter none (ExecutionRow.syscall input.instruction).event =
      (HostTerminalLedger.receipt? (input.message flag)).map (fun word => (Word.toBitVec64 word).setWidth 32) := by
  simp only [hostExitAfter, ExecutionRow.event, rawCode_syscallEventOfRow,
    arg1_syscallEventOfRow, HostTerminalLedger.receipt?, HostCallChip.Inputs.message, SyscallKind.code]
  -- Both `if`s decide the same halt test, spelled folded on the right and unfolded on the left.
  by_cases h : Word.toBitVec64 input.instruction.op_a_memory.prev_value = 0
  · have h' := h
    simp only [Word.toBitVec64, Word.toNat] at h'
    simp only [h, h', if_true, Option.map_some]
    rfl
  · have h' := h
    simp only [Word.toBitVec64, Word.toNat] at h'
    simp only [h, h', if_false, Option.map_none]

private theorem inventory_receipts (instructions : List (DecodedInstructionRow p))
    (wrappers : List (Environment (ZMod p))) :
    ((instructions.map ExecutionRow.instruction ++
      (wrappers.map fun env => ExecutionRow.syscall (HostCallLedger.input env).instruction)).filterMap
        (fun row => hostExitAfter none row.event)) =
      ((wrappers.map HostCallLedger.call).filterMap HostTerminalLedger.receipt?).map
        (fun word => (Word.toBitVec64 word).setWidth 32) := by
  have selected := HostQueueCPUReplay.filterMap_inventory
    ExecutionRow.instruction ExecutionRow.halt (fun env => ExecutionRow.syscall (HostCallLedger.input env).instruction)
    HostCallLedger.call (fun row => hostExitAfter none row.event)
    (fun message => (HostTerminalLedger.receipt? message).map (fun word => (Word.toBitVec64 word).setWidth 32))
    instructions [] wrappers (fun _ _ => rfl) (by simp) (fun env => wrapper_receipt (HostCallLedger.input env) _)
  simpa only [List.map_nil, List.append_nil, List.map_filterMap] using selected

variable {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
  {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- Every semantic HALT receipt is exactly one authenticated physical handler receipt. -/
theorem GroundingCarrier.terminal_receipts
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (carrier.events.filterMap (hostExitAfter none)).Perm
      (((HostLocalHandoff.calls (HostHintQueueBoundary.projected witness)).filterMap
        HostTerminalLedger.receipt?).map (fun word => (Word.toBitVec64 word).setWidth 32)) := by
  have inventory : ((LocalCore.executionRows
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).filterMap
        (fun row => hostExitAfter none row.event)) =
      ((HostCallLedger.calls (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness)) witness.data).filterMap
        HostTerminalLedger.receipt?).map (fun word => (Word.toBitVec64 word).setWidth 32) := by
    have wrappers := HostLocalCore.hostCallTable_projection (HostHintQueueBoundary.projected witness)
    simp only [HostHintQueueBoundary.projected_data] at wrappers
    rw [LocalCore.executionRows, HostHintReadTerminal.legacy_rows_nil witness constraints,
      List.map_nil, List.append_nil, ← wrappers, List.map_map]
    exact inventory_receipts _ _
  have physical := (carrier.exhaustive.map ExecutionRow.event).filterMap (hostExitAfter none)
  simp only [List.filterMap_map, Function.comp_def] at physical
  rw [inventory] at physical
  have interface := source_interface (p := p) source.host.io.hints
  have handoff := HostLocalHandoff.calls_perm_of_balancedChannel (HostHintQueueBoundary.projected witness)
    (resources_hostCall_silent interface) (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced)
  simp only [HostHintQueueBoundary.projected_data] at handoff
  simpa only [ExecutionCarrier.events, List.filterMap_map, Function.comp_def] using
    physical.trans ((handoff.filterMap HostTerminalLedger.receipt?).map
      (fun word => (Word.toBitVec64 word).setWidth 32))

private theorem decode_exit (code : BitVec 32) :
    (Word.toBitVec64 (HostExitBoundary.encode (p := p) code)).setWidth 32 = code := by
  simp [HostExitBoundary.encode, Target.toBitVec64_bitVecToWord]

private theorem option_eq_of_perm {α : Type*} (left right : Option α)
    (same : left.toList.Perm right.toList) : left = right := by
  cases left <;> cases right
  · rfl
  · simp at same
  · simp at same
  · exact congrArg some (List.cons.inj (List.perm_singleton.mp same)).1

/-- The supplied optional exit is the actual endpoint's status, without a running-source premise. -/
theorem GroundingCarrier.final_terminal (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (path : ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events target) : target.host.exitCode = bankFinal.exitCode := by
  by_cases running : source.host.exitCode = none
  · have semantic := path.exit_receipts
    change carrier.events.filterMap (hostExitAfter none) =
      (if source.host.exitCode = none then target.host.exitCode.toList else []) at semantic
    rw [if_pos running] at semantic
    have ledger := (HostTerminalLedger.receipts witness constraints balanced).map
      (fun word => (Word.toBitVec64 word).setWidth 32)
    rw [if_pos running] at ledger
    have decoded : (bankFinal.exitCode.toList.map (HostExitBoundary.encode (p := p))).map
        (fun word => (Word.toBitVec64 word).setWidth 32) = bankFinal.exitCode.toList := by
      simp only [List.map_map, Function.comp_def, decode_exit, List.map_id_fun', id_eq]
    rw [decoded] at ledger
    have agrees := (carrier.terminal_receipts constraints balanced).trans ledger
    rw [semantic] at agrees
    exact option_eq_of_perm _ _ agrees
  · have status := (HostTerminalLedger.source_status witness balanced).resolve_left running
    have unchanged := (path.of_halted running).2
    rw [unchanged]
    exact status

end SP1Clean.Soundness.HostHintReadCPU
