import SP1Clean.Soundness.CoreExecutionRow
import SP1Clean.Soundness.SyscallRowSemantics
import SP1Clean.Soundness.WalkTimeline
import SP1Clean.Soundness.MixedRowTransport

/-! # Event labels and positions independent of source policy

Both core assemblies read the same complete event labels from their physical rows. The common
alignment theorem identifies an occurrence from its derived clock, including repeated row values.
Labels describe claims to be checked by stateful replay; decoding a result does not authenticate it.
-/

namespace SP1Clean.Soundness.NativeCore

universe u

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Decode the actual HALT register words, retaining the raw code until constraints prove it zero. -/
noncomputable def haltEventOfRow (row : HaltChip.Inputs (ZMod p)) : Machine.CoreSyscallEvent where
  clock := StateMsg.timeNat (HaltChip.statePulledMessage row)
  pc := StateMsg.pcBits (HaltChip.statePulledMessage row)
  nextPc := Machine.haltPc
  rawCode := Word.toBitVec64 row.x5_memory.prev_value
  arg1 := Word.toBitVec64 row.x10_memory.prev_value
  arg2 := Word.toBitVec64 row.x11_memory.prev_value
  result := Word.toBitVec64 row.x5_memory.prev_value

/-- The semantic event carried by a physical active row. -/
noncomputable def ExecutionRow.event : ExecutionRow p → Machine.ExecutionEvent
  | .instruction _ => .ordinary
  | .halt row => .syscall (haltEventOfRow row)
  | .syscall row => .syscall (syscallEventOfRow row)

/-- Physical event widths and semantic event costs agree before execution is reconstructed. -/
theorem ExecutionRow.event_duration (event : ExecutionRow p) :
    event.event.duration = event.duration := by
  cases event <;> rfl

omit [Fact (2 ^ 25 < p)] in
/-- A positive State walk and time-preserving alignment identify the exact ordered occurrence. -/
theorem ordered_at_of_alignment {α : Type u} (facts : α → RowFacts p)
    {incoming outgoing : StateMsg (ZMod p)} {ordered : List α} {rows : List (RowFacts p)}
    (aligned : List.Forall₂ WindowAligned rows (ordered.map facts))
    (walk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush)) incoming outgoing rows)
    (gap : ∀ row ∈ rows, StateMsg.timeNat row.statePull + 8 ≤ StateMsg.timeNat row.statePush)
    {event : α} (member : event ∈ ordered) {n : ℕ}
    (atIndex : StateMsg.timeNat (facts event).statePull =
      (rowTimeline (StateMsg.timeNat incoming) rows gap).start n) :
    ordered[n]? = some event := by
  obtain ⟨k, present⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, element⟩ := List.getElem?_eq_some_iff.mp present
  have leftBound : k < rows.length := by
    have lengths := aligned.length_eq
    simp only [List.length_map] at lengths
    omega
  have related := aligned.get leftBound (by simpa only [List.length_map] using bound)
  simp only [List.get_eq_getElem, List.getElem_map, element] at related
  have pull := rowTimeline_pullTime_of_getElem? walk gap (List.getElem?_eq_getElem leftBound)
  have same : n = k := (start_injective (rowTimeline (StateMsg.timeNat incoming) rows gap))
    (atIndex.symm.trans (related.pullTime.symm.trans pull))
  rwa [same]

end SP1Clean.Soundness.NativeCore
