import SP1Clean.Soundness.HostHintReadExecutionPath
import SP1Clean.Soundness.HostHintReadBanks
import SP1Clean.Model.Core.SailBookkeeping

/-! # Complete retirement bookkeeping along the installed local execution

The same exhaustive CPU walk determines the ordinary-step count and last ordinary nextPC.
Actual chip effects authenticate each update, while all host adapters frame these registers.
No instruction dispatch, replay-success, or bookkeeping agreement is supplied by the caller of
the endpoint execution theorem. Binding these observations to a supplied target remains separate.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core NativeCore HostHintReadLocal
open LeanRV64D.Defs (Register)

private def retirementObservation (state : SailState) : Bool × Option Bool × Option (BitVec 64) :=
  (retirementEnabled state, state.regs.get? Register.minstret_increment, state.regs.get? Register.minstret)

private theorem ordinary_retirement {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] {program : Target.GuestProgram}
    {row : Trace.RowView (ZMod p)} {current next : SailState}
    (effect : Target.RowEffect program row current next) :
    retirementObservation next = retirementTick (retirementObservation current) true := by
  have enabledFrame : retirementEnabled next = retirementEnabled current := by
    unfold retirementEnabled
    rw [effect.otherRegs Register.mcountinhibit (by decide) (by decide) (by decide) (by decide)
      (fun index => by unfold reg_idx_to_Register; split <;> decide),
      effect.otherRegs Register.minstretcfg (by decide) (by decide) (by decide) (by decide)
        (fun index => by unfold reg_idx_to_Register; split <;> decide)]
  obtain ⟨enabled, ran, flag, counter⟩ := effect.retirement
  have observed := retirementEnabled_of_run ran
  simp only [retirementObservation, retirementTick, ↓reduceIte]
  simp only [enabledFrame, observed, flag, counter]
  cases enabled <;> simp [Sail.BitVec.addInt]

private theorem host_retirement (execution : HostExecution) (current : SailState) (pc : BitVec 64) :
    retirementObservation (execution.apply current pc) = retirementObservation current := by
  unfold retirementObservation retirementEnabled
  rw [execution.other_register_frame current pc Register.mcountinhibit (by decide) (by decide),
    execution.other_register_frame current pc Register.minstretcfg (by decide) (by decide),
    execution.other_register_frame current pc Register.minstret_increment (by decide) (by decide),
    execution.other_register_frame current pc Register.minstret (by decide) (by decide)]

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance bookkeepingLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance bookkeepingLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem step_bookkeeping (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {n : ℕ} {current next : ExecutionState} {row : ExecutionRow p}
    (atRow : carrier.ordered[n]? = some row)
    (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (carrier.events.take n) = some current)
    (replay : replayStep? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current row.event = some next) :
    retirementObservation next.sail = retirementTick (retirementObservation current.sail) row.event.isOrdinary ∧
      next.sail.regs.get? Register.nextPC =
        if row.event.isOrdinary then next.sail.regs.get? Register.PC else current.sail.regs.get? Register.nextPC := by
  cases row with
  | instruction row =>
    have effect := (carrier.instruction_effect_at valid constraints balanced atRow prefixReplay replay).2
    exact ⟨ordinary_retirement effect, effect.nextPC⟩
  | syscall row | halt row =>
    have step := (replayHost?_eq_some_iff _ _ _ _ _).mp replay
    cases step with
    | syscall ran =>
      obtain ⟨pc, execution, _, _, _, _, sail, _⟩ := HostState.step_observations ran
      rw [sail]
      exact ⟨host_retirement execution current.sail pc,
        execution.other_register_frame current.sail pc Register.nextPC (by decide) (by decide)⟩

/-- The actual ordinary inventory fixes both retirement slots, preserving the source enable
policy and handling empty segments, inhibited counting, and wraparound uniformly. -/
theorem GroundingCarrier.retirement (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    target.sail.regs.get? Register.minstret_increment =
        (if carrier.events.countP Machine.ExecutionEvent.isOrdinary = 0
          then source.sail.registers.get? Register.minstret_increment
          else some (retirementEnabled source.sail.realize)) ∧
      target.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
        (fun value => value + BitVec.ofNat 64
          (if retirementEnabled source.sail.realize then carrier.events.countP Machine.ExecutionEvent.isOrdinary else 0)) := by
  have folded := replayEvents?_fold ExecutionRow.event (fun state => retirementObservation state.sail)
    (fun values row => retirementTick values row.event.isOrdinary) replay
    (fun n current next row atRow prefixReplay step =>
      (step_bookkeeping valid carrier constraints balanced atRow
        (by simpa only [ExecutionCarrier.events, List.map_take] using prefixReplay) step).1)
  rw [retirementTick_fold] at folded
  have count : carrier.ordered.countP (fun row => row.event.isOrdinary) =
      carrier.events.countP Machine.ExecutionEvent.isOrdinary := by
    simp only [ExecutionCarrier.events, List.countP_map, Function.comp_def]
  rw [count] at folded
  exact (Prod.mk.inj (Prod.mk.inj folded).2)

/-- Final nextPC follows from the semantic tape and final PC. Host-only and empty shards
preserve the incoming nextPC, including when HALT parks PC at its sentinel. -/
theorem GroundingCarrier.nextPC (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    target.sail.regs.get? Register.nextPC =
      nextPcAfter carrier.events (source.sail.registers.get? Register.nextPC)
        (target.sail.regs.get? Register.PC) := by
  apply replayEvents?_nextPC replay
  intro n current next event atEvent prefixReplay step
  simp only [ExecutionCarrier.events, List.getElem?_map] at atEvent
  obtain ⟨row, atRow, rfl⟩ := Option.map_eq_some_iff.mp atEvent
  exact (step_bookkeeping valid carrier constraints balanced atRow prefixReplay step).2

end SP1Clean.Soundness.HostHintReadCPU
