import SP1Clean.Model.Core.ExecutionWritePolicy
import SP1Clean.Model.Core.NativeLayout

/-! # Native instruction and timestamp representability

Sail's successful memory accesses need not be aligned. The native instruction chips additionally
require width alignment; this named semantic restriction is independent of compiler success.
The active clock phase comes from the native CPUState circuit's thirteen-bit range check of
`(clk_0_16 - 1) / 8`, used by ordinary and host rows alike. It implies the local access window.
Unused endpoints, including stopped identities, have no active-window or fetch obligation.
-/

namespace SP1Clean.Model.Core
open Machine Soundness.Target LeanRV64D.Defs Semantics

/-- A decoded native memory instruction uses a width-aligned span wholly inside guest memory. -/
def instructionMemoryEncoded (register : BitVec 5 → Option (BitVec 64)) : instruction → Prop
  | .LOAD (offset, rs1, _, _, width) | .STORE (offset, _, rs1, width) =>
      ∃ base, register (regidxBits rs1) = some base ∧
        let address := (memoryEffectiveAddress base offset).toNat
        NativeLayout.guestMemory.ContainsSpan address width.toNat ∧ address % width.toNat = 0
  | _ => True

/-- Ordinary decoding uses the existing configured Sail decoder and canonical image/routing checks. -/
def ordinaryEncodedAt (program : GuestProgram) (source : SailState) : Prop :=
  ∃ pc word decoded, source.regs.get? Register.PC = some pc ∧
    program.fetchWord pc = some word ∧ ConfiguredDecode word decoded ∧
    instructionImageOK decoded = true ∧ (instructionRouteId decoded).isSome = true ∧
    instructionMemoryEncoded source.get_reg? decoded

/-- The active source's RAM/C/B/A offsets fit the same low timestamp limb without carry. -/
def activeClockWindow (clock : ℕ) : Prop := clock % 2 ^ 24 + 4 < 2 ^ 24

/-- Active native CPU rows have phase one modulo eight, enforced by their shared range lookup. -/
def activeClockPhase (clock : ℕ) : Prop := clock % 8 = 1

/-- The circuit-enforced phase leaves room for all four ordinary memory positions. -/
theorem activeClockPhase.window {clock : ℕ} (phase : activeClockPhase clock) : activeClockWindow clock := by
  have congruent : clock % 2 ^ 24 % 8 = 1 := by
    rw [Nat.mod_mod_of_dvd clock (by decide : 8 ∣ 2 ^ 24)]
    exact phase
  have bound := Nat.mod_lt clock (by decide : 0 < 2 ^ 24)
  unfold activeClockWindow
  omega

/-- Encoding conditions on one actual event source. Host access bounds are checked by its interpreter. -/
def eventEncodedAt (program : GuestProgram) (source : ExecutionState) (event : ExecutionEvent) : Prop :=
  activeClockPhase source.clock ∧
    (event = .ordinary → ordinaryEncodedAt program source.sail)

namespace ExecutionPath

/-- Every actual occurrence has native encoding conditions at its complete replayed source. -/
def Encoded (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) : Prop :=
  ∀ n current event, events[n]? = some event →
    replayEvents? policy program source (events.take n) = some current →
      eventEncodedAt program current event

variable {policy : HostPolicy} {program : GuestProgram}
  {source middle target : ExecutionState} {event : ExecutionEvent} {events first second : List ExecutionEvent}

@[simp] theorem encoded_nil : Encoded policy program source [] := by
  intro n current event atEvent
  simp at atEvent

theorem encoded_cons_iff (step : ExecutionStep policy program source event middle) :
    Encoded policy program source (event :: events) ↔
      eventEncodedAt program source event ∧ Encoded policy program middle events := by
  constructor
  · intro encoded
    refine ⟨encoded 0 source event rfl rfl, ?_⟩
    intro n current label atEvent replay
    apply encoded (n + 1) current label (by simpa only [List.getElem?_cons_succ] using atEvent)
    simpa only [List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using replay
  · rintro ⟨head, tail⟩ n current label atEvent replay
    cases n with
    | zero =>
      cases Option.some.inj replay
      cases Option.some.inj atEvent
      exact head
    | succ n =>
      apply tail n current label (by simpa only [List.getElem?_cons_succ] using atEvent)
      simpa only [List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using replay

/-- Exact composition of encoding conditions at the shared semantic boundary. -/
theorem encoded_append_iff (left : ExecutionPath policy program source first middle) :
    Encoded policy program source (first ++ second) ↔
      Encoded policy program source first ∧ Encoded policy program middle second := by
  induction left with
  | nil => simp only [List.nil_append, encoded_nil, true_and]
  | cons step _ ih => simp only [List.cons_append, encoded_cons_iff step, ih, and_assoc]

/-- Cutting an encoded path introduces no phase reset or new fetch at the cut itself. -/
theorem Encoded.split (encoded : Encoded policy program source events)
    (path : ExecutionPath policy program source events target) (cut : ℕ) :
    ∃ middle, ExecutionPath policy program source (events.take cut) middle ∧
      ExecutionPath policy program middle (events.drop cut) target ∧
      Encoded policy program source (events.take cut) ∧ Encoded policy program middle (events.drop cut) := by
  obtain ⟨middle, left, right⟩ := path.split cut
  have both := (encoded_append_iff left).mp
    (show Encoded policy program source (events.take cut ++ events.drop cut) by
      simpa only [List.take_append_drop] using encoded)
  exact ⟨middle, left, right, both⟩

end ExecutionPath
end SP1Clean.Model.Core
