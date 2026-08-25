import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.Decode

/-!
# Proof-independent decode of a located transition

`Machine.LocatedTransition` is the chronological carrier shared by soundness and completeness.
This file gives it one executable decode projection: read the source PC, fetch the committed word,
and run the pinned Sail decoder.  The returned decoder state is deliberately ignored here; validity
of the exact semantic relation separately records that decoding leaves the source state unchanged.

The projection stores no decoded shadow beside the execution.  A compiler recomputes it, while the
semantic relation proves that this computation returns the instruction already justified by the
official transition evidence.
-/

open LeanRV64D.Defs
open SP1Clean.Soundness.Target

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions

/-- Decode the instruction fetched at a located transition's source PC. -/
noncomputable def decodeLocated? (program : GuestProgram) (located : Machine.LocatedTransition) :
    Option instruction := do
  let pc ← located.source.regs.get? Register.PC
  let word ← program.fetchWord pc
  match (ext_decode word).run located.source with
  | .ok decoded _ => some decoded
  | _ => none

/-- Direct constructor theorem used by the exact semantic relation. -/
theorem decodeLocated?_eq_some_of
    {program : GuestProgram} {located : Machine.LocatedTransition}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (pcEq : located.source.regs.get? Register.PC = some pc)
    (fetch : program.fetchWord pc = some word)
    (decode : (ext_decode word).run located.source = .ok decoded located.source) :
    decodeLocated? program located = some decoded := by
  simp [decodeLocated?, pcEq, fetch, decode]

/-- Successful computation exposes the fetched PC and word, without introducing a second carrier. -/
theorem decodeLocated?_components
    {program : GuestProgram} {located : Machine.LocatedTransition} {decoded : instruction}
    (generated : decodeLocated? program located = some decoded) :
    ∃ pc : BitVec 64, ∃ word : BitVec 32, ∃ decoderState : SailState,
      located.source.regs.get? Register.PC = some pc ∧
        program.fetchWord pc = some word ∧
        (ext_decode word).run located.source = .ok decoded decoderState := by
  unfold decodeLocated? at generated
  cases pcEq : located.source.regs.get? Register.PC with
  | none => simp [pcEq] at generated
  | some pc =>
      simp [pcEq] at generated
      cases fetchEq : program.fetchWord pc with
      | none => simp [fetchEq] at generated
      | some word =>
          rw [fetchEq] at generated
          change (match (ext_decode word).run located.source with
            | .ok value _ => some value
            | _ => none) = some decoded at generated
          cases decodeEq : (ext_decode word).run located.source with
          | ok value decoderState =>
              rw [decodeEq] at generated
              injection generated
              subst value
              exact ⟨pc, word, decoderState, rfl, fetchEq, decodeEq⟩
          | error exception decoderState =>
              rw [decodeEq] at generated
              contradiction

end SP1Clean.Semantics
