import SP1Clean.Proofs.Chips.DecodedProgramProvider
import SP1Clean.Model.Semantics.Truth
import SP1Clean.Proofs.Sail.InstructionDecode
import ToClean.Air.ChannelClosure

/-! # Authentic Program rows from fixed AIR constraints

The checked image computes the complete fixed table. Its circuit contract and the uniform
Sail decoder theorem establish actual ROM meaning, independently of prover data and lookup
multiplicity. This bridge needs no decoder certificate or semantic provider-validity premise.
-/

namespace SP1Clean.DecodedProgramProvider

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The whole provider contract authenticates every message against the checked image's
actual instruction ROM and official Sail decoder. This is independent of prover data and count. -/
theorem spec_committed {image : ProgramImage} (valid : image.Valid)
    {input : ProgramProviderChip.Inputs (ZMod p)} {data : ProverData (ZMod p)}
    (spec : (circuit image).Spec input () data) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg input.toMessage) := by
  obtain ⟨entry, member, decoded⟩ := (image.programTable_spec input.toMessage).mp spec.2
  obtain ⟨row, decodedRow, messageEq⟩ := Option.map_eq_some_iff.mp decoded
  have rowEq : Semantics.rowOfMsg input.toMessage = row := by rw [← messageEq]; rfl
  rw [rowEq]
  have bounds : 2 ^ 16 ≤ entry.1.toNat ∧ entry.1.toNat + 4 ≤ 2 ^ 48 :=
    (valid.2.1 entry member).2.1
  exact ProgramTable.row_committed_of_decode SailDecode.instructionDecode_agrees
    (image.fetchWord_of_mem valid member) (by omega) decodedRow

/-- A physical provider row satisfying its raw constraints names an authentic instruction in
this image. Fixed lookups are part of `ConstraintsHold`; channel balance is not a premise. -/
theorem constraints_committed {image : ProgramImage} (valid : image.Valid)
    (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit image } : Component (ZMod p)).operations.ConstraintsHold env) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg (({ circuit := circuit image } : Component (ZMod p)).rowInput env).toMessage) := by
  exact spec_committed valid (({ circuit := circuit image } : Component (ZMod p)).weakSoundness_of_no_guarantees
    rfl (by trivial) constraints).1

/-- The evaluated provider ledger has exactly the complete committed message as its payload. -/
theorem program_interaction_payload (image : ProgramImage) (env : Environment (ZMod p))
    (interaction : Interaction (ZMod p))
    (member : interaction ∈ ({ circuit := circuit image } : Component (ZMod p)).operations.interactionValuesWith
      Channels.programChannel.toRaw env) :
    interaction.msg = (toElements
      (({ circuit := circuit image } : Component (ZMod p)).rowInput env).toMessage).toArray :=
  FixedProgramProvider.program_interaction_payload image.programTable env interaction member

end SP1Clean.DecodedProgramProvider
