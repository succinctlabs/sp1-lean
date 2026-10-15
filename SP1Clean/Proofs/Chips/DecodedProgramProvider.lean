import SP1Clean.Model.Core.ProgramTable
import SP1Clean.Proofs.Chips.FixedProgramProvider

/-! # Constructing fixed Program-provider rows from the checked image

The provider's fixed lookup is the computed ROM table. The constructor supplies a complete
message and an arbitrary lookup count, including zero-count padding, and discharges the circuit's
prover assumptions. Its semantic contract reaches the checked program's actual ROM and official
Sail decoding in `DecodedProgramProvider/Bridge.lean`, including at zero multiplicity.
-/

namespace SP1Clean.DecodedProgramProvider

open Circuit SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The whole-row circuit specialized to the image's computed fixed table. -/
def circuit (image : ProgramImage) := FixedProgramProvider.circuit (image.programTable (p := p))

/-- Supply the multiplicity without changing any field of the fetched instruction. -/
def inputOfMessage (msg : ProgramMsg (ZMod p)) (multiplicity : ZMod p) :
    ProgramProviderChip.Inputs (ZMod p) where
  pc0 := msg.pc0
  pc1 := msg.pc1
  pc2 := msg.pc2
  opcode := msg.opcode
  op_a := msg.op_a
  op_b := msg.op_b
  op_c := msg.op_c
  op_a_0 := msg.op_a_0
  imm_b := msg.imm_b
  imm_c := msg.imm_c
  multiplicity

/-- Supply all row inputs directly from a listed ROM entry. -/
def populate? (image : ProgramImage) (entry : BitVec 64 × BitVec 32) (multiplicity : ZMod p) :
    Option (ProgramProviderChip.Inputs (ZMod p)) :=
  if entry ∈ image.rom then (ProgramTable.message? entry).map (inputOfMessage · multiplicity)
  else none

omit [Fact (2 ^ 17 < p)] in
/-- Constructor success depends only on membership and executable decoding. -/
theorem populate_isSome_iff (image : ProgramImage) (entry : BitVec 64 × BitVec 32)
    (multiplicity : ZMod p) :
    (populate? image entry multiplicity).isSome = true ↔
      entry ∈ image.rom ∧ (ProgramTable.message? (p := p) entry).isSome = true := by
  simp only [populate?]
  split <;> simp_all

/-- The constructor discharges every provider assumption, including complete fixed membership. -/
theorem populate_assumptions {image : ProgramImage} {entry : BitVec 64 × BitVec 32}
    {multiplicity : ZMod p} {input : ProgramProviderChip.Inputs (ZMod p)}
    (populated : populate? image entry multiplicity = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit image).ProverAssumptions input data hint := by
  unfold populate? at populated
  split at populated
  · rename_i member
    obtain ⟨msg, decoded, rfl⟩ := Option.map_eq_some_iff.mp populated
    change ProgramMsg.RowSpec msg ∧ image.programTable.Spec msg
    exact ⟨ProgramTable.message_rowSpec decoded,
      (image.programTable_spec msg).mpr ⟨entry, member, decoded⟩⟩
  · cases populated

end SP1Clean.DecodedProgramProvider
