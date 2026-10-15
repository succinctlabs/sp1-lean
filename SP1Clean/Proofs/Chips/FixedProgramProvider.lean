import ToClean.Gadgets.LookupProjection
import SP1Clean.Proofs.Chips.ProgramProviderChip
import Clean.Air.FlatComponent

/-! # A program provider bound to concrete fixed rows

The original provider establishes row-local range facts but does not constrain the program's
opcode and operand contents. This wrapper composes that provider and a static-table lookup on
the complete message. The fixed table is an ensemble parameter, independent of prover data.

Its specification records actual fixed-ROM membership. A native program decoder must supply the
table and prove its rows describe the checked program; that construction is separate from this
whole-row circuit proof. Zero-multiplicity padding also uses a valid fixed row.
-/

namespace SP1Clean.FixedProgramProvider

open Circuit
open SP1Clean.Channels (ProgramMsg programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The existing range-checked provider, strengthened with complete fixed-program membership. -/
def circuit (rom : StaticTable (ZMod p) ProgramMsg) :
    GeneralFormalCircuit (ZMod p) ProgramProviderChip.Inputs unit where
  name := "sp1.native.program.fixed"
  main input := do
    let _ ← ProgramProviderChip.circuit input
    lookup rom.toTable input.toMessage
  Spec input _ _ := ProgramMsg.RowSpec input.toMessage ∧ rom.Spec input.toMessage
  ProverAssumptions input _ _ := ProgramMsg.RowSpec input.toMessage ∧ rom.Spec input.toMessage
  channelsWithRequirements := [programChannel.toRaw]
  soundness := by
    circuit_proof_start [ProgramProviderChip.circuit, ProgramProviderChip.Inputs.toMessage]
    exact h_holds
  completeness := by
    circuit_proof_start [ProgramProviderChip.circuit, ProgramProviderChip.Inputs.toMessage]
    exact h_assumptions

/-- Adding fixed membership preserves the provider's exact Program payload and multiplicity. -/
theorem main_program_interactions (rom : StaticTable (ZMod p) ProgramMsg)
    (input : Var ProgramProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    (((circuit rom).main input).operations offset).interactionsWith programChannel.toRaw =
      [(programChannel.pushedIf input.multiplicity input.toMessage).toRaw] := by
  have emitted := InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact
    ProgramProviderChip.circuit programChannel.toRaw input offset
    [.lookup ⟨rom.toTable.toRaw, toElements input.toMessage⟩]
    (programChannel.pushedIf input.multiplicity input.toMessage).toRaw
    (ProgramProviderChip.main_program_interactions input offset)
  simpa only [circuit, circuit_norm] using emitted

omit [Fact (2 ^ 17 < p)] in
private theorem payload_of_program_emission
    (provider : GeneralFormalCircuit (ZMod p) ProgramProviderChip.Inputs unit)
    (emission : ∀ input offset, ((provider.main input).operations offset).interactionsWith
      programChannel.toRaw = [(programChannel.pushedIf input.multiplicity input.toMessage).toRaw])
    (env : Environment (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ ({ circuit := provider } : Air.Flat.Component (ZMod p)).operations.interactionValuesWith
      programChannel.toRaw env) :
    interaction.msg = (toElements
      (({ circuit := provider } : Air.Flat.Component (ZMod p)).rowInput env).toMessage).toArray := by
  rw [Operations.interactionValuesWith, Air.Flat.Component.interactionsWith_eq] at member
  change interaction ∈ (((provider.main (varFromOffset ProgramProviderChip.Inputs 0)).operations
    (size ProgramProviderChip.Inputs)).interactionsWith programChannel.toRaw).map _ at member
  rw [emission] at member
  obtain rfl := List.mem_singleton.mp member
  have evaluated := Channel.eval_pushedIf (channel := programChannel (p := p))
    (enabled := (varFromOffset ProgramProviderChip.Inputs 0).multiplicity)
    (msg := (varFromOffset ProgramProviderChip.Inputs 0).toMessage) (env := env)
  exact (congrArg Interaction.msg evaluated).trans (by
    change (toElements (eval env (varFromOffset ProgramProviderChip.Inputs 0).toMessage)).toArray = _
    rw [ProgramProviderChip.Inputs.eval_toMessage]
    simp only [eval_varFromOffset_valueFromOffset, Air.Flat.Component.rowInput])

/-- The evaluated ledger preserves the complete provider input as its Program payload. -/
theorem program_interaction_payload (rom : StaticTable (ZMod p) ProgramMsg)
    (env : Environment (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ ({ circuit := circuit rom } : Air.Flat.Component (ZMod p)).operations.interactionValuesWith
      programChannel.toRaw env) :
    interaction.msg = (toElements
      (({ circuit := circuit rom } : Air.Flat.Component (ZMod p)).rowInput env).toMessage).toArray :=
  payload_of_program_emission (circuit rom) (main_program_interactions rom) env interaction member

/-- The fixed program provider authenticates exactly the supplied ROM table. -/
@[circuit_norm] theorem main_lookupNames (rom : StaticTable (ZMod p) ProgramMsg)
    (input : Var ProgramProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    (((circuit rom).main input).operations offset).lookups.map (·.table.name) = [rom.name] := by
  simp [circuit, ProgramProviderChip.circuit, ProgramProviderChip.main,
    Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]
  rfl

end SP1Clean.FixedProgramProvider
