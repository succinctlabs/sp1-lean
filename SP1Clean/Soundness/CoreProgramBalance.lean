import SP1Clean.Soundness.NativeCoreFinalBoundary
import SP1Clean.Soundness.TypedProgram

/-! # Shared Program authentication for native core assemblies

The fixed image table authenticates every active Program fetch. All other native components are
silent or emit gated unit pulls. Clean's actual count-bounded balance therefore authenticates each
active fetch, independently of table order and of State/Memory grounding.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- A structural Program consumer contributes only disabled interactions or unit pulls. -/
def ProgramPulls (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith programChannel.toRaw
      (Environment.fromArray physical data), interaction.mult = 0 ∨ interaction.mult = -1

omit [Fact (2 ^ 24 < p)] in
theorem programPulls_of_silent (component : Component (ZMod p))
    (silent : programChannel.toRaw ∉ component.circuit.channels) : ProgramPulls component := by
  intro data physical _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith programChannel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

private theorem instruction_programPulls (component : Component (ZMod p))
    (member : component ∈ sp1Tables (p := p)) : ProgramPulls component := by
  obtain ⟨chip, chipMem, rfl⟩ := List.mem_map.mp member
  intro data physical constraints interaction emitted
  rw [supportedChip_programEmissionShape chip chipMem data physical constraints] at emitted
  obtain rfl := List.mem_singleton.mp emitted
  rcases supportedChip_selectorConstraintShape chip chipMem data physical constraints with zero | one
  · left
    change -(chip.decodeRow data physical).is_real = 0
    rw [show (chip.decodeRow data physical).is_real = 0 from zero, neg_zero]
  · right
    change -(chip.decodeRow data physical).is_real = -1
    rw [show (chip.decodeRow data physical).is_real = 1 from one]

omit [Fact (2 ^ 24 < p)] in
private theorem programPulls_of_gated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (gate : Var Input (ZMod p) → Expression (ZMod p))
    (message : Var Input (ZMod p) → Var ProgramMsg (ZMod p))
    (emission : ∀ input offset, ((circuit.main input).operations offset).interactionsWith
      programChannel.toRaw = [(programChannel.pulledIf (gate input) (message input)).toRaw])
    (binary : ∀ input offset env,
      ConstraintsHold.Shallow env ((circuit.main input).operations offset) →
        env (gate input) = 0 ∨ env (gate input) = 1) : ProgramPulls { circuit } := by
  intro data physical constraints interaction member
  have bound := binary (varFromOffset Input 0) (size Input) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints circuit _ constraints)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((circuit.main (varFromOffset Input 0)).operations
    (size Input)).interactionsWith programChannel.toRaw).map _ at member
  rw [emission] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, neg_eq_zero, neg_inj]
  simpa only [CircuitType.eval_expr] using bound

private theorem halt_programPulls : ProgramPulls ({ circuit := HaltChip.circuit } : Component (ZMod p)) :=
  programPulls_of_gated HaltChip.circuit (fun input => input.is_real) HaltChip.programMsg
    HaltChip.interactionsWith_program_eq HaltChip.selectorBinary_of_shallow

private theorem syscall_programPulls : ProgramPulls ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)) :=
  programPulls_of_gated SyscallInstrsChip.circuit (fun input => input.is_real) SyscallInstrsChip.programMsg
    Faithful.syscallInstrsInteractionsWith_program SyscallInstrsChip.selectorBinary_of_shallow

private theorem remainingProvider_programPulls (component : Component (ZMod p))
    (member : component ∈ (sp1ProviderTables (p := p)).take 23 ++ sp1ProviderTables.drop 26) :
    ProgramPulls component := by
  rw [sp1ProviderTables, ← List.map_take, ← List.map_drop, ← List.map_append] at member
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have noProgram : .program ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noInit : .memoryInit ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noFinal : .memoryFinalize ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  cases id with
  | program => exact (noProgram idMem).elim
  | memoryInit => exact (noInit idMem).elim
  | memoryFinalize => exact (noFinal idMem).elim
  | halt => exact halt_programPulls
  | syscallInstrs => exact syscall_programPulls
  | byte provider =>
      apply programPulls_of_silent
      cases provider <;> change programChannel.toRaw ∉ [byteChannel.toRaw]
      all_goals simp [programChannel_eq_byteChannel_false]
  | range width =>
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [byteChannel.toRaw]
      simp [programChannel_eq_byteChannel_false]
  | memoryBump =>
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [byteChannel.toRaw, memoryChannel.toRaw, memoryChannel.toRaw]
      simp [programChannel_eq_byteChannel_false, programChannel_eq_memoryChannel_false]
  | stateBump =>
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
      simp [programChannel_eq_byteChannel_false, programChannel_eq_stateChannel_false]

/-- Only the computed ROM can produce Program messages in the shared execution suffix. -/
theorem interior_program_source (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ afterFinalTables image) :
    component = ({ circuit := DecodedProgramProvider.circuit image } : Component (ZMod p)) ∨ ProgramPulls component := by
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | instruction) | providers
  · exact Or.inl rfl
  · exact Or.inr (instruction_programPulls component instruction)
  · exact Or.inr (remainingProvider_programPulls component (List.mem_append.mpr providers))

/-- Count-bounded Program balance authenticates a pull whenever the checked ROM is the sole
possible producer. The enclosing ensemble and its source-state policy are arbitrary. -/
theorem program_pull_committed_of_sources {Public : TypeMap} [ProvableType Public]
    {assembly : Ensemble (ZMod p) Public} {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness assembly) (constraints : witness.Constraints)
    (balance : BalancedInteractions (witness.interactionsWith programChannel.toRaw))
    (verifier : ∀ (input : Public (ZMod p)) (data : ProverData (ZMod p)),
      ∀ interaction ∈ assembly.verifierOperations.interactionValuesWith programChannel.toRaw
        (Environment.fromInput input data), interaction.mult = 0 ∨ interaction.mult = -1)
    (sources : ∀ component ∈ assembly.tables,
      component = ({ circuit := DecodedProgramProvider.circuit image } : Component (ZMod p)) ∨ ProgramPulls component)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.mult = -1)
    (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) := by
  obtain ⟨source, sourceMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balance interaction member active
  rcases EnsembleWitness.mem_interactionsWith.mp sourceMem with verifierMem | ⟨table, tableMem, sourceMem⟩
  · exact ((verifier witness.publicInput witness.data source verifierMem).elim nonzero notPull).elim
  · obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp sourceMem
    have checked := constraints table tableMem physical physicalMem
    rcases sources table.component
      (EnsembleWitness.mem_component_of_mem tableMem) with fixed | pulls
    · rw [fixed] at emitted checked
      have committed := DecodedProgramProvider.constraints_committed valid (Environment.fromArray physical witness.data) checked
      have same := (DecodedProgramProvider.program_interaction_payload image _ source emitted).symm.trans
        (samePayload.trans payload)
      have messageEq : (({ circuit := DecodedProgramProvider.circuit image } : Component (ZMod p)).rowInput
          (Environment.fromArray physical witness.data)).toMessage = message := by
        have vectorEq := Vector.toArray_inj.mp same
        have decoded := congrArg (fromElements (M := ProgramMsg)) vectorEq
        simpa only [ProvableType.fromElements_toElements] using decoded
      rw [messageEq] at committed
      exact committed
    · exact ((pulls witness.data physical checked source emitted).elim nonzero notPull).elim

end SP1Clean.Soundness.NativeCore
