import SP1Clean.Native.Operations.WritePermission
import ToClean.Air.ChannelClosure
import ToClean.Circuit.InteractionRecovery

/-! # Byte permission authentication from a structural ledger

A fixed provider proves writability from its raw assertions and lookup. Count-bounded balance
then authenticates every unit pull, provided the public verifier and every other component emit only
zero or unit-negative permission interactions. This separates the generic matching argument from the concrete assembly's
exhaustive source classification and from the store's byte-footprint proof.
-/

namespace SP1Clean.Soundness.WritePermission

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Consumers cannot forge a positive permission source, including on padding rows. -/
def Pulls (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith WritePermissionProvider.channel.toRaw
      (Environment.fromArray physical data), interaction.mult = 0 ∨ interaction.mult = -1

omit [Fact (2 ^ 17 < p)] in
theorem pulls_of_silent (component : Component (ZMod p))
    (silent : WritePermissionProvider.channel.toRaw ∉ component.circuit.channels) : Pulls component := by
  intro data physical _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

theorem provider_constraints (image : ProgramImage) (env : Environment (ZMod p))
    (constraints : ({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)).operations.ConstraintsHold env) :
    WritePermissionProvider.Permitted image
      (({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)).rowInput env).address :=
  (({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)).weakSoundness_of_no_guarantees
    rfl (by trivial) constraints).1

theorem provider_emission (image : ProgramImage) (input : Var WritePermissionProvider.Inputs (ZMod p))
    (offset : ℕ) :
    ((WritePermissionProvider.circuit image).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw = [(WritePermissionProvider.channel.pushed input.address).toRaw] := by
  have range (offset : ℕ) (value : Expression (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega))
      WritePermissionProvider.channel.toRaw (n := offset) value
      (by change _ ∉ []; simp) (by change _ ∉ []; simp)
  have order (offset : ℕ) (value : Var AddressOrder.Inputs (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddressOrder.circuit
      WritePermissionProvider.channel.toRaw (n := offset) value
      (by change _ ∉ []; simp) (by change _ ∉ []; simp)
  simp only [WritePermissionProvider.circuit, WritePermissionProvider.main, circuit_norm]
  simp only [range, order, List.nil_append]

theorem provider_payload (image : ProgramImage) (env : Environment (ZMod p))
    (interaction : Interaction (ZMod p))
    (member : interaction ∈ ({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)).operations.interactionValuesWith
      WritePermissionProvider.channel.toRaw env) :
    interaction.msg = (toElements
      (({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)).rowInput env).address).toArray := by
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((WritePermissionProvider.circuit image).main
    (varFromOffset WritePermissionProvider.Inputs 0)).operations (size WritePermissionProvider.Inputs)
    |>.interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [provider_emission] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [Channel.eval_pushed, Channel.pushedValue]
  have input := eval_varFromOffset_valueFromOffset WritePermissionProvider.Inputs 0 env
  have address := congrArg WritePermissionProvider.Inputs.address input
  simpa only [Component.rowInput, circuit_norm] using congrArg (fun value => (toElements value).toArray) address

/-- A matched provider proves the requested byte writable in the fixed image. -/
theorem pull_permitted_of_sources {Public : TypeMap} [ProvableType Public]
    {assembly : Ensemble (ZMod p) Public} (image : ProgramImage)
    (witness : EnsembleWitness assembly) (constraints : witness.Constraints)
    (balance : BalancedInteractions (witness.interactionsWith WritePermissionProvider.channel.toRaw))
    (verifier : ∀ (input : Public (ZMod p)) (data : ProverData (ZMod p)),
      ∀ interaction ∈ assembly.verifierOperations.interactionValuesWith
      WritePermissionProvider.channel.toRaw (Environment.fromInput input data),
      interaction.mult = 0 ∨ interaction.mult = -1)
    (sources : ∀ component ∈ assembly.tables,
      component = ({ circuit := WritePermissionProvider.circuit image } : Component (ZMod p)) ∨ Pulls component)
    (address : fields 3 (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : interaction.mult = -1) (payload : interaction.msg = (toElements address).toArray) :
    WritePermissionProvider.Permitted image address := by
  obtain ⟨provider, providerMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balance interaction member active
  rcases EnsembleWitness.mem_interactionsWith.mp providerMem with verifierMem | ⟨table, tableMem, providerMem⟩
  · exact ((verifier witness.publicInput witness.data provider verifierMem).elim nonzero notPull).elim
  · obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp providerMem
    have checked := constraints table tableMem physical physicalMem
    rcases sources table.component
      (EnsembleWitness.mem_component_of_mem tableMem) with fixed | pulls
    · rw [fixed] at emitted checked
      have permitted := provider_constraints image (Environment.fromArray physical witness.data) checked
      have same := (provider_payload image _ provider emitted).symm.trans (samePayload.trans payload)
      have addressEq := congrArg (fromElements (M := fields 3)) (Vector.toArray_inj.mp same)
      simp only [ProvableType.fromElements_toElements] at addressEq
      rw [addressEq] at permitted
      exact permitted
    · exact ((pulls witness.data physical checked provider emitted).elim nonzero notPull).elim

end SP1Clean.Soundness.WritePermission
