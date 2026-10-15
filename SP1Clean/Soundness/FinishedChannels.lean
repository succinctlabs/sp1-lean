import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.ChannelClosure

/-! # Finished structural channels from actual ensemble balance

Byte and Program requirements follow from each component's raw constraints. Clean channel
consistency therefore closes every table's pull guarantees, independently of table positions.
These are structural lookup facts; committed-ROM membership remains a stronger global theorem.
-/

namespace SP1Clean.Soundness

open SP1Clean
open Air.Flat
open Circuit
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel
  syscallChannel publicValuesChannel)

-- Same bound as `sp1Ensemble` (`Mul`/`DivRem` carry `Fact (2 ^ 24 < p)`), with the project-standard
-- `Fact (2 ^ 17 < p)` derived locally. KoalaBear satisfies it.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## Channel and channel-list facts -/

/-- The exact requirement-channel shape of the 25 instruction chips.  Most require State and Memory;
ShiftLeft, ShiftRight, and Branch carry State on their guarantee side and require only Memory. -/
private lemma sp1Tables_cwr_eq :
    (sp1Tables (p := p)).map (·.circuit.channelsWithRequirements) =
      List.replicate 7 [stateChannel.toRaw, memoryChannel.toRaw] ++
      [[memoryChannel.toRaw], [memoryChannel.toRaw],
       [stateChannel.toRaw, memoryChannel.toRaw],
       [stateChannel.toRaw, memoryChannel.toRaw], [memoryChannel.toRaw]] ++
      List.replicate 13 [stateChannel.toRaw, memoryChannel.toRaw] := rfl

lemma sp1Tables_cwr_subset : ∀ c ∈ sp1Tables (p := p),
    c.circuit.channelsWithRequirements ⊆ [stateChannel.toRaw, memoryChannel.toRaw] := by
  intro c hc channel hchannel
  have h := List.mem_map_of_mem
    (f := fun c : Component (ZMod p) => c.circuit.channelsWithRequirements) hc
  rw [sp1Tables_cwr_eq] at h
  simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
    or_false] at h
  norm_num at h
  have hshape :
      c.circuit.channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] ∨
      c.circuit.channelsWithRequirements = [memoryChannel.toRaw] := by
    tauto
  rcases hshape with hshape | hshape <;> rw [hshape] at hchannel <;> simp_all

/-- The 30 provider tables' (guarantee, requirement) channel pairs: the 23 byte
providers push-prove byte, the program provider push-proves program, the memory boundary provider
push-proves memory, the finalize table pulls memory owing nothing, — W3 — the MemoryBump table
pulls byte/memory and owes its refreshed memory push, the StateBump table pulls byte/state
owing nothing (the State bus has no requirements), the Halt table pulls all four gated buses
and owes only its memory read-backs (the Exit pushes carry `Guarantees := True`), and the
`SyscallInstrs` table touches all seven buses — it is the only table that names the syscall and
public-values channels — owing, like Halt, only its memory read-backs. -/
private lemma providers_channels_eq :
    (sp1ProviderTables (p := p)).map
      (fun c => (c.circuit.channelsWithGuarantees, c.circuit.channelsWithRequirements)) =
    List.replicate 23 ([], [byteChannel.toRaw]) ++
      [([], [programChannel.toRaw]), ([], [memoryChannel.toRaw]),
       ([memoryChannel.toRaw], []),
       ([byteChannel.toRaw, memoryChannel.toRaw], [memoryChannel.toRaw]),
       ([byteChannel.toRaw, stateChannel.toRaw], []),
       ([byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
         exitChannel.toRaw], [memoryChannel.toRaw]),
       ([byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
         exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw],
        [memoryChannel.toRaw])] := rfl

/-- Every provider circuit's `Assumptions` is the structure default `fun _ _ => True`. -/
private lemma providers_assumptions :
    ∀ c ∈ sp1ProviderTables (p := p), ∀ env : Environment (ZMod p), c.CircuitAssumptions env := by
  intro c hc env
  rw [sp1ProviderTables_explicit] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · fin_cases hc <;> trivial
  · obtain ⟨width, _, rfl⟩ := List.mem_map.mp hc
    trivial
  · fin_cases hc <;> trivial

/-- Every component proves Byte/Program requirements from its constraints. Only the closed
lookup providers list these requirement channels; every other component omits them. -/
theorem sp1_component_finished_requirements (component : Component (ZMod p))
    (member : component ∈ (sp1Ensemble (p := p)).tables)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  simp only [sp1Ensemble_tables, List.mem_append] at member
  rcases member with member | member
  · exact absent (fun required => outside (sp1Tables_cwr_subset _ member required))
  · have shape := List.mem_map_of_mem
      (f := fun c : Component (ZMod p) =>
        (c.circuit.channelsWithGuarantees, c.circuit.channelsWithRequirements)) member
    rw [providers_channels_eq] at shape
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at shape
    have cases : component.circuit.channelsWithGuarantees = [] ∨
        component.circuit.channelsWithRequirements = [] ∨
        component.circuit.channelsWithRequirements = [memoryChannel.toRaw] := by tauto
    rcases cases with noGuarantees | noRequirements | memoryOnly
    · have requirements := (component.weakSoundness_of_no_guarantees noGuarantees
        (providers_assumptions _ member env) constraints).2
      exact fun interaction emitted _ => requirements interaction emitted
    · exact absent (by simp [noRequirements])
    · exact absent (by
        rw [memoryOnly]
        intro required
        exact outside (List.mem_cons_of_mem _ required))

/-- Byte and Program structural guarantees are grounded by their provider circuits and actual
channel balance, for both the separate public verifier and every physical table. -/
theorem sp1_finishedChannel_guarantees (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hC : witness.Constraints) (hB : witness.BalancedChannels) :
    ((sp1Ensemble (p := p)).VerifierChannelGuarantees witness.publicInput witness.data byteChannel.toRaw ∧
      (sp1Ensemble (p := p)).VerifierChannelGuarantees witness.publicInput witness.data programChannel.toRaw) ∧
    ∀ table ∈ witness.tables,
      table.ChannelGuarantees witness.data byteChannel.toRaw ∧
      table.ChannelGuarantees witness.data programChannel.toRaw := by
  have closed (channel : RawChannel (ZMod p)) [channel.Consistent]
      (member : channel ∈ (sp1Ensemble (p := p)).channels)
      (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw]) :
      (sp1Ensemble (p := p)).VerifierChannelGuarantees witness.publicInput witness.data channel ∧
        ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel := by
    apply witness.channelGuarantees_of_component_requirements channel hC (hB channel member) ?_
      (fun component componentMem env constraints =>
        sp1_component_finished_requirements component componentMem channel outside env constraints)
    intro input data
    apply Ensemble.verifierChannelRequirements_of_not_mem
    intro used
    apply outside
    apply List.mem_cons.mpr
    left
    simpa [sp1Ensemble, sp1StateVerifierProgram, Verifier.ofInteractions,
      sp1StateVerifierMain, circuit_norm] using used
  have byte := closed byteChannel.toRaw (by simp [sp1Ensemble_channels]) (by simp [circuit_norm])
  have program := closed programChannel.toRaw (by simp [sp1Ensemble_channels]) (by simp [circuit_norm])
  exact ⟨⟨byte.1, program.1⟩, fun table member => ⟨byte.2 table member, program.2 table member⟩⟩

end SP1Clean.Soundness
