import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit

/-! # Recovering a subcircuit's interactions on a channel it does not declare

For the Memory/Program "emitted = projection" theorems (`docs/bus-model.md` §6): a composed reader like
`Readers/RTypeReader.lean` emits its Memory/Program interactions *directly* in `main`, but also composes
byte-only `RegisterAccessCols` subcircuits. To recover `interactionsWith memoryChannel` over `main`,
those subcircuits must provably contribute **nothing** to the Memory bus.

Clean's `interactionsWith_subcircuit` reduces a subcircuit to the *filtered flattened* interactions, and
`Subcircuit.ChannelsLawful` (available via every `ElaboratedCircuit`'s `subcircuitChannelsLawful`) records
that a subcircuit's flat channels are ⊆ its declared `channelsWith{Guarantees,Requirements}`. So a channel
outside both declared lists matches no flat interaction — the filter is empty and the subcircuit drops out.
`interactionsWith_formalSubcircuit_eq_nil` packages exactly that, per `FormalCircuit`. -/

namespace SP1Clean.InteractionRecovery

open Circuit Operations

variable {F : Type} [Field F]

/-- **A formal subcircuit emits nothing on a channel it does not declare.** If `channel` is in neither
`circuit.channelsWithGuarantees` nor `circuit.channelsWithRequirements`, then the subcircuit it produces
contributes no interaction on `channel`, so it drops out of `interactionsWith channel`. -/
lemma interactionsWith_formalSubcircuit_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  have hsub := (FormalCircuit.toSubcircuit_channelsLawful (circuit := circuit) (n := n)
    (input_var := input)).2.2
  rw [FormalCircuit.toSubcircuit_channelsWithGuarantees,
    FormalCircuit.toSubcircuit_channelsWithRequirements] at hsub
  rw [interactionsWith_subcircuit, List.filter_eq_nil_iff.mpr ?_, List.nil_append]
  intro i hi hci
  have hci' : i.channel = channel := by simpa using hci
  have hmem : i.channel ∈ FlatOperation.channels (circuit.toSubcircuit n input).ops.toFlat := by
    rw [FlatOperation.channels]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  have hcontra := hsub hmem
  rw [hci'] at hcontra
  exact (List.mem_append.mp hcontra).elim h_g h_r

/-- **`.main`-form companion** (matches what `circuit_norm` leaves after reducing a formal subcircuit):
a circuit's `main` emits nothing on a channel outside its declared `channels` (= guarantees ++
requirements). Derived from `ElaboratedCircuit.channels_subset`. This is the lemma that drops the
byte-only `RegisterAccessCols` (and the channel-free `op_a_0` Equality gate) from
`interactionsWith memoryChannel`/`programChannel` over `RTypeReader.main`. -/
lemma interactionsWith_main_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ)
    (h : channel ∉ circuit.channels) :
    interactionsWith channel ((circuit.main input).operations offset) = [] := by
  rw [interactionsWith]
  apply List.filter_eq_nil_iff.mpr
  intro i hi hci
  have hci' : i.channel = channel := by simpa using hci
  have hmem : channel ∈ ((circuit.main input).operations offset).channels := by
    rw [Operations.channels, ← hci']; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact h (circuit.channels_subset input offset hmem)

open Classical in
/-- A **formal-assertion** subcircuit (e.g. an `op_a_0 * wv === 0` gate, desugared to
`Gadgets.Equality.circuit`) emits nothing on a channel it doesn't declare — so its raw
`FlatOperation.interactions … |>.filter` (the shape `circuit_norm` leaves for an assertion subcircuit,
which has no `.main` interaction reduction) is empty. Equality declares no channels, so any `channel`
qualifies. -/
lemma filter_interactions_formalAssertion_eq_nil {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (channel : RawChannel F) {n : ℕ} (input : Var Input F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    (FlatOperation.interactions (circuit.toSubcircuit n input).ops.toFlat).filter
      (fun i => i.channel = channel) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i hi hci
  have hci' : i.channel = channel := by simpa using hci
  have hsub := (FormalAssertion.toSubcircuit_channelsLawful (circuit := circuit) (n := n)
    (input_var := input)).2.2
  rw [FormalAssertion.toSubcircuit_channelsWithGuarantees,
    FormalAssertion.toSubcircuit_channelsWithRequirements] at hsub
  have hmem : i.channel ∈ FlatOperation.channels (circuit.toSubcircuit n input).ops.toFlat := by
    rw [FlatOperation.channels]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  have hcontra := hsub hmem
  rw [hci'] at hcontra
  exact (List.mem_append.mp hcontra).elim h_g h_r

/-- `.2`-projection form of `interactionsWith_main_eq_nil` — `circuit_norm` unfolds `Circuit.operations`
to `(circuit.main input offset).2`, so this is the shape that actually appears after reducing
`RTypeReader.main`; defeq to the `.operations` form. Tagged `@[circuit_norm]` so the reduction discharges
the byte-only subcircuits' Memory/Program contributions automatically (with `channel ∉ circuit.channels`
left as a side goal that the channel-distinctness lemmas close). Applied explicitly (not as
`circuit_norm`) since its `channel ∉ circuit.channels` hypothesis isn't auto-dischargeable inline. -/
lemma interactionsWith_main_snd_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ)
    (h : channel ∉ circuit.channels) :
    interactionsWith channel (circuit.main input offset).2 = [] :=
  interactionsWith_main_eq_nil circuit channel input offset h

end SP1Clean.InteractionRecovery
