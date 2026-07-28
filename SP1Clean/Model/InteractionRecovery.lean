import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit

/-! # Recovering a subcircuit's interactions on a channel it does not declare

For the Memory/Program "emitted = projection" theorems (`docs/bus-model.md` §6): a composed reader
like `Readers/RTypeReader.lean` emits its Memory/Program interactions *directly* in `main`, but also
composes byte-only `RegisterAccessCols` subcircuits. To recover `interactionsWith memoryChannel`
over `main`, those subcircuits must provably contribute **nothing** to the Memory bus.

Clean's `interactionsWith_subcircuit` reduces a subcircuit to the *filtered flattened* interactions,
and `Subcircuit.ChannelsLawful` (available via every `ElaboratedCircuit`'s
`subcircuitChannelsLawful`) records that a subcircuit's flat channels are ⊆ its declared
`channelsWith{Guarantees,Requirements}`. So a channel outside both declared lists matches no flat
interaction — the filter is empty and the subcircuit drops out.
`interactionsWith_formalSubcircuit_eq_nil` packages exactly that, per `FormalCircuit`. -/

namespace SP1Clean.InteractionRecovery

open Circuit Operations

variable {F : Type} [FiniteField F]

/-- A lawful subcircuit emits nothing on a channel absent from both sides of its declared
interface. -/
lemma interactionsWith_subcircuit_eq_nil_of_channelsLawful {n : ℕ}
    (subcircuit : Subcircuit F n) (channel : RawChannel F) (ops : Operations F)
    (h_g : channel ∉ subcircuit.channelsWithGuarantees)
    (h_r : channel ∉ subcircuit.channelsWithRequirements)
    (h_lawful : subcircuit.ChannelsLawful) :
    interactionsWith channel (.subcircuit subcircuit :: ops) = interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, List.filter_eq_nil_iff.mpr ?_, List.nil_append]
  intro i hi hci
  have hci' : i.channel = channel := by simpa using hci
  have hmem : channel ∈ FlatOperation.channels subcircuit.ops.toFlat := by
    rw [FlatOperation.channels, ← hci']; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact (List.mem_append.mp (h_lawful.2.2 hmem)).elim h_g h_r

/-- **A formal subcircuit emits nothing on a channel it does not declare.** If `channel` is in
neither `circuit.channelsWithGuarantees` nor `circuit.channelsWithRequirements`, then the subcircuit
it produces contributes no interaction on `channel`, so it drops out of
`interactionsWith channel`. -/
lemma interactionsWith_formalSubcircuit_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  refine interactionsWith_subcircuit_eq_nil_of_channelsLawful _ _ _ ?_ ?_
    (FormalCircuit.toSubcircuit_channelsLawful (circuit := circuit) (n := n) (input_var := input))
  · simpa only [FormalCircuit.toSubcircuit_channelsWithGuarantees]
  · simpa only [FormalCircuit.toSubcircuit_channelsWithRequirements]

/-- General-formal-circuit companion to `interactionsWith_formalSubcircuit_eq_nil`. -/
lemma interactionsWith_generalSubcircuit_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  refine interactionsWith_subcircuit_eq_nil_of_channelsLawful _ _ _ ?_ ?_
    (GeneralFormalCircuit.toSubcircuit_channelsLawful
      (circuit := circuit) (n := n) (input_var := input))
  · simpa only [GeneralFormalCircuit.toSubcircuit_channelsWithGuarantees]
  · simpa only [GeneralFormalCircuit.toSubcircuit_channelsWithRequirements]

/-- Formal-assertion companion to `interactionsWith_formalSubcircuit_eq_nil`. -/
lemma interactionsWith_assertionSubcircuit_eq_nil {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  refine interactionsWith_subcircuit_eq_nil_of_channelsLawful _ _ _ ?_ ?_
    (FormalAssertion.toSubcircuit_channelsLawful
      (circuit := circuit) (n := n) (input_var := input))
  · simpa only [FormalAssertion.toSubcircuit_channelsWithGuarantees]
  · simpa only [FormalAssertion.toSubcircuit_channelsWithRequirements]

/-- Reuse a child general circuit's exposed interaction when it is composed as a subcircuit. -/
lemma interactionsWith_generalSubcircuit_eq_of_mem_exposed
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (exposed : ExposedChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_exposed : exposed ∈ circuit.exposedChannels input n) :
    interactionsWith exposed.channel (.subcircuit (circuit.toSubcircuit n input) :: ops) =
      exposed.interactions ++ interactionsWith exposed.channel ops := by
  rw [interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change interactionsWith exposed.channel ((circuit.main input).operations n) ++
    interactionsWith exposed.channel ops = _
  rw [circuit.interactionsWith_eq_of_mem_exposedChannels input n exposed h_exposed]

/-- Singleton-exposure form of `interactionsWith_generalSubcircuit_eq_of_mem_exposed`. -/
lemma interactionsWith_generalSubcircuit_eq_of_singleton_exposure
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (exposed : ExposedChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_exposed : circuit.exposedChannels input n = [exposed]) :
    interactionsWith exposed.channel (.subcircuit (circuit.toSubcircuit n input) :: ops) =
      exposed.interactions ++ interactionsWith exposed.channel ops := by
  refine interactionsWith_generalSubcircuit_eq_of_mem_exposed circuit exposed input ops ?_
  rw [h_exposed]; exact List.mem_singleton_self exposed

/-- Turn an exact single-interaction projection of a child circuit's `main` into the compositional
subcircuit form used by composing chips.  This is the channel-generic home of the former
`Soundness/TypedProgram.lean` helper `programInteractions_subcircuit_of_main`; the per-reader
Program-fetch lemmas next to each reader's `circuit` instantiate it at `programChannel`. -/
lemma interactionsWith_generalSubcircuit_of_main_exact {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ) (ops : Operations F)
    (interaction : AbstractInteraction F)
    (main_exact : ((circuit.main input).operations offset).interactionsWith channel =
      [interaction]) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interaction :: interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change interactionsWith channel ((circuit.main input).operations offset) ++
      interactionsWith channel ops = _
  rw [main_exact, List.singleton_append]

/-- List form of `interactionsWith_generalSubcircuit_of_main_exact`, for a child that emits
**several** interactions on the channel (the per-reader Memory lists: read-prior pulls + read-back
pushes). -/
lemma interactionsWith_generalSubcircuit_of_main_exact_list {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ) (ops : Operations F)
    (interactions : List (AbstractInteraction F))
    (main_exact : ((circuit.main input).operations offset).interactionsWith channel =
      interactions) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interactions ++ interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change interactionsWith channel ((circuit.main input).operations offset) ++
      interactionsWith channel ops = _
  rw [main_exact]

/-- Formal-assertion companion of `interactionsWith_generalSubcircuit_of_main_exact_list`
(e.g. the `RegisterWrite` op_a write push, composed as a Clean `assertion`). -/
lemma interactionsWith_assertionSubcircuit_of_main_exact {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ) (ops : Operations F)
    (interactions : List (AbstractInteraction F))
    (main_exact : ((circuit.main input).operations offset).interactionsWith channel =
      interactions) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interactions ++ interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions]
  change interactionsWith channel ((circuit.main input).operations offset) ++
      interactionsWith channel ops = _
  rw [main_exact]

/-- **`.main`-form companion** (matches what `circuit_norm` leaves after reducing a formal
subcircuit): a circuit's `main` emits nothing on a channel outside its declared `channels`
(= guarantees ++ requirements). Derived from `ElaboratedCircuit.channels_subset`. This drops the
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
`FlatOperation.interactions … |>.filter` (the shape `circuit_norm` leaves for an assertion
subcircuit, which has no `.main` interaction reduction) is empty. Equality declares no channels, so
any `channel` qualifies. -/
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
  have hmem : channel ∈ FlatOperation.channels (circuit.toSubcircuit n input).ops.toFlat := by
    rw [FlatOperation.channels, ← hci']; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact (List.mem_append.mp (hsub hmem)).elim h_g h_r

/-- `.2`-projection form of `interactionsWith_main_eq_nil` — `circuit_norm` unfolds
`Circuit.operations` to `(circuit.main input offset).2`, so this is the shape that actually appears
after reducing `RTypeReader.main`; defeq to the `.operations` form. It discharges the byte-only
subcircuits' Memory/Program contributions, leaving `channel ∉ circuit.channels` as a side goal
that the channel-distinctness lemmas close. Applied explicitly (not as `circuit_norm`) since that
hypothesis isn't auto-dischargeable inline. -/
lemma interactionsWith_main_snd_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ)
    (h : channel ∉ circuit.channels) :
    interactionsWith channel (circuit.main input offset).2 = [] :=
  interactionsWith_main_eq_nil circuit channel input offset h

end SP1Clean.InteractionRecovery
