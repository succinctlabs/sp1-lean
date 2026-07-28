import SP1Clean.Model.Channels
import SP1Clean.Model.InteractionProjection
import Clean.Air.FlatEnsemble

/-! # Typed views of evaluated Clean interactions

Clean evaluates every channel interaction into the heterogeneous `Interaction` type.  This module
adds a proof-carrying typed view which retains that exact evaluated interaction while recovering the
message type from the channel.  It is deliberately an adapter over Clean's value, not a second bus
representation: erasing the wrapper gives `Operations.interactionValuesWith` definitionally up to
the list's membership proofs.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- Full nested constraint satisfaction distributes over operation concatenation. This is the
`Operations.ConstraintsHold` counterpart of Clean's flat-list `constraintsHold_append`. -/
theorem operationsConstraintsHold_append (env : Environment F)
    (left right : Operations F) :
    (left ++ right).ConstraintsHold env ↔
      left.ConstraintsHold env ∧ right.ConstraintsHold env := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.forall_mem_append]
  tauto

/-- Extract the field equality represented by one retained Clean equality subcircuit. -/
theorem equality_of_singleton_constraintsHold
    (env : Environment F) (left right : Expression F) (offset : ℕ) :
    Operations.ConstraintsHold env
        [.subcircuit (@FormalAssertion.toSubcircuit F _ (ProvablePair field field)
          ProvablePair.instance (Gadgets.Equality.circuit field) offset (left, right))] →
      env left = env right := by
  intro constraints
  have difference :
      env (toElements (M := field) left)[0] - env (toElements (M := field) right)[0] = 0 := by
    simpa [Operations.ConstraintsHold, FormalAssertion.toSubcircuit,
      Gadgets.Equality.main, Gadgets.allZero, Circuit.forEach.operations_eq,
      FlatOperation.constraints, FlatOperation.lookups, eval_sub, circuit_norm] using constraints
  have leftEq : env (toElements (M := field) left)[0] = env left := rfl
  have rightEq : env (toElements (M := field) right)[0] = env right := rfl
  rwa [leftEq, rightEq, sub_eq_zero] at difference

/-- An evaluated Clean interaction together with evidence that it belongs to `channel`. -/
structure TypedInteraction (channel : Channel F Message) where
  raw : Interaction F
  channel_eq : raw.channel = channel.toRaw

namespace TypedInteraction

/-- A typed wrapper for Clean's evaluated gated pull. -/
def pulledIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) :
    TypedInteraction channel where
  raw := channel.pulledIfValue enabled msg
  channel_eq := rfl

/-- A typed wrapper for Clean's evaluated gated push. -/
def pushedIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) :
    TypedInteraction channel where
  raw := channel.pushedIfValue enabled msg
  channel_eq := rfl

/-- The proof carried beside an interaction is irrelevant; the original Clean value determines the
typed wrapper. -/
theorem raw_injective {channel : Channel F Message} :
    Function.Injective (@raw F _ Message _ channel) := by
  rintro ⟨-, -⟩ ⟨-, -⟩ rfl
  rfl

@[simp] theorem pulledIfValue_raw (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pulledIfValue channel enabled msg).raw = channel.pulledIfValue enabled msg := rfl

@[simp] theorem pushedIfValue_raw (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pushedIfValue channel enabled msg).raw = channel.pushedIfValue enabled msg := rfl

/-- The original Clean multiplicity. -/
def mult {channel : Channel F Message} (interaction : TypedInteraction channel) : F :=
  interaction.raw.mult

/-- Recover the channel's typed message from the original evaluated array. -/
noncomputable def message {channel : Channel F Message}
    (interaction : TypedInteraction channel) : Message F :=
  fromElements ⟨interaction.raw.msg, by
    simpa only [interaction.channel_eq, Channel.toRaw_arity] using interaction.raw.same_size⟩

@[simp] theorem message_toElements {channel : Channel F Message}
    (interaction : TypedInteraction channel) :
    (toElements interaction.message).toArray = interaction.raw.msg := by
  unfold message
  rw [ProvableType.toElements_fromElements]

theorem message_eq_iff {channel : Channel F Message}
    (interaction : TypedInteraction channel) (msg : Message F) :
    interaction.message = msg ↔
      interaction.raw.msg = (toElements msg).toArray := by
  unfold message
  rw [ProvableType.fromElements_eq_iff]
  exact ⟨congrArg Vector.toArray, fun h => Vector.toArray_inj.mp h⟩

@[simp] theorem pulledIfValue_mult (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pulledIfValue channel enabled msg).mult = -enabled := rfl

@[simp] theorem pushedIfValue_mult (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pushedIfValue channel enabled msg).mult = enabled := rfl

@[simp] theorem pulledIfValue_message (channel : Channel F Message) (enabled : F)
    (msg : Message F) : (pulledIfValue channel enabled msg).message = msg := by
  rw [message_eq_iff]
  rfl

@[simp] theorem pushedIfValue_message (channel : Channel F Message) (enabled : F)
    (msg : Message F) : (pushedIfValue channel enabled msg).message = msg := by
  rw [message_eq_iff]
  rfl

/-- Attach the channel equality to an evaluated abstract interaction. -/
def eval (channel : Channel F Message) (env : Environment F) (interaction : AbstractInteraction F)
    (channel_eq : interaction.channel = channel.toRaw) : TypedInteraction channel where
  raw := interaction.eval env
  channel_eq := by simpa only [AbstractInteraction.eval_channel] using channel_eq

@[simp] theorem eval_raw (channel : Channel F Message) (env : Environment F)
    (interaction : AbstractInteraction F) (channel_eq : interaction.channel = channel.toRaw) :
    (eval channel env interaction channel_eq).raw = interaction.eval env := rfl

/-- Evaluating an exact syntactic channel pull produces its canonical typed value.  Factoring this
generically avoids re-normalizing large concrete message structures in every chip proof. -/
theorem eval_pulledIf (channel : Channel F Message) (env : Environment F)
    (enabled : Expression F) (msg : Message (Expression F)) :
    eval channel env (channel.pulledIf enabled msg).toRaw rfl =
      pulledIfValue channel (Expression.eval env enabled) (Eval.eval env msg) := by
  apply raw_injective
  change (channel.pulledIf enabled msg).toRaw.eval env =
    channel.pulledIfValue (Expression.eval env enabled) (Eval.eval env msg)
  simpa only [CircuitType.eval_expr] using
    (Channel.eval_pulledIf (channel := channel) (enabled := enabled) (msg := msg) (env := env))

/-- A nonzero positive interaction that satisfies Clean's raw requirement proves the typed channel
predicate for its recovered message. This is the push-side dual of consuming a channel guarantee. -/
theorem guarantee_of_requirements {p : ℕ} [Fact p.Prime]
    {Message : TypeMap} [ProvableType Message]
    {channel : Channel (ZMod p) Message} (interaction : TypedInteraction channel)
    (data : ProverData (ZMod p)) (hp : 2 < p)
    (requirements : interaction.raw.Requirements data)
    (positive : signedVal interaction.mult = 1) :
    channel.Guarantees interaction.message data := by
  obtain ⟨⟨rawChannel, mult, message, sameSize, assumes⟩, channelEq⟩ := interaction
  dsimp only at channelEq
  subst rawChannel
  change signedVal mult = 1 at positive
  have multOne : mult = 1 := by rw [← intCast_signedVal mult, positive]; norm_num
  change channel.toRaw.Requirements mult ⟨message, sameSize⟩ data at requirements
  simp only [Channel.toRaw] at requirements
  letI : Fact (ringChar (ZMod p) ≠ 2) := ⟨by rw [ZMod.ringChar_zmod_n]; omega⟩
  have multNeNeg : mult ≠ -1 := by rw [multOne]; exact one_ne_neg_one
  have guarantee := requirements multNeNeg (by simp [multOne])
  simpa only [TypedInteraction.message, Interaction.msgVector] using guarantee

end TypedInteraction

/-- The exact interactions emitted by `ops` on `channel`, with their message type recovered. -/
noncomputable def typedInteractionValuesWith (ops : Operations F)
    (channel : Channel F Message) (env : Environment F) : List (TypedInteraction channel) :=
  (ops.interactionsWith channel.toRaw).attach.map fun interaction =>
    TypedInteraction.eval channel env interaction.1
      (Operations.channel_eq_of_mem_interactionsWith interaction.2)

/-- Every syntactic interaction retained by `interactionsWith` has its canonical evaluated typed
wrapper in `typedInteractionValuesWith`.  This is the pointwise introduction rule for the adapter. -/
theorem mem_typedInteractionValuesWith (ops : Operations F)
    (channel : Channel F Message) (env : Environment F)
    {interaction : AbstractInteraction F}
    (member : interaction ∈ ops.interactionsWith channel.toRaw) :
    TypedInteraction.eval channel env interaction
        (Operations.channel_eq_of_mem_interactionsWith member) ∈
      typedInteractionValuesWith ops channel env := by
  unfold typedInteractionValuesWith
  exact List.mem_map.mpr ⟨⟨interaction, member⟩, by simp, rfl⟩

/-- A typed view of a channel with no syntactic interactions is empty. -/
theorem typedInteractionValuesWith_eq_nil_of_interactionsWith_eq_nil
    (ops : Operations F) (channel : Channel F Message) (env : Environment F)
    (empty : ops.interactionsWith channel.toRaw = []) :
    typedInteractionValuesWith ops channel env = [] := by
  simp [typedInteractionValuesWith, empty]

/-- The typed adapter neither invents nor drops evaluated interactions. -/
@[simp] theorem typedInteractionValuesWith_raw (ops : Operations F)
    (channel : Channel F Message) (env : Environment F) :
    (typedInteractionValuesWith ops channel env).map TypedInteraction.raw =
      ops.interactionValuesWith channel.toRaw env := by
  unfold typedInteractionValuesWith Operations.interactionValuesWith
  rw [List.map_map]
  change ((ops.interactionsWith channel.toRaw).attach.map
      (fun interaction => AbstractInteraction.eval env interaction.1)) = _
  exact List.attach_map_val

/-- Typed channel interactions emitted by every physical row of a Clean table. -/
noncomputable def typedTableInteractionsWith (table : Table F) (channel : Channel F Message) :
    List (TypedInteraction channel) :=
  table.table.flatMap fun row =>
    typedInteractionValuesWith table.component.operations channel (table.environment row)

/-- Erasing the typed table view recovers Clean's actual interaction list. -/
@[simp] theorem typedTableInteractionsWith_raw (table : Table F) (channel : Channel F Message) :
    (typedTableInteractionsWith table channel).map TypedInteraction.raw =
      table.interactionsWith channel.toRaw := by
  simp only [typedTableInteractionsWith, Table.interactionsWith, List.map_flatMap,
    typedInteractionValuesWith_raw]

/-- Typed interactions on one channel across the verifier and every witness table. -/
noncomputable def typedEnsembleInteractionsWith {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble)
    (channel : Channel F Message) : List (TypedInteraction channel) :=
  witness.allTables.flatMap (typedTableInteractionsWith · channel)

/-- Erasure agrees exactly with Clean's ensemble-level channel interaction list. -/
@[simp] theorem typedEnsembleInteractionsWith_raw {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble)
    (channel : Channel F Message) :
    (typedEnsembleInteractionsWith witness channel).map TypedInteraction.raw =
      witness.interactionsWith channel.toRaw := by
  simp only [typedEnsembleInteractionsWith, Air.Flat.EnsembleWitness.interactionsWith,
    List.map_flatMap, typedTableInteractionsWith_raw]

/-! ## Balance without an untyped lookup-key shadow -/

section TypedBalance

variable {p : ℕ} [Fact p.Prime]
variable {Message : TypeMap} [ProvableType Message]
variable {channel : Channel (ZMod p) Message}

/-- The centered value of the canonical pull multiplicity `-1`.  Every active-pull argument in this
module descends through it. -/
private lemma signedVal_neg_one (hp : 2 < p) : signedVal (-1 : ZMod p) = -1 := by
  rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (by omega)]
  norm_num

/-- The signed multiplicity at one typed message.  Equality is checked on the channel's canonical
element encoding, so this is exactly Clean's `balanceOf` with a typed key. -/
noncomputable def typedMultiplicitySum (interactions : List (TypedInteraction channel))
    (msg : Message (ZMod p)) : ℤ :=
  ((interactions.filter fun interaction =>
      interaction.raw.msg = (toElements msg).toArray).map fun interaction =>
        signedVal interaction.mult).sum

/-- Active positive contributions, retaining their typed messages. -/
noncomputable def producedMessages (interactions : List (TypedInteraction channel)) :
    List (Message (ZMod p)) :=
  (interactions.filter fun interaction => signedVal interaction.mult = 1).map
    TypedInteraction.message

/-- Active negative contributions, retaining their typed messages. -/
noncomputable def consumedMessages (interactions : List (TypedInteraction channel)) :
    List (Message (ZMod p)) :=
  (interactions.filter fun interaction => signedVal interaction.mult = -1).map
    TypedInteraction.message

/-- An exact typed interaction with active pull multiplicity contributes its recovered message to
`consumedMessages`. -/
theorem TypedInteraction.message_mem_consumedMessages
    (interaction : TypedInteraction channel) (interactions : List (TypedInteraction channel))
    (member : interaction ∈ interactions) (negative : signedVal interaction.mult = -1) :
    interaction.message ∈ consumedMessages interactions := by
  unfold consumedMessages
  refine List.mem_map.mpr ⟨interaction, List.mem_filter.mpr ⟨member, ?_⟩, rfl⟩
  simpa only [decide_eq_true_eq] using negative

/-- An active syntactic `pulledIf` retained by an operation list contributes its evaluated message
to that exact list's consumed typed messages.  This packages the proof-irrelevant typed wrapper and
the centered-multiplicity calculation once, leaving chip contracts to prove only structural list
membership and semantic field bindings. -/
theorem eval_pulledIf_message_mem_consumedMessages (ops : Operations (ZMod p))
    (channel : Channel (ZMod p) Message) (env : Environment (ZMod p))
    (enabled : Expression (ZMod p)) (msg : Message (Expression (ZMod p)))
    (member : (channel.pulledIf enabled msg).toRaw ∈
      ops.interactionsWith channel.toRaw)
    (hp : 2 < p) (active : Expression.eval env enabled = 1) :
    Eval.eval env msg ∈ consumedMessages (typedInteractionValuesWith ops channel env) := by
  let abstract := (channel.pulledIf enabled msg).toRaw
  let typed := TypedInteraction.eval channel env abstract
    (Operations.channel_eq_of_mem_interactionsWith member)
  have typedMem : typed ∈ typedInteractionValuesWith ops channel env :=
    mem_typedInteractionValuesWith ops channel env member
  have typedEq : typed = TypedInteraction.pulledIfValue channel
      (Expression.eval env enabled) (Eval.eval env msg) := by
    simpa only [typed, abstract] using TypedInteraction.eval_pulledIf channel env enabled msg
  have negative : signedVal typed.mult = -1 := by
    rw [typedEq, TypedInteraction.pulledIfValue_mult, active]
    exact signedVal_neg_one hp
  have messageMem :=
    TypedInteraction.message_mem_consumedMessages typed _ typedMem negative
  simpa only [typedEq, TypedInteraction.pulledIfValue_message] using messageMem

/-- A finished channel guarantee may be specialized to any exact active syntactic pull in the
operation list.  This is the pull-side counterpart of `guarantee_of_mem_producedTableMessages`:
chip contracts prove only interaction membership and the active gate, while this lemma performs
the generic descent through Clean's raw-channel representation. -/
theorem guarantee_of_eval_pulledIf_mem (ops : Operations (ZMod p))
    (channel : Channel (ZMod p) Message) (env : Environment (ZMod p))
    (enabled : Expression (ZMod p)) (msg : Message (Expression (ZMod p)))
    (member : (channel.pulledIf enabled msg).toRaw ∈
      ops.interactionsWith channel.toRaw)
    (guarantees : ops.ChannelGuarantees channel.toRaw env)
    (active : Expression.eval env enabled = 1) :
    channel.Guarantees (Eval.eval env msg) env.data := by
  rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff] at guarantees
  have pulled := guarantees _ member
  rw [ChannelInteraction.toRaw_guarantees] at pulled
  apply pulled
  · rfl
  · simp only [Channel.pulledIf, pulledIf_mult, eval_neg, active]

/-- Erase the dependent raw-channel representation after a typed wrapper has fixed its channel.
Pattern-matching the wrapper is important here: rewriting `raw.channel` directly gives Lean an
ill-typed dependent motive because the raw message vector is indexed by that channel's arity. -/
theorem TypedInteraction.guarantee_of_rawGuarantees
    (channel : Channel (ZMod p) Message) (interaction : TypedInteraction channel)
    (data : ProverData (ZMod p)) (rawGuarantees : interaction.raw.Guarantees data)
    (assumes : interaction.raw.assumeGuarantees)
    (negative : interaction.mult = -1) :
    channel.Guarantees interaction.message data := by
  obtain ⟨⟨rawChannel, mult, message, sameSize, assumeRaw⟩, channelEq⟩ := interaction
  dsimp only at channelEq
  subst rawChannel
  exact rawGuarantees assumes negative

/-- A typed evaluated interaction inherits its channel predicate from Clean's finished
`ChannelGuarantees` whenever it is an assumption-carrying active pull.  Unlike
`guarantee_of_eval_pulledIf_mem`, this form starts from the exact typed interaction list and is
therefore convenient after a chip's interaction-shape theorem has already hidden the syntax. -/
theorem TypedInteraction.guarantee_of_channelGuarantees
    (ops : Operations (ZMod p)) (channel : Channel (ZMod p) Message)
    (env : Environment (ZMod p)) (interaction : TypedInteraction channel)
    (member : interaction ∈ typedInteractionValuesWith ops channel env)
    (guarantees : ops.ChannelGuarantees channel.toRaw env)
    (assumes : interaction.raw.assumeGuarantees)
    (negative : interaction.mult = -1) :
    channel.Guarantees interaction.message env.data := by
  unfold typedInteractionValuesWith at member
  obtain ⟨⟨abstract, abstractMem⟩, -, rfl⟩ := List.mem_map.mp member
  rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff] at guarantees
  have evaluated : (abstract.eval env).Guarantees env.data :=
    AbstractInteraction.eval_guarantees.mpr (guarantees abstract abstractMem)
  exact TypedInteraction.guarantee_of_rawGuarantees channel _ env.data evaluated assumes negative

/-- Full parent constraints restrict to the flattened constraints of any retained subcircuit.
This is the constraint analogue of `channelGuarantees_subcircuit_of_mem`; it is useful when a
chip-owned routing assertion deliberately lives inside a semantic proof-boundary subcircuit. -/
theorem constraintsHoldFlat_subcircuit_of_mem (env : Environment (ZMod p))
    (ops : Operations (ZMod p)) {n : ℕ} (sub : Subcircuit (ZMod p) n)
    (subMem : ⟨n, sub⟩ ∈ ops.subcircuits) (constraints : ops.ConstraintsHold env) :
    FlatOperation.ConstraintsHoldFlat env sub.ops.toFlat := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  have allConstraints := Operations.forall_constraints_iff.mp constraints.1
  have allLookups := Operations.forall_lookups_iff.mp constraints.2
  exact ⟨allConstraints.2 _ subMem, allLookups.2 _ subMem⟩

/-- Parent constraints restrict to the `main` operation list of any retained
`GeneralFormalCircuit` boundary.  This is the folded constraint analogue of
`channelGuarantees_subcircuit_of_mem`; callers need not unfold the completed subcircuit record. -/
theorem constraintsHold_generalSubcircuit_of_mem {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p))
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ)
    (subMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  have nested := constraintsHoldFlat_subcircuit_of_mem env ops
    (circuit.toSubcircuit offset input) subMem constraints
  rwa [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nested

/-- Parent constraints restrict to the `main` operation list of any retained `FormalCircuit`
boundary. This is the witnessed-output companion to
`constraintsHold_generalSubcircuit_of_mem`. -/
theorem constraintsHold_formalSubcircuit_of_mem {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p))
    (circuit : FormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ)
    (subMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  have nested := constraintsHoldFlat_subcircuit_of_mem env ops
    (circuit.toSubcircuit offset input) subMem constraints
  rwa [FormalCircuit.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nested

/-- Parent constraints restrict to the `main` operation list of any retained
`FormalAssertion` boundary. This is the assertion-only companion to
`constraintsHold_generalSubcircuit_of_mem`. -/
theorem constraintsHold_assertionSubcircuit_of_mem {Input : TypeMap}
    [ProvableType Input]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p))
    (circuit : FormalAssertion (ZMod p) Input)
    (input : Var Input (ZMod p)) (offset : ℕ)
    (subMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  have nested := constraintsHoldFlat_subcircuit_of_mem env ops
    (circuit.toSubcircuit offset input) subMem constraints
  rwa [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nested

/-- Clean requirements on a physical table prove the typed predicate of each exact active push. -/
theorem guarantee_of_mem_producedTableMessages (table : Table (ZMod p))
    (channel : Channel (ZMod p) Message) (hp : 2 < p)
    (requirements : table.ChannelRequirements channel.toRaw) (msg : Message (ZMod p))
    (member : msg ∈ producedMessages (typedTableInteractionsWith table channel)) :
    channel.Guarantees msg table.data := by
  unfold producedMessages at member
  obtain ⟨interaction, interactionMem, messageEq⟩ := List.mem_map.mp member
  obtain ⟨typedMem, positive⟩ := List.mem_filter.mp interactionMem
  simp only [decide_eq_true_eq] at positive
  have rawMem : interaction.raw ∈ table.interactionsWith channel.toRaw := by
    rw [← typedTableInteractionsWith_raw]
    exact List.mem_map_of_mem typedMem
  have rawRequirements : interaction.raw.Requirements table.data :=
    (Table.channelRequirements_iff_forall table channel.toRaw).mp requirements
      interaction.raw rawMem
  rw [← messageEq]
  exact interaction.guarantee_of_requirements table.data hp rawRequirements positive

/-- If every active typed pull message satisfies the typed channel predicate, then the original
operation list has Clean's exact `ChannelGuarantees`.  This transports semantic grounding back to
the circuit theorem without replacing or reinterpreting its interaction list. -/
theorem channelGuarantees_of_consumedMessages (ops : Operations (ZMod p))
    (channel : Channel (ZMod p) Message) (env : Environment (ZMod p))
    (hp : 2 < p)
    (guarantees : ∀ msg ∈ consumedMessages (typedInteractionValuesWith ops channel env),
      channel.Guarantees msg env.data) :
    ops.ChannelGuarantees channel.toRaw env := by
  rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff]
  intro interaction interactionMem
  have channelEq := Operations.channel_eq_of_mem_interactionsWith interactionMem
  obtain ⟨rawChannel, mult, message, assumes⟩ := interaction
  dsimp only at channelEq
  subst rawChannel
  simp only [AbstractInteraction.Guarantees, Channel.toRaw]
  intro _ pullMult
  let interaction : AbstractInteraction (ZMod p) :=
    ⟨channel.toRaw, mult, message, assumes⟩
  have currentMem : interaction ∈ ops.interactionsWith channel.toRaw := by
    simpa only [interaction] using interactionMem
  let typed := TypedInteraction.eval channel env interaction
    (Operations.channel_eq_of_mem_interactionsWith currentMem)
  have typedMem : typed ∈ typedInteractionValuesWith ops channel env :=
    mem_typedInteractionValuesWith ops channel env currentMem
  have pullSigned : signedVal typed.mult = -1 := by
    change signedVal (Expression.eval env interaction.mult) = -1
    rw [pullMult]
    exact signedVal_neg_one hp
  have messageMem :=
    TypedInteraction.message_mem_consumedMessages typed _ typedMem pullSigned
  have grounded := guarantees typed.message messageMem
  have messageEq : typed.message =
      fromElements (message.map (Expression.eval env)) := by
    apply (TypedInteraction.message_eq_iff typed _).2
    simp only [typed, interaction, TypedInteraction.eval_raw, AbstractInteraction.eval,
      ProvableType.toElements_fromElements]
    rfl
  rwa [messageEq] at grounded

@[simp] theorem producedMessages_append (left right : List (TypedInteraction channel)) :
    producedMessages (left ++ right) = producedMessages left ++ producedMessages right := by
  simp [producedMessages, List.filter_append]

@[simp] theorem consumedMessages_append (left right : List (TypedInteraction channel)) :
    consumedMessages (left ++ right) = consumedMessages left ++ consumedMessages right := by
  simp [consumedMessages, List.filter_append]

/-- A list of integers in `{-1, 0, 1}` has sum bounded by its length. -/
private theorem abs_sum_le_length (values : List ℤ)
    (binary : ∀ value ∈ values, value = -1 ∨ value = 0 ∨ value = 1) :
    |values.sum| ≤ values.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have valueBound : |value| ≤ 1 := by
        rcases binary value (by simp) with h | h | h <;> simp [h]
      have tailBound := ih (fun x hx => binary x (List.mem_cons_of_mem value hx))
      have sumBound : |value + values.sum| ≤ |value| + |values.sum| :=
        abs_add_le value values.sum
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- Casting a signed list sum back into `ZMod p` distributes over the list. -/
private theorem intCast_list_sum (values : List ℤ) :
    ((values.sum : ℤ) : ZMod p) = (values.map fun value : ℤ => (value : ZMod p)).sum := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih]

/-- Clean field balance implies exact integer balance at every typed message when multiplicities are
binary.  The proof uses Clean's interaction-count bound to exclude modular wraparound. -/
theorem typedMultiplicitySum_eq_zero_of_balanced
    (interactions : List (TypedInteraction channel))
    (balanced : BalancedInteractions (interactions.map TypedInteraction.raw))
    (binary : ∀ interaction ∈ interactions,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1) :
    ∀ msg, typedMultiplicitySum interactions msg = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have lengthLt : interactions.length < p := by
    rcases balanced.1 with lengthLt | characteristicZero
    · simpa only [List.length_map, ZMod.ringChar_zmod_n] using lengthLt
    · rw [ZMod.ringChar_zmod_n] at characteristicZero
      exact absurd characteristicZero (Fact.out (p := p.Prime)).ne_zero
  intro msg
  have castZero : ((typedMultiplicitySum interactions msg : ℤ) : ZMod p) = 0 := by
    calc
      ((typedMultiplicitySum interactions msg : ℤ) : ZMod p) =
          ((interactions.filter fun interaction =>
            interaction.raw.msg = (toElements msg).toArray).map
              fun interaction => interaction.mult).sum := by
        unfold typedMultiplicitySum
        rw [intCast_list_sum, List.map_map]
        exact congrArg List.sum (List.map_congr_left fun interaction _ =>
          intCast_signedVal interaction.mult)
      _ = balanceOf (interactions.map TypedInteraction.raw) (toElements msg).toArray := by
        unfold balanceOf
        rw [List.filter_map, List.map_map]
        rfl
      _ = 0 := balanced.2 _
  have divides : (p : ℤ) ∣ typedMultiplicitySum interactions msg :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp castZero
  have sumBound : |typedMultiplicitySum interactions msg| ≤
      (interactions.filter fun interaction =>
        interaction.raw.msg = (toElements msg).toArray).length := by
    unfold typedMultiplicitySum
    have bound := abs_sum_le_length
      ((interactions.filter fun interaction =>
        interaction.raw.msg = (toElements msg).toArray).map fun interaction =>
          signedVal interaction.mult) (by
        intro value valueMem
        obtain ⟨interaction, interactionMem, rfl⟩ := List.mem_map.mp valueMem
        exact binary interaction (List.mem_of_mem_filter interactionMem))
    simpa only [List.length_map] using bound
  have filteredLength :
      (interactions.filter fun interaction =>
        interaction.raw.msg = (toElements msg).toArray).length ≤ interactions.length :=
    List.length_filter_le _ _
  exact Int.eq_zero_of_abs_lt_dvd divides (by omega)

@[simp] private theorem typedMultiplicitySum_cons
    (interaction : TypedInteraction channel) (interactions : List (TypedInteraction channel))
    (msg : Message (ZMod p)) :
    typedMultiplicitySum (interaction :: interactions) msg =
      (if interaction.raw.msg = (toElements msg).toArray then signedVal interaction.mult else 0) +
        typedMultiplicitySum interactions msg := by
  by_cases same : interaction.raw.msg = (toElements msg).toArray <;>
    simp [typedMultiplicitySum, same]

/-- If a balanced channel is split into pull-only consumers and arbitrary providers, every active
consumer pull has a matching nonzero provider interaction.  Provider multiplicities need not be
binary: Clean's own balance theorem finds a matching non-pull, and the consumer shape forces that
interaction into the provider suffix. -/
theorem provider_matches_active_pull
    (consumers providers : List (TypedInteraction channel))
    (balanced : BalancedInteractions ((consumers ++ providers).map TypedInteraction.raw))
    (consumerShape : ∀ interaction ∈ consumers,
      interaction.mult = 0 ∨ interaction.mult = -1)
    (target : TypedInteraction channel) (targetMem : target ∈ consumers)
    (targetPull : target.mult = -1) :
    ∃ provider ∈ providers,
      provider.message = target.message ∧ provider.mult ≠ 0 := by
  have targetRawMem : target.raw ∈
      (consumers ++ providers).map TypedInteraction.raw :=
    List.mem_map.mpr ⟨target, List.mem_append_left providers targetMem, rfl⟩
  have targetRawPull : target.raw.mult = -1 := by
    simpa only [TypedInteraction.mult] using targetPull
  obtain ⟨rawProvider, rawProviderMem, sameMessage, providerNeZero, providerNePull⟩ :=
    exists_push_of_pull _ balanced target.raw targetRawMem targetRawPull
  rw [List.map_append] at rawProviderMem
  rcases List.mem_append.mp rawProviderMem with consumerMem | providerMem
  · obtain ⟨consumer, consumerMem, consumerRaw⟩ := List.mem_map.mp consumerMem
    have providerMult : rawProvider.mult = consumer.mult := by
      simpa only [TypedInteraction.mult] using congrArg Interaction.mult consumerRaw.symm
    rcases consumerShape consumer consumerMem with zero | pull
    · exact (providerNeZero (providerMult.trans zero)).elim
    · exact (providerNePull (providerMult.trans pull)).elim
  · obtain ⟨provider, providerMem, providerRaw⟩ := List.mem_map.mp providerMem
    refine ⟨provider, providerMem, ?_, ?_⟩
    · rw [TypedInteraction.message_eq_iff]
      exact (congrArg Interaction.msg providerRaw).trans
        (sameMessage.trans (TypedInteraction.message_toElements target).symm)
    · exact fun providerZero =>
        providerNeZero ((congrArg Interaction.mult providerRaw).symm.trans providerZero)

@[simp] private theorem producedMessages_cons
    (interaction : TypedInteraction channel) (interactions : List (TypedInteraction channel)) :
    producedMessages (interaction :: interactions) =
      if signedVal interaction.mult = 1 then
        interaction.message :: producedMessages interactions
      else producedMessages interactions := by
  by_cases positive : signedVal interaction.mult = 1 <;>
    simp [producedMessages, positive]

@[simp] private theorem consumedMessages_cons
    (interaction : TypedInteraction channel) (interactions : List (TypedInteraction channel)) :
    consumedMessages (interaction :: interactions) =
      if signedVal interaction.mult = -1 then
        interaction.message :: consumedMessages interactions
      else consumedMessages interactions := by
  by_cases negative : signedVal interaction.mult = -1 <;>
    simp [consumedMessages, negative]

private theorem typedMultiplicitySum_eq_counts [DecidableEq (Message (ZMod p))]
    (interactions : List (TypedInteraction channel))
    (binary : ∀ interaction ∈ interactions,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1) (msg : Message (ZMod p)) :
    typedMultiplicitySum interactions msg =
      (producedMessages interactions).count msg - (consumedMessages interactions).count msg := by
  induction interactions with
  | nil => simp [typedMultiplicitySum, producedMessages, consumedMessages]
  | cons interaction interactions ih =>
      have headBinary := binary interaction (by simp)
      have tailBinary : ∀ i ∈ interactions,
          signedVal i.mult = -1 ∨ signedVal i.mult = 0 ∨ signedVal i.mult = 1 :=
        fun i hi => binary i (List.mem_cons_of_mem interaction hi)
      have ih' := ih tailBinary
      by_cases same : interaction.raw.msg = (toElements msg).toArray
      · have messageEq : interaction.message = msg :=
          (TypedInteraction.message_eq_iff interaction msg).2 same
        rw [typedMultiplicitySum_cons, producedMessages_cons, consumedMessages_cons]
        rcases headBinary with head | head | head <;> simp [same, messageEq, head, ih'] <;> omega
      · have messageNe : interaction.message ≠ msg := fun equal =>
          same ((TypedInteraction.message_eq_iff interaction msg).1 equal)
        rw [typedMultiplicitySum_cons, producedMessages_cons, consumedMessages_cons]
        rcases headBinary with head | head | head <;> simp [same, messageNe, head, ih']

/-- For a balanced typed channel with binary multiplicities, active pushes are a permutation of
active pulls as typed messages.  This is the production balance interface used by State, Program,
and Memory grounding. -/
theorem producedMessages_perm_consumedMessages [DecidableEq (Message (ZMod p))]
    (interactions : List (TypedInteraction channel))
    (balanced : BalancedInteractions (interactions.map TypedInteraction.raw))
    (binary : ∀ interaction ∈ interactions,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1) :
    (producedMessages interactions).Perm (consumedMessages interactions) := by
  rw [List.perm_iff_count]
  intro msg
  have zero := typedMultiplicitySum_eq_zero_of_balanced interactions balanced binary msg
  rw [typedMultiplicitySum_eq_counts interactions binary msg] at zero
  omega

end TypedBalance

end SP1Clean.Soundness
