import Clean.Circuit.Basic
import Clean.Circuit.Channel

/-! # `VmChannel` — a typed channel with decoupled `Guarantees`/`Owed`

Clean's typed `Channel` couples the two roles of its predicate in `Channel.toRaw`: what a **pull
receives** (`toRaw.Guarantees`) and what a **push must prove row-locally** (`toRaw.Requirements`) are
both `channel.Guarantees`. That coupling is right for lookup-style channels (a byte provider *can*
locally prove its pushed row valid) but impossible for semantic VM channels: a memory read-back push
cannot locally prove "no intervening write", and a state push cannot locally prove reachability — those
are global balance facts (see `Soundness/TimedChannel.lean`, the timestamped grounding engine).

`VmChannel` splits the roles at the typed layer, building directly on Clean's **own primitive**
(`RawChannel` already carries independent `Guarantees`/`Requirements` fields — only the `Channel.toRaw`
sugar couples them):

- `Guarantees` — the semantic payload a pull receives (grounded by the engine, not by pushers);
- `Owed` — what a push proves row-locally (`toRaw.Requirements`); for the SP1 VM channels this stays at
  today's strength (state: `True`, memory: `isU64`), so every existing push-requirement proof survives.

A `VmChannel` with `Owed = Guarantees` produces a `RawChannel` definitionally equal to the
corresponding `Channel.toRaw` — plain channels are the degenerate case. The emission API
(`pull`/`push`/`pullIf`/`pushIf`/`emit`) produces the same `.interact` ops as Clean's, so `main` bodies
migrate by changing only the channel definition, and the mirrored `circuit_norm` lemma set keeps
`circuit_proof_start` producing the same hypothesis shapes. -/

variable {F : Type} [Field F]
variable {Message : TypeMap} [ProvableType Message]

/-- A typed channel whose pull-side `Guarantees` and push-side `Owed` are independent. The engine
(`Soundness/TimedChannel.lean`) closes the gap globally; locally a push owes only `Owed`. -/
structure VmChannel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String
  /-- the semantic payload a pull receives (engine-grounded; NOT proven by pushers locally). -/
  Guarantees (message : Message F) (data : ProverData F) : Prop
  /-- the row-local proof obligation of a push. -/
  Owed (message : Message F) (data : ProverData F) : Prop

namespace VmChannel

/-- The raw channel: pulls receive `Guarantees`, pushes owe `Owed` — Clean's `RawChannel` primitive
carries the split natively. -/
def toRaw (channel : VmChannel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    mult = -1 → channel.Guarantees (fromElements message) data
  Requirements mult message data :=
    mult ≠ -1 → mult ≠ 0 → channel.Owed (fromElements message) data

instance : CoeOut (VmChannel F Message) (RawChannel F) where
  coe := toRaw

@[circuit_norm]
lemma toRaw_name (channel : VmChannel F Message) :
    channel.toRaw.name = channel.name := rfl
@[circuit_norm]
lemma toRaw_arity (channel : VmChannel F Message) :
    channel.toRaw.arity = size Message := rfl

end VmChannel

/-- The typed-interaction mirror of Clean's `ChannelInteraction`, over a `VmChannel`. -/
structure VmChannelInteraction (channel : VmChannel F Message) where
  mult : Expression F
  msg : Message (Expression F)
  assumeGuarantees : Bool

namespace VmChannelInteraction

variable {channel : VmChannel F Message}

def toRaw (i : VmChannelInteraction channel) : AbstractInteraction F :=
  ⟨ channel.toRaw, i.mult, toElements i.msg, i.assumeGuarantees ⟩

@[circuit_norm] lemma toRaw_channel (i : VmChannelInteraction channel) :
  i.toRaw.channel = channel.toRaw := rfl
@[circuit_norm] lemma toRaw_mult (i : VmChannelInteraction channel) :
  i.toRaw.mult = i.mult := rfl
@[circuit_norm] lemma toRaw_msg (i : VmChannelInteraction channel) :
    i.toRaw.msg = toElements i.msg := rfl
@[circuit_norm] lemma toRaw_assumeGuarantees (i : VmChannelInteraction channel) :
    i.toRaw.assumeGuarantees = i.assumeGuarantees := rfl

/-- The typed guarantee an interaction carries (pull side; the semantic payload). -/
@[circuit_norm]
def Guarantees (i : VmChannelInteraction channel) (env : Environment F) : Prop :=
  i.assumeGuarantees → Expression.eval env i.mult = -1 →
    channel.Guarantees (eval env i.msg) env.data

/-- The typed obligation an interaction owes (push side; `Owed`, NOT `Guarantees`). -/
@[circuit_norm]
def Requirements (i : VmChannelInteraction channel) (env : Environment F) : Prop :=
  Expression.eval env i.mult ≠ -1 → Expression.eval env i.mult ≠ 0 →
    channel.Owed (eval env i.msg) env.data

@[circuit_norm]
lemma toRaw_guarantees (env : Environment F) (int : VmChannelInteraction channel) :
    int.toRaw.Guarantees env ↔ int.Guarantees env := by
  simp [AbstractInteraction.Guarantees, Guarantees, toRaw, VmChannel.toRaw,
    ProvableType.fromElements_eval_toElements]

@[circuit_norm]
lemma toRaw_requirements (env : Environment F) (int : VmChannelInteraction channel) :
    int.toRaw.Requirements env ↔ int.Requirements env := by
  simp [AbstractInteraction.Requirements, Requirements, toRaw, VmChannel.toRaw,
    ProvableType.fromElements_eval_toElements]

lemma toRaw_inj {i j : VmChannelInteraction channel} :
    i.toRaw = j.toRaw ↔ i = j := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  rcases i with ⟨ mult, msg, assumeGuarantees ⟩
  rcases j with ⟨ mult', msg', assumeGuarantees' ⟩
  simp only [toRaw, AbstractInteraction.mk.injEq, mk.injEq, true_and] at h ⊢
  rcases h with ⟨ h_mult, h_msg, h_assume ⟩
  refine ⟨ h_mult, ?_, h_assume ⟩
  have h_msg_eq : toElements msg = toElements msg' := eq_of_heq h_msg
  rw [← ProvableType.fromElements_toElements msg,
    ← ProvableType.fromElements_toElements msg', h_msg_eq]

end VmChannelInteraction

namespace VmChannel

variable {channel : VmChannel F Message}

/-! ## Interaction constructors (`expose`-side normal forms, mirroring Clean's) -/

/-- Interaction with multiplicity `-1` (a pull; receives the semantic guarantee). -/
def pulled (channel : VmChannel F Message) (msg : Message (Expression F)) :
    VmChannelInteraction channel :=
  { mult := -1, msg, assumeGuarantees := true }

/-- Conditional pull: at `enabled = 1` a pull, at `enabled = 0` disabled. -/
def pulledIf (channel : VmChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : VmChannelInteraction channel :=
  { mult := -enabled, msg, assumeGuarantees := true }

/-- Interaction with multiplicity `1` (a push; owes `Owed`). -/
def pushed (channel : VmChannel F Message) (msg : Message (Expression F)) :
    VmChannelInteraction channel :=
  { mult := 1, msg, assumeGuarantees := false }

/-- Conditional push: at `enabled = 1` a push, at `enabled = 0` disabled. -/
def pushedIf (channel : VmChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : VmChannelInteraction channel :=
  { mult := enabled, msg, assumeGuarantees := false }

@[circuit_norm] lemma pulled_mult (msg : Message (Expression F)) :
  (channel.pulled msg).mult = -1 := rfl
@[circuit_norm] lemma pulled_msg (msg : Message (Expression F)) :
  (channel.pulled msg).msg = msg := rfl
@[circuit_norm] lemma pulled_assumeGuarantees (msg : Message (Expression F)) :
  (channel.pulled msg).assumeGuarantees = true := rfl
@[circuit_norm] lemma pulledIf_mult (enabled : Expression F) (msg : Message (Expression F)) :
  (channel.pulledIf enabled msg).mult = -enabled := rfl
@[circuit_norm] lemma pulledIf_msg (enabled : Expression F) (msg : Message (Expression F)) :
  (channel.pulledIf enabled msg).msg = msg := rfl
@[circuit_norm] lemma pulledIf_assumeGuarantees (enabled : Expression F) (msg : Message (Expression F)) :
  (channel.pulledIf enabled msg).assumeGuarantees = true := rfl
@[circuit_norm] lemma pushed_mult (msg : Message (Expression F)) :
  (channel.pushed msg).mult = 1 := rfl
@[circuit_norm] lemma pushed_msg (msg : Message (Expression F)) :
  (channel.pushed msg).msg = msg := rfl
@[circuit_norm] lemma pushed_assumeGuarantees (msg : Message (Expression F)) :
  (channel.pushed msg).assumeGuarantees = false := rfl
omit [Field F] in
@[circuit_norm] lemma pushedIf_mult (enabled : Expression F) (msg : Message (Expression F)) :
  (channel.pushedIf enabled msg).mult = enabled := rfl
omit [Field F] in
@[circuit_norm] lemma pushedIf_msg (enabled : Expression F) (msg : Message (Expression F)) :
  (channel.pushedIf enabled msg).msg = msg := rfl
omit [Field F] in
@[circuit_norm] lemma pushedIf_assumeGuarantees (enabled : Expression F) (msg : Message (Expression F)) :
  (channel.pushedIf enabled msg).assumeGuarantees = false := rfl

/-! ## Monadic emission (the `main`-body API, producing the same `.interact` ops as Clean's) -/

/-- Emit an interaction with explicit multiplicity (no guarantee assumed, owes `Owed` off `{0,-1}`). -/
@[circuit_norm]
def emit (channel : VmChannel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    Circuit F Unit := fun _ =>
  let interaction : VmChannelInteraction channel := ⟨ mult, msg, false ⟩
  ((), [.interact interaction.toRaw])

/-- Pull: multiplicity `-1`, receives the semantic guarantee. -/
@[circuit_norm]
def pull (channel : VmChannel F Message) (msg : Message (Expression F)) :
    Circuit F Unit := fun _ =>
  let interaction : VmChannelInteraction channel := ⟨ -1, msg, true ⟩
  ((), [.interact interaction.toRaw])

/-- Gated pull: multiplicity `-enabled`, receives the semantic guarantee when live. -/
@[circuit_norm]
def pullIf (channel : VmChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : VmChannelInteraction channel := ⟨ -enabled, msg, true ⟩
  ((), [.interact interaction.toRaw])

/-- Push: multiplicity `1`, owes `Owed` row-locally. -/
@[circuit_norm]
def push (channel : VmChannel F Message) (msg : Message (Expression F)) :
    Circuit F Unit := fun _ =>
  let interaction : VmChannelInteraction channel := ⟨ 1, msg, false ⟩
  ((), [.interact interaction.toRaw])

/-- Gated push: multiplicity `enabled`, owes `Owed` when live. -/
@[circuit_norm]
def pushIf (channel : VmChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  let interaction : VmChannelInteraction channel := ⟨ enabled, msg, false ⟩
  ((), [.interact interaction.toRaw])

/-! ## Exposure (the `exposedChannels` API) -/

/-- Expose a `VmChannel` interaction list (raw `ExposedChannel`, like Clean's `expose`). -/
def expose (channel : VmChannel F Message)
    (interactions : List (VmChannelInteraction channel)) : List (ExposedChannel F) :=
  [{ channel := channel.toRaw, interactions := interactions.map (·.toRaw) }]

/-- The `ExposedChannelsLawful`-reducer for `VmChannel.expose` — the analog of Clean's
`Channel.exposedChannelsLawful_expose` (`@[circuit_norm ↓]`), so a chip's `exposedChannels_eq` over a
`VmChannel.expose` reduces to a single `interactionsWith channel.toRaw = interactions.map toRaw` goal. -/
@[circuit_norm ↓]
lemma exposedChannelsLawful_expose (ops : Operations F) (channel : VmChannel F Message)
    (interactions : List (VmChannelInteraction channel)) :
    ops.ExposedChannelsLawful (channel.expose interactions) ↔
      ops.interactionsWith channel.toRaw = interactions.map (·.toRaw) := by
  simp only [Operations.ExposedChannelsLawful, expose, List.mem_singleton, forall_eq]

@[circuit_norm]
lemma mem_expose_pullIf_pushIf (enabled enabled' : Expression F)
    (pull pull' push push' : Message (Expression F)) :
    (⟨ channel.toRaw, [(channel.pulledIf enabled pull).toRaw,
      (channel.pushedIf enabled push).toRaw] ⟩ : ExposedChannel F) ∈
      channel.expose [channel.pulledIf enabled' pull', channel.pushedIf enabled' push'] ↔
    enabled = enabled' ∧ pull = pull' ∧ push = push' := by
  simp only [expose, List.mem_singleton, List.map_cons, List.map_nil,
    ExposedChannel.mk.injEq, true_and, List.cons.injEq, and_true,
    VmChannelInteraction.toRaw_inj, pulledIf, pushedIf]
  simp
  tauto

@[circuit_norm]
lemma mem_expose_pulled_pushed (pull pull' push push' : Message (Expression F)) :
    (⟨ channel.toRaw, [(channel.pulled pull).toRaw,
      (channel.pushed push).toRaw] ⟩ : ExposedChannel F) ∈
      channel.expose [channel.pulled pull', channel.pushed push'] ↔
    pull = pull' ∧ push = push' := by
  simp only [expose, List.mem_singleton, List.map_cons, List.map_nil,
    ExposedChannel.mk.injEq, true_and, List.cons.injEq, and_true,
    VmChannelInteraction.toRaw_inj, pulled, pushed]
  simp

/-! ## Evaluated interaction values (the witness-level normal forms, mirroring Clean's `*Value`) -/

@[circuit_norm]
def pulledValue (channel : VmChannel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := -1
  msg := (toElements msg).toArray
  same_size := by simp [VmChannel.toRaw]
  assumeGuarantees := true

@[circuit_norm]
def pushedValue (channel : VmChannel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := 1
  msg := (toElements msg).toArray
  same_size := by simp [VmChannel.toRaw]
  assumeGuarantees := false

@[circuit_norm]
def pulledIfValue (channel : VmChannel F Message) (enabled : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := -enabled
  msg := (toElements msg).toArray
  same_size := by simp [VmChannel.toRaw]
  assumeGuarantees := true

@[circuit_norm]
def pushedIfValue (channel : VmChannel F Message) (enabled : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := enabled
  msg := (toElements msg).toArray
  same_size := by simp [VmChannel.toRaw]
  assumeGuarantees := false

/-- A boolean-gated pull owes nothing (its `Requirements` is vacuous at mults `0`/`-1`). -/
lemma pulledIfValue_requirements_of_isBool_enabled {channel : VmChannel F Message}
  {enabled : F} {msg : Message F} {data : ProverData F} :
    enabled = 0 ∨ enabled = 1 →
    (channel.pulledIfValue enabled msg).Requirements data := by
  simp only [Interaction.Requirements, pulledIfValue, VmChannel.toRaw]
  grind

/-- A push assumes no guarantees (its `Guarantees` is vacuous). -/
lemma pushedIfValue_guarantees {channel : VmChannel F Message}
  {enabled : F} {msg : Message F} {data : ProverData F} :
    (channel.pushedIfValue enabled msg).Guarantees data := by
  simp [Interaction.Guarantees, pushedIfValue]

private lemma toArray_map_eval {msg : Message (Expression F)} {env : Environment F} :
    (Vector.map (fun x => Expression.eval env x) (toElements msg)).toArray
      = (toElements (eval env msg)).toArray :=
  congrArg Vector.toArray
    (by rw [← ProvableType.fromElements_eq_iff, CircuitType.eval_var]; rfl)

lemma eval_pulled {channel : VmChannel F Message} {msg : Message (Expression F)}
    {env : Environment F} :
    ((channel.pulled msg).toRaw).eval env = channel.pulledValue (eval env msg) := by
  simp only [circuit_norm, pulled, VmChannelInteraction.toRaw, AbstractInteraction.eval,
    Interaction.mk.injEq]
  exact toArray_map_eval

lemma eval_pushed {channel : VmChannel F Message} {msg : Message (Expression F)}
    {env : Environment F} :
    ((channel.pushed msg).toRaw).eval env = channel.pushedValue (eval env msg) := by
  simp only [circuit_norm, pushed, VmChannelInteraction.toRaw, AbstractInteraction.eval,
    Interaction.mk.injEq]
  exact toArray_map_eval

lemma eval_pulledIf {channel : VmChannel F Message} {enabled : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
    ((channel.pulledIf enabled msg).toRaw).eval env
      = channel.pulledIfValue (Expression.eval env enabled) (eval env msg) := by
  simp only [circuit_norm, pulledIf, VmChannelInteraction.toRaw, AbstractInteraction.eval,
    Interaction.mk.injEq]
  exact toArray_map_eval

lemma eval_pushedIf {channel : VmChannel F Message} {enabled : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
    ((channel.pushedIf enabled msg).toRaw).eval env
      = channel.pushedIfValue (Expression.eval env enabled) (eval env msg) := by
  simp only [circuit_norm, pushedIf, VmChannelInteraction.toRaw, AbstractInteraction.eval,
    Interaction.mk.injEq]
  exact toArray_map_eval

/-! ## The degenerate case: `Owed = Guarantees` recovers a plain Clean channel -/

/-- A `VmChannel` with `Owed = Guarantees` has the same raw channel as the plain `Channel` with the
same name and guarantee — plain channels are the degenerate case of the split. -/
lemma toRaw_eq_channel_toRaw (name : String)
    (G : Message F → ProverData F → Prop) :
    (VmChannel.toRaw ⟨name, G, G⟩ : RawChannel F)
      = Channel.toRaw ⟨name, G⟩ := rfl

end VmChannel
