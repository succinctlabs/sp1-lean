import SP1Clean.Foundations.ByteTable
import SP1Clean.Foundations.Word
import Clean.Circuit.Basic
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Cross-chip interaction channels (the bus, as the circuit actually emits it)

The shared Clean `Channel`s that the readers/chips `push`/`pull` to model SP1's cross-chip
interaction buses (`builder.send`/`receive`). Each `Channel` here is the Lean analog of one SP1
`InteractionKind`; emitting on it is the *real* in-circuit bus (vs. the hand-written trace-level
`*Lookups` shadows in `Soundness/`), so that `Soundness/*Consistency.lean` can eventually be
re-pointed at `Operations.interactionsWith <channel>` and the projections become theorems
(`interactionsWith_eq_of_mem_exposedChannels`). See `docs/bus-model.md`.

The feasibility of emitting these inside the witnessed-`FormalCircuit` recipe — axiom-clean, at the
existing heartbeat floor — was established by `Readers/CPUStateChannelSpike.lean`.

This module carries the **State** bus (the slice already modelled at the trace level by
`Soundness/StateConsistency.lean`) and the **Byte** bus (SP1's preprocessed `ByteChip`,
`Foundations/ByteTable.lean`). The `Program`/`Memory` channels join here as their phases land. -/

namespace SP1Clean.Channels

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The **multiplicity-gated raw form** of a channel — the faithful-to-SP1 obligation. Unlike
`Channel.toRaw`, whose `Requirements` fires at *every* `mult ≠ -1` (padding `mult = 0` included, so it would
demand the guarantee on free padding columns — see `docs/bus-model.md` §7), this fires the proof obligation
only when the interaction **genuinely participates** (`mult ∉ {0, -1}`, i.e. `is_real ≠ 0` on a send), and
hands the guarantee at a genuine receive (`mult = -1`). Padding (`mult = 0`) owes and assumes nothing —
exactly matching SP1, where a multiplicity-`0` interaction drops out of the LogUp sum and its values are
irrelevant. The audit (`docs/bus-model.md` §7): SP1 leaves padding columns free and relies on global
multiplicity-matching, so the model gates the obligation on `mult ≠ 0` rather than range-checking
unconditionally (which would regress the `is_real` multiplicity) or value-folding. -/
def _root_.Channel.toRawGated {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data := mult = -1 → channel.Guarantees (fromElements message) data
  Requirements mult message data :=
    mult ≠ -1 → mult ≠ 0 → channel.Guarantees (fromElements message) data

@[circuit_norm] lemma _root_.Channel.toRawGated_name {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) : channel.toRawGated.name = channel.name := rfl
@[circuit_norm] lemma _root_.Channel.toRawGated_arity {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) : channel.toRawGated.arity = size Message := rfl
@[circuit_norm] lemma _root_.Channel.toRawGated_guarantees {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (mult : F) (message : Vector F (size Message))
    (data : ProverData F) :
    channel.toRawGated.Guarantees mult message data
      = (mult = -1 → channel.Guarantees (fromElements message) data) := rfl
@[circuit_norm] lemma _root_.Channel.toRawGated_requirements {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (mult : F) (message : Vector F (size Message))
    (data : ProverData F) :
    channel.toRawGated.Requirements mult message data
      = (mult ≠ -1 → mult ≠ 0 → channel.Guarantees (fromElements message) data) := rfl

/-- The **received** (gated) interaction in normal form — the `assumeGuarantees := true` analog of
`emittedGated` for the symmetric `toRawGated` channel: what `gatedReceive` emits. Kept **folded** with
`@[circuit_norm]` projection lemmas so the `interactionsWith` channel filter and the soundness/completeness
`.Requirements`/`.Guarantees` reduce to the clean implication form (the role Clean's
`ChannelInteraction.toRaw_*` lemmas played for the old `toRaw` pull). -/
def _root_.Channel.receivedGated {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    AbstractInteraction F :=
  ⟨channel.toRawGated, -gate, toElements msg, true⟩

@[circuit_norm] lemma _root_.Channel.receivedGated_channel {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    (channel.receivedGated gate msg).channel = channel.toRawGated := rfl
@[circuit_norm] lemma _root_.Channel.receivedGated_mult {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    (channel.receivedGated gate msg).mult = -gate := rfl
@[circuit_norm] lemma _root_.Channel.receivedGated_msg {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    (channel.receivedGated gate msg).msg = toElements msg := rfl
@[circuit_norm] lemma _root_.Channel.receivedGated_assumeGuarantees {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    (channel.receivedGated gate msg).assumeGuarantees = true := rfl

/-- The received pull's soundness/completeness **requirement** (`circuit_norm`): owes the channel guarantee
only at genuine participation (`mult ∉ {0,-1}`), which a binary `-gate` never reaches (`binary_gate_req_vacuous`). -/
@[circuit_norm]
lemma _root_.Channel.receivedGated_requirements {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Requirements (channel.receivedGated gate msg) env ↔
      (Expression.eval env (-gate) ≠ -1 → Expression.eval env (-gate) ≠ 0 →
        channel.Guarantees (Eval.eval env msg) env.data) := by
  simp only [Channel.receivedGated, AbstractInteraction.Requirements, Channel.toRawGated,
    ProvableType.fromElements_eval_toElements]

/-- The received pull's **guarantee** (`circuit_norm`): hands `channel.Guarantees` to soundness at `mult = -1`
(a real row, `gate = 1`); padding (`mult = 0`) hands nothing. -/
@[circuit_norm]
lemma _root_.Channel.receivedGated_guarantees {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Guarantees (channel.receivedGated gate msg) env ↔
      (Expression.eval env (-gate) = -1 → channel.Guarantees (Eval.eval env msg) env.data) := by
  simp only [Channel.receivedGated, AbstractInteraction.Guarantees, Channel.toRawGated,
    ProvableType.fromElements_eval_toElements, true_implies]

/-- A **gated receive**: a `pull` on the multiplicity-gated raw form (`toRawGated`) whose multiplicity is
`-gate` instead of the constant `-1` — so on real rows (`gate = is_real = 1`) it is `-1` and fires the
channel's `Guarantees`, and on padding (`gate = 0`) it is `0`, contributing nothing to the bus (genuinely
`is_real`-gated, matching SP1's `send_byte` multiplicity with **raw** values; `docs/bus-model.md` §7).
Because it is `toRawGated`, the `Requirements` clause fires only at genuine participation (`mult ∉ {0,-1}`),
which a binary `gate` never reaches — so padding owes nothing and the value is passed **raw** (no
`gate * value` fold). A consumer that assumes `gate ∈ {0,1}` discharges the (vacuous) requirement via
`binary_gate_req_vacuous`. On real rows it hands soundness the channel's `Guarantees` (e.g. `ByteRowSpec`).
Definitionally identical to `receiveGated` (the byte bus's name for the same gated pull). -/
@[circuit_norm]
def _root_.Channel.gatedReceive {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    Circuit F Unit := fun _ =>
  ((), [.interact (channel.receivedGated gate msg)])

/-- The emitted (gated) interaction in normal form — the analog of Clean's `emitted` for the
multiplicity-gated raw channel (`assumeGuarantees := false`). Sharing this between `emitGated` (what `main`
emits) and `exposeGated` (what `exposedChannels` declares) keeps the `channelsLawful` exposed-consistency a
syntactic match. -/
def _root_.Channel.emittedGated {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    AbstractInteraction F :=
  ⟨channel.toRawGated, mult, toElements msg, false⟩

-- Keep `emittedGated` **folded** (à la Clean's `emitted`) and expose its projections as `@[circuit_norm]`
-- rfl-lemmas, so the `interactionsWith` channel filter + the soundness `.Requirements`/`.Guarantees`
-- (below) match on the folded form rather than an unfolded record.
@[circuit_norm] lemma _root_.Channel.emittedGated_channel {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    (channel.emittedGated mult msg).channel = channel.toRawGated := rfl
@[circuit_norm] lemma _root_.Channel.emittedGated_mult {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    (channel.emittedGated mult msg).mult = mult := rfl
@[circuit_norm] lemma _root_.Channel.emittedGated_msg {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    (channel.emittedGated mult msg).msg = toElements msg := rfl
@[circuit_norm] lemma _root_.Channel.emittedGated_assumeGuarantees {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    (channel.emittedGated mult msg).assumeGuarantees = false := rfl

/-- A **gated emit** on the multiplicity-gated raw channel (`assumeGuarantees := false`): the SP1-faithful
send / receive-direction emit whose proof obligation is vacuous on padding (`mult = 0`). Use for the
State/Memory/Program *sends* (`mult = +is_real`) and the receive-direction emits (`mult = -is_real`) that the
chip must *prove*. The `is_real` multiplicity is preserved; padding owes nothing (`toRawGated`). -/
@[circuit_norm]
def _root_.Channel.emitGated {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) :
    Circuit F Unit := fun _ =>
  ((), [.interact (channel.emittedGated mult msg)])

/-- Expose a list of gated emits for the "emitted = projection" recovery — the analog of Clean's `expose`
for the multiplicity-gated raw channel (declares `channel.toRawGated`, interactions verbatim). -/
@[circuit_norm]
def _root_.Channel.exposeGated {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (interactions : List (AbstractInteraction F)) : List (ExposedChannel F) :=
  [{ channel := channel.toRawGated, interactions }]

/-- The soundness obligation of a gated emit, in usable form — the `toRawGated` analog of Clean's
`ChannelInteraction.toRaw_requirements`. A gated emit owes its channel guarantee **only when it genuinely
participates** (`mult ∉ {0, -1}`); padding (`mult = 0`) and the receive direction (`mult = -1`) owe nothing.
Tagged `circuit_norm` so `circuit_proof_start`/soundness unfolds the emit's `.Requirements` automatically. -/
@[circuit_norm]
lemma _root_.Channel.emittedGated_requirements {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Requirements (channel.emittedGated mult msg) env ↔
      (Expression.eval env mult ≠ -1 → Expression.eval env mult ≠ 0 →
        channel.Guarantees (Eval.eval env msg) env.data) := by
  simp only [Channel.emittedGated, AbstractInteraction.Requirements, Channel.toRawGated,
    ProvableType.fromElements_eval_toElements]

/-- A gated emit hands soundness **nothing** as a local guarantee (`assumeGuarantees := false`): its meaning
is the trace-level bus balance, not a per-row hypothesis. The `toRawGated` analog of the
`assumeGuarantees = false` branch of `ChannelInteraction.toRaw_guarantees`. -/
@[circuit_norm]
lemma _root_.Channel.emittedGated_guarantees {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (mult : Expression F) (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Guarantees (channel.emittedGated mult msg) env ↔ True := by
  simp only [Channel.emittedGated, AbstractInteraction.Guarantees, iff_true]
  intro h; exact absurd h (by simp)

/-- A **gated receive** on the multiplicity-gated raw channel (`assumeGuarantees := true`, `mult = -gate`):
hands the channel's `Guarantees` to soundness on a real row (`gate = 1`, `mult = -1`) and owes/assumes
nothing on padding (`gate = 0`, `mult = 0`). Use for register read-backs that *assume* `isU64` of the read
value (the writer proved it) — the genuine receive that gives a consuming chip a usable hypothesis. -/
@[circuit_norm]
def _root_.Channel.receiveGated {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (gate : Expression F) (msg : Message (Expression F)) :
    Circuit F Unit := fun _ =>
  ((), [.interact ⟨channel.toRawGated, -gate, toElements msg, true⟩])

/-! ### Asymmetric gated channel — receive assumes more than a send proves

For the **Memory** bus the receive/send obligation is genuinely asymmetric: a register **read-back receive**
*assumes* the full message well-formedness (`addr`-shape **and** `isU64` of the value), while a **send** only
*proves* the `addr`-shape. The `isU64` gap is a cross-chip fact — the *writer* range-checked the value and the
offline-memory balance carries it to the reader — so the reader assumes it without a matching local send proof
(justified by the trace-level balance, `Soundness/MemoryConsistency.lean`'s `TraceMemoryLink`; SP1's memory
model, `docs/bus-model.md` §7). `toRawGatedAsym channel sendReq` puts the strong `channel.Guarantees` on the
**receive** (`mult = -1`) and the weak `sendReq` on the **send** (`mult ∉ {0,-1}`); padding (`mult = 0`) owes
and assumes nothing. -/
def _root_.Channel.toRawGatedAsym {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data := mult = -1 → channel.Guarantees (fromElements message) data
  Requirements mult message data := mult ≠ -1 → mult ≠ 0 → sendReq (fromElements message) data

@[circuit_norm] lemma _root_.Channel.toRawGatedAsym_name {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) :
    (channel.toRawGatedAsym sendReq).name = channel.name := rfl
@[circuit_norm] lemma _root_.Channel.toRawGatedAsym_arity {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) :
    (channel.toRawGatedAsym sendReq).arity = size Message := rfl

/-- A **send** on the asymmetric channel (`assumeGuarantees := false`), kept folded with `@[circuit_norm]`
projection lemmas (like `emittedGated`). Proves only `sendReq` on a genuine send. -/
def _root_.Channel.sentAsym {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (mult : Expression F)
    (msg : Message (Expression F)) : AbstractInteraction F :=
  ⟨channel.toRawGatedAsym sendReq, mult, toElements msg, false⟩

@[circuit_norm] lemma _root_.Channel.sentAsym_channel {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (mult : Expression F) (msg) :
    (channel.sentAsym sendReq mult msg).channel = channel.toRawGatedAsym sendReq := rfl
@[circuit_norm] lemma _root_.Channel.sentAsym_mult {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (mult : Expression F) (msg) :
    (channel.sentAsym sendReq mult msg).mult = mult := rfl
@[circuit_norm] lemma _root_.Channel.sentAsym_msg {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (mult : Expression F) (msg) :
    (channel.sentAsym sendReq mult msg).msg = toElements msg := rfl
@[circuit_norm] lemma _root_.Channel.sentAsym_assumeGuarantees {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (mult : Expression F) (msg) :
    (channel.sentAsym sendReq mult msg).assumeGuarantees = false := rfl

/-- A **receive** on the asymmetric channel (`assumeGuarantees := true`, `mult = -gate`), folded with
projection lemmas. Hands the strong `channel.Guarantees` on a real row. -/
def _root_.Channel.recvAsym {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (gate : Expression F)
    (msg : Message (Expression F)) : AbstractInteraction F :=
  ⟨channel.toRawGatedAsym sendReq, -gate, toElements msg, true⟩

@[circuit_norm] lemma _root_.Channel.recvAsym_channel {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (gate : Expression F) (msg) :
    (channel.recvAsym sendReq gate msg).channel = channel.toRawGatedAsym sendReq := rfl
@[circuit_norm] lemma _root_.Channel.recvAsym_mult {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (gate : Expression F) (msg) :
    (channel.recvAsym sendReq gate msg).mult = -gate := rfl
@[circuit_norm] lemma _root_.Channel.recvAsym_msg {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (gate : Expression F) (msg) :
    (channel.recvAsym sendReq gate msg).msg = toElements msg := rfl
@[circuit_norm] lemma _root_.Channel.recvAsym_assumeGuarantees {F : Type} [Field F] {Message : TypeMap}
    [ProvableType Message] (channel : Channel F Message) (sendReq) (gate : Expression F) (msg) :
    (channel.recvAsym sendReq gate msg).assumeGuarantees = true := rfl

/-- The send obligation (`circuit_norm`): a `sentAsym` owes only `sendReq` on a genuine send (`mult ∉ {0,-1}`). -/
@[circuit_norm]
lemma _root_.Channel.sentAsym_requirements {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (mult : Expression F)
    (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Requirements (channel.sentAsym sendReq mult msg) env ↔
      (Expression.eval env mult ≠ -1 → Expression.eval env mult ≠ 0 → sendReq (Eval.eval env msg) env.data) := by
  simp only [Channel.sentAsym, AbstractInteraction.Requirements, Channel.toRawGatedAsym,
    ProvableType.fromElements_eval_toElements]

/-- The receive guarantee (`circuit_norm`): a `recvAsym` hands the strong `channel.Guarantees` at `mult = -1`. -/
@[circuit_norm]
lemma _root_.Channel.recvAsym_guarantees {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (gate : Expression F)
    (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Guarantees (channel.recvAsym sendReq gate msg) env ↔
      (Expression.eval env (-gate) = -1 → channel.Guarantees (Eval.eval env msg) env.data) := by
  simp only [Channel.recvAsym, AbstractInteraction.Guarantees, Channel.toRawGatedAsym,
    ProvableType.fromElements_eval_toElements, true_implies]

/-- The receive's own (vacuous on real rows / padding) send-obligation: `recvAsym` owes `sendReq` only at
`mult ∉ {0,-1}`, which a `-gate` multiplicity with `gate ∈ {0,1}` never hits. -/
@[circuit_norm]
lemma _root_.Channel.recvAsym_requirements {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (gate : Expression F)
    (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Requirements (channel.recvAsym sendReq gate msg) env ↔
      (Expression.eval env (-gate) ≠ -1 → Expression.eval env (-gate) ≠ 0 →
        sendReq (Eval.eval env msg) env.data) := by
  simp only [Channel.recvAsym, AbstractInteraction.Requirements, Channel.toRawGatedAsym,
    ProvableType.fromElements_eval_toElements]

/-- A `sentAsym` hands soundness **nothing** (`assumeGuarantees := false`) — clears the vacuous send
guarantees from `h_holds`. -/
@[circuit_norm]
lemma _root_.Channel.sentAsym_guarantees {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (mult : Expression F)
    (msg : Message (Expression F)) (env : Environment F) :
    AbstractInteraction.Guarantees (channel.sentAsym sendReq mult msg) env ↔ True := by
  simp only [Channel.sentAsym, AbstractInteraction.Guarantees, iff_true]
  intro h; exact absurd h (by simp)

/-- Emit a **send** on the asymmetric channel. -/
@[circuit_norm]
def _root_.Channel.emitGatedAsym {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (mult : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.sentAsym sendReq mult msg)])

/-- Emit a genuine **receive** on the asymmetric channel (`mult = -gate`). -/
@[circuit_norm]
def _root_.Channel.receiveGatedAsym {F : Type} [Field F] {Message : TypeMap} [ProvableType Message]
    (channel : Channel F Message) (sendReq : Message F → ProverData F → Prop) (gate : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.recvAsym sendReq gate msg)])

/-- The State-bus message — `(clk_high, clk_low, pc0, pc1, pc2)`, arity 5, matching SP1's
`AirInteraction.state` (`crates/hypercube/src/lookup/interaction.rs`) and the `.state` interaction in
`Extracted/CPUState.lean`. Each CPU/ALU row receives the current `(clk, pc)` and sends the next. -/
structure StateMsg (F : Type) where
  clk_high : F
  clk_low : F
  pc0 : F
  pc1 : F
  pc2 : F
deriving ProvableStruct

/-- Per-row well-formedness of a State message: **`True`**. SP1's `CPUState::eval`
(`crates/core/machine/src/adapter/state.rs:90-98`) range-checks *only* the clock (`clk_0_16` 13-bit Range
+ `clk_16_24` U8Range) — **it does not range-check `pc`** (the `receive_state`/`send_state` pass `cols.pc`/
`next_pc` un-bounded). So the State *send* proves no local guarantee; the pc-limb bounds are *received*
facts (the previous row's send / the verifier-committed initial pc via the PC chain, and the program ROM),
exactly like the register-index bounds. The earlier `pc < 2^16` conjuncts here were discharged by divergent
`pc` byte checks in `Readers/CPUState.lean` that SP1 has no analog of; removed in the byte faithfulness
cleanup. The cross-row PC chain stays the trace level (`Soundness/StateConsistency.lean`). -/
def StateMsg.Spec (_ : StateMsg (ZMod p)) : Prop := True

/-- The State channel (SP1 `InteractionKind.State`). `Guarantees := StateMsg.Spec = True`: SP1's State
send proves no local well-formedness (it range-checks no pc; the clk checks are separate byte sends). Still
emitted via `emitGated` (`toRawGated`) so the `is_real` multiplicity (`+is_real` send / `-is_real`
receive / `0` padding) is preserved. The cross-row PC chain stays the trace level
(`Soundness/StateConsistency.lean`). -/
def stateChannel : Channel (ZMod p) StateMsg where
  name := "SP1State"
  Guarantees msg _ := StateMsg.Spec msg

/-- The Memory-bus message — `(clk_high, clk_low, addr0, addr1, addr2, v0, v1, v2, v3)`, arity 9,
matching SP1's `AirInteraction.memory` (`crates/hypercube/src/lookup/interaction.rs`) and the `.memory`
interaction in `Extracted/RTypeReader.lean`. Registers use `addr0` = register index, `addr1 = addr2 = 0`;
`(v0, v1, v2, v3)` is the 4-limb little-endian word. Each register access sends the prior value at the
previous timestamp and receives the new value at the current timestamp. -/
structure MemoryMsg (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  v0 : F
  v1 : F
  v2 : F
  v3 : F
deriving ProvableStruct

/-- Per-row register-access address shape (`addr1 = addr2 = 0`). Kept as a small structural predicate (e.g.
for trace use); it is **not** the memory channel's `Guarantees` — see `memoryChannel`. -/
def MemoryMsg.Spec (msg : MemoryMsg (ZMod p)) : Prop :=
  msg.addr1 = 0 ∧ msg.addr2 = 0

/-- The Memory channel (SP1 `InteractionKind.Memory`). `Guarantees := True`: the memory bus is **just the
balance** — the chip *emits* the per-row register interactions (`±is_real`) and the value's well-formedness
(`isU64`) is **not** a per-row channel fact. Operand `isU64` for a consuming ALU chip is a chip-level
**`Assumptions`** precondition (discharged at the machine/trace level from the offline-memory balance + the
writer), not forced into the channel — the idiomatic split (see `docs/bus-model.md` §7). The cross-row
offline-memory meaning stays trace-level (`Soundness/MemoryConsistency.lean`'s `TraceMemoryLink`). The `name`
matches the `"SP1Memory"` key in `memoryLookups`. -/
def memoryChannel : Channel (ZMod p) MemoryMsg where
  name := "SP1Memory"
  Guarantees _ _ := True

/-- The Program-bus message — the arity-16 instruction-fetch tuple `(pc0, pc1, pc2, opcode, op_a,
op_b0..3, op_c0..3, op_a_0, imm_b, imm_c)`, matching SP1's `AirInteraction.program`
(`crates/hypercube/src/lookup/interaction.rs`, `InteractionKind::Program => 16`) and the `.send
(.program …)` in `Extracted/RTypeReader.lean`. `op_b`/`op_c` are the two operands as 4-limb words; for an
R-type row only the register-index limb is non-zero (`op_b1..3 = op_c1..3 = imm_b = imm_c = 0`). -/
structure ProgramMsg (F : Type) where
  pc0 : F
  pc1 : F
  pc2 : F
  opcode : F
  op_a : F
  op_b0 : F
  op_b1 : F
  op_b2 : F
  op_b3 : F
  op_c0 : F
  op_c1 : F
  op_c2 : F
  op_c3 : F
  op_a_0 : F
  imm_b : F
  imm_c : F
deriving ProvableStruct

/-- Per-row well-formedness of a Program message — the part a CPU row can **send-prove locally** for *any*
adapter type. The only genuinely send-local fact is that `op_a_0` is boolean (from the reader's
unconditional `op_a_0 * (op_a_0 - 1) = 0` gate). Everything else is a **decode** fact that belongs on the
**receive** side (`ProgramChip.ProgramRowSpec`), not the send-side channel `Guarantees`:
the register-index **bounds** (`op_a < 32`, `op_b0`/`op_c0 < 2^16`), the opcode `trusted_instr` decode, the
`op_a_0 = 1 ↔ op_a = 0` decode, pc bounds/alignment, **and the R-type/I-type operand shape** (`op_b1..3 = 0`,
and for register-`c` ops `op_c1..3 = imm_c = 0`). The last point is why this is *not* `op_c1..3 = imm_c = 0`:
an immediate-`c` op (the `ALUTypeReader` adapter — `Addw`, `Lt`, `Bitwise`, shifts) legitimately sends a
non-zero `op_c` word with `imm_c = 1`, so the R/I-type shape cannot be a send guarantee; it is decoded on
receive. (`RTypeReader` still emits literal `0`s in those slots, so it proves the same — strictly weaker —
guarantee; nothing downstream consumes the dropped facts. ROM-membership stays trace-level,
`Soundness/ProgramConsistency.lean`.) -/
def ProgramMsg.Spec (msg : ProgramMsg (ZMod p)) : Prop :=
  msg.op_a_0 = 0 ∨ msg.op_a_0 = 1

/-- The Program channel (SP1 `InteractionKind.Program`). `Guarantees := ProgramMsg.Spec` (R-type shape +
`op_a_0` boolean). Emitted via `Channel.emit` (default `toRaw`, gated by `is_trusted` = `is_real` on Add):
the shape slots are literal `0` and `op_a_0` boolean comes from the reader's unconditional gate, so the send
proves the guarantee on every row. The index bounds + opcode decode are *received* from the decode/ProgramChip
(not a local send). The `name` matches the `"SP1Program"` key in `programLookups`. -/
def programChannel : Channel (ZMod p) ProgramMsg where
  name := "SP1Program"
  Guarantees msg _ := ProgramMsg.Spec msg

/-- The Byte channel (SP1 `InteractionKind.Byte`), lookups into the preprocessed `ByteChip`/`RangeChip`.
Its `Guarantees` is `ByteRowSpec`, the byte-table membership predicate — and **Byte is the root of
well-formedness** (`docs/bus-model.md` §7): unlike State/Memory/Program (dynamic buses → emit,
`Guarantees := True`), the byte receiver is a *preprocessed static table* whose rows satisfy `ByteRowSpec`
by construction, so it is the one bus where a consumer can soundly **pull** and obtain the fact locally.
A range check that *needs* its fact (`BitwiseOperation`'s `result = b op c`, `AddOperation`'s result range)
pulls `(op, value, w, 0)` and gets `ByteRowSpec`; a reader that only emits the check pulls-and-discards.
Gating is **multiplicity-gated** (`gatedReceive`, mult `-is_real` on `toRawGated`), faithful to SP1's
`send_byte(op, value, w, 0, is_real)`: the value is passed **raw** (no `is_real * value` fold) and padding
(`mult = 0`) drops out of the LogUp sum entirely (`mult / fingerprint(values)` with `mult = 0`), owing
nothing — discharged by `binary_gate_req_vacuous` (`docs/bus-model.md` §7). The provider side is
`Chips/ByteChip.lean` (pushes the table, proves each row); until it lands the pull's justification is
threaded as `Soundness/ByteConsistency.lean`'s `TraceByteLink`. Pulled by
`Readers/{CPUState,RegisterAccessTimestamp,RegisterAccessCols,RTypeReader}.lean`. -/
def byteChannel : Channel (ZMod p) ByteRow where
  name := "SP1Byte"
  Guarantees msg _ := ByteRowSpec msg

omit [Fact (2 ^ 17 < p)] in
/-- A `toRawGated` byte/range pull's **padding requirement** is vacuous for a binary `is_real` gate: the
`gatedReceive` multiplicity is `-is_real`, so its requirement antecedents `-is_real ≠ -1` (⟹ `is_real ≠ 1`)
and `-is_real ≠ 0` (⟹ `is_real ≠ 0`) are *jointly contradictory* — no byte reasoning, no value-fold.
This replaces the old `gate_zero_of_ne … ; (byteRowSpec_* 0).mpr …` discharge: faithful to SP1, where a
multiplicity-`0` (or `-1`) interaction imposes no local obligation (`docs/bus-model.md` §7). -/
lemma binary_gate_req_vacuous {is_real : ZMod p} (hbin : is_real = 0 ∨ is_real = 1) (P : Prop) :
    (-is_real ≠ -1 → -is_real ≠ 0 → P) := by
  rcases hbin with h | h <;> subst h <;> simp

open Classical in
/-- **Subcircuit interactions, kept in `interactionsWith` form.** Combines Clean's
`Operations.interactionsWith_subcircuit` (which exposes the raw `FlatOperation.interactions … |>.filter`)
with `FormalCircuit.toSubcircuit_interactions` (which rewrites that flat list back to the child `main`'s
operations). Keeping the result as `interactionsWith channel ((circuit.main input).operations n)` — rather
than the unfolded `.interactions.filter` — is what lets a child's bottom-up `interactionsWith_<chan>_eq`
rfl-lemma fire when a parent composes it (the readers' Memory/Program recovery, `docs/bus-model.md` §5/§7).
Tagged `circuit_norm` at **high priority** so it fires before Clean's more-general
`Operations.interactionsWith_subcircuit` (which would expose the raw `FlatOperation` form and lose the
fold). -/
@[circuit_norm high]
lemma interactionsWith_subcircuit_formal {F : Type} [Field F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (channel : RawChannel F) (circuit : FormalCircuit F Input Output)
    (input : Var Input F) (n : ℕ) (ops : Operations F) :
    Operations.interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops) =
      Operations.interactionsWith channel ((circuit.main input).operations n) ++
        Operations.interactionsWith channel ops := by
  rw [Operations.interactionsWith_subcircuit, FormalCircuit.toSubcircuit_interactions]
  rfl

set_option linter.unusedSectionVars false in
/-- Two channels with distinct `name`s have distinct `toRaw`s — as a `simp`-shaped `= False` so the
`interactionsWith` per-op `if i.channel = channel` conditions for a *different* bus reduce to the `else`
branch **without expanding the channel record** (which would break a child's bottom-up
`interactionsWith_<chan>_eq` rfl-lemma matching). -/
private lemma toRaw_eq_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (h : c1.name ≠ c2.name) :
    (c1.toRaw = c2.toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  exact h (by rw [← Channel.toRaw_name c1, ← Channel.toRaw_name c2, he])

omit [Fact (2 ^ 17 < p)] in
/-- A `toRaw` and a `toRawGated` with distinct `name`s are distinct `RawChannel`s — the mixed-form analog of
`toRaw_eq_false_of_name_ne`, needed once a chip lists both `byteChannel.toRawGated` (gated *receive*) and a
`*.toRawGated` (gated *emit*) in its channel lists. (`omit`s the `2^17` fact so it applies in `CPUState`'s
`channelsLawful`, which elaborates under `Fact p.Prime` only.) -/
private lemma toRaw_eq_toRawGated_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (h : c1.name ≠ c2.name) :
    (c1.toRaw = c2.toRawGated) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  exact h (by rw [← Channel.toRaw_name c1, ← Channel.toRawGated_name c2, he])

omit [Fact (2 ^ 17 < p)] in
/-- Symmetric form of `toRaw_eq_toRawGated_false_of_name_ne`. -/
private lemma toRawGated_eq_toRaw_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (h : c1.name ≠ c2.name) :
    (c1.toRawGated = c2.toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  exact h (by rw [← Channel.toRawGated_name c1, ← Channel.toRaw_name c2, he])

omit [Fact (2 ^ 17 < p)] in
/-- Two `toRawGated`s with distinct `name`s are distinct — for mutual distinctness among the gated
State/Memory/Program emits. -/
private lemma toRawGated_eq_toRawGated_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (h : c1.name ≠ c2.name) :
    (c1.toRawGated = c2.toRawGated) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  exact h (by rw [← Channel.toRawGated_name c1, ← Channel.toRawGated_name c2, he])

-- Mixed-form distinctness involving the asymmetric raw channel (`toRawGatedAsym`), by `name` (omit the
-- `2^17` fact so they apply wherever `channelsLawful` does).
omit [Fact (2 ^ 17 < p)] in
private lemma toRaw_eq_toRawGatedAsym_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (sr2 : M2 (ZMod p) → ProverData (ZMod p) → Prop)
    (h : c1.name ≠ c2.name) : (c1.toRaw = c2.toRawGatedAsym sr2) = False := by
  simp only [eq_iff_iff, iff_false]; intro he
  exact h (by rw [← Channel.toRaw_name c1, ← Channel.toRawGatedAsym_name c2 sr2, he])
omit [Fact (2 ^ 17 < p)] in
private lemma toRawGatedAsym_eq_toRaw_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (sr1 : M1 (ZMod p) → ProverData (ZMod p) → Prop)
    (h : c1.name ≠ c2.name) : (c1.toRawGatedAsym sr1 = c2.toRaw) = False := by
  simp only [eq_iff_iff, iff_false]; intro he
  exact h (by rw [← Channel.toRawGatedAsym_name c1 sr1, ← Channel.toRaw_name c2, he])
omit [Fact (2 ^ 17 < p)] in
private lemma toRawGated_eq_toRawGatedAsym_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (sr2 : M2 (ZMod p) → ProverData (ZMod p) → Prop)
    (h : c1.name ≠ c2.name) : (c1.toRawGated = c2.toRawGatedAsym sr2) = False := by
  simp only [eq_iff_iff, iff_false]; intro he
  exact h (by rw [← Channel.toRawGated_name c1, ← Channel.toRawGatedAsym_name c2 sr2, he])
omit [Fact (2 ^ 17 < p)] in
private lemma toRawGatedAsym_eq_toRawGated_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (sr1 : M1 (ZMod p) → ProverData (ZMod p) → Prop)
    (h : c1.name ≠ c2.name) : (c1.toRawGatedAsym sr1 = c2.toRawGated) = False := by
  simp only [eq_iff_iff, iff_false]; intro he
  exact h (by rw [← Channel.toRawGatedAsym_name c1 sr1, ← Channel.toRawGated_name c2, he])

omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_stateChannelGated_false :
    ((byteChannel (p := p)).toRawGated = (stateChannel (p := p)).toRawGated) = False :=
  toRawGated_eq_toRawGated_false_of_name_ne (by simp [byteChannel, stateChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma stateChannelGated_eq_byteChannel_false :
    ((stateChannel (p := p)).toRawGated = (byteChannel (p := p)).toRawGated) = False :=
  toRawGated_eq_toRawGated_false_of_name_ne (by simp [stateChannel, byteChannel])

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma byteChannel_eq_memoryChannel_false :
    ((byteChannel (p := p)).toRawGated = (memoryChannel (p := p)).toRaw) = False :=
  toRawGated_eq_toRaw_false_of_name_ne (by simp [byteChannel, memoryChannel])
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma byteChannel_eq_programChannel_false :
    ((byteChannel (p := p)).toRawGated = (programChannel (p := p)).toRaw) = False :=
  toRawGated_eq_toRaw_false_of_name_ne (by simp [byteChannel, programChannel])
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma byteChannel_eq_stateChannel_false :
    ((byteChannel (p := p)).toRawGated = (stateChannel (p := p)).toRaw) = False :=
  toRawGated_eq_toRaw_false_of_name_ne (by simp [byteChannel, stateChannel])
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma programChannel_eq_memoryChannel_false :
    ((programChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [programChannel, memoryChannel])
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma memoryChannel_eq_programChannel_false :
    ((memoryChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [memoryChannel, programChannel])
-- Symmetric forms (the `*_eq_byteChannel_*` reverses), needed when discharging
-- `memoryChannel/programChannel ∉ RegisterAccessCols.channels = [byteChannel.toRawGated, byteChannel.toRawGated]`
-- in the P6 `interactionsWith_main_eq_nil` recovery (the byte-only reader subcircuits drop out).
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma memoryChannel_eq_byteChannel_false :
    ((memoryChannel (p := p)).toRaw = (byteChannel (p := p)).toRawGated) = False :=
  toRaw_eq_toRawGated_false_of_name_ne (by simp [memoryChannel, byteChannel])
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma programChannel_eq_byteChannel_false :
    ((programChannel (p := p)).toRaw = (byteChannel (p := p)).toRawGated) = False :=
  toRaw_eq_toRawGated_false_of_name_ne (by simp [programChannel, byteChannel])

-- These belong with Clean's `channels_lawful` default (`Clean/Circuit/Basic.lean`, which runs
-- `simp only [circuit_norm, seval]; try trivial`) — a pinned dep we don't edit — so we tag them here
-- instead. With them in `circuit_norm`, that default tactic closes every chip's channel-subset/membership
-- goal automatically, so a chip just **omits** `channelsLawful` (no hand-written override). See
-- `docs/agents/proof-patterns.md`. The mechanism: each circuit exposes its channel lists as `@[circuit_norm]`
-- rfl-lemmas right after its `elaborated` instance; `cons_subset`/`mem_cons`/`cons_ne_nil`/`not_mem_nil`/
-- `Subset.refl` then reduce the residual `⊆`/`∈` goals and `or_false`/`and_self` clean up the leftover
-- propositional skeleton (simp's built-in `rfl` closes the `chan = chan` leaves).
attribute [circuit_norm]
  List.cons_subset List.mem_cons List.cons_ne_nil List.not_mem_nil List.Subset.refl or_false and_self

end SP1Clean.Channels
