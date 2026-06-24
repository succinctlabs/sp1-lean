import SP1Clean.Model.InteractionBus
import SP1Clean.Model.Channels

/-! # Evaluating an emitted interaction to a trace-level `LookupAccess`

The **"emitted = projection"** bridge (`docs/bus-model.md` §2/§7): a circuit's emitted
`AbstractInteraction`s (expression-valued, over circuit `operations`) evaluate — through an `Environment` —
to the trace-level `LookupAccess`es that the hand-written `Soundness/*Consistency.lean` projections
(`stateLookups`/`memoryLookups`/`programLookups`/`byteLookups`) produce. This lets each `*Lookups` shadow be
shown equal to `(interactionsWith channel ops).map (toAccess env)` — the val-image of what the circuit
*actually emits* — rather than remaining a hand-authored shadow.

The one subtlety is the **signed multiplicity**: a receive's emitted multiplicity `-is_real` evaluates in
`ZMod p` to `p - is_real.val` (for `is_real = 1`, that's `p - 1`), which must map to `-1 : ℤ`. `signedVal`
takes the centered representative; `signedVal_is_real`/`signedVal_neg_is_real` pin it to `±is_real.val` for
the binary `is_real` the buses gate by. -/

namespace SP1Clean

open SP1Clean.LookupAccessList

variable {p : ℕ} [NeZero p]

/-- The `InteractionKind` of a channel, recovered from its `name` (the four buses this project models). -/
def kindOf (name : String) : InteractionKind :=
  if name = "SP1Memory" then .Memory
  else if name = "SP1Program" then .Program
  else if name = "SP1State" then .State
  else .Byte

/-- The **signed** value of a field element: its centered representative in `(-p/2, p/2]`, as `ℤ`. For the
`±is_real` multiplicities the buses use this is exactly `±is_real.val` (`signedVal_is_real`/`_neg_is_real`);
the trace-level `*Lookups` use `±(is_real.val : ℤ)`, so this is what reconciles the emitted multiplicity. -/
def signedVal (x : ZMod p) : ℤ :=
  if 2 * x.val ≤ p then (x.val : ℤ) else (x.val : ℤ) - (p : ℤ)

omit [NeZero p] in
/-- The `ZMod.val` of a binary `is_real` is `0` or `1`. -/
lemma val_of_binary (hp : 2 < p) {is_real : ZMod p} (h : is_real = 0 ∨ is_real = 1) :
    is_real.val = 0 ∨ is_real.val = 1 := by
  haveI : NeZero p := ⟨by omega⟩
  rcases h with h | h <;> subst h <;>
    simp [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]

omit [NeZero p] in
/-- For a binary `is_real`, `signedVal is_real = is_real.val` (the positive/`send` multiplicity; both
candidate values `0`/`1` satisfy `2 * val ≤ p`, so the centered representative is `val` itself). -/
lemma signedVal_is_real (hp : 2 < p) {is_real : ZMod p} (h : is_real = 0 ∨ is_real = 1) :
    signedVal is_real = (is_real.val : ℤ) := by
  rcases val_of_binary hp h with hv | hv <;> (simp only [signedVal, hv]; rw [if_pos (by omega)])

omit [NeZero p] in
/-- For a binary `is_real`, `signedVal (-is_real) = -is_real.val` (the negative/`receive` multiplicity):
`-is_real` evaluates to `p - is_real.val`, whose centered representative is `-(is_real.val)`. -/
lemma signedVal_neg_is_real (hp : 2 < p) {is_real : ZMod p} (h : is_real = 0 ∨ is_real = 1) :
    signedVal (-is_real) = -(is_real.val : ℤ) := by
  haveI : NeZero p := ⟨by omega⟩
  rcases h with h | h <;> subst h
  · simp [signedVal, ZMod.val_zero]
  · have hv : (-1 : ZMod p).val = p - 1 := by
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      subst hm; simp [ZMod.val_neg_one]
    have hv1 : (1 : ZMod p).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
    simp only [signedVal, hv, hv1]
    rw [if_neg (by omega), Nat.cast_sub (show 1 ≤ p by omega)]
    push_cast; ring

/-- `signedVal` is a **section** of the canonical projection `ℤ → ZMod p`: casting the centered
representative back recovers the element. This is what lets Clean's *field* channel balance be read as
a `mod p` statement about the native ℤ multiplicities (`GatedVm/BalanceMod.lean`). -/
lemma intCast_signedVal (x : ZMod p) : ((signedVal x : ℤ) : ZMod p) = x := by
  have hval : ((x.val : ℤ) : ZMod p) = x := by
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  unfold signedVal
  split
  · exact hval
  · rw [Int.cast_sub, hval, Int.cast_natCast, ZMod.natCast_self, sub_zero]

omit [NeZero p] in
/-- Evaluate one **evaluated** interaction (Clean's heterogeneous `Interaction F` — what an
`EnsembleWitness`'s tables carry after `AbstractInteraction.eval`) to its trace-level `LookupAccess`:
the evaluated counterpart of `AbstractInteraction.toAccess`. Bus kind from the channel `name`, the
table `name`, the message val-projected, and the centered signed multiplicity. -/
def Interaction.toAccess (i : Interaction (ZMod p)) : LookupAccess :=
  (kindOf i.channel.name, i.channel.name, i.msg.toList.map ZMod.val, signedVal i.mult)

variable [Fact p.Prime]

/-- Evaluate one emitted interaction to its trace-level `LookupAccess`: the bus kind from the channel
`name`, the table `name`, the message through `Expression.eval env` then `ZMod.val`, and the signed
multiplicity. The val-image of what the circuit emits. -/
noncomputable def AbstractInteraction.toAccess (env : Environment (ZMod p))
    (i : AbstractInteraction (ZMod p)) : LookupAccess :=
  (kindOf i.channel.name, i.channel.name,
    (i.msg.map (Expression.eval env)).toList.map ZMod.val,
    signedVal (Expression.eval env i.mult))

open SP1Clean.Channels (stateChannel StateMsg)

omit [NeZero p] in
/-- **Kernel of the State "emitted = projection".** The `toAccess`-image of a pushed `stateChannel`
message (post-#398 `circuit_norm` normal form: `pushIf`) is exactly the `stateLookups`-style
`LookupAccess`: bus `.State`, table `"SP1State"`, the five message fields val-projected, and the signed
multiplicity. This is the per-interaction computation the `stateLookups_eq_emitted` derived theorem maps
over the recovered `interactionsWith` list. -/
lemma toAccess_pushIf_state (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : StateMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pushIf (channel := stateChannel) mult msg).toRaw =
      (InteractionKind.State, "SP1State",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val],
        signedVal (Expression.eval env mult)) := by
  simp [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pushIf,
    Channel.toRaw, kindOf, stateChannel, toElements, toComponents, components,
    ProvableStruct.componentsToElements]

open SP1Clean.Channels (memoryChannel MemoryMsg programChannel ProgramMsg)

omit [NeZero p] in
/-- **Kernel of the Memory "emitted = projection".** The `toAccess`-image of a pushed `memoryChannel`
message (a plain `Channel.emit`, default `toRaw`; post-#398 `circuit_norm` normal form: `pushIf`) is the
9-field `memoryLookups`-style `LookupAccess`: bus `.Memory`, table `"SP1Memory"`, the nine fields
val-projected, and the signed multiplicity. The `toElements` unfold is done with `simp only`
(deterministic, linear) — plain `simp` over the full set blows up at `whnf` for the 9/16-field structs;
the trailing `simp` only normalizes the resulting `Vector.cast`/`++`/`map`/`toList` chain. -/
lemma toAccess_pushIf_memory (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : MemoryMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pushIf (channel := memoryChannel) mult msg).toRaw =
      (InteractionKind.Memory, "SP1Memory",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
         (Expression.eval env msg.addr2).val, (Expression.eval env msg.v0).val,
         (Expression.eval env msg.v1).val, (Expression.eval env msg.v2).val,
         (Expression.eval env msg.v3).val],
        signedVal (Expression.eval env mult)) := by
  simp only [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pushIf,
    Channel.toRaw, kindOf, memoryChannel, if_true, toElements, toComponents, components,
    ProvableStruct.componentsToElements]
  simp

omit [NeZero p] in
/-- **Kernel of the Program "emitted = projection".** The `toAccess`-image of a pushed `programChannel`
message (a plain `Channel.emit`, default `toRaw`; post-#398 `circuit_norm` normal form: `pushIf`) is the
16-field `programLookups`-style `LookupAccess`: bus `.Program`, table `"SP1Program"`, the sixteen fields
val-projected, and the signed multiplicity. -/
lemma toAccess_pushIf_program (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : ProgramMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pushIf (channel := programChannel) mult msg).toRaw =
      (InteractionKind.Program, "SP1Program",
        [(Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val, (Expression.eval env msg.opcode).val,
         (Expression.eval env msg.op_a).val, (Expression.eval env msg.op_b0).val,
         (Expression.eval env msg.op_b1).val, (Expression.eval env msg.op_b2).val,
         (Expression.eval env msg.op_b3).val, (Expression.eval env msg.op_c0).val,
         (Expression.eval env msg.op_c1).val, (Expression.eval env msg.op_c2).val,
         (Expression.eval env msg.op_c3).val, (Expression.eval env msg.op_a_0).val,
         (Expression.eval env msg.imm_b).val, (Expression.eval env msg.imm_c).val],
        signedVal (Expression.eval env mult)) := by
  simp only [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pushIf,
    Channel.toRaw, kindOf, programChannel, if_true, toElements, toComponents, components,
    ProvableStruct.componentsToElements]
  simp

open SP1Clean.Channels (byteChannel)

omit [NeZero p] in
/-- **Kernel of the Byte "received = projection".** The `toAccess`-image of a pulled `byteChannel` row
(a gated byte *pull*, multiplicity `-gate`; post-#398 `circuit_norm` normal form: `pullIf`, what
`Channel.pullIf` emits) is the `byteSend`-style `LookupAccess`: bus `.Byte`, table `"SP1Byte"`, the
four `ByteRow` fields val-projected, and the signed multiplicity `signedVal (eval env (-gate))`. The
`pullIf`/`byteChannel`/`ByteRow` analog of `toAccess_pushIf_state`. -/
lemma toAccess_pullIf_byte (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : ByteRow (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pullIf (channel := byteChannel) gate msg).toRaw =
      (InteractionKind.Byte, "SP1Byte",
        [(Expression.eval env msg.opcode).val, (Expression.eval env msg.a).val,
         (Expression.eval env msg.b).val, (Expression.eval env msg.c).val],
        signedVal (Expression.eval env (-gate))) := by
  simp [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pullIf, Channel.toRaw, kindOf,
    byteChannel, toElements, toComponents, components, ProvableStruct.componentsToElements]

end SP1Clean
