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
    signedVal (- is_real) = -(is_real.val : ℤ) := by
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

omit [NeZero p] in
/-- **`signedVal` is odd** for an odd prime `p`: `signedVal (-x) = -signedVal x` for *every* `x`
(no binarity needed). The centered representative of `-x` is the negation of that of `x`, because
`2 * x.val = p` is impossible for odd `p`. This is the general sign-symmetry behind the W11 program-bus
LogUp polarity flip (the faithfulness anchors carry `is_real`/`is_trusted` as free field elements, so the
binary `signedVal_neg_is_real` does not apply). -/
lemma signedVal_neg [Fact p.Prime] (hp : 2 < p) (x : ZMod p) :
    signedVal (-x) = -signedVal x := by
  haveI : NeZero p := ⟨by omega⟩
  have hpp : p.Prime := Fact.out
  have hodd : ¬ (2 ∣ p) := fun h2 => by
    rcases hpp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp [signedVal, ZMod.val_zero]
  · have hxlt : x.val < p := ZMod.val_lt x
    have hxpos : 0 < x.val := by rw [ZMod.val_pos]; exact hx
    haveI : NeZero x := ⟨hx⟩
    have hvneg : (-x).val = p - x.val := ZMod.val_neg_of_ne_zero x
    have hne : 2 * x.val ≠ p := fun he => hodd ⟨x.val, he.symm⟩
    unfold signedVal
    rw [hvneg]
    by_cases h : 2 * x.val ≤ p
    · have h' : 2 * x.val < p := lt_of_le_of_ne h hne
      rw [if_pos h, if_neg (by omega), Nat.cast_sub (by omega)]; ring
    · rw [if_neg h, if_pos (by omega), Nat.cast_sub (by omega)]; ring

/-- `signedVal` is a **section** of the canonical projection `ℤ → ZMod p`: casting the centered
representative back recovers the element. This is what lets Clean's *field* channel balance be read as
a `mod p` statement about the native ℤ multiplicities (`Model/BalanceBridge.lean`). -/
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
    AbstractInteraction.toAccess env (stateChannel.pushedIf mult msg).toRaw =
      (InteractionKind.State, "SP1State",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val],
        signedVal (Expression.eval env mult)) := by
  simp [AbstractInteraction.toAccess, VmChannelInteraction.toRaw, VmChannel.pushedIf,
    VmChannel.toRaw, kindOf, stateChannel, toElements, toComponents, components,
    ProvableStruct.componentsToElements]

omit [NeZero p] in
/-- **Kernel of the State "received = projection" (gated VM pull).** The `pullIf`/`stateChannel`/`StateMsg`
analog of `toAccess_pushIf_state` — the W11 form, after `CPUState` switched its `receive_state` from
`emit (-is_real)` to `Channel.pullIf is_real` (so each chip can `expose` the `[pulledIf, pushedIf]` pair for
Clean's `VmTables`). Its signed multiplicity is `signedVal (eval env (-gate))`; `toAccess` ignores
`assumeGuarantees`, so the projected `LookupAccess` is identical to the old `pushIf (-is_real)` form. -/
lemma toAccess_pullIf_state (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : StateMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (stateChannel.pulledIf gate msg).toRaw =
      (InteractionKind.State, "SP1State",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val],
        signedVal (Expression.eval env (-gate))) := by
  simp [AbstractInteraction.toAccess, VmChannelInteraction.toRaw, VmChannel.pulledIf,
    VmChannel.toRaw, kindOf, stateChannel, toElements, toComponents, components,
    ProvableStruct.componentsToElements]

open SP1Clean.Channels (memoryChannel MemoryMsg programChannel ProgramMsg)

/-- Expand a 4-vector's `toList` into its four elements — the `Word`-field analog of the flat scalar
components in the `toElements` unfolds below (the `MemoryMsg.value` word flattens through `toElements`
as a `Vector`, not four scalars). -/
private lemma toList_word {α : Type} (w : Vector α 4) :
    w.toList = [w[0], w[1], w[2], w[3]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases i <;> simp

omit [NeZero p] in
/-- **Kernel of the Memory "emitted = projection".** The `toAccess`-image of a pushed `memoryChannel`
message (a plain `Channel.emit`, default `toRaw`; post-#398 `circuit_norm` normal form: `pushIf`) is the
9-field `memoryLookups`-style `LookupAccess`: bus `.Memory`, table `"SP1Memory"`, the nine fields
val-projected, and the signed multiplicity. The `toElements` unfold is done with `simp only`
(deterministic, linear) — plain `simp` over the full set blows up at `whnf` for the 9/16-field structs;
the trailing `simp` only normalizes the resulting `Vector.cast`/`++`/`map`/`toList` chain. -/
lemma toAccess_pushIf_memory (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : MemoryMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pushedIf (channel :=memoryChannel) mult msg).toRaw =
      (InteractionKind.Memory, "SP1Memory",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
         (Expression.eval env msg.addr2).val, (Expression.eval env msg.value[0]).val,
         (Expression.eval env msg.value[1]).val, (Expression.eval env msg.value[2]).val,
         (Expression.eval env msg.value[3]).val],
        signedVal (Expression.eval env mult)) := by
  simp only [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pushedIf,
    Channel.toRaw, kindOf, memoryChannel, if_true, toElements, toComponents, components,
    ProvableStruct.componentsToElements]
  simp [Vector.toList_append, toList_word]

omit [NeZero p] in
/-- **Kernel of the Memory "received = projection" (gated VM pull).** The `pullIf`/`memoryChannel`/`MemoryMsg`
analog of `toAccess_pushIf_memory` — the W11 polarity-flip form, after the readers switched a memory
*read-prior* `emit +is_real` (send) to `Channel.pullIf is_real` (the writer/provider now pushes & proves
`MemoryMsg.isU64`; chips pull & derive it). Its signed multiplicity is `signedVal (eval env (-gate))`;
`toAccess` ignores the channel `Guarantees`, so the projected `LookupAccess` is identical to the old
`pushIf is_real` form modulo the sign. -/
lemma toAccess_pullIf_memory (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : MemoryMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pulledIf (channel := memoryChannel) gate msg).toRaw =
      (InteractionKind.Memory, "SP1Memory",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
         (Expression.eval env msg.addr2).val, (Expression.eval env msg.value[0]).val,
         (Expression.eval env msg.value[1]).val, (Expression.eval env msg.value[2]).val,
         (Expression.eval env msg.value[3]).val],
        signedVal (Expression.eval env (-gate))) := by
  simp only [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pulledIf,
    Channel.toRaw, kindOf, memoryChannel, if_true, toElements, toComponents, components,
    ProvableStruct.componentsToElements]
  simp [Vector.toList_append, toList_word]

omit [NeZero p] in
/-- **Kernel of the Program "emitted = projection".** The `toAccess`-image of a pushed `programChannel`
message (a plain `Channel.emit`, default `toRaw`; post-#398 `circuit_norm` normal form: `pushIf`) is the
16-field `programLookups`-style `LookupAccess`: bus `.Program`, table `"SP1Program"`, the sixteen fields
val-projected, and the signed multiplicity. -/
lemma toAccess_pushIf_program (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : ProgramMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (programChannel.pushedIf mult msg).toRaw =
      (InteractionKind.Program, "SP1Program",
        [(Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val, (Expression.eval env msg.opcode).val,
         (Expression.eval env msg.op_a).val, (Expression.eval env msg.op_b[0]).val,
         (Expression.eval env msg.op_b[1]).val, (Expression.eval env msg.op_b[2]).val,
         (Expression.eval env msg.op_b[3]).val, (Expression.eval env msg.op_c[0]).val,
         (Expression.eval env msg.op_c[1]).val, (Expression.eval env msg.op_c[2]).val,
         (Expression.eval env msg.op_c[3]).val, (Expression.eval env msg.op_a_0).val,
         (Expression.eval env msg.imm_b).val, (Expression.eval env msg.imm_c).val],
        signedVal (Expression.eval env mult)) := by
  simp only [AbstractInteraction.toAccess, VmChannelInteraction.toRaw, VmChannel.pushedIf,
    VmChannel.toRaw, kindOf, programChannel, if_true, toElements, toComponents, components,
    ProvableStruct.componentsToElements]
  -- Two `Word` fields (`op_b`/`op_c`) followed by trailing scalars: the op_c append doesn't split under
  -- plain `simp` (a `toList` normal-form loop), so force the split with an explicit `rw` (op_b reduces on
  -- its own). Cf. the memory kernels, where `value` is the last field and `toList_word` alone suffices.
  simp [Vector.toList_append, toList_word]; rw [Vector.toList_append]; simp [toList_word]

omit [NeZero p] in
/-- **Kernel of the Program "received = projection" (gated VM pull).** The `pullIf`/`programChannel`/
`ProgramMsg` analog of `toAccess_pushIf_program` — the W11 polarity-flip form, after the CPU readers switched
their `programChannel.emit +is_trusted` (send) to `Channel.pullIf is_trusted` (the ROM provider now pushes and
proves `ProgramMsg.RowSpec`; chips pull and derive). Its signed multiplicity is `signedVal (eval env (-gate))`;
`toAccess` ignores the channel `Guarantees`, so the projected `LookupAccess` is identical to the old
`pushIf is_trusted` form modulo the sign. -/
lemma toAccess_pullIf_program (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : ProgramMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (programChannel.pulledIf gate msg).toRaw =
      (InteractionKind.Program, "SP1Program",
        [(Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val, (Expression.eval env msg.opcode).val,
         (Expression.eval env msg.op_a).val, (Expression.eval env msg.op_b[0]).val,
         (Expression.eval env msg.op_b[1]).val, (Expression.eval env msg.op_b[2]).val,
         (Expression.eval env msg.op_b[3]).val, (Expression.eval env msg.op_c[0]).val,
         (Expression.eval env msg.op_c[1]).val, (Expression.eval env msg.op_c[2]).val,
         (Expression.eval env msg.op_c[3]).val, (Expression.eval env msg.op_a_0).val,
         (Expression.eval env msg.imm_b).val, (Expression.eval env msg.imm_c).val],
        signedVal (Expression.eval env (-gate))) := by
  simp only [AbstractInteraction.toAccess, VmChannelInteraction.toRaw, VmChannel.pulledIf,
    VmChannel.toRaw, kindOf, programChannel, if_true, toElements, toComponents, components,
    ProvableStruct.componentsToElements]
  -- See the push kernel: force the op_c append split with an explicit `rw` (the `Word`-plus-trailing-scalars
  -- shape that plain `simp`'s `toList` normalization won't split).
  simp [Vector.toList_append, toList_word]; rw [Vector.toList_append]; simp [toList_word]

open SP1Clean.Channels (byteChannel)

omit [NeZero p] in
/-- **Kernel of the Byte "received = projection".** The `toAccess`-image of a pulled `byteChannel` row
(a gated byte *pull*, multiplicity `-gate`; post-#398 `circuit_norm` normal form: `pullIf`, what
`Channel.pullIf` emits) is the `byteSend`-style `LookupAccess`: bus `.Byte`, table `"SP1Byte"`, the
four `ByteRow` fields val-projected, and the signed multiplicity `signedVal (eval env (-gate))`. The
`pullIf`/`byteChannel`/`ByteRow` analog of `toAccess_pushIf_state`. -/
lemma toAccess_pullIf_byte (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : ByteRow (Expression (ZMod p))) :
    AbstractInteraction.toAccess env (pulledIf (channel :=byteChannel) gate msg).toRaw =
      (InteractionKind.Byte, "SP1Byte",
        [(Expression.eval env msg.opcode).val, (Expression.eval env msg.a).val,
         (Expression.eval env msg.b).val, (Expression.eval env msg.c).val],
        signedVal (Expression.eval env (-gate))) := by
  simp [AbstractInteraction.toAccess, ChannelInteraction.toRaw, pulledIf, Channel.toRaw, kindOf,
    byteChannel, toElements, toComponents, components, ProvableStruct.componentsToElements]

end SP1Clean
