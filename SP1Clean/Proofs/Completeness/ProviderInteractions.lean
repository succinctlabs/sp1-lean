import SP1Clean.Model.CleanLedger
import SP1Clean.Proofs.Completeness.Ledger

/-! # What one built provider row actually emits

`Model/InteractionBus.lean`'s closure proves that appending "one recounted access per demanded key"
to a consumer skeleton zeroes every selected key. To turn that into a statement about the trace's
*actual* provider tables, each provider needs a closed form: **a built row emits exactly one access,
and here it is**.

That is the hypothesis shape of `tableCleanAccesses_build_map_singleton`
(`Model/CleanLedger.lean`), which is why these are stated as

```
component.operations.interactions.map (AbstractInteraction.toAccess env) = [access]
```

## Clean orientation, deliberately

The exact→native transport proves the same facts through `Faithful.nativeAccesses`, which splits by
channel and **dualizes Memory and Program** (`negMult`) to match the Rust AIR's send/receive
convention. None of that is wanted here: the completeness side compares against Clean's own ledger,
so the dualization would be a round trip that cancels itself, and routing through it would drag a
`Faithful` dependency into the completeness layer for nothing. Stating these over
`Operations.interactions` directly is both shorter and closer to what the caller needs.

## The route

Clean supplies the hard step. `Component.operations` and `rowOperations` differ only in how the input
variables are introduced, and `Air.Flat.Component.interactions_eq` says their interaction lists are
equal outright. From there a provider that names a single channel has
`interactions = interactionsWith channel`, and the per-provider symbolic lemma evaluates that to one
access. `Ledger.OnlyChannel` and its ten instances (`Proofs/Completeness/Ledger.lean:245-327`) supply
the single-channel premise; they already existed for the balance argument.
-/

namespace SP1Clean.Soundness

open Air.Flat (Component)
open SP1Clean.Channels (byteChannel programChannel)

-- `Fact (2 ^ 24 < p)` matches `Proofs/Completeness/Providers.lean`, where the provider
-- `Component` wrappers live; it also supplies the `2 ^ 17 < p` the byte circuits need.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- A component that names one channel emits all of its interactions on that channel, so the
unfiltered list and the channel-filtered one coincide. This is what lets the per-provider closed
forms below be stated over `Operations.interactions` — the form
`tableCleanAccesses_build_map_singleton` consumes — while being *proved* through the channel-indexed
symbolic lemmas, which is the only form the circuit's own `simp` set produces. -/
theorem interactions_eq_interactionsWith_of_onlyChannel
    (c : Component (ZMod p)) (channel : RawChannel (ZMod p))
    (only : Ledger.OnlyChannel c channel) :
    c.operations.interactions = c.operations.interactionsWith channel := by
  rw [Component.interactionsWith_eq, Component.interactions_eq]
  unfold Operations.interactionsWith
  symm
  apply List.filter_eq_self.mpr
  intro interaction interactionMem
  simp only [decide_eq_true_eq]
  have channelMem : interaction.channel ∈
      ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).channels :=
    List.mem_map.mpr ⟨interaction, interactionMem, rfl⟩
  exact only interaction.channel
    (c.circuit.channels_subset (varFromOffset c.Input 0) (size c.Input) channelMem)

/-! ## Gadget-skipping

The byte providers all range-check their operands in-circuit before pushing. `rangeCheck` and
`assertBool` are assertion subcircuits — they name no channel — so they contribute nothing to any
channel's interaction list and can be stepped over without unfolding a bit decomposition. -/

omit [Fact (2 ^ 24 < p)] in
theorem rangeCheck_interactionsWith (n : ℕ) (hn : 2 ^ n < p)
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Expression (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit ((Gadgets.ToBits.rangeCheck n hn).toSubcircuit
          offset input) :: ops) = Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

theorem rangeCheck8_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Expression (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit ((Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).toSubcircuit
          offset input) :: ops) = Operations.interactionsWith channel ops :=
  rangeCheck_interactionsWith 8 ByteChip.two_pow_eight_lt channel offset input ops

/-! ## U8Range -/

/-- The symbolic Byte-channel list of the `U8Range` provider: one push of `⟨3, 0, b, c⟩` gated by the
row's explicit multiplicity, with the two `rangeCheck 8` assertions stepped over. -/
theorem u8Range_interactionsWith_byte :
    (ByteChip.U8Range.component (p := p)).operations.interactionsWith byteChannel.toRaw =
      [(pushedIf (channel := byteChannel) (var ⟨2⟩)
        (⟨3, 0, var ⟨0⟩, var ⟨1⟩⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations (⟨ByteChip.U8Range.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk]
  rw [show (ByteChip.U8Range.circuit (p := p)).main = ByteChip.U8Range.main from rfl]
  simp only [ByteChip.U8Range.main, Circuit.operations, Circuit.bind_def,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append,
    rangeCheck8_interactionsWith, Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append]
  simp only [if_true]
  rfl

/-- **A built `U8Range` row emits exactly one access, and this is it.**

The Tier-1 shape: exactly the `rowAccess` hypothesis of `tableCleanAccesses_build_map_singleton`,
so a whole provider table's ledger follows from this by one application. The key is the row's own
`(3, 0, b, c)` and the multiplicity is the row's explicit input column — which is what makes
zero-multiplicity padding and aggregated counts reachable through the builder at all. -/
theorem u8Range_buildRow_cleanAccesses
    (input : ByteChip.U8Range.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (ByteChip.U8Range.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ByteChip.U8Range.component (p := p)).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(3 : ZMod p).val, (0 : ZMod p).val, input.b.val, input.c.val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_U8Range, u8Range_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega)]
  -- `rw` cannot close the cells here: the goal's `input` is at `component.Input`, the lemmas' at
  -- `Inputs`, and the two are only definitionally equal. Destructuring settles it directly.
  cases input
  rfl

end SP1Clean.Soundness
