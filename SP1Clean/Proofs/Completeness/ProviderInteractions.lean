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

omit [Fact (2 ^ 24 < p)] in
theorem assertBool_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Expression (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (assertBool.toSubcircuit offset input) :: ops) =
      Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

/-! ## MSB

The first family with a *derived* output cell: the pushed row's `a` field is the high bit, which the
circuit witnesses rather than reading from the input. That cell is recovered from the circuit's own
`Spec` through `buildRow_spec_requirements`, which is why this family (and And/Or/Xor/Ltu below)
carries a byte-bound premise where `U8Range` and `Range` do not. -/

/-- Row-level symbolic Byte list for `MSB`. -/
theorem msb_interactionsWith_byte
    (input : Var ByteChip.MSB.Inputs (ZMod p)) (offset : ℕ) :
    ((ByteChip.MSB.main input).operations offset).interactionsWith byteChannel.toRaw =
      [(pushedIf (channel := byteChannel) input.multiplicity
        (⟨5,
          var ⟨offset +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b⟩,
          input.b, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.MSB.main, Circuit.operations, Circuit.bind_def, witnessField,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
    rangeCheck8_interactionsWith, assertBool_interactionsWith,
    Channel.pushIf, Operations.interactionsWith_interact, Operations.interactionsWith_nil,
    ChannelInteraction.toRaw_channel, List.nil_append]
  simp only [if_true, circuit_norm, Nat.add_zero]

theorem msb_main_output_eq
    (input : Var ByteChip.MSB.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.MSB.main input).output offset =
      var ⟨offset +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b⟩ := rfl

/-- The witnessed high-bit cell of a built `MSB` row, recovered from the circuit's own `Spec`. -/
theorem msb_buildRow_result
    (input : ByteChip.MSB.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bound : input.b.val < 2 ^ 8) :
    Expression.eval
      (Environment.fromArray
        ((⟨ByteChip.MSB.circuit⟩ : Component (ZMod p)).buildRow input data hint) data)
      (var ⟨size ByteChip.MSB.Inputs +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
          (varFromOffset ByteChip.MSB.Inputs 0 : Var ByteChip.MSB.Inputs (ZMod p)).b⟩) =
      if 128 ≤ input.b.val then 1 else 0 := by
  let component := (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.MSB.computableWitnesses bound (by trivial)).1
  have hinput : component.rowInput env = input :=
    component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : Expression.eval env
      ((ByteChip.MSB.circuit (p := p)).output
        (varFromOffset ByteChip.MSB.Inputs 0) (size ByteChip.MSB.Inputs)) =
      if 128 ≤ input.b.val then 1 else 0 := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← msb_main_output_eq]
  rw [← show (ByteChip.MSB.circuit (p := p)).main = ByteChip.MSB.main from rfl]
  rw [(ByteChip.MSB.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The `MSB` input variable's fields, by cell. -/
theorem msbVar_b :
    (varFromOffset ByteChip.MSB.Inputs 0 : Var ByteChip.MSB.Inputs (ZMod p)).b = var ⟨0⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem msbVar_multiplicity :
    (varFromOffset ByteChip.MSB.Inputs 0 : Var ByteChip.MSB.Inputs (ZMod p)).multiplicity
      = var ⟨1⟩ := rfl

/-- Component-level form of `msb_interactionsWith_byte`, at the offset `Component.rowOperations`
introduces. -/
theorem msb_component_interactionsWith_byte :
    (ByteChip.MSB.component (p := p)).operations.interactionsWith byteChannel.toRaw =
      [(pushedIf (channel := byteChannel)
          (varFromOffset ByteChip.MSB.Inputs 0 : Var ByteChip.MSB.Inputs (ZMod p)).multiplicity
        (⟨5,
          var ⟨size ByteChip.MSB.Inputs +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
              (varFromOffset ByteChip.MSB.Inputs 0 : Var ByteChip.MSB.Inputs (ZMod p)).b⟩,
          (varFromOffset ByteChip.MSB.Inputs 0 : Var ByteChip.MSB.Inputs (ZMod p)).b,
          0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations (⟨ByteChip.MSB.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (ByteChip.MSB.circuit (p := p)).main = ByteChip.MSB.main from rfl]
  exact msb_interactionsWith_byte _ _

/-- **A built `MSB` row emits exactly one access.** -/
theorem msb_buildRow_cleanAccesses
    (input : ByteChip.MSB.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (bound : input.b.val < 2 ^ 8) :
    (ByteChip.MSB.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ByteChip.MSB.component (p := p)).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(5 : ZMod p).val, (if 128 ≤ input.b.val then (1 : ZMod p) else 0).val,
         input.b.val, (0 : ZMod p).val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_MSB, msb_component_interactionsWith_byte]
  show (List.map _ _ : LookupAccessList) = _
  unfold ByteChip.MSB.component
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [msb_buildRow_result input data hint bound, msbVar_b, msbVar_multiplicity,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 2; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 2; omega)]
  cases input
  simp only [Expression.eval]
  rfl

/-! ## AndByte

MSB's shape with two operands: the pushed row's `a` field is the `And8` gadget's output, recovered
from the circuit's `Spec`, and the premise is a bound on both bytes. Or/Xor/Ltu differ only in the
gadget and the operation. -/

theorem and8_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Var Gadgets.And.And8.Inputs (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (Gadgets.And.And8.circuit.toSubcircuit offset input) :: ops) =
      Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

theorem and_interactionsWith_byte
    (input : Var ByteChip.AndByte.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith byteChannel.toRaw
      ((ByteChip.AndByte.main input).operations offset) =
      [(pushedIf (channel := byteChannel) input.multiplicity
        (⟨0,
          Gadgets.And.And8.circuit.output { x := input.b, y := input.c }
            (offset +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c),
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.AndByte.main, Circuit.operations, Circuit.bind_def,
    subcircuit, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    and8_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

theorem and_main_output_eq
    (input : Var ByteChip.AndByte.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.AndByte.main input).output offset =
      Gadgets.And.And8.circuit.output { x := input.b, y := input.c }
        (offset +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c) := rfl

/-- The witnessed AND cell of a built `AndByte` row. -/
theorem and_buildRow_result_val
    (input : ByteChip.AndByte.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (Expression.eval
      (Environment.fromArray
        ((⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p)).buildRow input data hint) data)
      (Gadgets.And.And8.circuit.output
        { x := (varFromOffset ByteChip.AndByte.Inputs 0 :
                  Var ByteChip.AndByte.Inputs (ZMod p)).b,
          y := (varFromOffset ByteChip.AndByte.Inputs 0 :
                  Var ByteChip.AndByte.Inputs (ZMod p)).c }
        (size ByteChip.AndByte.Inputs +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
            (varFromOffset ByteChip.AndByte.Inputs 0 :
              Var ByteChip.AndByte.Inputs (ZMod p)).b +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
            (varFromOffset ByteChip.AndByte.Inputs 0 :
              Var ByteChip.AndByte.Inputs (ZMod p)).c))).val =
      input.b.val &&& input.c.val := by
  let component := (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.AndByte.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input :=
    component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : (Expression.eval env
      ((ByteChip.AndByte.circuit (p := p)).output
        (varFromOffset ByteChip.AndByte.Inputs 0) (size ByteChip.AndByte.Inputs))).val =
      input.b.val &&& input.c.val := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← and_main_output_eq]
  rw [← show (ByteChip.AndByte.circuit (p := p)).main = ByteChip.AndByte.main from rfl]
  rw [(ByteChip.AndByte.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem andVar_b :
    (varFromOffset ByteChip.AndByte.Inputs 0 : Var ByteChip.AndByte.Inputs (ZMod p)).b
      = var ⟨0⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem andVar_c :
    (varFromOffset ByteChip.AndByte.Inputs 0 : Var ByteChip.AndByte.Inputs (ZMod p)).c
      = var ⟨1⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem andVar_multiplicity :
    (varFromOffset ByteChip.AndByte.Inputs 0 : Var ByteChip.AndByte.Inputs (ZMod p)).multiplicity
      = var ⟨2⟩ := rfl

theorem and_component_interactionsWith_byte :
    (ByteChip.AndByte.component (p := p)).operations.interactionsWith byteChannel.toRaw =
      Operations.interactionsWith byteChannel.toRaw
        ((ByteChip.AndByte.main
          (varFromOffset ByteChip.AndByte.Inputs 0)).operations
            (size ByteChip.AndByte.Inputs)) := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations
        (⟨ByteChip.AndByte.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (ByteChip.AndByte.circuit (p := p)).main = ByteChip.AndByte.main from rfl]

/-- **A built `AndByte` row emits exactly one access.** -/
theorem and_buildRow_cleanAccesses
    (input : ByteChip.AndByte.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (ByteChip.AndByte.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ByteChip.AndByte.component (p := p)).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(0 : ZMod p).val, input.b.val &&& input.c.val, input.b.val, input.c.val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_AndByte, and_component_interactionsWith_byte,
    and_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  unfold ByteChip.AndByte.component
  rw [and_buildRow_result_val input data hint bounds, andVar_b, andVar_c, andVar_multiplicity,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega)]
  cases input
  simp only [Expression.eval]
  rfl

/-! ## OrByte — AndByte's shape with the `Or8` gadget -/

theorem or8_interactionsWith
    (channel : RawChannel (ZMod p)) (offset : ℕ)
    (input : Var Gadgets.Or.Or8.Inputs (ZMod p)) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (Gadgets.Or.Or8.circuit.toSubcircuit offset input) :: ops) =
      Operations.interactionsWith channel ops := by
  apply InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil
  · change channel ∉ ([] : List (RawChannel (ZMod p)))
    exact List.not_mem_nil

theorem or_interactionsWith_byte
    (input : Var ByteChip.OrByte.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith byteChannel.toRaw
      ((ByteChip.OrByte.main input).operations offset) =
      [(pushedIf (channel := byteChannel) input.multiplicity
        (⟨1,
          Gadgets.Or.Or8.circuit.output { x := input.b, y := input.c }
            (offset +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
              (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c),
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.OrByte.main, Circuit.operations, Circuit.bind_def,
    subcircuit, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    or8_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

theorem or_main_output_eq
    (input : Var ByteChip.OrByte.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.OrByte.main input).output offset =
      Gadgets.Or.Or8.circuit.output { x := input.b, y := input.c }
        (offset +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c) := rfl

theorem or_buildRow_result_val
    (input : ByteChip.OrByte.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (Expression.eval
      (Environment.fromArray
        ((⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p)).buildRow input data hint) data)
      (Gadgets.Or.Or8.circuit.output
        { x := (varFromOffset ByteChip.OrByte.Inputs 0 :
                  Var ByteChip.OrByte.Inputs (ZMod p)).b,
          y := (varFromOffset ByteChip.OrByte.Inputs 0 :
                  Var ByteChip.OrByte.Inputs (ZMod p)).c }
        (size ByteChip.OrByte.Inputs +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
            (varFromOffset ByteChip.OrByte.Inputs 0 : Var ByteChip.OrByte.Inputs (ZMod p)).b +
          (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
            (varFromOffset ByteChip.OrByte.Inputs 0 :
              Var ByteChip.OrByte.Inputs (ZMod p)).c))).val =
      input.b.val ||| input.c.val := by
  let component := (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.OrByte.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input :=
    component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : (Expression.eval env
      ((ByteChip.OrByte.circuit (p := p)).output
        (varFromOffset ByteChip.OrByte.Inputs 0) (size ByteChip.OrByte.Inputs))).val =
      input.b.val ||| input.c.val := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← or_main_output_eq]
  rw [← show (ByteChip.OrByte.circuit (p := p)).main = ByteChip.OrByte.main from rfl]
  rw [(ByteChip.OrByte.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem orVar_b :
    (varFromOffset ByteChip.OrByte.Inputs 0 : Var ByteChip.OrByte.Inputs (ZMod p)).b
      = var ⟨0⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem orVar_c :
    (varFromOffset ByteChip.OrByte.Inputs 0 : Var ByteChip.OrByte.Inputs (ZMod p)).c
      = var ⟨1⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem orVar_multiplicity :
    (varFromOffset ByteChip.OrByte.Inputs 0 : Var ByteChip.OrByte.Inputs (ZMod p)).multiplicity
      = var ⟨2⟩ := rfl

theorem or_component_interactionsWith_byte :
    (ByteChip.OrByte.component (p := p)).operations.interactionsWith byteChannel.toRaw =
      Operations.interactionsWith byteChannel.toRaw
        ((ByteChip.OrByte.main
          (varFromOffset ByteChip.OrByte.Inputs 0)).operations
            (size ByteChip.OrByte.Inputs)) := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations
        (⟨ByteChip.OrByte.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (ByteChip.OrByte.circuit (p := p)).main = ByteChip.OrByte.main from rfl]

/-- **A built `OrByte` row emits exactly one access.** -/
theorem or_buildRow_cleanAccesses
    (input : ByteChip.OrByte.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (ByteChip.OrByte.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ByteChip.OrByte.component (p := p)).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(1 : ZMod p).val, input.b.val ||| input.c.val, input.b.val, input.c.val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_OrByte, or_component_interactionsWith_byte,
    or_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  unfold ByteChip.OrByte.component
  rw [or_buildRow_result_val input data hint bounds, orVar_b, orVar_c, orVar_multiplicity,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega)]
  cases input
  simp only [Expression.eval]
  rfl

/-! ## XorByte — MSB's witnessed-cell shape, with two operands -/

theorem xor_interactionsWith_byte
    (input : Var ByteChip.XorByte.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith byteChannel.toRaw
      ((ByteChip.XorByte.main input).operations offset) =
      [(pushedIf (channel := byteChannel) input.multiplicity
        (⟨2,
          var ⟨offset +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩,
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.XorByte.main, Circuit.operations, Circuit.bind_def,
    witnessField, lookup, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    Operations.interactionsWith_witness, Operations.interactionsWith_lookup]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

theorem xor_main_output_eq
    (input : Var ByteChip.XorByte.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.XorByte.main input).output offset =
      var ⟨offset +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩ := rfl

theorem xor_buildRow_result
    (input : ByteChip.XorByte.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    ((Expression.eval
      (Environment.fromArray
        ((⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p)).buildRow input data hint) data)
      (var ⟨size ByteChip.XorByte.Inputs +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
          (varFromOffset ByteChip.XorByte.Inputs 0 : Var ByteChip.XorByte.Inputs (ZMod p)).b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
          (varFromOffset ByteChip.XorByte.Inputs 0 :
            Var ByteChip.XorByte.Inputs (ZMod p)).c⟩))).val =
      input.b.val ^^^ input.c.val := by
  let component := (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.XorByte.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input :=
    component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : ((Expression.eval env
      ((ByteChip.XorByte.circuit (p := p)).output
        (varFromOffset ByteChip.XorByte.Inputs 0) (size ByteChip.XorByte.Inputs)))).val =
      input.b.val ^^^ input.c.val := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← xor_main_output_eq]
  rw [← show (ByteChip.XorByte.circuit (p := p)).main = ByteChip.XorByte.main from rfl]
  rw [(ByteChip.XorByte.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem xorVar_b :
    (varFromOffset ByteChip.XorByte.Inputs 0 : Var ByteChip.XorByte.Inputs (ZMod p)).b
      = var ⟨0⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem xorVar_c :
    (varFromOffset ByteChip.XorByte.Inputs 0 : Var ByteChip.XorByte.Inputs (ZMod p)).c
      = var ⟨1⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem xorVar_multiplicity :
    (varFromOffset ByteChip.XorByte.Inputs 0 : Var ByteChip.XorByte.Inputs (ZMod p)).multiplicity
      = var ⟨2⟩ := rfl

theorem xor_component_interactionsWith_byte :
    (ByteChip.XorByte.component (p := p)).operations.interactionsWith byteChannel.toRaw =
      Operations.interactionsWith byteChannel.toRaw
        ((ByteChip.XorByte.main
          (varFromOffset ByteChip.XorByte.Inputs 0)).operations
            (size ByteChip.XorByte.Inputs)) := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations
        (⟨ByteChip.XorByte.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (ByteChip.XorByte.circuit (p := p)).main = ByteChip.XorByte.main from rfl]

/-- **A built `XorByte` row emits exactly one access.** -/
theorem xor_buildRow_cleanAccesses
    (input : ByteChip.XorByte.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (ByteChip.XorByte.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ByteChip.XorByte.component (p := p)).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(2 : ZMod p).val, input.b.val ^^^ input.c.val, input.b.val, input.c.val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_XorByte, xor_component_interactionsWith_byte,
    xor_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  unfold ByteChip.XorByte.component
  rw [xor_buildRow_result input data hint bounds, xorVar_b, xorVar_c, xorVar_multiplicity,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega)]
  cases input
  simp only [Expression.eval]
  rfl

/-! ## Ltu — MSB's witnessed-cell shape, with two operands -/

theorem ltu_interactionsWith_byte
    (input : Var ByteChip.Ltu.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith byteChannel.toRaw
      ((ByteChip.Ltu.main input).operations offset) =
      [(pushedIf (channel := byteChannel) input.multiplicity
        (⟨4,
          var ⟨offset +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
            (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩,
          input.b, input.c⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [ByteChip.Ltu.main, Circuit.operations, Circuit.bind_def,
    witnessField, assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck8_interactionsWith,
    Operations.interactionsWith_witness, assertBool_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm, Nat.add_zero]

theorem ltu_main_output_eq
    (input : Var ByteChip.Ltu.Inputs (ZMod p)) (offset : ℕ) :
    (ByteChip.Ltu.main input).output offset =
      var ⟨offset +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength input.c⟩ := rfl

theorem ltu_buildRow_result
    (input : ByteChip.Ltu.Inputs (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (Expression.eval
      (Environment.fromArray
        ((⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p)).buildRow input data hint) data)
      (var ⟨size ByteChip.Ltu.Inputs +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
          (varFromOffset ByteChip.Ltu.Inputs 0 : Var ByteChip.Ltu.Inputs (ZMod p)).b +
        (Gadgets.ToBits.rangeCheck 8 ByteChip.two_pow_eight_lt).localLength
          (varFromOffset ByteChip.Ltu.Inputs 0 :
            Var ByteChip.Ltu.Inputs (ZMod p)).c⟩)) =
      if input.b.val < input.c.val then 1 else 0 := by
  let component := (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray (component.buildRow input data hint) data
  have hspec := (component.buildRow_spec_requirements input data hint
    ByteChip.Ltu.computableWitnesses bounds (by trivial)).1
  have hinput : component.rowInput env = input :=
    component.rowInput_buildRow input data data hint
  simp only [Air.Flat.Component.Spec] at hspec
  rw [hinput] at hspec
  have hresult : (Expression.eval env
      ((ByteChip.Ltu.circuit (p := p)).output
        (varFromOffset ByteChip.Ltu.Inputs 0) (size ByteChip.Ltu.Inputs))) =
      if input.b.val < input.c.val then 1 else 0 := by
    simpa only [component, Air.Flat.Component.rowOutput, circuit_norm] using hspec.2
  rw [← ltu_main_output_eq]
  rw [← show (ByteChip.Ltu.circuit (p := p)).main = ByteChip.Ltu.main from rfl]
  rw [(ByteChip.Ltu.circuit (p := p)).elaborated.output_eq]
  exact hresult

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem ltuVar_b :
    (varFromOffset ByteChip.Ltu.Inputs 0 : Var ByteChip.Ltu.Inputs (ZMod p)).b
      = var ⟨0⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem ltuVar_c :
    (varFromOffset ByteChip.Ltu.Inputs 0 : Var ByteChip.Ltu.Inputs (ZMod p)).c
      = var ⟨1⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem ltuVar_multiplicity :
    (varFromOffset ByteChip.Ltu.Inputs 0 : Var ByteChip.Ltu.Inputs (ZMod p)).multiplicity
      = var ⟨2⟩ := rfl

theorem ltu_component_interactionsWith_byte :
    (ByteChip.Ltu.component (p := p)).operations.interactionsWith byteChannel.toRaw =
      Operations.interactionsWith byteChannel.toRaw
        ((ByteChip.Ltu.main
          (varFromOffset ByteChip.Ltu.Inputs 0)).operations
            (size ByteChip.Ltu.Inputs)) := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations
        (⟨ByteChip.Ltu.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (ByteChip.Ltu.circuit (p := p)).main = ByteChip.Ltu.main from rfl]

/-- **A built `Ltu` row emits exactly one access.** -/
theorem ltu_buildRow_cleanAccesses
    (input : ByteChip.Ltu.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (bounds : input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) :
    (ByteChip.Ltu.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ByteChip.Ltu.component (p := p)).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(4 : ZMod p).val, (if input.b.val < input.c.val then (1 : ZMod p) else 0).val, input.b.val, input.c.val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_Ltu, ltu_component_interactionsWith_byte,
    ltu_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  unfold ByteChip.Ltu.component
  rw [ltu_buildRow_result input data hint bounds, ltuVar_b, ltuVar_c, ltuVar_multiplicity,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get _ _ _ _ 2 (by change 2 < 3; omega)]
  cases input
  simp only [Expression.eval]
  rfl

/-! ## Range — `U8Range`'s shape, parameterised by width

Stated over `RangeChip.componentFor width`, which is what the trace builds (one table per width in
SP1's complete `0 … 16` profile), rather than over `RangeChip.component n hn`. -/

theorem range_interactionsWith_byte (width : RangeChip.Width)
    (input : Var RangeChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith byteChannel.toRaw
        ((RangeChip.main width.val
          (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt)) input).operations offset) =
      [(pushedIf (channel := byteChannel) input.multiplicity
        (⟨6, input.a, Expression.const ((width.val : ℕ) : ZMod p), 0⟩ :
          ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [RangeChip.main, Circuit.operations, Circuit.bind_def,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem rangeVar_a :
    (varFromOffset RangeChip.Inputs 0 : Var RangeChip.Inputs (ZMod p)).a = var ⟨0⟩ := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem rangeVar_multiplicity :
    (varFromOffset RangeChip.Inputs 0 : Var RangeChip.Inputs (ZMod p)).multiplicity
      = var ⟨1⟩ := rfl

/-- `Ledger.onlyChannel_Range` at the width-indexed component the trace actually builds.
`componentFor width` and `component width.val _` are definitionally equal, but `rw` needs the
spelling the goal carries. -/
theorem onlyChannel_rangeComponentFor (width : RangeChip.Width) :
    Ledger.OnlyChannel (RangeChip.componentFor (p := p) width) byteChannel.toRaw :=
  Ledger.onlyChannel_Range width.val (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt))

theorem range_component_interactionsWith_byte (width : RangeChip.Width) :
    (RangeChip.componentFor (p := p) width).operations.interactionsWith byteChannel.toRaw =
      Operations.interactionsWith byteChannel.toRaw
        ((RangeChip.main width.val
          (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt))
          (varFromOffset RangeChip.Inputs 0)).operations (size RangeChip.Inputs)) := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith byteChannel.toRaw
      (Air.Flat.Component.rowOperations
        (⟨RangeChip.circuitFor width⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (RangeChip.circuitFor (p := p) width).main =
      RangeChip.main width.val
        (RangeChip.two_pow_lt (Nat.le_of_lt_succ width.isLt)) from rfl]

/-- **A built `Range` row emits exactly one access**, at its width's key. -/
theorem range_buildRow_cleanAccesses (width : RangeChip.Width)
    (input : RangeChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (RangeChip.componentFor (p := p) width).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((RangeChip.componentFor (p := p) width).buildRow input data hint) data)) =
      [(InteractionKind.Byte, "SP1Byte",
        [(6 : ZMod p).val, input.a.val, ((width.val : ℕ) : ZMod p).val, (0 : ZMod p).val],
        signedVal input.multiplicity)] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      (onlyChannel_rangeComponentFor width),
    range_component_interactionsWith_byte, range_interactionsWith_byte]
  simp only [List.map_cons, List.map_nil, toAccess_pushIf_byte]
  rw [rangeVar_a, rangeVar_multiplicity,
    eval_var_buildRow_input_get _ _ _ _ 0 (by change 0 < 2; omega),
    eval_var_buildRow_input_get _ _ _ _ 1 (by change 1 < 2; omega)]
  cases input
  simp only [Expression.eval]
  rfl

/-! ## Program — the ROM provider

Program is the one family whose row is wide (sixteen key cells plus the multiplicity), so the
per-cell `eval_var_buildRow_input_get` route the Byte families use would be sixteen rewrites. It is
also the one family whose pushed message is a named struct (`Inputs.toMessage`) rather than an
inline `ByteRow` literal, and that is what makes the shorter route available: evaluate the *whole*
input variable at once via `Component.rowInput_buildRow`, and the cells follow. -/

/-- The single Program access a built ROM row emits. Named rather than inlined because sixteen key
cells inside a theorem statement obscure the one thing worth reading — that the multiplicity is the
row's own explicit fetch-count column. -/
def programRowAccess (input : ProgramProviderChip.Inputs (ZMod p)) : LookupAccess :=
  (InteractionKind.Program, "SP1Program",
    [input.pc0.val, input.pc1.val, input.pc2.val, input.opcode.val,
      input.op_a.val, input.op_b[0].val, input.op_b[1].val,
      input.op_b[2].val, input.op_b[3].val, input.op_c[0].val,
      input.op_c[1].val, input.op_c[2].val, input.op_c[3].val,
      input.op_a_0.val, input.imm_b.val, input.imm_c.val],
    signedVal input.multiplicity)

theorem program_interactionsWith_program
    (input : Var ProgramProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactionsWith programChannel.toRaw
        ((ProgramProviderChip.main input).operations offset) =
      [(pushedIf (channel := programChannel) input.multiplicity input.toMessage).toRaw] := by
  simp only [ProgramProviderChip.main, Circuit.operations, Circuit.bind_def,
    assertion, Operations.localLength]
  simp only [Operations.interactionsWith_append, rangeCheck_interactionsWith,
    assertBool_interactionsWith]
  simp only [Channel.pushIf, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel, List.nil_append,
    if_true, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
theorem program_toAccess_eq_programRowAccess (env : Environment (ZMod p))
    (input : Var ProgramProviderChip.Inputs (ZMod p)) :
    AbstractInteraction.toAccess env
        (pushedIf (channel := programChannel) input.multiplicity input.toMessage).toRaw =
      programRowAccess (Eval.eval env input) := by
  rw [toAccess_pushIf_program]
  simp only [programRowAccess, ProgramProviderChip.Inputs.toMessage, circuit_norm]

theorem program_component_interactionsWith_program :
    (ProgramProviderChip.component (p := p)).operations.interactionsWith programChannel.toRaw =
      [(pushedIf (channel := programChannel)
          (varFromOffset ProgramProviderChip.Inputs 0 :
            Var ProgramProviderChip.Inputs (ZMod p)).multiplicity
          (varFromOffset ProgramProviderChip.Inputs 0 :
            Var ProgramProviderChip.Inputs (ZMod p)).toMessage).toRaw] := by
  rw [Component.interactionsWith_eq]
  show Operations.interactionsWith programChannel.toRaw
      (Air.Flat.Component.rowOperations
        (⟨ProgramProviderChip.circuit⟩ : Component (ZMod p))) = _
  rw [Air.Flat.Component.rowOperations_mk,
    show (ProgramProviderChip.circuit (p := p)).main = ProgramProviderChip.main from rfl]
  exact program_interactionsWith_program _ _

/-- **A built `Program` row emits exactly one access**, at its own instruction's key, with its own
fetch count as the multiplicity. -/
theorem program_buildRow_cleanAccesses
    (input : ProgramProviderChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (ProgramProviderChip.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((ProgramProviderChip.component (p := p)).buildRow input data hint) data)) =
      [programRowAccess input] := by
  rw [interactions_eq_interactionsWith_of_onlyChannel _ programChannel.toRaw
      Ledger.onlyChannel_ProgramProvider, program_component_interactionsWith_program]
  simp only [List.map_cons, List.map_nil, program_toAccess_eq_programRowAccess]
  rw [eval_varFromOffset_valueFromOffset]
  -- `rowInput_buildRow` is stated at `component.Input`, the goal at `Inputs`; only definitionally
  -- equal, so restate it at the goal's spelling before rewriting.
  have rowEq : valueFromOffset ProgramProviderChip.Inputs 0
      (Environment.fromArray
        ((ProgramProviderChip.component (p := p)).buildRow input data hint) data) = input :=
    (ProgramProviderChip.component (p := p)).rowInput_buildRow input data data hint
  rw [rowEq]

end SP1Clean.Soundness
