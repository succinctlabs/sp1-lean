import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Mathlib.Data.ZMod.Basic

/-! # `assertZeros` — batched zero-asserts + their `circuit_norm` normalization lemmas

The one-bind batched assert emitter used for the DivRem chip's own-constraint tail
(`assertZeros (ownAsserts cols)`), together with the `@[circuit_norm]` lemmas that let Clean's
`ElaboratedCircuit` obligations and `circuit_proof_start` close over it without unfolding the opaque
expression list: a list of `.assert` ops contributes 0 length, 0 subcircuit offsets, no channels, and
its constraint condition is plain list membership.

Relocated verbatim from `Proofs/Chips/DivRemChip/Defs.lean` (which now imports this module) so that
the `DivRemCore` assertion gadget (`Native/Operations/DivRemOperation/Core.lean`) can emit the same
tail without importing the whole chip skeleton. Namespace stays `SP1Clean.DivRemChip`, so every
existing fully-qualified reference is unchanged. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Emit a list of zero-asserts in one circuit bind (`es.map .assert`). Used for `ownAsserts cols`. -/
def assertZeros (es : List (Expression (ZMod p))) : Circuit (ZMod p) Unit :=
  fun _ => ((), es.map (fun e => .assert e))

-- `circuit_norm` lemmas so `ElaboratedCircuit` obligations close on `assertZeros es` without unfolding
-- the opaque `ownAsserts cols`: a list of `.assert` ops contributes 0 length, 0 subcircuit offsets, no channels.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_map_assert (es : List (Expression (ZMod p))) :
    Operations.localLength (es.map fun e => (Operation.assert e)) = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma shallowConstraints_map_assert (es : List (Expression (ZMod p))) :
    Operations.shallowConstraints (es.map fun e => (Operation.assert e)) = es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, Operations.shallowConstraints, ih]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma forAll_map_assert (offset : ℕ) (cond : Condition (ZMod p))
    (es : List (Expression (ZMod p))) :
    Operations.forAll offset cond (es.map fun e => (Operation.assert e))
      ↔ ∀ e ∈ es, cond.assert offset e := by
  induction es with
  | nil => simp [Operations.forAll]
  | cons e es ih =>
    simp only [List.map_cons, Operations.forAll, ih, List.mem_cons, forall_eq_or_imp]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma forAllNoOffset_map_assert (cond : ConditionNoOffset (ZMod p))
    (es : List (Expression (ZMod p))) :
    Operations.forAllNoOffset cond (es.map fun e => (Operation.assert e))
      ↔ ∀ e ∈ es, cond.assert e := by
  induction es with
  | nil => simp [Operations.forAllNoOffset]
  | cons e es ih =>
    simp only [List.map_cons, Operations.forAllNoOffset, ih, List.mem_cons, forall_eq_or_imp]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma shallowChannels_map_assert (es : List (Expression (ZMod p))) :
    Operations.shallowChannels (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.shallowChannels, List.map_cons]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma subChannelsG_map_assert (es : List (Expression (ZMod p))) :
    Operations.subcircuitChannelsWithGuarantees (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.subcircuitChannelsWithGuarantees, List.map_cons]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma subChannelsR_map_assert (es : List (Expression (ZMod p))) :
    Operations.subcircuitChannelsWithRequirements (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.subcircuitChannelsWithRequirements, List.map_cons]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma interactions_map_assert (es : List (Expression (ZMod p))) :
    Operations.interactions (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.interactions, List.map_cons, ih]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma lookups_map_assert (es : List (Expression (ZMod p))) :
    Operations.lookups (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.lookups, List.map_cons, ih]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma shallowInteractions_map_assert (es : List (Expression (ZMod p))) :
    Operations.shallowInteractions (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.shallowInteractions, List.map_cons, ih]

-- `interactionsWith` (per-channel filter) of a list of pure `.assert` ops is empty — lets the
-- `exposedChannels_eq` State-bus descent close over `assertZeros (ownAsserts cols)` without unfolding.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma interactionsWith_map_assert (channel : RawChannel (ZMod p))
    (es : List (Expression (ZMod p))) :
    Operations.interactionsWith channel (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.map_cons, Operations.interactionsWith_assert, ih]

/-- The batched own-assert tail is structurally just a family of zero-length, channel-free
`assertZero` circuits. Register that fact once so Clean can derive the enclosing chip metadata. -/
instance : ExplicitCircuits (F := ZMod p) assertZeros where
  output _ _ := ()
  localLength _ _ := 0
  operations es _ := es.map fun e => .assert e
  localLength_eq es _ := by simp [assertZeros, Circuit.localLength, circuit_norm]
  subcircuitsConsistent es _ := by
    simp [assertZeros, Operations.SubcircuitsConsistent, circuit_norm]
  channelsWithGuarantees _ _ := []
  channelsLawful es _ := by simp [assertZeros, Operations.ChannelsLawful, circuit_norm]

end SP1Clean.DivRemChip
