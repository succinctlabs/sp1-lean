import Clean.Circuit.WitnessGeneration
import Clean.Circuit.Subcircuit

/-! # Composition lemmas for `ComputableWitnesses`

A circuit's `completeness` field says "*any* environment consistent with my witness generators
satisfies my constraints"; it never exhibits such an environment. Clean's array-backed interpreter
`Circuit.witgen` does exhibit one, and `Circuit.witgen_usesLocalWitnesses` proves it honest — but
only for circuits satisfying `Circuit.ComputableWitnesses`, i.e. whose generators read the
environment strictly below the circuit's starting offset.

Clean supplies `FormalCircuitBase.compose_computableWitnesses` for children that *carry* a
`ComputableWitnesses` field, but a `FormalAssertion` or `GeneralFormalCircuit` child carries no such
field. The lemmas here close that hole in the two cases a composed chip meets.

* A child that witnesses **no cells at all** satisfies any witness-congruence condition vacuously,
  and can therefore be dispatched by its `localLength` alone, with no unfolding of its operations
  (`forAll_witnessCongr_of_localLength_zero`, `forAll_witnessCongr_of_subcircuit`). Unfolding
  composed children is precisely the elaboration blow-up that makes these proofs intractable at
  scale, so avoiding it is the point.
* A child that **does** witness cells is dispatched by its *own* `ComputableWitnesses`, proved once
  at the child (`forAll_witnessCongr_of_generalSubcircuit`, and its `FormalCircuit` /
  `FormalAssertion` twins `forAll_witnessCongr_of_formalSubcircuit` /
  `forAll_witnessCongr_of_assertionSubcircuit` — all three `toSubcircuit`s nest the child's own
  operation list, so the three proofs differ only in which projection to unfold). Clean's
  `Circuit.subcircuit_computableWitnesses` is the analogous step for a `FormalCircuit`, but it goes
  through `ComputableWitnesses'`, whose side condition is "the child's input variable reads only
  cells below the offset" — unprovable in a parent whose own `ComputableWitnesses` quantifies over
  an arbitrary input variable. The parent's condition carries an input-agreement premise instead,
  and that premise is what transports to the child, so the bridge is stated with an explicit
  `Q → eval env input = eval env' input` rather than an `OnlyAccessedBelow`.
* A zero-witness *nested* operation list — Clean's `forEach` combinator emits one, not a single
  subcircuit — is dispatched by `Operations.forAllFlat_witnessCongr_of_localLength_zero`, the
  `Operations` twin of `forAll_witnessCongr_of_localLength_zero`.

## Upstream

Destined for `Clean/Circuit/Subcircuit.lean`, beside `compose_computableWitnesses` and
`Circuit.subcircuit_computableWitnesses`. Clean has exactly one `ComputableWitnesses` instance in
tree (`Gadgets/Addition8/Addition8FullCarry.lean`), which has no subcircuits and so never needs
this; any composed circuit does. -/

namespace FlatOperation

open Circuit

variable {F : Type} [FiniteField F]

/-- A zero-witness operation list satisfies any witness-*congruence* condition vacuously: each of its
witness operations produces a `Vector F 0`, and all of those are equal.

This is the lemma that keeps a chip's `ComputableWitnesses` proof proportional to the witnesses the
chip actually declares: the composed readers and gadgets contribute no cells, so their flattened
operation lists are dispatched by their `localLength`, with no unfolding.

The two premise families `P`/`Q` are left abstract so the statement matches
`FormalCircuitBase.ComputableWitnesses`'s condition (an offset-indexed environment-agreement premise,
then a closed input-agreement premise) without naming it. -/
theorem forAll_witnessCongr_of_localLength_zero {env env' : ProverEnvironment F}
    {P : ℕ → Prop} {Q : Prop} :
    ∀ (ops : List (FlatOperation F)) (n : ℕ), localLength ops = 0 →
      forAll n
        { witness := fun offset _ compute => P offset → Q → compute.eval env = compute.eval env' }
        ops := by
  intro ops
  induction ops with
  | nil => intro n _; trivial
  | cons op ops ih =>
    intro n h
    cases op with
    | witness m c =>
      simp only [localLength, Nat.add_eq_zero_iff] at h
      obtain ⟨hm, hops⟩ := h
      subst hm
      refine ⟨fun _ _ => ?_, ih _ hops⟩
      apply Vector.ext
      omega
    | assert e => exact ⟨trivial, ih _ h⟩
    | lookup l => exact ⟨trivial, ih _ h⟩
    | interact i => exact ⟨trivial, ih _ h⟩

/-- The same, for a composed subcircuit: read its cell count off `localLength` (which `circuit_norm`
computes from the child's own `localLength_eq`) instead of unfolding its operations. -/
theorem forAll_witnessCongr_of_subcircuit {env env' : ProverEnvironment F}
    {P : ℕ → Prop} {Q : Prop} {m : ℕ} (s : Subcircuit F m) (n : ℕ) (h : s.localLength = 0) :
    forAll n
      { witness := fun offset _ compute => P offset → Q → compute.eval env = compute.eval env' }
      s.ops.toFlat :=
  forAll_witnessCongr_of_localLength_zero _ _ (by rw [← s.localLength_eq, h])

/-- Weakening the *input-agreement* premise of a witness-congruence condition. The parent's premise
is agreement of the **parent's** input row; the child's `ComputableWitnesses` is stated with
agreement of the **child's** input variable. One implication between the two propositions — which
is a `congrArg` in the parent, since the child input is built from the parent's — transports the
whole flattened condition. -/
theorem forAll_witnessCongr_mono {env env' : ProverEnvironment F} {Q Q' : Prop} (h : Q' → Q) :
    ∀ (ops : List (FlatOperation F)) (n : ℕ),
      forAll n { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q →
            compute.eval env = compute.eval env' } ops →
      forAll n { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q' →
            compute.eval env = compute.eval env' } ops := by
  intro ops
  induction ops with
  | nil => intro n _; trivial
  | cons op ops ih =>
    intro n hall
    cases op with
    | witness m c => exact ⟨fun ha hq => hall.1 ha (h hq), ih _ hall.2⟩
    | assert e => exact ⟨trivial, ih _ hall.2⟩
    | lookup l => exact ⟨trivial, ih _ hall.2⟩
    | interact i => exact ⟨trivial, ih _ hall.2⟩

/-- The `Operations` form of `forAll_witnessCongr_of_localLength_zero`: a nested operation list that
declares no cells satisfies any witness-congruence condition.

Needed because Clean's `forEach` combinator produces a *list* of subcircuits rather than one
subcircuit, so the sibling lemma — which reads a single `Subcircuit`'s `localLength` — does not
apply. `Operations.forAllFlat` is by definition `Operations.forAll` at the subcircuit-flattening
condition, so the two statements meet definitionally at the use site. -/
theorem _root_.Operations.forAllFlat_witnessCongr_of_localLength_zero
    {env env' : ProverEnvironment F} {P : ℕ → Prop} {Q : Prop} (ops : Operations F) (n : ℕ)
    (h : ops.localLength = 0) :
    ops.forAllFlat n
      { witness := fun offset _ compute =>
          P offset → Q → compute.eval env = compute.eval env' } := by
  rw [← Operations.forAll_toFlat_iff]
  exact forAll_witnessCongr_of_localLength_zero _ _
    (by rw [FlatOperation.localLength_toFlat, h])

/-- `forAll_witnessCongr_mono` with the offset premise in scope: weakening the input-agreement
premise may itself use the environment agreement, provided the operation list starts at or after
the offset that agreement is stated at.

This is what a child whose *input expression reads a cell of the parent* needs — SP1's `MSB` and
`LTU` byte providers range-check `2 * b - msb * 256`, where `msb` is a cell the parent witnessed
just above the row input. Every witness inside the child sits at an offset at least the child's
starting offset, so `ProverEnvironment.agreesBelow_of_le` recovers agreement there. -/
theorem forAll_witnessCongr_mono_agrees {env env' : ProverEnvironment F} {Q Q' : Prop} {n : ℕ}
    (h : ProverEnvironment.AgreesBelow n env env' → Q' → Q) :
    ∀ (ops : List (FlatOperation F)) (m : ℕ), n ≤ m →
      forAll m { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q →
            compute.eval env = compute.eval env' } ops →
      forAll m { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q' →
            compute.eval env = compute.eval env' } ops := by
  intro ops
  induction ops with
  | nil => intro m _ _; trivial
  | cons op ops ih =>
    intro m hnm hall
    cases op with
    | witness k c =>
      exact ⟨fun ha hq => hall.1 ha (h (ProverEnvironment.agreesBelow_of_le ha hnm) hq),
        ih _ (by omega) hall.2⟩
    | assert e => exact ⟨trivial, ih _ hnm hall.2⟩
    | lookup l => exact ⟨trivial, ih _ hnm hall.2⟩
    | interact i => exact ⟨trivial, ih _ hnm hall.2⟩

variable {β α : TypeMap} [ProvableType β] [ProvableType α]

/-- **A witnessing `GeneralFormalCircuit` child is dispatched by its own `ComputableWitnesses`.**
The counterpart of `forAll_witnessCongr_of_subcircuit` for a child that actually witnesses cells:
instead of reading the child's cell count off `localLength`, read the child's own honest-witness
theorem, and transport the input-agreement premise with `h_in`.

`h_in` is the parent-side obligation and is one `congrArg` per input field the child reads: the
child's input variable is assembled from the parent's, so agreement of the evaluated parent row
gives agreement of the evaluated child row. -/
theorem forAll_witnessCongr_of_generalSubcircuit {env env' : ProverEnvironment F} {Q : Prop}
    (circuit : GeneralFormalCircuit F β α) (input : Var β F) (n : ℕ)
    (h_cw : circuit.base.ComputableWitnesses)
    (h_in : Q → Eval.eval env input = Eval.eval env' input) :
    forAll n
      { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q →
            compute.eval env = compute.eval env' }
      (circuit.toSubcircuit n input).ops.toFlat := by
  have h := h_cw n input env env'
  rw [← Operations.forAll_toFlat_iff] at h
  have h2 := forAll_witnessCongr_mono h_in _ n h
  simpa only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat] using h2

/-- The `FormalCircuit` twin of `forAll_witnessCongr_of_generalSubcircuit` — Clean's gadget library
is written at this type (`Gadgets.And.And8.circuit`, `Gadgets.Or.Or8.circuit`, …), and a gadget that
witnesses its result cell needs its own `ComputableWitnesses` just as a general circuit does.

`h_in` is stated at the `mono_agrees` strength: a caller whose child input is a plain projection of
the parent row ignores the extra premise. The offset appears twice in the goal — once as the
`forAll` offset, once inside `toSubcircuit` — and a parent's two spellings of it differ
syntactically (`localLength x + k` versus `k + (localLength x + 0)`), so the two are taken
separately with an explicit `m = n`, dischargeable by `omega` with `localLength` left opaque.
Unifying them instead forces `whnf` through the child's `localLength`, which is the documented
elaboration cliff. -/
theorem forAll_witnessCongr_of_formalSubcircuit {env env' : ProverEnvironment F} {Q : Prop}
    (circuit : FormalCircuit F β α) (input : Var β F) {m n : ℕ} (hmn : m = n)
    (h_cw : circuit.base.ComputableWitnesses)
    (h_in : ProverEnvironment.AgreesBelow n env env' → Q →
      Eval.eval env input = Eval.eval env' input) :
    forAll m
      { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q →
            compute.eval env = compute.eval env' }
      (circuit.toSubcircuit n input).ops.toFlat := by
  subst hmn
  have h := h_cw m input env env'
  rw [← Operations.forAll_toFlat_iff] at h
  have h2 := forAll_witnessCongr_mono_agrees h_in _ m le_rfl h
  simpa only [FormalCircuit.toSubcircuit, Operations.toNested_toFlat] using h2

/-- The `FormalAssertion` twin of `forAll_witnessCongr_of_generalSubcircuit`. An assertion returns
no output but may still declare cells — a bit decomposition is the canonical case
(`Gadgets.ToBits.rangeCheck`), and every byte/range provider composes one. -/
theorem forAll_witnessCongr_of_assertionSubcircuit {env env' : ProverEnvironment F} {Q : Prop}
    (circuit : FormalAssertion F β) (input : Var β F) {m n : ℕ} (hmn : m = n)
    (h_cw : circuit.base.ComputableWitnesses)
    (h_in : ProverEnvironment.AgreesBelow n env env' → Q →
      Eval.eval env input = Eval.eval env' input) :
    forAll m
      { witness := fun offset _ compute =>
          ProverEnvironment.AgreesBelow offset env env' → Q →
            compute.eval env = compute.eval env' }
      (circuit.toSubcircuit n input).ops.toFlat := by
  subst hmn
  have h := h_cw m input env env'
  rw [← Operations.forAll_toFlat_iff] at h
  have h2 := forAll_witnessCongr_mono_agrees h_in _ m le_rfl h
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat] using h2

end FlatOperation
