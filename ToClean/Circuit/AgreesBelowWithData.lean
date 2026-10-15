module

public import Clean.Circuit.Subcircuit
public import Clean.Circuit.Theorems

/-! # `AgreesBelow` over all three prover-environment channels

## Gap against upstream

Clean's `ProverEnvironment.AgreesBelow n env env'` (`Clean/Circuit/Basic.lean`) says only that the
two environments agree on the cells below `n`: `∀ i < n, env.get i = env'.get i`. The
witness-computability obligations built on it — `Operations.ComputableWitnesses`,
`Circuit.ComputableWitnesses`, `FormalCircuitBase.ComputableWitnesses` — therefore demand that a
witness generator produce equal outputs on any two environments agreeing on those cells, whatever
committed prover data (`data`) or prover hints (`hint`) they carry. A generator that reads either
channel (`Witgen.FExpr.dataGet` / `hintGet`) cannot meet that: two environments identical in every
cell but committing different hints evaluate it to different values, so the obligation is false, not
merely hard. SP1's hint-driven chips (Bitwise, Lt, Mul, Branch, the shifts, DivRem) are live
instances; Clean PR #450 carries the two-line counterexample
`Examples.DataWitness.not_computable_from_cells_alone`.

The honesty theorems that *consume* the obligation never need that much: every pair of environments
they compare — `fromList init hint` against `fromList (init ++ generated) hint` — shares one `data`
and one `hint` by construction. So the right predicate constrains all three channels, with cells
constrained only below `n` (they are produced incrementally) and `data`/`hint` in full (they are
ambient inputs fixed before generation begins):

`AgreesBelowWithData n env env' := env.AgreesBelow n env' ∧ env.data = env'.data ∧ env.hint = env'.hint`.

Upstream this is a strengthening of `ProverEnvironment.AgreesBelow` itself (Clean PR #450), which
changes an existing declaration and so cannot be staged in `ToClean/`. This file carries the
strengthened predicate under the additive name `AgreesBelowWithData`, the matching
`…ComputableWitnessesWithData` obligations, and the two consumers of the predicate whose statements
the SP1 development uses — `FormalCircuitBase.computableWitnesses_implies` and
`ProverEnvironment.agreesBelow_of_le` — re-proved at the strengthened predicate. The honesty chain
itself (`Circuit.witgenWithData_usesLocalWitnesses`) is in `ToClean.Circuit.WitnessGenerationData`.
On acceptance of PR #450 every `…WithData` name here collapses onto Clean's own and this file goes.

For the record, the upstream declarations whose statements or proofs the strengthening touches —
the set that would have to move to a Clean fork branch if a *modified* declaration were ever
required downstream: `ProverEnvironment.AgreesBelow`, `ProverEnvironment.OnlyAccessedBelow`,
`Operations.ComputableWitnesses`, `Circuit.ComputableWitnesses`,
`FormalCircuitBase.ComputableWitnesses` / `ComputableWitnesses'` / `computableWitnesses_implies` /
`compose_computableWitnesses`, `Circuit.subcircuit_computableWitnesses`,
`FlatOperation.proverEnvironment_usesLocalWitnesses`, `Circuit.proverEnvironment_usesLocalWitnesses`,
`Circuit.witgen_usesLocalWitnesses`, `ProverEnvironment.agreesBelow_of_le`,
`FlatOperation.onlyAccessedBelow_all`, `LookupCircuit.computableWitnesses`, and the one in-tree
instance `Gadgets.Addition8FullCarry`. None is needed at the modified statement: the SP1 development
consumes only the additive declarations below. -/

@[expose] public section

variable {F : Type}

/-- Two prover environments are indistinguishable to a witness generator running at offset `n`:
they agree on every cell below `n`, and on the committed data and the prover hints in full. -/
def ProverEnvironment.AgreesBelowWithData (n : ℕ) (env env' : ProverEnvironment F) : Prop :=
  env.AgreesBelow n env' ∧ env.data = env'.data ∧ env.hint = env'.hint

namespace ProverEnvironment.AgreesBelowWithData
variable {n : ℕ} {env env' : ProverEnvironment F}

theorem agreesBelow (h : env.AgreesBelowWithData n env') : env.AgreesBelow n env' := h.1

theorem get_eq (h : env.AgreesBelowWithData n env') {i : ℕ} (hi : i < n) :
    env.get i = env'.get i :=
  h.1 i hi

theorem data_eq (h : env.AgreesBelowWithData n env') : env.data = env'.data := h.2.1

theorem hint_eq (h : env.AgreesBelowWithData n env') : env.hint = env'.hint := h.2.2

end ProverEnvironment.AgreesBelowWithData

theorem ProverEnvironment.agreesBelowWithData_rfl (n : ℕ) (env : ProverEnvironment F) :
    env.AgreesBelowWithData n env :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

/-- `ProverEnvironment.agreesBelow_of_le` at the strengthened predicate. -/
theorem ProverEnvironment.agreesBelowWithData_of_le {n m : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelowWithData n env') (hmn : m ≤ n) : env.AgreesBelowWithData m env' :=
  ⟨ProverEnvironment.agreesBelow_of_le h.1 hmn, h.2.1, h.2.2⟩

section
variable [FiniteField F]

/-- `Operations.ComputableWitnesses` with the environment-agreement premise strengthened to
`AgreesBelowWithData`: every witness generator produces equal outputs on environments that agree on
the cells below its offset and on the committed data and hints. -/
def Operations.ComputableWitnessesWithData (ops : Operations F) (n : ℕ)
    (env env' : ProverEnvironment F) : Prop :=
  ops.forAllFlat n { witness n _ compute :=
    env.AgreesBelowWithData n env' → compute.eval env = compute.eval env' }

/-- `Circuit.ComputableWitnesses` at the strengthened premise. -/
def Circuit.ComputableWitnessesWithData {α : Type} (circuit : Circuit F α) (n : ℕ) : Prop :=
  ∀ env env', (circuit.operations n).ComputableWitnessesWithData n env env'

variable {α β : TypeMap} [ProvableType α] [ProvableType β]

/-- `FormalCircuitBase.ComputableWitnesses'` at the strengthened premise: the input variable reads
only cells below the offset (Clean's cell-only `OnlyAccessedBelow` — a stronger hypothesis than the
strengthened predicate needs, and the one `Table.build`'s row layout discharges). -/
def FormalCircuitBase.ComputableWitnessesWithData' (circuit : FormalCircuitBase F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F),
    ProverEnvironment.OnlyAccessedBelow n (F := F) (eval · input) →
      (circuit.main input).ComputableWitnessesWithData n

/-- `FormalCircuitBase.ComputableWitnesses` at the strengthened premise — the per-witness-step
obligation a formal circuit proves: agreement below the step's offset, on the committed data and
hints, and on the evaluated input, transfers to the witness value. -/
def FormalCircuitBase.ComputableWitnessesWithData (circuit : FormalCircuitBase F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) (env env' : ProverEnvironment F),
    circuit.main input |>.operations n |>.forAllFlat n {
      witness n _ compute :=
        env.AgreesBelowWithData n env' → eval env input = eval env' input →
          compute.eval env = compute.eval env' }

/-- `FormalCircuitBase.computableWitnesses_implies` at the strengthened premise: the per-step
obligation implies the offset-indexed one. Clean's proof verbatim, projecting the cell component of
the strengthened agreement where the input-locality hypothesis is used. -/
lemma FormalCircuitBase.computableWitnessesWithData_implies {circuit : FormalCircuitBase F β α} :
    circuit.ComputableWitnessesWithData → circuit.ComputableWitnessesWithData' := by
  simp only [ComputableWitnessesWithData, ComputableWitnessesWithData']
  intro h_computable n input input_only_accesses_n env env'
  specialize h_computable n input env env'
  specialize input_only_accesses_n env env'
  simp only [Operations.ComputableWitnessesWithData, ← Operations.forAll_toFlat_iff] at *
  generalize ((circuit.main input).operations n).toFlat = ops at *
  revert h_computable
  apply FlatOperation.forAll_implies
  simp only [Condition.implies, Condition.ignoreSubcircuit, imp_self]
  induction ops using FlatOperation.induct generalizing n with
  | empty => trivial
  | assert | lookup | interact => simp_all [FlatOperation.forAll]
  | witness m c ops ih =>
    simp only [FlatOperation.forAll]
    exact ⟨fun h h_agrees => h h_agrees (input_only_accesses_n h_agrees.agreesBelow),
      ih (m + n) fun h_agrees =>
        input_only_accesses_n (ProverEnvironment.agreesBelow_of_le h_agrees (by omega))⟩

end
