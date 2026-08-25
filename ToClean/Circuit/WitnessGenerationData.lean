import Clean.Circuit.WitnessGeneration

/-!
# Honest witness generation against committed prover data

A `ProverEnvironment` has three channels a witness generator can read: cells (`get`), committed
prover data (`data`, via `Witgen.FExpr.dataGet`) and prover hints (`hint`, via `hintGet`). Clean's
witness interpreters — `FlatOperation.dynamicWitnesses`, `Circuit.proverEnvironment` and the
array-backed `Circuit.witgen` — build their environment with `ProverEnvironment.fromList` /
`fromArray`, both of which hard-code `data _ _ := #[]`. So the environment they exhibit commits *no*
data, and the honesty theorem `Circuit.witgen_usesLocalWitnesses` is only available at that empty
commitment.

This file re-runs the same construction with the committed data supplied by the caller: the
`…WithData` counterpart of each definition, and the same honesty theorem, ending at

* `Circuit.witgenWithData_usesLocalWitnesses` — array-backed witness generation against arbitrary
  committed `data` uses the circuit's local witnesses,

under exactly Clean's hypothesis (`Circuit.ComputableWitnesses`) and no other. That matters wherever
the environment a downstream theorem is stated at carries real data: a flat-AIR `Table` shares one
`ProverData` across its rows and reads every row through `Environment.fromArray row table.data`, so
an honesty theorem at the empty commitment cannot be transported to it — the witness generators may
read `data`, and `ProverEnvironment.AgreesBelow` (rightly) refuses to identify environments that
commit different data (`Clean.Examples.DataWitness.not_computable_from_cells_alone` is the witness
that this is not a gap in the proof but a fact about the definition).

## Upstream

Destined for `Clean/Circuit/Basic.lean` + `Clean/Circuit/Theorems.lean` +
`Clean/Circuit/WitnessGeneration.lean`. Clean has the whole chain already, in the data-free form;
`Clean/Circuit/WitnessGeneration.lean`'s module docstring records the omission as deliberate and
deferred ("circuits whose witnesses read `env.data` … need the environment extended with that data,
which applies to both interpreters equally and is left to a later phase"). What is missing is only
the `data` parameter — every proof below is Clean's own proof with that parameter threaded.

Upstream this should land as a *generalization*: add the `data` argument to
`ProverEnvironment.fromList`/`fromArray`, `FlatOperation.dynamicWitness(es)`,
`FlatOperation.proverEnvironment`, `Circuit.proverEnvironment`, `FlatOperation.witgen(Step)` and
`Circuit.witgen`, and delete this file — the data-free spellings are then the `fun _ _ => #[]`
instances. That is a change to existing Clean declarations, which this repository stages in the
Clean fork rather than here; the additive `…WithData` names below let the dependent development
proceed at the current pin, and are the exact declarations the generalization subsumes. The suffix
is therefore expected to disappear on acceptance, unlike the rest of `ToClean/`.
-/

variable {F : Type} [FiniteField F] {α : Type}

/-- Build a `ProverEnvironment` from a witness list, the committed prover data, and a prover hint.
Data-carrying counterpart of `ProverEnvironment.fromList`. -/
def ProverEnvironment.fromListWithData (witnesses : List F) (data : ProverData F)
    (hint : ProverHint F) : ProverEnvironment F where
  get i := witnesses[i]?.getD 0
  data := data
  hint := hint

/-- Build a `ProverEnvironment` from a witness array (O(1) reads), the committed prover data, and a
prover hint. Data-carrying counterpart of `ProverEnvironment.fromArray`. -/
def ProverEnvironment.fromArrayWithData (witnesses : Array F) (data : ProverData F)
    (hint : ProverHint F) : ProverEnvironment F where
  get i := witnesses[i]?.getD 0
  data := data
  hint := hint

theorem ProverEnvironment.fromArrayWithData_eq_fromListWithData (witnesses : Array F)
    (data : ProverData F) (hint : ProverHint F) :
    ProverEnvironment.fromArrayWithData witnesses data hint
      = .fromListWithData witnesses.toList data hint := by
  simp only [ProverEnvironment.fromArrayWithData, ProverEnvironment.fromListWithData,
    Array.getElem?_toList]

namespace FlatOperation
variable {data : ProverData F} {hint : ProverHint F}

/-- The witnesses one operation contributes, computed against the environment of all witnesses so
far *and* the committed data. Data-carrying counterpart of `FlatOperation.dynamicWitness`. -/
def dynamicWitnessWithData (data : ProverData F) (hint : ProverHint F) (op : FlatOperation F)
    (acc : List F) : List F := match op with
  | .witness _ compute => (compute.eval (.fromListWithData acc data hint)).toList
  | .assert _ => []
  | .lookup _ => []
  | .interact _ => []

/-- Reference (list-backed) witness generation against committed data. Data-carrying counterpart of
`FlatOperation.dynamicWitnesses`. -/
def dynamicWitnessesWithData (ops : List (FlatOperation F)) (data : ProverData F)
    (hint : ProverHint F) (init : List F) : List F :=
  ops.foldl (fun acc op => acc ++ dynamicWitnessWithData data hint op acc) init

/-- The environment reference witness generation exhibits, carrying the committed data. -/
def proverEnvironmentWithData (ops : List (FlatOperation F)) (data : ProverData F)
    (hint : ProverHint F) (init : List F) : ProverEnvironment F :=
  .fromListWithData (dynamicWitnessesWithData ops data hint init) data hint

lemma dynamicWitnessWithData_length {op : FlatOperation F} {init : List F} :
    (dynamicWitnessWithData data hint op init).length = op.singleLocalLength := by
  rcases op <;> simp [dynamicWitnessWithData, singleLocalLength]

lemma dynamicWitnessesWithData_length {ops : List (FlatOperation F)} (init : List F) :
    (dynamicWitnessesWithData ops data hint init).length = init.length + localLength ops := by
  induction ops generalizing init with
  | nil => rw [dynamicWitnessesWithData, List.foldl_nil, localLength, add_zero]
  | cons op ops ih =>
    simp_all +arith [dynamicWitnessesWithData, localLength_cons, dynamicWitnessWithData_length]

lemma dynamicWitnessesWithData_cons {op : FlatOperation F} {ops : List (FlatOperation F)}
    {acc : List F} :
    dynamicWitnessesWithData (op :: ops) data hint acc
      = dynamicWitnessesWithData ops data hint (acc ++ dynamicWitnessWithData data hint op acc) := by
  simp only [dynamicWitnessesWithData, List.foldl_cons]

lemma getElem?_dynamicWitnessesWithData_of_lt {ops : List (FlatOperation F)} {acc : List F} {i : ℕ}
    (hi : i < acc.length) :
    (dynamicWitnessesWithData ops data hint acc)[i]?.getD 0 = acc[i] := by
  simp only [dynamicWitnessesWithData]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ dynamicWitnessWithData data hint op acc).length := by
      rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma getElem?_dynamicWitnessesWithData_cons_right {op : FlatOperation F}
    {ops : List (FlatOperation F)} {init : List F} {i : ℕ} (hi : i < op.singleLocalLength) :
    (dynamicWitnessesWithData (op :: ops) data hint init)[init.length + i]?.getD 0 =
      (dynamicWitnessWithData data hint op init)[i]'(dynamicWitnessWithData_length (F := F) ▸ hi) := by
  rw [dynamicWitnessesWithData_cons,
    getElem?_dynamicWitnessesWithData_of_lt (by simp [hi, dynamicWitnessWithData_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

/-- Flat version of `Circuit.proverEnvironmentWithData_usesLocalWitnesses`: reference witness
generation against committed data is honest. -/
theorem proverEnvironmentWithData_usesLocalWitnesses {ops : List (FlatOperation F)}
    (init : List F) :
    (∀ (env env' : ProverEnvironment F),
      forAll init.length { witness n _ c := env.AgreesBelow n env' → c.eval env = c.eval env' } ops) →
      (proverEnvironmentWithData ops data hint init).UsesLocalWitnessesFlat init.length ops := by
  simp only [proverEnvironmentWithData, ProverEnvironment.UsesLocalWitnessesFlat,
    ProverEnvironment.ExtendsVector]
  intro h_computable
  induction ops generalizing init with
  | nil => trivial
  | cons op ops ih =>
    simp only [forAll_cons] at h_computable ⊢
    cases op with
    | assert | lookup | interact =>
      simp_all [dynamicWitnessesWithData_cons, Condition.applyFlat, singleLocalLength,
        dynamicWitnessWithData]
    | witness m compute =>
      simp_all only [Condition.applyFlat, singleLocalLength, ProverEnvironment.AgreesBelow]
      -- get rid of ih first
      constructor; case right =>
        specialize ih (init ++ (compute.eval (.fromListWithData init data hint)).toList)
        simp only [List.length_append, Vector.length_toList] at ih
        ring_nf at *
        exact ih fun _ _ => (h_computable ..).right
      clear ih
      replace h_computable := fun env env' => (h_computable env env').left
      intro i
      simp only [ProverEnvironment.fromListWithData]
      rw [getElem?_dynamicWitnessesWithData_cons_right i.is_lt]
      simp only [dynamicWitnessWithData, Vector.getElem_toList]
      congr 1
      apply h_computable
      -- `data` and `hint` are literally shared: every environment here is `.fromListWithData _ data hint`.
      refine ⟨?_, rfl, rfl⟩
      intro j hj
      simp [ProverEnvironment.fromListWithData, hj, getElem?_dynamicWitnessesWithData_of_lt]

/-- One step of array-backed witness generation against committed data. Data-carrying counterpart of
`FlatOperation.witgenStep`. -/
def witgenStepWithData (data : ProverData F) (hint : ProverHint F) (acc : Array F) :
    FlatOperation F → Array F
  | .witness _ code => acc ++ (code.eval (.fromArrayWithData acc data hint)).toArray
  | .assert _ | .lookup _ | .interact _ => acc

/-- Array-backed witness generation against committed data: a single linear fold over the
operations. Data-carrying counterpart of `FlatOperation.witgen`. -/
def witgenWithData (data : ProverData F) (hint : ProverHint F) (ops : List (FlatOperation F))
    (init : Array F) : Array F :=
  ops.foldl (witgenStepWithData data hint) init

lemma witgenStepWithData_toList (data : ProverData F) (hint : ProverHint F) (acc : Array F)
    (op : FlatOperation F) :
    (witgenStepWithData data hint acc op).toList
      = acc.toList ++ dynamicWitnessWithData data hint op acc.toList := by
  cases op <;>
    simp [witgenStepWithData, dynamicWitnessWithData,
      ProverEnvironment.fromArrayWithData_eq_fromListWithData, Vector.toList]

/-- The array-backed interpreter agrees with the list-backed reference semantics, at any committed
data. -/
theorem witgenWithData_eq_dynamicWitnessesWithData (data : ProverData F) (hint : ProverHint F)
    (ops : List (FlatOperation F)) (init : Array F) :
    witgenWithData data hint ops init
      = (dynamicWitnessesWithData ops data hint init.toList).toArray := by
  induction ops generalizing init with
  | nil => simp [witgenWithData, dynamicWitnessesWithData]
  | cons op ops ih =>
    rw [witgenWithData, List.foldl_cons, ← witgenWithData, dynamicWitnessesWithData_cons, ih,
      witgenStepWithData_toList]

end FlatOperation

namespace Circuit
variable {data : ProverData F} {hint : ProverHint F}

/-- The environment a circuit's own witness generators exhibit, carrying the committed prover data.
Data-carrying counterpart of `Circuit.proverEnvironment`. -/
def proverEnvironmentWithData (circuit : Circuit F α) (data : ProverData F) (hint : ProverHint F)
    (init : List F := []) : ProverEnvironment F :=
  .fromListWithData
    (FlatOperation.dynamicWitnessesWithData (circuit.operations init.length).toFlat data hint init)
    data hint

/-- If a circuit has computable witnesses, `proverEnvironmentWithData` agrees with the circuit's
witness generators — at *any* committed data. Data-carrying counterpart of
`Circuit.proverEnvironment_usesLocalWitnesses`. -/
theorem proverEnvironmentWithData_usesLocalWitnesses (circuit : Circuit F α) (data : ProverData F)
    (hint : ProverHint F) (init : List F) :
    circuit.ComputableWitnesses init.length →
      (circuit.proverEnvironmentWithData data hint init).UsesLocalWitnesses init.length
        (circuit.operations init.length) := by
  intro h_computable
  simp_all only [proverEnvironmentWithData, Circuit.ComputableWitnesses,
    Operations.ComputableWitnesses, ← Operations.forAll_toFlat_iff,
    ProverEnvironment.UsesLocalWitnesses]
  exact FlatOperation.proverEnvironmentWithData_usesLocalWitnesses init h_computable

/-- Fast witness generation for a circuit against committed prover data: array-backed, single linear
pass. `init` provides the witnesses below the circuit's starting offset (typically the inputs); the
result extends it with all witnesses created by the circuit. Data-carrying counterpart of
`Circuit.witgen`. -/
def witgenWithData (circuit : Circuit F α) (data : ProverData F) (hint : ProverHint F)
    (init : Array F := #[]) : Array F :=
  FlatOperation.witgenWithData data hint (circuit.operations init.size).toFlat init

/-- `Circuit.witgenWithData` builds exactly the environment of `Circuit.proverEnvironmentWithData`. -/
theorem witgenWithData_proverEnvironment (circuit : Circuit F α) (data : ProverData F)
    (hint : ProverHint F) (init : Array F) :
    ProverEnvironment.fromArrayWithData (circuit.witgenWithData data hint init) data hint
      = circuit.proverEnvironmentWithData data hint init.toList := by
  rw [proverEnvironmentWithData, witgenWithData,
    ProverEnvironment.fromArrayWithData_eq_fromListWithData,
    FlatOperation.witgenWithData_eq_dynamicWitnessesWithData]
  simp

/-- **Honest array-backed witness generation at a committed `ProverData`.** If a circuit has
computable witnesses, the environment built from `Circuit.witgenWithData` uses the circuit's local
witnesses. This is `Circuit.witgen_usesLocalWitnesses` with the empty commitment `fun _ _ => #[]`
replaced by an arbitrary one, and it needs no hypothesis Clean's version does not. -/
theorem witgenWithData_usesLocalWitnesses (circuit : Circuit F α) (data : ProverData F)
    (hint : ProverHint F) (init : Array F) (h_computable : circuit.ComputableWitnesses init.size) :
    (ProverEnvironment.fromArrayWithData (circuit.witgenWithData data hint init) data
      hint).UsesLocalWitnesses init.size (circuit.operations init.size) := by
  rw [witgenWithData_proverEnvironment]
  have h := circuit.proverEnvironmentWithData_usesLocalWitnesses data hint init.toList
  simp only [Array.length_toList] at h
  exact h h_computable

/-- Witness generation extends `init`: it appends exactly the circuit's local witnesses. -/
theorem size_witgenWithData (circuit : Circuit F α) (data : ProverData F) (hint : ProverHint F)
    (init : Array F) :
    (circuit.witgenWithData data hint init).size
      = init.size + (circuit.operations init.size).localLength := by
  rw [witgenWithData, FlatOperation.witgenWithData_eq_dynamicWitnessesWithData]
  simp only [List.size_toArray, FlatOperation.dynamicWitnessesWithData_length,
    Array.length_toList, FlatOperation.localLength_toFlat]

/-- Witness generation leaves `init` in place: the generated row starts with the cells it was
seeded with. -/
theorem getElem?_witgenWithData_of_lt (circuit : Circuit F α) (data : ProverData F)
    (hint : ProverHint F) {init : Array F} {i : ℕ} (hi : i < init.size) :
    (circuit.witgenWithData data hint init)[i]?.getD 0 = init[i] := by
  rw [witgenWithData, FlatOperation.witgenWithData_eq_dynamicWitnessesWithData]
  rw [List.getElem?_toArray]
  exact FlatOperation.getElem?_dynamicWitnessesWithData_of_lt (by simpa using hi)

end Circuit
