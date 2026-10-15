module

public import ToClean.Circuit.WitnessGenerationData
public import Clean.Air.FlatComponent
public import Clean.Circuit.Foundations

/-! # Semantic table construction and its completeness proof

Clean's built-in AIR witness generator supplies the runtime scheduler and Rust export. This
addition supplies a semantic row/table construction theorem: honest circuit witnesses and the
circuit's prover assumptions imply the resulting physical constraints and channel guarantees.
It does not establish scheduler completeness or agreement with final derived data.

Rows are built at explicit prover data and a shared hint. A table stores
only its component and physical rows; its constraints and ledger are evaluated at the enclosing
ensemble's canonical data. The congruence lemmas identify which obligations survive a data change.
Fixed-column tables require the same exact fixed-prefix invariant as Clean's `Table` constructor.

The missing upstream capabilities are the row-layout and completeness lemmas, plus environment
congruence for circuit constraints and interactions. Remove these additions when Clean supplies
equivalent proofs for its canonical witness generator.
-/

@[expose] public section

variable {F : Type} [FiniteField F]

/-! ## Environment congruence

`Expression.eval` reads only `env.get`, so evaluated expressions transport across a change of
evaluation data. Lookup containment and channel guarantees/requirements can read `env.data` and
need separate transport proofs. The complete witness's canonical data still comes from its rows. -/

theorem Expression.eval_congr {env env' : Environment F} (h : env.get = env'.get)
    (e : Expression F) : Expression.eval env e = Expression.eval env' e := by
  induction e with
  | var v => simp only [Expression.eval, h]
  | const c => rfl
  | add x y ihx ihy => simp only [Expression.eval, ihx, ihy]
  | mul x y ihx ihy => simp only [Expression.eval, ihx, ihy]

namespace Operations

/-- `Operations.ConstraintsHold` transports across any change of environment that preserves the
cells, provided the lookups still hold. The lookup premise is exactly the part of `ConstraintsHold`
that reads `env.data`; it is vacuous for a lookup-free operation list
(`constraintsHold_congr_of_lookups_nil`). -/
theorem constraintsHold_congr {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get)
    (h_lookups : ∀ l ∈ ops.lookups, l.Contains env → l.Contains env')
    (h : ops.ConstraintsHold env) : ops.ConstraintsHold env' :=
  ⟨fun e he => (Expression.eval_congr h_get e).symm.trans (h.1 e he),
    fun l hl => h_lookups l hl (h.2 l hl)⟩

/-- `ConstraintsHold` transports across a change of evaluation data that agrees on the tables
the operations actually look up. `Lookup.Contains` reads one data key per lookup. -/
theorem constraintsHold_congr_of_data_agree {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get)
    (h_data : ∀ l ∈ ops.lookups,
      env.data l.table.name l.table.arity = env'.data l.table.name l.table.arity)
    (h : ops.ConstraintsHold env) : ops.ConstraintsHold env' := by
  refine constraintsHold_congr h_get (fun l hl h_contains => ?_) h
  have h_entry : l.entry.map (Expression.eval env) = l.entry.map (Expression.eval env') := by
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_map, Expression.eval_congr h_get]
  simpa only [Lookup.Contains, ← h_data l hl, ← h_entry] using h_contains

/-- A lookup-free operation list's constraints depend on the environment's cells alone. -/
theorem constraintsHold_congr_of_lookups_nil {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get) (h_lookups : ops.lookups = [])
    (h : ops.ConstraintsHold env) : ops.ConstraintsHold env' :=
  constraintsHold_congr h_get (by simp [h_lookups]) h

end Operations

/-- Evaluating an interaction reads only the environment's cells. -/
theorem AbstractInteraction.eval_congr {i : AbstractInteraction F} {env env' : Environment F}
    (h : env.get = env'.get) : i.eval env = i.eval env' := by
  simp only [AbstractInteraction.eval, Expression.eval_congr h]

namespace Operations

/-- Concrete interaction values depend on the environment's cells alone. The predicates
`Interaction.Guarantees`/`Requirements` still take data as an explicit argument. -/
theorem interactionValues_congr {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get) : ops.interactionValues env = ops.interactionValues env' := by
  simp only [interactionValues]
  exact List.map_congr_left fun i _ => AbstractInteraction.eval_congr h_get

/-- Per-channel version of `interactionValues_congr`. -/
theorem interactionValuesWith_congr {ops : Operations F} {channel : RawChannel F}
    {env env' : Environment F} (h_get : env.get = env'.get) :
    ops.interactionValuesWith channel env = ops.interactionValuesWith channel env' := by
  simp only [interactionValuesWith]
  exact List.map_congr_left fun i _ => AbstractInteraction.eval_congr h_get

end Operations

namespace ProvableType
variable {M : TypeMap} [ProvableType M]

omit [FiniteField F] in
/-- The value a row's cells decode to at a given offset depends only on those cells. -/
theorem valueFromOffset_congr (M : TypeMap) [ProvableType M] (offset : ℕ)
    {env env' : Environment F} (h : ∀ i < offset + size M, env.get i = env'.get i) :
    valueFromOffset M offset env = valueFromOffset M offset env' := by
  simp only [valueFromOffset]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_mapRange]
  exact h _ (by omega)

/-- The canonical row input variable reads only the cells below `size M` — the side condition of
`FormalCircuitBase.ComputableWitnessesWithData'`, discharged once for the AIR row layout. -/
theorem onlyAccessedBelow_varFromOffset_zero (M : TypeMap) [ProvableType M] :
    ProverEnvironment.OnlyAccessedBelow (size M) (F := F)
      (Eval.eval · (varFromOffset (F := F) M 0)) := by
  have h_eval : ∀ e : ProverEnvironment F,
      Eval.eval e (varFromOffset (F := F) M 0) = valueFromOffset M 0 e.toEnvironment :=
    fun e => by rw [eval_varFromOffset_prover]; rfl
  intro env env' h
  simp only [h_eval]
  exact valueFromOffset_congr M 0 fun i _ => h _ (by omega)

end ProvableType

namespace Air.Flat
namespace Component

/-! ## The row a component builds for one semantic input -/

/--
The physical AIR row a component builds for one semantic input: the `size Input` input cells,
followed by the cells the circuit's own witness generators compute, in emission order.

This is the row layout `Component` already fixes — `rowInput` decodes the first `size Input` cells,
`rowOperations` starts at offset `size Input` — so seeding array-backed witness generation with
`toElements input` makes the generated cells land exactly where `rowOperations` expects them.
-/
def buildRow (c : Component F) (input : c.Input F) (data : ProverData F) (hint : ProverHint F) :
    Array F :=
  (c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint (toElements input).toArray

lemma buildRow_def (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) :
    c.buildRow input data hint
      = (c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint
          (toElements input).toArray := rfl

/-- A built row is a row of the component's table: it has exactly the component's width. -/
theorem size_buildRow (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) : (c.buildRow input data hint).size = c.width := by
  rw [buildRow, Circuit.size_witgenWithData]
  simp only [Vector.size_toArray, width, GeneralFormalCircuit.size_eq]
  congr 1
  exact c.circuit.localLength_eq _ _

/-- The input cells survive witness generation: reading the built row back through the component's
own `rowInput` recovers the semantic input. The environment's committed data is irrelevant, so the
row may be read at a `ProverData` other than the one it was built with. -/
theorem rowInput_buildRow (c : Component F) (input : c.Input F) (data data' : ProverData F)
    (hint : ProverHint F) :
    c.rowInput (Environment.fromArray (c.buildRow input data hint) data') = input := by
  have h : (Vector.mapRange (size c.Input) fun i =>
      (Environment.fromArray (c.buildRow input data hint) data').get (0 + i))
      = toElements input := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_mapRange, Nat.zero_add]
    rw [buildRow, Circuit.getElem?_witgenWithData_of_lt _ _ _ (by simpa using hi)]
    simp
  rw [rowInput, valueFromOffset, h, ProvableType.fromElements_toElements]

/-- The environment a built row is read at, as a `ProverEnvironment` — the same environment
witness generation ran in, so the circuit's completeness theorem applies to it directly. -/
lemma proverEnvironment_buildRow_toEnvironment (c : Component F) (input : c.Input F)
    (data : ProverData F) (hint : ProverHint F) :
    (ProverEnvironment.fromArrayWithData (c.buildRow input data hint) data
      hint).toEnvironment = Environment.fromArray (c.buildRow input data hint) data := rfl

/-! ## The keystone: a built row satisfies the component's constraints -/

/--
**A component builds valid rows.** If the component's circuit has computable witnesses (Clean's
standard honest-prover side condition) and the semantic input satisfies the circuit's
`ProverAssumptions` at the data and hint the row is built with, then the built row satisfies the
component's full per-row assertion system: `ConstraintsHold` and `FullGuarantees`.

This is `GeneralFormalCircuit.original_full_completeness` transported onto the AIR row layout. The
chain is: `FormalCircuitBase.computableWitnessesWithData_implies` (with the row input variable reading only
cells below `size Input`) gives `Circuit.ComputableWitnessesWithData` at the row offset;
`Circuit.witgenWithData_usesLocalWitnesses` turns that into an honest environment carrying the
committed `data`; `original_full_completeness` fires; and `Component.constraintsHold_iff` /
`guarantees_iff` land the result on `Component.operations`.
-/
theorem buildRow_constraintsHold (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : c.circuit.ProverAssumptions input data hint) :
    c.operations.ConstraintsHold (Environment.fromArray (c.buildRow input data hint) data) ∧
      c.operations.FullGuarantees (Environment.fromArray (c.buildRow input data hint) data) := by
  set inputVar : Var c.Input F := varFromOffset c.Input 0 with h_inputVar
  set env : ProverEnvironment F :=
    ProverEnvironment.fromArrayWithData (c.buildRow input data hint) data hint with h_env
  -- the row input variable only reads cells below the row offset, so the circuit's
  -- `ComputableWitnessesWithData` obligation applies at that offset
  have h_computable' : (c.circuit.main inputVar).ComputableWitnessesWithData (size c.Input) :=
    FormalCircuitBase.computableWitnessesWithData_implies h_computable (size c.Input) inputVar
      (ProvableType.onlyAccessedBelow_varFromOffset_zero c.Input)
  -- witness generation against the committed data is therefore honest
  have h_uses : env.UsesLocalWitnesses (size c.Input)
      ((c.circuit.main inputVar).operations (size c.Input)) := by
    have h := Circuit.witgenWithData_usesLocalWitnesses (c.circuit.main inputVar) data hint
      (toElements input).toArray (by simpa using h_computable')
    simpa [h_env, buildRow, h_inputVar] using h
  -- the row decodes back to the semantic input
  have h_input : Eval.eval env inputVar = input := by
    rw [h_inputVar, ProvableType.eval_varFromOffset_prover]
    exact c.rowInput_buildRow input data data hint
  have h := c.circuit.original_full_completeness (size c.Input) env inputVar h_uses
    (by rw [h_input]; exact h_prover)
  exact ⟨(c.constraintsHold_iff _).mpr h.1, (c.guarantees_iff _).mpr h.2⟩

/-- A valid row produced by `buildRow` also satisfies the component's semantic specification and
all channel requirements.  This is the composition of honest witness generation with the
component's already-bundled soundness theorem; downstream table transports can use the semantic
boundary without reopening a circuit's witness implementation. -/
theorem buildRow_spec_requirements (c : Component F) (input : c.Input F)
    (data : ProverData F) (hint : ProverHint F)
    (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : c.circuit.ProverAssumptions input data hint)
    (h_assumptions : c.circuit.Assumptions input data) :
    let env := Environment.fromArray (c.buildRow input data hint) data
    c.Spec env ∧ c.operations.FullRequirements env := by
  dsimp only
  let env := Environment.fromArray (c.buildRow input data hint) data
  have built := c.buildRow_constraintsHold input data hint h_computable h_prover
  apply c.weakSoundness
  · change c.circuit.Assumptions (c.rowInput env) data
    rw [show env = Environment.fromArray (c.buildRow input data hint) data from rfl,
      c.rowInput_buildRow input data data hint]
    exact h_assumptions
  · exact built.1
  · exact built.2

/-- A lookup-free component's constraints survive a change of evaluation data without
rebuilding its rows. -/
theorem constraintsHold_setData (c : Component F) {row : Array F} {data data' : ProverData F}
    (h_lookups : c.operations.lookups = [])
    (h : c.operations.ConstraintsHold (Environment.fromArray row data)) :
    c.operations.ConstraintsHold (Environment.fromArray row data') :=
  Operations.constraintsHold_congr_of_lookups_nil (env := Environment.fromArray row data)
    (env' := Environment.fromArray row data') rfl h_lookups h

/-- The interactions a built row emits do not depend on the environment's committed data at all. -/
theorem interactionValuesWith_setData (c : Component F) {row : Array F}
    {data data' : ProverData F} (channel : RawChannel F) :
    c.operations.interactionValuesWith channel (Environment.fromArray row data)
      = c.operations.interactionValuesWith channel (Environment.fromArray row data') :=
  Operations.interactionValuesWith_congr (env := Environment.fromArray row data)
    (env' := Environment.fromArray row data') rfl

/-- **A circuit that generates no witness cells builds exactly the row it was seeded with.** The
generated array has the seed's size (`size_witgenWithData` at `localLength = 0`) and agrees with it
at every index (`getElem?_witgenWithData_of_lt`), so it *is* the seed. -/
theorem buildRow_of_localLength_zero (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) (hzero : c.circuit.localLength (varFromOffset c.Input 0) = 0) :
    c.buildRow input data hint = (toElements input).toArray := by
  have hlen : ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).localLength
      = 0 := by
    rw [show ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).localLength
      = (c.circuit.main (varFromOffset c.Input 0)).localLength (size c.Input) from rfl,
      c.circuit.localLength_eq, hzero]
  have hsize : (c.buildRow input data hint).size = (toElements input).toArray.size := by
    rw [buildRow, Circuit.size_witgenWithData, Vector.size_toArray, hlen, Nat.add_zero]
  refine Array.ext hsize ?_
  intro i hi hi'
  have hbound : i < ((c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint
      (toElements input).toArray).size := hi
  have := Circuit.getElem?_witgenWithData_of_lt (c.circuit.main (varFromOffset c.Input 0)) data
    hint (init := (toElements input).toArray) hi'
  rw [Array.getElem?_eq_getElem hbound] at this
  show ((c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint
    (toElements input).toArray)[i]'hbound = _
  simpa using this

/-- Decode the verifier's fixed prefix followed by prover-owned suffix cells. -/
def fixedInput (c : Component F) (fixed : FixedColumns F) (index : ℕ) (suffix : Array F) :
    c.Input F :=
  fromElements (Vector.ofFn fun cell : Fin (size c.Input) =>
    if cell.val < fixed.width then (fixed.row index)[cell.val]?.getD 0
    else suffix[cell.val - fixed.width]?.getD 0)

/-- Honest row generation preserves every verifier-fixed input cell. -/
theorem buildRow_fixedInput_prefix (c : Component F) (fixed : FixedColumns F)
    (columns : c.fixedColumns = some fixed) (index : ℕ) (suffix : Array F)
    (data : ProverData F) (hint : ProverHint F) :
    (c.buildRow (c.fixedInput fixed index suffix) data hint).extract 0 fixed.width = fixed.row index := by
  have width : fixed.width ≤ size c.Input := by
    simpa only [columns, Option.map_some, Option.getD_some] using c.fixed_width_le_input
  have fixedSize : (fixed.row index).size = fixed.width := by simp [FixedColumns.row]
  have rowSize : size c.Input ≤ (c.buildRow (c.fixedInput fixed index suffix) data hint).size := by
    rw [buildRow, Circuit.size_witgenWithData, Vector.size_toArray]
    omega
  apply Array.ext
  · simp only [Array.size_extract, Nat.sub_zero, fixedSize]
    omega
  · intro cell left right
    have bound : cell < fixed.width := by omega
    have inputBound : cell < (toElements (c.fixedInput fixed index suffix)).toArray.size := by
      simp only [Vector.size_toArray]
      omega
    have cells := Circuit.getElem?_witgenWithData_of_lt
      (c.circuit.main (varFromOffset c.Input 0)) data hint inputBound
    change (c.buildRow (c.fixedInput fixed index suffix) data hint)[cell]?.getD 0 =
      (toElements (c.fixedInput fixed index suffix)).toArray[cell] at cells
    have generatedBound : cell < (c.buildRow (c.fixedInput fixed index suffix) data hint).size := by omega
    rw [Array.getElem?_eq_getElem generatedBound] at cells
    simpa [Array.getElem_extract, fixedInput, ProvableType.toElements_fromElements,
      bound, Array.getElem?_eq_getElem right] using cells

end Component

/-! ## Assembling a whole table -/

namespace Table

/-- A physical table's literal ledger depends only on its committed cells. Semantic channel
predicates and lookup constraints still require their own data-transport arguments. -/
theorem interactionsWith_setData (table : Table F) (data data' : ProverData F)
    (channel : RawChannel F) :
    table.interactionsWith data channel = table.interactionsWith data' channel := by
  apply congrArg List.flatten
  exact List.map_congr_left fun _ _ => table.component.interactionValuesWith_setData channel

/-- Build physical rows with one hint shared by all inputs. -/
def build (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F)
    (fixed : c.fixedRowsMatch (inputs.map (c.buildRow · data hint)) := by
      preserve_tactic_target
      trivial) : Table F where
  component := c
  table := inputs.map (c.buildRow · data hint)
  uniform_width := by
    intro row member
    obtain ⟨input, _, rfl⟩ := List.mem_map.mp member
    exact c.size_buildRow input data hint
  fixed_rows_match := fixed

/-- Build all verifier-fixed rows using Clean's row witness generator. The suffix is indexed
by physical row, so duplicate fixed messages and zero-demand rows retain their positions.
This is a semantic table constructor; channel scheduling remains Clean's responsibility. -/
def buildPreallocated (c : Component F) (fixed : FixedColumns F)
    (columns : c.fixedColumns = some fixed) (suffix : ℕ → Array F)
    (data : ProverData F) (hint : ProverHint F) : Table F :=
  build c ((List.range fixed.height).map fun index => c.fixedInput fixed index (suffix index))
    data hint (by
      simp only [Component.fixedRowsMatch, columns, FixedColumns.RowsMatch, List.map_map]
      exact List.map_congr_left fun index _ => c.buildRow_fixedInput_prefix fixed columns index _ data hint)

@[simp] theorem buildPreallocated_component (c : Component F) (fixed : FixedColumns F)
    (columns : c.fixedColumns = some fixed) (suffix : ℕ → Array F)
    (data : ProverData F) (hint : ProverHint F) :
    (buildPreallocated c fixed columns suffix data hint).component = c := rfl

@[simp] theorem buildPreallocated_length (c : Component F) (fixed : FixedColumns F)
    (columns : c.fixedColumns = some fixed) (suffix : ℕ → Array F)
    (data : ProverData F) (hint : ProverHint F) :
    (buildPreallocated c fixed columns suffix data hint).length = fixed.height := by
  simp [buildPreallocated, build, length]

/-- Build ordinary input rows, or allocate the complete fixed trace with the supplied suffixes.
The fixed prefix always comes from the component's verifier-owned program. -/
def buildWithFixed (c : Component F) (inputs : List (c.Input F))
    (suffix : FixedColumns F → ℕ → Array F) (data : ProverData F) (hint : ProverHint F) : Table F :=
  match columns : c.fixedColumns with
  | none => build c inputs data hint (by simp only [Component.fixedRowsMatch, columns])
  | some fixed => buildPreallocated c fixed columns (suffix fixed) data hint

@[simp] theorem buildWithFixed_component (c : Component F) (inputs : List (c.Input F))
    (suffix : FixedColumns F → ℕ → Array F) (data : ProverData F) (hint : ProverHint F) :
    (buildWithFixed c inputs suffix data hint).component = c := by
  unfold buildWithFixed
  split <;> rfl

section ConstantHint
variable (c : Component F) (inputs : List (c.Input F)) (data : ProverData F) (hint : ProverHint F)
  (fixed : c.fixedRowsMatch (inputs.map (c.buildRow · data hint)))

@[simp] lemma build_component : (build c inputs data hint fixed).component = c := rfl

@[simp] lemma build_table :
    (build c inputs data hint fixed).table = inputs.map (c.buildRow · data hint) := rfl

@[simp] lemma build_length : (build c inputs data hint fixed).length = inputs.length := List.length_map ..

/-- Honest constant-hint witnesses satisfy the physical constraints at the generation data. -/
theorem build_constraints (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : ∀ input ∈ inputs, c.circuit.ProverAssumptions input data hint) :
    (build c inputs data hint fixed).Constraints data := by
  intro row member
  obtain ⟨input, h_input, rfl⟩ := List.mem_map.mp member
  exact (c.buildRow_constraintsHold input data hint h_computable (h_prover input h_input)).1

/-- Honest constant-hint witnesses satisfy the channel guarantees at the generation data. -/
theorem build_guarantees (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : ∀ input ∈ inputs, c.circuit.ProverAssumptions input data hint) :
    (build c inputs data hint fixed).Guarantees data := by
  intro row member
  obtain ⟨input, h_input, rfl⟩ := List.mem_map.mp member
  exact (c.buildRow_constraintsHold input data hint h_computable (h_prover input h_input)).2

/-- The literal per-channel ledger at any evaluation data. -/
theorem build_interactions (evaluationData : ProverData F) (channel : RawChannel F) :
    (build c inputs data hint fixed).interactionsWith evaluationData channel =
      inputs.flatMap fun input => c.operations.interactionValuesWith channel
        (Environment.fromArray (c.buildRow input data hint) evaluationData) := by
  simp only [interactionsWith, build_table, build_component, List.flatMap_map]

/-- All interaction occurrences at any evaluation data. -/
theorem build_interactionValues (evaluationData : ProverData F) :
    (build c inputs data hint fixed).interactions evaluationData =
      inputs.flatMap fun input => c.operations.interactionValues
        (Environment.fromArray (c.buildRow input data hint) evaluationData) := by
  simp only [interactions, build_table, build_component, List.flatMap_map]

end ConstantHint

/-- Every emitted occurrence belongs to one of the component's declared channels. -/
theorem channel_mem_channels_of_mem_interactions (table : Table F) (data : ProverData F) :
    ∀ i ∈ table.interactions data, i.channel ∈ table.component.circuit.channels := by
  rw [Table.forall_interactions_iff]
  intro _ _ i interactionMem
  rw [AbstractInteraction.eval_channel]
  simp only [Component.interactions_eq] at interactionMem
  refine table.component.circuit.channels_subset table.component.rowInputVar
    table.component.rowOffset ?_
  simp only [Operations.channels, List.mem_map]
  exact ⟨i, interactionMem, rfl⟩

end Table
end Air.Flat
