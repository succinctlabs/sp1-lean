import ToClean.Air.Realizes
import ToClean.Air.PublicVerifier
import SP1Clean.Soundness.RankedGrounding
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Data.ZMod.Basic

/-! # A complete, executable counter arithmetization

This example closes Clean's raw `Ensemble.Statement` against PolyFun's labeled trace
semantics. It is deliberately independent of RISC-V and of SP1 faithfulness. The single
event increments a natural number below 15. A fixed lookup prevents modular wraparound;
State balance and a strict rank recover every physical transition occurrence.
-/

namespace SP1Clean.Soundness.CounterExample

open Air.Flat Circuit PFunctor PFunctor.DynSystem
open scoped BigOperators

/-- A small prime field with ample room for the complete interaction budget. -/
abbrev F := ZMod 97

instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- A direction exists precisely when incrementing is permitted. -/
def interface : PFunctor where
  A := ℕ
  B n := PLift (n < 15)

/-- The only event is increment. -/
inductive Event where
  | increment
deriving DecidableEq, Repr

/-- Natural-number semantics, independently of fields, rows, and compilation. -/
@[reducible] def machine : Labeled interface where
  State := ℕ
  toDynSystem := DynSystem.mk' id (fun n _ => n + 1)
  Event := Event
  event _ _ := .increment

/-- Canonical natural interpretation of the two public field elements. -/
def boundary (input : fieldPair F) : machine.State × machine.State :=
  (input.1.val, input.2.val)

/-- The semantic resource policy mentions neither AIR witnesses nor compiler success. -/
def admissible (input : fieldPair F) (events : List Event) : Prop :=
  input.1.val ≤ 15 ∧ input.2.val ≤ 15 ∧ events.length ≤ 15

private theorem prefix_last {n count : ℕ} (orbit : machine.toDynSystem.Prefix n count) :
    orbit.last = n + count := by
  induction orbit with
  | nil => rfl
  | @step n count direction tail ih =>
    change tail.last = n + (count + 1)
    change tail.last = n + 1 + count at ih
    omega

/-- Every semantic event increments the natural state exactly once. -/
theorem trace_length {initial final : ℕ} {events : List Event}
    (trace : machine.Trace initial events final) : final = initial + events.length := by
  obtain ⟨count, orbit, rfl, rfl⟩ := trace
  rw [orbit.length_events machine.event]
  exact prefix_last orbit

private theorem trace_of_length (initial : ℕ) (events : List Event)
    (bound : initial + events.length ≤ 15) :
    machine.Trace initial events (initial + events.length) := by
  induction events generalizing initial with
  | nil => exact Labeled.Trace.nil (m := machine) initial
  | cons event rest ih =>
    cases event
    have stepBound : initial < 15 := by simp only [List.length_cons] at bound; omega
    have tailBound : initial + 1 + rest.length ≤ 15 := by
      simp only [List.length_cons] at bound; omega
    obtain ⟨count, orbit, labels, last⟩ := ih (initial + 1) tailBound
    refine ⟨count + 1, .step ⟨stepBound⟩ orbit, ?_, ?_⟩
    · change Event.increment :: orbit.events machine.event = Event.increment :: rest
      rw [labels]
    · change orbit.last = initial + (Event.increment :: rest).length
      exact last.trans (by change initial + 1 + rest.length = initial + (rest.length + 1); omega)

/-- A genuinely fixed, finite lookup, including an explicit enumeration. -/
def rangeTable (limit : ℕ) (small : limit ≤ 97) : StaticTable F field where
  name := s!"CounterRange{limit}"
  length := limit
  row i := (i.val : F)
  index value := value.val
  Spec value := value.val < limit
  contains_iff value := by
    constructor
    · rintro ⟨i, rfl⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt small)]
      exact i.isLt
    · intro bound
      exact ⟨⟨value.val, bound⟩, (ZMod.natCast_zmod_val value).symm⟩

/-- The sole dynamic channel carries a single counter value. -/
def state : Channel F field where
  name := "CounterState"
  Guarantees _ _ := True

private theorem natural_increment {previous next : F} (bound : previous.val < 15)
    (equation : next = previous + 1) : next.val = previous.val + 1 := by
  rw [equation, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]

private theorem field_increment {previous next : F} (equation : next.val = previous.val + 1) :
    next = previous + 1 := by
  have cast := congrArg (fun n : ℕ => (n : F)) equation
  simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using cast

private def transitionMain (input : Var fieldPair F) : Circuit F Unit := do
  lookup (rangeTable 15 (by decide)).toTable input.1
  assertZero (input.2 - (input.1 + 1))
  state.pull input.1
  state.push input.2

/-- A row proves an ordinary natural increment, including its enabling condition. -/
def transition : GeneralFormalCircuit F fieldPair unit where
  name := "CounterTransition"
  main := transitionMain
  Spec input _ _ := input.1.val < 15 ∧ input.2.val = input.1.val + 1
  ProverAssumptions input _ _ := input.1.val < 15 ∧ input.2.val = input.1.val + 1
  soundness := by
    circuit_proof_start [transitionMain, rangeTable, state]
    simp_all only [Prod.ext_iff]
    exact ⟨trivial, natural_increment h_holds.1 (sub_eq_zero.mp h_holds.2)⟩
  completeness := by
    circuit_proof_start [transitionMain, rangeTable, state]
    simp_all only [Prod.ext_iff]
    exact ⟨trivial, sub_eq_zero.mpr (field_increment h_assumptions.2)⟩

private def rangeExpression (value : Expression F) : ℕ → Expression F
  | 0 => 1
  | count + 1 => rangeExpression value count * (value - (count : F))

@[circuit_norm] private theorem rangeExpression_eval (env : Environment F)
    (value : Expression F) (count : ℕ) :
    env (rangeExpression value count) = ∏ index ∈ Finset.range count, (env value - (index : F)) := by
  induction count with
  | zero => simp [rangeExpression, circuit_norm]
  | succ count ih => simp [rangeExpression, circuit_norm, ih, Finset.prod_range_succ]

private theorem rangeProduct_zero (value : F) :
    (∏ index ∈ Finset.range 16, (value - (index : F))) = 0 ↔ value.val ≤ 15 := by
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨index, member, zero⟩
    have bound := Finset.mem_range.mp member
    rw [sub_eq_zero] at zero
    rw [zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro bound
    refine ⟨value.val, Finset.mem_range.mpr (by omega), ?_⟩
    rw [ZMod.natCast_zmod_val, sub_self]

private def verifierMain (input : Var fieldPair F) : Circuit F Unit := do
  assertZero (rangeExpression input.1 16)
  assertZero (rangeExpression input.2 16)

/-- The two public polynomial assertions mean exactly that both endpoints lie in 0..15. -/
def verifier : GeneralFormalCircuit F fieldPair unit where
  name := "CounterPublicBounds"
  main := verifierMain
  Spec input _ _ := input.1.val ≤ 15 ∧ input.2.val ≤ 15
  ProverAssumptions input _ _ := input.1.val ≤ 15 ∧ input.2.val ≤ 15
  soundness := by
    circuit_proof_start [verifierMain, rangeProduct_zero]
    simp_all only [Prod.ext_iff, and_self]
  completeness := by
    circuit_proof_start [verifierMain, rangeProduct_zero]
    simp_all only [Prod.ext_iff, and_self]

/-- Install the endpoint assertions through the shared, interaction-only verifier adapter. -/
def boundaryChecks : PublicVerifier F fieldPair where
  name := "CounterBounds"
  circuit := verifier
  assumptions := by intros; trivial
  length_zero := by intro input; simp [verifier, circuit_norm]
  lookups := by intros; simp [verifier, verifierMain, circuit_norm]
  interactions := by intros; simp [verifier, verifierMain, circuit_norm]

private def boundaryProgram : Verifier.Program F fieldPair where
  main input := do
    Verifier.push state input.1
    Verifier.pull state input.2

private def baseEnsemble : Ensemble F fieldPair where
  tables := [{ circuit := transition }]
  unique_names := List.nodup_singleton _
  channels := [state.toRaw]
  verifier := boundaryProgram

/-- One physical transition table; the separate verifier enforces public bounds and state endpoints. -/
abbrev ensemble : Ensemble F fieldPair := boundaryChecks.install baseEnsemble

private theorem check_channel_ne_state : boundaryChecks.channel baseEnsemble ≠ state.toRaw := by
  intro equal
  have absent := boundaryChecks.channel_not_mem baseEnsemble
  rw [equal] at absent
  exact absent (List.mem_singleton_self _)

private theorem boundary_count : boundaryChecks.CountBound := by
  left
  norm_num [PublicVerifier.assertions, boundaryChecks, verifier, verifierMain, circuit_norm,
    ZMod.ringChar_zmod_n]

/-- Decode the two physical cells (Clean supplies zero for absent cells). -/
def decodeRow (row : Array F) : fieldPair F :=
  (row[0]?.getD 0, row[1]?.getD 0)

private theorem transition_constraints (env : Environment F) :
    ({ circuit := transition } : Component F).operations.ConstraintsHold env ↔
      (env.get 0).val < 15 ∧ (env.get 1).val = (env.get 0).val + 1 := by
  rw [Component.constraintsHold_iff]
  simp only [Component.rowOperations, transition, transitionMain, circuit_norm,
    Lookup.Contains, Table.toRaw, StaticTable.toTable]
  rw [and_comm]
  change ((∃ i : Fin 15, env.get 0 = (i.val : F)) ∧
    env.get 1 - (env.get 0 + 1) = 0) ↔ _
  have range : (∃ i : Fin 15, env.get 0 = (i.val : F)) ↔ (env.get 0).val < 15 :=
    (rangeTable 15 (by decide)).contains_iff _
  rw [range]
  change ((env.get 0).val < 15 ∧ env.get 1 - (env.get 0 + 1) = 0) ↔ _
  constructor
  · rintro ⟨bound, equation⟩
    exact ⟨bound, natural_increment bound (sub_eq_zero.mp equation)⟩
  · rintro ⟨bound, equation⟩
    exact ⟨bound, sub_eq_zero.mpr (field_increment equation)⟩

private theorem verifier_checks (input : fieldPair F) (data : ProverData F) :
    boundaryChecks.Checks input data ↔ input.1.val ≤ 15 ∧ input.2.val ≤ 15 := by
  simp [PublicVerifier.Checks, boundaryChecks, verifier, verifierMain, circuit_norm,
    rangeProduct_zero, explicit_provable_type]

private theorem transition_interactions (env : Environment F) :
    ({ circuit := transition } : Component F).operations.interactionValuesWith state.toRaw env =
      [state.pulledValue (env.get 0), state.pushedValue (env.get 1)] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, transition, transitionMain, circuit_norm]
  simp only [AbstractInteraction.eval, ChannelInteraction.toRaw, circuit_norm, explicit_provable_type]

private theorem verifier_interactions (env : Environment F) :
    boundaryProgram.circuitOperations.interactionValuesWith state.toRaw env =
      [state.pushedValue (env.get 0), state.pulledValue (env.get 1)] := by
  simp [boundaryProgram, Operations.interactionValuesWith, circuit_norm,
    AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.pushedValue, Channel.pulledValue,
    Channel.emitted, Channel.pulled, explicit_provable_type]

/-- A table witness from explicit transition pairs, useful also for adversarial regressions. -/
def witnessOfRows (input : fieldPair F) (rows : List (fieldPair F)) : EnsembleWitness ensemble where
  tables := [{
    component := { circuit := transition }
    table := rows.map (fun row => #[row.1, row.2])
    uniform_width := by
      intro row member
      obtain ⟨pair, _, rfl⟩ := List.mem_map.mp member
      rfl
  }]
  publicInput := input
  same_length := rfl
  same_circuits := by intro i bound; have : i = 0 := by change i < 1 at bound; omega
                      subst i; rfl

private theorem one_table (witness : EnsembleWitness ensemble) :
    ∃ table, witness.tables = [table] ∧ table.component = { circuit := transition } := by
  have length : witness.tables.length = 1 := witness.same_length.symm
  obtain ⟨table, tables⟩ := List.length_eq_one_iff.mp length
  refine ⟨table, tables, ?_⟩
  have circuit := witness.same_circuits 0 (by decide)
  simpa only [tables, ensemble, PublicVerifier.install, baseEnsemble, List.getElem_cons_zero] using circuit.symm

private theorem witness_constraints (witness : EnsembleWitness ensemble) (table : Table F)
    (tables : witness.tables = [table]) (component : table.component = { circuit := transition }) :
    witness.Constraints ↔
      ∀ row ∈ table.table, (decodeRow row).1.val < 15 ∧
        (decodeRow row).2.val = (decodeRow row).1.val + 1 := by
  change (∀ current ∈ witness.tables, current.Constraints witness.data) ↔ _
  simp only [tables, List.mem_singleton, forall_eq, Table.Constraints, component,
    transition_constraints]
  rfl

private theorem witness_ledger (witness : EnsembleWitness ensemble) (table : Table F)
    (tables : witness.tables = [table]) (component : table.component = { circuit := transition }) :
    witness.interactionsWith state.toRaw = state.transitionLedger
      witness.publicInput.1 witness.publicInput.2 table.table decodeRow := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    ensemble, boundaryChecks.install_verifier_interactions baseEnsemble _ _ check_channel_ne_state,
    EnsembleWitness.tableContext, TableContext.interactionsWith, tables,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Table.interactionsWith,
    component, transition_interactions]
  rw [show baseEnsemble.verifierOperations = boundaryProgram.circuitOperations from rfl,
    verifier_interactions]
  rfl

private theorem walk_length {rows : List (Array F)} {initial final : ℕ}
    (walk : Walk.IsWalk (fun row => ((decodeRow row).1.val, (decodeRow row).2.val))
      initial final rows)
    (increments : ∀ row ∈ rows, (decodeRow row).2.val = (decodeRow row).1.val + 1) :
    final = initial + rows.length := by
  induction rows generalizing initial with
  | nil => exact walk.symm
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have head := increments row (List.mem_cons_self ..)
    have last := ih tail (fun other member => increments other (List.mem_cons_of_mem _ member))
    simp only [List.length_cons]
    dsimp only at source last
    omega

/-- Raw AIR acceptance recovers a semantic trace; ranked grounding consumes every physical row. -/
theorem soundness : ensemble.Soundness (fun _ => True)
    (fun input => ∃ events, Interpretation machine boundary admissible input events) := by
  rintro input _ ⟨witness, rfl, constraints, balanced⟩
  obtain ⟨table, tables, component⟩ := one_table witness
  have rows := (witness_constraints witness table tables component).mp constraints
  have checks := (boundaryChecks.project_balanced_iff witness).mp balanced
  have endpoints := (verifier_checks witness.publicInput witness.data).mp checks.2.2
  have stateBalance := balanced state.toRaw (List.mem_append_left _ (List.mem_singleton_self _))
  change BalancedInteractions (witness.interactionsWith state.toRaw) at stateBalance
  rw [witness_ledger witness table tables component] at stateBalance
  have permutation := (state.transitionLedger_balanced_iff _ _ _ _).mp stateBalance |>.2
  have endpointBalance : RankedGrounding.EndpointBalanced (table.table : Multiset (Array F))
      (fun row => ((decodeRow row).1.val, (decodeRow row).2.val))
      witness.publicInput.1.val witness.publicInput.2.val := by
    have projected := permutation.map ZMod.val
    simpa only [RankedGrounding.EndpointBalanced, Multiset.map_coe, List.map_cons,
      List.map_map, Function.comp_def, Multiset.cons_coe] using Multiset.coe_eq_coe.mpr projected
  obtain ⟨path, walk, exhaustive⟩ := RankedGrounding.exists_exhaustiveTrail_of_endpointBalanced
    (table.table : Multiset (Array F))
    (fun row => ((decodeRow row).1.val, (decodeRow row).2.val)) id
    witness.publicInput.1.val witness.publicInput.2.val endpointBalance
    (by intro row member; have fact := rows row member
        change (decodeRow row).1.val < (decodeRow row).2.val; omega)
  have pathRows : ∀ row ∈ path, row ∈ table.table := by
    intro row member
    exact Multiset.mem_coe.mp (exhaustive ▸ Multiset.mem_coe.mpr member)
  have length := walk_length walk (fun row member => (rows row (pathRows row member)).2)
  let events := List.replicate path.length Event.increment
  have eventLength : events.length = path.length := List.length_replicate
  refine ⟨events, ?_, ?_⟩
  · change machine.Trace witness.publicInput.1.val events witness.publicInput.2.val
    rw [length, ← eventLength]
    exact trace_of_length _ _ (by rw [eventLength, ← length]; exact endpoints.2)
  · exact ⟨endpoints.1, endpoints.2, by rw [eventLength]; omega⟩

/-- Consecutive rows, with no padding. The zero-event case has no transition rows. -/
def consecutiveRows (initial : ℕ) : ℕ → List (fieldPair F)
  | 0 => []
  | count + 1 => ((initial : F), ((initial + 1 : ℕ) : F)) :: consecutiveRows (initial + 1) count

/-- Compilation emits exactly one physical transition row per event. -/
@[simp] theorem consecutiveRows_length (initial count : ℕ) :
    (consecutiveRows initial count).length = count := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih => simp only [consecutiveRows, List.length_cons, ih]

private theorem consecutiveRows_spec (initial count : ℕ) (bound : initial + count ≤ 15) :
    ∀ row ∈ consecutiveRows initial count, row.1.val < 15 ∧ row.2.val = row.1.val + 1 := by
  induction count generalizing initial with
  | zero => simp [consecutiveRows]
  | succ count ih =>
    intro row member
    rcases List.mem_cons.mp member with rfl | tail
    · simp only [ZMod.val_natCast,
        Nat.mod_eq_of_lt (show initial < 97 by omega),
        Nat.mod_eq_of_lt (show initial + 1 < 97 by omega)]
      exact ⟨by omega, trivial⟩
    · exact ih (initial + 1) (by omega) row tail

private theorem consecutiveRows_walk (initial count : ℕ) :
    Walk.IsWalk (fun row : fieldPair F => row) (initial : F) ((initial + count : ℕ) : F)
      (consecutiveRows initial count) := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
    refine ⟨rfl, ?_⟩
    have equal : initial + 1 + count = initial + (count + 1) := by omega
    simpa only [equal] using ih (initial + 1)

/-- The compiler's concrete witness obeys exactly the semantic row contracts. -/
theorem witnessOfRows_constraints (input : fieldPair F) (rows : List (fieldPair F)) :
    (witnessOfRows input rows).Constraints ↔
      ∀ row ∈ rows, row.1.val < 15 ∧ row.2.val = row.1.val + 1 := by
  have contract := witness_constraints (witnessOfRows input rows)
    ((witnessOfRows input rows).tables[0]'(by change 0 < 1; decide)) rfl rfl
  rw [contract]
  constructor
  · intro valid row member
    exact valid #[row.1, row.2] (List.mem_map.mpr ⟨row, member, rfl⟩)
  · intro valid row member
    change row ∈ rows.map (fun pair => #[pair.1, pair.2]) at member
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp member
    subst row
    exact valid pair pairMember

/-- Every row and both boundary messages occur in the actual typed-channel ledger. -/
theorem witnessOfRows_ledger (input : fieldPair F) (rows : List (fieldPair F)) :
    (witnessOfRows input rows).interactionsWith state.toRaw =
      state.transitionLedger input.1 input.2 rows id := by
  have ledger := witness_ledger (witnessOfRows input rows)
    ((witnessOfRows input rows).tables[0]'(by change 0 < 1; decide)) rfl rfl
  simpa [witnessOfRows, Channel.transitionLedger, decodeRow, List.flatMap_map] using ledger

/-- Exact physical interaction count, including both boundary interactions. -/
theorem witnessOfRows_interaction_count (input : fieldPair F) (rows : List (fieldPair F)) :
    ((witnessOfRows input rows).interactionsWith state.toRaw).length = 2 * rows.length + 2 := by
  rw [witnessOfRows_ledger]
  simp only [Channel.transitionLedger, List.length_append, List.length_cons,
    List.length_nil, List.length_flatMap]
  induction rows with
  | nil => decide
  | cons row rest ih => simp_all only [List.map_cons, List.sum_cons, List.length_cons]; omega

private theorem consecutiveRows_valid (input : fieldPair F) (count : ℕ)
    (initialBound : input.1.val ≤ 15) (finalBound : input.2.val ≤ 15)
    (length : input.2.val = input.1.val + count) :
    (witnessOfRows input (consecutiveRows input.1.val count)).Valid input := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [witnessOfRows_constraints]
    exact consecutiveRows_spec _ _ (by omega)
  · apply (boundaryChecks.project_balanced_iff _).mpr
    refine ⟨?_, boundary_count, (verifier_checks input _).mpr ⟨initialBound, finalBound⟩⟩
    intro channel member
    obtain rfl := List.mem_singleton.mp member
    change BalancedInteractions ((boundaryChecks.project (witnessOfRows input _)).interactionsWith state.toRaw)
    rw [boundaryChecks.project_interactions (ens := baseEnsemble)
      (witnessOfRows input (consecutiveRows input.1.val count)) state.toRaw check_channel_ne_state]
    rw [witnessOfRows_ledger, Channel.transitionLedger_balanced_iff]
    constructor
    · left
      simp only [consecutiveRows_length, ZMod.ringChar_zmod_n]
      omega
    · have walk := consecutiveRows_walk input.1.val count
      rw [← length, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at walk
      have endpoints := RankedGrounding.endpointBalanced_of_isWalk (fun row : fieldPair F => row) walk
      exact Multiset.coe_eq_coe.mp (by
        simpa only [RankedGrounding.EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, id_eq] using endpoints)

/-- Executable data-only compilation; invalid boundaries and incorrect event counts are rejected. -/
def compile (input : fieldPair F) (events : List Event) : Option (EnsembleWitness ensemble) :=
  if input.1.val ≤ 15 ∧ input.2.val ≤ 15 ∧ events.length ≤ 15 ∧
      input.2.val = input.1.val + events.length then
    some (witnessOfRows input (consecutiveRows input.1.val events.length))
  else none

/-- A successful compilation validates both the supplied execution and its raw AIR witness. -/
theorem compile_sound (input : fieldPair F) (events : List Event) (witness : EnsembleWitness ensemble)
    (compiled : compile input events = some witness) :
    Interpretation machine boundary admissible input events ∧ witness.Valid input := by
  unfold compile at compiled
  split at compiled
  · rename_i accepted
    obtain ⟨initialBound, finalBound, countBound, length⟩ := accepted
    obtain rfl := Option.some.inj compiled
    refine ⟨⟨?_, initialBound, finalBound, countBound⟩, ?_⟩
    · change machine.Trace input.1.val events input.2.val
      rw [length]
      exact trace_of_length _ _ (by omega)
    · exact consecutiveRows_valid input _ initialBound finalBound length
  · contradiction

/-- Every admissible semantic trace compiles; no readiness premise is required. -/
theorem compile_complete (input : fieldPair F) (events : List Event)
    (execution : Interpretation machine boundary admissible input events) :
    ∃ witness, compile input events = some witness := by
  obtain ⟨trace, initialBound, finalBound, countBound⟩ := execution
  have length := trace_length trace
  exact ⟨_, if_pos ⟨initialBound, finalBound, countBound, length⟩⟩

/-- The closed proof-independent compiler interface. -/
def compiler : EnsembleCompiler ensemble (List Event) (Interpretation machine boundary admissible) where
  compile := compile
  sound := compile_sound
  complete := compile_complete

/-- Complete soundness and constructive completeness of the actual Clean ensemble. -/
def realizes : Realizes machine ensemble boundary admissible where
  sound := soundness
  compiler := compiler

/-- The raw AIR language is exactly the independently defined admissible trace language. -/
theorem statement_iff (input : fieldPair F) :
    ensemble.Statement input ↔ ∃ events,
      machine.Trace (boundary input).1 events (boundary input).2 ∧ admissible input events :=
  realizes.statement_iff input

/-- The semantic budget implies the exact compiler State count fits strictly below the characteristic. -/
theorem compiled_interaction_bound (input : fieldPair F) (events : List Event)
    (admitted : admissible input events) :
    ((witnessOfRows input (consecutiveRows input.1.val events.length)).interactionsWith state.toRaw).length
      = 2 * events.length + 2 ∧ 2 * events.length + 2 ≤ 32 ∧ (32 : ℕ) < 97 := by
  rw [witnessOfRows_interaction_count, consecutiveRows_length]
  exact ⟨rfl, by have bound := admitted.2.2; omega, by decide⟩

end SP1Clean.Soundness.CounterExample
