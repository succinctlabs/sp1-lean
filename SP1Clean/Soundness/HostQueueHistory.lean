import SP1Clean.Soundness.HintQueueHistory
import SP1Clean.Soundness.HostQueueOrder
import SP1Clean.Soundness.HostHintReadLocalExecution
import SP1Clean.Soundness.HostHintReadLocalQueue
import SP1Clean.Proofs.Chips.HostHintLengthChip.Bridge

/-! # Current queue truth for the implemented physical handlers

Actual HINT_LEN and HINT_READ rows determine semantic queue events. Authenticated records in a
later persistent inventory restrict to the current frontier before each step. The generic history
engine allows growing stores; the currently implemented handlers preserve the allocation inventory.
WRITE/hook allocations need their own authenticated local advance and ordering proofs.
-/

namespace SP1Clean.Soundness.HostQueueHistory

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintQueue HostQueueOrder

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def event (row : Row (p := p)) : Event :=
  match row.1 with
  | none => .read (Word.toNat (HostHintReadCoverage.input row.2).call.arg2)
  | some _ => .length (Word.toBitVec64 (valueFromOffset HostHintLengthChip.Inputs 0 row.2).call.result)

def Records (store : Store) (row : Row (p := p)) : Prop :=
  match row.1 with
  | none => (HostHintReadCoverage.input row.2).node.Binds store ∧
      (HostHintReadCoverage.input row.2).endStep.word.Binds store
  | some empty => empty = false → (valueFromOffset HostHintLengthChip.Inputs 0 row.2).node.Binds store

private theorem read_edge (env : Environment (ZMod p)) :
    edge (none, env) = ((HostHintReadCoverage.input env).previous, (HostHintReadCoverage.input env).next) := rfl

private theorem length_edge (empty : Bool) (env : Environment (ZMod p)) :
    edge (some empty, env) = ((valueFromOffset HostHintLengthChip.Inputs 0 env).previous,
      (valueFromOffset HostHintLengthChip.Inputs 0 env).next) := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem read_advance (input : HostHintReadChip.Inputs (ZMod p)) (valid : HostHintReadChip.Spec input)
    (upper store : Store) (hints : List Bytes) (bounded : Extends store upper)
    (header : input.node.Binds upper) (ending : input.endStep.word.Binds upper)
    (current : input.previous.Binds store hints) :
    ∃ nextHints, (Event.read (Word.toNat input.call.arg2)).apply? hints = some nextHints ∧
      input.next.Binds store nextHints := by
  have head := valid.2.2.2.2.2.2.1
  have bound : Address.toNat input.node.pointer ≤ store.size := by
    rw [← head]
    exact current.2.2.2.bound
  obtain ⟨node, rest, _, hintsEq, next, count, _⟩ := HostHintReadChip.node_effect_of_spec input valid
    store hints current (header.restrict bounded bound) (ending.restrict bounded bound)
  exact ⟨rest, by simp only [Event.apply?, hintsEq, count, ↓reduceIte], next⟩

omit [Fact (2 ^ 25 < p)] in
private theorem length_advance [Fact (2 ^ 17 < p)] (empty : Bool) (input : HostHintLengthChip.Inputs (ZMod p))
    (valid : HostHintLengthChip.Spec empty input) (upper store : Store) (hints : List Bytes)
    (bounded : Extends store upper) (header : empty = false → input.node.Binds upper)
    (current : input.previous.Binds store hints) :
    (Event.length (Word.toBitVec64 input.call.result)).apply? hints = some hints ∧
      input.next.Binds store hints := by
  have binding : empty = false → input.node.Binds store := by
    intro nonempty
    subst empty
    have head : input.previous.head = input.node.pointer := valid.2.2.2.1
    apply (header rfl).restrict bounded
    rw [← head]
    exact current.2.2.2.bound
  have result := HostHintLengthChip.result_of_spec empty input valid
    { io := ⟨hints, []⟩ } store current.2.2.2 binding
  exact ⟨by simp only [Event.apply?, result, ↓reduceIte], HostHintLengthChip.next_binds input store hints current⟩

/-- Actual row contracts turn authenticated later records into a valid current-queue step. -/
theorem advance (row : Row (p := p)) (upper : Store)
    (valid : (view row.1).component.Spec row.2) (records : Records upper row) :
    HintQueueHistory.Advances edge event upper row := by
  intro store hints bounded current
  rcases row with ⟨index, env⟩
  cases index with
  | none =>
    change HostHintReadChip.Spec (HostHintReadCoverage.input env) at valid
    change (HostHintReadCoverage.input env).node.Binds upper ∧
      (HostHintReadCoverage.input env).endStep.word.Binds upper at records
    simp only [read_edge, event] at current ⊢
    obtain ⟨nextHints, applied, next⟩ := read_advance (HostHintReadCoverage.input env) valid
      upper store hints bounded records.1 records.2 current
    exact ⟨store, nextHints, .refl _, bounded, applied, next⟩
  | some empty =>
    change HostHintLengthChip.Spec empty (valueFromOffset HostHintLengthChip.Inputs 0 env) at valid
    change empty = false → (valueFromOffset HostHintLengthChip.Inputs 0 env).node.Binds upper at records
    simp only [length_edge, event] at current ⊢
    have step := length_advance empty (valueFromOffset HostHintLengthChip.Inputs 0 env) valid
      upper store hints bounded records current
    exact ⟨store, hints, .refl _, bounded, step⟩

private theorem length_record (env : Environment (ZMod p)) :
    (lengthView false).component.operations.interactionValuesWith nodeChannel.toRaw env =
      [nodeChannel.pulledValue (valueFromOffset HostHintLengthChip.Inputs 0 env).node] := by
  have evalNode (input : Var HostHintLengthChip.Inputs (ZMod p)) :
      eval env input.node = (eval env input).node := by
    rcases input with ⟨call, previous, node⟩
    cases node
    simp only [circuit_norm]
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HostHintLengthChip.main false (varFromOffset HostHintLengthChip.Inputs 0)).operations
    (size HostHintLengthChip.Inputs)).interactionValuesWith nodeChannel.toRaw env = _
  rw [HostHintLengthChip.node_values, evalNode, eval_varFromOffset_valueFromOffset]
  rfl

open HostHintReadLocal

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

private theorem pull_mem
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (row : Row (p := p)) (member : row ∈ TransitionView.readIndexedRows indices (queueTables witness) witness.data)
    (channel : RawChannel (ZMod p)) (interaction : Interaction (ZMod p))
    (present : interaction ∈ (view row.1).component.operations.interactionValuesWith channel row.2) :
    interaction ∈ witness.interactionsWith channel := by
  have inside : interaction ∈ (queueTables witness).flatMap (·.interactionsWith witness.data channel) := by
    rw [TransitionView.readIndexedRows_interactions indices (fun index => (view index).component)
      _ witness.data _ (queueTables_aligned witness)]
    exact List.mem_flatMap.mpr ⟨row, member, present⟩
  obtain ⟨table, tableMem, present⟩ := List.mem_flatMap.mp inside
  exact EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨table, queueTables_mem witness table tableMem, present⟩)

/-- Authentication follows the very node/word pulls made by each physical queue row. -/
theorem records_of_witness
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (store : Store) (authenticated : RecordAuthentication witness store) (balanced : RecordChannels witness)
    (row : Row (p := p)) (member : row ∈ TransitionView.readIndexedRows indices (queueTables witness) witness.data) :
    Records store row := by
  rcases row with ⟨index, env⟩
  cases index with
  | none =>
    constructor
    · apply (node_authenticated witness store authenticated balanced.node _ ?_).2
      apply pull_mem witness (none, env) member
      change _ ∈ HostHintReadCoverage.handler.operations.interactionValuesWith nodeChannel.toRaw env
      rw [(handler_records env).1]
      exact List.mem_cons_self ..
    · apply (word_authenticated witness store authenticated balanced.word _ ?_).2
      apply pull_mem witness (none, env) member
      change _ ∈ HostHintReadCoverage.handler.operations.interactionValuesWith wordChannel.toRaw env
      rw [(handler_records env).2]
      exact List.mem_cons_self ..
  | some empty =>
    intro nonempty
    subst empty
    apply (node_authenticated witness store authenticated balanced.node _ ?_).2
    apply pull_mem witness (some false, env) member
    rw [show (view (some false)).component = (lengthView false).component from rfl, length_record]
    exact List.mem_cons_self ..

end SP1Clean.Soundness.HostQueueHistory
