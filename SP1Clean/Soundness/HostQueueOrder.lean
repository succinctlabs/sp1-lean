import SP1Clean.Soundness.HostHintReadCoverage
import SP1Clean.Proofs.Chips.HostHintLengthChip.Ledger

/-! # Queue chronology from the physical HINT_LEN and HINT_READ tables

The implemented queue handlers each replace one complete queue token, including its allocation
frontier. Strict event clocks turn their actual balanced ledger into an exhaustive ordered path.
Boundary messages are explicit here: a ledger containing only these transitions can balance
only when all three tables are empty. Source-record providers do not supply queue endpoints.
The path retains head/frontier continuity; semantic queue truth and future allocating handlers
must be connected by the enclosing execution argument.
-/

namespace SP1Clean.Soundness.HostQueueOrder

open Circuit Air.Flat HostHintQueue RankedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem eval_read_queue (env : Environment (ZMod p)) (row : Var HostHintReadChip.Inputs (ZMod p)) :
    eval env row.previous = (eval env row).previous ∧ eval env row.next = (eval env row).next := by
  rcases row with ⟨call, previous, node, span, lastIndex, lastValue⟩
  cases call
  cases previous
  cases node
  simp only [HostHintReadChip.Inputs.next, circuit_norm, and_self]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_length_queue (env : Environment (ZMod p)) (row : Var HostHintLengthChip.Inputs (ZMod p)) :
    eval env row.previous = (eval env row).previous ∧ eval env row.next = (eval env row).next := by
  rcases row with ⟨call, previous, node⟩
  cases call
  cases previous
  simp only [HostHintLengthChip.Inputs.next, circuit_norm, and_self]

def readView : TransitionView (stateChannel (p := p)) where
  component := HostHintReadCoverage.handler
  edge env := let row := HostHintReadCoverage.input env; (row.previous, row.next)
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
      (size HostHintReadChip.Inputs)).interactionValuesWith stateChannel.toRaw env = _
    rw [HostHintReadChip.queue_values, (eval_read_queue _ _).1, (eval_read_queue _ _).2,
      eval_varFromOffset_valueFromOffset]
    rfl

def lengthView (empty : Bool) : TransitionView (stateChannel (p := p)) where
  component := { circuit := HostHintLengthChip.circuit empty }
  edge env := let row := valueFromOffset HostHintLengthChip.Inputs 0 env; (row.previous, row.next)
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHintLengthChip.main empty (varFromOffset HostHintLengthChip.Inputs 0)).operations
      (size HostHintLengthChip.Inputs)).interactionValuesWith stateChannel.toRaw env = _
    rw [HostHintLengthChip.state_values, (eval_length_queue _ _).1, (eval_length_queue _ _).2,
      eval_varFromOffset_valueFromOffset]

/-- The current queue-changing/observing registry; allocating WRITE/hook handlers remain open. -/
abbrev Index := Option Bool

def indices : List Index := [none, some false, some true]

def view : Index → TransitionView (stateChannel (p := p))
  | none => readView
  | some empty => lengthView empty

abbrev Row := Index × Environment (ZMod p)

def edge (row : Row (p := p)) : State (ZMod p) × State (ZMod p) := (view row.1).edge row.2

def time (state : State (ZMod p)) : ℕ := Semantics.clkNat state.clk_high state.clk_low

omit [Fact (2 ^ 25 < p)] in
private theorem read_strict (input : HostHintReadChip.Inputs (ZMod p)) (valid : HostHintReadChip.Spec input) :
    time input.previous < time input.next := valid.2.2.2.2.2.2.2.1.2.2.2.2

omit [Fact (2 ^ 25 < p)] in
private theorem length_strict (empty : Bool) (input : HostHintLengthChip.Inputs (ZMod p))
    (valid : HostHintLengthChip.Spec empty input) : time input.previous < time input.next := valid.2.2.1.2.2.2.2

theorem view_strict (index : Index) (env : Environment (ZMod p)) (valid : (view index).component.Spec env) :
    time ((view index).edge env).1 < time ((view index).edge env).2 := by
  cases index with
  | none => exact read_strict (HostHintReadCoverage.input env) valid
  | some empty => exact length_strict empty (valueFromOffset HostHintLengthChip.Inputs 0 env) valid

theorem rows_spec (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables)
    (valid : ∀ table ∈ tables, table.Spec data) :
    ∀ row ∈ TransitionView.readIndexedRows indices tables data, (view row.1).component.Spec row.2 := by
  apply TransitionView.readIndexedRows_spec indices view tables data _ valid
  simpa only [List.forall₂_map_left_iff] using aligned

/-- Every occurrence of a physical queue row contributes exactly one complete token pair. -/
theorem interactions (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables) :
    tables.flatMap (·.interactionsWith data stateChannel.toRaw) =
      (TransitionView.readIndexedRows indices tables data).flatMap (fun row =>
        [stateChannel.pulledValue (edge row).1, stateChannel.pushedValue (edge row).2]) := by
  rw [TransitionView.readIndexedRows_interactions indices (fun index => (view index).component) tables data _ aligned]
  apply List.flatMap_congr
  intro row _
  exact (view row.1).interactions row.2

/-- Actual token balance orders all queue rows, retaining head and allocation-frontier continuity.
The enclosing verifier must supply and bind both endpoint messages. -/
theorem ordered (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables)
    (valid : ∀ table ∈ tables, table.Spec data) (initial final : State (ZMod p))
    (balanced : BalancedInteractions ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
      tables.flatMap (·.interactionsWith data stateChannel.toRaw))) :
    ∃ path : List (Row (p := p)), path.Perm (TransitionView.readIndexedRows indices tables data) ∧
      Walk.IsWalk edge initial final path := by
  classical
  rw [interactions tables data aligned] at balanced
  change BalancedInteractions (stateChannel.transitionLedger initial final
    (TransitionView.readIndexedRows indices tables data) edge) at balanced
  have endpoints := (stateChannel.transitionLedger_balanced_iff _ _ _ _).mp balanced
  have balance : EndpointBalanced (↑(TransitionView.readIndexedRows indices tables data)) edge initial final := by
    simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints.2
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑(TransitionView.readIndexedRows indices tables data)) edge time initial final
    balance (fun row member =>
      view_strict row.1 row.2 (rows_spec tables data aligned valid row (Multiset.mem_coe.mp member)))
  exact ⟨path, Multiset.coe_eq_coe.mp exhaustive, walk⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem nil_of_strict_balance {R V : Type*} (edge : R → V × V) (rank : V → ℕ) (rows : List R)
    (closed : (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)))
    (strict : ∀ row ∈ rows, rank (edge row).1 < rank (edge row).2) : rows = [] := by
  classical
  cases rows with
  | nil => rfl
  | cons row rest =>
    have endpoints : EndpointBalanced (↑(row :: rest)) edge (edge row).1 (edge row).1 := by
      exact Quot.sound (closed.cons (edge row).1)
    have empty := eq_zero_of_endpointBalanced_self _ edge rank
      (fun row member => strict row (Multiset.mem_coe.mp member)) endpoints
    simp at empty

/-- Omitting queue endpoints forbids every active HINT_LEN/HINT_READ row; record sources alone
cannot establish non-vacuity of the complete ensemble relation. -/
theorem rows_nil_of_balanced (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables)
    (valid : ∀ table ∈ tables, table.Spec data)
    (balanced : BalancedInteractions (tables.flatMap (·.interactionsWith data stateChannel.toRaw))) :
    TransitionView.readIndexedRows indices tables data = [] := by
  classical
  rw [interactions tables data aligned] at balanced
  have closed := (stateChannel.pairedLedger_balanced_iff
    (TransitionView.readIndexedRows indices tables data) edge).mp balanced
  exact nil_of_strict_balance edge time _ closed.2
    (fun row member => view_strict row.1 row.2 (rows_spec tables data aligned valid row member))

/-- The present queue clock encoding cannot represent a queue handler at event time zero.
This agrees with SP1's active 1-mod-8 profile; range-only source checks also admit identities at zero. -/
theorem positive_event_time (index : Index) (env : Environment (ZMod p))
    (valid : (view index).component.Spec env) : 0 < time ((view index).edge env).2 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (view_strict index env valid)

end SP1Clean.Soundness.HostQueueOrder
