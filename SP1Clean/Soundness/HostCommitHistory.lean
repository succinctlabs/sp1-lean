import SP1Clean.Proofs.Chips.HostCommitChip.Ledger
import SP1Clean.Proofs.Chips.HostCommitChip.Bridge
import SP1Clean.Soundness.RankedGrounding
import ToClean.Air.TransitionView

/-! # Ordered mutable commitment histories from physical bank tables

The eight slot components share one bank channel. Their actual balanced ledger, including explicit
initial/final records and Clean's count bound, yields an exhaustive chronological history. Folding
that history through the independent host interpreter gives the final bank and frames all other
host state. The enclosing machine must authenticate the endpoints, discharge local table specs,
and balance the instruction handoffs; these are not conclusions of this subsystem theorem.
-/

namespace SP1Clean.Soundness.HostCommitHistory

open Circuit Air.Flat SP1Clean.HostCommitChip SP1Clean.Model.Core RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem eval_previous (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨call, previous, comparison, bytes⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_next (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) (slot : Fin 8) :
    Eval.eval env (input.next slot) = (Eval.eval env input).next slot := by
  rcases input with ⟨call, previous, comparison, bytes⟩
  rcases call with ⟨high, low, code, arg1, arg2, result, length⟩
  rcases previous with ⟨previousHigh, previousLow, values⟩
  simp only [Inputs.next, circuit_norm, eval_vector, Vector.map_set, ProvableType.eval_fields]

def view (deferred : Bool) (slot : Fin 8) : TransitionView (stateChannel (p := p) deferred) where
  component := { circuit := HostCommitChip.circuit deferred slot }
  edge env :=
    let input := valueFromOffset Inputs 0 env
    (input.previous, input.next slot)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, HostCommitChip.circuit]
    rw [main_state_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
      eval_previous, eval_next, eval_varFromOffset_valueFromOffset]

abbrev Row := Fin 8 × Environment (ZMod p)

def rowInput (row : Row (p := p)) : Inputs (ZMod p) := valueFromOffset Inputs 0 row.2

def edge (row : Row (p := p)) : State (ZMod p) × State (ZMod p) :=
  ((rowInput row).previous, (rowInput row).next row.1)

/-- Execute a bank history through the independent host interpreter. Every input is a physical row. -/
def execute (deferred : Bool) (policy : HostPolicy) (context : HostReadContext)
    (host : HostState) (row : Row (p := p)) : Option HostState :=
  let call := (rowInput row).call
  (host.executeKind policy context (if deferred then .commitDeferred else .commit)
    (Word.toBitVec64 call.arg1) (Word.toBitVec64 call.arg2)).map (·.state)

private theorem fold_of_walk (deferred : Bool) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext) (host : HostState)
    (initial final : State (ZMod p)) (path : List (Row (p := p)))
    (valid : ∀ row ∈ path, Spec deferred row.1 (rowInput row))
    (walk : Walk.IsWalk edge initial final path) :
    path.foldlM (execute deferred policy context) (initial.apply deferred host) =
      some (final.apply deferred host) := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    rfl
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have step := executeKind_of_spec deferred row.1 (rowInput row)
      (valid row (List.mem_cons_self ..)) host policy characteristic context
    change (rowInput row).previous = initial at source
    rw [source] at step
    simp only [List.foldlM_cons, execute, step, Option.map_some]
    exact ih _ (fun other member => valid other (List.mem_cons_of_mem _ member)) tail

private theorem rows_spec (deferred : Bool) (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun slot table => (view deferred slot).component = table.component)
      (List.finRange 8) tables) (valid : ∀ table ∈ tables, table.Spec data) :
    ∀ row ∈ TransitionView.readIndexedRows (List.finRange 8) tables data,
      Spec deferred row.1 (rowInput row) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      ((List.finRange 8).map (view deferred)) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  exact TransitionView.readIndexedRows_spec (List.finRange 8) (view deferred) tables data alignment valid

private theorem rows_balanced (deferred : Bool) (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun slot table => (view deferred slot).component = table.component)
      (List.finRange 8) tables)
    (balanced : BalancedInteractions
      ([(stateChannel deferred).pushedValue initial, (stateChannel deferred).pulledValue final] ++
        tables.flatMap (·.interactionsWith data (stateChannel deferred).toRaw))) :
    EndpointBalanced (↑(TransitionView.readIndexedRows (List.finRange 8) tables data)) edge initial final := by
  let rows := TransitionView.readIndexedRows (List.finRange 8) tables data
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      ((List.finRange 8).map (view deferred)) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions
    ((List.finRange 8).map (view deferred)) tables data alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected] at balanced
  change BalancedInteractions ((stateChannel deferred).transitionLedger initial final rows edge) at balanced
  have endpoints := ((stateChannel deferred).transitionLedger_balanced_iff initial final rows edge).mp balanced
  simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe]
    using endpoints.2

private theorem strict_of_spec (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p))
    (valid : Spec deferred slot input) :
    Semantics.clkNat input.previous.clk_high input.previous.clk_low <
      Semantics.clkNat (input.next slot).clk_high (input.next slot).clk_low :=
  valid.2.1.2.2.2.2

private theorem history_of_balance (deferred : Bool) (rows : List (Row (p := p)))
    (initial final : State (ZMod p)) (valid : ∀ row ∈ rows, Spec deferred row.1 (rowInput row))
    (balanced : EndpointBalanced (↑rows) edge initial final)
    (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) (host : HostState) :
    ∃ path : List (Row (p := p)), path.Perm rows ∧ Walk.IsWalk edge initial final path ∧
      path.foldlM (execute deferred policy context) (initial.apply deferred host) =
        some (final.apply deferred host) := by
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced (↑rows) edge
    (fun state => Semantics.clkNat state.clk_high state.clk_low) initial final balanced
    (by
      intro row member
      change Semantics.clkNat (rowInput row).previous.clk_high (rowInput row).previous.clk_low <
        Semantics.clkNat ((rowInput row).next row.1).clk_high ((rowInput row).next row.1).clk_low
      exact strict_of_spec deferred row.1 (rowInput row) (valid row (Multiset.mem_coe.mp member)))
  have perm : path.Perm rows := Multiset.coe_eq_coe.mp exhaustive
  refine ⟨path, perm, walk, fold_of_walk deferred policy characteristic context host initial final path ?_ walk⟩
  intro row member
  exact valid row (perm.mem_iff.mp member)

/-- Balanced physical bank tables execute every row exactly once and produce their final bank.
The endpoint and local-spec premises are explicit integration boundaries. -/
theorem ordered_history (deferred : Bool) (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun slot table => (view deferred slot).component = table.component)
      (List.finRange 8) tables)
    (valid : ∀ table ∈ tables, table.Spec data)
    (balanced : BalancedInteractions
      ([(stateChannel deferred).pushedValue initial, (stateChannel deferred).pulledValue final] ++
        tables.flatMap (·.interactionsWith data (stateChannel deferred).toRaw)))
    (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) (host : HostState) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows (List.finRange 8) tables data) ∧
      Walk.IsWalk edge initial final path ∧
      path.foldlM (execute deferred policy context) (initial.apply deferred host) =
        some (final.apply deferred host) := by
  exact history_of_balance deferred _ initial final (rows_spec deferred tables data aligned valid)
    (rows_balanced deferred tables data initial final aligned balanced) policy characteristic context host

end SP1Clean.Soundness.HostCommitHistory
