import SP1Clean.Proofs.Chips.HintReadWordChip.Ledger
import SP1Clean.Soundness.RankedGrounding
import ToClean.Air.TransitionView
import ToClean.Air.MessageFilter

/-! # Complete successive hint word coverage from physical table balance

Both consumer variants contribute their actual cursor edges. Unit balance and exact natural
index successors yield an exhaustive path with precisely the consecutive index inventory.
The cursor retains the clock and node throughout. Endpoint authentication, immutable word
binding, and installation in the mixed ensemble are separate integration obligations.
-/

namespace SP1Clean.Soundness.HintReadCoverage

open Circuit Air.Flat HintReadWordChip RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_previous (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  simp only [Inputs.previous, Inputs.address, HostRamAccessChip.Inputs.clockLow, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_next (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.next = (Eval.eval env input).next := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  simp only [Inputs.next, HostRamAccessChip.Inputs.clockLow, circuit_norm]

def view (last : Bool) : TransitionView (stateChannel (p := p)) where
  component := { circuit := HintReadWordChip.circuit last }
  edge env :=
    let input := valueFromOffset Inputs 0 env
    (input.previous, input.next)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, HintReadWordChip.circuit]
    rw [main_state_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
      eval_previous, eval_next, eval_varFromOffset_valueFromOffset]

def variants : List Bool := [false, true]

abbrev Row := Bool × Environment (ZMod p)

def rowInput (row : Row (p := p)) : Inputs (ZMod p) := valueFromOffset Inputs 0 row.2

def edge (row : Row (p := p)) : State (ZMod p) × State (ZMod p) :=
  ((rowInput row).previous, (rowInput row).next)

def context (state : State (ZMod p)) := (state.clk_high, state.clk_low, state.pointer)

theorem rows_spec (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec data) :
    ∀ row ∈ TransitionView.readIndexedRows variants tables data, Spec row.1 (rowInput row) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  exact TransitionView.readIndexedRows_spec variants view tables data alignment valid

/-- Coverage uses authenticated words and exact index/address successors. The prior RAM values
and timestamps are separate facts to be established by Memory grounding. -/
def Steps (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) : Prop :=
  ∀ row ∈ TransitionView.readIndexedRows variants tables data,
    HintReadStep.Spec row.1 ((rowInput row).step row.1)

theorem steps_of_specs (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec data) : Steps tables data :=
  fun row member => (rows_spec tables data aligned valid row member).2

/-- Registered word components have no fixed columns, so selecting complete rows preserves
all fixed-column obligations. This is derived from the component registry. -/
theorem selection_fixed (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (keep : Bool → Environment (ZMod p) → Bool)
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables) :
    ∀ last table, (last, table) ∈ variants.zip tables → table.component.fixedRowsMatch
      (table.table.filter fun row => keep last (Environment.fromArray row data)) := by
  intro last table paired
  rw [← List.forall₂_zip aligned paired]
  trivial

omit [Fact (2 ^ 25 < p)] in
/-- Selecting one call retains exactly the corresponding word-step facts. -/
theorem Steps.select {tables : List (Table (ZMod p))} {data : ProverData (ZMod p)}
    (valid : Steps tables data) (keep : Bool → Environment (ZMod p) → Bool)
    (fixed : ∀ last table, (last, table) ∈ variants.zip tables → table.component.fixedRowsMatch
      (table.table.filter fun row => keep last (Environment.fromArray row data))) :
    Steps (TransitionView.selectTables variants tables data keep fixed) data := by
  intro row member
  rw [TransitionView.readIndexedRows_selectTables] at member
  exact valid row (List.mem_filter.mp member).1

theorem rows_balanced (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component)
      variants tables)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith data stateChannel.toRaw))) :
    EndpointBalanced (↑(TransitionView.readIndexedRows variants tables data)) edge initial final := by
  let rows := TransitionView.readIndexedRows variants tables data
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions
    (variants.map view) tables data alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected] at balanced
  change BalancedInteractions (stateChannel.transitionLedger initial final rows edge) at balanced
  have endpoints := (stateChannel.transitionLedger_balanced_iff initial final rows edge).mp balanced
  simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe]
    using endpoints.2

omit [Fact (2 ^ 25 < p)] in
private theorem indices_of_walk {R V : Type*} (edge : R → V × V) (index : V → ℕ)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (step : ∀ row ∈ path, index (edge row).2 = index (edge row).1 + 1) :
    index final = index initial + path.length ∧
      path.map (fun row => index (edge row).1) = List.range' (index initial) path.length := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have successor := step row (List.mem_cons_self ..)
    rw [source] at successor
    have result := ih _ tail (fun other member => step other (List.mem_cons_of_mem _ member))
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    rw [List.map_cons, source, result.2, successor, List.length_cons, List.range'_succ]

omit [Fact (2 ^ 25 < p)] in
private theorem context_of_walk {R V C : Type*} (edge : R → V × V) (context : V → C)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (preserve : ∀ row ∈ path, context (edge row).2 = context (edge row).1) :
    context final = context initial ∧ ∀ row ∈ path, context (edge row).1 = context initial := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have same := preserve row (List.mem_cons_self ..)
    rw [source] at same
    have result := ih _ tail (fun other member => preserve other (List.mem_cons_of_mem _ member))
    refine ⟨result.1.trans same, ?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [source]
    · exact (result.2 other member).trans same

omit [Fact (2 ^ 25 < p)] in
private theorem successor_of_spec (last : Bool) (input : Inputs (ZMod p))
    (valid : HintReadStep.Spec last (input.step last)) :
    Address.toNat input.next.index = Address.toNat input.previous.index + 1 := valid.2.2.2.2.1

omit [Fact (2 ^ 25 < p)] in
private theorem ranked_cover {R V C : Type*} (edge : R → V × V) (index : V → ℕ) (context : V → C)
    (rows : List R) (initial final : V) (balance : EndpointBalanced (↑rows) edge initial final)
    (successors : ∀ row ∈ rows, index (edge row).2 = index (edge row).1 + 1)
    (preserve : ∀ row ∈ rows, context (edge row).2 = context (edge row).1) :
    ∃ path : List R, path.Perm rows ∧ Walk.IsWalk edge initial final path ∧
      index final = index initial + path.length ∧
      path.map (fun row => index (edge row).1) = List.range' (index initial) path.length ∧
      context final = context initial ∧ ∀ row ∈ path, context (edge row).1 = context initial := by
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑rows) edge index initial final balance (by
      intro row member
      rw [successors row (Multiset.mem_coe.mp member)]
      omega)
  have perm : path.Perm rows := Multiset.coe_eq_coe.mp exhaustive
  have indices := indices_of_walk edge index initial final path walk
    (fun row member => successors row (perm.mem_iff.mp member))
  have same := context_of_walk edge context initial final path walk
    (fun row member => preserve row (perm.mem_iff.mp member))
  exact ⟨path, perm, walk, indices.1, indices.2, same.1, same.2⟩

omit [Fact (2 ^ 25 < p)] in
private theorem context_preserve (input : Inputs (ZMod p)) : context input.next = context input.previous := rfl

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem nil_of_closed {R V : Type*} (edge : R → V × V) (index : V → ℕ) (rows : List R)
    (closed : (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)))
    (successors : ∀ row ∈ rows, index (edge row).2 = index (edge row).1 + 1) : rows = [] := by
  classical
  cases rows with
  | nil => rfl
  | cons row rest =>
    have balanced : EndpointBalanced (↑(row :: rest)) edge (edge row).1 (edge row).1 := by
      simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using
        closed.cons (edge row).1
    have empty := eq_zero_of_endpointBalanced_self (↑(row :: rest)) edge index
      (fun current member => by rw [successors current (Multiset.mem_coe.mp member)]; omega) balanced
    simp at empty

/-- A balanced set of consumers without any handler endpoints must be empty. -/
theorem rows_nil_of_balanced (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : Steps tables data)
    (balanced : BalancedInteractions (tables.flatMap (·.interactionsWith data stateChannel.toRaw))) :
    TransitionView.readIndexedRows variants tables data = [] := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions (variants.map view) tables data alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected] at balanced
  have closed := (stateChannel.pairedLedger_balanced_iff
    (TransitionView.readIndexedRows variants tables data) edge).mp balanced
  exact nil_of_closed edge (fun state : State (ZMod p) => Address.toNat state.index)
    (TransitionView.readIndexedRows variants tables data) closed.2
    (fun row member => successor_of_spec row.1 (rowInput row) (valid row member))

/-- Every physical word row occurs exactly once, with successive indices and a fixed call/node.
Authenticated word-step contracts and ledger balance determine the order internally. -/
theorem ordered_cover (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : Steps tables data)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith data stateChannel.toRaw))) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows variants tables data) ∧
      Walk.IsWalk edge initial final path ∧
      Address.toNat final.index = Address.toNat initial.index + path.length ∧
      path.map (fun row => Address.toNat (rowInput row).index) =
        List.range' (Address.toNat initial.index) path.length ∧
      context final = context initial ∧
      ∀ row ∈ path, context (rowInput row).previous = context initial := by
  apply ranked_cover edge (fun state : State (ZMod p) => Address.toNat state.index) context
    (TransitionView.readIndexedRows variants tables data) initial final
    (rows_balanced tables data initial final aligned balanced)
  · intro row member
    exact successor_of_spec row.1 (rowInput row) (valid row member)
  · intro row _
    exact context_preserve (rowInput row)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem lower_of_walk {R V : Type*} (edge : R → V × V) (address : V → ℕ)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (steps : ∀ row ∈ path, address (edge row).1 ≤ address (edge row).2) :
    ∀ row ∈ path, address initial ≤ address (edge row).1 := by
  induction path generalizing initial with
  | nil => simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [source]
    · exact le_trans (by rw [← source]; exact steps row (List.mem_cons_self ..))
        (ih _ tail (fun r h => steps r (List.mem_cons_of_mem _ h)) other member)

/-- Every consumer address is at least the handler's start address. This needs only the
authenticated successor constraints, independently of the prior RAM word or timestamp. -/
theorem address_lower (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : Steps tables data)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith data stateChannel.toRaw))) :
    ∀ row ∈ TransitionView.readIndexedRows variants tables data,
      Address.toNat initial.address ≤ Address.toNat (rowInput row).address := by
  obtain ⟨path, perm, walk, _⟩ := ordered_cover tables data initial final aligned valid balanced
  have lower := lower_of_walk edge (fun state : State (ZMod p) => Address.toNat state.address)
    initial final path walk (by
      intro row member
      have advance := (valid row (perm.mem_iff.mp member)).2.2.2.2.2.2
      change Address.toNat (rowInput row).address ≤ Address.toNat (rowInput row).nextAddress
      change Address.toNat (rowInput row).nextAddress = Address.toNat (rowInput row).address + _ at advance
      omega)
  exact fun row member => lower row (perm.mem_iff.mpr member)

/-- Zero-based endpoints force exactly the full count, independently of physical row order. -/
theorem complete_indices (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : Steps tables data)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith data stateChannel.toRaw)))
    (zero : Address.toNat initial.index = 0) :
    ((TransitionView.readIndexedRows variants tables data).map fun row => Address.toNat (rowInput row).index).Perm
      (List.range (Address.toNat final.index)) := by
  obtain ⟨path, perm, _, count, indices, _⟩ := ordered_cover tables data initial final aligned valid balanced
  rw [zero, Nat.zero_add] at count
  rw [zero, ← List.range_eq_range'] at indices
  rw [count, ← indices]
  exact (perm.map _).symm

/-- A constructed complete cursor walk balances the physical tables under Clean's count guard. -/
theorem balanced_of_walk (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (path : List (Row (p := p))) (perm : path.Perm (TransitionView.readIndexedRows variants tables data))
    (walk : Walk.IsWalk edge initial final path) (bound : 2 * (path.length + 1) < p) :
    BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith data stateChannel.toRaw)) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions (variants.map view) tables data alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected]
  change BalancedInteractions (stateChannel.transitionLedger initial final
    (TransitionView.readIndexedRows variants tables data) edge)
  apply (stateChannel.transitionLedger_balanced_iff _ _ _ _).mpr
  refine ⟨Or.inl ?_, ?_⟩
  · simpa only [← perm.length_eq, ZMod.ringChar_zmod_n] using bound
  · have endpoints := endpointBalanced_of_isWalk edge walk
    have endpointPerm : (initial :: path.map (fun row => (edge row).2)).Perm
        (final :: path.map (fun row => (edge row).1)) := by
      simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints
    exact ((perm.map (fun row => (edge row).2)).cons initial).symm.trans
      (endpointPerm.trans ((perm.map (fun row => (edge row).1)).cons final))

end SP1Clean.Soundness.HintReadCoverage
