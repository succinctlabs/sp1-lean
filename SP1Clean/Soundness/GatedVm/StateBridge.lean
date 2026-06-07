import SP1Clean.Soundness.GatedVm.Chain
import SP1Clean.Soundness.StateConsistency

/-! # SP1 state bus ⇒ `GatedVm.Balanced`: instantiating the Eulerian core

Connects the abstract balance⇒trail core (`GatedVm.exists_trail` in `Chain.lean`) to SP1's concrete
state bus (`Soundness/StateConsistency.lean`). Each real row is the directed edge
`receiveKey → sendKey` (its current state → next state); the verifier boundary contributes a genesis
production of the public initial key and a finalization consumption of the public final key. We show
the native multiset balance `isConsistentBalanced` (per-key signed `multiplicitySum = 0`) of
`row bus ++ boundary` is exactly the abstract degree balance `GatedVm.Balanced` over the real-row edge
multiset — with **no** clock side conditions. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The state-bus **receive** key of a row's state access: its current `(clk, pc)` — the first entry of
`stateLookups` (a `-is_real` receive). Matches `stateLookups` exactly. -/
def rcvKey (sa : StateAccess (ZMod p)) : LookupKey :=
  (InteractionKind.State, "SP1State", [sa.clk_high.val, sa.clk_low.val, sa.pc[0].val, sa.pc[1].val, sa.pc[2].val])

/-- The state-bus **send** key: the next state `(clk+8, next_pc)` — the second entry of `stateLookups`
(a `+is_real` send). -/
def sndKey (sa : StateAccess (ZMod p)) : LookupKey :=
  (InteractionKind.State, "SP1State",
    [sa.clk_high.val, (sa.clk_low + 8).val, sa.next_pc[0].val, sa.next_pc[1].val, sa.next_pc[2].val])

/-- The directed edge a row contributes to the state multigraph: `current → next`. -/
def stateEdge (sa : StateAccess (ZMod p)) : LookupKey × LookupKey := (rcvKey sa, sndKey sa)

/-- "Real row whose receive key is `k`". -/
def rcvP (k : LookupKey) (r : Trace.RowView (ZMod p)) : Prop :=
  (stateAccess r).is_real ≠ 0 ∧ rcvKey (stateAccess r) = k

/-- "Real row whose send key is `k`". -/
def sndP (k : LookupKey) (r : Trace.RowView (ZMod p)) : Prop :=
  (stateAccess r).is_real ≠ 0 ∧ sndKey (stateAccess r) = k

instance (k : LookupKey) (r : Trace.RowView (ZMod p)) : Decidable (rcvP k r) := by
  unfold rcvP; infer_instance
instance (k : LookupKey) (r : Trace.RowView (ZMod p)) : Decidable (sndP k r) := by
  unfold sndP; infer_instance

/-- The real-row edge multiset: the real rows, with `edge r := stateEdge (stateAccess r)`. -/
def realRowEdges (rows : List (Trace.RowView (ZMod p))) : Multiset (Trace.RowView (ZMod p)) :=
  (↑rows : Multiset _).filter (fun r => (stateAccess r).is_real ≠ 0)

/-- Per-row state-bus contribution at key `k`: `+is_real` at the send key, `-is_real` at the receive
key. -/
lemma mult_stateLookups (r : Trace.RowView (ZMod p)) (k : LookupKey) :
    multiplicitySum (stateLookups r) k
      = (if sndKey (stateAccess r) = k then ((stateAccess r).is_real.val : ℤ) else 0)
        - (if rcvKey (stateAccess r) = k then ((stateAccess r).is_real.val : ℤ) else 0) := by
  simp only [stateLookups, multiplicitySum_cons, multiplicitySum_nil, add_zero, keyOf, multOf,
    rcvKey, sndKey]
  split_ifs <;> ring

private lemma val_one_int : ((1 : ZMod p).val : ℤ) = 1 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp [ZMod.val_one]

/-- **Step A.** The aggregated state bus's per-key sum equals `indeg − outdeg` of the real-row edge
multigraph: `#{real r : sndKey = k} − #{real r : rcvKey = k}` (sends positive, receives negative). -/
lemma multiplicitySum_aggregate (rows : List (Trace.RowView (ZMod p)))
    (hbin : ∀ r ∈ rows, r.is_real = 0 ∨ r.is_real = 1) (k : LookupKey) :
    multiplicitySum (aggregateChipRows rows stateLookups) k
      = ((rows.countP (fun r => decide (sndP k r)) : ℤ))
        - (rows.countP (fun r => decide (rcvP k r))) := by
  induction rows with
  | nil => simp [aggregateChipRows, multiplicitySum_nil]
  | cons r rs IH =>
    have hr := hbin r (by simp)
    have hsa : (stateAccess r).is_real = r.is_real := rfl
    have per_row :
        (if sndKey (stateAccess r) = k then ((stateAccess r).is_real.val : ℤ) else 0)
          - (if rcvKey (stateAccess r) = k then ((stateAccess r).is_real.val : ℤ) else 0)
        = (if decide (sndP k r) then (1 : ℤ) else 0) - (if decide (rcvP k r) then 1 else 0) := by
      rcases hr with h0 | h1
      · simp [sndP, rcvP, hsa, h0]
      · have hre : (stateAccess r).is_real ≠ 0 := by rw [hsa, h1]; exact one_ne_zero
        have ho : ((stateAccess r).is_real.val : ℤ) = 1 := by rw [hsa, h1]; exact val_one_int
        rw [ho]
        by_cases hsn : sndKey (stateAccess r) = k <;> by_cases hrc : rcvKey (stateAccess r) = k <;>
          simp [sndP, rcvP, hre, hsn, hrc]
    rw [aggregateChipRows, List.flatMap_cons, multiplicitySum_append, mult_stateLookups r k,
      show rs.flatMap stateLookups = aggregateChipRows rs stateLookups from rfl,
      IH (fun x hx => hbin x (List.mem_cons_of_mem _ hx)), per_row, List.countP_cons,
      List.countP_cons]
    push_cast
    ring

/-- Out-degree of the real-row edge multigraph at `k` = `#{real r : rcvKey = k}`. -/
lemma outdeg_realRowEdges (rows : List (Trace.RowView (ZMod p))) (k : LookupKey) :
    GatedVm.outdeg (realRowEdges rows) (fun r => stateEdge (stateAccess r)) k
      = rows.countP (fun r => decide (rcvP k r)) := by
  simp only [GatedVm.outdeg, stateEdge, realRowEdges]
  rw [← Multiset.countP_eq_card_filter, Multiset.countP_filter, Multiset.coe_countP]
  apply List.countP_congr
  intro r _
  simp [rcvP, and_comm]

/-- In-degree at `k` = `#{real r : sndKey = k}`. -/
lemma indeg_realRowEdges (rows : List (Trace.RowView (ZMod p))) (k : LookupKey) :
    GatedVm.indeg (realRowEdges rows) (fun r => stateEdge (stateAccess r)) k
      = rows.countP (fun r => decide (sndP k r)) := by
  simp only [GatedVm.indeg, stateEdge, realRowEdges]
  rw [← Multiset.countP_eq_card_filter, Multiset.countP_filter, Multiset.coe_countP]
  apply List.countP_congr
  intro r _
  simp [sndP, and_comm]

/-- **Bus ⇒ `Balanced`.** The native state-bus balance of `row bus ++ [genesis +init, final −1]` is
exactly the abstract degree balance over the real-row edge multigraph, with `src` the public initial
key and `snk` the public final key — no clock injectivity / advance. This is the input to
`GatedVm.exists_trail`. -/
theorem balanced_state_bus
    (rows : List (Trace.RowView (ZMod p)))
    (hbin : ∀ r ∈ rows, r.is_real = 0 ∨ r.is_real = 1)
    (initEntry finalEntry : List ℕ)
    (h_bal : isConsistentBalanced (aggregateChipRows rows stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntry, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntry, (-1 : ℤ))])) :
    GatedVm.Balanced (realRowEdges rows) (fun r => stateEdge (stateAccess r))
      (InteractionKind.State, "SP1State", initEntry)
      (InteractionKind.State, "SP1State", finalEntry) := by
  intro k
  have hb := h_bal k
  rw [multiplicitySum_append, multiplicitySum_aggregate rows hbin k] at hb
  have hbd : multiplicitySum
      [(InteractionKind.State, "SP1State", initEntry, (1 : ℤ)),
       (InteractionKind.State, "SP1State", finalEntry, (-1 : ℤ))] k
      = (if (InteractionKind.State, "SP1State", initEntry) = k then 1 else 0)
        - (if (InteractionKind.State, "SP1State", finalEntry) = k then 1 else 0) := by
    simp only [multiplicitySum_cons, multiplicitySum_nil, keyOf, multOf, add_zero]
    split_ifs <;> ring
  rw [hbd] at hb
  rw [outdeg_realRowEdges rows k, indeg_realRowEdges rows k]
  have ei : (if (InteractionKind.State, "SP1State", initEntry) = k then (1 : ℤ) else 0)
          = (if k = (InteractionKind.State, "SP1State", initEntry) then 1 else 0) := by
    by_cases h : (InteractionKind.State, "SP1State", initEntry) = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  have ef : (if (InteractionKind.State, "SP1State", finalEntry) = k then (1 : ℤ) else 0)
          = (if k = (InteractionKind.State, "SP1State", finalEntry) then 1 else 0) := by
    by_cases h : (InteractionKind.State, "SP1State", finalEntry) = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [ei, ef] at hb
  linarith [hb]

/-- **Balance ⇒ a real-row execution trail.** Combining `balanced_state_bus` with the abstract
`GatedVm.exists_trail`: from the balanced state bus (+ genesis/finalization boundary) there is a walk of
**real rows** chaining the public initial state to the public final state — each step a row's
`current → next` transition, the whole trail's rows a sub-multiset of the real rows. No clock injectivity
or advance. (`DecidableEq` on rows is supplied classically; it only feeds `Multiset.erase` in the
abstract proof and does not affect the resulting proposition — `Classical.choice` is already in the
axiom baseline.) -/
theorem state_trail_of_balance
    (rows : List (Trace.RowView (ZMod p)))
    (hbin : ∀ r ∈ rows, r.is_real = 0 ∨ r.is_real = 1)
    (initEntry finalEntry : List ℕ)
    (h_bal : isConsistentBalanced (aggregateChipRows rows stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntry, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntry, (-1 : ℤ))])) :
    ∃ path : List (Trace.RowView (ZMod p)),
      GatedVm.IsWalk (fun r => stateEdge (stateAccess r))
          (InteractionKind.State, "SP1State", initEntry)
          (InteractionKind.State, "SP1State", finalEntry) path
        ∧ (↑path : Multiset (Trace.RowView (ZMod p))) ≤ realRowEdges rows := by
  classical
  exact GatedVm.exists_trail (fun r => stateEdge (stateAccess r)) (realRowEdges rows)
    (InteractionKind.State, "SP1State", initEntry) (InteractionKind.State, "SP1State", finalEntry)
    (balanced_state_bus rows hbin initEntry finalEntry h_bal)

/-- Every row appearing in such a trail is real. -/
theorem trail_rows_real {rows path : List (Trace.RowView (ZMod p))}
    (h : (↑path : Multiset (Trace.RowView (ZMod p))) ≤ realRowEdges rows)
    {r : Trace.RowView (ZMod p)} (hr : r ∈ path) : (stateAccess r).is_real ≠ 0 := by
  have hmem : r ∈ realRowEdges rows := Multiset.mem_of_le h (by simpa using hr)
  simp only [realRowEdges, Multiset.mem_filter] at hmem
  exact hmem.2

end SP1Clean.Soundness
