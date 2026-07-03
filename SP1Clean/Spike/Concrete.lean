import SP1Clean.Spike.AddRow

/-! # Spike capstone — the end-to-end composition on a concrete two-row trace

**Phase-1 de-risk spike** (`SP1Clean/Spike/`, deleted after the real sweep). The final gate criterion:
the pieces *compose*. A straight-line two-instruction trace (two chained `AddRow`s) is run through the
whole stack —

  chip `Spec` + the `TryStepLift` seam ──`AddRow.stepFact`/`frameFact`──▶ `StepFact`/`FrameFact`
                                        ──`Engine.walk`──▶ `StateTruth fin` (+ final `MemTruth`s)

— demonstrating that the reachability capstone (`StateTruth` of the committed program's final state) is
produced from per-row chip facts + the boundary, with memory never appearing in the conclusion.

**What is a hypothesis, and why (the honest seam inventory):**
- `h_lift0/1 : TryStepLift` — the `try_step` fetch-decode-execute reduction (Phase 3). In production
  `tryStepReduction ∘ opcode-inversion ∘ correct_add_native`; the spike has no program bus so the
  "this pc holds this ADD" content is folded in.
- `h_spec0/1 : Spec` — supplied by the decode seam (`Component.weakSoundness`) in the real capstone; a
  boundary of the spike, not the redesign.
- `h_ok0/1 : RowOK` — the in-circuit timestamp-ordering facts. `AddRow` elided the byte-timestamp
  gadgets (spike license), so these are assumed here; in production they are theorems from the readers'
  `RegisterAccessTimestamp`/`MemoryAccess` clk-diff gadgets.
- `h_head : StateTruth head`, `h_live : LiveOK`, `h_mbal` — the ensemble boundary: the verifier's
  genesis state push (vkey `pc_start`/`init_clk`), the memory-init provider's genesis frontier, and the
  per-key memory balance. In production these are the provider tables' `Assumptions` + the `Statement`'s
  `BalancedChannels`.

The **state balance is proved outright** (`stateBalance_two`) for the chained trace — high signal that
LogUp balance is a *natural* consequence of chaining, not an extra assumption. -/

namespace SP1Clean.Spike.Concrete

open SP1Clean.Channels (StateMsg MemoryMsg)
open SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **State balance is natural.** For a chained two-row trace (`row 1` pulls exactly what `row 0`
pushed), the State-bus multiset balance — `head` + the pushes = `fin` + the pulls — holds by
permutation. No hypothesis: chaining *is* balance. -/
theorem stateBalance_two (i0 i1 : AddRow.Inputs (ZMod p))
    (h_chain : AddRow.statePullMsg i1 = AddRow.statePushMsg i0) :
    (AddRow.statePullMsg i0)
        ::ₘ (↑(([AddRow.rowFactsOf i0, AddRow.rowFactsOf i1]).map (·.statePush))
              : Multiset (StateMsg (ZMod p)))
      = (AddRow.statePushMsg i1)
        ::ₘ ↑(([AddRow.rowFactsOf i0, AddRow.rowFactsOf i1]).map (·.statePull)) := by
  simp only [AddRow.rowFactsOf, List.map_cons, List.map_nil, h_chain]
  -- both sides are `x ::ₘ ↑[a, b] = ↑[x, a, b]`; the two lists are a cyclic rotation
  rw [Multiset.cons_coe, Multiset.cons_coe]
  refine Multiset.coe_eq_coe.mpr ?_
  -- [pull0, push0, push1] ~ [push1, pull0, push0]  =  [a,b] ++ [c] ~ [c] ++ [a,b]
  exact (List.perm_append_comm (l₁ := [AddRow.statePullMsg i0, AddRow.statePushMsg i0])
    (l₂ := [AddRow.statePushMsg i1]))

/-- **The spike capstone.** Two chained `AddRow`s + the boundary ⟹ the final state is `StateTruth`
(the committed program's execution reaches `fin`), and every finalize pull is `MemTruth`. The chip
facts flow `Spec` → `stepFact`/`frameFact` → `walk`; the state balance is discharged concretely, the
memory balance and genesis truths are the ensemble boundary. Memory is bookkeeping — absent from the
conclusion's reachability half. -/
theorem capstone_two [Fact (2 ^ 24 < p)]
    (data : ProverData (ZMod p)) (i0 i1 : AddRow.Inputs (ZMod p))
    (finM live : BitVec 5 → MemoryMsg (ZMod p))
    (h_chain : AddRow.statePullMsg i1 = AddRow.statePushMsg i0)
    -- per-row chip facts (Spec from the decode seam; TryStepLift the Phase-3 seam)
    (h_lift0 : AddRow.TryStepLift i0 data) (h_lift1 : AddRow.TryStepLift i1 data)
    (h_spec0 : AddRow.Spec i0 data) (h_spec1 : AddRow.Spec i1 data)
    (h_assm0 : AddRow.Assumptions i0 data) (h_assm1 : AddRow.Assumptions i1 data)
    (h_real0 : i0.is_real = 1) (h_real1 : i1.is_real = 1)
    -- the in-circuit timing facts (the byte-gadgets AddRow elided)
    (h_ok0 : RowOK (AddRow.rowFactsOf i0)) (h_ok1 : RowOK (AddRow.rowFactsOf i1))
    -- the ensemble boundary: genesis state truth, genesis memory frontier, memory balance
    (h_head : StateTruth (AddRow.statePullMsg i0) data)
    (h_live : LiveOK data (StateMsg.timeNat (AddRow.statePullMsg i0)) live)
    (h_mbal : ∀ i : BitVec 5, (live i)
        ::ₘ pushesAt [AddRow.rowFactsOf i0, AddRow.rowFactsOf i1] i
      = (finM i) ::ₘ pullsAt [AddRow.rowFactsOf i0, AddRow.rowFactsOf i1] i) :
    StateTruth (AddRow.statePushMsg i1) data ∧ ∀ i : BitVec 5, MemTruth (finM i) data := by
  -- the chip → engine handoff: each row's Spec + seam gives its StepFact and FrameFact
  have h_step : ∀ r ∈ [AddRow.rowFactsOf i0, AddRow.rowFactsOf i1], StepFact data r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact AddRow.stepFact h_lift0 h_spec0 h_assm0 h_real0
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact AddRow.stepFact h_lift1 h_spec1 h_assm1 h_real1
      · exact absurd hr (List.not_mem_nil)
  have h_frame : ∀ r ∈ [AddRow.rowFactsOf i0, AddRow.rowFactsOf i1], FrameFact data r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact AddRow.frameFact h_lift0 h_spec0 h_assm0 h_real0
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact AddRow.frameFact h_lift1 h_spec1 h_assm1 h_real1
      · exact absurd hr (List.not_mem_nil)
  have h_ok : ∀ r ∈ [AddRow.rowFactsOf i0, AddRow.rowFactsOf i1], RowOK r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h_ok0
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact h_ok1
      · exact absurd hr (List.not_mem_nil)
  -- the reachability capstone falls out of the engine
  obtain ⟨_, hfin, hfinM⟩ :=
    walk data (AddRow.statePushMsg i1) finM 2 [AddRow.rowFactsOf i0, AddRow.rowFactsOf i1]
      (AddRow.statePullMsg i0) live rfl h_step h_frame h_ok h_head h_live
      (stateBalance_two i0 i1 h_chain) h_mbal
  exact ⟨hfin, hfinM⟩

end SP1Clean.Spike.Concrete
