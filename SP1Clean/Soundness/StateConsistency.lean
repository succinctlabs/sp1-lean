import SP1Clean.Trace
import SP1Clean.Foundations.InteractionBus
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Readers.CPUState

/-! # Trace-level State-bus (PC-chain) consistency

The trace-level meaning of the State interactions that `Readers/CPUState.lean` + the chip emit (row
emission → bus data → trace consistency). Each row's CPUState fragment contributes two State-bus
interactions (`Extracted/CPUState.lean`):

- `receive (.state clk_high clk_low pc) is_real` and
- `send (.state clk_high (clk_low + 8) next_pc) is_real`.

Each row projects to a signed pair of `LookupAccess` contributions (`stateLookups`, receive negative /
send positive, both `is_real`-gated) feeding `Foundations/InteractionBus.lean`, and to a `StateAccess`
record whose adjacent-pair consistency is the **PC chain** `pcChainProp` (`a.next_pc = b.pc`, clock
advances by 8).

## Honest scope

`pcChainProp`, the projections, the aggregator, `aggregateStateAccesses_pcChain`, and the padding-row
gating witness `stateLookups_padding` are proven. The link
**multiset-balance ⟹ `pcChainProp`** needs whole-trace clock-injectivity reasoning and is threaded as
`TraceStateLink`: an honest assumption, not a `sorry`/axiom; deriving it natively is the marked next
step. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ}

/-- Per-row state-bus record: clock components (`clk_high`, recombined `clk_low`), current `pc`, the
row's claimed `next_pc`, and the `is_real` gate. -/
structure StateAccess (F : Type) where
  clk_high : F
  clk_low : F
  pc : Vector F 3
  next_pc : Vector F 3
  is_real : F

/-- State-access projection for a row: `next_pc` is the row's committed transition target (the chip
supplies `#v[pc[0]+4, pc[1], pc[2]]` for a straight-line chip, a data-dependent target for control
flow), `clk_low` recombines the 16-bit clock split, `is_real` is the committed selector. Mirrors
`Extracted/CPUState.lean`'s call shape (`clk_increment = 8`). -/
def stateAccess (r : Trace.RowView (ZMod p)) : StateAccess (ZMod p) :=
  { clk_high := r.state.clk_high,
    clk_low := r.state.clk_0_16 + r.state.clk_16_24 * 65536,
    pc := r.state.pc,
    next_pc := r.next_pc,
    is_real := r.is_real }

/-- The two signed State-bus contributions an Add row emits: `receive` at the current `(clk, pc)`
with `-is_real`, `send` at `(clk + 8, next_pc)` with `+is_real`. On padding rows (`is_real = 0`) both
multiplicities vanish (`stateLookups_padding`). -/
def stateLookups (r : Trace.RowView (ZMod p)) : LookupAccessList :=
  let sa := stateAccess r
  [ (.State, "SP1State",
      [sa.clk_high.val, sa.clk_low.val, sa.pc[0].val, sa.pc[1].val, sa.pc[2].val],
      -(sa.is_real.val : ℤ)),
    (.State, "SP1State",
      [sa.clk_high.val, (sa.clk_low + 8).val,
        sa.next_pc[0].val, sa.next_pc[1].val, sa.next_pc[2].val],
      (sa.is_real.val : ℤ)) ]

/-- The PC-chain predicate: every adjacent pair of *real* rows agrees on the PC handoff
(`a.next_pc = b.pc`) and the encoded clock advances by exactly `clkIncrement`. Padding pairs are
vacuous. -/
def pcChainProp (clkIncrement : ZMod p) : List (StateAccess (ZMod p)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (a.is_real ≠ 0 ∧ b.is_real ≠ 0 →
        a.next_pc = b.pc ∧
        a.clk_high * (2 ^ 24 : ZMod p) + a.clk_low + clkIncrement =
          b.clk_high * (2 ^ 24 : ZMod p) + b.clk_low) ∧
      pcChainProp clkIncrement (b :: rest)

/-- Aggregate the trace into its per-row state-access list, in chronological order. -/
def aggregateStateAccesses (rows : List (Trace.RowView (ZMod p))) : List (StateAccess (ZMod p)) :=
  rows.map stateAccess

/-- Trace-shape State-bus invariant: the aggregated accesses satisfy the PC chain. -/
structure TraceStateValid (rows : List (Trace.RowView (ZMod p))) (clkIncrement : ZMod p) : Prop where
  chain_holds : pcChainProp clkIncrement (aggregateStateAccesses rows)

/-- State-bus boundary: the first row's `pc` equals the verifier-committed `initial_pc`, the last
row's `next_pc` equals `final_pc`. These tie the on-chain PC chain to externally visible state. -/
structure TraceStateBoundary (rows : List (Trace.RowView (ZMod p)))
    (initial_pc final_pc : Vector (ZMod p) 3) : Prop where
  initial_match : (rows.head?).map (fun r => (stateAccess r).pc) = some initial_pc
  final_match : (rows.getLast?).map (fun r => (stateAccess r).next_pc) = some final_pc

/-- The aggregated accesses satisfy the PC chain under `TraceStateValid` (direct projection). -/
theorem aggregateStateAccesses_pcChain (rows : List (Trace.RowView (ZMod p))) (clkIncrement : ZMod p)
    (h : TraceStateValid rows clkIncrement) :
    pcChainProp clkIncrement (aggregateStateAccesses rows) :=
  h.chain_holds

/-- **The crux (threaded; residual named).** The per-adjacent-pair PC handoff + clock advance.
`state_successor_of_balance` derives, from the balanced State bus via `balanced_pos_has_neg`, that every
real row's `(clk+8, next_pc)` send key is cancelled by some real row's `(clk, pc)` receive — a `+8`
PC-handoff successor *exists*. The residual gap to `pcChainProp` is pinning that successor to the
*adjacent* list position: `clkInjective` (uniqueness) + the clock-advance side condition `TraceClkAdvance`
(stated as `pcChain_of_balance_and_clkInj`). Until that adjacency induction is closed, the chain is
threaded as an honest assumption. -/
def TraceStateLink (rows : List (Trace.RowView (ZMod p))) (clkIncrement : ZMod p) : Prop :=
  pcChainProp clkIncrement (aggregateStateAccesses rows)

/-- Discharge of `TraceStateValid` from the threaded state link (a re-bundling). -/
theorem traceStateValid_of_stateLink (rows : List (Trace.RowView (ZMod p))) (clkIncrement : ZMod p)
    (h_link : TraceStateLink rows clkIncrement) : TraceStateValid rows clkIncrement :=
  ⟨h_link⟩

/-- **Gating is real.** A padding row (`is_real = 0`) contributes zero to *every* State-bus key: both
its signed contributions have multiplicity 0. The emission is genuinely `is_real`-gated, matching SP1's
`send/receive … is_real`. -/
theorem stateLookups_padding [NeZero p] (r : Trace.RowView (ZMod p)) (h : r.is_real = 0) :
    ∀ k, multiplicitySum (stateLookups r) k = 0 := by
  have hz : ((stateAccess r).is_real.val : ℤ) = 0 := by
    simp only [stateAccess, h, ZMod.val_zero, Nat.cast_zero]
  intro k
  simp only [stateLookups, multiplicitySum_cons, multiplicitySum_nil, multOf, hz, neg_zero,
    ite_self, add_zero]

/-- **Successor exists (from State balance).** On a balanced State bus, every real row `a`'s `send` key
`(clk_high, clk_low+8, next_pc)` is cancelled by the `receive` of some real row `b` — so `b`'s current
`(clk_high, clk_low, pc)` equals `a`'s claimed `(clk_high, clk_low+8, next_pc)` as field values
(val-injectivity). The closed-bus, order-sensitive analogue of `byteAccessValid_of_balance`: per real row it
derives that a `+8` PC-handoff successor *exists* in the trace. Pinning that successor to the *adjacent* row
— i.e. `pcChainProp` — additionally needs whole-trace clock injectivity (`clkInjective`); this lemma is the
provable membership-style half. The clock conclusion stays at `ZMod p` level (one `ZMod.val_injective`), so
no `2^24 < p` bound is needed and `+8` wraparound is irrelevant. -/
theorem state_successor_of_balance [NeZero p]
    (rows : List (Trace.RowView (ZMod p)))
    (h_bal : isConsistentBalanced (aggregateChipRows rows stateLookups))
    (a : Trace.RowView (ZMod p)) (ha : a ∈ rows) (h_real : a.is_real ≠ 0) :
    ∃ b ∈ rows, b.is_real ≠ 0 ∧
      b.state.clk_high = a.state.clk_high ∧
      (stateAccess b).clk_low = (stateAccess a).clk_low + 8 ∧
      (stateAccess b).pc = (stateAccess a).next_pc := by
  -- `a`'s send contribution (the 2nd element of `stateLookups a`), a strictly-positive bus entry
  set send : LookupAccess :=
    (.State, "SP1State",
      [(stateAccess a).clk_high.val, ((stateAccess a).clk_low + 8).val,
        (stateAccess a).next_pc[0].val, (stateAccess a).next_pc[1].val, (stateAccess a).next_pc[2].val],
      ((stateAccess a).is_real.val : ℤ)) with hsend
  have h_send_mem : send ∈ aggregateChipRows rows stateLookups :=
    List.mem_flatMap.mpr ⟨a, ha, by rw [hsend]; simp [stateLookups]⟩
  have hvne : (stateAccess a).is_real.val ≠ 0 := fun hv =>
    h_real (ZMod.val_injective p (by rw [ZMod.val_zero]; exact hv))
  have h_pos : 0 < multOf send := by rw [hsend]; simp only [multOf]; omega
  obtain ⟨bacc, hbacc_mem, hbacc_key, hbacc_neg⟩ :=
    balanced_pos_has_neg (aggregateChipRows rows stateLookups) (keyOf send) h_bal send h_send_mem rfl h_pos
  obtain ⟨b, hb, hbacc_in⟩ := List.mem_flatMap.mp hbacc_mem
  refine ⟨b, hb, ?_⟩
  simp only [stateLookups, List.mem_cons, List.not_mem_nil, or_false] at hbacc_in
  rcases hbacc_in with rfl | rfl
  · -- the receive of `b`: negative multiplicity is consistent; recover the field equalities from the key
    have hbne : b.is_real ≠ 0 := by
      intro hb0
      simp only [multOf, stateAccess, hb0, ZMod.val_zero] at hbacc_neg
      omega
    rw [hsend] at hbacc_key
    simp only [keyOf, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at hbacc_key
    obtain ⟨hch, hcl, hp0, hp1, hp2⟩ := hbacc_key
    refine ⟨hbne, ZMod.val_injective p hch, ZMod.val_injective p hcl, ?_⟩
    apply Vector.ext; intro i hi
    rcases i with _ | _ | _ | i
    · exact ZMod.val_injective p hp0
    · exact ZMod.val_injective p hp1
    · exact ZMod.val_injective p hp2
    · exact absurd hi (by omega)
  · -- the send of `b`: its multiplicity is `+is_real.val ≥ 0`, contradicting `multOf bacc < 0`
    simp only [multOf] at hbacc_neg
    exact absurd hbacc_neg (not_lt.mpr (by positivity))

/-- Whole-trace clock injectivity: distinct state accesses have distinct encoded clocks
`clk_high · 2^24 + clk_low`. The trace-shape fact (SP1 timestamps are globally unique) that — together with
execution-order layout — would upgrade `state_successor_of_balance`'s "a `+8` successor *exists*" to "the
*adjacent* row is the successor", i.e. `pcChainProp`. -/
def clkInjective (accs : List (StateAccess (ZMod p))) : Prop :=
  ∀ i j : Fin accs.length,
    (accs.get i).clk_high * (2 ^ 24 : ZMod p) + (accs.get i).clk_low =
      (accs.get j).clk_high * (2 ^ 24 : ZMod p) + (accs.get j).clk_low → i = j

/-! ## The PC chain from balance

`state_successor_of_balance` is the order-insensitive half: from the balanced State bus it derives that
every real row's `(clk+8, next_pc)` send key is matched by *some* real row's `(clk, pc)` receive — a `+8`
PC-handoff successor *exists*. Below the adjacency gap is closed: with whole-trace clock injectivity
(`clkInjective`) and the **clock-advance** side condition (`TraceClkAdvance`, consecutive real rows'
encoded clocks differ by exactly `8`), the successor is pinned to the *adjacent* row, yielding the full
`pcChainProp`. The bus balance supplies the **PC-handoff** half (`a.next_pc = b.pc`); the **clock-advance**
half is assumed as `TraceClkAdvance` (enforced by the state chip's own `clk_low + 8` constraint, not by
the bus — a future clock-link pass discharges it from per-row Specs). -/

/-- The per-adjacent-pair relation `pcChainProp` recurses on (the first conjunct of its `a :: b :: rest`
case): for real rows, the PC handoff `a.next_pc = b.pc` and the encoded-clock advance by `clkIncrement`. -/
def pcStep (clkIncrement : ZMod p) (a b : StateAccess (ZMod p)) : Prop :=
  a.is_real ≠ 0 ∧ b.is_real ≠ 0 →
    a.next_pc = b.pc ∧
    a.clk_high * (2 ^ 24 : ZMod p) + a.clk_low + clkIncrement =
      b.clk_high * (2 ^ 24 : ZMod p) + b.clk_low

/-- The clock-advance-only relation: for real rows, the encoded clock advances by `clkIncrement`. The
clock half of `pcStep`, isolated so it can be assumed as a standalone trace-shape side condition. -/
def clkStep (clkIncrement : ZMod p) (a b : StateAccess (ZMod p)) : Prop :=
  a.is_real ≠ 0 ∧ b.is_real ≠ 0 →
    a.clk_high * (2 ^ 24 : ZMod p) + a.clk_low + clkIncrement =
      b.clk_high * (2 ^ 24 : ZMod p) + b.clk_low

/-- **Clock-advance trace-shape side condition.** Adjacent real rows' encoded clocks differ by exactly
`clkIncrement`. Enforced by the state chip's `clk_low + clkIncrement` constraint (a future pass discharges it
from per-row Specs); the residual that — with `clkInjective` — upgrades the existential
`state_successor_of_balance` to the adjacent `pcChainProp`. -/
def TraceClkAdvance (clkIncrement : ZMod p) (accs : List (StateAccess (ZMod p))) : Prop :=
  List.IsChain (clkStep clkIncrement) accs

/-- `pcChainProp` is exactly the `List.IsChain` of its per-pair relation `pcStep` — so the adjacency
characterization `List.isChain_iff_getElem` applies. -/
theorem pcChainProp_iff_isChain (clkIncrement : ZMod p) (l : List (StateAccess (ZMod p))) :
    pcChainProp clkIncrement l ↔ List.IsChain (pcStep clkIncrement) l := by
  induction l with
  | nil => exact ⟨fun _ => List.isChain_nil, fun _ => trivial⟩
  | cons a t IH =>
    cases t with
    | nil => exact ⟨fun _ => List.isChain_singleton a, fun _ => trivial⟩
    | cons b t' =>
      rw [List.isChain_cons_cons, ← IH]
      rfl

/-- **Clock injectivity, getElem form.** `clkInjective` rephrased over row indices: two rows with equal
encoded clocks are the same index. The bridge `state_adjacent_pc_handoff` consumes. -/
theorem clkInjective_getElem {rows : List (Trace.RowView (ZMod p))}
    (h_inj : clkInjective (aggregateStateAccesses rows))
    {i j : ℕ} (hi : i < rows.length) (hj : j < rows.length)
    (h_clk : (stateAccess rows[i]).clk_high * (2 ^ 24 : ZMod p) + (stateAccess rows[i]).clk_low =
        (stateAccess rows[j]).clk_high * (2 ^ 24 : ZMod p) + (stateAccess rows[j]).clk_low) :
    i = j := by
  have hlen : (aggregateStateAccesses rows).length = rows.length := by
    simp [aggregateStateAccesses]
  have key := h_inj ⟨i, by rw [hlen]; exact hi⟩ ⟨j, by rw [hlen]; exact hj⟩
  simp only [aggregateStateAccesses, List.get_eq_getElem, List.getElem_map] at key
  exact congrArg Fin.val (key h_clk)

/-- **Adjacent PC handoff from balance.** For adjacent real rows `i, i+1`, the balanced State bus + clock
injectivity + the clock-advance side condition force `next_pc(i) = pc(i+1)`. *Proof:*
`state_successor_of_balance` gives a real row `b'` with `clk(b') = clk(i)+8 ∧ pc(b') = next_pc(i)`;
`TraceClkAdvance` gives `clk(i+1) = clk(i)+8`; `clkInjective` forces `b' = rows[i+1]`; transport the PC eq. -/
theorem state_adjacent_pc_handoff [NeZero p]
    (rows : List (Trace.RowView (ZMod p)))
    (h_bal : isConsistentBalanced (aggregateChipRows rows stateLookups))
    (h_inj : clkInjective (aggregateStateAccesses rows))
    (h_clk : TraceClkAdvance 8 (aggregateStateAccesses rows))
    {i : ℕ} (hi1 : i + 1 < rows.length)
    (h_areal : (rows[i]'(by omega)).is_real ≠ 0)
    (h_breal : (rows[i + 1]'hi1).is_real ≠ 0) :
    (stateAccess (rows[i]'(by omega))).next_pc = (stateAccess (rows[i + 1]'hi1)).pc := by
  have hi : i < rows.length := by omega
  -- the `+8` successor that exists by balance
  obtain ⟨b', hb'_mem, hb'_real, hb'_ch, hb'_cl, hb'_pc⟩ :=
    state_successor_of_balance rows h_bal (rows[i]'hi) (List.getElem_mem hi) h_areal
  -- clock-advance at the adjacent pair: clk(i) + 8 = clk(i+1)
  have hlen : (aggregateStateAccesses rows).length = rows.length := by simp [aggregateStateAccesses]
  have h_step := (List.isChain_iff_getElem.mp h_clk) i (by rw [hlen]; omega)
  simp only [aggregateStateAccesses, List.getElem_map] at h_step
  have h_clkadv := h_step ⟨h_areal, h_breal⟩
  -- encoded clock of b' equals encoded clock of rows[i+1]
  have h_eq : (stateAccess b').clk_high * (2 ^ 24 : ZMod p) + (stateAccess b').clk_low =
      (stateAccess (rows[i + 1]'hi1)).clk_high * (2 ^ 24 : ZMod p) +
        (stateAccess (rows[i + 1]'hi1)).clk_low := by
    have hch : (stateAccess b').clk_high = (stateAccess (rows[i]'hi)).clk_high := by
      simp only [stateAccess]; exact hb'_ch
    rw [hch, hb'_cl, ← h_clkadv, add_assoc]
  -- pin b' to the adjacent row index
  obtain ⟨k, hk, hk_eq⟩ := List.getElem_of_mem hb'_mem
  have hki : k = i + 1 :=
    clkInjective_getElem h_inj hk hi1 (by rw [hk_eq]; exact h_eq)
  subst hki
  -- transport the PC equation: rows[k] = rows[i+1] (proof-irrelevant) = b'
  have hpc_eq : (stateAccess (rows[i + 1]'hi1)).pc = (stateAccess (rows[i + 1]'hk)).pc := rfl
  rw [hpc_eq, hk_eq, hb'_pc]

/-- **The PC chain from balance.** Discharges `pcChainProp 8` — and hence
`TraceStateLink` — from the balanced State bus + clock injectivity + the clock-advance side condition. The
adjacency induction over `List.isChain_iff_getElem` keeps the *full* `rows`/`h_bal`/`h_inj` fixed (peeling a
row would break balance, which `balanced_pos_has_neg` matches against the whole trace): each adjacent pair's
PC handoff is `state_adjacent_pc_handoff`, its clock advance is `TraceClkAdvance`. -/
theorem pcChain_of_balance_and_clkInj [NeZero p]
    (rows : List (Trace.RowView (ZMod p)))
    (h_bal : isConsistentBalanced (aggregateChipRows rows stateLookups))
    (h_inj : clkInjective (aggregateStateAccesses rows))
    (h_clk : TraceClkAdvance 8 (aggregateStateAccesses rows)) :
    pcChainProp 8 (aggregateStateAccesses rows) := by
  have hlen : (aggregateStateAccesses rows).length = rows.length := by simp [aggregateStateAccesses]
  rw [pcChainProp_iff_isChain, List.isChain_iff_getElem]
  intro i hi
  rw [hlen] at hi
  simp only [aggregateStateAccesses, List.getElem_map]
  intro ⟨h_areal, h_breal⟩
  refine ⟨state_adjacent_pc_handoff rows h_bal h_inj h_clk hi h_areal h_breal, ?_⟩
  have h_step := (List.isChain_iff_getElem.mp h_clk) i (by rw [hlen]; exact hi)
  simp only [aggregateStateAccesses, List.getElem_map] at h_step
  exact h_step ⟨h_areal, h_breal⟩

/-! ## emitted = projection (State bus)

`stateLookups` is not a hand-authored shadow — it is the val-image
(`AbstractInteraction.toAccess`) of the State interactions `Readers/CPUState.lean` *actually emits*,
recovered from its `exposedChannels` via Clean's `interactionsWith_eq_of_mem_exposedChannels`. The
bridge is parameterised by an `env` and a *row-realises-circuit* hypothesis (the `Trace.RowView` ↔
committed-column binding `Trace.lean` elides, being Sail-free) — it connects the emission to the
projection without smuggling in trace consistency. -/

open SP1Clean.Channels (stateChannel StateMsg)

/-- **emitted = projection for the State bus.** Given an environment realising the row's CPUState
columns (`h_*`) and a binary `is_real`, the hand-written `stateLookups r` is exactly the
`AbstractInteraction.toAccess`-image of the State interactions the `CPUState` reader emits at `offset` —
recovered from its `exposedChannels`. So `stateLookups` is a derived projection of the real emission. -/
theorem stateLookups_eq_emitted [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (r : Trace.RowView (ZMod p)) (env : Environment (ZMod p)) (offset : ℕ)
    (input_var : Var Readers.CPUState.Inputs (ZMod p))
    (h_real : r.is_real = 0 ∨ r.is_real = 1)
    (h_ir : Expression.eval env input_var.is_real = r.is_real)
    (h_ch : Expression.eval env input_var.cols.clk_high = r.state.clk_high)
    (h_c0 : Expression.eval env input_var.cols.clk_0_16 = r.state.clk_0_16)
    (h_c1 : Expression.eval env input_var.cols.clk_16_24 = r.state.clk_16_24)
    (h_p0 : Expression.eval env input_var.cols.pc[0] = r.state.pc[0])
    (h_p1 : Expression.eval env input_var.cols.pc[1] = r.state.pc[1])
    (h_p2 : Expression.eval env input_var.cols.pc[2] = r.state.pc[2])
    (h_np0 : Expression.eval env input_var.next_pc[0] = r.next_pc[0])
    (h_np1 : Expression.eval env input_var.next_pc[1] = r.next_pc[1])
    (h_np2 : Expression.eval env input_var.next_pc[2] = r.next_pc[2])
    (h_clk : Expression.eval env input_var.clk_inc = 8) :
    stateLookups r =
      (((Readers.CPUState.main (p := p) input_var).operations offset).interactionsWith
          stateChannel.toRawGated).map (AbstractInteraction.toAccess env) := by
  -- recover the two State interactions from `main` (unfold + `circuit_norm`; the
  -- `byteChannel.toRawGated ≠ stateChannel.toRawGated` distinctness lemmas filter out the byte pulls).
  simp only [Readers.CPUState.main, circuit_norm]
  -- `hk` is the gated kernel `toAccess_emittedGated_state`; it `rw`s against the recovered interactions.
  have hk : ∀ (m : Expression (ZMod p)) (s : StateMsg (Expression (ZMod p))),
      AbstractInteraction.toAccess env (stateChannel.emittedGated m s) =
        (InteractionKind.State, "SP1State",
          [(Expression.eval env s.clk_high).val, (Expression.eval env s.clk_low).val,
           (Expression.eval env s.pc0).val, (Expression.eval env s.pc1).val,
           (Expression.eval env s.pc2).val], signedVal (Expression.eval env m)) :=
    fun m s => toAccess_emittedGated_state env m s
  simp only [hk]
  -- `cols`/`next_pc`/`clk_inc` are reader *inputs*; their evals are pinned by the binding hypotheses
  -- (`h_*`/`h_np*`/`h_clk`); `circuit_norm` distributes `eval` over the `clk_low` sum (+ `clk_inc`).
  simp only [circuit_norm, stateLookups, stateAccess, h_ch, h_c0, h_c1, h_p0, h_p1, h_p2,
    h_np0, h_np1, h_np2, h_clk]
  -- only the multiplicities differ: `signedVal (∓eval is_real)` vs `∓is_real.val`. `h_ir` ties the eval to
  -- `r.is_real`; the `signedVal` lemmas evaluate the centered representative on the gate.
  have hp2 : 2 < p := by
    have h := Fact.out (p := 2 ^ 17 < p)
    have h2 : (2 : ℕ) < 2 ^ 17 := by norm_num
    omega
  rw [h_ir, signedVal_neg_is_real hp2 h_real, signedVal_is_real hp2 h_real]

end SP1Clean.Soundness
