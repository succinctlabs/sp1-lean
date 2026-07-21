import SP1Clean.Soundness.TouchChains

/-! # Timed grounding for the ordinary memory slice

This is the productionized ordinary-window grounding induction. Given a batch of row-fact records
(each carrying its `LocalStepFact` and a `FrameFact`), a true
boundary state push, per-key multiset balance of the state and memory records, and the in-circuit-style
per-row ordering/shape facts, **every pull's guarantee holds** — and in particular the final state
pull's `LocalStateTruth` and the memory finalize pulls' `LocalMemTruth`.

All semantic facts are relative to the selected shard initial state and public initial clock. Boot
reachability and zero-register initialization are intentionally outside this theorem; they are supplied
only when a shard-local execution is anchored in the fixed machine model.

Current scope, kept explicit rather than hidden behind a full-machine name:

- **Balance representation**: plain `Multiset` equalities over lists of messages (no
  `LookupAccessList`/`BalanceBridge` detour) — `genesis + pushes = final + pulls` per bus/key, where
  the per-key genesis/final records are `Option`s (`optMS` — lists of length ≤ 1). The
  field→ℤ→multiset translation from the real channel data is a separate seam
  (`Model/BalanceBridge.lean` is the existing adapter).
- **The full memory axis, straight-line, single row type**: the keys are `Semantics.MemLoc`
  (registers *and* RAM word addresses). The frontier is **partial** — `live : MemLoc → Option _` —
  because a total invariant over 2^64 RAM cells is not populatable; balance itself forces a `some`
  genesis at every key the minimal row touches (the chain's head pull, whose only admissible match
  is the frontier — every batch push is too late). **Intra-row same-key chains are admitted**
  (the landed SP-6 refinement, `Soundness/TouchChains.lean`): a row may touch one location several
  times (`add x1, x1, x2`; `bne x1, x1`) — its same-key touches form a slot-ordered chain whose
  links (each later pull re-claims the row's own previous push) are *derived* from balance, never
  certified by `TouchOK`.
- **Location-dependent effect offsets** (SP1's ordinary schedule, matching `microValue`'s effect
  convention): a register write lands at `t + 4`, a RAM write at `t + 1` (`writeOffset`); register
  reads observe pre-write content anywhere in `[t, t + 3]`, while RAM reads are pinned at `δ = 0`
  (`readWindow` — the RAM effect lands at `+1`, so only the window start observes pre-effect
  content).
- **The three layers collapse into one strong induction** on the remaining rows (`walk`): at each
  step the row with **minimal state-pull time** is popped; state balance + the `+8`/mod-8
  discipline force its state pull to equal the running head and give every remaining row the
  `t + 8` gap (layer A: `stateBalance_remaining_ge_eight`); per touched key, that gap forces the
  chain's head pull to equal the `live` frontier record, derives the intra-row links, and cancels
  the whole chain (layer B: `chainForcing_step_of_gap`); and its `LocalStepFact`/`FrameFact` fire
  to advance the head, the frontier (to each chain's **last** push), and the truth invariants
  (layer C: step facts fire in time order).
- **`FrameFact` is a required per-row record beyond `Truth.LocalStepFact`**, now over **all**
  locations: the step fact alone cannot give the engine value-persistence across a window for
  locations the row does not change — chips owe frames for RAM words as well as registers.
- The `microValue` **epoch lemmas** — the register trio (`regEpoch`, `microValue_reg`,
  `localValueAt_shift`) and the RAM trio (`ramEpoch`, `microValue_ram`, `localValueAt_shift_ram`) —
  are the semantic crux of "chain linearity ⇒ currency": the trajectory content is constant on
  each epoch (`[c0+8k+4, c0+8(k+1)+4)` for registers, `[c0+8k+1, c0+8(k+1)+1)` for RAM), so
  intra-window shifts are free and cross-window persistence reduces to the rows' frames. Mid-chain
  pull currency needs no shifting at all: nothing can follow a same-key write (the SP-6 production
  value layer, `chain_pull_values`), so every chain pull carries the frontier value inside the
  pre-effect read window.
- **The SP-6 fields are load-bearing**: `RowOK.align8` (mod-8 window alignment of every state pull
  to the public initial clock) feeds `stateBalance_remaining_ge_eight`'s `t + 8` gap — the one fact
  the link derivation consumes — and `LiveOK`'s frontier-time bound (`timeNat m ≤ t` per `some`
  record) is re-established from each chain's last-push bound (`≤ t + 4 < t + 8`). -/

namespace SP1Clean.Soundness.TimedGrounding

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The register-epoch view of `microValue` -/

/-- The `chainState` index whose content `microValue` reads at a **register** location: window
`k = (τ - c0) / 8` pre-state for offsets `0..3`, post-state (`k+1`) for offsets `4..7`. -/
def regEpoch (c0 τ : ℕ) : ℕ :=
  if τ < c0 then 0 else (τ - c0) / 8 + (if 4 ≤ (τ - c0) % 8 then 1 else 0)

/-- `microValue` at a register is the `regEpoch`-indexed trajectory content. -/
lemma microValue_reg (s0 : SailState) (c0 : ℕ) (i : BitVec 5) (τ : ℕ) :
    microValue s0 c0 (MemLoc.reg i) τ
      = (chainState s0 (regEpoch c0 τ)).bind (locContent · (MemLoc.reg i)) := by
  rw [microValue, regEpoch]
  by_cases h : τ < c0
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    by_cases h4 : 4 ≤ (τ - c0) % 8 <;> simp [h4]

lemma regEpoch_eq_of {c0 τ n : ℕ} (h : c0 + 8 * n ≤ τ) (h' : τ < c0 + 8 * n + 4) :
    regEpoch c0 τ = n := by
  simp only [regEpoch]
  split
  · omega
  · split <;> omega

lemma regEpoch_eq_succ_of {c0 τ n : ℕ} (h : c0 + 8 * n + 4 ≤ τ) (h' : τ < c0 + 8 * n + 12) :
    regEpoch c0 τ = n + 1 := by
  simp only [regEpoch]
  split
  · omega
  · split <;> omega

/-- One real Sail step determines `stepOnce`. -/
lemma stepOnce_of_sailStep {s s' : SailState} (h : SailStep s s') : stepOnce s = some s' := by
  obtain ⟨b, hrun⟩ := h
  change SP1Clean.Machine.stepOnce s = some s'
  unfold SP1Clean.Machine.stepOnce
  rw [hrun]

/-- Extend a determined trajectory by one determined step. -/
lemma chainState_succ_of {s0 s s' : SailState} {n : ℕ}
    (h : chainState s0 n = some s) (h' : stepOnce s = some s') :
    chainState s0 (n + 1) = some s' := by
  change SP1Clean.Machine.trajectory s0 n = some s at h
  change SP1Clean.Machine.stepOnce s = some s' at h'
  change (SP1Clean.Machine.trajectory s0 n).bind SP1Clean.Machine.stepOnce = some s'
  rw [h, Option.bind_some, h']

omit [Fact (2 ^ 17 < p)] in
/-- **Intra-epoch shift.** A register `LocalValueAt` fact moves freely between two times of the same epoch
of the same execution window; the window alignment (`τ ≡ c0 mod 8`-gradedness) is read off the state
message's `LocalStateTruth`. Window `Or.inl`: both times in the pre-write half `[t, t+4)`;
`Or.inr`: both in the post-write epoch `[t+4, t+12)`. -/
lemma localValueAt_shift {program : GuestProgram} {initial : SailState} {initialClock : ℕ}
    {m : StateMsg (ZMod p)} (h_m : LocalStateTruth program initial initialClock m)
    {i : BitVec 5} {v : Word (ZMod p)} {τ τ' : ℕ}
    (hwin : (StateMsg.timeNat m ≤ τ ∧ τ < StateMsg.timeNat m + 4 ∧
             StateMsg.timeNat m ≤ τ' ∧ τ' < StateMsg.timeNat m + 4) ∨
            (StateMsg.timeNat m + 4 ≤ τ ∧ τ < StateMsg.timeNat m + 12 ∧
             StateMsg.timeNat m + 4 ≤ τ' ∧ τ' < StateMsg.timeNat m + 12))
    (h : LocalValueAt initial initialClock (MemLoc.reg i) τ v) :
    LocalValueAt initial initialClock (MemLoc.reg i) τ' v := by
  obtain ⟨n, -, -, htime, -, -, -⟩ := h_m
  have hv := h
  unfold LocalValueAt at hv ⊢
  rw [microValue_reg] at hv ⊢
  have he : regEpoch initialClock τ' = regEpoch initialClock τ := by
    rcases hwin with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rw [regEpoch_eq_of (n := n) (by omega) (by omega),
        regEpoch_eq_of (n := n) (by omega) (by omega)]
    · rw [regEpoch_eq_succ_of (n := n) (by omega) (by omega),
        regEpoch_eq_succ_of (n := n) (by omega) (by omega)]
  rw [he]
  exact hv

/-! ## The RAM-epoch view of `microValue` -/

/-- The `chainState` index whose content `microValue` reads at a **RAM** location: window
`k = (τ - c0) / 8` pre-state at offset `0` only, post-state (`k+1`) for offsets `1..7` — the RAM
effect lands at the `+1` `MemoryAccess` push offset. -/
def ramEpoch (c0 τ : ℕ) : ℕ :=
  if τ < c0 then 0 else (τ - c0) / 8 + (if 1 ≤ (τ - c0) % 8 then 1 else 0)

/-- `microValue` at a RAM address is the `ramEpoch`-indexed trajectory content. -/
lemma microValue_ram (s0 : SailState) (c0 : ℕ) (a : BitVec 64) (τ : ℕ) :
    microValue s0 c0 (MemLoc.ram a) τ
      = (chainState s0 (ramEpoch c0 τ)).bind (locContent · (MemLoc.ram a)) := by
  rw [microValue, ramEpoch]
  by_cases h : τ < c0
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    by_cases h1 : 1 ≤ (τ - c0) % 8 <;> simp [h1]

lemma ramEpoch_eq_of {c0 τ n : ℕ} (h : c0 + 8 * n ≤ τ) (h' : τ < c0 + 8 * n + 1) :
    ramEpoch c0 τ = n := by
  simp only [ramEpoch]
  split
  · omega
  · split <;> omega

lemma ramEpoch_eq_succ_of {c0 τ n : ℕ} (h : c0 + 8 * n + 1 ≤ τ) (h' : τ < c0 + 8 * n + 9) :
    ramEpoch c0 τ = n + 1 := by
  simp only [ramEpoch]
  split
  · omega
  · split <;> omega

omit [Fact (2 ^ 17 < p)] in
/-- **Intra-epoch shift, RAM.** The RAM analogue of `localValueAt_shift`: a RAM `LocalValueAt` fact
moves freely between two times of the same RAM epoch of the same execution window. Window `Or.inl`:
both times at the pre-effect point `[t, t+1)` (i.e. exactly `t`); `Or.inr`: both in the post-effect
epoch `[t+1, t+9)`. -/
lemma localValueAt_shift_ram {program : GuestProgram} {initial : SailState} {initialClock : ℕ}
    {m : StateMsg (ZMod p)} (h_m : LocalStateTruth program initial initialClock m)
    {a : BitVec 64} {v : Word (ZMod p)} {τ τ' : ℕ}
    (hwin : (StateMsg.timeNat m ≤ τ ∧ τ < StateMsg.timeNat m + 1 ∧
             StateMsg.timeNat m ≤ τ' ∧ τ' < StateMsg.timeNat m + 1) ∨
            (StateMsg.timeNat m + 1 ≤ τ ∧ τ < StateMsg.timeNat m + 9 ∧
             StateMsg.timeNat m + 1 ≤ τ' ∧ τ' < StateMsg.timeNat m + 9))
    (h : LocalValueAt initial initialClock (MemLoc.ram a) τ v) :
    LocalValueAt initial initialClock (MemLoc.ram a) τ' v := by
  obtain ⟨n, -, -, htime, -, -, -⟩ := h_m
  have hv := h
  unfold LocalValueAt at hv ⊢
  rw [microValue_ram] at hv ⊢
  have he : ramEpoch initialClock τ' = ramEpoch initialClock τ := by
    rcases hwin with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rw [ramEpoch_eq_of (n := n) (by omega) (by omega),
        ramEpoch_eq_of (n := n) (by omega) (by omega)]
    · rw [ramEpoch_eq_succ_of (n := n) (by omega) (by omega),
        ramEpoch_eq_succ_of (n := n) (by omega) (by omega)]
  rw [he]
  exact hv

/-! ## The per-row records

The schedule offsets (`writeOffset`/`readWindow`), `optMS`, the touch/chain structures
(`Touch`/`TouchOK`/`ChainOK`/`rowTouchesAt`/`rowPullsAt`/`rowPushesAt`), and the SP-6 balance
lemmas live in `Soundness/TouchChains.lean` (same namespace). -/

/-- **The per-row frame obligation**: `LocalStepFact` alone is not enough for the engine — each row
must also certify that it does not disturb locations it does not change. Under the same hypotheses as
the step fact (pulled state truth + operand currency), for any location (register **or** RAM word)
whose pushes this row all agree with `v` (untouched: vacuous; read-back: the re-pushed value; write:
the written value when it happens to equal `v`), a `LocalValueAt v` fact advances across the row's
window. -/
def FrameFact (program : GuestProgram) (initial : SailState) (initialClock : ℕ)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program initial initialClock r.statePull →
  (∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
      SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  ∀ (loc : MemLoc) (v : Word (ZMod p)),
    (∀ m ∈ r.memPushes, MemoryMsg.locOf m = loc → m.value = v) →
    LocalValueAt initial initialClock loc (StateMsg.timeNat r.statePull) v →
    LocalValueAt initial initialClock loc (StateMsg.timeNat r.statePush) v

/-- The in-circuit-style per-row facts: `+8` clock discipline, mod-8 window alignment to the public
initial clock (the SP-6 gap input), positionally paired touches (each carrying the
`prev_clk < access_clk` bound and read-window/write-offset shape of `TouchOK`), and per-key
slot-monotone push times. Same-key touches are admitted — register-alias rows — and their chain
links are *derived* from balance by the walk, never certified here. -/
structure RowOK (initialClock : ℕ) (r : RowFacts p) : Prop where
  time8 : StateMsg.timeNat r.statePush = StateMsg.timeNat r.statePull + 8
  align8 : StateMsg.timeNat r.statePull % 8 = initialClock % 8
  touches : List.Forall₂ (TouchOK (StateMsg.timeNat r.statePull)) r.memPulls r.memPushes
  chain_mono : ∀ loc : MemLoc, List.IsChain
    (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2) (rowTouchesAt r loc)
  /-- Every push this row emits carries a bounded (`< 2^24`) access timestamp — the reader's own
  constraint-level `clk_low` range check.  Independent of the walk's currency, so the induction can
  read a same-key re-read pull's `ClkBound` off this field instead of the not-yet-established step
  output (the currency-circularity break, D0). -/
  pushClkBound : ∀ m ∈ r.memPushes, SP1Clean.Channels.MemoryMsg.ClkBound m

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Package a row's per-key touches as the chain bundle consumed by the per-key forcing. -/
lemma RowOK.chainOK {initialClock : ℕ} {r : RowFacts p} (hok : RowOK initialClock r)
    (loc : MemLoc) : ChainOK loc (StateMsg.timeNat r.statePull) (rowTouchesAt r loc) := by
  have hmem : ∀ pq ∈ rowTouchesAt r loc,
      TouchOK (StateMsg.timeNat r.statePull) pq.1 pq.2 ∧ MemoryMsg.locOf pq.2 = loc := by
    intro pq hpq
    obtain ⟨hz, hloc⟩ := mem_rowTouchesAt.mp hpq
    exact ⟨List.forall₂_zip hok.touches hz, hloc⟩
  refine
    { pull_loc := fun pq hpq => ?_
      push_loc := fun pq hpq => (hmem pq hpq).2
      slot := fun pq hpq => (hmem pq hpq).1.pull_lt_push
      read_lo := fun pq hpq => (hmem pq hpq).1.read_lo
      read_hi := fun pq hpq => ?_
      push_kind := fun pq hpq => ?_
      push_mono := hok.chain_mono loc }
  · rw [← (hmem pq hpq).1.loc_eq]
    exact (hmem pq hpq).2
  · have h := (hmem pq hpq).1.read_hi
    rwa [(hmem pq hpq).1.loc_eq.symm.trans (hmem pq hpq).2] at h
  · rcases (hmem pq hpq).1.push_kind with h | h
    · exact Or.inl h
    · right
      rwa [(hmem pq hpq).2] at h

/-- The engine's per-row conclusion: every pull guarantee of the row holds (the state pull's
`LocalStateTruth`, each memory pull's `LocalMemTruth`), plus the read-time currency the row's step fact
consumed. -/
def Grounded (program : GuestProgram) (initial : SailState) (initialClock : ℕ)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program initial initialClock r.statePull ∧
  ∀ mp ∈ r.memPulls, LocalMemTruth initial initialClock mp.1 ∧
    LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value

/-- **The carrier alignment relation** (Phase B1). The engine's `RowOK` pairs each pull positionally
with the same-location push at that push's micro-time (`t+3`/`t+2` for the register read-backs, `t`
for the write slot), so the walk must be fed an *aligned* carrier — but `ChipGroundingContracts`
proves `LocalStepFact`/`FrameFact` over the *ordinary* carrier (every pull read at the window start
`t`, in emitted order), and the row-`Spec` consumers read the ordinary carrier too. `AlignsWith
r_align r_ord` records that the two share their state edge and push list and that every ordinary pull
is matched by an aligned pull carrying the same message inside the pre-write register epoch
`[t, t+4)`. Register-axis only; the RAM analogue (loads/stores, Phase R) uses `localValueAt_shift_ram`
and the `[t, t+1)` window. -/
structure AlignsWith (r_align r_ord : RowFacts p) : Prop where
  statePull : r_align.statePull = r_ord.statePull
  statePush : r_align.statePush = r_ord.statePush
  pushes : r_align.memPushes = r_ord.memPushes
  reg : ∀ mp ∈ r_ord.memPulls, ∃ i : BitVec 5, MemoryMsg.locOf mp.1 = MemLoc.reg i
  ordTime : ∀ mp ∈ r_ord.memPulls, mp.2 = StateMsg.timeNat r_ord.statePull
  match_ : ∀ mp ∈ r_ord.memPulls, ∃ mp' ∈ r_align.memPulls, mp'.1 = mp.1 ∧
    StateMsg.timeNat r_align.statePull ≤ mp'.2 ∧
    mp'.2 < StateMsg.timeNat r_align.statePull + 4

omit [Fact (2 ^ 17 < p)] in
/-- **The shared engine of all three carrier transports.** Ordinary pull currency (every pull read at
the window start `t`) is derived from aligned pull currency by shifting each matched pull back to `t`
inside its pre-write register epoch via `localValueAt_shift`. -/
theorem ordinaryPullCurrency_of_aligned
    {program : GuestProgram} {initial : SailState} {initialClock : ℕ}
    {r_align r_ord : RowFacts p} (h : AlignsWith r_align r_ord)
    (hstateTruth : LocalStateTruth program initial initialClock r_align.statePull)
    (hcurr_al : ∀ mp ∈ r_align.memPulls, MemoryMsg.isU64 mp.1 ∧
      MemoryMsg.ClkBound mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∀ mp ∈ r_ord.memPulls, MemoryMsg.isU64 mp.1 ∧
      MemoryMsg.ClkBound mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
  intro mp hmp
  obtain ⟨i, hloc⟩ := h.reg mp hmp
  obtain ⟨mp', hmp'_mem, hmsg, hlo, hhi⟩ := h.match_ mp hmp
  obtain ⟨hu64, hclk, hval_al⟩ := hcurr_al mp' hmp'_mem
  refine ⟨hmsg ▸ hu64, hmsg ▸ hclk, ?_⟩
  rw [hloc, h.ordTime mp hmp]
  have hval_al' : LocalValueAt initial initialClock (MemLoc.reg i) mp'.2 mp.1.value := by
    rw [← hmsg, ← show MemoryMsg.locOf mp'.1 = MemLoc.reg i from hmsg ▸ hloc]
    exact hval_al
  have hst : StateMsg.timeNat r_align.statePull = StateMsg.timeNat r_ord.statePull := by
    rw [h.statePull]
  refine localValueAt_shift hstateTruth (Or.inl ⟨hlo, hhi, ?_, ?_⟩) hval_al' <;> omega

omit [Fact (2 ^ 17 < p)] in
/-- `LocalStepFact` transports from the ordinary carrier (where `ChipGroundingContracts` proves it) to
the aligned carrier (which the walk consumes): aligned pull currency shifts back to `t`, feeds the
ordinary step, and its conclusion (pushed-state truth + push truths) is carrier-shared. -/
theorem localStepFact_align_of_ordinary
    {program : GuestProgram} {initial : SailState} {initialClock : ℕ}
    {r_align r_ord : RowFacts p} (h : AlignsWith r_align r_ord)
    (step_ord : LocalStepFact program initial initialClock r_ord) :
    LocalStepFact program initial initialClock r_align := by
  intro hpull hcurr_al
  have hpull_ord : LocalStateTruth program initial initialClock r_ord.statePull := by
    rw [← h.statePull]; exact hpull
  have hcurr_ord := ordinaryPullCurrency_of_aligned h hpull hcurr_al
  obtain ⟨hpush_ord, hmem_ord⟩ := step_ord hpull_ord hcurr_ord
  refine ⟨?_, ?_⟩
  · rw [h.statePush]; exact hpush_ord
  · rw [h.pushes]; exact hmem_ord

omit [Fact (2 ^ 17 < p)] in
/-- `FrameFact` transports the same way. -/
theorem frameFact_align_of_ordinary
    {program : GuestProgram} {initial : SailState} {initialClock : ℕ}
    {r_align r_ord : RowFacts p} (h : AlignsWith r_align r_ord)
    (frame_ord : FrameFact program initial initialClock r_ord) :
    FrameFact program initial initialClock r_align := by
  intro hpull hcurr_al loc v hpush hstart
  have hpull_ord : LocalStateTruth program initial initialClock r_ord.statePull := by
    rw [← h.statePull]; exact hpull
  have hcurr_ord := ordinaryPullCurrency_of_aligned h hpull hcurr_al
  have hpush_ord : ∀ m ∈ r_ord.memPushes, MemoryMsg.locOf m = loc → m.value = v := by
    rw [← h.pushes]; exact hpush
  have := frame_ord hpull_ord hcurr_ord loc v hpush_ord (by rw [← h.statePull]; exact hstart)
  rw [h.statePush]; exact this

omit [Fact (2 ^ 17 < p)] in
/-- **The aligned→ordinary grounding transport** — the direction the row-`Spec` consumers
(`valueOperandsBound_of_grounded`) need. `LocalMemTruth` is carrier-independent (it speaks of the
message's own time), so it transfers by message identity; only the read-time currency is shifted. -/
theorem grounded_ordinary_of_aligned
    {program : GuestProgram} {initial : SailState} {initialClock : ℕ}
    {r_align r_ord : RowFacts p} (h : AlignsWith r_align r_ord)
    (grounded_align : Grounded program initial initialClock r_align) :
    Grounded program initial initialClock r_ord := by
  obtain ⟨hstateTruth_al, hpulls_al⟩ := grounded_align
  refine ⟨by rw [← h.statePull]; exact hstateTruth_al, ?_⟩
  intro mp hmp
  obtain ⟨i, hloc⟩ := h.reg mp hmp
  obtain ⟨mp', hmp'_mem, hmsg, hlo, hhi⟩ := h.match_ mp hmp
  obtain ⟨hmemtruth, hval_al⟩ := hpulls_al mp' hmp'_mem
  refine ⟨hmsg ▸ hmemtruth, ?_⟩
  rw [hloc, h.ordTime mp hmp]
  have hval_al' : LocalValueAt initial initialClock (MemLoc.reg i) mp'.2 mp.1.value := by
    rw [← hmsg, ← show MemoryMsg.locOf mp'.1 = MemLoc.reg i from hmsg ▸ hloc]
    exact hval_al
  have hst : StateMsg.timeNat r_align.statePull = StateMsg.timeNat r_ord.statePull := by
    rw [h.statePull]
  refine localValueAt_shift hstateTruth_al (Or.inl ⟨hlo, hhi, ?_, ?_⟩) hval_al' <;> omega

/-- The walk invariant for the **partial** per-key memory frontier `live`: at each key that carries a
frontier record, that record sits at the key, its own guarantee (`LocalMemTruth`) holds, its value is
current at the head time `t`, and its time is at most `t` (the SP-6 forward-compatibility bound).
Keys with `live loc = none` (untouched RAM, in particular) carry no invariant. -/
def LiveOK (initial : SailState) (initialClock t : ℕ)
    (live : MemLoc → Option (MemoryMsg (ZMod p))) : Prop :=
  ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), live loc = some m →
    MemoryMsg.locOf m = loc ∧
    LocalMemTruth initial initialClock m ∧
    LocalValueAt initial initialClock loc t m.value ∧
    MemoryMsg.timeNat m ≤ t

/-! ## Per-key record lists -/

/-- All pulled prior messages of a batch at location `loc` (as a multiset — order is irrelevant). -/
def pullsAt (rows : List (RowFacts p)) (loc : MemLoc) : Multiset (MemoryMsg (ZMod p)) :=
  (rows.map fun r => (↑(rowPullsAt r loc) : Multiset (MemoryMsg (ZMod p)))).sum

/-- All pushed messages of a batch at location `loc`. -/
def pushesAt (rows : List (RowFacts p)) (loc : MemLoc) : Multiset (MemoryMsg (ZMod p)) :=
  (rows.map fun r => (↑(rowPushesAt r loc) : Multiset (MemoryMsg (ZMod p)))).sum

/-! ## List/multiset helpers -/

private lemma exists_min_by {α : Type} (f : α → ℕ) :
    ∀ (l : List α), l ≠ [] → ∃ r ∈ l, ∀ r' ∈ l, f r ≤ f r'
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_singleton_self a, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨r, hr, hmin⟩ := exists_min_by f (b :: l) (List.cons_ne_nil b l)
    by_cases hab : f a ≤ f r
    · refine ⟨a, List.mem_cons_self, fun r' hr' => ?_⟩
      rcases List.mem_cons.mp hr' with rfl | h
      · exact le_refl _
      · exact le_trans hab (hmin r' h)
    · refine ⟨r, List.mem_cons_of_mem a hr, fun r' hr' => ?_⟩
      rcases List.mem_cons.mp hr' with rfl | h
      · omega
      · exact hmin r' h

private lemma forall₂_exists_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => intro b hb; cases hb
  | cons hR _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hR⟩
    · obtain ⟨a, ha, hab⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

private lemma mem_listSum_map {α β : Type} (f : α → Multiset β) :
    ∀ (l : List α) (b : β), b ∈ (l.map f).sum ↔ ∃ a ∈ l, b ∈ f a
  | [], b => by simp
  | a :: l, b => by
    simp only [List.map_cons, List.sum_cons, Multiset.mem_add, mem_listSum_map f l b,
      List.mem_cons]
    constructor
    · rintro (h | ⟨a', ha', hb⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨a', Or.inr ha', hb⟩
    · rintro ⟨a', rfl | ha', hb⟩
      · exact Or.inl hb
      · exact Or.inr ⟨a', ha', hb⟩

private lemma listSum_map_pop {α β : Type} (f : α → Multiset β) (l1 l2 : List α) (r : α) :
    ((l1 ++ r :: l2).map f).sum = f r + ((l1 ++ l2).map f).sum := by
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  rw [add_left_comm]

private lemma coe_map_pop {α β : Type} (f : α → β) (l1 l2 : List α) (r : α) :
    (↑((l1 ++ r :: l2).map f) : Multiset β) = f r ::ₘ ↑((l1 ++ l2).map f) := by
  refine Multiset.coe_eq_coe.mpr ?_
  exact List.perm_middle.map f

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private lemma pushesAt_pop (l1 l2 : List (RowFacts p)) (r : RowFacts p) (loc : MemLoc) :
    pushesAt (l1 ++ r :: l2) loc
      = (↑(rowPushesAt r loc) : Multiset (MemoryMsg (ZMod p))) + pushesAt (l1 ++ l2) loc := by
  simp only [pushesAt]
  exact listSum_map_pop _ l1 l2 r

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private lemma pullsAt_pop (l1 l2 : List (RowFacts p)) (r : RowFacts p) (loc : MemLoc) :
    pullsAt (l1 ++ r :: l2) loc
      = (↑(rowPullsAt r loc) : Multiset (MemoryMsg (ZMod p))) + pullsAt (l1 ++ l2) loc := by
  simp only [pullsAt]
  exact listSum_map_pop _ l1 l2 r

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- All pushes of a row happen at/after its state-pull time. -/
lemma push_time_ge {c0 : ℕ} {r : RowFacts p} (hok : RowOK c0 r) {q : MemoryMsg (ZMod p)}
    (hq : q ∈ r.memPushes) : StateMsg.timeNat r.statePull ≤ MemoryMsg.timeNat q := by
  obtain ⟨mp, -, hto⟩ := forall₂_exists_left hok.touches q hq
  exact hto.push_lo

/-! ## The timed grounding walk -/

omit [Fact (2 ^ 17 < p)] in
/-- **The ordinary timed grounding theorem.** Given per-row `LocalStepFact`s and
`FrameFact`s, the in-circuit-style shape/ordering facts (`RowOK`), a true head state record
(`LocalStateTruth head` — the boundary init push at the top level), a true partial per-key memory
frontier (`LiveOK` — the genesis pushes at the top level), and the state/memory multiset balances,
**every pull's guarantee holds**: each row is `Grounded` (its state pull's `LocalStateTruth`, its
memory pulls' `LocalMemTruth`s, and its read-time currencies), the final state pull `fin` is true, and
each key's finalize pull `finM loc` (where present) is true.

Strong induction on the batch size: pop the row with minimal state-pull time; state balance + time
discipline force it to pull `head`, and `stateBalance_remaining_ge_eight` gives every remaining row
the `t + 8` gap (layer A); per touched key, `chainForcing_step_of_gap` forces the chain's head pull
to equal the frontier — in particular balance forces a `some` genesis there — derives the intra-row
links, and cancels the whole chain (layer B); its `LocalStepFact` fires (layer C), and its chain
last-pushes/`FrameFact` rebuild the invariant one window later. Same-key multi-touch rows are fully
supported: tail pulls re-claim the row's own read-backs (`chain_pull_values` — nothing can follow a
same-key write), and their `LocalMemTruth` comes from the row's own fired pushes. -/
theorem walk (program : GuestProgram) (initial : SailState) (initialClock : ℕ)
    (fin : StateMsg (ZMod p))
    (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFact program initial initialClock r) →
      (∀ r ∈ rows, FrameFact program initial initialClock r) →
      (∀ r ∈ rows, RowOK initialClock r) →
      LocalStateTruth program initial initialClock head →
      LiveOK initial initialClock (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, Grounded program initial initialClock r) ∧
        LocalStateTruth program initial initialClock fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          LocalMemTruth initial initialClock m := by
  intro N
  induction N with
  | zero =>
    intro rows head live hlen _ _ _ h_head h_live h_sbal h_mbal
    obtain rfl : rows = [] := List.length_eq_zero_iff.mp hlen
    have h_fin : head = fin := by simpa using h_sbal
    refine ⟨by simp, h_fin ▸ h_head, fun loc m hm => ?_⟩
    have h_fm : optMS (live loc) = optMS (finM loc) := by
      simpa [pullsAt, pushesAt] using h_mbal loc
    rw [hm, optMS_some] at h_fm
    cases hlv : live loc with
    | none => rw [hlv, optMS_none] at h_fm; simp at h_fm
    | some m' =>
      rw [hlv, optMS_some, Multiset.singleton_inj] at h_fm
      exact h_fm ▸ (h_live loc m' hlv).2.1
  | succ N ih =>
    intro rows head live hlen h_step h_frame h_ok h_head h_live h_sbal h_mbal
    have hne : rows ≠ [] := fun h => by simp [h] at hlen
    -- (A) the row with minimal state-pull time pulls `head`: any other candidate match in the
    -- balance would be a push, whose time is its own pull time + 8 > the minimum.
    obtain ⟨r, hr_mem, hr_min⟩ := exists_min_by (fun r => StateMsg.timeNat r.statePull) rows hne
    have h_rok := h_ok r hr_mem
    have hr_pull : r.statePull = head := by
      have hmem : r.statePull
          ∈ (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))) := by
        rw [h_sbal]
        exact Multiset.mem_cons_of_mem (Multiset.mem_coe.mpr (List.mem_map_of_mem hr_mem))
      rcases Multiset.mem_cons.mp hmem with h | h
      · exact h
      · exfalso
        obtain ⟨r'', hr''_mem, hr''_eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
        have h8 := (h_ok r'' hr''_mem).time8
        have hmin := hr_min r'' hr''_mem
        rw [hr''_eq] at h8
        omega
    have h_rtruth : LocalStateTruth program initial initialClock r.statePull := by
      rw [hr_pull]
      exact h_head
    have ht_head : StateMsg.timeNat r.statePull = StateMsg.timeNat head := by rw [hr_pull]
    -- pop `r` out of the batch
    obtain ⟨l1, l2, rfl⟩ : ∃ l1 l2, rows = l1 ++ r :: l2 := List.append_of_mem hr_mem
    have hlen' : (l1 ++ l2).length = N := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    have hsub : ∀ r' ∈ l1 ++ l2, r' ∈ l1 ++ r :: l2 := fun r' hr' => mem_middle r hr'
    -- the SP-6 state gap (invariants 1 + 2): every remaining row's window starts ≥ t + 8
    have h_gap : ∀ r' ∈ l1 ++ l2,
        StateMsg.timeNat r.statePull + 8 ≤ StateMsg.timeNat r'.statePull := by
      refine stateBalance_remaining_ge_eight (fun r' h => (h_ok r' h).time8) hr_min
        (fun r' h => ?_) ht_head.symm hr_pull h_sbal
      rw [(h_ok r' h).align8, h_rok.align8]
    -- hence every remaining row's push is ≥ t + 8 — the gap the link derivation consumes
    have h_opush : ∀ loc : MemLoc, ∀ m ∈ pushesAt (l1 ++ l2) loc,
        StateMsg.timeNat r.statePull + 8 ≤ MemoryMsg.timeNat m := by
      intro loc m hm
      simp only [pushesAt, mem_listSum_map] at hm
      obtain ⟨r', hr'_mem, hm'⟩ := hm
      have hq : m ∈ r'.memPushes := List.mem_of_mem_filter (Multiset.mem_coe.mp hm')
      have h1 := push_time_ge (h_ok r' (hsub r' hr'_mem)) hq
      have h2 := h_gap r' hr'_mem
      omega
    -- (B) the per-key chain forcing at every key `r` touches: the frontier holds the chain's head
    -- pull, the intra-row links are derived from balance, the whole chain cancels, and the chain's
    -- last push is the new frontier with the re-established time bound.
    have h_key : ∀ (loc : MemLoc) (hne' : rowTouchesAt r loc ≠ []),
        live loc = some ((rowTouchesAt r loc).head hne').1.1 ∧
          List.IsChain (fun a b : Touch p => b.1.1 = a.2) (rowTouchesAt r loc) ∧
          (((rowTouchesAt r loc).getLast hne').2 ::ₘ pushesAt (l1 ++ l2) loc
            = optMS (finM loc) + pullsAt (l1 ++ l2) loc) ∧
          MemoryMsg.timeNat ((rowTouchesAt r loc).getLast hne').2
            ≤ StateMsg.timeNat r.statePull + 4 := by
      intro loc hne'
      have hbal := h_mbal loc
      rw [pushesAt_pop, pullsAt_pop, rowPushesAt_eq h_rok.touches loc,
        rowPullsAt_eq h_rok.touches loc,
        add_left_comm (optMS (finM loc))
          (↑(chainPulls (rowTouchesAt r loc)) : Multiset (MemoryMsg (ZMod p)))] at hbal
      exact chainForcing_step_of_gap hne' (h_rok.chainOK loc) (h_opush loc) hbal
    -- read-time currency for `r`'s pulls: every chain pull carries the frontier value (nothing
    -- can follow a same-key write), current throughout the location's pre-effect read window
    have h_curr : ∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
        LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
      intro mp hmp
      obtain ⟨q, hq_zip⟩ := mem_zip_of_mem_left h_rok.touches mp hmp
      have hto : TouchOK (StateMsg.timeNat r.statePull) mp q :=
        List.forall₂_zip h_rok.touches hq_zip
      have hmem_own : (mp, q) ∈ rowTouchesAt r (MemoryMsg.locOf mp.1) :=
        mem_rowTouchesAt.mpr ⟨hq_zip, hto.loc_eq⟩
      have hne' : rowTouchesAt r (MemoryMsg.locOf mp.1) ≠ [] := List.ne_nil_of_mem hmem_own
      obtain ⟨hlive_eq, hlink, -, -⟩ := h_key _ hne'
      obtain ⟨-, hmt₀, hval₀, -⟩ := h_live _ _ hlive_eq
      have hveq : mp.1.value
          = ((rowTouchesAt r (MemoryMsg.locOf mp.1)).head hne').1.1.value :=
        chain_pull_values _ (h_rok.chainOK _) hlink hne' (mp, q) hmem_own
      refine ⟨by simpa [SP1Clean.Channels.MemoryMsg.isU64, hveq] using hmt₀.1, ?_, ?_⟩
      · -- `ClkBound`: a head pull is the frontier record (bound from `LiveOK`'s `LocalMemTruth`); a
        -- same-key re-read pull is one of the row's own pushes (bound from `RowOK.pushClkBound`, not
        -- the not-yet-established step output — the currency-circularity break).
        rcases chain_pull_head_or_push _ hne' hlink (mp, q) hmem_own with hhd | hpush
        · rw [show mp.1 = ((rowTouchesAt r (MemoryMsg.locOf mp.1)).head hne').1.1 from hhd]
          exact hmt₀.2.1
        · obtain ⟨pq', hpq', hpq'_eq⟩ := mem_chainPushes.mp hpush
          have hq_mem : mp.1 ∈ r.memPushes := by
            rw [← hpq'_eq]
            exact (List.of_mem_zip (mem_rowTouchesAt.mp hpq').1).2
          exact h_rok.pushClkBound mp.1 hq_mem
      · rw [← hveq] at hval₀
        have hlo : StateMsg.timeNat r.statePull ≤ mp.2 :=
          (h_rok.chainOK (MemoryMsg.locOf mp.1)).read_lo (mp, q) hmem_own
        have hhi : mp.2 ≤ StateMsg.timeNat r.statePull + readWindow (MemoryMsg.locOf mp.1) :=
          (h_rok.chainOK (MemoryMsg.locOf mp.1)).read_hi (mp, q) hmem_own
        cases hloc : MemoryMsg.locOf mp.1 with
        | reg i =>
          rw [hloc, readWindow_reg] at hhi
          rw [hloc] at hval₀
          exact localValueAt_shift h_head
            (Or.inl ⟨le_refl _, by omega, by omega, by omega⟩) hval₀
        | ram a =>
          rw [hloc, readWindow_ram] at hhi
          rw [hloc] at hval₀
          have hread : mp.2 = StateMsg.timeNat head := by omega
          rw [hread]
          exact hval₀
    -- (C) fire the row's StepFact
    have h_after := h_step r hr_mem h_rtruth h_curr
    -- the row is Grounded: head pulls are true frontier records, tail pulls are the row's own
    -- (just-fired) read-back pushes
    have h_ground_r : Grounded program initial initialClock r := by
      refine ⟨h_rtruth, fun mp hmp => ⟨?_, (h_curr mp hmp).2.2⟩⟩
      obtain ⟨q, hq_zip⟩ := mem_zip_of_mem_left h_rok.touches mp hmp
      have hto : TouchOK (StateMsg.timeNat r.statePull) mp q :=
        List.forall₂_zip h_rok.touches hq_zip
      have hmem_own : (mp, q) ∈ rowTouchesAt r (MemoryMsg.locOf mp.1) :=
        mem_rowTouchesAt.mpr ⟨hq_zip, hto.loc_eq⟩
      have hne' : rowTouchesAt r (MemoryMsg.locOf mp.1) ≠ [] := List.ne_nil_of_mem hmem_own
      obtain ⟨hlive_eq, hlink, -, -⟩ := h_key _ hne'
      rcases chain_pull_head_or_push _ hne' hlink (mp, q) hmem_own with hhd | hpush
      · rw [show mp.1 = ((rowTouchesAt r (MemoryMsg.locOf mp.1)).head hne').1.1 from hhd]
        exact (h_live _ _ hlive_eq).2.1
      · obtain ⟨pq', hpq', hpq'_eq⟩ := mem_chainPushes.mp hpush
        have hq_mem : mp.1 ∈ r.memPushes := by
          rw [← hpq'_eq]
          exact (List.of_mem_zip (mem_rowTouchesAt.mp hpq').1).2
        exact h_after.2 mp.1 hq_mem
    have h8 := h_rok.time8
    -- the new frontier: the chain's last push where the row touched, unchanged elsewhere
    have h_liveOK' : LiveOK initial initialClock (StateMsg.timeNat r.statePush)
        (fun loc => ((rowTouchesAt r loc).getLast?.map (·.2)).or (live loc)) := by
      intro loc m hm
      dsimp only at hm
      by_cases hemp : rowTouchesAt r loc = []
      · -- untouched key: the frontier record persists via the row's frame
        rw [hemp] at hm
        simp only [List.getLast?_nil, Option.map_none, Option.none_or] at hm
        obtain ⟨hloc_m, hmt_m, hval_m, htime_m⟩ := h_live loc m hm
        refine ⟨hloc_m, hmt_m, ?_, by omega⟩
        refine h_frame r hr_mem h_rtruth h_curr loc m.value ?_ ?_
        · intro m' hm' hml
          exfalso
          have hmem' : m' ∈ rowPushesAt r loc := List.mem_filter.mpr ⟨hm', by simpa using hml⟩
          rw [rowPushesAt_eq h_rok.touches loc, hemp] at hmem'
          simp [chainPushes] at hmem'
        · rw [ht_head]
          exact hval_m
      · -- touched key: the chain's last push is the new frontier record
        obtain ⟨hlive_eq, hlink, -, hlast⟩ := h_key loc hemp
        rw [List.getLast?_eq_some_getLast hemp] at hm
        simp only [Option.map_some, Option.some_or, Option.some.injEq] at hm
        subst hm
        have hlast_mem : (rowTouchesAt r loc).getLast hemp ∈ rowTouchesAt r loc :=
          List.getLast_mem hemp
        have hloc_q : MemoryMsg.locOf ((rowTouchesAt r loc).getLast hemp).2 = loc :=
          (h_rok.chainOK loc).push_loc _ hlast_mem
        have hq_mem : ((rowTouchesAt r loc).getLast hemp).2 ∈ r.memPushes :=
          (List.of_mem_zip (mem_rowTouchesAt.mp hlast_mem).1).2
        have hmt_q := h_after.2 _ hq_mem
        refine ⟨hloc_q, hmt_q, ?_, by omega⟩
        rcases (h_rok.chainOK loc).push_kind _ hlast_mem with ⟨hv, -⟩ | hw
        · -- read-back last slot: the whole chain is read-backs of the (still-current) frontier
          -- value — frame across
          obtain ⟨-, -, hval₀, -⟩ := h_live loc _ hlive_eq
          have hpushv := chain_push_values _ (h_rok.chainOK loc) hlink hemp hv
          refine h_frame r hr_mem h_rtruth h_curr loc
            ((rowTouchesAt r loc).getLast hemp).2.value ?_ ?_
          · intro m' hm' hml
            have hmem' : m' ∈ rowPushesAt r loc := List.mem_filter.mpr ⟨hm', by simpa using hml⟩
            rw [rowPushesAt_eq h_rok.touches loc] at hmem'
            obtain ⟨pq', hpq', hpq'_eq⟩ := mem_chainPushes.mp hmem'
            rw [← hpq'_eq, hpushv pq' hpq', hpushv _ hlast_mem]
          · rw [hpushv _ hlast_mem, ht_head]
            exact hval₀
        · -- write last slot: the push's own MemTruth at `t + writeOffset`, shifted to the window
          -- end
          have hmt := hmt_q.2.2
          rw [hloc_q] at hmt
          cases loc with
          | reg i =>
            rw [writeOffset_reg] at hw
            exact localValueAt_shift h_head
              (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
          | ram a =>
            rw [writeOffset_ram] at hw
            exact localValueAt_shift_ram h_head
              (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
    -- state balance advances: cancel the consumed head
    have h_sbal' : r.statePush ::ₘ (↑((l1 ++ l2).map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑((l1 ++ l2).map (·.statePull)) := by
      have h := h_sbal
      rw [coe_map_pop, coe_map_pop, hr_pull, Multiset.cons_swap fin head] at h
      exact (Multiset.cons_inj_right _).mp h
    -- per-key memory balance advances: cancel the consumed frontier chain
    have h_mbal' : ∀ loc : MemLoc,
        optMS (((rowTouchesAt r loc).getLast?.map (·.2)).or (live loc)) + pushesAt (l1 ++ l2) loc
          = optMS (finM loc) + pullsAt (l1 ++ l2) loc := by
      intro loc
      by_cases hemp : rowTouchesAt r loc = []
      · have hbal := h_mbal loc
        rw [pushesAt_pop, pullsAt_pop, rowPushesAt_eq h_rok.touches loc,
          rowPullsAt_eq h_rok.touches loc, hemp] at hbal
        simp only [chainPushes, chainPulls, List.map_nil, Multiset.coe_nil, zero_add] at hbal
        rw [hemp]
        simpa using hbal
      · obtain ⟨-, -, hcancel, -⟩ := h_key loc hemp
        rw [List.getLast?_eq_some_getLast hemp]
        simp only [Option.map_some, Option.some_or, optMS_some, Multiset.singleton_add]
        exact hcancel
    -- recurse on the rest
    obtain ⟨hg_rest, hfin, hfinM⟩ := ih (l1 ++ l2) r.statePush
      (fun loc => ((rowTouchesAt r loc).getLast?.map (·.2)).or (live loc)) hlen'
      (fun r' h => h_step r' (hsub r' h)) (fun r' h => h_frame r' (hsub r' h))
      (fun r' h => h_ok r' (hsub r' h)) h_after.1 h_liveOK' h_sbal' h_mbal'
    refine ⟨?_, hfin, hfinM⟩
    intro r' hr'
    rcases List.mem_append.mp hr' with h | h
    · exact hg_rest r' (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact h_ground_r
      · exact hg_rest r' (List.mem_append_right _ h)

end SP1Clean.Soundness.TimedGrounding
