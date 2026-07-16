import SP1Clean.Model.Semantics.Truth

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
  genesis at every key the minimal row pulls (its pulled prior strictly predates the window, while
  every batch push sits at/after it). Every row's touched locations are pairwise distinct
  (`RowOK.locs_nodup` — intra-row same-location chaining is the SP-6 walk-invariant refinement,
  still pending).
- **Location-dependent effect offsets** (SP1's ordinary schedule, matching `microValue`'s effect
  convention): a register write lands at `t + 4`, a RAM write at `t + 1` (`writeOffset`); register
  reads observe pre-write content anywhere in `[t, t + 3]`, while RAM reads are pinned at `δ = 0`
  (`readWindow` — the RAM effect lands at `+1`, so only the window start observes pre-effect
  content).
- **The three layers collapse into one strong induction** on the remaining rows (`walk`): at each step
  the row with **minimal state-pull time** is popped; balance + per-row time discipline force its
  state pull to equal the running head (layer A: unique live record per level), its memory pulls to
  equal the per-key `live` frontier messages (layer B: per-key push uniqueness ⇒ chain linearity),
  and its `LocalStepFact`/`FrameFact` fire to advance the head, the frontier, and the truth invariants
  (layer C: step facts fire in time order).
- **`FrameFact` is a required per-row record beyond `Truth.LocalStepFact`**, now over **all**
  locations: the step fact alone cannot give the engine value-persistence across a window for
  locations the row does not change — chips owe frames for RAM words as well as registers.
- The `microValue` **epoch lemmas** — the register trio (`regEpoch`, `microValue_reg`,
  `localValueAt_shift`) and the RAM trio (`ramEpoch`, `microValue_ram`, `localValueAt_shift_ram`) —
  are the semantic crux of "chain linearity ⇒ currency": the trajectory content is constant on
  each epoch (`[c0+8k+4, c0+8(k+1)+4)` for registers, `[c0+8k+1, c0+8(k+1)+1)` for RAM), so
  intra-window shifts are free and cross-window persistence reduces to the rows' frames.
- **Forward-compatible SP-6 fields**: `RowOK.align8` (mod-8 window alignment of every state pull to
  the public initial clock) and `LiveOK`'s frontier-time bound (`timeNat m ≤ t` per `some` record)
  are carried and re-established through the walk now, ahead of the intra-row chain rewrite that
  consumes them. -/

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

/-! ## Location-dependent schedule offsets -/

/-- The per-location write-effect offset of SP1's ordinary schedule: a register write lands at
`t + 4` (the op_a write offset), a RAM write at `t + 1` (the `MemoryAccess` push offset) — matching
`microValue`'s effect convention. -/
def writeOffset : MemLoc → ℕ
  | .reg _ => 4
  | .ram _ => 1

@[simp] lemma writeOffset_reg (i : BitVec 5) : writeOffset (MemLoc.reg i) = 4 := rfl

@[simp] lemma writeOffset_ram (a : BitVec 64) : writeOffset (MemLoc.ram a) = 1 := rfl

lemma writeOffset_le (loc : MemLoc) : writeOffset loc ≤ 4 := by
  cases loc <;> simp

/-- The per-location inclusive pre-effect read-window width: register reads observe pre-write
content anywhere in `[t, t + 3]`; RAM reads must sit at `δ = 0` (read time `= t`), since the RAM
effect lands at `t + 1`. -/
def readWindow : MemLoc → ℕ
  | .reg _ => 3
  | .ram _ => 0

@[simp] lemma readWindow_reg (i : BitVec 5) : readWindow (MemLoc.reg i) = 3 := rfl

@[simp] lemma readWindow_ram (a : BitVec 64) : readWindow (MemLoc.ram a) = 0 := rfl

/-! ## The per-row records -/

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
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  ∀ (loc : MemLoc) (v : Word (ZMod p)),
    (∀ m ∈ r.memPushes, MemoryMsg.locOf m = loc → m.value = v) →
    LocalValueAt initial initialClock loc (StateMsg.timeNat r.statePull) v →
    LocalValueAt initial initialClock loc (StateMsg.timeNat r.statePush) v

/-- The in-circuit-style shape/ordering facts for one paired pull/push touch of a row whose state-pull
time is `t`: same location, the pulled prior strictly predates the row, the read happens in the
location's pre-effect read window (`[t, t+3]` for registers, exactly `t` for RAM), and the push is
either a read-back (same value, pre-write time) or the write at `t + writeOffset` (`t + 4` register,
`t + 1` RAM). -/
structure TouchOK (t : ℕ) (mp : MemoryMsg (ZMod p) × ℕ) (q : MemoryMsg (ZMod p)) : Prop where
  loc_eq : MemoryMsg.locOf q = MemoryMsg.locOf mp.1
  pull_before : MemoryMsg.timeNat mp.1 < t
  read_lo : t ≤ mp.2
  read_hi : mp.2 ≤ t + readWindow (MemoryMsg.locOf mp.1)
  push_kind : (q.value = mp.1.value ∧ t ≤ MemoryMsg.timeNat q ∧ MemoryMsg.timeNat q ≤ t + 3) ∨
    MemoryMsg.timeNat q = t + writeOffset (MemoryMsg.locOf q)

/-- The in-circuit-style per-row facts: `+8` clock discipline, mod-8 window alignment to the public
initial clock (the SP-6 forward-compatibility field), positionally paired touches, and
pairwise-distinct touched locations. -/
structure RowOK (initialClock : ℕ) (r : RowFacts p) : Prop where
  time8 : StateMsg.timeNat r.statePush = StateMsg.timeNat r.statePull + 8
  align8 : StateMsg.timeNat r.statePull % 8 = initialClock % 8
  touches : List.Forall₂ (TouchOK (StateMsg.timeNat r.statePull)) r.memPulls r.memPushes
  locs_nodup : (r.memPushes.map MemoryMsg.locOf).Nodup

/-- The engine's per-row conclusion: every pull guarantee of the row holds (the state pull's
`LocalStateTruth`, each memory pull's `LocalMemTruth`), plus the read-time currency the row's step fact
consumed. -/
def Grounded (program : GuestProgram) (initial : SailState) (initialClock : ℕ)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program initial initialClock r.statePull ∧
  ∀ mp ∈ r.memPulls, LocalMemTruth initial initialClock mp.1 ∧
    LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value

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

/-- An optional boundary record as a multiset (per-key genesis/final frontier entries have length
≤ 1). -/
def optMS {α : Type} (o : Option α) : Multiset α := ↑o.toList

@[simp] lemma optMS_none {α : Type} : optMS (none : Option α) = 0 := rfl

@[simp] lemma optMS_some {α : Type} (a : α) : optMS (some a) = {a} := rfl

lemma mem_optMS {α : Type} {a : α} {o : Option α} : a ∈ optMS o ↔ o = some a := by
  cases o with
  | none => simp
  | some b => simp [eq_comm]

/-- The row's pulled prior messages at location `loc`. -/
def rowPullsAt (r : RowFacts p) (loc : MemLoc) : List (MemoryMsg (ZMod p)) :=
  (r.memPulls.map (·.1)).filter fun m => MemoryMsg.locOf m = loc

/-- The row's pushed messages at location `loc`. -/
def rowPushesAt (r : RowFacts p) (loc : MemLoc) : List (MemoryMsg (ZMod p)) :=
  r.memPushes.filter fun m => MemoryMsg.locOf m = loc

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

private lemma forall₂_exists_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ a ∈ l₁, ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hR _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hR⟩
    · obtain ⟨b, hb, hab⟩ := ih a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

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

private lemma forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → g b = f a) {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₂.map g = l₁.map f := by
  induction h with
  | nil => rfl
  | cons hR _ ih => simp [hfg _ _ hR, ih]

/-- In a list whose `g`-image is `Nodup`, filtering at a member's `g`-value yields that singleton. -/
private lemma filter_map_nodup_singleton {α β : Type} [DecidableEq β] (g : α → β) :
    ∀ (l : List α), (l.map g).Nodup → ∀ a ∈ l, ∀ (b : β), g a = b →
      l.filter (fun x => g x = b) = [a]
  | [], _, a, ha => absurd ha (List.not_mem_nil)
  | x :: l, hnd, a, ha => by
    intro b hab
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [List.filter_cons_of_pos (by simp [hab])]
      have : l.filter (fun x => g x = b) = [] := by
        refine List.filter_eq_nil_iff.mpr fun c hc hgc => ?_
        simp only [decide_eq_true_eq] at hgc
        exact hnd.1 (by rw [hab, ← hgc]; exact List.mem_map_of_mem hc)
      rw [this]
    · rw [List.filter_cons_of_neg ?_, filter_map_nodup_singleton g l hnd.2 a ha' b hab]
      simp only [decide_eq_true_eq]
      intro hgx
      exact hnd.1 (by rw [hgx, ← hab]; exact List.mem_map_of_mem ha')

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
/-- All pushes of a row happen at/after its state-pull time. -/
lemma push_time_ge {c0 : ℕ} {r : RowFacts p} (hok : RowOK c0 r) {q : MemoryMsg (ZMod p)}
    (hq : q ∈ r.memPushes) : StateMsg.timeNat r.statePull ≤ MemoryMsg.timeNat q := by
  obtain ⟨mp, -, hto⟩ := forall₂_exists_left hok.touches q hq
  rcases hto.push_kind with ⟨-, h, -⟩ | h <;> omega

/-! ## The timed grounding walk -/

omit [Fact (2 ^ 17 < p)] in
/-- **The ordinary timed grounding theorem.** Given per-row `LocalStepFact`s and
`FrameFact`s, the in-circuit-style shape/ordering facts (`RowOK`), a true head state record
(`LocalStateTruth head` — the boundary init push at the top level), a true partial per-key memory
frontier (`LiveOK` — the genesis pushes at the top level), and the state/memory multiset balances,
**every pull's guarantee holds**: each row is `Grounded` (its state pull's `LocalStateTruth`, its
memory pulls' `LocalMemTruth`s, and its read-time currencies), the final state pull `fin` is true, and
each key's finalize pull `finM loc` (where present) is true.

Strong induction on the batch size: pop the row with minimal state-pull time; balance + time
discipline force it to pull `head` (layer A) and its memory pulls to equal the frontier — in
particular balance forces a `some` genesis at every key the row pulls (layer B); its `LocalStepFact`
fires (layer C), and its pushes/`FrameFact` rebuild the invariant one window later. -/
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
    -- (B) every memory pull of `r` equals the per-key frontier: its match in the per-key balance
    -- cannot be a push (all push times sit at/after their row's window ≥ the minimal window, while
    -- the pulled prior strictly predates it) — so balance forces a `some` genesis at the key.
    have h_match : ∀ mp ∈ r.memPulls, live (MemoryMsg.locOf mp.1) = some mp.1 := by
      intro mp hmp
      obtain ⟨q, hq_mem, hto⟩ := forall₂_exists_right h_rok.touches mp hmp
      have hmem : mp.1 ∈ optMS (live (MemoryMsg.locOf mp.1))
          + pushesAt rows (MemoryMsg.locOf mp.1) := by
        rw [h_mbal (MemoryMsg.locOf mp.1)]
        refine Multiset.mem_add.mpr (Or.inr ?_)
        simp only [pullsAt, mem_listSum_map]
        exact ⟨r, hr_mem, Multiset.mem_coe.mpr (List.mem_filter.mpr
          ⟨List.mem_map_of_mem hmp, by simp⟩)⟩
      rcases Multiset.mem_add.mp hmem with h | h
      · exact mem_optMS.mp h
      · exfalso
        simp only [pushesAt, mem_listSum_map] at h
        obtain ⟨r', hr'_mem, hq'⟩ := h
        have hq'_mem : mp.1 ∈ r'.memPushes :=
          List.mem_of_mem_filter (Multiset.mem_coe.mp hq')
        have h1 := push_time_ge (h_ok r' hr'_mem) hq'_mem
        have h2 := hr_min r' hr'_mem
        have h3 := hto.pull_before
        omega
    -- read-time currency for `r`'s pulls, from the frontier + intra-epoch shift (register reads
    -- shift within the pre-write half-window; RAM reads are pinned at the window start)
    have h_curr : ∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
      intro mp hmp
      obtain ⟨-, hmt_live, hval_live, -⟩ := h_live _ mp.1 (h_match mp hmp)
      obtain ⟨q, hq_mem, hto⟩ := forall₂_exists_right h_rok.touches mp hmp
      refine ⟨hmt_live.1, ?_⟩
      have hlo := hto.read_lo
      have hhi := hto.read_hi
      cases hloc : MemoryMsg.locOf mp.1 with
      | reg i =>
        rw [hloc, readWindow_reg] at hhi
        rw [hloc] at hval_live
        exact localValueAt_shift h_head
          (Or.inl ⟨le_refl _, by omega, by omega, by omega⟩) hval_live
      | ram a =>
        rw [hloc, readWindow_ram] at hhi
        rw [hloc] at hval_live
        have hread : mp.2 = StateMsg.timeNat head := by omega
        rw [hread]
        exact hval_live
    -- (C) fire the row's StepFact
    have h_after := h_step r hr_mem h_rtruth h_curr
    have h_ground_r : Grounded program initial initialClock r := ⟨h_rtruth, fun mp hmp =>
      ⟨(h_live _ mp.1 (h_match mp hmp)).2.1, (h_curr mp hmp).2⟩⟩
    -- pop `r` out of the batch
    obtain ⟨l1, l2, rfl⟩ : ∃ l1 l2, rows = l1 ++ r :: l2 := List.append_of_mem hr_mem
    have hlen' : (l1 ++ l2).length = N := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    have hsub : ∀ r' ∈ l1 ++ l2, r' ∈ l1 ++ r :: l2 := by
      intro r' hr'
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    -- the row's per-key contributions are singletons (distinct touched locations)
    have h_maps : r.memPushes.map MemoryMsg.locOf
        = r.memPulls.map (fun mp => MemoryMsg.locOf mp.1) :=
      forall₂_map_eq (fun _ _ hto => hto.loc_eq) h_rok.touches
    have h_pulls_nodup : ((r.memPulls.map (·.1)).map MemoryMsg.locOf).Nodup := by
      rw [List.map_map]
      show (r.memPulls.map (fun mp => MemoryMsg.locOf mp.1)).Nodup
      rw [← h_maps]
      exact h_rok.locs_nodup
    have h_touch_push : ∀ (loc : MemLoc), ∀ q ∈ r.memPushes,
        MemoryMsg.locOf q = loc → rowPushesAt r loc = [q] := by
      intro loc q hq hloc
      unfold rowPushesAt
      exact filter_map_nodup_singleton _ _ h_rok.locs_nodup q hq _ hloc
    have h_touch_pull : ∀ (loc : MemLoc), ∀ mp ∈ r.memPulls,
        MemoryMsg.locOf mp.1 = loc → rowPullsAt r loc = [mp.1] := by
      intro loc mp hmp hloc
      unfold rowPullsAt
      exact filter_map_nodup_singleton _ _ h_pulls_nodup mp.1 (List.mem_map_of_mem hmp) _ hloc
    have h_untouched : ∀ loc : MemLoc,
        (¬ ∃ q ∈ r.memPushes, MemoryMsg.locOf q = loc) →
        rowPushesAt r loc = [] ∧ rowPullsAt r loc = [] := by
      intro loc hno
      constructor
      · unfold rowPushesAt
        refine List.filter_eq_nil_iff.mpr fun q hq hloc => ?_
        simp only [decide_eq_true_eq] at hloc
        exact hno ⟨q, hq, hloc⟩
      · unfold rowPullsAt
        refine List.filter_eq_nil_iff.mpr fun m hm hloc => ?_
        simp only [decide_eq_true_eq] at hloc
        obtain ⟨mp, hmp, rfl⟩ := List.mem_map.mp hm
        obtain ⟨q, hq, hto⟩ := forall₂_exists_right h_rok.touches mp hmp
        exact hno ⟨q, hq, hto.loc_eq.trans hloc⟩
    have h8 := h_rok.time8
    -- the new frontier: the row's push where it touched, unchanged (possibly absent) elsewhere
    have h_liveOK' : LiveOK initial initialClock (StateMsg.timeNat r.statePush)
        (fun loc => (rowPushesAt r loc).head?.or (live loc)) := by
      intro loc m hm
      dsimp only at hm
      by_cases htouch : ∃ q ∈ r.memPushes, MemoryMsg.locOf q = loc
      · obtain ⟨q, hq_mem, hq_loc⟩ := htouch
        rw [h_touch_push loc q hq_mem hq_loc] at hm
        simp only [List.head?_cons, Option.some_or, Option.some.injEq] at hm
        subst hm
        obtain ⟨mp, hmp_mem, hto⟩ := forall₂_exists_left h_rok.touches q hq_mem
        have hmp_loc : MemoryMsg.locOf mp.1 = loc := by rw [← hto.loc_eq]; exact hq_loc
        have hlive_eq := h_match mp hmp_mem
        rw [hmp_loc] at hlive_eq
        obtain ⟨-, -, hval_live, -⟩ := h_live loc mp.1 hlive_eq
        refine ⟨hq_loc, h_after.2 q hq_mem, ?_, ?_⟩
        · rcases hto.push_kind with ⟨hvq, hlo, hhi⟩ | hw
          · -- read-back: the pushed value is the (still-current) pulled value — frame across
            refine h_frame r hr_mem h_rtruth h_curr loc q.value ?_ ?_
            · intro m' hm' hml
              have hqm : ([q] : List (MemoryMsg (ZMod p))) = [m'] := by
                rw [← h_touch_push loc q hq_mem hq_loc, h_touch_push loc m' hm' hml]
              have hq_eq : q = m' := by simpa using hqm
              rw [← hq_eq]
            · rw [hvq, ht_head]
              exact hval_live
          · -- write: the push's own MemTruth at `t + writeOffset`, shifted to the window end
            have hmt := (h_after.2 q hq_mem).2
            rw [hq_loc] at hmt hw
            cases loc with
            | reg i =>
              rw [writeOffset_reg] at hw
              exact localValueAt_shift h_head
                (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
            | ram a =>
              rw [writeOffset_ram] at hw
              exact localValueAt_shift_ram h_head
                (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
        · -- frontier-time bound: read-backs sit in the pre-write window, writes at `+offset ≤ +4`
          rcases hto.push_kind with ⟨-, -, hhi⟩ | hw
          · omega
          · have hle := writeOffset_le (MemoryMsg.locOf q)
            omega
      · obtain ⟨hp, -⟩ := h_untouched loc htouch
        rw [hp] at hm
        simp only [List.head?_nil, Option.none_or] at hm
        obtain ⟨hloc_m, hmt_m, hval_m, htime_m⟩ := h_live loc m hm
        refine ⟨hloc_m, hmt_m, ?_, by omega⟩
        refine h_frame r hr_mem h_rtruth h_curr loc m.value ?_ ?_
        · intro m' hm' hml
          exact absurd ⟨m', hm', hml⟩ htouch
        · rw [ht_head]
          exact hval_m
    -- state balance advances: cancel the consumed head
    have h_sbal' : r.statePush ::ₘ (↑((l1 ++ l2).map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑((l1 ++ l2).map (·.statePull)) := by
      have h := h_sbal
      rw [coe_map_pop, coe_map_pop, hr_pull, Multiset.cons_swap fin head] at h
      exact (Multiset.cons_inj_right _).mp h
    -- per-key memory balance advances: cancel the consumed frontier
    have h_mbal' : ∀ loc : MemLoc,
        optMS ((rowPushesAt r loc).head?.or (live loc)) + pushesAt (l1 ++ l2) loc
          = optMS (finM loc) + pullsAt (l1 ++ l2) loc := by
      intro loc
      have hbal := h_mbal loc
      simp only [pushesAt, pullsAt] at hbal ⊢
      rw [listSum_map_pop, listSum_map_pop] at hbal
      by_cases htouch : ∃ q ∈ r.memPushes, MemoryMsg.locOf q = loc
      · obtain ⟨q, hq_mem, hq_loc⟩ := htouch
        obtain ⟨mp, hmp_mem, hto⟩ := forall₂_exists_left h_rok.touches q hq_mem
        have hmp_loc : MemoryMsg.locOf mp.1 = loc := by rw [← hto.loc_eq]; exact hq_loc
        have hlive_eq := h_match mp hmp_mem
        rw [hmp_loc] at hlive_eq
        rw [h_touch_push loc q hq_mem hq_loc, h_touch_pull loc mp hmp_mem hmp_loc,
          hlive_eq] at hbal
        rw [h_touch_push loc q hq_mem hq_loc]
        simp only [List.head?_cons, Option.some_or, optMS_some, Multiset.coe_singleton,
          Multiset.singleton_add] at hbal ⊢
        rw [Multiset.add_cons] at hbal
        exact (Multiset.cons_inj_right _).mp hbal
      · obtain ⟨hp, hl⟩ := h_untouched loc htouch
        rw [hp, hl] at hbal
        rw [hp]
        simp only [List.head?_nil, Option.none_or, Multiset.coe_nil, Multiset.zero_add]
          at hbal ⊢
        exact hbal
    -- recurse on the rest
    obtain ⟨hg_rest, hfin, hfinM⟩ := ih (l1 ++ l2) r.statePush
      (fun loc => (rowPushesAt r loc).head?.or (live loc)) hlen'
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
