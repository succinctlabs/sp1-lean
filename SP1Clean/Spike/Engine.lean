import SP1Clean.Model.Semantics.Truth

/-! # Spike engine — the minimal timed grounding theorem

**Phase-1 de-risk spike** (`SP1Clean/Spike/`, deleted after the real sweep). The timestamped grounding
induction: given a batch of row-fact records (each carrying its `StepFact` and a `FrameFact`), a true
boundary state push, per-key multiset balance of the state and memory records, and the in-circuit-style
per-row ordering/shape facts, **every pull's guarantee holds** — and in particular the final state
pull's `StateTruth` and the memory finalize pulls' `MemTruth`.

Design decisions (spike license, documented for the Phase-2+ report):

- **Balance representation**: plain `Multiset` equalities over lists of messages (no
  `LookupAccessList`/`BalanceBridge` detour) — `{init} + pushes = {fin} + pulls` per bus/key. The
  field→ℤ→multiset translation from the real channel data is a separate seam
  (`Model/BalanceBridge.lean` is the existing adapter).
- **Registers only, straight-line, single row type**: the memory keys are register indices
  (`BitVec 5`); every row's touched locations are register-shaped and pairwise distinct
  (`RowOK.locs_nodup` — intra-row same-register chaining is a Phase-2+ walk-invariant refinement).
- **The three layers collapse into one strong induction** on the remaining rows (`walk`): at each step
  the row with **minimal state-pull time** is popped; balance + per-row time discipline force its
  state pull to equal the running head (layer A: unique live record per level), its memory pulls to
  equal the per-key `live` frontier messages (layer B: per-key push uniqueness ⇒ chain linearity),
  and its `StepFact`/`FrameFact` fire to advance the head, the frontier, and the truth invariants
  (layer C: step facts fire in time order).
- **`FrameFact` is a required per-row record beyond `Truth.StepFact`**: `StepFact` alone cannot give
  the engine value-persistence across a window for locations the row does not change — a key Phase-1
  finding: the per-chip `advance` obligation must include a register-frame fact.
- The `microValue` **register-epoch lemmas** (`regEpoch`, `microValue_reg`, `valueAt_shift`) are the
  semantic crux of "chain linearity ⇒ currency": for registers, the trajectory content is constant on
  each epoch `[c0+8k+4, c0+8(k+1)+4)`, so intra-window shifts are free and cross-window persistence
  reduces to the rows' frames. -/

namespace SP1Clean.Spike

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
  simp [stepOnce, hrun]

/-- Extend a determined trajectory by one determined step. -/
lemma chainState_succ_of {s0 s s' : SailState} {n : ℕ}
    (h : chainState s0 n = some s) (h' : stepOnce s = some s') :
    chainState s0 (n + 1) = some s' := by
  rw [chainState, h, Option.bind_some, h']

omit [Fact (2 ^ 17 < p)] in
/-- **Intra-epoch shift.** A register `ValueAt` fact moves freely between two times of the same epoch
of the same execution window; the window alignment (`τ ≡ c0 mod 8`-gradedness) is read off the state
message's `StateTruth` per loader. Window `Or.inl`: both times in the pre-write half `[t, t+4)`;
`Or.inr`: both in the post-write epoch `[t+4, t+12)`. -/
lemma valueAt_shift {data : ProverData (ZMod p)} {m : StateMsg (ZMod p)}
    (h_m : StateTruth m data) {i : BitVec 5} {v : Word (ZMod p)} {τ τ' : ℕ}
    (hwin : (StateMsg.timeNat m ≤ τ ∧ τ < StateMsg.timeNat m + 4 ∧
             StateMsg.timeNat m ≤ τ' ∧ τ' < StateMsg.timeNat m + 4) ∨
            (StateMsg.timeNat m + 4 ≤ τ ∧ τ < StateMsg.timeNat m + 12 ∧
             StateMsg.timeNat m + 4 ≤ τ' ∧ τ' < StateMsg.timeNat m + 12))
    (h : ValueAt data (MemLoc.reg i) τ v) :
    ValueAt data (MemLoc.reg i) τ' v := by
  intro s0 hini hzero
  obtain ⟨n, -, -, htime, -, -, -⟩ := h_m s0 hini hzero
  have hv := h s0 hini hzero
  rw [microValue_reg] at hv ⊢
  have he : regEpoch (Commit.initClkNat data) τ' = regEpoch (Commit.initClkNat data) τ := by
    rcases hwin with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rw [regEpoch_eq_of (n := n) (by omega) (by omega),
        regEpoch_eq_of (n := n) (by omega) (by omega)]
    · rw [regEpoch_eq_succ_of (n := n) (by omega) (by omega),
        regEpoch_eq_succ_of (n := n) (by omega) (by omega)]
  rw [he]
  exact hv

/-! ## The per-row records -/

/-- **The per-row frame obligation** (a Phase-1 finding: `Truth.StepFact` alone is not enough for the
engine — each row must also certify that it does not disturb registers it does not change). Under the
same hypotheses as `StepFact` (pulled state truth + operand currency), for any register whose pushes
this row all agree with `v` (untouched: vacuous; read-back: the re-pushed value; write: the written
value when it happens to equal `v`), a `ValueAt v` fact advances across the row's window. -/
def FrameFact (data : ProverData (ZMod p)) (r : RowFacts p) : Prop :=
  StateTruth r.statePull data →
  (∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
      ValueAt data (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  ∀ (i : BitVec 5) (v : Word (ZMod p)),
    (∀ m ∈ r.memPushes, MemoryMsg.locOf m = MemLoc.reg i → m.value = v) →
    ValueAt data (MemLoc.reg i) (StateMsg.timeNat r.statePull) v →
    ValueAt data (MemLoc.reg i) (StateMsg.timeNat r.statePush) v

/-- The in-circuit-style shape/ordering facts for one paired pull/push touch of a row whose state-pull
time is `t`: same (register) location, the pulled prior strictly predates the row, the read happens in
the row's pre-write half-window, and the push is either a read-back (same value, pre-write time) or
the write at `t + 4`. -/
structure TouchOK (t : ℕ) (mp : MemoryMsg (ZMod p) × ℕ) (q : MemoryMsg (ZMod p)) : Prop where
  loc_eq : MemoryMsg.locOf q = MemoryMsg.locOf mp.1
  is_reg : ∃ i : BitVec 5, MemoryMsg.locOf q = MemLoc.reg i
  pull_before : MemoryMsg.timeNat mp.1 < t
  read_lo : t ≤ mp.2
  read_hi : mp.2 ≤ t + 3
  push_kind : (q.value = mp.1.value ∧ t ≤ MemoryMsg.timeNat q ∧ MemoryMsg.timeNat q ≤ t + 3) ∨
    MemoryMsg.timeNat q = t + 4

/-- The in-circuit-style per-row facts: `+8` clock discipline, positionally paired touches, and
pairwise-distinct touched locations. -/
structure RowOK (r : RowFacts p) : Prop where
  time8 : StateMsg.timeNat r.statePush = StateMsg.timeNat r.statePull + 8
  touches : List.Forall₂ (TouchOK (StateMsg.timeNat r.statePull)) r.memPulls r.memPushes
  locs_nodup : (r.memPushes.map MemoryMsg.locOf).Nodup

/-- The engine's per-row conclusion: every pull guarantee of the row holds (the state pull's
`StateTruth`, each memory pull's `MemTruth`), plus the read-time currency the row's `StepFact`
consumed. -/
def Grounded (data : ProverData (ZMod p)) (r : RowFacts p) : Prop :=
  StateTruth r.statePull data ∧
  ∀ mp ∈ r.memPulls, MemTruth mp.1 data ∧
    ValueAt data (MemoryMsg.locOf mp.1) mp.2 mp.1.value

/-- The walk invariant for the per-key memory frontier `live`: each key's frontier message sits at
that key, its own guarantee (`MemTruth`) holds, and its value is current at the head time `t`. -/
def LiveOK (data : ProverData (ZMod p)) (t : ℕ) (live : BitVec 5 → MemoryMsg (ZMod p)) : Prop :=
  ∀ i : BitVec 5, MemoryMsg.locOf (live i) = MemLoc.reg i ∧
    MemTruth (live i) data ∧
    ValueAt data (MemLoc.reg i) t (live i).value

/-! ## Per-key record lists -/

/-- The row's pulled prior messages at register `i`. -/
def rowPullsAt (r : RowFacts p) (i : BitVec 5) : List (MemoryMsg (ZMod p)) :=
  (r.memPulls.map (·.1)).filter fun m => MemoryMsg.locOf m = MemLoc.reg i

/-- The row's pushed messages at register `i`. -/
def rowPushesAt (r : RowFacts p) (i : BitVec 5) : List (MemoryMsg (ZMod p)) :=
  r.memPushes.filter fun m => MemoryMsg.locOf m = MemLoc.reg i

/-- All pulled prior messages of a batch at register `i` (as a multiset — order is irrelevant). -/
def pullsAt (rows : List (RowFacts p)) (i : BitVec 5) : Multiset (MemoryMsg (ZMod p)) :=
  (rows.map fun r => (↑(rowPullsAt r i) : Multiset (MemoryMsg (ZMod p)))).sum

/-- All pushed messages of a batch at register `i`. -/
def pushesAt (rows : List (RowFacts p)) (i : BitVec 5) : Multiset (MemoryMsg (ZMod p)) :=
  (rows.map fun r => (↑(rowPushesAt r i) : Multiset (MemoryMsg (ZMod p)))).sum

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
lemma push_time_ge {r : RowFacts p} (hok : RowOK r) {q : MemoryMsg (ZMod p)}
    (hq : q ∈ r.memPushes) : StateMsg.timeNat r.statePull ≤ MemoryMsg.timeNat q := by
  obtain ⟨mp, -, hto⟩ := forall₂_exists_left hok.touches q hq
  rcases hto.push_kind with ⟨-, h, -⟩ | h <;> omega

/-! ## The timed grounding walk -/

omit [Fact (2 ^ 17 < p)] in
/-- **The timed grounding theorem** (the spike's engine capstone). Given per-row `StepFact`s and
`FrameFact`s, the in-circuit-style shape/ordering facts (`RowOK`), a true head state record
(`StateTruth head` — the boundary init push at the top level), a true per-key memory frontier
(`LiveOK` — the genesis pushes at the top level), and the state/memory multiset balances, **every
pull's guarantee holds**: each row is `Grounded` (its state pull's `StateTruth`, its memory pulls'
`MemTruth`s, and its read-time currencies), the final state pull `fin` is true, and each key's
finalize pull `finM i` is true.

Strong induction on the batch size: pop the row with minimal state-pull time; balance + time
discipline force it to pull `head` (layer A) and its memory pulls to equal the frontier (layer B);
its `StepFact` fires (layer C), and its pushes/`FrameFact` rebuild the invariant one window later. -/
theorem walk (data : ProverData (ZMod p)) (fin : StateMsg (ZMod p))
    (finM : BitVec 5 → MemoryMsg (ZMod p)) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : BitVec 5 → MemoryMsg (ZMod p)),
      rows.length = N →
      (∀ r ∈ rows, StepFact data r) →
      (∀ r ∈ rows, FrameFact data r) →
      (∀ r ∈ rows, RowOK r) →
      StateTruth head data →
      LiveOK data (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ i : BitVec 5, (live i) ::ₘ pushesAt rows i = (finM i) ::ₘ pullsAt rows i) →
      (∀ r ∈ rows, Grounded data r) ∧ StateTruth fin data ∧
        ∀ i : BitVec 5, MemTruth (finM i) data := by
  intro N
  induction N with
  | zero =>
    intro rows head live hlen _ _ _ h_head h_live h_sbal h_mbal
    obtain rfl : rows = [] := List.length_eq_zero_iff.mp hlen
    have h_fin : head = fin := by simpa using h_sbal
    refine ⟨by simp, h_fin ▸ h_head, fun i => ?_⟩
    have h_fm : live i = finM i := by simpa [pullsAt, pushesAt] using h_mbal i
    exact h_fm ▸ (h_live i).2.1
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
    have h_rtruth : StateTruth r.statePull data := by rw [hr_pull]; exact h_head
    have ht_head : StateMsg.timeNat r.statePull = StateMsg.timeNat head := by rw [hr_pull]
    -- (B) every memory pull of `r` equals the per-key frontier: its match in the per-key balance
    -- cannot be a push (all push times sit at/after their row's window ≥ the minimal window, while
    -- the pulled prior strictly predates it).
    have h_match : ∀ mp ∈ r.memPulls, ∃ i : BitVec 5,
        MemoryMsg.locOf mp.1 = MemLoc.reg i ∧ mp.1 = live i := by
      intro mp hmp
      obtain ⟨q, hq_mem, hto⟩ := forall₂_exists_right h_rok.touches mp hmp
      obtain ⟨i, hqi⟩ := hto.is_reg
      have hloc : MemoryMsg.locOf mp.1 = MemLoc.reg i := by rw [← hto.loc_eq]; exact hqi
      refine ⟨i, hloc, ?_⟩
      have hmem : mp.1 ∈ ((live i) ::ₘ pushesAt rows i) := by
        rw [h_mbal i]
        refine Multiset.mem_cons_of_mem ?_
        simp only [pullsAt, mem_listSum_map]
        exact ⟨r, hr_mem, Multiset.mem_coe.mpr (List.mem_filter.mpr
          ⟨List.mem_map_of_mem hmp, by simp [hloc]⟩)⟩
      rcases Multiset.mem_cons.mp hmem with h | h
      · exact h
      · exfalso
        simp only [pushesAt, mem_listSum_map] at h
        obtain ⟨r', hr'_mem, hq'⟩ := h
        have hq'_mem : mp.1 ∈ r'.memPushes :=
          List.mem_of_mem_filter (Multiset.mem_coe.mp hq')
        have h1 := push_time_ge (h_ok r' hr'_mem) hq'_mem
        have h2 := hr_min r' hr'_mem
        have h3 := hto.pull_before
        omega
    -- read-time currency for `r`'s pulls, from the frontier + intra-epoch shift
    have h_curr : ∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        ValueAt data (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
      intro mp hmp
      obtain ⟨i, hloc, hlive⟩ := h_match mp hmp
      obtain ⟨q, hq_mem, hto⟩ := forall₂_exists_right h_rok.touches mp hmp
      refine ⟨by rw [hlive]; exact (h_live i).2.1.1, ?_⟩
      rw [hloc, hlive]
      refine valueAt_shift h_head (Or.inl ⟨le_refl _, by omega, ?_, ?_⟩) (h_live i).2.2
      · have := hto.read_lo; omega
      · have := hto.read_hi; omega
    -- (C) fire the row's StepFact
    have h_after := h_step r hr_mem h_rtruth h_curr
    have h_ground_r : Grounded data r := ⟨h_rtruth, fun mp hmp => by
      obtain ⟨i, hloc, hlive⟩ := h_match mp hmp
      exact ⟨by rw [hlive]; exact (h_live i).2.1, (h_curr mp hmp).2⟩⟩
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
    have h_touch_push : ∀ (i : BitVec 5), ∀ q ∈ r.memPushes,
        MemoryMsg.locOf q = MemLoc.reg i → rowPushesAt r i = [q] := by
      intro i q hq hloc
      unfold rowPushesAt
      exact filter_map_nodup_singleton _ _ h_rok.locs_nodup q hq _ hloc
    have h_touch_pull : ∀ (i : BitVec 5), ∀ mp ∈ r.memPulls,
        MemoryMsg.locOf mp.1 = MemLoc.reg i → rowPullsAt r i = [mp.1] := by
      intro i mp hmp hloc
      unfold rowPullsAt
      exact filter_map_nodup_singleton _ _ h_pulls_nodup mp.1 (List.mem_map_of_mem hmp) _ hloc
    have h_untouched : ∀ i : BitVec 5,
        (¬ ∃ q ∈ r.memPushes, MemoryMsg.locOf q = MemLoc.reg i) →
        rowPushesAt r i = [] ∧ rowPullsAt r i = [] := by
      intro i hno
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
    -- the new frontier: the row's push where it touched, unchanged elsewhere
    have h_liveOK' : LiveOK data (StateMsg.timeNat r.statePush)
        (fun i => (rowPushesAt r i).headD (live i)) := by
      intro i
      dsimp only
      by_cases htouch : ∃ q ∈ r.memPushes, MemoryMsg.locOf q = MemLoc.reg i
      · obtain ⟨q, hq_mem, hq_loc⟩ := htouch
        rw [h_touch_push i q hq_mem hq_loc]
        simp only [List.headD_cons]
        obtain ⟨mp, hmp_mem, hto⟩ := forall₂_exists_left h_rok.touches q hq_mem
        have hmp_loc : MemoryMsg.locOf mp.1 = MemLoc.reg i := by rw [← hto.loc_eq]; exact hq_loc
        obtain ⟨i', hloc', hlive_eq⟩ := h_match mp hmp_mem
        rw [MemLoc.reg.inj (hloc'.symm.trans hmp_loc)] at hlive_eq
        refine ⟨hq_loc, h_after.2 q hq_mem, ?_⟩
        rcases hto.push_kind with ⟨hvq, hlo, hhi⟩ | hw
        · -- read-back: the pushed value is the (still-current) pulled value — frame across the window
          refine h_frame r hr_mem h_rtruth h_curr i q.value ?_ ?_
          · intro m hm hml
            have hqm : ([q] : List (MemoryMsg (ZMod p))) = [m] := by
              rw [← h_touch_push i q hq_mem hq_loc, h_touch_push i m hm hml]
            have hq_eq : q = m := by simpa using hqm
            rw [← hq_eq]
          · rw [hvq, hlive_eq, ht_head]
            exact (h_live i).2.2
        · -- write: the push's own MemTruth at `t+4`, shifted to the window end
          have hmt := (h_after.2 q hq_mem).2
          rw [hq_loc] at hmt
          exact valueAt_shift h_head (Or.inr ⟨by omega, by omega, by omega, by omega⟩) hmt
      · obtain ⟨hp, -⟩ := h_untouched i htouch
        rw [hp]
        simp only [List.headD_nil]
        refine ⟨(h_live i).1, (h_live i).2.1, ?_⟩
        refine h_frame r hr_mem h_rtruth h_curr i (live i).value ?_ ?_
        · intro m hm hml
          exact absurd ⟨m, hm, hml⟩ htouch
        · rw [ht_head]
          exact (h_live i).2.2
    -- state balance advances: cancel the consumed head
    have h_sbal' : r.statePush ::ₘ (↑((l1 ++ l2).map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑((l1 ++ l2).map (·.statePull)) := by
      have h := h_sbal
      rw [coe_map_pop, coe_map_pop, hr_pull, Multiset.cons_swap fin head] at h
      exact (Multiset.cons_inj_right _).mp h
    -- per-key memory balance advances: cancel the consumed frontier
    have h_mbal' : ∀ i : BitVec 5,
        ((rowPushesAt r i).headD (live i)) ::ₘ pushesAt (l1 ++ l2) i
          = (finM i) ::ₘ pullsAt (l1 ++ l2) i := by
      intro i
      have hbal := h_mbal i
      simp only [pushesAt, pullsAt] at hbal ⊢
      rw [listSum_map_pop, listSum_map_pop] at hbal
      by_cases htouch : ∃ q ∈ r.memPushes, MemoryMsg.locOf q = MemLoc.reg i
      · obtain ⟨q, hq_mem, hq_loc⟩ := htouch
        obtain ⟨mp, hmp_mem, hto⟩ := forall₂_exists_left h_rok.touches q hq_mem
        have hmp_loc : MemoryMsg.locOf mp.1 = MemLoc.reg i := by rw [← hto.loc_eq]; exact hq_loc
        obtain ⟨i', hloc', hlive_eq⟩ := h_match mp hmp_mem
        rw [MemLoc.reg.inj (hloc'.symm.trans hmp_loc)] at hlive_eq
        rw [h_touch_push i q hq_mem hq_loc, h_touch_pull i mp hmp_mem hmp_loc, hlive_eq] at hbal
        rw [h_touch_push i q hq_mem hq_loc]
        simp only [List.headD_cons]
        simp only [Multiset.coe_singleton, Multiset.singleton_add] at hbal
        rw [Multiset.cons_swap (finM i) (live i)] at hbal
        exact (Multiset.cons_inj_right _).mp hbal
      · obtain ⟨hp, hl⟩ := h_untouched i htouch
        rw [hp, hl] at hbal
        rw [hp]
        simp only [List.headD_nil, Multiset.coe_nil, Multiset.zero_add] at hbal ⊢
        exact hbal
    -- recurse on the rest
    obtain ⟨hg_rest, hfin, hfinM⟩ := ih (l1 ++ l2) r.statePush
      (fun i => (rowPushesAt r i).headD (live i)) hlen'
      (fun r' h => h_step r' (hsub r' h)) (fun r' h => h_frame r' (hsub r' h))
      (fun r' h => h_ok r' (hsub r' h)) h_after.1 h_liveOK' h_sbal' h_mbal'
    refine ⟨?_, hfin, hfinM⟩
    intro r' hr'
    rcases List.mem_append.mp hr' with h | h
    · exact hg_rest r' (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact h_ground_r
      · exact hg_rest r' (List.mem_append_right _ h)

end SP1Clean.Spike
