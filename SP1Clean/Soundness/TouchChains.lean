import SP1Clean.Model.Semantics.Truth

/-! # Intra-row same-key touch chains — the SP-6 port

The production port of `docs/spikes/sp6_intra_row_chains.lean`: within one row at window time `t`,
the same-key Memory touches form a **slot-ordered chain** — the first pull claims a strictly
pre-row record, each later pull re-claims the row's own previous push, and push times are strictly
increasing inside the row window. This admits register-alias rows (`add x1, x1, x2`; `bne x1, x1`),
which the previous `RowOK.locs_nodup` invariant excluded.

Everything here is restated over the real bus types: keys are `MemoryMsg.locOf`, times are
`MemoryMsg.timeNat`/`StateMsg.timeNat`, rows are `RowFacts`. The multiset algebra is Fact-free, so
this module carries no field assumptions. Contents:

* the per-location schedule offsets (`writeOffset`/`readWindow`) and the `optMS` boundary coercion
  (moved here from `TimedGrounding.lean`; same namespace, so all names are unchanged);
* `Touch`/`TouchOK` — one positionally paired (pull, push) touch and its in-circuit per-slot facts.
  Per SP-6 deviations D4/D5, `TouchOK` certifies **no** chain links and no pre-row head-pull bound:
  the head-pull identification and the intra-row links are *derived* from balance. `pull_before`
  (`pull.time < t`) is replaced by the honest `prev_clk < access_clk` bound `pull_lt_push`, and the
  read-back branch of `push_kind` pins the pushed record at the read micro-time (`timeNat q = mp.2`,
  what SP1's memory argument actually does) — the production value-layer fact that makes
  reads-after-write structurally impossible (see `readback_of_succ`);
* `rowTouchesAt` — the row's same-key touch chain at a location (the filtered pull/push zip), with
  the `rowPullsAt`/`rowPushesAt` filter equivalences;
* `ChainOK` — the per-key chain bundle (keys, `prev_clk < clk` slots, read windows, push kinds,
  slot-monotone push times), built from `RowOK` by `RowOK.chainOK` in `TimedGrounding.lean`;
* the six spike theorems: `chain_shift`, `chainLinks_of_balance` (D4 — links from balance),
  `chainForcing_step` (chain cancellation), `chainForcing_step_of_gap` (the walk's per-key step:
  forcing + links + cancellation + the re-established frontier bound), and the state-bus pair
  `stateBalance_unique_minimal` / `stateBalance_remaining_ge_eight` (invariants 2 + 1: the `t + 8`
  gap for every remaining row, consumed as the other-rows' push gap);
* the value layer the spike deliberately left to production: `chain_pull_values` (every pull in a
  chain carries the frontier value — a write can never be followed by another same-key slot),
  `chain_push_values` (with a read-back last slot, every push carries the frontier value — the
  `FrameFact` input), and `chain_pull_head_or_push` (every pull is the head or a row-own push — the
  `LocalMemTruth` routing).

Production deviations from the spike, beyond re-typing: the memory-side frontier is threaded as an
`Option` (`optMS live`) because the walk's per-key frontier map is partial, and the balance RHS
folds the spike's `finM ::ₘ Q` into one unconstrained multiset `R`; the head-pull forcing lives in
`chainLinks_of_balance` (not `chainForcing_step`) since `head_lt` is no longer certified — exactly
the D4/D5 resolution. -/

namespace SP1Clean.Soundness.TimedGrounding

open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ}

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

lemma readWindow_le (loc : MemLoc) : readWindow loc ≤ 3 := by
  cases loc <;> simp

/-! ## Optional boundary records -/

/-- An optional boundary record as a multiset (per-key genesis/final frontier entries have length
≤ 1). -/
def optMS {α : Type} (o : Option α) : Multiset α := ↑o.toList

@[simp] lemma optMS_none {α : Type} : optMS (none : Option α) = 0 := rfl

@[simp] lemma optMS_some {α : Type} (a : α) : optMS (some a) = {a} := rfl

lemma mem_optMS {α : Type} {a : α} {o : Option α} : a ∈ optMS o ↔ o = some a := by
  cases o with
  | none => simp
  | some b => simp [eq_comm]

/-! ## Touches -/

/-- One paired (pull, push) touch of a row: the pulled prior record with the row-local read
micro-time, and the pushed new/read-back record. -/
abbrev Touch (p : ℕ) : Type := (MemoryMsg (ZMod p) × ℕ) × MemoryMsg (ZMod p)

/-- The claimed prior records of a chain. -/
def chainPulls (c : List (Touch p)) : List (MemoryMsg (ZMod p)) := c.map fun pq => pq.1.1

/-- The pushed records of a chain. -/
def chainPushes (c : List (Touch p)) : List (MemoryMsg (ZMod p)) := c.map Prod.snd

lemma chainPulls_cons (pq : Touch p) (c : List (Touch p)) :
    chainPulls (pq :: c) = pq.1.1 :: chainPulls c := rfl

lemma chainPushes_cons (pq : Touch p) (c : List (Touch p)) :
    chainPushes (pq :: c) = pq.2 :: chainPushes c := rfl

lemma chainPulls_cons_coe (pq : Touch p) (c : List (Touch p)) :
    (↑(chainPulls (pq :: c)) : Multiset (MemoryMsg (ZMod p))) = pq.1.1 ::ₘ ↑(chainPulls c) := by
  simp [chainPulls, Multiset.cons_coe]

lemma chainPushes_cons_coe (pq : Touch p) (c : List (Touch p)) :
    (↑(chainPushes (pq :: c)) : Multiset (MemoryMsg (ZMod p))) = pq.2 ::ₘ ↑(chainPushes c) := by
  simp [chainPushes, Multiset.cons_coe]

lemma mem_chainPushes {c : List (Touch p)} {m : MemoryMsg (ZMod p)} :
    m ∈ chainPushes c ↔ ∃ pq ∈ c, (pq : Touch p).2 = m :=
  List.mem_map

/-- The in-circuit-style shape/ordering facts for one paired pull/push touch of a row whose
state-pull time is `t`: same location; the pulled prior strictly predates the push (SP1's
`prev_clk < access_clk`); the read happens in the location's pre-effect read window (`[t, t+3]` for
registers, exactly `t` for RAM); and the push is either a read-back — same value, pushed **at the
read micro-time** — or the write at `t + writeOffset` (`t + 4` register, `t + 1` RAM). No pre-row
bound on the pull and no chain-link facts: those are derived from balance (SP-6 D4/D5). -/
structure TouchOK (t : ℕ) (mp : MemoryMsg (ZMod p) × ℕ) (q : MemoryMsg (ZMod p)) : Prop where
  loc_eq : MemoryMsg.locOf q = MemoryMsg.locOf mp.1
  pull_lt_push : MemoryMsg.timeNat mp.1 < MemoryMsg.timeNat q
  read_lo : t ≤ mp.2
  read_hi : mp.2 ≤ t + readWindow (MemoryMsg.locOf mp.1)
  push_kind : (q.value = mp.1.value ∧ MemoryMsg.timeNat q = mp.2) ∨
    MemoryMsg.timeNat q = t + writeOffset (MemoryMsg.locOf q)

/-- All pushes land at/after the row window start. -/
lemma TouchOK.push_lo {t : ℕ} {mp : MemoryMsg (ZMod p) × ℕ} {q : MemoryMsg (ZMod p)}
    (h : TouchOK t mp q) : t ≤ MemoryMsg.timeNat q := by
  rcases h.push_kind with ⟨-, hq⟩ | hq
  · have := h.read_lo
    omega
  · omega

/-- All pushes land by the row's last effect slot. -/
lemma TouchOK.push_hi {t : ℕ} {mp : MemoryMsg (ZMod p) × ℕ} {q : MemoryMsg (ZMod p)}
    (h : TouchOK t mp q) : MemoryMsg.timeNat q ≤ t + 4 := by
  rcases h.push_kind with ⟨-, hq⟩ | hq
  · have h1 := h.read_hi
    have h2 := readWindow_le (MemoryMsg.locOf mp.1)
    omega
  · have := writeOffset_le (MemoryMsg.locOf q)
    omega

/-! ## Per-key touch chains of a row -/

/-- The row's same-key touches at `loc`, in slot order: the positional pull/push pairing filtered
at the key. -/
def rowTouchesAt (r : RowFacts p) (loc : MemLoc) : List (Touch p) :=
  (r.memPulls.zip r.memPushes).filter fun pq => MemoryMsg.locOf pq.2 = loc

lemma mem_rowTouchesAt {r : RowFacts p} {loc : MemLoc} {pq : Touch p} :
    pq ∈ rowTouchesAt r loc ↔
      pq ∈ r.memPulls.zip r.memPushes ∧ MemoryMsg.locOf pq.2 = loc := by
  simp [rowTouchesAt]

/-- The row's pulled prior messages at location `loc`. -/
def rowPullsAt (r : RowFacts p) (loc : MemLoc) : List (MemoryMsg (ZMod p)) :=
  (r.memPulls.map (·.1)).filter fun m => MemoryMsg.locOf m = loc

/-- The row's pushed messages at location `loc`. -/
def rowPushesAt (r : RowFacts p) (loc : MemLoc) : List (MemoryMsg (ZMod p)) :=
  r.memPushes.filter fun m => MemoryMsg.locOf m = loc

/-- **Chain discipline** for one row's same-key touches at window time `t` — the SP-6 production
`ChainOK`. All facts are per-slot in-circuit facts plus slot monotonicity of push times; per
deviations D4/D5 there is **no** link field and no pre-row head-pull bound. -/
structure ChainOK (loc : MemLoc) (t : ℕ) (c : List (Touch p)) : Prop where
  pull_loc : ∀ pq ∈ c, MemoryMsg.locOf (pq : Touch p).1.1 = loc
  push_loc : ∀ pq ∈ c, MemoryMsg.locOf (pq : Touch p).2 = loc
  slot : ∀ pq ∈ c, MemoryMsg.timeNat (pq : Touch p).1.1 < MemoryMsg.timeNat pq.2
  read_lo : ∀ pq ∈ c, t ≤ (pq : Touch p).1.2
  read_hi : ∀ pq ∈ c, (pq : Touch p).1.2 ≤ t + readWindow loc
  push_kind : ∀ pq ∈ c, ((pq : Touch p).2.value = pq.1.1.value ∧
      MemoryMsg.timeNat pq.2 = pq.1.2) ∨ MemoryMsg.timeNat pq.2 = t + writeOffset loc
  push_mono : List.IsChain
    (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2) c

lemma ChainOK.push_lo {loc : MemLoc} {t : ℕ} {c : List (Touch p)} (h : ChainOK loc t c) :
    ∀ pq ∈ c, t ≤ MemoryMsg.timeNat pq.2 := by
  intro pq hpq
  rcases h.push_kind pq hpq with ⟨-, ht⟩ | hw
  · have := h.read_lo pq hpq
    omega
  · omega

lemma ChainOK.push_hi {loc : MemLoc} {t : ℕ} {c : List (Touch p)} (h : ChainOK loc t c) :
    ∀ pq ∈ c, MemoryMsg.timeNat pq.2 ≤ t + 4 := by
  intro pq hpq
  rcases h.push_kind pq hpq with ⟨-, ht⟩ | hw
  · have h1 := h.read_hi pq hpq
    have h2 := readWindow_le loc
    omega
  · have := writeOffset_le loc
    omega

lemma ChainOK.tail {loc : MemLoc} {t : ℕ} {a : Touch p} {c : List (Touch p)}
    (h : ChainOK loc t (a :: c)) : ChainOK loc t c where
  pull_loc pq hpq := h.pull_loc pq (List.mem_cons_of_mem _ hpq)
  push_loc pq hpq := h.push_loc pq (List.mem_cons_of_mem _ hpq)
  slot pq hpq := h.slot pq (List.mem_cons_of_mem _ hpq)
  read_lo pq hpq := h.read_lo pq (List.mem_cons_of_mem _ hpq)
  read_hi pq hpq := h.read_hi pq (List.mem_cons_of_mem _ hpq)
  push_kind pq hpq := h.push_kind pq (List.mem_cons_of_mem _ hpq)
  push_mono := h.push_mono.tail

/-! ## Forall₂/zip/filter plumbing -/

/-- A positional pairing pairs every pull with some push. -/
lemma mem_zip_of_mem_left {t : ℕ} :
    ∀ {l₁ : List (MemoryMsg (ZMod p) × ℕ)} {l₂ : List (MemoryMsg (ZMod p))},
      List.Forall₂ (TouchOK t) l₁ l₂ →
      ∀ mp ∈ l₁, ∃ q, (mp, q) ∈ l₁.zip l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => intro mp hmp; cases hmp
  | @cons a b l₁' l₂' hR htail ih =>
    intro mp hmp
    rw [List.zip_cons_cons]
    rcases List.mem_cons.mp hmp with rfl | hmp'
    · exact ⟨b, List.mem_cons_self⟩
    · obtain ⟨q, hq⟩ := ih mp hmp'
      exact ⟨q, List.mem_cons_of_mem _ hq⟩

private lemma filter_zip_map_snd {t : ℕ} :
    ∀ {l₁ : List (MemoryMsg (ZMod p) × ℕ)} {l₂ : List (MemoryMsg (ZMod p))},
      List.Forall₂ (TouchOK t) l₁ l₂ → ∀ loc : MemLoc,
        chainPushes ((l₁.zip l₂).filter fun pq => MemoryMsg.locOf pq.2 = loc)
          = l₂.filter fun q => MemoryMsg.locOf q = loc := by
  intro l₁ l₂ h loc
  induction h with
  | nil => rfl
  | @cons mp q l₁' l₂' hR htail ih =>
    rw [List.zip_cons_cons]
    by_cases hq : MemoryMsg.locOf q = loc
    · rw [List.filter_cons_of_pos (by simpa using hq), List.filter_cons_of_pos (by simpa using hq),
        chainPushes_cons, ih]
    · rw [List.filter_cons_of_neg (by simpa using hq), List.filter_cons_of_neg (by simpa using hq)]
      exact ih

private lemma filter_zip_map_fst {t : ℕ} :
    ∀ {l₁ : List (MemoryMsg (ZMod p) × ℕ)} {l₂ : List (MemoryMsg (ZMod p))},
      List.Forall₂ (TouchOK t) l₁ l₂ → ∀ loc : MemLoc,
        chainPulls ((l₁.zip l₂).filter fun pq => MemoryMsg.locOf pq.2 = loc)
          = (l₁.map (·.1)).filter fun m => MemoryMsg.locOf m = loc := by
  intro l₁ l₂ h loc
  induction h with
  | nil => rfl
  | @cons mp q l₁' l₂' hR htail ih =>
    rw [List.zip_cons_cons, List.map_cons]
    by_cases hq : MemoryMsg.locOf q = loc
    · have hmp : MemoryMsg.locOf mp.1 = loc := hR.loc_eq ▸ hq
      rw [List.filter_cons_of_pos (by simpa using hq), List.filter_cons_of_pos (by simpa using hmp),
        chainPulls_cons, ih]
    · have hmp : ¬MemoryMsg.locOf mp.1 = loc := fun hc => hq (hR.loc_eq.trans hc)
      rw [List.filter_cons_of_neg (by simpa using hq), List.filter_cons_of_neg (by simpa using hmp)]
      exact ih

/-- Under the positional pairing, the per-key push filter is the chain's push list. -/
lemma rowPushesAt_eq {t : ℕ} {r : RowFacts p}
    (h : List.Forall₂ (TouchOK t) r.memPulls r.memPushes) (loc : MemLoc) :
    rowPushesAt r loc = chainPushes (rowTouchesAt r loc) :=
  (filter_zip_map_snd h loc).symm

/-- Under the positional pairing, the per-key pull filter is the chain's pull list. -/
lemma rowPullsAt_eq {t : ℕ} {r : RowFacts p}
    (h : List.Forall₂ (TouchOK t) r.memPulls r.memPushes) (loc : MemLoc) :
    rowPullsAt r loc = chainPulls (rowTouchesAt r loc) :=
  (filter_zip_map_fst h loc).symm

/-! ## The chain-shift identity -/

/-- **The chain-shift identity**: for a linked chain, the head pull plus all pushes equals the
last push plus all pulls, as multisets — each interior push cancels against the next pull. This is
the algebraic heart of the intra-row generalization: it lets the walk cancel a whole chain from the
per-key balance in one move. -/
lemma chain_shift :
    ∀ (c : List (Touch p)) (hc : c ≠ []),
      List.IsChain (fun a b : Touch p => b.1.1 = a.2) c →
      (c.head hc).1.1 ::ₘ (↑(chainPushes c) : Multiset (MemoryMsg (ZMod p)))
        = (c.getLast hc).2 ::ₘ ↑(chainPulls c)
  | [], hc, _ => absurd rfl hc
  | [pq], _, _ => by
      simp only [chainPushes, chainPulls, List.map_cons, List.map_nil, List.head_cons,
        List.getLast_singleton]
      rw [Multiset.cons_coe, Multiset.cons_coe]
      exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)
  | pq :: b :: rest, _, hlink => by
      obtain ⟨hpb, htail⟩ := List.isChain_cons_cons.mp hlink
      have ih := chain_shift (b :: rest) (List.cons_ne_nil _ _) htail
      simp only [List.head_cons] at ih ⊢
      rw [List.getLast_cons (List.cons_ne_nil b rest)]
      rw [chainPushes_cons_coe, chainPulls_cons_coe, ← hpb, ih]
      exact Multiset.cons_swap _ _ _

/-! ## Deriving the chain links from balance (the D4 resolution)

Per-slot in-circuit facts only — no link assumptions. Each slot's pull is strictly earlier than its
own push (`prev_clk < clk`), hence than every own push from that slot on (slot monotonicity), and
`≤ t + 4 < t + 8 ≤` every other row's push — so in the balance it can only match the running front.
Popping the matched slot re-founds the balance with that slot's push as the new front, and the
induction walks the whole slot list. -/

/-- Slot monotonicity propagates: the head's push is strictly earlier than every later push. -/
private lemma head_lt_of_mono :
    ∀ (rest : List (Touch p)) (pq : Touch p),
      List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        (pq :: rest) →
      ∀ pq' ∈ rest, MemoryMsg.timeNat pq.2 < MemoryMsg.timeNat pq'.2
  | [], _, _ => by simp
  | b :: rest', pq, h => by
      obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp h
      intro pq' hpq'
      rcases List.mem_cons.mp hpq' with rfl | hpq'
      · exact hab
      · exact lt_trans hab (head_lt_of_mono rest' b htail pq' hpq')

/-- The head pull can match no push: not an own push (strictly later, by `prev_clk < clk` + slot
monotonicity), not another row's push (`≤ t + 4 < t + 8`). -/
private lemma headPull_not_matched {t : ℕ} {pq : Touch p} {rest : List (Touch p)}
    {P : Multiset (MemoryMsg (ZMod p))}
    (hslot : ∀ x ∈ pq :: rest, MemoryMsg.timeNat x.1.1 < MemoryMsg.timeNat x.2)
    (hhi : ∀ x ∈ pq :: rest, MemoryMsg.timeNat x.2 ≤ t + 4)
    (hmono : List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (pq :: rest))
    (hP : ∀ m ∈ P, t + 8 ≤ MemoryMsg.timeNat m) :
    pq.1.1 ∉ (↑(chainPushes (pq :: rest)) : Multiset (MemoryMsg (ZMod p))) + P := by
  intro hmem
  have hs := hslot pq List.mem_cons_self
  rcases Multiset.mem_add.mp hmem with h | h
  · obtain ⟨pq', hpq', heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
    rcases List.mem_cons.mp hpq' with rfl | hpq'
    · rw [heq] at hs
      omega
    · have hlt := head_lt_of_mono rest pq hmono pq' hpq'
      rw [heq] at hlt
      omega
  · have h8 := hP _ h
    have h4 := hhi pq List.mem_cons_self
    omega

/-- **Head-pull forcing from per-slot facts alone** (concrete running front). -/
private lemma headPull_forced {t : ℕ} {front : MemoryMsg (ZMod p)} {pq : Touch p}
    {rest : List (Touch p)} {P R : Multiset (MemoryMsg (ZMod p))}
    (hslot : ∀ x ∈ pq :: rest, MemoryMsg.timeNat x.1.1 < MemoryMsg.timeNat x.2)
    (hhi : ∀ x ∈ pq :: rest, MemoryMsg.timeNat x.2 ≤ t + 4)
    (hmono : List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (pq :: rest))
    (hP : ∀ m ∈ P, t + 8 ≤ MemoryMsg.timeNat m)
    (hbal : front ::ₘ ((↑(chainPushes (pq :: rest)) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls (pq :: rest)) + R) :
    pq.1.1 = front := by
  have hmem : pq.1.1
      ∈ front ::ₘ ((↑(chainPushes (pq :: rest)) : Multiset (MemoryMsg (ZMod p))) + P) := by
    rw [hbal]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr
      (List.mem_map_of_mem List.mem_cons_self)))
  rcases Multiset.mem_cons.mp hmem with h | h
  · exact h
  · exact absurd h (headPull_not_matched hslot hhi hmono hP)

/-- Popping one matched slot from the balance: the forced head pull cancels against the front,
leaving the slot's own push as the new front. -/
private lemma balance_pop {front : MemoryMsg (ZMod p)} {pq : Touch p} {rest : List (Touch p)}
    {P R : Multiset (MemoryMsg (ZMod p))} (hhead : pq.1.1 = front)
    (hbal : front ::ₘ ((↑(chainPushes (pq :: rest)) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls (pq :: rest)) + R) :
    pq.2 ::ₘ ((↑(chainPushes rest) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls rest) + R := by
  rw [chainPushes_cons_coe, chainPulls_cons_coe, Multiset.cons_add, Multiset.cons_add,
    hhead] at hbal
  exact (Multiset.cons_inj_right front).mp hbal

/-- The slot-walking induction: from per-slot facts and the balance with running front `front`,
the head pull equals `front` and all intra-row links hold. -/
private lemma chainLinks_aux {t : ℕ} :
    ∀ (own : List (Touch p)) (front : MemoryMsg (ZMod p)) (P R : Multiset (MemoryMsg (ZMod p))),
      (∀ x ∈ own, MemoryMsg.timeNat x.1.1 < MemoryMsg.timeNat x.2) →
      (∀ x ∈ own, MemoryMsg.timeNat x.2 ≤ t + 4) →
      List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2) own →
      (∀ m ∈ P, t + 8 ≤ MemoryMsg.timeNat m) →
      front ::ₘ ((↑(chainPushes own) : Multiset (MemoryMsg (ZMod p))) + P)
        = ↑(chainPulls own) + R →
      (∀ h : own ≠ [], (own.head h).1.1 = front) ∧
        List.IsChain (fun a b : Touch p => b.1.1 = a.2) own
  | [], _, _, _, _, _, _, _, _ => ⟨fun h => absurd rfl h, List.isChain_nil⟩
  | [pq], _, P, R, hslot, hhi, hmono, hP, hbal =>
      ⟨fun _ => headPull_forced hslot hhi hmono hP hbal, List.isChain_singleton _⟩
  | pq :: b :: rest', _, P, R, hslot, hhi, hmono, hP, hbal => by
      have hhead := headPull_forced hslot hhi hmono hP hbal
      have hbal' := balance_pop hhead hbal
      obtain ⟨ih_head, ih_link⟩ := chainLinks_aux (b :: rest') pq.2 P R
        (fun x hx => hslot x (List.mem_cons_of_mem _ hx))
        (fun x hx => hhi x (List.mem_cons_of_mem _ hx))
        (List.isChain_cons_cons.mp hmono).2 hP hbal'
      exact ⟨fun _ => hhead,
        List.isChain_cons_cons.mpr ⟨ih_head (List.cons_ne_nil _ _), ih_link⟩⟩

/-- **The D4 resolution: chain links are derivable from balance.** Given only the per-slot
in-circuit facts of `ChainOK` plus the `t + 8` gap on other rows' pushes, the balance forces the
partial frontier to hold exactly the chain's head pull and every later pull to equal the row's own
previous push — no circuit-certified link facts. -/
theorem chainLinks_of_balance {loc : MemLoc} {t : ℕ} {live : Option (MemoryMsg (ZMod p))}
    {own : List (Touch p)} (hne : own ≠ []) (hok : ChainOK loc t own)
    {P R : Multiset (MemoryMsg (ZMod p))} (hP : ∀ m ∈ P, t + 8 ≤ MemoryMsg.timeNat m)
    (hbal : optMS live + ((↑(chainPushes own) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls own) + R) :
    live = some (own.head hne).1.1 ∧
      List.IsChain (fun a b : Touch p => b.1.1 = a.2) own := by
  match own, hne with
  | pq :: rest, _ =>
    have hslot : ∀ x ∈ pq :: rest, MemoryMsg.timeNat x.1.1 < MemoryMsg.timeNat x.2 := hok.slot
    have hhi : ∀ x ∈ pq :: rest, MemoryMsg.timeNat x.2 ≤ t + 4 := hok.push_hi
    have hmem : pq.1.1
        ∈ optMS live + ((↑(chainPushes (pq :: rest)) : Multiset (MemoryMsg (ZMod p))) + P) := by
      rw [hbal]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr
        (List.mem_map_of_mem List.mem_cons_self)))
    have hlive : live = some pq.1.1 := by
      rcases Multiset.mem_add.mp hmem with h | h
      · exact mem_optMS.mp h
      · exact absurd h (headPull_not_matched hslot hhi hok.push_mono hP)
    have hbal' : pq.1.1 ::ₘ ((↑(chainPushes (pq :: rest)) : Multiset (MemoryMsg (ZMod p))) + P)
        = ↑(chainPulls (pq :: rest)) + R := by
      rw [hlive, optMS_some, Multiset.singleton_add] at hbal
      exact hbal
    obtain ⟨-, hlink⟩ := chainLinks_aux (pq :: rest) pq.1.1 P R hslot hhi hok.push_mono hP hbal'
    exact ⟨hlive, hlink⟩

/-! ## The per-key chain forcing step -/

/-- **Chain cancellation**: with the links established and the head pull identified with the
front, the whole chain cancels from the per-key balance via `chain_shift`, re-founding it with the
chain's last push as the new frontier. -/
theorem chainForcing_step {t : ℕ} {live : MemoryMsg (ZMod p)} {own : List (Touch p)}
    (hne : own ≠ [])
    (hlink : List.IsChain (fun a b : Touch p => b.1.1 = a.2) own)
    (hhead : (own.head hne).1.1 = live)
    (hhi : ∀ x ∈ own, MemoryMsg.timeNat x.2 ≤ t + 4)
    {P R : Multiset (MemoryMsg (ZMod p))}
    (hbal : live ::ₘ ((↑(chainPushes own) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls own) + R) :
    ((own.getLast hne).2 ::ₘ P = R) ∧ MemoryMsg.timeNat (own.getLast hne).2 ≤ t + 4 := by
  have hshift := chain_shift own hne hlink
  rw [hhead] at hshift
  have hstep : (own.getLast hne).2 ::ₘ ((↑(chainPulls own) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls own) + R := by
    rw [← Multiset.cons_add, ← hshift, Multiset.cons_add]
    exact hbal
  have h2 : (↑(chainPulls own) : Multiset (MemoryMsg (ZMod p))) + ((own.getLast hne).2 ::ₘ P)
      = ↑(chainPulls own) + R := by
    rw [Multiset.add_cons]
    exact hstep
  exact ⟨add_left_cancel h2, hhi _ (List.getLast_mem hne)⟩

/-- **The walk's per-key induction step** (the design-literal composite consuming the `t + 8`
gap): from `ChainOK` and the per-key balance against the partial frontier, the frontier holds
exactly the head pull, the intra-row links hold, the chain cancels leaving the last push as the new
frontier, and the new frontier's time re-establishes the `LiveOK` bound (`≤ t + 4 < t + 8`). -/
theorem chainForcing_step_of_gap {loc : MemLoc} {t : ℕ} {live : Option (MemoryMsg (ZMod p))}
    {own : List (Touch p)} (hne : own ≠ []) (hok : ChainOK loc t own)
    {P R : Multiset (MemoryMsg (ZMod p))} (hP : ∀ m ∈ P, t + 8 ≤ MemoryMsg.timeNat m)
    (hbal : optMS live + ((↑(chainPushes own) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls own) + R) :
    live = some (own.head hne).1.1 ∧
      List.IsChain (fun a b : Touch p => b.1.1 = a.2) own ∧
      ((own.getLast hne).2 ::ₘ P = R) ∧
      MemoryMsg.timeNat (own.getLast hne).2 ≤ t + 4 := by
  obtain ⟨hlive, hlink⟩ := chainLinks_of_balance hne hok hP hbal
  have hbal' : (own.head hne).1.1 ::ₘ ((↑(chainPushes own) : Multiset (MemoryMsg (ZMod p))) + P)
      = ↑(chainPulls own) + R := by
    rw [hlive, optMS_some, Multiset.singleton_add] at hbal
    exact hbal
  obtain ⟨hcancel, hlast⟩ := chainForcing_step hne hlink rfl hok.push_hi hbal'
  exact ⟨hlive, hlink, hcancel, hlast⟩

/-! ## The value layer

The spike validated the balance algebra; this is the production value layer it flagged. The
schedule numbers make a same-key slot after a write impossible: a register write lands at the
window's last effect slot (`t + 4`, above every admissible later push time), and a RAM write at
`t + 1` beats any later same-key push, whose read-back time would have to be the pinned `t`. So
every non-last slot is a read-back, and pull/push values propagate the frontier value. -/

/-- A slot followed by another same-key slot is a read-back. -/
private lemma readback_of_succ {loc : MemLoc} {t : ℕ} {a b : Touch p} {rest : List (Touch p)}
    (hok : ChainOK loc t (a :: b :: rest)) : a.2.value = a.1.1.value := by
  rcases hok.push_kind a List.mem_cons_self with ⟨hv, -⟩ | hw
  · exact hv
  · exfalso
    have hmono : MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2 :=
      (List.isChain_cons_cons.mp hok.push_mono).1
    have hb_mem : b ∈ a :: b :: rest := List.mem_cons_of_mem _ List.mem_cons_self
    have hbhi := hok.read_hi b hb_mem
    rcases hok.push_kind b hb_mem with ⟨-, hbt⟩ | hbw
    · cases loc with
      | reg i =>
        rw [writeOffset_reg] at hw
        rw [readWindow_reg] at hbhi
        omega
      | ram addr =>
        rw [writeOffset_ram] at hw
        rw [readWindow_ram] at hbhi
        omega
    · cases loc with
      | reg i =>
        rw [writeOffset_reg] at hw hbw
        omega
      | ram addr =>
        rw [writeOffset_ram] at hw hbw
        omega

/-- **Chain pull currency**: every pull in a linked chain carries the head pull's value — later
pulls re-claim read-backs only, since nothing can follow a write. -/
lemma chain_pull_values {loc : MemLoc} {t : ℕ} :
    ∀ (c : List (Touch p)), ChainOK loc t c →
      List.IsChain (fun a b : Touch p => b.1.1 = a.2) c →
      ∀ (hc : c ≠ []), ∀ pq ∈ c, pq.1.1.value = (c.head hc).1.1.value
  | [], _, _, hc => absurd rfl hc
  | [a], _, _, _ => by
      intro pq hpq
      rcases List.mem_singleton.mp hpq with rfl
      rfl
  | a :: b :: rest, hok, hlink, _ => by
      intro pq hpq
      rcases List.mem_cons.mp hpq with rfl | hpq'
      · rfl
      · have ih := chain_pull_values (b :: rest) hok.tail
          (List.isChain_cons_cons.mp hlink).2 (List.cons_ne_nil _ _) pq hpq'
        rw [List.head_cons] at ih
        rw [ih, (List.isChain_cons_cons.mp hlink).1, readback_of_succ hok, List.head_cons]

/-- **Chain push values**: when the last slot is a read-back, the whole chain is read-backs, so
every push carries the head pull's value — the input to the row's `FrameFact` at this key. -/
lemma chain_push_values {loc : MemLoc} {t : ℕ} :
    ∀ (c : List (Touch p)), ChainOK loc t c →
      List.IsChain (fun a b : Touch p => b.1.1 = a.2) c →
      ∀ (hc : c ≠ []), (c.getLast hc).2.value = (c.getLast hc).1.1.value →
      ∀ pq ∈ c, pq.2.value = (c.head hc).1.1.value
  | [], _, _, hc, _ => absurd rfl hc
  | [a], _, _, _, hlast => by
      intro pq hpq
      rcases List.mem_singleton.mp hpq with rfl
      simpa using hlast
  | a :: b :: rest, hok, hlink, _, hlast => by
      have hlast' := hlast
      rw [List.getLast_cons (List.cons_ne_nil b rest)] at hlast'
      intro pq hpq
      rcases List.mem_cons.mp hpq with rfl | hpq'
      · rw [List.head_cons]
        exact readback_of_succ hok
      · have ih := chain_push_values (b :: rest) hok.tail
          (List.isChain_cons_cons.mp hlink).2 (List.cons_ne_nil _ _) hlast' pq hpq'
        rw [List.head_cons] at ih
        rw [ih, (List.isChain_cons_cons.mp hlink).1, readback_of_succ hok, List.head_cons]

/-- **Pull routing**: every pull of a linked chain is the head pull or one of the row's own
pushes — the case split that routes `LocalMemTruth` from the frontier or the row's own step fact. -/
lemma chain_pull_head_or_push :
    ∀ (c : List (Touch p)) (hc : c ≠ []),
      List.IsChain (fun a b : Touch p => b.1.1 = a.2) c →
      ∀ pq ∈ c, pq.1.1 = (c.head hc).1.1 ∨ pq.1.1 ∈ chainPushes c
  | [], hc, _ => absurd rfl hc
  | [a], _, _ => by
      intro pq hpq
      rcases List.mem_singleton.mp hpq with rfl
      exact Or.inl rfl
  | a :: b :: rest, _, hlink => by
      intro pq hpq
      rcases List.mem_cons.mp hpq with rfl | hpq'
      · exact Or.inl rfl
      · rcases chain_pull_head_or_push (b :: rest) (List.cons_ne_nil _ _)
          (List.isChain_cons_cons.mp hlink).2 pq hpq' with h | h
        · right
          rw [List.head_cons] at h
          rw [chainPushes_cons, h, (List.isChain_cons_cons.mp hlink).1]
          exact List.mem_cons_self
        · right
          rw [chainPushes_cons]
          exact List.mem_cons_of_mem _ h

/-! ## The state-bus uniqueness of the minimal row -/

private lemma coe_map_pop {α β : Type} (f : α → β) (l1 l2 : List α) (r : α) :
    (↑((l1 ++ r :: l2).map f) : Multiset β) = f r ::ₘ ↑((l1 ++ l2).map f) :=
  Multiset.coe_eq_coe.mpr (List.perm_middle.map f)

/-- Re-insert the popped row into a batch membership. -/
lemma mem_middle {α : Type} {l1 l2 : List α} (r₀ : α) {r : α} (h : r ∈ l1 ++ l2) :
    r ∈ l1 ++ r₀ :: l2 := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- **State-balance uniqueness of the minimal row** (proved, not assumed — SP-6 invariant 2). With
the `+8` clock discipline and all pull times `≥ t`, once the popped row pulls the head record at
time `t`, every *other* row's state-pull time is strictly greater than `t`: a second pull at time
`t` could match no push (times `≥ t + 8`), so it would equal `head` — but then the pulls contain
two copies of `head`, and after cancelling the left `head` some push must equal `head`, impossible
by time. -/
theorem stateBalance_unique_minimal {t : ℕ} {head fin : StateMsg (ZMod p)}
    {l1 l2 : List (RowFacts p)} {r₀ : RowFacts p}
    (htime8 : ∀ r ∈ l1 ++ r₀ :: l2,
      StateMsg.timeNat r.statePush = StateMsg.timeNat r.statePull + 8)
    (hmin : ∀ r ∈ l1 ++ r₀ :: l2, t ≤ StateMsg.timeNat r.statePull)
    (hhead_t : StateMsg.timeNat head = t)
    (hr₀ : r₀.statePull = head)
    (hbal : head ::ₘ (↑((l1 ++ r₀ :: l2).map (·.statePush)) : Multiset (StateMsg (ZMod p)))
      = fin ::ₘ ↑((l1 ++ r₀ :: l2).map (·.statePull))) :
    ∀ r' ∈ l1 ++ l2, t < StateMsg.timeNat r'.statePull := by
  intro r' hr'
  by_contra hle
  have hr'_full : r' ∈ l1 ++ r₀ :: l2 := mem_middle r₀ hr'
  have ht' : StateMsg.timeNat r'.statePull = t :=
    le_antisymm (Nat.not_lt.mp hle) (hmin r' hr'_full)
  -- Step 1: the second pull at time `t` can only match `head` in the balance.
  have hmem : r'.statePull
      ∈ head ::ₘ (↑((l1 ++ r₀ :: l2).map (·.statePush)) : Multiset (StateMsg (ZMod p))) := by
    rw [hbal]
    exact Multiset.mem_cons_of_mem (Multiset.mem_coe.mpr (List.mem_map_of_mem hr'_full))
  have hr'_head : r'.statePull = head := by
    rcases Multiset.mem_cons.mp hmem with h | h
    · exact h
    · exfalso
      obtain ⟨r'', hr''_mem, heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
      have h8 := htime8 r'' hr''_mem
      have hm := hmin r'' hr''_mem
      rw [heq] at h8
      omega
  -- Step 2: two copies of `head` among the pulls sink the balance — cancelling the left `head`
  -- forces some push to equal `head`, impossible by the `+8` time discipline.
  have hpop : (↑((l1 ++ r₀ :: l2).map (·.statePull)) : Multiset (StateMsg (ZMod p)))
      = r₀.statePull ::ₘ ↑((l1 ++ l2).map (·.statePull)) := coe_map_pop _ l1 l2 r₀
  have hmem2 : head ∈ (↑((l1 ++ l2).map (·.statePull)) : Multiset (StateMsg (ZMod p))) := by
    rw [← hr'_head]
    exact Multiset.mem_coe.mpr (List.mem_map_of_mem hr')
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hmem2
  rw [hpop, hr₀, hrest, Multiset.cons_swap fin head] at hbal
  have hpushes := (Multiset.cons_inj_right head).mp hbal
  have hhead_push : head
      ∈ (↑((l1 ++ r₀ :: l2).map (·.statePush)) : Multiset (StateMsg (ZMod p))) := by
    rw [hpushes]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  obtain ⟨r'', hr''_mem, heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hhead_push)
  have h8 := htime8 r'' hr''_mem
  have hm := hmin r'' hr''_mem
  rw [heq] at h8
  omega

/-- **Composition with mod-8 window alignment** (SP-6 invariant 1): the balance-forced `> t` of
`stateBalance_unique_minimal` lifts to `≥ t + 8` for every remaining row, which (with each row's
own `push_lo`) supplies the other-rows' push gap consumed by `chainForcing_step_of_gap` and keeps
every remaining push out of the popped row's window `[t, t + 4] ⊂ [t, t + 8)`. -/
theorem stateBalance_remaining_ge_eight {t : ℕ} {head fin : StateMsg (ZMod p)}
    {l1 l2 : List (RowFacts p)} {r₀ : RowFacts p}
    (htime8 : ∀ r ∈ l1 ++ r₀ :: l2,
      StateMsg.timeNat r.statePush = StateMsg.timeNat r.statePull + 8)
    (hmin : ∀ r ∈ l1 ++ r₀ :: l2, t ≤ StateMsg.timeNat r.statePull)
    (halign : ∀ r ∈ l1 ++ r₀ :: l2, StateMsg.timeNat r.statePull % 8 = t % 8)
    (hhead_t : StateMsg.timeNat head = t)
    (hr₀ : r₀.statePull = head)
    (hbal : head ::ₘ (↑((l1 ++ r₀ :: l2).map (·.statePush)) : Multiset (StateMsg (ZMod p)))
      = fin ::ₘ ↑((l1 ++ r₀ :: l2).map (·.statePull))) :
    ∀ r' ∈ l1 ++ l2, t + 8 ≤ StateMsg.timeNat r'.statePull := by
  intro r' hr'
  have h1 := stateBalance_unique_minimal htime8 hmin hhead_t hr₀ hbal r' hr'
  have h2 := halign r' (mem_middle r₀ hr')
  omega

end SP1Clean.Soundness.TimedGrounding
