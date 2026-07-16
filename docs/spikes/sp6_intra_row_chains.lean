import Mathlib

/-!
# SP-6 de-risk spike: intra-row same-key touch chains for `TimedGrounding.walk`

**Isolated spike.** Imports Mathlib only; touches nothing under `SP1Clean/`. It proves the
abstract multiset core of the planned generalization of
`SP1Clean/Soundness/TimedGrounding.lean`'s `walk` from `RowOK.locs_nodup` (each row touches each
memory key at most once) to **ordered intra-row chains**: within one row at window time `t`, the
same-key touches `[(p₁,q₁),…,(pₙ,qₙ)]` satisfy `p₁.time < t` (the pre-row claim), `pⱼ₊₁ = qⱼ`
(each later pull re-claims the row's own previous push), and push times strictly increasing in
`[t, t+4]`. This admits register-alias rows (`add x1, x1, x2`; `bne x1, x1`).

Main theorems (abstract `Msg` over arbitrary key/value types, ℕ times; no SP1 imports):

* `chainForcing_step` — one induction step of the per-key forcing: given the whole-batch balance
  `live ::ₘ (chain pushes + other pushes) = finM ::ₘ (chain pulls + other pulls)` at one key,
  chain discipline for the minimal row, and every *other* push at time `≥ t`, the chain's head
  pull is forced to equal the frontier `live`, the whole chain cancels (via the `chain_shift`
  identity `p₁ ::ₘ pushes = qₙ ::ₘ pulls`), the balance re-establishes with the chain's **last
  push** `qₙ` as the new frontier (`qₙ ::ₘ P = finM ::ₘ Q`), and `qₙ.time ≤ t + 4`. The
  other-rows' pull multiset `Q` is *unconstrained* — deliberately: a later row's chain-head pull
  may legitimately claim this row's last push; the honest statement forces ONLY the minimal
  row's head pull.
* `stateBalance_unique_minimal` — the state-bus uniqueness fact (proved, not assumed): with the
  `+8` clock discipline (`push.time = pull.time + 8`), all pull times `≥ t`, and `head.time = t`,
  once one row `r₀` pulls `head`, *every other* row's state-pull time is `> t`. (Two pulls at
  time `t` both force to `head`; two copies of `head` among the pulls force some push to equal
  `head`, impossible since push times are `≥ t + 8`.)
* `stateBalance_remaining_ge_eight` — the composition: adding mod-8 window alignment
  (invariant 1) turns `> t` into `≥ t + 8` for every remaining row.
* `chainForcing_step_of_gap` — the design-literal wrapper consuming the `t + 8` gap that
  `stateBalance_remaining_ge_eight` supplies.
* `chainLinks_of_balance` — the D4 resolution: the chain-link equalities `pⱼ₊₁ = qⱼ` and the
  head-pull identification `p₁ = live` are *derived* from the balance given only per-slot
  in-circuit facts — `pullⱼ.time < pushⱼ.time` (SP1's `prev_clk < clk`), push times `≤ t + 4`
  and slot-strictly increasing, and the `t + 8` gap on other rows' pushes. `TouchOK`/extraction
  never needs to certify intra-row links.

## The three new invariants, as validated

1. **Mod-8 window alignment** (`RowOK` gains `pull.time ≡ c0 [MOD 8]`): consumed in
   `stateBalance_remaining_ge_eight` to lift the balance-forced `> t` to `≥ t + 8`.
2. **Unique minimal row**: NOT assumed — derived from the state balance
   (`stateBalance_unique_minimal`), exactly as the design hoped, including the subtle case where
   a second row's pull literally *equals* `head` (killed via the double-copy push argument).
3. **Frontier-time bound** (`LiveOK` gains `live.time ≤ t`): its *re-establishment* is proved —
   the new frontier `qₙ` has `qₙ.time ≤ t + 4 < t + 8 ≤` every remaining row's time.

## DESIGN DEVIATIONS discovered (the point of the spike)

* **(D1) The per-key forcing needs only `t ≤` other pushes, not `t + 8 ≤`.** Minimality alone
  (every other row's time `≥ t`, hence its pushes `≥ t`) already forces the head pull
  (`p₁.time < t` beats every push). The full `t + 8` gap from invariants 1+2 is therefore NOT
  load-bearing in the per-key multiset algebra; `chainForcing_step` states the weaker `t ≤`
  hypothesis and `chainForcing_step_of_gap` recovers the design-literal form. The gap IS still
  needed: (a) on the state bus, to pop rows in strict window order, and (b) in the semantic
  value layer (`localValueAt_shift` currency), where the new frontier's time must not overrun
  the next head time (`t + 4 < t + 8 ≤ t'` — this is where invariant 3 re-establishes).
* **(D2) Invariant 3's bound `live.time ≤ t` is not consumed by the balance layer at all.**
  The forcing instead *yields* the sharper `live.time < t` as a conclusion (from `p₁ = live` and
  `p₁.time < t`). Its consumption site remains the production value layer. It is kept as an
  (unused) `_hlive` hypothesis only in the design-literal wrapper.
* **(D3) Strict monotonicity of chain push times (`push_mono`) is not needed for the balance
  algebra** — the chain-link equalities `pⱼ₊₁ = qⱼ` cancel the tail pulls against the interior
  pushes purely algebraically (`chain_shift`). It is carried in `ChainOK` because the production
  value layer (read-back currency ordering within the window) will need it.
* **(D4) RESOLVED — the links ARE derivable from balance** (`chainLinks_of_balance`): if the
  circuit certifies only per-slot time bounds — not literal pull-equals-previous-push
  equalities — the engine can still *derive* `pⱼ₊₁ = qⱼ` and `p₁ = live`. Slot `j`'s pull is
  strictly earlier than its own push, hence than every own push from slot `j` on (slot
  monotonicity), and `≤ t + 4 < t + 8 ≤` every other row's push — so its only possible LHS
  match is the running front (`live` for slot 1, then the previous slot's push), and the
  balance pops one matched slot per induction step (`chainLinks_aux`). This is the one place
  where the window-exclusivity gap of invariants 1+2 is genuinely load-bearing, exactly as
  predicted. `TouchOK` does NOT need to certify links; extraction supplies per-slot bounds.
* **(D5) The link derivation needs no frontier-time hypothesis at all** — neither
  `live.time ≤ t` nor `< t`: pure membership forcing suffices, with no double-copy argument
  (unlike the state bus, the slot discipline makes every competing LHS message strictly later
  than the pull being forced). Unused likewise: the key facts and the `t ≤ push` lower bounds;
  load-bearing are only `pull < push`, `push ≤ t + 4`, slot monotonicity, and the gap (any
  `t + 5 ≤` bound works; production supplies `t + 8`). `ChainOK.head_lt` (`p₁.time < t`) is
  then *derived* from `p₁ = live` plus the walk's frontier bound (the previous step re-founds
  `live.time ≤ t_prev + 4 < t_prev + 8 ≤ t`; genesis: `≤ initial clock < t`), refining D2.
-/

namespace SP6

/-- An abstract bus message: a key, a ℕ time, a value (mirrors the `MemoryMsg`/`StateMsg`
shapes of `TimedGrounding.lean`). -/
structure Msg (K V : Type) where
  key : K
  time : ℕ
  val : V

/-- One paired (pull, push) touch. Also reused as a state-row `(statePull, statePush)` pair in
the state-bus lemmas. -/
abbrev Touch (K V : Type) := Msg K V × Msg K V

variable {K V : Type}

/-- The claimed previous records of a chain (analog of `rowPullsAt`). -/
def pulls (c : List (Touch K V)) : List (Msg K V) := c.map Prod.fst

/-- The new records of a chain (analog of `rowPushesAt`). -/
def pushes (c : List (Touch K V)) : List (Msg K V) := c.map Prod.snd

/-! ## Generic list/multiset helpers (idioms copied from `TimedGrounding.lean`) -/

lemma coe_map_pop {α β : Type} (f : α → β) (l1 l2 : List α) (r : α) :
    (↑((l1 ++ r :: l2).map f) : Multiset β) = f r ::ₘ ↑((l1 ++ l2).map f) :=
  Multiset.coe_eq_coe.mpr (List.perm_middle.map f)

lemma mem_middle {α : Type} {l1 l2 : List α} (r₀ : α) {r : α} (h : r ∈ l1 ++ l2) :
    r ∈ l1 ++ r₀ :: l2 := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-! ## Chain discipline -/

/-- **Chain discipline** for one row's same-key touches at window time `t` — the planned
generalization of `TouchOK` + `RowOK.locs_nodup`. The first pull claims a strictly pre-row
record; each later pull re-claims the row's own previous push; pushes live in `[t, t+4]` with
strictly increasing times (per-slot offsets); everything sits at the fixed key `k`. -/
structure ChainOK (k : K) (t : ℕ) (c : List (Touch K V)) : Prop where
  pull_key : ∀ pq ∈ c, (Prod.fst pq).key = k
  push_key : ∀ pq ∈ c, (Prod.snd pq).key = k
  head_lt : ∀ h : c ≠ [], (c.head h).1.time < t
  link : List.IsChain (fun pq pq' => pq'.1 = pq.2) c
  push_lo : ∀ pq ∈ c, t ≤ (Prod.snd pq).time
  push_hi : ∀ pq ∈ c, (Prod.snd pq).time ≤ t + 4
  push_mono : List.IsChain (fun pq pq' => (Prod.snd pq).time < (Prod.snd pq').time) c

/-- **The chain-shift identity**: for a linked chain, the head pull plus all pushes equals the
last push plus all pulls, as multisets — each interior push `qⱼ` cancels against the next pull
`pⱼ₊₁ = qⱼ`. This is the algebraic heart of the intra-row generalization: it lets the walk
cancel a whole chain from the per-key balance in one move. -/
lemma chain_shift :
    ∀ (c : List (Touch K V)) (hc : c ≠ []),
      List.IsChain (fun pq pq' => pq'.1 = pq.2) c →
      (c.head hc).1 ::ₘ (↑(pushes c) : Multiset (Msg K V))
        = (c.getLast hc).2 ::ₘ (↑(pulls c) : Multiset (Msg K V))
  | [], hc, _ => absurd rfl hc
  | [pq], _, _ => by
      simp only [pushes, pulls, List.map_cons, List.map_nil, List.head_cons,
        List.getLast_singleton]
      rw [Multiset.cons_coe, Multiset.cons_coe]
      exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)
  | pq :: b :: rest, _, hlink => by
      obtain ⟨hpb, htail⟩ := List.isChain_cons_cons.mp hlink
      have ih := chain_shift (b :: rest) (List.cons_ne_nil _ _) htail
      simp only [List.head_cons] at ih ⊢
      rw [List.getLast_cons (List.cons_ne_nil b rest)]
      have hpush : (↑(pushes (pq :: b :: rest)) : Multiset (Msg K V))
          = pq.2 ::ₘ ↑(pushes (b :: rest)) := by
        simp [pushes, Multiset.cons_coe]
      have hpull : (↑(pulls (pq :: b :: rest)) : Multiset (Msg K V))
          = pq.1 ::ₘ ↑(pulls (b :: rest)) := by
        simp [pulls, Multiset.cons_coe]
      rw [hpush, hpull, ← hpb, ih]
      exact Multiset.cons_swap _ _ _

/-! ## The per-key chain forcing step -/

/-- **Per-key chain forcing, one induction step.** `live` is the current frontier at key `k`;
`c` is the minimal row's chain at `k` (nonempty); `P`/`Q` are the remaining rows' pushes/pulls
at `k`, with every remaining push at time `≥ t` (minimality suffices — see deviation D1; the
design's `t + 8` gap is consumed via `chainForcing_step_of_gap`). `Q` is unconstrained: later
rows' head pulls may legitimately claim this row's last push. The balance forces the head pull
to equal `live`, cancels the chain, and re-establishes the balance with the last push as the
new frontier, whose time is `≤ t + 4` (invariant 3 re-establishes since `t + 4 < t + 8 ≤` every
remaining row's time). -/
theorem chainForcing_step {k : K} {t : ℕ} {live finM : Msg K V}
    {c : List (Touch K V)} (hc : c ≠ []) (hok : ChainOK k t c)
    {P Q : Multiset (Msg K V)} (hP : ∀ m ∈ P, t ≤ m.time)
    (hbal : live ::ₘ ((↑(pushes c) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls c) : Multiset (Msg K V)) + Q)) :
    (c.head hc).1 = live ∧ live.time < t ∧
      ((c.getLast hc).2 ::ₘ P = finM ::ₘ Q) ∧ (c.getLast hc).2.time ≤ t + 4 := by
  -- Forcing: the head pull sits in the balance's RHS, hence in its LHS; every push (own chain
  -- or other rows) has time ≥ t while the head pull's time is < t, so it can only match `live`.
  have hp₁ : (c.head hc).1 = live := by
    have hmem : (c.head hc).1 ∈ live ::ₘ ((↑(pushes c) : Multiset (Msg K V)) + P) := by
      rw [hbal]
      refine Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inl ?_))
      exact Multiset.mem_coe.mpr (List.mem_map_of_mem (List.head_mem hc))
    have hlt := hok.head_lt hc
    rcases Multiset.mem_cons.mp hmem with h | h
    · exact h
    · exfalso
      rcases Multiset.mem_add.mp h with h | h
      · obtain ⟨pq, hpq, heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
        have hlo := hok.push_lo pq hpq
        rw [heq] at hlo
        omega
      · have := hP _ h
        omega
  -- Cancellation: rewrite the LHS through the chain-shift identity, then cancel the (common)
  -- pull multiset from both sides.
  have hshift := chain_shift c hc hok.link
  rw [hp₁] at hshift
  have hstep : (c.getLast hc).2 ::ₘ ((↑(pulls c) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls c) : Multiset (Msg K V)) + Q) := by
    rw [← Multiset.cons_add, ← hshift, Multiset.cons_add]
    exact hbal
  have hcancel : (c.getLast hc).2 ::ₘ P = finM ::ₘ Q := by
    have h2 : (↑(pulls c) : Multiset (Msg K V)) + ((c.getLast hc).2 ::ₘ P)
        = (↑(pulls c) : Multiset (Msg K V)) + (finM ::ₘ Q) := by
      rw [Multiset.add_cons, Multiset.add_cons]
      exact hstep
    exact add_left_cancel h2
  exact ⟨hp₁, hp₁ ▸ hok.head_lt hc, hcancel, hok.push_hi _ (List.getLast_mem hc)⟩

/-- The design-literal form of `chainForcing_step`: other rows' pushes carry the full `t + 8`
gap (supplied by `stateBalance_remaining_ge_eight` + each row's own `push_lo`), and the frontier
carries invariant 3's bound `live.time ≤ t` (unused by the algebra — deviation D2). -/
theorem chainForcing_step_of_gap {k : K} {t : ℕ} {live finM : Msg K V}
    {c : List (Touch K V)} (hc : c ≠ []) (hok : ChainOK k t c)
    {P Q : Multiset (Msg K V)} (hP8 : ∀ m ∈ P, t + 8 ≤ m.time)
    (_hlive : live.time ≤ t)
    (hbal : live ::ₘ ((↑(pushes c) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls c) : Multiset (Msg K V)) + Q)) :
    (c.head hc).1 = live ∧ live.time < t ∧
      ((c.getLast hc).2 ::ₘ P = finM ::ₘ Q) ∧ (c.getLast hc).2.time ≤ t + 4 :=
  chainForcing_step hc hok (fun m hm => by have := hP8 m hm; omega) hbal

/-! ## The state-bus uniqueness of the minimal row -/

/-- **State-balance uniqueness of the minimal row** (proved, not assumed — invariant 2). Rows
are `(statePull, statePush)` pairs with the `+8` clock discipline and all pull times `≥ t`;
`head.time = t`; the popped row `r₀` pulls `head`. Then every *other* row's pull time is
strictly greater than `t`: a second pull at time `t` could match no push (times `≥ t + 8`), so
it would equal `head` — but then the pulls contain two copies of `head`, and after cancelling
the LHS `head` some push must equal `head`, impossible by time. -/
theorem stateBalance_unique_minimal {t : ℕ} {head fin : Msg K V}
    {l1 l2 : List (Touch K V)} {r₀ : Touch K V}
    (htime8 : ∀ r ∈ l1 ++ r₀ :: l2, (Prod.snd r).time = (Prod.fst r).time + 8)
    (hmin : ∀ r ∈ l1 ++ r₀ :: l2, t ≤ (Prod.fst r).time)
    (hhead_t : head.time = t)
    (hr₀ : r₀.1 = head)
    (hbal : head ::ₘ (↑((l1 ++ r₀ :: l2).map Prod.snd) : Multiset (Msg K V))
      = fin ::ₘ (↑((l1 ++ r₀ :: l2).map Prod.fst) : Multiset (Msg K V))) :
    ∀ r' ∈ l1 ++ l2, t < (Prod.fst r').time := by
  intro r' hr'
  by_contra hle
  have hr'_full : r' ∈ l1 ++ r₀ :: l2 := mem_middle r₀ hr'
  have ht' : (Prod.fst r').time = t := le_antisymm (Nat.not_lt.mp hle) (hmin r' hr'_full)
  -- Step 1: the second pull at time `t` can only match `head` in the balance.
  have hmem : r'.1 ∈ head ::ₘ (↑((l1 ++ r₀ :: l2).map Prod.snd) : Multiset (Msg K V)) := by
    rw [hbal]
    exact Multiset.mem_cons_of_mem (Multiset.mem_coe.mpr (List.mem_map_of_mem hr'_full))
  have hr'_head : r'.1 = head := by
    rcases Multiset.mem_cons.mp hmem with h | h
    · exact h
    · exfalso
      obtain ⟨r'', hr''_mem, heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
      have h8 := htime8 r'' hr''_mem
      have hm := hmin r'' hr''_mem
      rw [heq] at h8
      omega
  -- Step 2: two copies of `head` among the pulls sink the balance — cancelling the LHS `head`
  -- forces some push to equal `head`, impossible by the `+8` time discipline.
  have hpop : (↑((l1 ++ r₀ :: l2).map Prod.fst) : Multiset (Msg K V))
      = r₀.1 ::ₘ ↑((l1 ++ l2).map Prod.fst) := coe_map_pop Prod.fst l1 l2 r₀
  have hmem2 : head ∈ (↑((l1 ++ l2).map Prod.fst) : Multiset (Msg K V)) := by
    rw [← hr'_head]
    exact Multiset.mem_coe.mpr (List.mem_map_of_mem hr')
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hmem2
  rw [hpop, hr₀, hrest, Multiset.cons_swap fin head] at hbal
  have hpushes := (Multiset.cons_inj_right head).mp hbal
  have hhead_push : head ∈ (↑((l1 ++ r₀ :: l2).map Prod.snd) : Multiset (Msg K V)) := by
    rw [hpushes]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  obtain ⟨r'', hr''_mem, heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hhead_push)
  have h8 := htime8 r'' hr''_mem
  have hm := hmin r'' hr''_mem
  rw [heq] at h8
  omega

/-- **Composition with mod-8 window alignment** (invariant 1): the balance-forced `> t` of
`stateBalance_unique_minimal` lifts to the design's `≥ t + 8` for every remaining row, which
(with each row's own `push_lo`) supplies `chainForcing_step_of_gap`'s `hP8` and keeps every
remaining push out of the popped row's window `[t, t+4] ⊂ [t, t+8)`. -/
theorem stateBalance_remaining_ge_eight {t : ℕ} {head fin : Msg K V}
    {l1 l2 : List (Touch K V)} {r₀ : Touch K V}
    (htime8 : ∀ r ∈ l1 ++ r₀ :: l2, (Prod.snd r).time = (Prod.fst r).time + 8)
    (hmin : ∀ r ∈ l1 ++ r₀ :: l2, t ≤ (Prod.fst r).time)
    (halign : ∀ r ∈ l1 ++ r₀ :: l2, (Prod.fst r).time % 8 = t % 8)
    (hhead_t : head.time = t)
    (hr₀ : r₀.1 = head)
    (hbal : head ::ₘ (↑((l1 ++ r₀ :: l2).map Prod.snd) : Multiset (Msg K V))
      = fin ::ₘ (↑((l1 ++ r₀ :: l2).map Prod.fst) : Multiset (Msg K V))) :
    ∀ r' ∈ l1 ++ l2, t + 8 ≤ (Prod.fst r').time := by
  intro r' hr'
  have h1 := stateBalance_unique_minimal htime8 hmin hhead_t hr₀ hbal r' hr'
  have h2 := halign r' (mem_middle r₀ hr')
  omega

/-! ## Deriving the chain links from balance (D4 resolution)

Per-slot in-circuit facts only — no link assumptions. Each slot's pull is strictly earlier than
its own push (`prev_clk < clk`), hence than every own push from that slot on (slot
monotonicity) and than every other row's push (`≤ t + 4 < t + 8 ≤`); so in the balance it can
only match the running front. Popping the matched slot re-founds the balance with that slot's
push as the new front, and the induction walks the whole slot list. -/

/-- Slot monotonicity propagates: the head's push is strictly earlier than every later push. -/
lemma head_lt_of_mono :
    ∀ (rest : List (Touch K V)) (pq : Touch K V),
      List.IsChain (fun a b => (Prod.snd a).time < (Prod.snd b).time) (pq :: rest) →
      ∀ pq' ∈ rest, (Prod.snd pq).time < (Prod.snd pq').time
  | [], _, _ => by simp
  | b :: rest', pq, h => by
      obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp h
      intro pq' hpq'
      rcases List.mem_cons.mp hpq' with rfl | hpq'
      · exact hab
      · exact lt_trans hab (head_lt_of_mono rest' b htail pq' hpq')

lemma pushes_cons_coe (pq : Touch K V) (c : List (Touch K V)) :
    (↑(pushes (pq :: c)) : Multiset (Msg K V)) = pq.2 ::ₘ ↑(pushes c) := by
  simp [pushes, Multiset.cons_coe]

lemma pulls_cons_coe (pq : Touch K V) (c : List (Touch K V)) :
    (↑(pulls (pq :: c)) : Multiset (Msg K V)) = pq.1 ::ₘ ↑(pulls c) := by
  simp [pulls, Multiset.cons_coe]

/-- **Head-pull forcing from per-slot facts alone** (no link hypotheses, no frontier-time
hypothesis): the first slot's pull can match neither an own push (strictly later, by
`prev_clk < clk` + slot monotonicity) nor another row's push (`≤ t + 4 < t + 8`), so it equals
the front. -/
lemma headPull_forced {t : ℕ} {front finM : Msg K V} {pq : Touch K V}
    {rest : List (Touch K V)} {P Q : Multiset (Msg K V)}
    (hslot : ∀ pq' ∈ pq :: rest, (Prod.fst pq').time < (Prod.snd pq').time)
    (hhi : ∀ pq' ∈ pq :: rest, (Prod.snd pq').time ≤ t + 4)
    (hmono : List.IsChain (fun a b => (Prod.snd a).time < (Prod.snd b).time) (pq :: rest))
    (hP : ∀ m ∈ P, t + 8 ≤ m.time)
    (hbal : front ::ₘ ((↑(pushes (pq :: rest)) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls (pq :: rest)) : Multiset (Msg K V)) + Q)) :
    pq.1 = front := by
  have hmem : pq.1 ∈ front ::ₘ ((↑(pushes (pq :: rest)) : Multiset (Msg K V)) + P) := by
    rw [hbal]
    refine Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inl ?_))
    exact Multiset.mem_coe.mpr (List.mem_map_of_mem List.mem_cons_self)
  rcases Multiset.mem_cons.mp hmem with h | h
  · exact h
  · exfalso
    have hs := hslot pq List.mem_cons_self
    rcases Multiset.mem_add.mp h with h | h
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

/-- Popping one matched slot from the balance: the forced head pull cancels against the front,
leaving the slot's own push as the new front. -/
lemma balance_pop {front finM : Msg K V} {pq : Touch K V} {rest : List (Touch K V)}
    {P Q : Multiset (Msg K V)} (hhead : pq.1 = front)
    (hbal : front ::ₘ ((↑(pushes (pq :: rest)) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls (pq :: rest)) : Multiset (Msg K V)) + Q)) :
    pq.2 ::ₘ ((↑(pushes rest) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls rest) : Multiset (Msg K V)) + Q) := by
  rw [pushes_cons_coe, pulls_cons_coe, Multiset.cons_add, Multiset.cons_add, hhead,
    Multiset.cons_swap finM front] at hbal
  exact (Multiset.cons_inj_right front).mp hbal

/-- The slot-walking induction: from per-slot facts and the balance with running front `front`,
the head pull equals `front` and all intra-row links hold. -/
lemma chainLinks_aux {t : ℕ} {finM : Msg K V} :
    ∀ (own : List (Touch K V)) (front : Msg K V) (P Q : Multiset (Msg K V)),
      (∀ pq ∈ own, (Prod.fst pq).time < (Prod.snd pq).time) →
      (∀ pq ∈ own, (Prod.snd pq).time ≤ t + 4) →
      List.IsChain (fun a b => (Prod.snd a).time < (Prod.snd b).time) own →
      (∀ m ∈ P, t + 8 ≤ m.time) →
      front ::ₘ ((↑(pushes own) : Multiset (Msg K V)) + P)
        = finM ::ₘ ((↑(pulls own) : Multiset (Msg K V)) + Q) →
      (∀ h : own ≠ [], (own.head h).1 = front) ∧
        List.IsChain (fun pq pq' => pq'.1 = pq.2) own
  | [], _, _, _, _, _, _, _, _ => ⟨fun h => absurd rfl h, List.isChain_nil⟩
  | [pq], _, P, Q, hslot, hhi, hmono, hP, hbal =>
      ⟨fun _ => headPull_forced hslot hhi hmono hP hbal, List.isChain_singleton _⟩
  | pq :: b :: rest', _, P, Q, hslot, hhi, hmono, hP, hbal => by
      have hhead := headPull_forced hslot hhi hmono hP hbal
      have hbal' := balance_pop hhead hbal
      obtain ⟨ih_head, ih_link⟩ := chainLinks_aux (b :: rest') pq.2 P Q
        (fun x hx => hslot x (List.mem_cons_of_mem _ hx))
        (fun x hx => hhi x (List.mem_cons_of_mem _ hx))
        (List.isChain_cons_cons.mp hmono).2 hP hbal'
      exact ⟨fun _ => hhead,
        List.isChain_cons_cons.mpr ⟨ih_head (List.cons_ne_nil _ _), ih_link⟩⟩

/-- **The D4 resolution: chain links are derivable from balance.** Given only per-slot
in-circuit facts (each slot's pull strictly before its own push, pushes in `[t, t+4]` strictly
increasing in slot order, everything at key `k`) plus the `t + 8` gap on other rows' pushes,
the balance forces the head pull to equal `live` and every later pull to equal the row's own
previous push — `ChainOK.link` holds with no circuit-certified link facts. Load-bearing
hypotheses: `hslot`, `hhi`, `hmono`, `hP`, `hbal` (see D5 — the keys, `hlo`, and any
`live.time` bound are carried only for design fidelity). Combined with the walk's frontier
bound (`live.time < t`, re-founded by `chainForcing_step`), `p₁ = live` also derives
`ChainOK.head_lt`. -/
theorem chainLinks_of_balance {k : K} {t : ℕ} {live finM : Msg K V}
    {own : List (Touch K V)} (hne : own ≠ [])
    (_hkey_pull : ∀ pq ∈ own, (Prod.fst pq).key = k)
    (_hkey_push : ∀ pq ∈ own, (Prod.snd pq).key = k)
    (hslot : ∀ pq ∈ own, (Prod.fst pq).time < (Prod.snd pq).time)
    (_hlo : ∀ pq ∈ own, t ≤ (Prod.snd pq).time)
    (hhi : ∀ pq ∈ own, (Prod.snd pq).time ≤ t + 4)
    (hmono : List.IsChain (fun a b => (Prod.snd a).time < (Prod.snd b).time) own)
    {P Q : Multiset (Msg K V)} (hP : ∀ m ∈ P, t + 8 ≤ m.time)
    (hbal : live ::ₘ ((↑(pushes own) : Multiset (Msg K V)) + P)
      = finM ::ₘ ((↑(pulls own) : Multiset (Msg K V)) + Q)) :
    (own.head hne).1 = live ∧ List.IsChain (fun pq pq' => pq'.1 = pq.2) own := by
  obtain ⟨hhead, hlink⟩ := chainLinks_aux own live P Q hslot hhi hmono hP hbal
  exact ⟨hhead hne, hlink⟩

end SP6

#print axioms SP6.chain_shift
#print axioms SP6.chainForcing_step
#print axioms SP6.chainForcing_step_of_gap
#print axioms SP6.stateBalance_unique_minimal
#print axioms SP6.stateBalance_remaining_ge_eight
#print axioms SP6.chainLinks_of_balance
