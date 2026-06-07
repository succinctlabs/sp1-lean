import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Int

/-! # Multiplicity-weighted interaction bus (the trace-level lookup-bus core)

This is the **provable, circuit-free** heart of SP1's cross-chip interaction model, ported
natively from `sp1-lean`'s `SP1Clean/SP1Lookup.lean` (the pure-`List`/`ℤ` portion — the part that
ships axiom-clean there, untouched by the gated-lookup machinery that was `sorry`-blocked).

SP1's interaction model is a **multiplicity-weighted multiset bus**: every chip row contributes
`(kind, table_id, entry, multiplicity)` tuples to one of several typed buses (`State`, `Byte`,
`Program`, `Memory`, …); global soundness reduces to "for every `(kind, table_id, entry)` key, the
signed multiplicity sum over all rows is zero." Sends are positive, receives are negative. This
mirrors SP1's Rust `AirInteraction<E> { values, multiplicity, kind }`
(`crates/hypercube/src/air/interaction.rs`) and `InteractionKind` enum.

Because the per-key sum is a `List.filter`+`List.map`+`List.sum`, every property below is
permutation-invariant by construction — there is no order dependence (unlike the memory bus's
"last write wins"). That is what makes this core directly provable. The *connection* of a balanced
bus to a per-operation semantic property (e.g. the State bus's PC chain) is the genuinely hard step
and lives, per-bus, in the trace-consistency modules (`Soundness/StateConsistency.lean`). -/

namespace SP1Clean

/-- Tag for each cross-chip interaction. Mirrors SP1's `InteractionKind`
(`crates/hypercube/src/lookup/interaction.rs`). We carry the buses this project models; others
are listed so the discriminator covers SP1's full topology. -/
inductive InteractionKind where
  | Memory
  | Byte
  | Program
  | State
  deriving DecidableEq, Repr, Inhabited

/-- A single interaction-bus contribution: which bus, which named table within it, the entry (the
table row, as a list of `ℕ` — field values projected through `ZMod.val`), and the **signed**
multiplicity (`ℤ`: sends positive, receives negative). For a balanced bus the multiplicities for
each distinct `(kind, table_id, entry)` sum to zero. -/
abbrev LookupAccess := InteractionKind × String × List ℕ × ℤ

/-- A list of interaction-bus contributions in trace-emission order. Each chip row contributes 0 or
more entries. -/
abbrev LookupAccessList := List LookupAccess

namespace LookupAccessList

/-- The grouping key: which bus, which table, which entry — multiplicity excluded. -/
abbrev LookupKey := InteractionKind × String × List ℕ

@[reducible] def keyOf (a : LookupAccess) : LookupKey := (a.1, a.2.1, a.2.2.1)
@[reducible] def multOf (a : LookupAccess) : ℤ := a.2.2.2

/-- Restrict to the contributions matching one `(kind, table_id, entry)` key. -/
def filterKey (accesses : LookupAccessList) (k : LookupKey) : LookupAccessList :=
  accesses.filter (fun a => keyOf a = k)

/-- Signed multiplicity sum for one key across the whole list. The bus is balanced iff this is `0`
for every key. -/
def multiplicitySum (accesses : LookupAccessList) (k : LookupKey) : ℤ :=
  ((filterKey accesses k).map multOf).sum

theorem multiplicitySum_nil (k : LookupKey) : multiplicitySum [] k = 0 := rfl

theorem multiplicitySum_cons (head : LookupAccess) (tail : LookupAccessList) (k : LookupKey) :
    multiplicitySum (head :: tail) k =
      (if keyOf head = k then multOf head else 0) + multiplicitySum tail k := by
  simp only [multiplicitySum, filterKey, List.filter_cons]
  by_cases h : keyOf head = k
  · simp [h]
  · simp [h]

theorem multiplicitySum_append (l1 l2 : LookupAccessList) (k : LookupKey) :
    multiplicitySum (l1 ++ l2) k = multiplicitySum l1 k + multiplicitySum l2 k := by
  simp only [multiplicitySum, filterKey, List.filter_append, List.map_append, List.sum_append]

/-- Permutation invariance: reordering rows does not change any per-key sum. This is the structural
fact that makes `isConsistentBalanced` permutation-invariant. -/
theorem multiplicitySum_perm (l1 l2 : LookupAccessList) (h : l1.Perm l2) (k : LookupKey) :
    multiplicitySum l1 k = multiplicitySum l2 k := by
  simp only [multiplicitySum, filterKey]
  exact (h.filter _).map _ |>.sum_eq

/-! ## Consistency predicates -/

/-- Online form: for every key that appears anywhere, the signed sum is zero (a single-pass trace
analyzer's check). -/
def isConsistentOnline (accesses : LookupAccessList) : Prop :=
  ∀ (k : LookupKey), (∃ a ∈ accesses, keyOf a = k) → multiplicitySum accesses k = 0

/-- Balanced form: every key (observed or not) sums to zero. Equivalent, since absent keys sum to
zero by construction. -/
def isConsistentBalanced (accesses : LookupAccessList) : Prop :=
  ∀ (k : LookupKey), multiplicitySum accesses k = 0

theorem isConsistentBalanced_implies_isConsistentOnline (accesses : LookupAccessList) :
    isConsistentBalanced accesses → isConsistentOnline accesses := by
  intro h k _; exact h k

theorem isConsistentBalanced_perm (l1 l2 : LookupAccessList) (h_perm : l1.Perm l2)
    (h_bal : isConsistentBalanced l1) : isConsistentBalanced l2 := by
  intro k
  rw [← multiplicitySum_perm l1 l2 h_perm k]
  exact h_bal k

theorem multiplicitySum_filter (accesses : LookupAccessList) (k : LookupKey) :
    multiplicitySum accesses k = multiplicitySum (filterKey accesses k) k := by
  simp only [multiplicitySum, filterKey, List.filter_filter, Bool.and_self]

/-- The online ("every observed key") and balanced ("every key") forms coincide, because absent
keys trivially sum to zero. -/
theorem isConsistentBalanced_iff_allBalanced (accesses : LookupAccessList) :
    isConsistentBalanced accesses ↔
      (∀ (k : LookupKey), (∃ a ∈ accesses, keyOf a = k) → multiplicitySum accesses k = 0) := by
  constructor
  · intro h k _; exact h k
  · intro h k
    by_cases h_mem : ∃ a ∈ accesses, keyOf a = k
    · exact h k h_mem
    · simp only [multiplicitySum, filterKey]
      rw [show (accesses.filter (fun a => keyOf a = k)) = [] from ?_]
      · rfl
      · apply List.filter_eq_nil_iff.mpr
        intro a h_a h_keq
        apply h_mem
        exact ⟨a, h_a, by simpa using h_keq⟩

/-- Main equivalence (parallel to OfflineMemory's online/offline theorem): online consistency holds
iff *some* permutation is balanced. Since `multiplicitySum` is permutation-invariant, the identity
permutation works — the two forms are pointwise equivalent. The permutation quantifier is kept for
API symmetry with the order-sensitive memory bus. -/
theorem isConsistentOnline_iff_isConsistentBalanced (accesses : LookupAccessList) :
    isConsistentOnline accesses ↔
      ∃ permuted : LookupAccessList, permuted.Perm accesses ∧ isConsistentBalanced permuted := by
  constructor
  · intro h_online
    exact ⟨accesses, .refl _, (isConsistentBalanced_iff_allBalanced accesses).mpr h_online⟩
  · rintro ⟨permuted, h_perm, h_bal⟩
    intro k _
    rw [← multiplicitySum_perm permuted accesses h_perm k]
    exact h_bal k

/-! ## Trace-level aggregation -/

/-- Concatenate per-row interaction contributions into one trace-level list. -/
def aggregateChipRows {α : Type} (rows : List α) (perRow : α → LookupAccessList) :
    LookupAccessList :=
  rows.flatMap perRow

/-- The trace-level claim a per-bus consistency module discharges: the aggregated per-row
contributions form a balanced bus. -/
def TraceLookupConsistent {α : Type} (rows : List α) (perRow : α → LookupAccessList) : Prop :=
  (aggregateChipRows rows perRow).isConsistentOnline

/-! ## The provider-cancels-sends lemma (the kernel of "balance ⟹ membership")

For a **lookup** bus (a preprocessed table, e.g. `ByteChip`) the consumers all *send* with non-negative
multiplicity and the table *receives* with negative multiplicity. The structural fact that drives every
"a balanced lookup bus makes each looked-up row a table member" argument: a strictly-positive send at a
key forces the provider to carry an entry at that key (it must, to cancel the send). Combined with "the
provider only ever carries valid-table-row keys" (native, by the table's construction), this gives
membership of every real send. -/

/-- A key with a strictly-positive consumer send on a balanced bus is **touched by the provider**: the
provider list has an entry at that key. (Consumers send non-negatively; the provider must cancel.) -/
theorem provider_touches_pos_send
    (consumers prov : LookupAccessList)
    (h_nonneg : ∀ b ∈ consumers, 0 ≤ multOf b)
    (h_bal : isConsistentBalanced (consumers ++ prov))
    (a : LookupAccess) (ha : a ∈ consumers) (h_pos : 0 < multOf a) :
    ∃ b ∈ prov, keyOf b = keyOf a := by
  have hbalk : multiplicitySum consumers (keyOf a) + multiplicitySum prov (keyOf a) = 0 := by
    have := h_bal (keyOf a); rwa [multiplicitySum_append] at this
  -- the consumers' sum at this key is `≥ multOf a > 0` (a is one of them; all are non-negative)
  have hcons_pos : 0 < multiplicitySum consumers (keyOf a) := by
    have ha_mem : multOf a ∈ (filterKey consumers (keyOf a)).map multOf :=
      List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [keyOf]⟩, rfl⟩
    have hle : multOf a ≤ multiplicitySum consumers (keyOf a) := by
      refine List.single_le_sum (fun x hx => ?_) _ ha_mem
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact h_nonneg b (List.mem_of_mem_filter hb)
    omega
  -- so the provider's sum at this key is non-zero, hence its filtered list is non-empty
  have hprov_ne : multiplicitySum prov (keyOf a) ≠ 0 := by omega
  by_contra h
  push_neg at h
  refine hprov_ne ?_
  simp only [multiplicitySum, filterKey]
  rw [List.filter_eq_nil_iff.mpr ?_]; · rfl
  intro b hb hkb
  exact absurd (by simpa using hkb) (h b hb)

/-! ## The closed-bus matching lemma (the kernel of "balance ⟹ a canceling receive exists")

For an **internal/closed** bus (e.g. the State PC-chain or the register Memory bus) there is no separate
provider: every send is cancelled by a *receive of another row*, not by an off-chip table. The structural
fact that drives every "balance ⟹ order-sensitive consistency" argument on such a bus: a strictly-positive
contribution at a key forces a strictly-*negative* contribution at the same key somewhere in the same list
(the sum at that key is `0`, and a positive summand needs a negative one to cancel it). The caller recovers
*which* row from the returned access's membership. This is the closed-bus dual of
`provider_touches_pos_send`. -/

/-- **Closed-bus matching.** On a balanced bus, a strictly-positive contribution at key `k` forces a
strictly-negative contribution at the SAME key in the SAME list. The returned `b` is the witnessing access;
the caller recovers its row from `b ∈ accesses`. -/
theorem balanced_pos_has_neg
    (accesses : LookupAccessList) (k : LookupKey)
    (h_bal : isConsistentBalanced accesses)
    (a : LookupAccess) (ha : a ∈ accesses) (hak : keyOf a = k) (h_pos : 0 < multOf a) :
    ∃ b ∈ accesses, keyOf b = k ∧ multOf b < 0 := by
  by_contra h
  push_neg at h
  -- if no contribution at key `k` is strictly negative, every summand of `multiplicitySum … k` is `≥ 0`
  have h_nonneg : ∀ x ∈ (filterKey accesses k).map multOf, 0 ≤ x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    have hb' := List.mem_filter.mp hb
    have hbk : keyOf b = k := by simpa using hb'.2
    have := h b hb'.1 hbk
    omega
  -- `a` itself is a strictly-positive summand at key `k`
  have ha_mem : multOf a ∈ (filterKey accesses k).map multOf :=
    List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [hak]⟩, rfl⟩
  have hle : multOf a ≤ ((filterKey accesses k).map multOf).sum :=
    List.single_le_sum h_nonneg _ ha_mem
  -- but the whole sum is `0` (balance), contradicting `0 < multOf a ≤ 0`
  have hsum : ((filterKey accesses k).map multOf).sum = 0 := by
    have := h_bal k; rwa [multiplicitySum] at this
  omega

/-! ## Cross-bus disjointness (a key of one bus ignores every other bus)

The interaction buses share one multiset but never interfere: each `(kind, …)` key belongs to exactly one
`InteractionKind`, and a contribution list whose entries all carry kind `K` sums to `0` at every key of a
*different* kind. This is what lets the machine-wide balance be split per bus — the byte keys see only the
byte sends and the `ByteChip` provider, the program keys only the program fetches and the `ProgramChip`. -/

/-- A list none of whose entries match key `k` contributes `0` to it. -/
theorem multiplicitySum_eq_zero_of_keyOf_ne {l : LookupAccessList} {k : LookupKey}
    (h : ∀ a ∈ l, keyOf a ≠ k) : multiplicitySum l k = 0 := by
  simp only [multiplicitySum, filterKey]
  rw [List.filter_eq_nil_iff.mpr ?_]
  · rfl
  · intro a ha hka; exact absurd (by simpa using hka) (h a ha)

/-- A list all of whose entries carry interaction-kind `K` sums to `0` at any key of a *different* kind —
the cross-bus disjointness that lets one bus's keys ignore every other bus. -/
theorem multiplicitySum_zero_of_kind {l : LookupAccessList} {k : LookupKey} {K : InteractionKind}
    (h_pure : ∀ a ∈ l, (keyOf a).1 = K) (hk : k.1 ≠ K) : multiplicitySum l k = 0 :=
  multiplicitySum_eq_zero_of_keyOf_ne (fun a ha heq => hk (by rw [← heq]; exact h_pure a ha))

/-! ## Partition by interaction kind (the recombine lemma for combined faithfulness anchors)

A `LookupAccessList` permutes to the concatenation of its four per-kind filters — every access carries
exactly one of the four `InteractionKind`s. This is the bridge that assembles the four per-channel
syntactic faithfulness facts (each an `=`/`Perm` of the channel-filtered projections) into one combined
"full emitted = full oracle" `Perm` over a chip's whole interaction list. The bus is a multiset, so the
order the four blocks come out in is irrelevant. -/

/-- `count x` of a kind-filtered list: keeps the count iff `x`'s kind matches, else `0`. -/
private lemma count_filter_kind (x : LookupAccess) (K : InteractionKind) (l : LookupAccessList) :
    List.count x (l.filter (fun a => a.1 = K)) = if x.1 = K then List.count x l else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filter_cons]
    by_cases haK : a.1 = K
    · simp only [haK, decide_true, if_true]
      rw [List.count_cons, List.count_cons, ih]
      by_cases hxK : x.1 = K
      · simp [hxK]
      · have hax : a ≠ x := by rintro rfl; exact hxK haK
        simp [hxK, hax]
    · simp only [haK, decide_false, Bool.false_eq_true, if_false, ih]
      rw [List.count_cons]
      by_cases hxK : x.1 = K
      · have hax : a ≠ x := by rintro rfl; exact haK hxK
        simp [hxK, hax]
      · simp [hxK]

/-- A `LookupAccessList` is a permutation of `(filter State) ++ (filter Byte) ++ (filter Memory) ++
(filter Program)` — its four-way partition by `InteractionKind`. -/
theorem perm_filter_by_kind (l : LookupAccessList) :
    l.Perm (l.filter (fun a => a.1 = InteractionKind.State) ++
              l.filter (fun a => a.1 = InteractionKind.Byte) ++
              l.filter (fun a => a.1 = InteractionKind.Memory) ++
              l.filter (fun a => a.1 = InteractionKind.Program)) := by
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append, count_filter_kind]
  rcases x with ⟨k, rest⟩
  cases k <;> simp

end LookupAccessList

end SP1Clean
