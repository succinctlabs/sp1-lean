import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Ring

/-! # Multiplicity-weighted interaction bus (the trace-level lookup-bus core)

The **provable, circuit-free** heart of SP1's cross-chip interaction model.
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

/-- The semantically active interaction contributions. An AIR interaction whose multiplicity is
zero contributes neither to LogUp nor to the trace-level signed multiplicity balance, so its
otherwise-unused key is not observable. This is the `LookupAccess` analogue of Clean's
`Air.Balance.activeInteractions`. -/
def active (accesses : LookupAccessList) : LookupAccessList :=
  accesses.filter (fun access => multOf access ≠ 0)

/-- Reordering a complete interaction list only reorders its active submultiset. -/
theorem active_perm {left right : LookupAccessList} (h : left.Perm right) :
    (active left).Perm (active right) :=
  h.filter _

theorem active_cons (head : LookupAccess) (tail : LookupAccessList) :
    active (head :: tail) =
      if multOf head ≠ 0 then head :: active tail else active tail := by
  by_cases hmult : multOf head = 0 <;> simp [active, hmult]

/-- Filtering for a bus or table commutes with discarding zero-multiplicity entries. -/
theorem active_append (left right : LookupAccessList) :
    active (left ++ right) = active left ++ active right := by
  simp only [active, List.filter_append]

theorem active_filter (accesses : LookupAccessList) (keep : LookupAccess → Bool) :
    active (accesses.filter keep) = (active accesses).filter keep := by
  simp only [active, List.filter_filter, Bool.and_comm]

/-- Negate a `LookupAccess`'s multiplicity, fixing its key. The faithfulness bridge for the W11
program-bus polarity flip: our circuit now emits the Program fetch as a `pull` (`−is_real`), so it
equals SP1's extracted oracle Program block **up to per-entry multiplicity negation** (a sound LogUp
sign symmetry — negating one channel's multiplicities preserves the balance). -/
@[reducible] def negMult (a : LookupAccess) : LookupAccess := (a.1, a.2.1, a.2.2.1, -a.2.2.2)

@[simp] lemma negMult_mk (k : InteractionKind) (s : String) (l : List ℕ) (m : ℤ) :
    negMult (k, s, l, m) = (k, s, l, -m) := rfl

@[simp] lemma keyOf_negMult (a : LookupAccess) : keyOf (negMult a) = keyOf a := rfl

@[simp] lemma multOf_negMult (a : LookupAccess) : multOf (negMult a) = -multOf a := rfl

lemma negMult_negMult (a : LookupAccess) : negMult (negMult a) = a := by
  simp only [negMult, neg_neg]

/-- `negMult` is a list-map involution: re-negating an already-negated block recovers it. Used (via
`rw`) by the combined faithfulness anchors, whose Program block carries one `negMult` (the W11
sign-flip) so the rest of the equation stays the pristine SP1 oracle. Not `@[simp]` (the bare LHS
is not in simp-normal form — `List.map_map` rewrites it first). -/
lemma map_negMult_negMult (l : LookupAccessList) :
    (l.map negMult).map negMult = l := by
  simp only [List.map_map, Function.comp_def, negMult_negMult, List.map_id']

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
  by_cases h : keyOf head = k <;> simp [h]

theorem multiplicitySum_append (l1 l2 : LookupAccessList) (k : LookupKey) :
    multiplicitySum (l1 ++ l2) k = multiplicitySum l1 k + multiplicitySum l2 k := by
  simp only [multiplicitySum, filterKey, List.filter_append, List.map_append, List.sum_append]

/-- How many times a *provider* must supply one key so that a consumer-only ledger balances at it.

`skeleton` is a ledger of consumers with the providers for that key deliberately absent, so its
contribution at the key is nonpositive and this is exactly its additive inverse. The `Int.toNat` is
therefore not truncation — callers state the nonpositivity separately, and truncation would silently
turn a provider *over*-supply into a demand of zero rather than a failure.

Both the exact→native transport and the completeness-side provider closure recount against this one
definition, which is why it lives here on the shared bus vocabulary rather than in either layer. -/
def providerRecount (skeleton : LookupAccessList) (key : LookupKey) : ℕ :=
  Int.toNat (-multiplicitySum skeleton key)

@[simp] theorem providerRecount_nil (key : LookupKey) : providerRecount [] key = 0 := rfl

/-- A ledger that is already balanced at a key demands nothing there. -/
theorem providerRecount_eq_zero_of_balanced {skeleton : LookupAccessList} {key : LookupKey}
    (h : multiplicitySum skeleton key = 0) : providerRecount skeleton key = 0 := by
  simp [providerRecount, h]

/-- Removing zero-multiplicity contributions preserves the signed balance at every key. -/
theorem multiplicitySum_active (accesses : LookupAccessList) (k : LookupKey) :
    multiplicitySum (active accesses) k = multiplicitySum accesses k := by
  induction accesses with
  | nil => rfl
  | cons head tail ih =>
      by_cases hmult : multOf head = 0 <;> simp [active_cons, multiplicitySum_cons, hmult, ih]

/-- **Filtering before projecting is invisible at a key the filter cannot drop.**

The shape every "whole ledger versus one channel's ledger" comparison reduces to: if every source
item whose projection lands on `k` survives the filter, the two sums agree at `k`. Stated over an
arbitrary source type because the source is Clean `Interaction`s, which this file cannot mention. -/
theorem multiplicitySum_filter_map_eq {α : Type*} (l : List α) (f : α → LookupAccess)
    (q : α → Bool) (k : LookupKey) (hkeep : ∀ a ∈ l, keyOf (f a) = k → q a = true) :
    multiplicitySum ((l.filter q).map f) k = multiplicitySum (l.map f) k := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
      have htail : ∀ a ∈ tail, keyOf (f a) = k → q a = true :=
        fun a ha => hkeep a (List.mem_cons_of_mem _ ha)
      rw [List.map_cons, multiplicitySum_cons]
      by_cases hq : q head = true
      · rw [List.filter_cons_of_pos hq, List.map_cons, multiplicitySum_cons, ih htail]
      · have hne : keyOf (f head) ≠ k := fun hkey =>
          hq (hkeep head List.mem_cons_self hkey)
        rw [List.filter_cons_of_neg (by simpa using hq), ih htail, if_neg hne, zero_add]

/-- A concatenation of per-item ledgers sums per item. The `flatMap` counterpart of
`multiplicitySum_append`, for a table family indexed by a list (the seventeen fixed Range widths). -/
theorem multiplicitySum_flatMap {α : Type*} (l : List α) (f : α → LookupAccessList)
    (k : LookupKey) :
    multiplicitySum (l.flatMap f) k = (l.map fun a => multiplicitySum (f a) k).sum := by
  induction l with
  | nil => rw [List.flatMap_nil, multiplicitySum_nil, List.map_nil, List.sum_nil]
  | cons head tail ih =>
      rw [List.flatMap_cons, multiplicitySum_append, ih, List.map_cons, List.sum_cons]

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
    isConsistentBalanced accesses → isConsistentOnline accesses :=
  fun h k _ => h k

theorem isConsistentBalanced_perm (l1 l2 : LookupAccessList) (h_perm : l1.Perm l2)
    (h_bal : isConsistentBalanced l1) : isConsistentBalanced l2 :=
  fun k => multiplicitySum_perm l1 l2 h_perm k ▸ h_bal k

theorem multiplicitySum_filter (accesses : LookupAccessList) (k : LookupKey) :
    multiplicitySum accesses k = multiplicitySum (filterKey accesses k) k := by
  simp only [multiplicitySum, filterKey, List.filter_filter, Bool.and_self]

/-- The online ("every observed key") and balanced ("every key") forms coincide, because absent
keys trivially sum to zero. -/
theorem isConsistentBalanced_iff_allBalanced (accesses : LookupAccessList) :
    isConsistentBalanced accesses ↔
      (∀ (k : LookupKey), (∃ a ∈ accesses, keyOf a = k) → multiplicitySum accesses k = 0) := by
  refine ⟨fun h k _ => h k, fun h k => ?_⟩
  by_cases h_mem : ∃ a ∈ accesses, keyOf a = k
  · exact h k h_mem
  · have hnil : accesses.filter (fun a => keyOf a = k) = [] :=
      List.filter_eq_nil_iff.mpr fun a h_a h_keq => h_mem ⟨a, h_a, by simpa using h_keq⟩
    simp only [multiplicitySum, filterKey, hnil, List.map_nil, List.sum_nil]

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

For a **lookup** bus (a preprocessed table, e.g. `ByteChip`) the consumers all *send* with
non-negative multiplicity and the table *receives* with negative multiplicity. The structural fact
that drives every "a balanced lookup bus makes each looked-up row a table member" argument: a
strictly-positive send at a key forces the provider to carry an entry at that key (it must, to
cancel the send). Combined with "the provider only ever carries valid-table-row keys" (native, by
the table's construction), this gives membership of every real send. -/

/-- A key with a strictly-positive consumer send on a balanced bus is **touched by the provider**:
the provider list has an entry at that key. (Consumers send non-negatively; the provider must
cancel.) -/
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
  push Not at h
  have hnil : prov.filter (fun b => keyOf b = keyOf a) = [] :=
    List.filter_eq_nil_iff.mpr fun b hb hkb => absurd (by simpa using hkb) (h b hb)
  exact hprov_ne (by simp only [multiplicitySum, filterKey, hnil, List.map_nil, List.sum_nil])

/-! ## Sign symmetry — the flipped-polarity dual provider lemma

The W11 program-bus polarity flip makes the consumers *pull* (non-positive multiplicity) rather than
*send*; the provider then *pushes* (positive). Negating every multiplicity preserves the balance
(`multiplicitySum` is linear), so the flipped-polarity "balance ⟹ membership" reduces to
`provider_touches_pos_send` on the negated bus. -/

/-- `multiplicitySum` is negated by `negMult`-mapping the bus (`negMult` fixes keys, flips
multiplicities). -/
theorem multiplicitySum_map_negMult (l : LookupAccessList) (k : LookupKey) :
    multiplicitySum (l.map negMult) k = -multiplicitySum l k := by
  induction l with
  | nil => simp [multiplicitySum_nil]
  | cons hd tl ih =>
    rw [List.map_cons, multiplicitySum_cons, multiplicitySum_cons, ih, keyOf_negMult,
      multOf_negMult]
    by_cases h : keyOf hd = k <;> simp only [h, if_true, if_false] <;> omega

/-- Balance is invariant under negating every multiplicity. -/
theorem isConsistentBalanced_map_negMult (l : LookupAccessList) :
    isConsistentBalanced (l.map negMult) ↔ isConsistentBalanced l := by
  simp only [isConsistentBalanced, multiplicitySum_map_negMult, neg_eq_zero]

/-- **Flipped-polarity provider touch.** The dual of `provider_touches_pos_send`: a key with a
strictly-*negative* consumer pull on a balanced bus is touched by the provider (consumers pull
non-positively; the provider must cancel with a positive push). Proved by negating the whole bus
and applying the positive lemma. -/
theorem provider_touches_neg_send
    (consumers prov : LookupAccessList)
    (h_nonpos : ∀ b ∈ consumers, multOf b ≤ 0)
    (h_bal : isConsistentBalanced (consumers ++ prov))
    (a : LookupAccess) (ha : a ∈ consumers) (h_neg : multOf a < 0) :
    ∃ b ∈ prov, keyOf b = keyOf a := by
  have h_bal' : isConsistentBalanced (consumers.map negMult ++ prov.map negMult) := by
    rw [← List.map_append]; exact (isConsistentBalanced_map_negMult _).mpr h_bal
  have h_nonneg' : ∀ b ∈ consumers.map negMult, 0 ≤ multOf b := by
    intro b hb; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have := h_nonpos c hc; rw [multOf_negMult]; omega
  have ha' : negMult a ∈ consumers.map negMult := List.mem_map.mpr ⟨a, ha, rfl⟩
  have h_pos' : 0 < multOf (negMult a) := by rw [multOf_negMult]; omega
  obtain ⟨b', hb', hkey'⟩ := provider_touches_pos_send _ _ h_nonneg' h_bal' (negMult a) ha' h_pos'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
  exact ⟨b, hb, by simpa using hkey'⟩

/-! ## The closed-bus matching lemma (the kernel of "balance ⟹ a canceling receive exists")

For an **internal/closed** bus (e.g. the State PC-chain or the register Memory bus) there is no
separate provider: every send is cancelled by a *receive of another row*, not by an off-chip table.
The structural fact that drives every "balance ⟹ order-sensitive consistency" argument on such a
bus: a strictly-positive contribution at a key forces a strictly-*negative* contribution at the same
key somewhere in the same list (the sum at that key is `0`, and a positive summand needs a negative
one to cancel it). The caller recovers *which* row from the returned access's membership. This is
the closed-bus dual of `provider_touches_pos_send`. -/

/-- **Closed-bus matching.** On a balanced bus, a strictly-positive contribution at key `k` forces a
strictly-negative contribution at the SAME key in the SAME list. The returned `b` is the witnessing
access; the caller recovers its row from `b ∈ accesses`. -/
theorem balanced_pos_has_neg
    (accesses : LookupAccessList) (k : LookupKey)
    (h_bal : isConsistentBalanced accesses)
    (a : LookupAccess) (ha : a ∈ accesses) (hak : keyOf a = k) (h_pos : 0 < multOf a) :
    ∃ b ∈ accesses, keyOf b = k ∧ multOf b < 0 := by
  by_contra h
  push Not at h
  -- if no contribution at key `k` is strictly negative, every summand of `multiplicitySum … k`
  -- is `≥ 0`
  have h_nonneg : ∀ x ∈ (filterKey accesses k).map multOf, 0 ≤ x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    have hb' := List.mem_filter.mp hb
    have := h b hb'.1 (by simpa using hb'.2)
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

The interaction buses share one multiset but never interfere: each `(kind, …)` key belongs to
exactly one `InteractionKind`, and a contribution list whose entries all carry kind `K` sums to `0`
at every key of a *different* kind. This is what lets the machine-wide balance be split per bus —
the byte keys see only the byte sends and the `ByteChip` provider, the program keys only the program
fetches and the `ProgramChip`. -/

/-- A list none of whose entries match key `k` contributes `0` to it. -/
theorem multiplicitySum_eq_zero_of_keyOf_ne {l : LookupAccessList} {k : LookupKey}
    (h : ∀ a ∈ l, keyOf a ≠ k) : multiplicitySum l k = 0 := by
  have hnil : l.filter (fun a => keyOf a = k) = [] :=
    List.filter_eq_nil_iff.mpr fun a ha hka => absurd (by simpa using hka) (h a ha)
  simp only [multiplicitySum, filterKey, hnil, List.map_nil, List.sum_nil]

/-- A list all of whose entries carry interaction-kind `K` sums to `0` at any key of a *different*
kind — the cross-bus disjointness that lets one bus's keys ignore every other bus. -/
theorem multiplicitySum_zero_of_kind {l : LookupAccessList} {k : LookupKey} {K : InteractionKind}
    (h_pure : ∀ a ∈ l, (keyOf a).1 = K) (hk : k.1 ≠ K) : multiplicitySum l k = 0 :=
  multiplicitySum_eq_zero_of_keyOf_ne (fun a ha heq => hk (by rw [← heq]; exact h_pure a ha))

/-- **Restricting a ledger to one bus changes nothing at that bus's keys.**

The computability lever. `List.filter` computes; Clean's per-channel `interactionsWith` projection
does not (it decides `RawChannel` equality classically). So a bus-local obligation stated over the
*filtered whole ledger* is a closed term an evaluator can reduce on a concrete shard, while the same
obligation stated over the channel projection is not — and this says the two agree where it
matters. -/
theorem multiplicitySum_filterKind (l : LookupAccessList) {K : InteractionKind} {k : LookupKey}
    (h : k.1 = K) :
    multiplicitySum (l.filter fun a => a.1 = K) k = multiplicitySum l k := by
  have := multiplicitySum_filter_map_eq l id (fun a => a.1 = K) k
    (fun a _ hka => by simp only [id] at hka; rw [← hka] at h; simpa using h)
  simpa using this

/-! ## Partition by interaction kind (the recombine lemma for combined faithfulness anchors)

A `LookupAccessList` permutes to the concatenation of its four per-kind filters — every access
carries exactly one of the four `InteractionKind`s. This is the bridge that assembles the four
per-channel syntactic faithfulness facts (each an `=`/`Perm` of the channel-filtered projections)
into one combined "full emitted = full oracle" `Perm` over a chip's whole interaction list. The bus
is a multiset, so the order the four blocks come out in is irrelevant. -/

/-- `count x` of a kind-filtered list: keeps the count iff `x`'s kind matches, else `0`. -/
private lemma count_filter_kind (x : LookupAccess) (K : InteractionKind) (l : LookupAccessList) :
    List.count x (l.filter (fun a => a.1 = K)) = if x.1 = K then List.count x l else 0 := by
  by_cases hxK : x.1 = K
  · simp [hxK, List.count_filter]
  · simp only [hxK, if_false]
    exact List.count_eq_zero_of_not_mem fun hmem => hxK (by simpa using (List.mem_filter.mp hmem).2)

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

/-- **The access at a key**, carrying a chosen multiplicity. The shared primitive of both reasons
a bus balances: a hand-off spends it at `±1`, a closure at a recounted total. -/
def accessAt (key : LookupKey) (mult : ℤ) : LookupAccess := (key.1, key.2.1, key.2.2, mult)

@[simp] theorem keyOf_accessAt (key : LookupKey) (mult : ℤ) : keyOf (accessAt key mult) = key := rfl

@[simp] theorem multOf_accessAt (key : LookupKey) (mult : ℤ) :
    multOf (accessAt key mult) = mult := rfl

/-! ## Why a bus balances: exactly two reasons

A bus balances at a key when that key's pushes and pulls cancel, and in `sp1Ensemble` there are
exactly two structural reasons that happens. Both are explicit list constructions over
`LookupAccess`, so both **compute**: on a concrete shard either side is a closed term a kernel or an
evaluator can reduce, with no circuit, no environment and no field arithmetic in the way.

* **Hand-off.** The bus carries *tokens*, and a token is created once and consumed once. The State
  bus carries a single token — the machine's `(clock, pc)`, pushed by the boundary verifier, pulled
  and re-pushed by each instruction row, pulled again at the end. The Memory bus carries one token
  per *record*: a location's `(address, value, timestamp)`, pushed by whoever wrote it and pulled by
  the next access to that location. `handoff` is the ledger of a token's whole life.

* **Closure.** The bus has designated *providers*, and consumers pull whatever they like; the
  provider supplies each demanded key's aggregate. That is the Byte bus (all six opcode tables and
  all seventeen Range widths) and the Program bus. `closingAccesses`, below.

The distinction is structural rather than stylistic, and each reason is unavailable to the other's
bus. A hand-off bus cannot be closed: recounting would invent a supplier for a token nobody created,
and the multiplicity it invented would have no row to live on. A closed bus has no chain to
telescope: a byte key is pulled by however many unrelated rows happen to need it, in no order.
Which reason applies to which bus is `preprocessedKey`'s scope decision
(`Proofs/Completeness/Closure.lean`), made once rather than per proof.

The asymmetry in what the two need is the tell. Closure carries real side conditions — the keys must
not repeat, the consumer side must not be net-positive, nothing with nonzero demand may be omitted —
because it is an arithmetic argument about counts. Hand-off carries **none**: the balance is a fact
about the tokens themselves.
-/

/-- **One token's complete life**: created once, consumed once. A bus's hand-off ledger is the
concatenation of the lives of the tokens it carried. -/
def handoff (keys : List LookupKey) : LookupAccessList :=
  keys.flatMap fun key => [accessAt key 1, accessAt key (-1)]

@[simp] theorem handoff_nil : handoff [] = [] := rfl

theorem handoff_cons (key : LookupKey) (keys : List LookupKey) :
    handoff (key :: keys) = accessAt key 1 :: accessAt key (-1) :: handoff keys := rfl

/-- **A bus of complete lives balances at every key** — with no side condition whatsoever: no
`Nodup`, no bound, no nonpositivity premise. That is the whole force of the hand-off model, and the
sharpest contrast with the closure below, which needs all three. -/
theorem multiplicitySum_handoff (keys : List LookupKey) (k : LookupKey) :
    multiplicitySum (handoff keys) k = 0 := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      rw [handoff_cons, multiplicitySum_cons, multiplicitySum_cons, ih,
        keyOf_accessAt, keyOf_accessAt, multOf_accessAt, multOf_accessAt]
      by_cases h : key = k <;> simp [h]

/-- **A ledger that merely *permutes* complete lives balances**, which is the form a real trace
takes: its accesses are spread across fifty-three tables in emission order, never grouped by token.
This is the shape a completeness obligation on a hand-off bus should be stated in. -/
theorem multiplicitySum_of_perm_handoff {l : LookupAccessList} {keys : List LookupKey}
    (h : l.Perm (handoff keys)) (k : LookupKey) : multiplicitySum l k = 0 := by
  rw [multiplicitySum_perm _ _ h, multiplicitySum_handoff]

theorem isConsistentBalanced_of_perm_handoff {l : LookupAccessList} {keys : List LookupKey}
    (h : l.Perm (handoff keys)) : isConsistentBalanced l :=
  fun k => multiplicitySum_of_perm_handoff h k

/-! ### A chain of hand-offs is a hand-off

`handoff` says what a *balanced* hand-off bus looks like: each token pushed once and pulled once,
grouped by token. A real bus does not look like that. It looks like a **chain** — a boundary push of
the first token, then one row per link, each pulling what it holds and pushing what it produces, and
a boundary pull of whatever the last link left holding. The tokens are interleaved across
fifty-three tables in emission order, and each interior token's push and pull come from *different*
rows.

These three declarations are the bridge, and they are the whole reason the State and Memory buses
balance. Everything is a plain list statement — no circuit, no field, no channel — because that is
the level at which the fact is true. -/

/-- What one row of a hand-off bus emits: it consumes the token it holds and produces the next. -/
def linkAccesses (held next : LookupKey) : LookupAccessList :=
  [accessAt held (-1), accessAt next 1]

/-- **Padding rows drop out.**

Every row of a hand-off bus emits its pull/push pair whether or not it is real; a padding row emits
the pair at multiplicity `0`. `active` is what removes them, and this is the computation: filtering
the *accesses* by nonzero multiplicity is the same as filtering the *rows* by their gate.

That equality is why the hand-off obligation is stated over `active` — without it the padding rows'
zero-multiplicity accesses sit in the ledger with no token's life to belong to, and the permutation
is false for every trace that pads. -/
theorem active_flatMap_gatedPair {α : Type*} (items : List α) (gate : α → ℤ)
    (held next : α → LookupKey) (hgate : ∀ a ∈ items, gate a = 0 ∨ gate a = 1) :
    active (items.flatMap fun a => [accessAt (held a) (-gate a), accessAt (next a) (gate a)]) =
      (items.filter fun a => gate a = 1).flatMap fun a => linkAccesses (held a) (next a) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      have htail : ∀ a ∈ tail, gate a = 0 ∨ gate a = 1 :=
        fun a ha => hgate a (List.mem_cons_of_mem _ ha)
      rw [List.flatMap_cons, active_append, ih htail, List.filter_cons]
      rcases hgate head List.mem_cons_self with hzero | hone
      · rw [if_neg (by simp [hzero]), hzero]
        simp only [active, List.filter_cons, neg_zero, multOf_accessAt, ne_eq, not_true_eq_false,
          decide_false, Bool.false_eq_true, if_false, List.filter_nil, List.nil_append]
      · rw [if_pos (by simp [hone]), hone, List.flatMap_cons]
        simp only [active, List.filter_cons, multOf_accessAt, linkAccesses]
        norm_num

/-- **The chain condition**: each link consumes what its predecessor produced, starting from the
token the boundary pushed and ending with the one the boundary pulls.

For the State bus this is the PC chain (`Soundness/StateConsistency.lean`'s `pcChainProp`) — each
row's `next_pc` is the next row's `pc`, and the clock advances by the row's own increment. For the
Memory bus it is the per-location record chain. -/
def IsHandoffChain : LookupKey → List (LookupKey × LookupKey) → LookupKey → Prop
  | held, [], last => held = last
  | held, link :: rest, last => link.1 = held ∧ IsHandoffChain link.2 rest last

/-- **A chain's ledger is a hand-off's**, up to the reordering a real trace imposes.

The induction is the argument: peel one link, and the token it consumed is exactly the one the
boundary push produced — so that token's life closes, and what remains is a shorter chain whose
boundary push is the token this link produced. The `perm_middle` step is the interleaving: the
boundary pull sits at the front of the emitted ledger but belongs at the end of the chain. -/
theorem chainLedger_perm_handoff :
    ∀ (first : LookupKey) (links : List (LookupKey × LookupKey)) (last : LookupKey),
      IsHandoffChain first links last →
      ([accessAt first 1, accessAt last (-1)] ++
        links.flatMap fun link => linkAccesses link.1 link.2).Perm
        (handoff (first :: links.map Prod.snd)) := by
  intro first links
  induction links generalizing first with
  | nil =>
      intro last hchain
      cases hchain
      simp only [List.flatMap_nil, List.append_nil, List.map_nil, handoff_cons, handoff_nil]
      exact List.Perm.refl _
  | cons link rest ih =>
      intro last hchain
      obtain ⟨hhead, htail⟩ := hchain
      subst hhead
      have hstep := ih link.2 last htail
      have hL : ([accessAt link.1 1, accessAt last (-1)] ++
            ((link :: rest).flatMap fun l => linkAccesses l.1 l.2))
          = accessAt link.1 1 :: accessAt last (-1) ::
              ([accessAt link.1 (-1), accessAt link.2 1] ++
                (rest.flatMap fun l => linkAccesses l.1 l.2)) := by
        simp only [List.flatMap_cons, linkAccesses, List.cons_append, List.nil_append]
      have hR : handoff (link.1 :: (link :: rest).map Prod.snd)
          = accessAt link.1 1 :: accessAt link.1 (-1) ::
              handoff (link.2 :: rest.map Prod.snd) := by
        simp only [List.map_cons, handoff_cons]
      rw [hL, hR]
      refine List.Perm.cons _ (List.Perm.trans List.perm_middle.symm ?_)
      exact List.Perm.cons _ hstep

/-- **A chain's ledger balances at every key** — the form a bus-local obligation consumes. -/
theorem multiplicitySum_chainLedger {first last : LookupKey}
    {links : List (LookupKey × LookupKey)} (hchain : IsHandoffChain first links last)
    (k : LookupKey) :
    multiplicitySum ([accessAt first 1, accessAt last (-1)] ++
      links.flatMap fun link => linkAccesses link.1 link.2) k = 0 :=
  multiplicitySum_of_perm_handoff (chainLedger_perm_handoff first links last hchain) k

/-! ## The closing ledger, and why it balances

This is the arithmetic heart of the closure, stated over bare `LookupAccessList`s so it can be read
and checked without any circuit in scope. Everything about chips, tables and witness generation is
someone else's problem; here a *provider* is just "one access per demanded key, carrying that key's
recount", and the claim is that adding it to the consumer ledger cancels every key.

The two side conditions are exactly the two ways this can fail, and neither is hidden:

* **nonpositivity** — at a key it closes, the consumer side must not be net-*positive*. Consumers
  pull (negative) and providers push (positive); a net-positive consumer key means something already
  supplied that key, and `Int.toNat` would silently round the resulting negative demand to zero
  rather than fail. This hypothesis is what makes the `Int.toNat` in `providerRecount` faithful.
* **coverage** — every key with nonzero demand must actually be in the list. Omitting one leaves it
  unbalanced. Note the converse is *not* required: listing a zero-demand key is harmless, it just
  emits a zero-multiplicity row.

`closingKeys` below satisfies both conditions structurally for the keys it selects, which is what
makes this a closure rather than another premise.
-/


/-- The provider ledger closing `skeleton` over `keys`: one recounted access per key. -/
def closingAccesses (skeleton : LookupAccessList) (keys : List LookupKey) : LookupAccessList :=
  keys.map fun key => accessAt key (providerRecount skeleton key : ℤ)

@[simp] theorem closingAccesses_nil (skeleton : LookupAccessList) :
    closingAccesses skeleton [] = [] := rfl

theorem closingAccesses_cons (skeleton : LookupAccessList) (key : LookupKey)
    (keys : List LookupKey) :
    closingAccesses skeleton (key :: keys) =
      accessAt key (providerRecount skeleton key : ℤ) :: closingAccesses skeleton keys := rfl

/-- Off the key list, a closing ledger contributes nothing. -/
theorem multiplicitySum_closingAccesses_of_not_mem (skeleton : LookupAccessList)
    {keys : List LookupKey} {key : LookupKey} (hkey : key ∉ keys) :
    multiplicitySum (closingAccesses skeleton keys) key = 0 := by
  refine multiplicitySum_eq_zero_of_keyOf_ne fun a ha => ?_
  rw [closingAccesses, List.mem_map] at ha
  obtain ⟨k', hk'mem, rfl⟩ := ha
  rw [keyOf_accessAt]
  rintro rfl
  exact hkey hk'mem

/-- At a listed key, a closing ledger supplies exactly that key's recount — provided the list does
not name the key twice, which would double-supply it. -/
theorem multiplicitySum_closingAccesses (skeleton : LookupAccessList) {keys : List LookupKey}
    (hnodup : keys.Nodup) {key : LookupKey} (hkey : key ∈ keys) :
    multiplicitySum (closingAccesses skeleton keys) key =
      (providerRecount skeleton key : ℤ) := by
  induction keys with
  | nil => cases hkey
  | cons head tail ih =>
      rw [closingAccesses_cons, multiplicitySum_cons]
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hkey with rfl | hmem
      · rw [if_pos (keyOf_accessAt _ _)]
        rw [multiplicitySum_closingAccesses_of_not_mem skeleton hhead]
        simp
      · have hne : keyOf (accessAt head (providerRecount skeleton head : ℤ)) ≠ key := by
          rw [keyOf_accessAt]
          rintro rfl
          exact hhead hmem
        rw [if_neg hne, ih htail hmem, zero_add]

/-- **The closure balances.** Appending the closing ledger to the consumer skeleton zeroes every
key, given that the skeleton is non-positive at each listed key and that no key with nonzero demand
was left off the list. -/
theorem multiplicitySum_append_closingAccesses (skeleton : LookupAccessList)
    {keys : List LookupKey} (hnodup : keys.Nodup)
    (hnonpos : ∀ key ∈ keys, multiplicitySum skeleton key ≤ 0)
    (hcover : ∀ key, multiplicitySum skeleton key ≠ 0 → key ∈ keys) (key : LookupKey) :
    multiplicitySum (skeleton ++ closingAccesses skeleton keys) key = 0 := by
  rw [multiplicitySum_append]
  by_cases hkey : key ∈ keys
  · rw [multiplicitySum_closingAccesses skeleton hnodup hkey, providerRecount,
      Int.toNat_of_nonneg (neg_nonneg.mpr (hnonpos key hkey))]
    ring
  · rw [multiplicitySum_closingAccesses_of_not_mem skeleton hkey,
      not_not.mp (fun h => hkey (hcover key h)), add_zero]

/-! ### Choosing the keys, so the two side conditions stop being premises

`closingKeys` selects every key the consumers actually touch, on the buses a provider is allowed to
supply. Deduplication gives `Nodup` for free, and "selected from the skeleton's own keys" gives
coverage for free — the two hypotheses of `multiplicitySum_append_closingAccesses` become theorems
rather than things a caller must promise.

The `select` predicate is what keeps this honest about scope. Byte (including Range) and Program are
selectable because a provider supplies those unilaterally. State and Memory are not: their balance
is a clock telescope and a per-address touch chain, and no recount can produce them.
`multiplicitySum_closingAccesses_of_not_select` is the other half of that story — it says the
closure leaves the unselected buses completely alone, so adding providers cannot break a State or
Memory balance that held before.
-/

/-- Every key the skeleton touches on a selectable bus, without duplicates. -/
def closingKeys (skeleton : LookupAccessList) (select : LookupKey → Bool) : List LookupKey :=
  ((skeleton.map keyOf).filter select).dedup

theorem closingKeys_nodup (skeleton : LookupAccessList) (select : LookupKey → Bool) :
    (closingKeys skeleton select).Nodup := List.nodup_dedup _

theorem select_of_mem_closingKeys {skeleton : LookupAccessList} {select : LookupKey → Bool}
    {key : LookupKey} (hkey : key ∈ closingKeys skeleton select) : select key = true := by
  rw [closingKeys, List.mem_dedup, List.mem_filter] at hkey
  exact hkey.2

/-- Coverage, for free: a selectable key with nonzero demand is always chosen. -/
theorem mem_closingKeys_of_multiplicitySum_ne_zero (skeleton : LookupAccessList)
    (select : LookupKey → Bool) {key : LookupKey} (hsel : select key = true)
    (h : multiplicitySum skeleton key ≠ 0) : key ∈ closingKeys skeleton select := by
  rw [closingKeys, List.mem_dedup, List.mem_filter]
  refine ⟨?_, hsel⟩
  by_contra hmem
  exact h (multiplicitySum_eq_zero_of_keyOf_ne fun a ha hka => hmem (hka ▸ List.mem_map_of_mem ha))

/-- The closure never touches a bus it was not asked to supply. This is what makes it safe to add:
a State or Memory balance that held before still holds after. -/
theorem multiplicitySum_closingAccesses_of_not_select (skeleton : LookupAccessList)
    {select : LookupKey → Bool} {key : LookupKey} (hsel : select key = false) :
    multiplicitySum (closingAccesses skeleton (closingKeys skeleton select)) key = 0 :=
  multiplicitySum_closingAccesses_of_not_mem skeleton fun hkey => by
    rw [select_of_mem_closingKeys hkey] at hsel; exact Bool.noConfusion hsel

/-- **The provider closure balances every selectable key.** Only non-positivity of the consumer side
remains a hypothesis — and that is a real fact about the shard, not a bookkeeping choice: it says no
consumer key is already net-supplied. -/
theorem multiplicitySum_append_closing (skeleton : LookupAccessList) (select : LookupKey → Bool)
    (hnonpos : ∀ key ∈ closingKeys skeleton select, multiplicitySum skeleton key ≤ 0)
    {key : LookupKey} (hsel : select key = true) :
    multiplicitySum (skeleton ++ closingAccesses skeleton (closingKeys skeleton select)) key = 0 := by
  rw [multiplicitySum_append]
  by_cases hkey : key ∈ closingKeys skeleton select
  · rw [multiplicitySum_closingAccesses skeleton (closingKeys_nodup skeleton select) hkey,
      providerRecount, Int.toNat_of_nonneg (neg_nonneg.mpr (hnonpos key hkey))]
    ring
  · rw [multiplicitySum_closingAccesses_of_not_mem skeleton hkey,
      not_not.mp (fun h => hkey (mem_closingKeys_of_multiplicitySum_ne_zero skeleton select hsel h)),
      add_zero]


end LookupAccessList

end SP1Clean
