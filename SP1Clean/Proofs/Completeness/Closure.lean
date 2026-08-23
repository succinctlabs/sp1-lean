import SP1Clean.Model.CleanLedger
import SP1Clean.Proofs.Completeness.Assembly

/-! # The provider closure: recounting Byte/Range/Program demand from the consumers

`SupportedCoreTraceWitness` takes its provider occurrence lists as raw input fields, and
`Soundness/AIRCompleteness.lean`'s `Balanced` is a *hypothesis*: the assembled witness satisfies
the ensemble's constraint system, but nothing derives that its channels cancel. Every use so far
discharges balance by compiled evaluation on a fully concrete shard — which is only available in the
test library, and is why `SP1CleanTest/Audit/ActiveTraceNonVacuity.lean` spends roughly five hundred
lines on ledger plumbing for a single `JAL x0, 0` row and does not generalise to a symbolic trace.

This module is the first half of closing that gap. It does not invent an algorithm: the exact→native
transport already recounts provider multiplicities from a deliberately provider-free consumer ledger
and proves the result balances (`Faithful/Transport/PreprocessedProviders.lean`). What it recounts
over is `CoreAIR.Current.Row`, the extracted exact AIR. The same recount applies verbatim to a
`Table.build`-over-events trace, and that is what is defined here.

## Why no per-chip interaction list is needed

The obvious shape for "what do the consumers demand" is a symbolic per-chip list, and the tree has a
partial one (`exposedByteInteractions` and friends). It is not what this needs, and it would be the
expensive way to get it — for eight of the twenty-five chips those byte pulls descend from the
`CPUState` reader and the arithmetic operation subcircuits, so exposing them means extending each
chip's `exposedChannels_eq` lawfulness proof through those subcircuits.

`Faithful/Transport/Table.lean`'s `tableCleanAccesses_build` needs none of it. It folds
`component.operations.interactions` — every channel at once, and the *computable* `.interactions`
rather than the `noncomputable` per-channel `.interactionsWith` projection — into a
`LookupAccessList` whose entries already carry their `(kind, table, entry)` key. Demand is then a
question about that list, not about any chip.

## The acyclicity condition, and why the skeleton is defined by position

A recount is only well-founded if the providers being recounted are absent from the ledger they
recount against; otherwise a provider's multiplicity depends on itself. The twenty-four preprocessed
providers (six Byte opcode tables, all seventeen fixed Range widths, and Program) occupy positions
`25 .. 48` of `sp1Ensemble.tables`, so the skeleton is everything outside that window: the verifier
row, the twenty-five instruction tables, MemoryInit/MemoryFinalize, and both bumps. That mirrors
`Transport/CoreEnsemble.lean`'s `exactNativeSkeletonLedger` exactly.

Taking the window positionally rather than re-listing the tables is deliberate — the skeleton and
the assembled `tables` then cannot drift apart under a future reordering, and
`skeletonTables_eq_split` below is the `rfl` that says so.

**Scope.** This closes the *shape* of the demand side only. Byte (including Range) and Program are
the channels a recount can close, because a provider supplies them unilaterally. State and Memory
cannot be recounted: their balance is a clock telescope and a per-address touch chain respectively,
and they remain explicit hypotheses — the same split the exact transport lives with
(`ExactNativeGlobalContract.remainingIntegerBalance`).
-/

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

namespace SP1Clean.LookupAccessList

/-- The access a provider emits at `key` with multiplicity `mult`. -/
def accessAt (key : LookupKey) (mult : ℤ) : LookupAccess := (key.1, key.2.1, key.2.2, mult)

@[simp] theorem keyOf_accessAt (key : LookupKey) (mult : ℤ) : keyOf (accessAt key mult) = key := rfl

@[simp] theorem multOf_accessAt (key : LookupKey) (mult : ℤ) :
    multOf (accessAt key mult) = mult := rfl

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

end SP1Clean.LookupAccessList

namespace SP1Clean.Soundness

open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- The trace's own verifier row, as a built table. Definitionally the row Clean's ensemble
verifier checks — `Assembly.lean`'s `witness_verifierTable` is the bridge. -/
def skeletonVerifierTable : Table (ZMod p) :=
  Table.build (verifierComponent (p := p)) [trace.publicValues] trace.data trace.hint

/-- Every table that *consumes* preprocessed provider keys, and no table that supplies them: the
verifier row, the twenty-five instruction tables, and the four-table
MemoryInit/MemoryFinalize/MemoryBump/StateBump tail. -/
def skeletonTables : List (Table (ZMod p)) :=
  trace.skeletonVerifierTable ::
    (trace.tables.take instructionTableCount ++
      trace.tables.drop (instructionTableCount + preprocessedProviderTableCount))

/-- The skeleton really is the assembled table list with the preprocessed provider window removed:
the same `tables`, split at the same two positions. -/
theorem skeletonTables_eq_split :
    trace.skeletonTables =
      trace.skeletonVerifierTable ::
        (trace.tables.take instructionTableCount ++
          trace.tables.drop (instructionTableCount + preprocessedProviderTableCount)) :=
  rfl

/-- The literal Clean access ledger of the consumer side. Preprocessed providers are absent by
construction, so a multiplicity recounted against this cannot depend on itself. -/
def skeletonLedger : LookupAccessList :=
  tablesCleanAccesses trace.skeletonTables

@[simp] theorem skeletonLedger_eq :
    trace.skeletonLedger =
      tableCleanAccesses trace.skeletonVerifierTable ++
        tablesCleanAccesses
          (trace.tables.take instructionTableCount ++
            trace.tables.drop (instructionTableCount + preprocessedProviderTableCount)) := by
  simp only [skeletonLedger, skeletonTables, tablesCleanAccesses, List.flatMap_cons]

/-- How many times the shard's consumers ask for one provider key.

This is the multiplicity an honest provider row must carry at that key. It is
`LookupAccessList.providerRecount` — the same function the exact→native transport recounts with,
not a second copy of it. -/
def providerDemand (key : LookupAccessList.LookupKey) : ℕ :=
  LookupAccessList.providerRecount trace.skeletonLedger key

/-- A key no consumer touches is demanded zero times, so the closure may omit its row entirely
rather than emit a zero-multiplicity padding row. -/
theorem providerDemand_eq_zero_of_untouched {key : LookupAccessList.LookupKey}
    (h : LookupAccessList.multiplicitySum trace.skeletonLedger key = 0) :
    trace.providerDemand key = 0 :=
  LookupAccessList.providerRecount_eq_zero_of_balanced h

/-! ### The trace's own closure

Instantiating the ledger closure at this trace's consumer skeleton. `preprocessedKey` is the scope
decision made concrete: the Byte bus (which carries the seventeen fixed Range widths as well as the
six byte opcodes) and the Program bus are supplied by preprocessed provider tables, so a recount can
close them. State and Memory are not, and `closingAccesses_not_preprocessed` records that the
closure leaves them untouched rather than quietly perturbing them.
-/

/-- The buses a provider closure is allowed to supply. -/
def preprocessedKey (key : LookupAccessList.LookupKey) : Bool :=
  match key.1 with
  | .Byte | .Program => true
  | .Memory | .State => false

/-- The provider ledger this trace's consumers demand: one recounted access per touched
Byte/Program key. -/
def closingAccesses : LookupAccessList :=
  LookupAccessList.closingAccesses trace.skeletonLedger
    (LookupAccessList.closingKeys trace.skeletonLedger preprocessedKey)

/-- **Byte and Program balance, derived rather than assumed** — given only that no consumer key is
already net-supplied. This is the statement that replaces a per-shard evaluation of the whole
ledger. -/
theorem closingAccesses_balances
    (hnonpos : ∀ key ∈ LookupAccessList.closingKeys trace.skeletonLedger preprocessedKey,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0)
    {key : LookupAccessList.LookupKey} (hsel : preprocessedKey key = true) :
    LookupAccessList.multiplicitySum (trace.skeletonLedger ++ trace.closingAccesses) key = 0 :=
  LookupAccessList.multiplicitySum_append_closing trace.skeletonLedger preprocessedKey hnonpos hsel

/-- The closure contributes nothing on State or Memory, so a balance already established there is
undisturbed by adding providers. -/
theorem closingAccesses_not_preprocessed {key : LookupAccessList.LookupKey}
    (hsel : preprocessedKey key = false) :
    LookupAccessList.multiplicitySum trace.closingAccesses key = 0 :=
  LookupAccessList.multiplicitySum_closingAccesses_of_not_select trace.skeletonLedger hsel

/-- Concretely: State keys are outside the closure's remit. -/
theorem closingAccesses_state (key : LookupAccessList.LookupKey) (hkind : key.1 = .State) :
    LookupAccessList.multiplicitySum trace.closingAccesses key = 0 :=
  trace.closingAccesses_not_preprocessed (by simp [preprocessedKey, hkind])

/-- Concretely: Memory keys are outside the closure's remit. -/
theorem closingAccesses_memory (key : LookupAccessList.LookupKey) (hkind : key.1 = .Memory) :
    LookupAccessList.multiplicitySum trace.closingAccesses key = 0 :=
  trace.closingAccesses_not_preprocessed (by simp [preprocessedKey, hkind])

end SupportedCoreTraceWitness

end SP1Clean.Soundness
