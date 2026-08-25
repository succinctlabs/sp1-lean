import SP1Clean.Model.Semantics.AccessSchedule
import SP1Clean.Proofs.Completeness.Providers

/-!
# Canonical Memory-boundary histories

The completeness compiler produces Memory accesses chronologically, while the Memory boundary
tables and the hand-off proof are indexed by location.  This module is the field-free join between
those views.  Its input is one chronological list of `MemoryHistoryAccess` records.  Instruction
accesses and inserted `MemoryBump` refreshes use the same carrier: both pull one record and push its
successor.

From that stream we deterministically construct:

* the `eraseDups`-ordered inventory of touched `MemLoc`s;
* the complete filtered history at each location;
* exactly one active memory-init row (clock zero, first pulled value) and one active memory-finalize
  row (last pushed value and timestamp) per touched location; and
* the family of `LookupAccessList.IsHandoffChain`s consumed by
  `ChipLedger.memoryLedger_perm_handoff`.

Nothing here assumes channel balance or a finished `SupportedCoreTraceWitness`.  The only semantic
premise of the chain theorem is the honest chronological one: the first record at each location has
previous timestamp zero, and every later pull is exactly the preceding push.  A small adapter from
`AccessSchedule` makes the execution compiler and this boundary construction share the scheduler's
single access representation.
-/

namespace SP1Clean.TraceGen

open Circuit
open SP1Clean.Semantics
open SP1Clean.LookupAccessList

/-! ## The common chronological carrier -/

/-- One complete life-transition of a Memory-bus record.  `previous`/`current` are full timestamps;
`pulled`/`pushed` are the corresponding 64-bit contents. -/
structure MemoryHistoryAccess where
  loc : MemLoc
  pulled : BitVec 64
  pushed : BitVec 64
  previous : ℕ
  current : ℕ
deriving DecidableEq

namespace MemoryHistoryAccess

/-- The instruction-access half of a scheduled role. -/
def ofStamped (base : ℕ) (stamped : StampedTouch) : MemoryHistoryAccess where
  loc := stamped.touch.loc
  pulled := stamped.touch.pulled
  pushed := stamped.touch.pushed
  previous := stamped.previous
  current := stamped.current base

/-- A MemoryBump is the same value-preserving record transition, at a register location.  The
well-formedness theorem of the scheduler proves that `addr < 32`; `BitVec.ofNat` keeps this adapter
total before that proof is applied. -/
def ofMemoryBump (event : MemoryBumpEvent) : MemoryHistoryAccess where
  loc := .reg (BitVec.ofNat 5 event.addr)
  pulled := BitVec.ofNat 64 event.value
  pushed := BitVec.ofNat 64 event.value
  previous := event.prevTs
  current := event.currTs

/-- Expand one scheduled role in actual time order: an optional refresh first, then the instruction
touch whose displaced timestamp observes that refresh. -/
def ofScheduledAccess (base : ℕ) (access : ScheduledAccess) : List MemoryHistoryAccess :=
  access.memoryBump?.toList.map ofMemoryBump ++ [ofStamped base access.stamped]

/-- The chronological Memory stream represented by one canonical access schedule. -/
def ofAccessSchedule (base : ℕ) (schedule : AccessSchedule) : List MemoryHistoryAccess :=
  schedule.accesses.flatMap (ofScheduledAccess base)

@[simp] theorem ofScheduledAccess_noBump {base : ℕ} {access : ScheduledAccess}
    (noBump : access.memoryBump? = none) :
    ofScheduledAccess base access = [ofStamped base access.stamped] := by
  simp [ofScheduledAccess, noBump]

/-- The adapter's load-bearing order equation: a refresh is the immediate predecessor of the
instruction touch which consumes its refreshed record. -/
@[simp] theorem ofScheduledAccess_someBump {base : ℕ} {access : ScheduledAccess}
    {event : MemoryBumpEvent} (hasBump : access.memoryBump? = some event) :
    ofScheduledAccess base access =
      [ofMemoryBump event, ofStamped base access.stamped] := by
  simp [ofScheduledAccess, hasBump]

/-- Peeling the one chronological stream preserves the schedule's role order and expands each
optional bump before, never after, its instruction access. -/
theorem ofAccessSchedule_cons (base : ℕ) (access : ScheduledAccess)
    (rest : List ScheduledAccess) (outgoing : AccessFrontier) :
    ofAccessSchedule base ⟨access :: rest, outgoing⟩ =
      ofScheduledAccess base access ++ ofAccessSchedule base ⟨rest, outgoing⟩ := by
  simp [ofAccessSchedule]

/-- Two consecutive records at one location form a genuine hand-off. -/
def Continues (earlier later : MemoryHistoryAccess) : Prop :=
  later.loc = earlier.loc ∧
    later.previous = earlier.current ∧
    later.pulled = earlier.pushed

/-- The canonical byte address used in the three address limbs of the Memory channel.  Register
records use their index; RAM records use the aligned eight-byte cell base. -/
def busAddress : MemLoc → ℕ
  | .reg index => index.toNat
  | .ram cell => cell.toNat * 8

/-- The Memory bus carries only 48 address bits and reserves `0..31` for register records.  A RAM
location is canonically representable exactly when its aligned base lies in the remaining 48-bit
address space. -/
def CanonicalAddress : MemLoc → Prop
  | .reg _ => True
  | .ram cell => 32 ≤ cell.toNat * 8 ∧ cell.toNat * 8 < 2 ^ 48

theorem busAddress_lt_two_pow_48 {loc : MemLoc}
    (canonical : CanonicalAddress loc) : busAddress loc < 2 ^ 48 := by
  cases loc with
  | reg index => exact lt_trans index.isLt (by norm_num)
  | ram cell =>
      simp only [CanonicalAddress] at canonical
      exact canonical.2

/-- Canonical register/RAM address encoding is injective.  The lower-bound clause is load-bearing:
without it, aligned RAM addresses `0,8,16,24` collide with the reserved register shapes. -/
theorem busAddress_injective_of_canonical {left right : MemLoc}
    (leftCanonical : CanonicalAddress left) (rightCanonical : CanonicalAddress right)
    (addressEq : busAddress left = busAddress right) : left = right := by
  cases left with
  | reg leftIndex =>
      cases right with
      | reg rightIndex =>
          simp only [busAddress] at addressEq
          congr 1
          exact BitVec.eq_of_toNat_eq addressEq
      | ram rightCell =>
          exfalso
          have leftLt : leftIndex.toNat < 32 := leftIndex.isLt
          simp only [CanonicalAddress] at rightCanonical
          simp only [busAddress] at addressEq
          omega
  | ram leftCell =>
      cases right with
      | reg rightIndex =>
          exfalso
          have rightLt : rightIndex.toNat < 32 := rightIndex.isLt
          simp only [CanonicalAddress] at leftCanonical
          simp only [busAddress] at addressEq
          omega
      | ram rightCell =>
          simp only [busAddress] at addressEq
          congr 1
          apply BitVec.eq_of_toNat_eq
          omega

/-- The record pulled by this access. -/
def pulledEntry (access : MemoryHistoryAccess) : MemRecordEntry where
  addr := busAddress access.loc
  value := access.pulled.toNat
  clk := access.previous
  multiplicity := true

/-- The record pushed by this access. -/
def pushedEntry (access : MemoryHistoryAccess) : MemRecordEntry where
  addr := busAddress access.loc
  value := access.pushed.toNat
  clk := access.current
  multiplicity := true

/-- Turn a boundary entry into exactly the key emitted on Clean's `SP1Memory` channel.  Keeping this
definition in terms of `toMemoryMsg` makes its clock/address/value limbing definitionally identical
to the provider builders. -/
def entryKey {p : ℕ} [NeZero p] (entry : MemRecordEntry) : LookupKey :=
  (InteractionKind.Memory, "SP1Memory",
    (toElements (entry.toMemoryMsg (p := p))).toList.map ZMod.val)

def pulledKey {p : ℕ} [NeZero p] (access : MemoryHistoryAccess) : LookupKey :=
  entryKey (p := p) access.pulledEntry

def pushedKey {p : ℕ} [NeZero p] (access : MemoryHistoryAccess) : LookupKey :=
  entryKey (p := p) access.pushedEntry

/-- One access's pull/push pair in the generic hand-off vocabulary. -/
def link {p : ℕ} [NeZero p] (access : MemoryHistoryAccess) : LookupKey × LookupKey :=
  (access.pulledKey (p := p), access.pushedKey (p := p))

theorem pulledKey_eq_pushedKey_of_continues {p : ℕ} [NeZero p]
    {earlier later : MemoryHistoryAccess} (continues : earlier.Continues later) :
    later.pulledKey (p := p) = earlier.pushedKey (p := p) := by
  rcases continues with ⟨locEq, timeEq, valueEq⟩
  apply congrArg (entryKey (p := p))
  simp_all [pulledEntry, pushedEntry, busAddress]

end MemoryHistoryAccess

/-! ## Deterministic per-location histories -/

/-- One location's chronological subsequence. -/
def memoryHistoryAt (stream : List MemoryHistoryAccess) (loc : MemLoc) :
    List MemoryHistoryAccess :=
  stream.filter fun access => access.loc = loc

/-- Touched locations, in first-occurrence order. -/
def touchedMemoryLocations (stream : List MemoryHistoryAccess) : List MemLoc :=
  (stream.map MemoryHistoryAccess.loc).dedup

@[simp] theorem mem_touchedMemoryLocations {stream : List MemoryHistoryAccess} {loc : MemLoc} :
    loc ∈ touchedMemoryLocations stream ↔ ∃ access ∈ stream, access.loc = loc := by
  simp [touchedMemoryLocations]

theorem mem_memoryHistoryAt {stream : List MemoryHistoryAccess} {access : MemoryHistoryAccess}
    (member : access ∈ stream) : access ∈ memoryHistoryAt stream access.loc := by
  simp [memoryHistoryAt, member]

theorem memoryHistoryAt_ne_nil_of_mem {stream : List MemoryHistoryAccess} {loc : MemLoc}
    (member : loc ∈ touchedMemoryLocations stream) : memoryHistoryAt stream loc ≠ [] := by
  rcases mem_touchedMemoryLocations.mp member with ⟨access, accessMem, rfl⟩
  exact fun empty => by
    have := mem_memoryHistoryAt accessMem
    rw [empty] at this
    simp at this

/-- A nonempty per-location history.  The proof is retained so boundary extraction needs no default
record and cannot silently invent an untouched location. -/
structure MemoryLocationHistory where
  loc : MemLoc
  accesses : List MemoryHistoryAccess
  nonempty : accesses ≠ []

namespace MemoryLocationHistory

/-- First record transition at this location. -/
def first (history : MemoryLocationHistory) : MemoryHistoryAccess :=
  history.accesses.head history.nonempty

/-- Last record transition at this location. -/
def last (history : MemoryLocationHistory) : MemoryHistoryAccess :=
  history.accesses.getLast history.nonempty

/-- The active genesis row: timestamp zero and the first value pulled at this location. -/
def initialEntry (history : MemoryLocationHistory) : MemRecordEntry where
  addr := MemoryHistoryAccess.busAddress history.loc
  value := history.first.pulled.toNat
  clk := 0
  multiplicity := true

/-- The active final row: the last pushed value at its actual final record timestamp. -/
def finalEntry (history : MemoryLocationHistory) : MemRecordEntry where
  addr := MemoryHistoryAccess.busAddress history.loc
  value := history.last.pushed.toNat
  clk := history.last.current
  multiplicity := true

theorem initialEntry_wellFormed (history : MemoryLocationHistory) :
    history.initialEntry.WellFormedInit := rfl

end MemoryLocationHistory

/-- The canonical family of nonempty histories. -/
def memoryLocationHistories (stream : List MemoryHistoryAccess) :
    List MemoryLocationHistory :=
  (touchedMemoryLocations stream).attach.map fun item =>
    { loc := item.1
      accesses := memoryHistoryAt stream item.1
      nonempty := memoryHistoryAt_ne_nil_of_mem item.2 }

/-- Every access in a canonical history has exactly the location by which that history was
filtered.  Thus callers never need to repeat the inventory's structural proof. -/
theorem memoryLocationHistory_access_loc {stream : List MemoryHistoryAccess}
    {history : MemoryLocationHistory} (historyMem : history ∈ memoryLocationHistories stream)
    {access : MemoryHistoryAccess} (accessMem : access ∈ history.accesses) :
    access.loc = history.loc := by
  rcases List.mem_map.mp historyMem with ⟨item, _, rfl⟩
  exact of_decide_eq_true (List.mem_filter.mp accessMem).2

@[simp] theorem memoryLocationHistories_map_loc (stream : List MemoryHistoryAccess) :
    (memoryLocationHistories stream).map MemoryLocationHistory.loc =
      touchedMemoryLocations stream := by
  simp only [memoryLocationHistories, List.map_map]
  simpa [Function.comp_def] using
    (List.attach_map_subtype_val (touchedMemoryLocations stream))

theorem memoryLocationHistories_nodup (stream : List MemoryHistoryAccess) :
    ((memoryLocationHistories stream).map MemoryLocationHistory.loc).Nodup := by
  rw [memoryLocationHistories_map_loc]
  exact List.nodup_dedup _

private theorem count_memoryHistoryAt (stream : List MemoryHistoryAccess) (loc : MemLoc)
    (target : MemoryHistoryAccess) :
    (memoryHistoryAt stream loc).count target =
      if target.loc = loc then stream.count target else 0 := by
  by_cases accepted : target.loc = loc
  · rw [if_pos accepted]
    exact List.count_filter (by simp [accepted])
  · rw [if_neg accepted, List.count_eq_zero_of_not_mem]
    simp [memoryHistoryAt, accepted]

private theorem sum_map_ite_of_nodup {loc : MemLoc} (count : ℕ) :
    ∀ locations : List MemLoc, locations.Nodup →
      (locations.map fun candidate => if loc = candidate then count else 0).sum =
        if loc ∈ locations then count else 0 := by
  intro locations nodup
  induction locations with
  | nil => simp
  | cons head tail ih =>
      have headNotMem := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases same : loc = head
      · subst head
        simp [headNotMem, ih tailNodup]
      · simp [same, ih tailNodup]

/-- Regrouping the chronological stream by its deterministic touched-location inventory loses and
duplicates no access.  This is the field-free permutation seam later used to regroup physical
instruction/MemoryBump rows into location chains. -/
theorem memoryStream_perm_grouped (stream : List MemoryHistoryAccess) :
    stream.Perm ((touchedMemoryLocations stream).flatMap (memoryHistoryAt stream)) := by
  apply List.perm_iff_count.mpr
  intro target
  rw [List.count_flatMap]
  change stream.count target =
    ((touchedMemoryLocations stream).map fun loc =>
      (memoryHistoryAt stream loc).count target).sum
  simp_rw [count_memoryHistoryAt stream]
  have collapse := sum_map_ite_of_nodup (loc := target.loc) (stream.count target)
    (touchedMemoryLocations stream) (by
      simpa only [touchedMemoryLocations] using
        List.nodup_dedup (stream.map MemoryHistoryAccess.loc))
  rw [collapse]
  by_cases touched : target.loc ∈ touchedMemoryLocations stream
  · simp [touched]
  · have targetNotMem : target ∉ stream := by
      intro targetMem
      exact touched (mem_touchedMemoryLocations.mpr ⟨target, targetMem, rfl⟩)
    simp [touched, List.count_eq_zero_of_not_mem targetNotMem]

/-- Same regrouping through the proof-carrying `MemoryLocationHistory` carrier. -/
theorem memoryStream_perm_locationHistories (stream : List MemoryHistoryAccess) :
    stream.Perm ((memoryLocationHistories stream).flatMap MemoryLocationHistory.accesses) := by
  refine (memoryStream_perm_grouped stream).trans ?_
  simp only [memoryLocationHistories, List.flatMap_map]
  have locationsPerm : (touchedMemoryLocations stream).Perm
      ((touchedMemoryLocations stream).attach.map Subtype.val) :=
    (List.attach_map_subtype_val (touchedMemoryLocations stream)).symm ▸ List.Perm.refl _
  have rightEq :
      ((touchedMemoryLocations stream).attach.map Subtype.val).flatMap
          (memoryHistoryAt stream) =
        (touchedMemoryLocations stream).attach.flatMap fun item =>
          memoryHistoryAt stream item.1 := by
    rw [List.flatMap_map]
  rw [← rightEq]
  exact List.Perm.flatMap_right (memoryHistoryAt stream) locationsPerm

/-- There is exactly one history for every touched location. -/
theorem memoryLocationHistories_count_loc (stream : List MemoryHistoryAccess) (loc : MemLoc) :
    ((memoryLocationHistories stream).map MemoryLocationHistory.loc).count loc =
      if loc ∈ touchedMemoryLocations stream then 1 else 0 := by
  rw [memoryLocationHistories_map_loc]
  simpa [touchedMemoryLocations] using
    (List.count_dedup (stream.map MemoryHistoryAccess.loc) loc)

/-! ## Boundary inventories -/

/-- One active memory-init row per touched location. -/
def memoryInitialEntries (stream : List MemoryHistoryAccess) : List MemRecordEntry :=
  (memoryLocationHistories stream).map MemoryLocationHistory.initialEntry

/-- One active memory-finalize row per touched location. -/
def memoryFinalEntries (stream : List MemoryHistoryAccess) : List MemRecordEntry :=
  (memoryLocationHistories stream).map MemoryLocationHistory.finalEntry

theorem memoryInitialEntries_wellFormed (stream : List MemoryHistoryAccess) :
    ∀ entry ∈ memoryInitialEntries stream, entry.WellFormedInit := by
  intro entry member
  rcases List.mem_map.mp member with ⟨history, _, rfl⟩
  exact history.initialEntry_wellFormed

@[simp] theorem memoryInitialEntries_length (stream : List MemoryHistoryAccess) :
    (memoryInitialEntries stream).length = (touchedMemoryLocations stream).length := by
  simp [memoryInitialEntries, memoryLocationHistories]

@[simp] theorem memoryFinalEntries_length (stream : List MemoryHistoryAccess) :
    (memoryFinalEntries stream).length = (touchedMemoryLocations stream).length := by
  simp [memoryFinalEntries, memoryLocationHistories]

theorem memoryInitialEntries_addresses (stream : List MemoryHistoryAccess) :
    (memoryInitialEntries stream).map MemRecordEntry.addr =
      (touchedMemoryLocations stream).map MemoryHistoryAccess.busAddress := by
  simp only [memoryInitialEntries, memoryLocationHistories, List.map_map]
  change (touchedMemoryLocations stream).attach.map
      (fun item => MemoryHistoryAccess.busAddress item.1) =
    (touchedMemoryLocations stream).map MemoryHistoryAccess.busAddress
  have mapped := congrArg (List.map MemoryHistoryAccess.busAddress)
    (List.attach_map_subtype_val (touchedMemoryLocations stream))
  rw [List.map_map] at mapped
  exact mapped

theorem memoryFinalEntries_addresses (stream : List MemoryHistoryAccess) :
    (memoryFinalEntries stream).map MemRecordEntry.addr =
      (touchedMemoryLocations stream).map MemoryHistoryAccess.busAddress := by
  simp only [memoryFinalEntries, memoryLocationHistories, List.map_map]
  change (touchedMemoryLocations stream).attach.map
      (fun item => MemoryHistoryAccess.busAddress item.1) =
    (touchedMemoryLocations stream).map MemoryHistoryAccess.busAddress
  have mapped := congrArg (List.map MemoryHistoryAccess.busAddress)
    (List.attach_map_subtype_val (touchedMemoryLocations stream))
  rw [List.map_map] at mapped
  exact mapped

/-- Every access uses the noncolliding canonical register/RAM address image. -/
def MemoryAddressesCanonical (stream : List MemoryHistoryAccess) : Prop :=
  ∀ access ∈ stream, MemoryHistoryAccess.CanonicalAddress access.loc

theorem canonical_of_mem_touched {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream) {loc : MemLoc}
    (member : loc ∈ touchedMemoryLocations stream) :
    MemoryHistoryAccess.CanonicalAddress loc := by
  rcases mem_touchedMemoryLocations.mp member with ⟨access, accessMem, rfl⟩
  exact canonical access accessMem

/-- Canonical boundary rows have no duplicate addresses, so both provider inventories are unique at
the exact key granularity used by the Memory-boundary soundness assumptions. -/
theorem memoryInitialEntries_addresses_nodup {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream) :
    ((memoryInitialEntries stream).map MemRecordEntry.addr).Nodup := by
  rw [memoryInitialEntries_addresses]
  apply List.Nodup.map_on _ (List.nodup_dedup _)
  intro left leftMem right rightMem addressEq
  exact MemoryHistoryAccess.busAddress_injective_of_canonical
    (canonical_of_mem_touched canonical leftMem)
    (canonical_of_mem_touched canonical rightMem) addressEq

theorem memoryFinalEntries_addresses_nodup {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream) :
    ((memoryFinalEntries stream).map MemRecordEntry.addr).Nodup := by
  rw [memoryFinalEntries_addresses]
  apply List.Nodup.map_on _ (List.nodup_dedup _)
  intro left leftMem right rightMem addressEq
  exact MemoryHistoryAccess.busAddress_injective_of_canonical
    (canonical_of_mem_touched canonical leftMem)
    (canonical_of_mem_touched canonical rightMem) addressEq

/-! ## Per-location hand-off chains -/

/-- A location history begins at timestamp zero and every later pull consumes exactly the preceding
push.  `List.IsChain` is adjacency, not all-pairs ordering.  `located` makes the boundary address
explicit; canonical histories obtain it directly from their defining filter. -/
structure MemoryLocationHistory.IsRecordChain (history : MemoryLocationHistory) : Prop where
  genesis : history.first.previous = 0
  adjacent : List.IsChain MemoryHistoryAccess.Continues history.accesses
  located : ∀ access ∈ history.accesses, access.loc = history.loc

/-- The chain descriptor consumed by `LookupAccessList.multiChainLedger_perm_handoff`. -/
def MemoryLocationHistory.handoffChain {p : ℕ} [NeZero p]
    (history : MemoryLocationHistory) : LookupKey × List (LookupKey × LookupKey) × LookupKey :=
  (MemoryHistoryAccess.entryKey (p := p) history.initialEntry,
    history.accesses.map (MemoryHistoryAccess.link (p := p)),
    MemoryHistoryAccess.entryKey (p := p) history.finalEntry)

/-- The full deterministic family of per-location Memory chains. -/
def memoryHandoffChains {p : ℕ} [NeZero p] (stream : List MemoryHistoryAccess) :
    List (LookupKey × List (LookupKey × LookupKey) × LookupKey) :=
  (memoryLocationHistories stream).map (MemoryLocationHistory.handoffChain (p := p))

private theorem isHandoffChain_of_accesses {p : ℕ} [NeZero p] :
    ∀ (first : MemoryHistoryAccess) (rest : List MemoryHistoryAccess),
      List.IsChain MemoryHistoryAccess.Continues (first :: rest) →
      IsHandoffChain (first.pulledKey (p := p))
        ((first :: rest).map (MemoryHistoryAccess.link (p := p)))
        (MemoryHistoryAccess.pushedKey (p := p) ((first :: rest).getLast (by simp))) := by
  intro first rest
  induction rest generalizing first with
  | nil =>
      intro _
      change first.pulledKey (p := p) = first.pulledKey (p := p) ∧
        first.pushedKey (p := p) = first.pushedKey (p := p)
      exact ⟨rfl, rfl⟩
  | cons next rest ih =>
      intro chain
      have headContinues : first.Continues next := (List.isChain_cons_cons.mp chain).1
      have tailChain : List.IsChain MemoryHistoryAccess.Continues (next :: rest) :=
        (List.isChain_cons_cons.mp chain).2
      change first.pulledKey (p := p) = first.pulledKey (p := p) ∧
        IsHandoffChain (first.pushedKey (p := p))
          ((next :: rest).map (MemoryHistoryAccess.link (p := p)))
          (MemoryHistoryAccess.pushedKey (p := p) ((first :: next :: rest).getLast (by simp)))
      refine ⟨rfl, ?_⟩
      rw [← MemoryHistoryAccess.pulledKey_eq_pushedKey_of_continues headContinues]
      simpa using ih next tailChain

theorem MemoryLocationHistory.isHandoffChain {p : ℕ} [NeZero p]
    (history : MemoryLocationHistory) (recordChain : history.IsRecordChain) :
    IsHandoffChain (history.handoffChain (p := p)).1
      (history.handoffChain (p := p)).2.1 (history.handoffChain (p := p)).2.2 := by
  rcases accessEq : history.accesses with _ | ⟨first, rest⟩
  · exact False.elim (history.nonempty accessEq)
  · have firstEq : history.first = first := by
      simp [MemoryLocationHistory.first, accessEq]
    have lastEq : history.last = (first :: rest).getLast (by simp) := by
      simp [MemoryLocationHistory.last, accessEq]
    have initialKeyEq : MemoryHistoryAccess.entryKey (p := p) history.initialEntry =
        first.pulledKey (p := p) := by
      apply congrArg (MemoryHistoryAccess.entryKey (p := p))
      have firstMem : first ∈ history.accesses := by rw [accessEq]; simp
      have firstLoc := recordChain.located first firstMem
      have firstPrevious : 0 = first.previous := by
        rw [← firstEq]
        exact recordChain.genesis.symm
      simp [MemoryLocationHistory.initialEntry, MemoryHistoryAccess.pulledEntry,
        firstEq, firstPrevious, firstLoc]
    have finalKeyEq : MemoryHistoryAccess.entryKey (p := p) history.finalEntry =
        ((first :: rest).getLast (by simp)).pushedKey (p := p) := by
      apply congrArg (MemoryHistoryAccess.entryKey (p := p))
      have lastMem : history.last ∈ history.accesses := by
        exact List.getLast_mem history.nonempty
      have lastLoc := recordChain.located history.last lastMem
      have finalLoc : ((first :: rest).getLast (by simp)).loc = history.loc := by
        rw [← lastEq]
        exact lastLoc
      simp [MemoryLocationHistory.finalEntry, MemoryHistoryAccess.pushedEntry, lastEq, finalLoc]
    rw [MemoryLocationHistory.handoffChain, initialKeyEq, finalKeyEq, accessEq]
    exact isHandoffChain_of_accesses first rest (by simpa [accessEq] using recordChain.adjacent)

/-- The only global history premise needed by the Memory hand-off construction. -/
def MemoryRecordChains (stream : List MemoryHistoryAccess) : Prop :=
  ∀ history ∈ memoryLocationHistories stream, history.IsRecordChain

/-- The actual semantic coupling obligation: genesis timestamp plus adjacent record agreement.
Location agreement is not included because the deterministic grouping proves it. -/
def MemoryRecordChronology (stream : List MemoryHistoryAccess) : Prop :=
  ∀ history ∈ memoryLocationHistories stream,
    history.first.previous = 0 ∧
      List.IsChain MemoryHistoryAccess.Continues history.accesses

theorem memoryRecordChains_of_chronology {stream : List MemoryHistoryAccess}
    (chronology : MemoryRecordChronology stream) : MemoryRecordChains stream := by
  intro history historyMem
  exact
    { genesis := (chronology history historyMem).1
      adjacent := (chronology history historyMem).2
      located := fun _ accessMem =>
        memoryLocationHistory_access_loc historyMem accessMem }

theorem memoryHandoffChains_isHandoffChain {p : ℕ} [NeZero p]
    {stream : List MemoryHistoryAccess} (recordChains : MemoryRecordChains stream) :
    ∀ chain ∈ memoryHandoffChains (p := p) stream,
      IsHandoffChain chain.1 chain.2.1 chain.2.2 := by
  intro chain member
  rcases List.mem_map.mp member with ⟨history, historyMem, rfl⟩
  exact history.isHandoffChain (p := p) (recordChains history historyMem)

/-- The canonical family already has the precise generic shape required by
`ChipLedger.memoryLedger_perm_handoff`; no balance assumption enters this proof. -/
theorem memoryChainsLedger_perm_handoff {p : ℕ} [NeZero p]
    {stream : List MemoryHistoryAccess} (recordChains : MemoryRecordChains stream) :
    ((memoryHandoffChains (p := p) stream).flatMap chainLedger).Perm
      (handoff ((memoryHandoffChains (p := p) stream).flatMap chainTokens)) :=
  multiChainLedger_perm_handoff _ (memoryHandoffChains_isHandoffChain recordChains)

end SP1Clean.TraceGen
