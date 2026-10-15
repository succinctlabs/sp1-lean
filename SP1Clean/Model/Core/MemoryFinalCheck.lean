import SP1Clean.Model.Core.MemorySnapshot

/-! # Finite comparison against a complete outgoing memory snapshot

Every final record must have the advertised target value. Everywhere without a record, the target
must retain the source value. The check examines all registers and the sparse byte supports of both
snapshots, so a changed untouched byte cannot escape by being omitted from the final inventory.
It distinguishes low RAM from register locations and ignores obsolete sparse-history entries.

This is executable boundary data validation, independent of execution and of the AIR field.
The enclosing AIR must derive the check from its fixed lookups and complete final-record ledger;
the check is not an additional semantic conjunct in the AIR statement.
-/

namespace SP1Clean.Model.Core.MemorySnapshot

open Semantics

/-- Check advertised final values and the complete complement of the finalized footprint. -/
def checkFinal (source target : MemorySnapshot) (records : List (MemLoc × BitVec 64)) : Bool :=
  records.all (fun record => target.read record.1 == record.2) &&
    (List.ofFn fun index : Fin 32 => BitVec.ofNat 5 index.val).all (fun index =>
      if (records.map Prod.fst).contains (.reg index) then true
      else source.read (.reg index) == target.read (.reg index)) &&
    source.memory.agreesOn target.memory (fun address => decide (address < 2 ^ 48) &&
      !((records.map Prod.fst).contains (.ram (BitVec.ofNat 61 (address / 8)))))

private theorem byte_cell (cell : RamCell) (index : Fin 8) :
    BitVec.ofNat 61 ((cell.toNat * 8 + index.val) / 8) = cell := by
  have quotient : (cell.toNat * 8 + index.val) / 8 = cell.toNat := by have := index.isLt; omega
  rw [quotient, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The complete finite change inventory, computed from both boundaries. Register locations
remain distinct from low RAM; obsolete updates and out-of-window entries add no changes. -/
def changes (source target : MemorySnapshot) : List MemLoc :=
  (((List.ofFn fun index : Fin 32 => MemLoc.reg (BitVec.ofNat 5 index.val)) ++
      ((source.memory.entries ++ target.memory.entries).filter (fun entry => decide (entry.1 < 2 ^ 48))).map
        (fun entry => MemLoc.ram (BitVec.ofNat 61 (entry.1 / 8)))).filter
    (fun loc => decide (source.read loc ≠ target.read loc))).dedup

/-- Every native location that changes occurs, even when no execution row lists it. -/
theorem mem_changes_iff (source target : MemorySnapshot) (loc : MemLoc) :
    loc ∈ source.changes target ↔ loc.busAddress < 2 ^ 48 ∧ source.read loc ≠ target.read loc := by
  simp only [changes, List.mem_dedup, List.mem_filter, decide_eq_true_eq, List.mem_append,
    List.mem_map, List.mem_ofFn]
  constructor
  · rintro ⟨(⟨index, rfl⟩ | ⟨entry, ⟨member, bound⟩, rfl⟩), different⟩
    · exact ⟨by have := index.isLt; simp only [MemLoc.busAddress, BitVec.toNat_ofNat]; omega, different⟩
    · refine ⟨?_, different⟩
      simp only [MemLoc.busAddress, BitVec.toNat_ofNat]
      omega
  · rintro ⟨bound, different⟩
    refine ⟨?_, different⟩
    cases loc with
    | reg index =>
        exact Or.inl ⟨⟨index.toNat, index.isLt⟩, by simp⟩
    | ram cell =>
        apply Or.inr
        by_contra absent
        apply different
        apply congrArg Word.bytesValue
        apply Vector.ext
        intro index small
        have byteBound : cell.toNat * 8 + index < 2 ^ 48 := by
          change cell.toNat * 8 < 2 ^ 48 at bound
          omega
        have noEntry : ∀ entry ∈ source.memory.entries ++ target.memory.entries,
            entry.1 ≠ cell.toNat * 8 + index := by
          intro entry member equal
          apply absent
          refine ⟨entry, ⟨List.mem_append.mp member, ?_⟩, ?_⟩
          · simpa only [equal] using byteBound
          · rw [equal, byte_cell cell ⟨index, small⟩]
        simp only [ByteMemory.wordBytes, Vector.getElem_ofFn]
        rw [source.memory.read_eq_zero_of_absent _ (fun entry member =>
          noEntry entry (List.mem_append_left _ member)),
          target.memory.read_eq_zero_of_absent _ (fun entry member =>
            noEntry entry (List.mem_append_right _ member))]

theorem changes_nodup (source target : MemorySnapshot) : (source.changes target).Nodup :=
  List.nodup_dedup _

/-- The executable check means exact final values and preservation at every unlisted native
location. Neither touched-location coverage nor an absent-key convention is assumed. -/
theorem checkFinal_iff (source target : MemorySnapshot) (records : List (MemLoc × BitVec 64)) :
    source.checkFinal target records = true ↔
      (∀ record ∈ records, target.read record.1 = record.2) ∧
      ∀ loc, loc.busAddress < 2 ^ 48 → loc ∉ records.map Prod.fst →
        source.read loc = target.read loc := by
  simp only [checkFinal, Bool.and_eq_true, List.all_eq_true, ByteMemory.agreesOn_iff]
  constructor
  · rintro ⟨⟨values, registers⟩, memory⟩
    refine ⟨fun record member => beq_iff_eq.mp (values record member), ?_⟩
    intro loc bound absent
    cases loc with
    | reg index =>
        have member : index ∈ (List.ofFn fun index : Fin 32 => BitVec.ofNat 5 index.val) := by
          apply List.mem_ofFn.mpr
          exact ⟨⟨index.toNat, index.isLt⟩, by simp⟩
        simpa only [List.contains_eq_mem, decide_eq_false_iff_not.mpr absent,
          Bool.false_eq_true, ↓reduceIte, beq_iff_eq] using registers index member
    | ram cell =>
        apply congrArg Word.bytesValue
        apply Vector.ext
        intro index small
        have addressBound : cell.toNat * 8 + index < 2 ^ 48 := by
          change cell.toNat * 8 < 2 ^ 48 at bound
          omega
        simp only [ByteMemory.wordBytes, Vector.getElem_ofFn]
        exact memory (cell.toNat * 8 + index) (by
          refine ⟨decide_eq_true addressBound, ?_⟩
          simp only [byte_cell cell ⟨index, small⟩, List.contains_eq_mem,
            decide_eq_false_iff_not.mpr absent, Bool.not_false])
  · rintro ⟨values, frame⟩
    refine ⟨⟨fun record member => beq_iff_eq.mpr (values record member), ?_⟩, ?_⟩
    · intro index _
      split
      · rfl
      next absent =>
        apply beq_iff_eq.mpr
        exact frame (.reg index) (by have := index.isLt; change index.toNat < 2 ^ 48; omega)
          (by simpa only [List.contains_eq_mem, decide_eq_true_eq] using absent)
    · intro address selected
      have facts : address < 2 ^ 48 ∧
          MemLoc.ram (BitVec.ofNat 61 (address / 8)) ∉ records.map Prod.fst := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          List.contains_eq_mem, decide_eq_false_iff_not] using selected
      have cellNat : (BitVec.ofNat 61 (address / 8)).toNat = address / 8 :=
        Nat.mod_eq_of_lt (by omega)
      have equal := frame (.ram (BitVec.ofNat 61 (address / 8)))
        (by simp only [MemLoc.busAddress, cellNat]; omega) facts.2
      have bytes := congrArg (fun word : BitVec 64 => word.extractLsb' (8 * (address % 8)) 8) equal
      simp only [read, cellNat, ByteMemory.readWord_byte _ _ ⟨address % 8, Nat.mod_lt _ (by decide)⟩] at bytes
      rw [show address / 8 * 8 + address % 8 = address by omega] at bytes
      exact bytes

/-- Fixed target-value checks and coverage of the computed change inventory suffice for the
complete endpoint check. This is the finite accounting obligation of the native boundary. -/
theorem checkFinal_iff_changes (source target : MemorySnapshot) (records : List (MemLoc × BitVec 64)) :
    source.checkFinal target records = true ↔
      (∀ record ∈ records, target.read record.1 = record.2) ∧
        source.changes target ⊆ records.map Prod.fst := by
  rw [checkFinal_iff]
  constructor
  · rintro ⟨values, frame⟩
    refine ⟨values, ?_⟩
    intro loc member
    have changed := (mem_changes_iff source target loc).mp member
    by_contra absent
    exact changed.2 (frame loc changed.1 absent)
  · rintro ⟨values, covered⟩
    refine ⟨values, ?_⟩
    intro loc bound absent
    by_contra different
    exact absent (covered ((mem_changes_iff source target loc).mpr ⟨bound, different⟩))

/-- The selected final value, or the source value if no record exists, equals the complete
supplied target. Duplicate records cannot hide a conflicting value because all are checked. -/
theorem read_of_checkFinal {source target : MemorySnapshot} {records : List (MemLoc × BitVec 64)}
    (checked : source.checkFinal target records = true) (loc : MemLoc)
    (bound : loc.busAddress < 2 ^ 48) :
    (((records.filter (fun record => decide (record.1 = loc))).head?).map Prod.snd).getD
      (source.read loc) = target.read loc := by
  have checks := (checkFinal_iff source target records).mp checked
  cases found : (records.filter (fun record => decide (record.1 = loc))).head? with
  | some record =>
      have member := List.mem_filter.mp (List.mem_of_head? found)
      have atLoc : record.1 = loc := of_decide_eq_true member.2
      simpa only [Option.map_some, Option.getD_some, atLoc] using (checks.1 record member.1).symm
  | none =>
      simp only [Option.map_none, Option.getD_none]
      apply checks.2 loc bound
      intro present
      obtain ⟨record, member, same⟩ := List.mem_map.mp present
      have empty := List.head?_eq_none_iff.mp found
      have included : record ∈ records.filter (fun record => decide (record.1 = loc)) :=
        List.mem_filter.mpr ⟨member, decide_eq_true same⟩
      rw [empty] at included
      exact List.not_mem_nil included

private theorem selected_of_mem (records : List (MemLoc × BitVec 64))
    (distinct : (records.map Prod.fst).Nodup) (record : MemLoc × BitVec 64)
    (member : record ∈ records) :
    (records.filter (fun entry => decide (entry.1 = record.1))).head? = some record := by
  induction records with
  | nil => contradiction
  | cons first rest ih =>
      have unique := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with rfl | later
      · simp
      · have different : first.1 ≠ record.1 := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨record, later, same.symm⟩)
        rw [List.filter_cons, if_neg (by simpa only [decide_eq_true_eq] using different)]
        exact ih unique.2 later

/-- For a unique bounded final inventory, the check is complete for exactly the pointwise
endpoint formula used by the grounding theorem. It imposes no sparse-history normal form. -/
theorem checkFinal_iff_reads (source target : MemorySnapshot) (records : List (MemLoc × BitVec 64))
    (distinct : (records.map Prod.fst).Nodup)
    (bounded : ∀ record ∈ records, record.1.busAddress < 2 ^ 48) :
    source.checkFinal target records = true ↔
      ∀ loc, loc.busAddress < 2 ^ 48 →
        (((records.filter (fun record => decide (record.1 = loc))).head?).map Prod.snd).getD
          (source.read loc) = target.read loc := by
  refine ⟨fun checked => read_of_checkFinal checked, ?_⟩
  intro reads
  apply (checkFinal_iff source target records).mpr
  constructor
  · intro record member
    have read := reads record.1 (bounded record member)
    rw [selected_of_mem records distinct record member, Option.map_some, Option.getD_some] at read
    exact read.symm
  · intro loc bound absent
    have empty : records.filter (fun record => decide (record.1 = loc)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro record member
      rw [decide_eq_true_eq]
      intro same
      exact absent (same ▸ List.mem_map_of_mem (f := Prod.fst) member)
    simpa only [empty, List.head?_nil, Option.map_none, Option.getD_none] using reads loc bound

end SP1Clean.Model.Core.MemorySnapshot
