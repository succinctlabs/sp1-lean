import SP1Clean.Model.Core.MemoryFinalCheck

/-! # Complete finite Memory endpoint checks

These exercise the data-only boundary check, not an installed AIR verifier. It must accept
equivalent sparse histories while rejecting both forged final values and unrecorded changes.
-/

namespace SP1CleanTest.Core.MemoryFinalCheck

open SP1Clean SP1Clean.Model.Core SP1Clean.Semantics

private def source : MemorySnapshot where
  registers := (Vector.replicate 32 0).set 1 17 |>.set 2 23
  memory := ⟨[(65536, 9), (65539, 10), (80000, 27), (0, 5), (2 ^ 48 - 1, 19)]⟩

private def target : MemorySnapshot where
  registers := source.registers.set 1 123
  memory := source.memory.write 65539 0

private def records : List (MemLoc × BitVec 64) :=
  [(.reg 1, 123), (.ram (BitVec.ofNat 61 (65536 / 8)), target.memory.readWord 65536)]

/-- Record order, repeated consistent records, and obsolete sparse entries do not affect equality.
Out-of-window sparse entries are absent in both Sail realizations. -/
theorem acceptsEquivalentEndpoints :
    [source.checkFinal target records,
     source.checkFinal target records.reverse,
     source.checkFinal target (records ++ records),
     source.checkFinal { target with memory.entries := target.memory.entries ++ [(65539, 99)] } records,
     source.checkFinal { target with memory := target.memory.write (2 ^ 48) 99 } records,
     source.checkFinal source [],
     source.checkFinal { source with memory.entries := source.memory.entries ++ [(80000, 99)] } []] =
      [true, true, true, true, true, true, true] := by native_decide

/-- Neither a missing record nor a matching record at a different kind/location can hide a
changed byte. All duplicate values are checked, even if the first record already has the right value. -/
theorem rejectsForgedEndpoints :
    [source.checkFinal { target with registers := target.registers.set 2 24 } records,
     source.checkFinal { target with memory := target.memory.write 80000 28 } records,
     source.checkFinal { target with memory := target.memory.write 90000 1 } records,
     source.checkFinal { target with memory := target.memory.write 0 6 } (records ++ [(.reg 0, 0)]),
     source.checkFinal { target with memory := target.memory.write (2 ^ 48 - 1) 20 } records,
     source.checkFinal { target with memory := target.memory.write 65538 1 } records,
     source.checkFinal target [],
     source.checkFinal target (records ++ [(.reg 1, 124)])] =
      [false, false, false, false, false, false, false, false] := by native_decide

/-- Coverage demands are computed from complete boundary data, ignoring history duplicates
but retaining low RAM and the last byte of the native window. -/
theorem completeChanges :
    [source.changes target == records.map Prod.fst,
     source.changes source == [],
     source.changes { target with memory.entries := target.memory.entries ++ [(65539, 99)] } ==
       source.changes target,
     source.changes { source with memory := source.memory.write 0 6 } == [.ram 0],
     source.changes { source with memory := source.memory.write (2 ^ 48 - 1) 20 } ==
       [.ram (BitVec.ofNat 61 ((2 ^ 48 - 1) / 8))],
     source.changes { source with memory := source.memory.write (2 ^ 48) 99 } == []] =
      [true, true, true, true, true, true] := by native_decide

end SP1CleanTest.Core.MemoryFinalCheck
