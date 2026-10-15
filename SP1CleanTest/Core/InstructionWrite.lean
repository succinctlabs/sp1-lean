import SP1Clean.Model.Core.InstructionWrite
import SP1Clean.Model.Core.InstructionDecode
import SP1Clean.Model.Core.ProgramImage

/-! # Ordinary write-policy regressions

The same byte-precise policy covers SB/SH/SW/SD, signed offsets, non-store instructions and
invalid observations. Whole-AIR same-value ROM-write rejection is tested in `Alignment/Core/LocalCore`.
-/

namespace SP1CleanTest.Core.InstructionWrite

open SP1Clean.Model.Core LeanRV64D.Defs

private def image : ProgramImage := ⟨[(65536, 0x00110023)], 65536, []⟩

private def registers (base : BitVec 64) : BitVec 5 → Option (BitVec 64) :=
  fun index => if index = 2 then some base else none

private def store (offset : BitVec 12) (width : word_width) : instruction :=
  .STORE (offset, .Regidx 1, .Regidx 2, width)

/-- All four widths include their last byte. No register or memory value can erase the write. -/
theorem fullStoreSpans :
    [1, 2, 4, 8].map (fun width => InstructionWrite.spans? (registers 65544) (store 0 width)) =
      [some [⟨65544, 1⟩], some [⟨65544, 2⟩], some [⟨65544, 4⟩], some [⟨65544, 8⟩]] ∧
    [1, 2, 4, 8].map (fun width =>
      InstructionWrite.check (fun address => address == 65544 + width.toNat - 1)
        (registers 65544) (store 0 width)) = [false, false, false, false] := by
  native_decide

/-- Signed immediates use RV64 wrapping addition, rather than unsigned or 48-bit addition. -/
theorem signedOffsets :
    InstructionWrite.spans? (registers 65544) (store 0xff8 8) = some [⟨65536, 8⟩] ∧
    InstructionWrite.spans? (registers 65544) (store 0xffc 4) = some [⟨65540, 4⟩] ∧
    InstructionWrite.spans? (registers 0) (store 0xfff 1) = some [⟨2 ^ 64 - 1, 1⟩] ∧
    InstructionWrite.spans? (registers (BitVec.allOnes 64)) (store 1 1) = some [⟨0, 1⟩] := by
  native_decide

/-- Writable bytes in the same eight-byte cell as code remain writable; overlapping stores fail. -/
theorem partialCellPolicy :
    [InstructionWrite.check image.readOnly (registers 65544) (store 0xffc 4),
     InstructionWrite.check image.readOnly (registers 65544) (store 0xff8 8),
     InstructionWrite.check image.readOnly (registers 65535) (store 0 2),
     InstructionWrite.check image.readOnly (registers 65540) (store 0 1)] =
      [true, false, false, true] := by
  native_decide

/-- Failure is not an empty footprint, and the check does not impose write permission on ADD. -/
theorem failClosed :
    InstructionWrite.check image.readOnly (fun _ => none) (store 0 1) = false ∧
    [0, 3, 16, -1].map (fun width =>
      InstructionWrite.check image.readOnly (registers 65544) (store 0 width)) =
        [false, false, false, false] ∧
    InstructionWrite.spans? (fun _ => none) (.RTYPE (.Regidx 1, .Regidx 2, .Regidx 3, .ADD)) = some [] ∧
    InstructionWrite.check (fun _ => true) (fun _ => none)
      (.RTYPE (.Regidx 1, .Regidx 2, .Regidx 3, .ADD)) = true ∧
    InstructionWrite.check image.readOnly (registers 65544) (.ECALL ()) = false := by
  native_decide

/-- The committed SB word and its parsed operand roles give the same protected footprint. -/
theorem decodedStore :
    (InstructionDecode.decode 0x00110023).map
      (InstructionWrite.check image.readOnly (registers 65536)) = some false ∧
    (InstructionDecode.decode 0x00110023).map
      (InstructionWrite.check image.readOnly (registers 65540)) = some true := by
  native_decide

end SP1CleanTest.Core.InstructionWrite
