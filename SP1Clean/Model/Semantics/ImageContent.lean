import SP1Clean.Model.Semantics.MicroTime

/-! # The committed image as cell content

`IsInitialState.imageLoaded` places the byte-granular ELF data image into Sail memory; the Memory
bus reads aligned 8-byte cells.  These decoders assemble the committed image at the bus
granularity so the boot boundary can bind Memory-init provider rows to the *committed* image
rather than to whatever content the selected initial state happens to carry.

The file sits beside `Model/Machine/Boot.lean`'s loader contract but below the machine layer
(`MicroTime` imports `Machine.Execution`, so the cell decoders cannot live in `Boot.lean`
itself).  Like `GuestProgram.lean`, the namespace records the intended `Target` vocabulary rather
than the directory. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness.Target.GuestProgram

open Sail LeanRV64D

/-- The image byte at natural address `a` (the `SailState.mem` key form). -/
def imageByte? (program : GuestProgram) (a : ℕ) : Option (BitVec 8) :=
  (program.memImage.find? (fun av => av.1.toNat == a)).map Prod.snd

/-- The image's 8-byte little-endian word covering one aligned RAM cell — present only when the
image supplies **every** byte of the cell.  Partially covered cells are deliberately `none`: their
content is governed by the quantified initial state (upstream, by the verifying-key layer), not by
this decoder. -/
def imageCell? (program : GuestProgram) (cell : SP1Clean.Semantics.RamCell) :
    Option (BitVec 64) := do
  let b0 ← program.imageByte? cell.baseAddr.toNat
  let b1 ← program.imageByte? (cell.baseAddr.toNat + 1)
  let b2 ← program.imageByte? (cell.baseAddr.toNat + 2)
  let b3 ← program.imageByte? (cell.baseAddr.toNat + 3)
  let b4 ← program.imageByte? (cell.baseAddr.toNat + 4)
  let b5 ← program.imageByte? (cell.baseAddr.toNat + 5)
  let b6 ← program.imageByte? (cell.baseAddr.toNat + 6)
  let b7 ← program.imageByte? (cell.baseAddr.toNat + 7)
  pure (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)

/-- The image content at a Memory-bus location: RAM cells only (registers have no image). -/
def imageContent? (program : GuestProgram) : SP1Clean.Semantics.MemLoc → Option (BitVec 64)
  | .reg _ => none
  | .ram cell => program.imageCell? cell

/-- A loaded image byte is the state's byte. -/
theorem imageByte?_loaded {program : GuestProgram} {s : SailState}
    (loaded : ∀ av ∈ program.memImage, s.mem.get? av.1.toNat = some av.2)
    {a : ℕ} {b : BitVec 8} (h : program.imageByte? a = some b) :
    s.mem.get? a = some b := by
  unfold imageByte? at h
  obtain ⟨av, hfind, hsnd⟩ := Option.map_eq_some_iff.mp h
  have haddr : av.1.toNat = a := by
    have := List.find?_some hfind
    simpa using this
  rw [← haddr, ← hsnd]
  exact loaded av (List.mem_of_find?_eq_some hfind)

/-- **Image-covered cells read the committed image** in any state satisfying `imageLoaded`. -/
theorem locContent_of_imageLoaded {program : GuestProgram} {s : SailState}
    (loaded : ∀ av ∈ program.memImage, s.mem.get? av.1.toNat = some av.2)
    {loc : SP1Clean.Semantics.MemLoc} {v : BitVec 64}
    (hv : program.imageContent? loc = some v) :
    SP1Clean.Semantics.locContent s loc = some v := by
  cases loc with
  | reg index => simp [imageContent?] at hv
  | ram cell =>
    simp only [imageContent?] at hv
    unfold imageCell? at hv
    rcases h0 : program.imageByte? cell.baseAddr.toNat with _ | b0
    · rw [h0] at hv; contradiction
    rcases h1 : program.imageByte? (cell.baseAddr.toNat + 1) with _ | b1
    · rw [h0, h1] at hv; contradiction
    rcases h2 : program.imageByte? (cell.baseAddr.toNat + 2) with _ | b2
    · rw [h0, h1, h2] at hv; contradiction
    rcases h3 : program.imageByte? (cell.baseAddr.toNat + 3) with _ | b3
    · rw [h0, h1, h2, h3] at hv; contradiction
    rcases h4 : program.imageByte? (cell.baseAddr.toNat + 4) with _ | b4
    · rw [h0, h1, h2, h3, h4] at hv; contradiction
    rcases h5 : program.imageByte? (cell.baseAddr.toNat + 5) with _ | b5
    · rw [h0, h1, h2, h3, h4, h5] at hv; contradiction
    rcases h6 : program.imageByte? (cell.baseAddr.toNat + 6) with _ | b6
    · rw [h0, h1, h2, h3, h4, h5, h6] at hv; contradiction
    rcases h7 : program.imageByte? (cell.baseAddr.toNat + 7) with _ | b7
    · rw [h0, h1, h2, h3, h4, h5, h6, h7] at hv; contradiction
    rw [h0, h1, h2, h3, h4, h5, h6, h7] at hv
    show SP1Clean.Semantics.ramWord64? s cell.baseAddr = some v
    unfold SP1Clean.Semantics.ramWord64?
    rw [imageByte?_loaded loaded h0, imageByte?_loaded loaded h1, imageByte?_loaded loaded h2,
      imageByte?_loaded loaded h3, imageByte?_loaded loaded h4, imageByte?_loaded loaded h5,
      imageByte?_loaded loaded h6, imageByte?_loaded loaded h7]
    simpa using hv

end SP1Clean.Soundness.Target.GuestProgram
