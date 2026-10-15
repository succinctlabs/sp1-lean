import SP1Clean.Soundness.HostFootprint
import SP1Clean.Model.SP1Field

/-! # Host byte-slice and aligned-word footprint regressions

Check real dispatcher footprints and Sail memory effects, including the distinction between a
defined word observation and equality of failed optional reads. These semantic checks do not
claim that the pending host AIR tables authenticate an execution.
-/

namespace SP1CleanTest.Core.HostFootprint

open SP1Clean SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Soundness.Target
open LeanRV64D LeanRV64D.Defs

private def policy : HostPolicy := ⟨⟨fun _ => false, NativeLayout.guestMemory⟩, SP1Prime⟩

private def source (code arg1 arg2 length : BitVec 64) : SailState :=
  let regs := (default : SailState).regs.insert Register.x5 code
  let regs := (regs.insert Register.x10 arg1).insert Register.x11 arg2
  { (default : SailState) with
    regs := regs.insert Register.x12 length
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      ((List.range 96).map fun offset => (65536 + offset, BitVec.ofNat 8 offset)) }

private def footprint (host : HostState) (state : SailState) : Option Model.Core.HostFootprint := do
  let execution ← host.run policy (.ofSail state)
  execution.footprint? (.ofSail state)

/-- Unaligned slices cover both endpoint cells; empty spans cover no cell. -/
theorem byteCovers :
    (MemorySpan.mk 65539 10).cells = [8192, 8193] ∧
    (MemorySpan.mk 65543 2).cells = [8192, 8193] ∧
    (MemorySpan.mk 65543 0).cells = [] ∧
    (MemorySpan.mk (2 ^ 48 - 1) 1).cells = [2 ^ 45 - 1] ∧
    MemorySpan.unionCells [⟨65537, 32⟩, ⟨65544, 32⟩] = [8192, 8193, 8194, 8195, 8196] := by
  native_decide

/-- WRITE's x12 is retained, and overlapping proof-request buffers share physical cells. -/
theorem dispatchFootprints :
    footprint {} (source 2 13 65543 2) = some ⟨[5, 10, 11, 12], [8192, 8193]⟩ ∧
    footprint {} (source 2 13 65543 0) = some ⟨[5, 10, 11, 12], []⟩ ∧
    footprint {} (source 27 65537 65544 0) = some ⟨[5, 10, 11], [8192, 8193, 8194, 8195, 8196]⟩ ∧
    footprint {} (source 16 0 7 0) = some ⟨[5, 10, 11], []⟩ := by native_decide

/-- Empty and aligned-length hints retain the mandatory final padding cell. -/
theorem paddedWriteFootprints :
    footprint { io.hints := [[]] } (source 241 65536 0 0) = some ⟨[5, 10, 11], [8192]⟩ ∧
    footprint { io.hints := [[1, 2, 3, 4, 5, 6, 7, 8]] } (source 241 65536 8 0) =
      some ⟨[5, 10, 11], [8192, 8193]⟩ := by native_decide

private def withByte (state : SailState) (address : ℕ) (byte : BitVec 8) : SailState :=
  { state with mem := state.mem.insert address byte }

/-- Outside changes preserve the complete result; changing an observed byte changes public output. -/
theorem observedDependency :
    ({} : HostState).run policy (.ofSail (source 2 13 65537 2)) =
      ({} : HostState).run policy (.ofSail (withByte (source 2 13 65537 2) 65560 99)) ∧
    (({} : HostState).run policy (.ofSail (withByte (source 2 13 65537 2) 65537 99))).map
      (·.effect.state.io.publicOutput) = some [99, 2] ∧
    (({} : HostState).run policy (.ofSail (source 2 13 65537 3))).map
      (·.effect.state.io.publicOutput) = some [1, 2, 3] := by native_decide

private def partialSource (byte : BitVec 8) : SailState :=
  { (source 2 13 65537 1) with mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insert 65537 byte }

/-- Equal failed word reads can conceal different readable bytes. The bridge requires actual
defined words, so this counterexample cannot satisfy `HostWordAgreement`. -/
theorem failedWordsDoNotAuthenticateBytes :
    locContent (partialSource 1) (.ram 8192) = none ∧
    locContent (partialSource 2) (.ram 8192) = none ∧
    (({} : HostState).run policy (.ofSail (partialSource 1))).map (·.effect.state.io.publicOutput) =
      some [1] ∧
    (({} : HostState).run policy (.ofSail (partialSource 2))).map (·.effect.state.io.publicOutput) =
      some [2] := by native_decide

private def writtenWords : Bool :=
  let before := source 241 65536 8 0
  match ({ io.hints := [[1, 2, 3, 4, 5, 6, 7, 8]] } : HostState).run policy (.ofSail before) with
  | none => false
  | some execution =>
    let after := execution.apply before 65536
    locContent after (.ram 8192) == some 0x0807060504030201 &&
      locContent after (.ram 8193) == some 0 &&
      locContent after (.ram 8194) == locContent before (.ram 8194)

/-- Written and padding words agree with little-endian host bytes; adjacent RAM words retain theirs. -/
theorem writtenWordMeaning : writtenWords = true := by native_decide

end SP1CleanTest.Core.HostFootprint
