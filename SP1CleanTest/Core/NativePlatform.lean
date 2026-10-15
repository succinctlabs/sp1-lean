import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Model.Semantics.SailFetch

/-! # The native platform fixes four-byte instruction alignment

The generated Sail model supports C/Zca. Finite source validation must therefore exclude a
source with `misa.C = 1`, even when all committed instructions are full-width and `misa.M = 1`.
This platform condition applies to empty/stopped boundaries as well as active segments.
-/

namespace SP1CleanTest.Core.NativePlatform

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target LeanRV64D.Defs LeanRV64D.Functions

private def image : ProgramImage := ⟨[(65536, 0x0020006f)], 65536, []⟩

private def source : ExecutionSnapshot where
  sail := { registers := (configuredState 65536).regs
            memory := image.initialMemory }
  host := {}
  clock := 17

/-- The ordinary native configuration remains a valid local source. -/
theorem nativeSourceAccepted : checkExecutionSource image source = true := by native_decide

private def compressed : ExecutionSnapshot :=
  { source with sail.registers := source.sail.registers.insert .misa 4100 }

/-- M is enabled in both sources; enabling C alone violates the native platform contract. -/
theorem compressedSourcesRejected :
    [checkExecutionSource image compressed,
     checkExecutionSource image { compressed with host.exitCode := some 0 }] = [false, false] := by
  native_decide

/-- The actual generated Sail query observes the disabled compressed mode at a checked source. -/
theorem officialSailMode :
    (currentlyEnabled .Ext_Zca).run source.sail.realize = .ok false source.sail.realize :=
  Advance.currentlyEnabled_zca_eq_false _
    ((checkExecutionSource_iff _ _).mp nativeSourceAccepted).configured

end SP1CleanTest.Core.NativePlatform
