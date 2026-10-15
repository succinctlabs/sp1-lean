import SP1Clean.Proofs.Chips.ProgramProviderChip
import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import Clean.Air.OrderedChannel

/-! # Provider composition through Clean's ordered channels

The Program and Memory providers can finish their structural channels, and the Memory finalizer
can consume the finished Memory channel. These small constructions exercise the upstream
`SoundEnsemble` interface, including distinct canonical table names. Whole-machine grounding is
proved by the library's complete ensemble; these examples supply no additional execution premise.
-/

namespace SP1CleanTest.ProviderEnsemble
open Circuit Air.Flat SP1Clean SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private def program (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  SoundEnsemble.empty (ZMod p) PublicIO
    |>.addTable { circuit := ProgramProviderChip.circuit }
        (by simp [circuit_norm, ProgramProviderChip.circuit]) (by simp [circuit_norm])
    |>.addFinishedChannel programChannel.toRaw

private def memory (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  SoundEnsemble.empty (ZMod p) PublicIO
    |>.addTable { circuit := MemoryProviderChip.circuit }
        (by simp [circuit_norm, MemoryProviderChip.circuit]) (by simp [circuit_norm])
    |>.addFinishedChannel memoryChannel.toRaw

private def boundary (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  memory (p := p) PublicIO
    |>.addTable { circuit := MemoryFinalizeChip.circuit }
        (by simp [circuit_norm, MemoryFinalizeChip.circuit, memory])
        (by simp [circuit_norm, MemoryFinalizeChip.circuit, memory])
        (by simp [circuit_norm, MemoryFinalizeChip.circuit, MemoryProviderChip.circuit, memory])

theorem programFinished (PublicIO : TypeMap) [ProvableType PublicIO] :
    (programChannel (p := p)).toRaw ∈ (program (p := p) PublicIO).finished := by
  simp [program, circuit_norm]

theorem memoryFinished (PublicIO : TypeMap) [ProvableType PublicIO] :
    (memoryChannel (p := p)).toRaw ∈ (boundary (p := p) PublicIO).finished := by
  simp [boundary, memory, circuit_norm]

theorem boundaryComponents (PublicIO : TypeMap) [ProvableType PublicIO] :
    (boundary (p := p) PublicIO).tables =
      [{ circuit := MemoryFinalizeChip.circuit }, { circuit := MemoryProviderChip.circuit }] := rfl

theorem boundaryNames (PublicIO : TypeMap) [ProvableType PublicIO] :
    ((boundary (p := p) PublicIO).tables.map (·.circuit.name)) =
      ["sp1.native.memory_finalize", "sp1.native.memory_init"] := rfl

end SP1CleanTest.ProviderEnsemble
