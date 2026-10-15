import Clean.Air.Extraction.Rust
import SP1Clean.Model.Channels
import SP1Clean.Model.SP1Field

/-! # Shared component-local export fixtures

Use Clean's built-in lowering, Rust emitter and preallocation for a production component.
External channels stay open: row comparisons do not establish ensemble balance.
-/

namespace SP1CleanTest.Core.ComponentExport

open Air.Flat SP1Clean

abbrev Fp := ZMod SP1Prime

/-- A production component with its original constraints and channel interactions. -/
def ensemble (component : Component Fp) : Ensemble Fp unit where
  tables := [component]
  unique_names := by simp
  channels := [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
    Channels.memoryChannel.toRaw, Channels.programChannel.toRaw]

/-- A single independent component input, supplied as prover construction data. -/
def config (Inputs : Type → Type) [ProvableType Inputs] : WitnessGeneration.Config Fp Inputs where
  modes := [.preallocated {
    rows := 1
    input := {
      width := size Inputs
      steps := []
      output := .mapRange (size Inputs) (.proverInputGet .idx)
    }
    input_valid := by rfl
    handlers := []
  }]
  padding := [{ input := Array.replicate (size Inputs) 0 }]
  fuel := 1

/-- Export a production circuit with ordinary inputs and zero padding through Clean. -/
def exportRust {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (name : String) (circuit : GeneralFormalCircuit Fp Input Output) : Except String String :=
  Extraction.Rust.ensembleToRust name (ensemble { circuit }) (config Input)

end SP1CleanTest.Core.ComponentExport
