import SP1Clean.FormalModel.Shard
import ToClean.Air.CompleteEnsemble

/-! # End-to-end proof targets for the native shard

The final assembly will be indexed by a checked program image and complete incoming/outgoing
snapshots. `header` is their canonical public encoding. `SoundnessTarget` starts at the raw Clean
statement, with no semantic conjunct added to the AIR. `CompilerTarget` must construct every table
and provider from data and prove success throughout the same semantic domain.

These are checked target types and conditional assembly laws, not closed instances. The complete boundary verifier, all-eight-call assembly, and compiler remain open.
In particular the current source-hint assembly's PC/clock/frontier theorem does not establish
`SoundnessTarget`. No queue cursor, bank path, instruction split, or grounding certificate occurs
in the intended public execution relation. Faithfulness to the pinned Rust AIR is separate.
-/

namespace SP1Clean.Soundness.Shard

open Air.Flat Model.Core Machine
open FormalModel.Shard

variable {p : ℕ} [Fact p.Prime]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The public header and complete state interpretation shared by soundness and compilation. -/
noncomputable def Interpretation (limits : ResourceLimits) (image : ProgramImage)
    (source target : ExecutionSnapshot) (header publicInput : PublicIO (ZMod p))
    (events : List ExecutionEvent) : Prop :=
  publicInput = header ∧ AdmissibleExecution limits p image source target events

/-- Raw AIR acceptance must yield a path to the supplied complete outgoing state. -/
abbrev SoundnessTarget (ensemble : Ensemble (ZMod p) PublicIO) (limits : ResourceLimits)
    (image : ProgramImage) (source target : ExecutionSnapshot) (header : PublicIO (ZMod p)) : Prop :=
  ensemble.Soundness (fun _ => True)
    (fun publicInput => ∃ events, Interpretation limits image source target header publicInput events)

/-- Constructive completeness reuses Clean's generic compiler interface. Its domain contains
neither compiler success nor native row-readiness predicates. Executability is a further check. -/
abbrev CompilerTarget (ensemble : Ensemble (ZMod p) PublicIO) (limits : ResourceLimits)
    (image : ProgramImage) (source target : ExecutionSnapshot) (header : PublicIO (ZMod p)) :=
  EnsembleCompiler ensemble (List ExecutionEvent) (Interpretation limits image source target header)

/-- Filling the two targets yields the existing generic sound-and-complete Clean interface. -/
def completeEnsemble {ensemble : Ensemble (ZMod p) PublicIO} {limits : ResourceLimits}
    {image : ProgramImage} {source target : ExecutionSnapshot} {header : PublicIO (ZMod p)}
    (sound : SoundnessTarget ensemble limits image source target header)
    (compiler : CompilerTarget ensemble limits image source target header) :
    CompleteEnsemble (ZMod p) PublicIO :=
  compiler.toCompleteEnsemble sound

/-- The intended single statement, conditional here on the two unfilled implementation targets. -/
theorem statement_iff {ensemble : Ensemble (ZMod p) PublicIO} {limits : ResourceLimits}
    {image : ProgramImage} {source target : ExecutionSnapshot} {header : PublicIO (ZMod p)}
    (sound : SoundnessTarget ensemble limits image source target header)
    (compiler : CompilerTarget ensemble limits image source target header) :
    ensemble.Statement header ↔
      ∃ events, AdmissibleExecution limits p image source target events := by
  simpa only [completeEnsemble, EnsembleCompiler.toCompleteEnsemble, Interpretation, true_and] using
    (completeEnsemble sound compiler).statement_iff header trivial

end SP1Clean.Soundness.Shard
