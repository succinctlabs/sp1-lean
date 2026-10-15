import ToClean.Air.Realizes
import SP1Clean.FormalModel.ShardMachine
import SP1Clean.Soundness.Shard.Contract

/-! # The shard targets as a machine realization

`SoundnessTarget` and `CompilerTarget` are exactly the two fields of `Air.Flat.Realizes` at the SP1
machine, with the fixed complete endpoints as the boundary and the header identity, source
validity, fixed ordinary-write policy, and resource profile as admissibility.
`statement_iff_of_realizes` re-derives the intended single statement from `Realizes.statement_iff`;
nothing is proved twice and no second
carrier is introduced: the machine is PolyFun's `Labeled` bundle of the existing `executionSystem`.
Both targets remain unfilled; this file fixes their generic shape.
-/

namespace SP1Clean.Soundness.Shard

open Air.Flat Model.Core Machine FormalModel.Shard PFunctor.DynSystem

variable {p : ℕ} [Fact p.Prime]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Every public input names the same complete endpoints of one fixed shard. -/
def boundary (source target : ExecutionSnapshot) :
    PublicIO (ZMod p) → ExecutionState × ExecutionState :=
  fun _ => (source.realize, target.realize)

/-- The header identity, source validity, ordinary-write permission, and resource profile. -/
noncomputable def admissible (limits : ResourceLimits) (image : ProgramImage) (valid : image.Valid)
    (source target : ExecutionSnapshot) (header : PublicIO (ZMod p)) :
    PublicIO (ZMod p) → List ExecutionEvent → Prop :=
  fun publicInput events =>
    publicInput = header ∧ ExecutionSourceValid image source ∧
      ExecutionPath.WritesPermitted (policy p image) (image.toGuestProgram valid) source.realize events ∧
      nativeProfile limits p image source target events

omit [Fact p.Prime] [ProvableType PublicIO] in
theorem interpretation_iff {limits : ResourceLimits} {image : ProgramImage} (valid : image.Valid)
    {source target : ExecutionSnapshot} {header publicInput : PublicIO (ZMod p)}
    {events : List ExecutionEvent} :
    Interpretation limits image source target header publicInput events ↔
      Air.Flat.Interpretation (sp1Machine p image valid) (boundary source target)
        (admissible limits image valid source target header) publicInput events := by
  simp only [Interpretation, AdmissibleExecution, Air.Flat.Interpretation, boundary, admissible,
    executes_iff (valid := valid)]
  tauto

/-- The two shard targets are exactly a realization of the SP1 machine. -/
def realizes {ensemble : Ensemble (ZMod p) PublicIO} {limits : ResourceLimits} {image : ProgramImage}
    (valid : image.Valid) {source target : ExecutionSnapshot} {header : PublicIO (ZMod p)}
    (sound : SoundnessTarget ensemble limits image source target header)
    (compiler : CompilerTarget ensemble limits image source target header) :
    Air.Flat.Realizes (sp1Machine p image valid) ensemble (boundary source target)
      (admissible limits image valid source target header) where
  sound publicInput _ accepted :=
    let ⟨events, interpretation⟩ := sound publicInput trivial accepted
    ⟨events, (interpretation_iff valid).mp interpretation⟩
  compiler :=
    { compile := compiler.compile
      sound := fun publicInput events witness compiled =>
        let ⟨interpretation, validWitness⟩ := compiler.sound publicInput events witness compiled
        ⟨(interpretation_iff valid).mp interpretation, validWitness⟩
      complete := fun publicInput events interpretation =>
        compiler.complete publicInput events ((interpretation_iff valid).mpr interpretation) }

/-- The intended single statement, derived from the machine realization. -/
theorem statement_iff_of_realizes {ensemble : Ensemble (ZMod p) PublicIO} {limits : ResourceLimits}
    {image : ProgramImage} (valid : image.Valid) {source target : ExecutionSnapshot}
    {header : PublicIO (ZMod p)}
    (sound : SoundnessTarget ensemble limits image source target header)
    (compiler : CompilerTarget ensemble limits image source target header) :
    ensemble.Statement header ↔
      ∃ events, AdmissibleExecution limits p image source target events := by
  rw [(realizes valid sound compiler).statement_iff header]
  refine exists_congr fun events => ?_
  -- `executes_iff` is instantiated by hand: `events : List (sp1Machine …).Event` only unfolds to
  -- `List ExecutionEvent` at default transparency, which `simp` no longer does when assigning it.
  simp only [boundary, admissible, AdmissibleExecution, true_and,
    executes_iff (valid := valid) (events := events)]
  tauto

end SP1Clean.Soundness.Shard
