import SP1Clean.Soundness.GatedVm.Defs

/-! # `GatedVm.toFormalEnsemble` — packaging a gated VM into a Clean `FormalEnsemble`

Takes the per-witness soundness obligation — *from the ensemble `Statement` (per-table constraints +
balanced channels) plus the public-input assumptions, conclude the spec* — and repackages it as a Clean
`Air.Flat.FormalEnsemble`. The packaging is gated-multiplicity agnostic: it imposes nothing about how the
witness's channels balance or how the spec is derived — that is supplied by the caller
(`Soundness/SP1GatedVm.lean`), which derives the cross-row content from the gated State-bus balance alone
via `gatedExecution_of_specs_and_balance`. Sorry-free; no new trust. -/

namespace SP1Clean.Soundness

open Air.Flat

variable {F : Type} [Field F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Build a `FormalEnsemble` from a `GatedVm` plus a per-witness soundness proof. The obligation is
stated in the convenient "given a witness with constraints + balanced channels (and the public-input
`Assumptions`), the `Spec` holds for its public input" form; this repackages it into the
`Ensemble.Soundness` shape (`∀ publicInput, Assumptions → Statement → Spec`) that `FormalEnsemble`
wants, discharging the `Statement` existential once here so callers never have to. -/
def GatedVm.toFormalEnsemble (vm : GatedVm F PublicIO)
    (Assumptions Spec : PublicIO F → Prop)
    (soundness : ∀ (witness : EnsembleWitness vm.toEnsemble),
        Assumptions witness.publicInput →
        witness.Constraints →
        witness.BalancedChannels →
        Spec witness.publicInput) :
    FormalEnsemble F PublicIO where
  ensemble := vm.toEnsemble
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    intro publicInput hA hStmt
    obtain ⟨witness, hpub, hC, hB⟩ := hStmt
    subst hpub
    exact soundness witness hA hC hB

@[simp] lemma GatedVm.toFormalEnsemble_ensemble (vm : GatedVm F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) (soundness) :
    (vm.toFormalEnsemble Assumptions Spec soundness).ensemble = vm.toEnsemble := rfl

@[simp] lemma GatedVm.toFormalEnsemble_spec (vm : GatedVm F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) (soundness) :
    (vm.toFormalEnsemble Assumptions Spec soundness).Spec = Spec := rfl

@[simp] lemma GatedVm.toFormalEnsemble_assumptions (vm : GatedVm F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) (soundness) :
    (vm.toFormalEnsemble Assumptions Spec soundness).Assumptions = Assumptions := rfl

end SP1Clean.Soundness
