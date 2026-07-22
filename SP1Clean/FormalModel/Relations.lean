import Mathlib.Data.Set.Basic

/-! # Witness relations and their languages

AIR soundness is most naturally a refinement between two witness relations.  The left relation says
that a public statement has a valid algebraic witness; the right says that it has a semantic execution
witness.  Keeping both witnesses explicit avoids conflating an AIR theorem with a proof-system
verifier theorem. -/

namespace SP1Clean.WitnessRelation

universe u v w x

/-- A relation between public values and a private witness. -/
abbrev Relation (Public : Type u) (Witness : Type v) := Public → Witness → Prop

/-- The product-set presentation used by ArkLib's oracle-reduction API.  This is only a change of
representation: SP1's deterministic semantic layer does not import or depend on ArkLib. -/
def asSet {Public : Type u} {Witness : Type v} (relation : Relation Public Witness) :
    Set (Public × Witness) :=
  { pair | relation pair.1 pair.2 }

/-- The public language obtained by existentially hiding a relation's witness. -/
def language {Public : Type u} {Witness : Type v} (relation : Relation Public Witness) : Set Public :=
  { statement | ∃ witness, relation statement witness }

@[simp] theorem mem_asSet_iff {Public : Type u} {Witness : Type v}
    (relation : Relation Public Witness)
    (statement : Public) (witness : Witness) :
    (statement, witness) ∈ asSet relation ↔ relation statement witness :=
  Iff.rfl

@[simp] theorem mem_language_iff {Public : Type u} {Witness : Type v}
    (relation : Relation Public Witness)
    (statement : Public) :
    statement ∈ language relation ↔ ∃ witness, relation statement witness :=
  Iff.rfl

/-- Witness-producing refinement: every left witness induces some right witness for the same public
statement.  This is the high-level shape of AIR soundness. -/
def Sound {Public : Type u} {AIRWitness : Type v} {ExecutionWitness : Type w}
    (air : Relation Public AIRWitness) (execution : Relation Public ExecutionWitness) : Prop :=
  ∀ statement airWitness, air statement airWitness →
    ∃ executionWitness, execution statement executionWitness

/-- A constructive refinement between witness relations.

Unlike `Sound`, this bundle exposes the postprocessor that turns an AIR witness into its semantic
witness.  The map is deliberately independent of the proof that the AIR relation holds: all
execution data must be decoded from the statement and witness themselves, while validity is used
only by `map_valid`.  This prevents an implementation from hiding witness selection inside an
existential proof and gives ArkLib an ordinary total postprocessor. -/
structure FunctionalRefinement {Public : Type u} {AIRWitness : Type v}
    {ExecutionWitness : Type w} (air : Relation Public AIRWitness)
    (execution : Relation Public ExecutionWitness) where
  map : Public → AIRWitness → ExecutionWitness
  map_valid : ∀ statement airWitness, air statement airWitness →
    execution statement (map statement airWitness)

/-- Forget the postprocessor and recover ordinary witness-producing soundness. -/
theorem FunctionalRefinement.sound {Public : Type u} {AIRWitness : Type v}
    {ExecutionWitness : Type w} {air : Relation Public AIRWitness}
    {execution : Relation Public ExecutionWitness}
    (refinement : FunctionalRefinement air execution) : Sound air execution := by
  intro statement airWitness valid
  exact ⟨refinement.map statement airWitness, refinement.map_valid statement airWitness valid⟩

/-- Constructive refinements compose without introducing a choice axiom. -/
def FunctionalRefinement.trans {Public : Type u} {Witness₁ : Type v} {Witness₂ : Type w}
    {Witness₃ : Type x} {relation₁ : Relation Public Witness₁}
    {relation₂ : Relation Public Witness₂} {relation₃ : Relation Public Witness₃}
    (refinement₁₂ : FunctionalRefinement relation₁ relation₂)
    (refinement₂₃ : FunctionalRefinement relation₂ relation₃) :
    FunctionalRefinement relation₁ relation₃ where
  map statement witness₁ :=
    refinement₂₃.map statement (refinement₁₂.map statement witness₁)
  map_valid statement witness₁ valid₁ :=
    refinement₂₃.map_valid statement
      (refinement₁₂.map statement witness₁)
      (refinement₁₂.map_valid statement witness₁ valid₁)

/-- Witness-producing completeness is the converse refinement.  It is deliberately independent of
Clean's per-circuit `GeneralFormalCircuit.Completeness`: a whole-machine proof must construct one
globally balanced AIR witness, not merely one satisfiable row at a time. -/
def Complete {Public : Type u} {AIRWitness : Type v} {ExecutionWitness : Type w}
    (air : Relation Public AIRWitness) (execution : Relation Public ExecutionWitness) : Prop :=
  ∀ statement executionWitness, execution statement executionWitness →
    ∃ airWitness, air statement airWitness

/-- Bidirectional correctness of two witness relations.  Soundness is the release-critical direction;
whole-machine completeness may remain an explicitly disclosed admission while trace generation is
being verified. -/
structure Correct {Public : Type u} {AIRWitness : Type v} {ExecutionWitness : Type w}
    (air : Relation Public AIRWitness) (execution : Relation Public ExecutionWitness) : Prop where
  sound : Sound air execution
  complete : Complete air execution

/-- Witness-producing refinement composes.  This is the deterministic theorem used at the seam
between an ArkLib extractor, SP1 AIR soundness, and the native execution relation. -/
theorem Sound.trans {Public : Type u} {Witness₁ : Type v} {Witness₂ : Type w}
    {Witness₃ : Type x}
    {relation₁ : Relation Public Witness₁} {relation₂ : Relation Public Witness₂}
    {relation₃ : Relation Public Witness₃}
    (h₁₂ : Sound relation₁ relation₂) (h₂₃ : Sound relation₂ relation₃) :
    Sound relation₁ relation₃ := by
  intro statement witness₁ h₁
  obtain ⟨witness₂, h₂⟩ := h₁₂ statement witness₁ h₁
  exact h₂₃ statement witness₂ h₂

/-- Turn an existential refinement proof into the deterministic post-processing function expected by
an extraction framework.  This is the only choice made at the AIR/ArkLib boundary; the accompanying
theorem below records exactly when the selected witness is valid. -/
noncomputable def Sound.extract {Public : Type u} {Witness₁ : Type v} {Witness₂ : Type w}
    {relation₁ : Relation Public Witness₁} {relation₂ : Relation Public Witness₂}
    (sound : Sound relation₁ relation₂) (statement : Public) (witness : Witness₁)
    (valid : relation₁ statement witness) : Witness₂ :=
  Classical.choose (sound statement witness valid)

theorem Sound.extract_valid {Public : Type u} {Witness₁ : Type v} {Witness₂ : Type w}
    {relation₁ : Relation Public Witness₁} {relation₂ : Relation Public Witness₂}
    (sound : Sound relation₁ relation₂) (statement : Public) (witness : Witness₁)
    (valid : relation₁ statement witness) :
    relation₂ statement (sound.extract statement witness valid) :=
  Classical.choose_spec (sound statement witness valid)

/-- Witness-producing soundness implies the usual public-language inclusion. -/
theorem Sound.language_subset {Public : Type u} {AIRWitness : Type v} {ExecutionWitness : Type w}
    {air : Relation Public AIRWitness} {execution : Relation Public ExecutionWitness}
    (sound : Sound air execution) :
    language air ⊆ language execution := by
  rintro statement ⟨airWitness, valid⟩
  exact sound statement airWitness valid

/-- Witness-producing completeness gives the converse public-language inclusion. -/
theorem Complete.language_subset {Public : Type u} {AIRWitness : Type v} {ExecutionWitness : Type w}
    {air : Relation Public AIRWitness} {execution : Relation Public ExecutionWitness}
    (complete : Complete air execution) :
    language execution ⊆ language air := by
  rintro statement ⟨executionWitness, valid⟩
  exact complete statement executionWitness valid

theorem Correct.language_eq {Public : Type u} {AIRWitness : Type v} {ExecutionWitness : Type w}
    {air : Relation Public AIRWitness} {execution : Relation Public ExecutionWitness}
    (correct : Correct air execution) :
    language air = language execution :=
  Set.Subset.antisymm correct.sound.language_subset correct.complete.language_subset

/-- ArkLib's `Set.language` is the first projection of `asSet`; expose the equivalence without
making the formal-model layer depend on ArkLib's namespace or protocol implementation. -/
theorem language_eq_fst_image {Public : Type u} {Witness : Type v}
    (relation : Relation Public Witness) :
    language relation = Prod.fst '' asSet relation := by
  ext statement
  constructor
  · rintro ⟨witness, valid⟩
    exact ⟨(statement, witness), valid, rfl⟩
  · rintro ⟨⟨statement', witness⟩, valid, rfl⟩
    exact ⟨witness, valid⟩

end SP1Clean.WitnessRelation
