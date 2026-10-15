import SP1Clean.FormalModel.Contracts.BoundedWord
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Circuits.Gadgets.LtUnsigned
import SP1Clean.Model.Semantics.Decode

/-! # A native unsigned constant-bound check

Compose the word range check and the existing unsigned comparator. The constant is encoded as
a full word, so bounds larger than the field characteristic do not become reduced field values.
The constructor computes comparison columns from the semantic input word.
-/

namespace SP1Clean.BoundedWord

open Circuit SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def limit (bound : ℕ) : Word (ZMod p) := bitVecToWord (BitVec.ofNat 64 bound)

private theorem limit_value (bound : ℕ) (fits : bound < 2 ^ 64) :
    Word.toNat (limit (p := p) bound) = bound := by
  rw [limit, ← Word.toBitVec64_toNat (isU64_bitVecToWord _),
    toBitVec64_bitVecToWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

def populate (bound : ℕ) (value : Word (ZMod p)) : Inputs (ZMod p) :=
  ⟨value, LtOperationUnsigned.populate value (limit bound)⟩

def ProverAssumptions (bound : ℕ) (input : Inputs (ZMod p)) : Prop :=
  Spec bound input ∧ input.comparison = LtOperationUnsigned.populate input.value (limit bound)

def main (bound : ℕ) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit input.value
  assertion LtOperationUnsigned.circuit ⟨input.value, const (limit bound), input.comparison, 1⟩
  assertZero (input.comparison.u16_compare_operation.bit - 1)

instance elaborated (bound : ℕ) : ElaboratedCircuit (ZMod p) Inputs unit (main bound) := by
  elaborate_circuit

omit [Fact (2 ^ 17 < p)] in
private theorem eval_limit (bound : ℕ) (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (Vector.map Expression.const (limit (p := p) bound)) = limit bound := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id _

theorem soundness (bound : ℕ) (fits : bound < 2 ^ 64) :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) (main bound)
      (fun _ _ => True) (fun input _ _ => Spec bound input) := by
  circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec]
  rw [eval_limit] at h_holds
  obtain ⟨valueBound, compare, one⟩ := h_holds
  have limitBound : Word.isU64 (limit (p := p) bound) := isU64_bitVecToWord _
  have result := (LtOperationUnsigned.result_semantic
    (compare ⟨fun _ => ⟨valueBound, limitBound⟩, Or.inr rfl⟩) rfl).1
  dsimp only at result
  rw [sub_eq_zero.mp one, limit_value bound fits] at result
  refine ⟨valueBound, ?_⟩
  split at result
  · assumption
  · exact False.elim (one_ne_zero result)

theorem completeness (bound : ℕ) (fits : bound < 2 ^ 64) :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) (main bound)
      (fun input _ _ => ProverAssumptions bound input) (fun _ _ _ => True) := by
  circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
    ProverAssumptions, Spec]
  rw [eval_limit]
  obtain ⟨⟨valueBound, boundValue⟩, comparisonEq⟩ := h_assumptions
  have limitBound : Word.isU64 (limit (p := p) bound) := isU64_bitVecToWord _
  have compare := LtOperationUnsigned.spec_populate (b := input_value) (cc := limit (p := p) bound) valueBound limitBound
  have result := (LtOperationUnsigned.result_semantic compare rfl).1
  rw [← comparisonEq] at compare result
  refine ⟨valueBound, ⟨⟨fun _ => ⟨valueBound, limitBound⟩, Or.inr rfl⟩, compare⟩, ?_⟩
  dsimp only at result
  rw [result, limit_value bound fits, if_pos boundValue, sub_self]

@[local circuit_norm] private theorem word_requirements :
    (WordRangeCheck.circuit (p := p)).channelsWithRequirements = [] := rfl

@[local circuit_norm] private theorem comparison_requirements :
    (LtOperationUnsigned.circuit (p := p)).channelsWithRequirements = [] := rfl

def circuit (bound : ℕ) (fits : bound < 2 ^ 64) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main bound
  elaborated := elaborated bound
  Spec input _ _ := Spec bound input
  ProverAssumptions input _ _ := ProverAssumptions bound input
  soundness := soundness bound fits
  completeness := completeness bound fits
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm]
    · simp only [main, circuit_norm]
    · intro env _
      simp only [main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
theorem populate_assumptions (bound : ℕ) (value : Word (ZMod p))
    (word : Word.isU64 value) (below : Word.toNat value < bound) :
    ProverAssumptions bound (populate bound value) := ⟨⟨word, below⟩, rfl⟩

end SP1Clean.BoundedWord
