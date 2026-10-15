import SP1Clean.Native.Operations.HintReadSpan

/-! # Sound and complete padded HINT_READ endpoints

The final carry forbids address wrap while permitting a mathematical one-past endpoint equal
to `2^48`. Alignment makes the last bounded address a complete in-window word. The exact
positive count includes final padding; actual row coverage is the consumer ledger's next task.
-/

namespace SP1Clean.HintReadSpan

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem one_word : Word.isU64 (#v[1, 0, 0, 0] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;> simp only [circuit_norm, ZMod.val_one, ZMod.val_zero] <;> norm_num

omit [Fact (2 ^ 17 < p)] in
private theorem one_value : Word.toNat (#v[1, 0, 0, 0] : Word (ZMod p)) = 1 := by
  simp only [Word.toNat_def, circuit_norm, ZMod.val_one, ZMod.val_zero]
  norm_num

theorem spec_of_parts (input : Inputs (ZMod p)) (start length : AddressDiv8.Output (ZMod p))
    (startSpec : AddressDiv8.Spec input.startDivision start)
    (lengthSpec : AddressDiv8.Spec input.length length) (aligned : start.remainder = 0)
    (lower : AddressOrder.Spec ⟨minimum, input.start⟩)
    (last : AddrAddOperation.Spec ⟨Address.asWord input.start, length.rounded, ⟨input.last⟩, 1⟩)
    (count : AddrAddOperation.Spec ⟨Address.asWord length.quotient, #v[1, 0, 0, 0], ⟨input.count⟩, 1⟩) :
    Spec input := by
  have startBound : Address.Bounded input.start := Address.bounded_of_isU64_asWord startSpec.1
  have startFits := Address.toNat_lt startBound
  have lengthFits := lengthSpec.2.1
  have rounded := lengthSpec.2.2.2.2.2.2
  have quotient := lengthSpec.2.2.2.1
  have alignment : Address.toNat input.start % 8 = 0 := by
    have remainder := startSpec.2.2.2.2.1
    simpa only [aligned, ZMod.val_zero, Inputs.startDivision, Address.toNat_asWord] using remainder.symm
  change Address.toNat minimum ≤ Address.toNat input.start at lower
  rw [minimum, Address.toNat_ofNat _ (by norm_num)] at lower
  have lastExact := AddrAddOperation.exact_sum _ _ _ last (by
    rw [Address.toNat_asWord, rounded]
    omega)
  have countExact := AddrAddOperation.exact_sum _ _ _ count (by
    rw [Address.toNat_asWord, quotient, one_value]
    omega)
  simp only [Address.toNat_asWord, rounded] at lastExact
  simp only [Address.toNat_asWord, quotient, one_value] at countExact
  refine ⟨startBound, lengthSpec.1, ⟨lower, alignment, ?_⟩,
    lastExact.1, lastExact.2.1, countExact.1, countExact.2.1⟩
  omega

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  AddressDiv8.ProverAssumptions input.startDivision ∧ AddressDiv8.ProverAssumptions input.length ∧ Spec input

theorem part_checks (input : Inputs (ZMod p)) (valid : Spec input)
    (start length : AddressDiv8.Output (ZMod p))
    (startSpec : AddressDiv8.Spec input.startDivision start)
    (lengthSpec : AddressDiv8.Spec input.length length) :
    start.remainder = 0 ∧
      (AddressOrder.Assumptions ⟨minimum, input.start⟩ ∧ AddressOrder.Spec ⟨minimum, input.start⟩) ∧
      (AddrAddOperation.Assumptions ⟨Address.asWord input.start, length.rounded, ⟨input.last⟩, 1⟩ ∧
        AddrAddOperation.Spec ⟨Address.asWord input.start, length.rounded, ⟨input.last⟩, 1⟩) ∧
      (AddrAddOperation.Assumptions ⟨Address.asWord length.quotient, #v[1, 0, 0, 0], ⟨input.count⟩, 1⟩ ∧
        AddrAddOperation.Spec ⟨Address.asWord length.quotient, #v[1, 0, 0, 0], ⟨input.count⟩, 1⟩) := by
  refine ⟨?_, ⟨⟨Address.bounded_ofNat _, valid.1⟩, ?_⟩,
    ⟨⟨Address.isU64_asWord valid.1, lengthSpec.2.2.2.2.2.1, Or.inr rfl⟩, ?_⟩,
    ⟨⟨Address.isU64_asWord lengthSpec.2.2.1, one_word, Or.inr rfl⟩, ?_⟩⟩
  · apply ZMod.val_injective
    simpa only [Inputs.startDivision, Address.toNat_asWord, valid.2.2.1.2.1, ZMod.val_zero]
      using startSpec.2.2.2.2.1
  · change Address.toNat minimum ≤ Address.toNat input.start
    rw [minimum, Address.toNat_ofNat _ (by norm_num)]
    exact valid.2.2.1.1
  · apply AddrAddOperation.spec_of_sum _ _ _ valid.2.2.2.1
    rw [Address.toNat_asWord, lengthSpec.2.2.2.2.2.2]
    exact valid.2.2.2.2.1
  · apply AddrAddOperation.spec_of_sum _ _ _ valid.2.2.2.2.2.1
    rw [Address.toNat_asWord, one_value, lengthSpec.2.2.2.1]
    exact valid.2.2.2.2.2.2

omit [Fact (2 ^ 17 < p)] in
private theorem eval_startDivision (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env input.startDivision = (ProvableStruct.eval env input).startDivision := by
  rcases input with ⟨start, startQuotients, length, last, count⟩
  simp only [Inputs.startDivision, Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (address : fields 3 (Expression (ZMod p))) :
    Vector.map (Expression.eval env) (Address.asWord address) =
      Address.asWord (Vector.map (Expression.eval env) address) := by
  simp only [Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_minimum (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (Vector.map Expression.const (minimum (p := p))) = minimum := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id _

omit [Fact (2 ^ 17 < p)] in
private theorem eval_rounded (env : Environment (ZMod p)) (output : Var AddressDiv8.Output (ZMod p)) :
    Vector.map (Expression.eval env) output.rounded = (ProvableStruct.eval env output).rounded := by
  rcases output with ⟨quotient, remainder, rounded⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_quotient (env : Environment (ZMod p)) (output : Var AddressDiv8.Output (ZMod p)) :
    Vector.map (Expression.eval env) output.quotient = (ProvableStruct.eval env output).quotient := by
  rcases output with ⟨quotient, remainder, rounded⟩
  simp only [circuit_norm]

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness := by
    circuit_proof_start [AddressDiv8.circuit, AddressOrder.circuit, AddrAddOperation.circuit,
      eval_startDivision, eval_asWord, eval_minimum, eval_rounded, eval_quotient]
    obtain ⟨start, length, aligned, lower, last, count⟩ := h_holds
    apply spec_of_parts _ _ _ start length aligned
    · exact lower ⟨Address.bounded_ofNat _, Address.bounded_of_isU64_asWord start.1⟩
    · exact last ⟨start.1, length.2.2.2.2.2.1, Or.inr rfl⟩
    · exact count ⟨Address.isU64_asWord length.2.2.1, one_word, Or.inr rfl⟩
  completeness := by
    circuit_proof_start [AddressDiv8.circuit, AddressOrder.circuit, AddrAddOperation.circuit,
      eval_startDivision, eval_asWord, eval_minimum, eval_rounded, eval_quotient]
    obtain ⟨start, length⟩ := h_env
    obtain ⟨startAssumptions, lengthAssumptions, valid⟩ := h_assumptions
    exact ⟨startAssumptions, lengthAssumptions,
      part_checks _ valid _ _ (start startAssumptions) (length lengthAssumptions)⟩

end SP1Clean.HintReadSpan
