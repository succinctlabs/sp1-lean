import SP1Clean.Native.Operations.AddressDiv8

/-! # Exact natural division and a total bounded constructor

Local thirteen/three-bit splits rule out every field wrap and imply canonical 48-bit inputs.
All output meanings follow from their Euclidean decompositions. Conversely, any bounded input
word computes the partial-quotient columns required by the circuit.
-/

namespace SP1Clean.AddressDiv8

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem split_value (value quotients : ZMod p) (q : quotients.val < 2 ^ 13)
    (r : (value - quotients * 8).val < 2 ^ 3) :
    value.val = quotients.val * 8 + (value - quotients * 8).val := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have equality : value = ((quotients.val * 8 + (value - quotients * 8).val : ℕ) : ZMod p) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  calc
    value.val = (((quotients.val * 8 + (value - quotients * 8).val : ℕ) : ZMod p)).val :=
      congrArg ZMod.val equality
    _ = _ := ZMod.val_natCast_of_lt (by omega)

private theorem assemble_value (q r : ZMod p) (hq : q.val < 2 ^ 13) (hr : r.val < 2 ^ 3) :
    (q + r * 8192).val = q.val + r.val * 8192 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have equality : q + r * 8192 = ((q.val + r.val * 8192 : ℕ) : ZMod p) := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    rfl
  rw [equality, ZMod.val_natCast_of_lt (by omega)]

private theorem times_eight (q : ZMod p) (bound : q.val < 2 ^ 13) : (q * 8).val = q.val * 8 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have equality : q * 8 = ((q.val * 8 : ℕ) : ZMod p) := by simp
  rw [equality, ZMod.val_natCast_of_lt (by omega)]

theorem spec_of_parts (input : Inputs (ZMod p))
    (q0 : input.quotients[0].val < 2 ^ 13) (r0 : (input.rest 0).val < 2 ^ 3)
    (q1 : input.quotients[1].val < 2 ^ 13) (r1 : (input.rest 1).val < 2 ^ 3)
    (q2 : input.quotients[2].val < 2 ^ 13) (r2 : (input.rest 2).val < 2 ^ 3)
    (top : input.value[3] = 0) : Spec input input.output := by
  have low := split_value input.value[0] input.quotients[0] q0 r0
  have middle := split_value input.value[1] input.quotients[1] q1 r1
  have high := split_value input.value[2] input.quotients[2] q2 r2
  change (input.value[0]).val = _ + (input.rest 0).val at low
  change (input.value[1]).val = _ + (input.rest 1).val at middle
  change (input.value[2]).val = _ + (input.rest 2).val at high
  have first := assemble_value input.quotients[0] (input.rest 1) q0 r1
  have second := assemble_value input.quotients[1] (input.rest 2) q1 r2
  have rounded := times_eight input.quotients[0] q0
  have word : Word.isU64 input.value := by
    apply Word.isU64_of_cases
    · omega
    · omega
    · omega
    · simp only [top, ZMod.val_zero]; omega
  refine ⟨word, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Word.toNat_def, top, ZMod.val_zero]
    omega
  · intro index
    fin_cases index <;> simp only [Inputs.output, circuit_norm]
    · omega
    · omega
    · omega
  · simp only [Inputs.output, Address.toNat, Word.toNat_def, circuit_norm, top,
      ZMod.val_zero, first, second]
    omega
  · simp only [Inputs.output, Word.toNat_def, top, ZMod.val_zero]
    omega
  · apply Word.isU64_of_cases
    · change (input.quotients[0] * 8).val < 2 ^ 16
      omega
    · exact word 1
    · exact word 2
    · simp only [Inputs.output, circuit_norm, ZMod.val_zero]; omega
  · simp only [Inputs.output, Word.toNat_def, circuit_norm, top, ZMod.val_zero, rounded]
    omega

def populate (value : Word (ZMod p)) : Inputs (ZMod p) :=
  ⟨value, Vector.ofFn fun index : Fin 3 => ((value[index.val].val / 8 : ℕ) : ZMod p)⟩

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.value ∧ Word.toNat input.value < 2 ^ 48 ∧ input = populate input.value

private theorem populate_part (value : ZMod p) (bound : value.val < 2 ^ 16) :
    (((value.val / 8 : ℕ) : ZMod p)).val < 2 ^ 13 ∧
      (value - ((value.val / 8 : ℕ) : ZMod p) * 8).val < 2 ^ 3 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have quotient := ZMod.val_natCast_of_lt (n := p) (show value.val / 8 < p by omega)
  have split : (((value.val / 8 : ℕ) : ZMod p) * 8 + ((value.val % 8 : ℕ) : ZMod p)) = value := by
    have total : value.val / 8 * 8 + value.val % 8 = value.val := by omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      using congrArg (fun n : ℕ => (n : ZMod p)) total
  have remainder : value - ((value.val / 8 : ℕ) : ZMod p) * 8 = ((value.val % 8 : ℕ) : ZMod p) := by
    linear_combination -split
  rw [quotient, remainder, ZMod.val_natCast_of_lt (by omega)]
  omega

theorem populate_checks (value : Word (ZMod p)) (word : Word.isU64 value)
    (bound : Word.toNat value < 2 ^ 48) :
    (∀ index : Fin 3, (populate value).quotients[index.val].val < 2 ^ 13 ∧
      ((populate value).rest index).val < 2 ^ 3) ∧ value[3] = 0 := by
  refine ⟨?_, ?_⟩
  · intro index
    simpa only [populate, Inputs.rest, Vector.getElem_ofFn] using populate_part value[index.val] (word index.castSucc)
  · apply ZMod.val_injective
    simp only [ZMod.val_zero]
    simp only [Word.toNat_def] at bound
    omega

omit [Fact (2 ^ 17 < p)] in
private theorem eval_output (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env input.output = (ProvableStruct.eval env input).output := by
  rcases input with ⟨value, quotients⟩
  simp only [Inputs.output, Inputs.rest, circuit_norm]

def circuit : GeneralFormalCircuit (ZMod p) Inputs Output where
  main
  elaborated
  Spec input output _ := Spec input output
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, Inputs.rest, eval_output]
    have valueEval (index : ℕ) (bound : index < 4) :
        Expression.eval env input_var_value[index] = input_value[index] := by
      simpa only [Vector.getElem_map] using congrArg (fun value : Word (ZMod p) => value[index]) h_input.1
    have quotientEval (index : ℕ) (bound : index < 3) :
        Expression.eval env input_var_quotients[index] = input_quotients[index] := by
      simpa only [Vector.getElem_map] using congrArg (fun value : fields 3 (ZMod p) => value[index]) h_input.2
    simp only [valueEval, quotientEval, Nat.reduceMod] at h_holds ⊢
    obtain ⟨q0, r0, q1, r1, q2, r2, top⟩ := h_holds
    exact spec_of_parts ⟨input_value, input_quotients⟩ q0 r0 q1 r1 q2 r2 top
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, Inputs.rest]
    have valueEval (index : ℕ) (bound : index < 4) :
        Expression.eval env input_var_value[index] = input_value[index] := by
      simpa only [Vector.getElem_map] using congrArg (fun value : Word (ZMod p) => value[index]) h_input.1
    have quotientEval (index : ℕ) (bound : index < 3) :
        Expression.eval env input_var_quotients[index] = input_quotients[index] := by
      simpa only [Vector.getElem_map] using congrArg (fun value : fields 3 (ZMod p) => value[index]) h_input.2
    simp only [valueEval, quotientEval, Nat.reduceMod]
    obtain ⟨word, bound, populated⟩ := h_assumptions
    have checks := populate_checks _ word bound
    rw [← populated] at checks
    exact ⟨(checks.1 0).1, (checks.1 0).2, (checks.1 1).1, (checks.1 1).2,
      (checks.1 2).1, (checks.1 2).2, checks.2⟩

omit [Fact (2 ^ 17 < p)] in
theorem populate_assumptions (value : Word (ZMod p)) (word : Word.isU64 value)
    (bound : Word.toNat value < 2 ^ 48) : ProverAssumptions (populate value) := ⟨word, bound, rfl⟩

end SP1Clean.AddressDiv8
