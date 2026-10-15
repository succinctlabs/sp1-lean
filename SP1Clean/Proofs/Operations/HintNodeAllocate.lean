import SP1Clean.Native.Operations.HintNodeAllocate

/-! # Checked fresh identities for persistent hint allocation

The address adder's high carry rules out 48-bit overflow; the frontier's bounded word rules out
64-bit wrap. Thus the result is an actual successor, not modular reuse of a historical identity.
The same semantic contract gives completeness, with all comparison/range witnesses computed.
-/

namespace SP1Clean.HintNodeAllocate

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem one_bounded : Word.isU64 (#v[1, 0, 0, 0] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;> simp only [circuit_norm, ZMod.val_one, ZMod.val_zero] <;> norm_num

omit [Fact (2 ^ 17 < p)] in
private theorem one_value : Word.toNat (#v[1, 0, 0, 0] : Word (ZMod p)) = 1 := by
  simp only [Word.toNat_def, circuit_norm, ZMod.val_one, ZMod.val_zero]
  norm_num

omit [Fact (2 ^ 17 < p)] in
private theorem addition_sound (input : Inputs (ZMod p))
    (bounded : Address.Bounded input.previous.allocated) (addition : AddrAddOperation.Spec input.addition) :
    Address.Bounded input.node.pointer ∧
      Address.toNat input.node.pointer = Address.toNat input.previous.allocated + 1 := by
  obtain ⟨sum, low, middle, high, fits⟩ := addition rfl
  have small := Address.toNat_lt bounded
  simp only [Inputs.addition, Address.toNat_asWord, one_value] at sum fits
  rw [Nat.mod_eq_of_lt (by omega)] at fits
  rw [Nat.mod_eq_of_lt fits] at sum
  refine ⟨?_, ?_⟩
  · intro index
    fin_cases index <;> assumption
  · simpa only [Address.toNat, Nat.mul_comm, Nat.reducePow] using sum

omit [Fact (2 ^ 17 < p)] in
private theorem addition_complete (input : Inputs (ZMod p)) (valid : Spec input) :
    AddrAddOperation.Assumptions input.addition ∧ AddrAddOperation.Spec input.addition := by
  refine ⟨⟨Address.isU64_asWord valid.2.1, one_bounded, Or.inr rfl⟩, ?_⟩
  intro _
  have bounded := valid.2.2.2.2.1.1
  have successor := valid.2.2.2.2.2
  have fits : Address.toNat input.previous.allocated + 1 < 2 ^ 48 := by
    rw [← successor]
    exact Address.toNat_lt bounded
  simp only [Inputs.addition, Address.toNat_asWord, one_value, Nat.mod_eq_of_lt fits,
    Nat.mod_eq_of_lt (show Address.toNat input.previous.allocated + 1 < 2 ^ 64 by omega)]
  refine ⟨?_, bounded 0, bounded 1, bounded 2, fits⟩
  simpa only [Address.toNat, Nat.mul_comm, Nat.reducePow] using successor

omit [Fact (2 ^ 17 < p)] in
private theorem semantic_spec (input : Inputs (ZMod p))
    (head : Word.isU64 (Address.asWord input.previous.head))
    (allocated : Word.isU64 (Address.asWord input.previous.allocated))
    (order : AddressOrder.Spec ⟨input.previous.head, input.previous.allocated⟩)
    (tail : input.node.tail = input.previous.head) (length : Word.isU64 input.node.length)
    (addition : AddrAddOperation.Spec input.addition) : Spec input := by
  have headBound := Address.bounded_of_isU64_asWord head
  have allocatedBound := Address.bounded_of_isU64_asWord allocated
  obtain ⟨pointerBound, successor⟩ := addition_sound input allocatedBound addition
  refine ⟨headBound, allocatedBound, order, tail, ⟨pointerBound, tail ▸ headBound, ?_, length⟩, successor⟩
  rw [tail, successor]
  exact Nat.lt_succ_of_le order

omit [Fact (2 ^ 17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (address : fields 3 (Expression (ZMod p))) :
    Vector.map (Expression.eval env) (Address.asWord address) =
      Address.asWord (Vector.map (Expression.eval env) address) := by
  simp only [Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_addition (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env input.addition = (ProvableStruct.eval env input).addition := by
  rcases input with ⟨⟨high, low, head, allocated⟩, ⟨pointer, tail, length⟩⟩
  simp only [Inputs.addition, Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_next (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env input.next = (ProvableStruct.eval env input).next := by
  rcases input with ⟨⟨high, low, head, allocated⟩, ⟨pointer, tail, length⟩⟩
  simp only [Inputs.next, circuit_norm]

def circuit : GeneralFormalCircuit (ZMod p) Inputs HostHintQueue.State where
  main
  elaborated
  Spec input output _ := Spec input ∧ output = input.next
  ProverAssumptions input _ _ := Spec input
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      Gadgets.Equality.circuit, AddressOrder.circuit, AddrAddOperation.circuit,
      eval_asWord, eval_addition, eval_next]
    obtain ⟨head, allocated, order, tail, length, addition⟩ := h_holds
    exact semantic_spec _ head allocated
      (order ⟨Address.bounded_of_isU64_asWord head, Address.bounded_of_isU64_asWord allocated⟩)
      tail length (addition ⟨allocated, one_bounded, Or.inr rfl⟩)
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      Gadgets.Equality.circuit, AddressOrder.circuit, AddrAddOperation.circuit,
      eval_asWord, eval_addition, eval_next]
    exact ⟨Address.isU64_asWord h_assumptions.1, Address.isU64_asWord h_assumptions.2.1,
      ⟨⟨h_assumptions.1, h_assumptions.2.1⟩, h_assumptions.2.2.1⟩,
      h_assumptions.2.2.2.1, h_assumptions.2.2.2.2.1.2.2.2, addition_complete _ h_assumptions⟩

end SP1Clean.HintNodeAllocate
