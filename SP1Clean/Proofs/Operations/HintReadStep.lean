import SP1Clean.Native.Operations.HintReadStep

/-! # Successive hint word semantics and completeness

The adder contracts establish natural-number successors, excluding disconnected cycles by the
word-index rank. Completeness requires only the semantic row contract; no arithmetic columns
are supplied by a proof argument.
-/

namespace SP1Clean.HintReadStep

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem one_word : Word.isU64 (#v[1, 0, 0, 0] : Word (ZMod p)) ∧
    Word.toNat (#v[1, 0, 0, 0] : Word (ZMod p)) = 1 := by
  constructor
  · apply Word.isU64_of_cases <;> simp only [circuit_norm, ZMod.val_one, ZMod.val_zero] <;> omega
  · simp only [Word.toNat_def, circuit_norm, ZMod.val_one, ZMod.val_zero]
    norm_num

private theorem increment_word (last : Bool) : Word.isU64 (increment (F := ZMod p) last) ∧
    Word.toNat (increment (F := ZMod p) last) = (if last then 0 else 8) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have eight : (8 : ZMod p).val = 8 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 8) (by omega)
  cases last <;> constructor
  all_goals
    first
    | apply Word.isU64_of_cases <;> simp only [increment, circuit_norm, eight, ZMod.val_zero] <;> omega
    | simp [increment, Word.toNat_def, eight]

theorem spec_of_parts (last : Bool) (input : Inputs (ZMod p)) (word : input.word.Valid)
    (marker : input.word.isLast = if last then 1 else 0)
    (address : Word.isU64 (Address.asWord input.address))
    (index : AddrAddOperation.Spec ⟨Address.asWord input.word.index, #v[1, 0, 0, 0], ⟨input.nextIndex⟩, 1⟩)
    (next : AddrAddOperation.Spec ⟨Address.asWord input.address, increment last, ⟨input.nextAddress⟩, 1⟩) :
    Spec last input := by
  have addressBound := Address.bounded_of_isU64_asWord address
  have indexBound := Address.toNat_lt word.2.2.1
  have addressFits := Address.toNat_lt addressBound
  have indexExact := AddrAddOperation.exact_sum _ _ _ index (by
    rw [Address.toNat_asWord, one_word.2]; omega)
  rw [Address.toNat_asWord, one_word.2] at indexExact
  have addressExact := AddrAddOperation.exact_sum _ _ _ next (by
    rw [Address.toNat_asWord, (increment_word last).2]
    split_ifs <;> omega)
  rw [Address.toNat_asWord, (increment_word last).2] at addressExact
  exact ⟨word, marker, addressBound, indexExact.1, indexExact.2.1, addressExact.1, addressExact.2.1⟩

theorem part_checks (last : Bool) (input : Inputs (ZMod p)) (valid : Spec last input) :
    Word.isU64 (Address.asWord input.address) ∧
      (AddrAddOperation.Assumptions ⟨Address.asWord input.word.index, #v[1, 0, 0, 0], ⟨input.nextIndex⟩, 1⟩ ∧
       AddrAddOperation.Spec ⟨Address.asWord input.word.index, #v[1, 0, 0, 0], ⟨input.nextIndex⟩, 1⟩) ∧
      (AddrAddOperation.Assumptions ⟨Address.asWord input.address, increment last, ⟨input.nextAddress⟩, 1⟩ ∧
       AddrAddOperation.Spec ⟨Address.asWord input.address, increment last, ⟨input.nextAddress⟩, 1⟩) := by
  refine ⟨Address.isU64_asWord valid.2.2.1,
    ⟨⟨Address.isU64_asWord valid.1.2.2.1, one_word.1, Or.inr rfl⟩, ?_⟩,
    ⟨⟨Address.isU64_asWord valid.2.2.1, (increment_word last).1, Or.inr rfl⟩, ?_⟩⟩
  · apply AddrAddOperation.spec_of_sum _ _ _ valid.2.2.2.1
    rw [Address.toNat_asWord, one_word.2]
    exact valid.2.2.2.2.1
  · apply AddrAddOperation.spec_of_sum _ _ _ valid.2.2.2.2.2.1
    rw [Address.toNat_asWord, (increment_word last).2]
    exact valid.2.2.2.2.2.2

omit [Fact (2 ^ 17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (address : fields 3 (Expression (ZMod p))) :
    Vector.map (Expression.eval env) (Address.asWord address) =
      Address.asWord (Vector.map (Expression.eval env) address) := by
  simp only [Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_increment (env : Environment (ZMod p)) (last : Bool) :
    Vector.map (Expression.eval env) (increment (F := Expression (ZMod p)) last) = increment last := by
  cases last <;> simp only [increment, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_marker (env : Environment (ZMod p)) (last : Bool) :
    Expression.eval env (if last then 1 else 0) = (if last then 1 else (0 : ZMod p)) := by
  cases last <;> simp only [circuit_norm]

def circuit (last : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main last
  elaborated := elaborated last
  channelsWithRequirements := [HostHintQueue.wordChannel.toRaw]
  Spec input _ _ := Spec last input
  ProverAssumptions input _ _ := Spec last input
  soundness := by
    circuit_proof_start [HostHintQueue.wordChannel, WordRangeCheck.circuit, WordRangeCheck.Spec,
      WordRangeCheck.Assumptions, AddrAddOperation.circuit, eval_asWord, eval_increment, eval_marker]
    obtain ⟨word, marker, address, index, next⟩ := h_holds
    have bounds := Address.bounded_of_isU64_asWord address
    exact spec_of_parts last
      ⟨⟨input_word_pointer, input_word_index, input_word_value, input_word_isLast⟩,
        input_address, input_nextIndex, input_nextAddress⟩ word (sub_eq_zero.mp marker) address
      (index ⟨Address.isU64_asWord word.2.2.1, one_word.1, Or.inr rfl⟩)
      (next ⟨Address.isU64_asWord bounds, (increment_word last).1, Or.inr rfl⟩)
  completeness := by
    circuit_proof_start [HostHintQueue.wordChannel, WordRangeCheck.circuit, WordRangeCheck.Spec,
      WordRangeCheck.Assumptions, AddrAddOperation.circuit, eval_asWord, eval_increment, eval_marker]
    exact ⟨h_assumptions.1, sub_eq_zero.mpr h_assumptions.2.1,
      part_checks last ⟨⟨input_word_pointer, input_word_index, input_word_value, input_word_isLast⟩,
        input_address, input_nextIndex, input_nextAddress⟩ h_assumptions⟩
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm, HostHintQueue.wordChannel,
        WordRangeCheck.circuit, AddrAddOperation.circuit]
    · simp only [main, circuit_norm, HostHintQueue.wordChannel,
        WordRangeCheck.circuit, AddrAddOperation.circuit]
    · intro env _
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction member
      apply Or.inl
      have selected := List.mem_map_of_mem (f := fun item : AbstractInteraction (ZMod p) => item.channel) member
      rw [← Operations.shallowChannels_eq_interactions_map] at selected
      simpa only [main, circuit_norm] using selected

end SP1Clean.HintReadStep
