import SP1Clean.FormalModel.Contracts.OrderedBoundary
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Circuits.Gadgets.LtUnsigned
import ToClean.Circuit.InteractionRecovery

/-! # A constrained ordered boundary link

Every row pulls its predecessor key and pushes its own key, both with unit multiplicity. Two
range checks and an unsigned comparison establish strict natural-number order. The channel
name is an ensemble parameter, allowing independent initialization and finalization chains.
-/

namespace SP1Clean.OrderedBoundary

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def channel (name : String) : Channel (ZMod p) Word where
  name
  Guarantees _ _ := True

omit [Fact (2 ^ 17 < p)] in
theorem channel_ne_byte (name : String) (distinct : name ≠ "SP1Byte") :
    (channel (p := p) name).toRaw ≠ Channels.byteChannel.toRaw := by
  intro equal
  exact distinct (congrArg RawChannel.name equal)

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  Spec input ∧ input.comparison = LtOperationUnsigned.populate input.previous input.current

def populate (previous current : Word (ZMod p)) : Inputs (ZMod p) :=
  ⟨previous, current, LtOperationUnsigned.populate previous current⟩

omit [Fact (2 ^ 17 < p)] in
theorem populate_assumptions (previous current : Word (ZMod p))
    (previousBound : Word.isU64 previous) (currentBound : Word.isU64 current)
    (increases : Word.toNat previous < Word.toNat current) :
    ProverAssumptions (populate previous current) :=
  ⟨⟨previousBound, currentBound, increases⟩, rfl⟩

def main (name : String) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit input.previous
  assertion WordRangeCheck.circuit input.current
  assertion LtOperationUnsigned.circuit ⟨input.previous, input.current, input.comparison, 1⟩
  assertZero (input.comparison.u16_compare_operation.bit - 1)
  (channel name).pull input.previous
  (channel name).push input.current

/-- The comparison and range subcircuits contribute no control interactions. -/
theorem main_interactions (name : String) (distinct : name ≠ "SP1Byte") (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main name input).operations offset).interactionsWith (channel name).toRaw =
      [((channel name).pulled input.previous).toRaw, ((channel name).pushed input.current).toRaw] := by
  have wordEmpty (word : Var Word (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil WordRangeCheck.circuit
      (channel name).toRaw word
      (by change (channel name).toRaw ∉ ([] : List (RawChannel (ZMod p))); exact List.not_mem_nil)
      (by simp [WordRangeCheck.circuit]) (n := n)
  have comparisonEmpty (args : Var LtOperationUnsigned.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil LtOperationUnsigned.circuit
      (channel name).toRaw args
      (by change (channel name).toRaw ∉ [Channels.byteChannel.toRaw]
          simpa only [List.mem_singleton] using channel_ne_byte name distinct)
      (by simp [LtOperationUnsigned.circuit]) (n := n)
  simp only [main, circuit_norm, wordEmpty, comparisonEmpty, List.nil_append]

def circuit (name : String) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main name
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  channelsWithRequirements := [(channel name).toRaw]
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm, channel, WordRangeCheck.circuit]
    · simp only [main, circuit_norm, channel, WordRangeCheck.circuit]
    · intro env _
      simp only [main, circuit_norm, channel, WordRangeCheck.circuit]
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec, channel]
    obtain ⟨previousBound, currentBound, compare, one⟩ := h_holds
    have result := (LtOperationUnsigned.result_semantic
      (compare ⟨fun _ => ⟨previousBound, currentBound⟩, Or.inr rfl⟩) rfl).1
    change input_comparison_u16_compare_operation_bit =
      if Word.toNat input_previous < Word.toNat input_current then 1 else 0 at result
    rw [sub_eq_zero.mp one] at result
    refine ⟨previousBound, currentBound, ?_⟩
    split at result
    · assumption
    · exact False.elim (one_ne_zero result)
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec, ProverAssumptions, Spec, channel]
    obtain ⟨⟨previousBound, currentBound, increases⟩, comparisonEq⟩ := h_assumptions
    have compare := LtOperationUnsigned.spec_populate (b := input_previous) (cc := input_current) previousBound currentBound
    have result := (LtOperationUnsigned.result_semantic compare rfl).1
    rw [← comparisonEq] at compare result
    refine ⟨previousBound, currentBound,
      ⟨⟨fun _ => ⟨previousBound, currentBound⟩, Or.inr rfl⟩, compare⟩, ?_⟩
    dsimp only at result
    rw [result, if_pos increases, sub_self]

/-- Composing the checked link preserves its exact control pair. -/
theorem subcircuit_interactions (name : String) (distinct : name ≠ "SP1Byte")
    (input : Var Inputs (ZMod p)) (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith (channel name).toRaw
      (.subcircuit ((circuit name).toSubcircuit offset input) :: ops) =
      [((channel name).pulled input.previous).toRaw, ((channel name).pushed input.current).toRaw] ++
        ops.interactionsWith (channel name).toRaw :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    (circuit name) (channel name).toRaw input offset ops _ (main_interactions name distinct input offset)

theorem interactionValues (name : String) (distinct : name ≠ "SP1Byte")
    (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main name input).operations offset).interactionValuesWith (channel name).toRaw env =
      [(channel name).pulledValue (Eval.eval env input.previous),
       (channel name).pushedValue (Eval.eval env input.current)] := by
  simp only [Operations.interactionValuesWith, main_interactions name distinct,
    List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed]

/-- Ordering is checked by assertions and channels, without additional lookup tables. -/
@[circuit_norm] theorem main_lookups (name : String) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main name input).operations offset).lookups = [] := by
  simp [main, WordRangeCheck.circuit, LtOperationUnsigned.circuit,
    LtOperationUnsigned.main, U16CompareOperation.circuit, U16CompareOperation.main,
    Gadgets.Equality.main, circuit_norm]

end SP1Clean.OrderedBoundary
