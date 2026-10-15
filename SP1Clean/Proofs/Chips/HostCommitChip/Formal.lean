import SP1Clean.Native.Chips.HostCommitChip.Defs

/-! # Soundness and completeness of native commitment-bank transitions

The selected call and value bound are checked locally. Strict clock order and the exact state
pair support a subsequent bank-history proof; no final-bank or fixed-public-digest equality is
assumed by this component.
-/

namespace SP1Clean.HostCommitChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p)) : Prop :=
  Spec deferred slot input ∧ input.comparison =
    LtOperationUnsigned.populate input.call.arg2 (BoundedWord.limit (bound p deferred))

omit [Fact (2 ^ 25 < p)] in
private theorem eval_zero (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (Vector.map Expression.const (0 : Word (ZMod p))) = 0 := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id _

theorem soundness (deferred : Bool) (slot : Fin 8) :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) (main deferred slot)
      (fun _ _ => True) (fun input _ _ => Spec deferred slot input) := by
  circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit, BoundedWord.circuit,
    U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions, U16toU8OperationSafe.Spec,
    codeWord, slotWord, Inputs.clock, HostCallChip.channel, stateChannel, publicValuesChannel]
  cases deferred <;> simp only [Bool.false_eq_true, ↓reduceIte, circuit_norm] at h_holds ⊢
  all_goals
    obtain ⟨code, index, result, length, clock, value, bytes⟩ := h_holds
    refine ⟨⟨?_, ?_, ?_, ?_, value⟩, clock, bytes⟩
    · simpa only [codeWord, circuit_norm] using code
    · simpa only [slotWord, circuit_norm] using index
    · simpa only [codeWord, circuit_norm] using result
    · simpa only [eval_zero] using length

theorem completeness (deferred : Bool) (slot : Fin 8) :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) (main deferred slot)
      (fun input _ _ => ProverAssumptions deferred slot input) (fun _ _ _ => True) := by
  circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit, BoundedWord.circuit,
    U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions, U16toU8OperationSafe.Spec,
    codeWord, slotWord, Inputs.clock, HostCallChip.channel, stateChannel, publicValuesChannel]
  cases deferred <;> simp only [Bool.false_eq_true, ↓reduceIte, circuit_norm] at h_assumptions ⊢
  all_goals
    obtain ⟨⟨⟨code, index, result, length, value⟩, clock, bytes⟩, comparison⟩ := h_assumptions
    refine ⟨?_, ?_, ?_, ?_, clock, ⟨value, comparison⟩, bytes⟩
    · simpa only [codeWord, circuit_norm] using code
    · simpa only [slotWord, circuit_norm] using index
    · simpa only [codeWord, circuit_norm] using result
    · simpa only [eval_zero] using length

def circuit (deferred : Bool) (slot : Fin 8) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := s!"sp1.native.{if deferred then "commit_deferred" else "commit"}.{slot.val}"
  main := main deferred slot
  elaborated := elaborated deferred slot
  Spec input _ _ := Spec deferred slot input
  ProverAssumptions input _ _ := ProverAssumptions deferred slot input
  soundness := soundness deferred slot
  completeness := completeness deferred slot
  requirementsChannelsLawful := by
    preserve_tactic_target
    cases deferred
    all_goals
      intro input offset
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, circuit_norm, publicValuesChannel, stateChannel, HostCallChip.channel,
          ClockOrder.circuit, BoundedWord.circuit, U16toU8OperationSafe.circuit, Gadgets.Equality.circuit]
      · simp only [main, circuit_norm, publicValuesChannel, stateChannel, HostCallChip.channel,
          ClockOrder.circuit, BoundedWord.circuit, U16toU8OperationSafe.circuit, Gadgets.Equality.circuit]
        tauto
      · intro env _
        simp only [main, circuit_norm, publicValuesChannel, stateChannel, HostCallChip.channel,
          ClockOrder.circuit, BoundedWord.circuit, U16toU8OperationSafe.circuit, Gadgets.Equality.circuit]
  channelsWithRequirements := [HostCallChip.channel.toRaw, (stateChannel deferred).toRaw, publicValuesChannel.toRaw]

end SP1Clean.HostCommitChip
