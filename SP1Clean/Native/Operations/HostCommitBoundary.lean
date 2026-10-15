import SP1Clean.FormalModel.Contracts.HostCommitBoundary
import Clean.Gadgets.Bits
import ToClean.Circuit.InteractionRecovery
import ToClean.Circuit.VerifierInteractions

/-! # Fixed endpoints for a mutable native bank

A zero-witness verifier fixes the supplied source words and public final words. The terminal component
keeps the last ordinary timestamp private, checks its bounds, and preserves all eight words.
No semantic truth is asserted by the bank channel.
-/

namespace SP1Clean.HostCommitBoundary

open Circuit HostCommitChip
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def terminalMain (deferred : Bool) (input : Var State (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) input.clk_high
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega)) input.clk_low
  (stateChannel deferred).pull input
  (stateChannel deferred).push (final input.values)

def terminal (deferred : Bool) : GeneralFormalCircuit (ZMod p) State unit where
  name := s!"sp1.native.{if deferred then "commit_deferred" else "commit"}.terminal"
  main := terminalMain deferred
  Spec input _ _ := TerminalSpec input
  ProverAssumptions input _ _ := TerminalSpec input
  channelsWithRequirements := [(stateChannel deferred).toRaw]
  soundness := by
    circuit_proof_start [terminalMain, Gadgets.ToBits.rangeCheck, stateChannel, final]
    exact h_holds
  completeness := by
    circuit_proof_start [terminalMain, Gadgets.ToBits.rangeCheck, stateChannel, final]
    exact h_assumptions

def verifierMain (deferred : Bool) (initialValues : Vector (Word (ZMod p)) 8) (values : Var (ProvableVector Word 8) (ZMod p)) :
    Circuit (ZMod p) Unit := do
  (stateChannel deferred).push (const (start initialValues))
  (stateChannel deferred).pull (final values)

def verifier (deferred : Bool) (initialValues : Vector (Word (ZMod p)) 8) :
    GeneralFormalCircuit (ZMod p) (ProvableVector Word 8) unit where
  main := verifierMain deferred initialValues
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  channelsWithRequirements := [(stateChannel deferred).toRaw]
  soundness := by circuit_proof_start [verifierMain, stateChannel]
  completeness := by circuit_proof_start [verifierMain, stateChannel]

/-- The same endpoint traffic admitted into Clean's separate public verifier. The circuit bundle
remains the composition boundary for the complete host-boundary circuit. -/
def verifierProgram (deferred : Bool) (initialValues : Vector (Word (ZMod p)) 8) :
    Verifier.Program (ZMod p) (ProvableVector Word 8) where
  main values := Verifier.ofInteractions ((verifierMain deferred initialValues values).operations 0).interactions
    (by
      intro interaction member env
      simp only [verifierMain, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [AbstractInteraction.Requirements, AbstractInteraction.Guarantees,
          ChannelInteraction.toRaw, stateChannel, Channel.toRaw, circuit_norm])

omit [Fact (2 ^ 25 < p)] in
private theorem range_empty (target : RawChannel (ZMod p)) (n : ℕ) (bound : 2 ^ n < p)
    (input : Expression (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck n bound) target input List.not_mem_nil List.not_mem_nil

theorem terminal_interactions (deferred : Bool) (input : Var State (ZMod p)) (offset : ℕ) :
    ((terminalMain deferred input).operations offset).interactionsWith (stateChannel deferred).toRaw =
      [((stateChannel deferred).pulled input).toRaw,
       ((stateChannel deferred).pushed (final input.values)).toRaw] := by
  simp only [terminalMain, circuit_norm, range_empty, List.nil_append]

omit [Fact (2 ^ 25 < p)] in
theorem verifier_interactions (deferred : Bool) (initialValues : Vector (Word (ZMod p)) 8) (values : Var (ProvableVector Word 8) (ZMod p)) (offset : ℕ) :
    ((verifierMain deferred initialValues values).operations offset).interactionsWith (stateChannel deferred).toRaw =
      [((stateChannel deferred).pushed (const (start initialValues))).toRaw,
       ((stateChannel deferred).pulled (final values)).toRaw] := by
  simp only [verifierMain, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_final (env : Environment (ZMod p)) (values : Var (ProvableVector Word 8) (ZMod p)) :
    Eval.eval env (final values) = final (Eval.eval env values) := by
  simp only [final, circuit_norm]

theorem terminal_values (deferred : Bool) (input : Var State (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    ((terminalMain deferred input).operations offset).interactionValuesWith (stateChannel deferred).toRaw env =
      [(stateChannel deferred).pulledValue (Eval.eval env input),
       (stateChannel deferred).pushedValue (final (Eval.eval env input.values))] := by
  simp only [Operations.interactionValuesWith, terminal_interactions, List.map_cons, List.map_nil,
    Channel.eval_pulled, Channel.eval_pushed, eval_final]

omit [Fact (2 ^ 25 < p)] in
theorem verifier_values (deferred : Bool) (initialValues : Vector (Word (ZMod p)) 8) (values : Var (ProvableVector Word 8) (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    ((verifierMain deferred initialValues values).operations offset).interactionValuesWith (stateChannel deferred).toRaw env =
      [(stateChannel deferred).pushedValue (start initialValues),
       (stateChannel deferred).pulledValue (final (Eval.eval env values))] := by
  simp only [Operations.interactionValuesWith, verifier_interactions, List.map_cons, List.map_nil,
    Channel.eval_pulled, Channel.eval_pushed, ProvableType.eval_const, eval_final]

theorem terminal_strict (input : State (ZMod p)) (valid : TerminalSpec input) :
    Semantics.clkNat input.clk_high input.clk_low <
      Semantics.clkNat (final input.values).clk_high (final input.values).clk_low := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have sentinel : (16777216 : ZMod p).val = 2 ^ 24 := by
    change ((16777216 : ℕ) : ZMod p).val = 2 ^ 24
    rw [ZMod.val_natCast_of_lt (by omega)]
    norm_num
  simp only [Semantics.clkNat, final, sentinel, ZMod.val_zero]
  obtain ⟨high, low⟩ := valid
  omega

end SP1Clean.HostCommitBoundary
