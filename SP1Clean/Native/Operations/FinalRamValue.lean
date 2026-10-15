import SP1Clean.FormalModel.Contracts.FinalRamValue
import SP1Clean.Native.Operations.InitialMemoryRead
import Clean.Gadgets.Equality
import SP1Clean.Math.WordEquality
import ToClean.Circuit.InteractionRecovery

/-! # Target RAM authentication through the shared byte-read circuit

All eight target bytes are checked, including unchanged bytes in a partially written word.
The fixed target table has a distinct export name from the incoming memory table.
-/

namespace SP1Clean.FinalRamValue

open Circuit Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (target : MemorySnapshot) (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) Unit := do
  let value ← InitialMemoryRead.circuitNamed target.memory "sp1.native.target_memory" (MemoryBoundary.address input)
  assertion (Gadgets.Equality.circuit Word) (value, input.value)
  (FinalMemoryValue.channel true).pull input

instance elaborated (target : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) MemoryMsg unit (main target) := by elaborate_circuit

theorem receipt_values (target : MemorySnapshot) (input : Var MemoryMsg (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith (FinalMemoryValue.channel true).toRaw env =
      [(FinalMemoryValue.channel true).pulledValue (eval env input)] := by
  have readEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (InitialMemoryRead.circuitNamed target.memory "sp1.native.target_memory").base
    (FinalMemoryValue.channel true).toRaw (MemoryBoundary.address input) n (by
      simp [circuit_norm, FinalMemoryValue.channel, byteChannel, Channel.toRaw])
  have equalEmpty (left right : Var Word (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit Word)
      (FinalMemoryValue.channel true).toRaw (left, right) (by simp [circuit_norm])
      (by simp [circuit_norm]) (n := n)
  have raw : ((main target input).operations offset).interactionsWith (FinalMemoryValue.channel true).toRaw =
      [((FinalMemoryValue.channel true).pulled input).toRaw] := by
    simp only [main, circuit_norm, equalEmpty, List.nil_append]
    simp only [Operations.interactionsWith] at readEmpty ⊢
    simp only [GeneralFormalCircuit.toSubcircuit_interactions, readEmpty, List.nil_append]
  rw [Operations.interactionValuesWith, raw]
  exact congrArg (fun value => [value]) Channel.eval_pulled

def circuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) MemoryMsg unit where
  name := "sp1.native.memory.check.ram"
  main := main target
  elaborated := elaborated target
  Spec input _ _ := Spec target input
  ProverAssumptions input _ _ := Spec target input
  channelsWithRequirements := [(FinalMemoryValue.channel true).toRaw]
  soundness := by
    circuit_proof_start [InitialMemoryRead.circuitNamed, Gadgets.Equality.circuit,
      FinalMemoryValue.channel, MemoryBoundary.address]
    simpa only [InitialMemoryRead.Spec, h_holds.2] using h_holds.1
  completeness := by
    circuit_proof_start [InitialMemoryRead.circuitNamed, Gadgets.Equality.circuit,
      FinalMemoryValue.channel, MemoryBoundary.address]
    refine ⟨⟨h_assumptions.1, h_assumptions.2.1⟩, ?_⟩
    have read := h_env ⟨h_assumptions.1, h_assumptions.2.1⟩
    apply Word.eq_of_toBitVec64_eq read.2.2.1 h_assumptions.2.2.1
    exact read.2.2.2.trans h_assumptions.2.2.2.symm

instance (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Decidable (Spec target record) := by
  unfold Spec Word.isU64
  infer_instance

/-- Validate the complete target record; the circuit generates its byte-read witnesses. -/
def populate? (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Option (MemoryMsg (ZMod p)) :=
  if Spec target record then some record else none

omit [Fact (2 ^ 17 < p)] in
theorem populate?_isSome_iff (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) :
    (populate? target record).isSome = true ↔ Spec target record := by
  unfold populate?
  split <;> simp_all

theorem populate?_sound (target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (input : MemoryMsg (ZMod p)) (found : populate? target record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit target).ProverAssumptions input data hint ∧ input = record := by
  unfold populate? at found
  split at found
  next valid =>
    obtain rfl := Option.some.inj found
    exact ⟨valid, rfl⟩
  next invalid => contradiction

end SP1Clean.FinalRamValue
