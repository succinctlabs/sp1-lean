import SP1Clean.Native.Operations.HintQueueBoundary
import SP1Clean.Native.Operations.HostCommitEndpoint
import SP1Clean.Native.Operations.HostExitBoundary

/-! # Native verifier boundaries for hints, commitment banks, and terminal status

The boundary circuits run as true Clean subcircuits. Their fixed source and
target values are statement parameters, while the bank terminals remain physical tables.
Clean's public verifier preserves every boundary interaction and enforces the two raw assertions
through a separate check channel. It allocates no physical rows or private witness cells.
-/

namespace SP1Clean.HostBoundary

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def main (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (_ : Var unit (ZMod p)) :
    Circuit (ZMod p) Unit := do
  let _ ← HostHintQueueBoundary.circuit hints queueFinal ()
  let _ ← HostCommitEndpoint.circuit false (source false) (target false) ()
  let _ ← HostCommitEndpoint.circuit true (source true) (target true) ()
  let _ ← HostExitBoundary.circuit sourceExit targetExit ()
  pure ()

def circuit (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) :
    GeneralFormalCircuit (ZMod p) unit unit where
  main := main hints queueFinal source target sourceExit targetExit
  Spec _ _ _ := hints.length < 2 ^ 48 ∧ (sourceExit = none ∨ sourceExit = targetExit)
  ProverAssumptions _ _ _ := hints.length < 2 ^ 48 ∧ (sourceExit = none ∨ sourceExit = targetExit)
  channelsWithRequirements := [HostHintQueue.stateChannel.toRaw,
    (HostCommitChip.stateChannel false).toRaw, (HostCommitChip.stateChannel true).toRaw,
    HostExitBoundary.channel.toRaw]
  soundness := by
    circuit_proof_all [main, HostHintQueueBoundary.circuit, HostCommitEndpoint.circuit, HostExitBoundary.circuit]
  completeness := by
    circuit_proof_all [main, HostHintQueueBoundary.circuit, HostCommitEndpoint.circuit, HostExitBoundary.circuit]

omit [Fact (2 ^ 25 < p)] in
theorem values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (offset : ℕ)
    (env : Environment (ZMod p)) (channel : RawChannel (ZMod p)) :
    ((main hints queueFinal source target sourceExit targetExit ()).operations offset).interactionValuesWith channel env =
      ((HostHintQueueBoundary.main hints queueFinal ()).operations offset).interactionValuesWith channel env ++
      ((HostCommitEndpoint.main false (source false) (target false) ()).operations offset).interactionValuesWith channel env ++
      ((HostCommitEndpoint.main true (source true) (target true) ()).operations offset).interactionValuesWith channel env ++
      ((HostExitBoundary.main sourceExit targetExit ()).operations offset).interactionValuesWith channel env := by
  simp only [main, Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, HostHintQueueBoundary.circuit,
    HostCommitEndpoint.circuit, HostExitBoundary.circuit, List.filter_append, List.map_append, List.append_assoc]

/-- Queue, bank, and terminal endpoints are invoked exactly once by the enclosing verifier. -/
def closed (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) : ClosedVerifier (ZMod p) where
  name := "host-boundary"
  circuit := circuit hints queueFinal source target sourceExit targetExit
  assumptions := by intros; trivial
  lookups := by
    simp only [circuit, main, circuit_norm, HostHintQueueBoundary.circuit, HostHintQueueBoundary.main, HostCommitEndpoint.circuit,
      HostCommitEndpoint.main, HostCommitBoundary.verifier, HostCommitBoundary.verifierMain,
      HostExitBoundary.circuit, HostExitBoundary.main]
  public_interactions := by
    intro interaction member env
    simp only [circuit, main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
      HostHintQueueBoundary.circuit, HostCommitEndpoint.circuit, HostExitBoundary.circuit,
      List.mem_append] at member
    rcases member with queue | firstBank | secondBank | terminal
    · exact (HostHintQueueBoundary.closed hints queueFinal).public_interactions interaction queue env
    · exact (HostCommitEndpoint.closed false (source false) (target false)).public_interactions interaction firstBank env
    · exact (HostCommitEndpoint.closed true (source true) (target true)).public_interactions interaction secondBank env
    · exact (HostExitBoundary.closed sourceExit targetExit).public_interactions interaction terminal env
  length_zero := rfl
  constraints := by
    intros
    simp only [circuit, main, circuit_norm, HostHintQueueBoundary.circuit,
      HostHintQueueBoundary.main, HostCommitEndpoint.circuit, HostCommitEndpoint.main,
      HostCommitBoundary.verifier, HostCommitBoundary.verifierMain, HostExitBoundary.circuit,
      HostExitBoundary.main, forall_eq_or_imp, Expression.eval]
  interactions := by
    intro offset env channel
    rw [show (circuit hints queueFinal source target sourceExit targetExit).main =
        main hints queueFinal source target sourceExit targetExit from rfl,
      values, values]
    exact congrArg₂ List.append
      (congrArg₂ List.append
        (congrArg₂ List.append ((HostHintQueueBoundary.closed hints queueFinal).interactions offset env channel)
          ((HostCommitEndpoint.closed false (source false) (target false)).interactions offset env channel))
        ((HostCommitEndpoint.closed true (source true) (target true)).interactions offset env channel))
      ((HostExitBoundary.closed sourceExit targetExit).interactions offset env channel)

omit [Fact (2 ^ 25 < p)] in
@[circuit_norm] theorem closed_main (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) :
    (closed hints queueFinal source target sourceExit targetExit).circuit.main =
      main hints queueFinal source target sourceExit targetExit := rfl

omit [Fact (2 ^ 25 < p)] in
/-- Raw constraints check source-queue size and preservation of an already-stopped status. -/
theorem constraints_spec (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((main hints queueFinal source target sourceExit targetExit ()).operations offset).ConstraintsHold env) :
    hints.length < 2 ^ 48 ∧ (sourceExit = none ∨ sourceExit = targetExit) := by
  simpa only [main, circuit_norm, HostHintQueueBoundary.circuit,
    HostHintQueueBoundary.main, HostCommitEndpoint.circuit, HostCommitEndpoint.main,
    HostCommitBoundary.verifier, HostCommitBoundary.verifierMain, HostExitBoundary.circuit,
    HostExitBoundary.main, forall_eq_or_imp, Expression.eval, ite_eq_left_iff,
    one_ne_zero, imp_false, not_not] using constraints

omit [Fact (2 ^ 25 < p)] in
theorem source_bound (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((main hints queueFinal source target sourceExit targetExit ()).operations offset).ConstraintsHold env) :
    hints.length < 2 ^ 48 := (constraints_spec _ _ _ _ _ _ _ _ constraints).1

omit [Fact (2 ^ 25 < p)] in
/-- Bank endpoints leave the queue channel's two fixed boundary messages unchanged. -/
theorem queue_values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main hints queueFinal source target sourceExit targetExit ()).operations offset).interactionValuesWith HostHintQueue.stateChannel.toRaw env =
      [HostHintQueue.stateChannel.pushedValue (HostHintQueueBoundary.initial hints),
        HostHintQueue.stateChannel.pulledValue queueFinal] := by
  rw [values, HostHintQueueBoundary.values, HostCommitEndpoint.values, HostCommitEndpoint.values, HostExitBoundary.values]
  simp [HostHintQueue.stateChannel, HostCommitChip.stateChannel, HostExitBoundary.channel, Channel.toRaw]

omit [Fact (2 ^ 25 < p)] in
/-- Each private bank receives precisely its own fixed source and final messages. -/
theorem bank_values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (offset : ℕ)
    (env : Environment (ZMod p)) (deferred : Bool) :
    ((main hints queueFinal source target sourceExit targetExit ()).operations offset).interactionValuesWith
      (HostCommitChip.stateChannel deferred).toRaw env =
      [(HostCommitChip.stateChannel deferred).pushedValue (HostCommitBoundary.start (source deferred)),
       (HostCommitChip.stateChannel deferred).pulledValue (HostCommitBoundary.final (target deferred))] := by
  rw [values, HostCommitEndpoint.values, HostCommitEndpoint.values, HostExitBoundary.values]
  have queue : ((HostHintQueueBoundary.main hints queueFinal ()).operations offset).interactionValuesWith
      (HostCommitChip.stateChannel deferred).toRaw env = [] := by
    cases deferred <;> simp [HostHintQueueBoundary.main, Operations.interactionValuesWith,
      Operations.interactionsWith, circuit_norm, HostHintQueue.stateChannel,
      HostCommitChip.stateChannel, Channel.toRaw]
  rw [queue]
  cases deferred <;> simp [HostCommitChip.stateChannel, HostExitBoundary.channel, Channel.toRaw]

omit [Fact (2 ^ 25 < p)] in
/-- Only the terminal subcircuit contributes to the new receipt channel. -/
theorem terminal_values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8)
    (sourceExit targetExit : Option (BitVec 32)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main hints queueFinal source target sourceExit targetExit ()).operations offset).interactionValuesWith
      HostExitBoundary.channel.toRaw env =
      [HostExitBoundary.channel.pulledIfValue (if sourceExit = none ∧ targetExit.isSome then 1 else 0)
        (HostExitBoundary.encode (targetExit.getD 0))] := by
  rw [values, HostCommitEndpoint.values, HostCommitEndpoint.values, HostExitBoundary.values]
  have queue : ((HostHintQueueBoundary.main hints queueFinal ()).operations offset).interactionValuesWith
      HostExitBoundary.channel.toRaw env = [] := by
    simp [HostHintQueueBoundary.main, Operations.interactionValuesWith, Operations.interactionsWith,
      circuit_norm, HostHintQueue.stateChannel, HostExitBoundary.channel, Channel.toRaw]
  rw [queue]
  simp [HostCommitChip.stateChannel, HostExitBoundary.channel, Channel.toRaw]

end SP1Clean.HostBoundary
