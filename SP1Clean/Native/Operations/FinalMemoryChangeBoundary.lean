import SP1Clean.Model.FinalMemoryChange
import ToClean.Air.VerifierExtension

/-! # Verifier-owned demand for every changed Memory location

The fixed demand is computed from both complete snapshots, including their sparse RAM supports.
The closed verifier adapter invokes it exactly once. No witness chooses its keys or row count.
-/

namespace SP1Clean.FinalMemoryChangeBoundary

open Circuit Air.Flat Model.Core FinalMemoryChange
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Emit a unit pull for each fixed key without allocating witness cells. -/
def main (keys : List (Key (ZMod p))) (_ : Var unit (ZMod p)) : Circuit (ZMod p) Unit :=
  forEach (Vector.ofFn fun i : Fin keys.length => keys[i.val]) fun key => channel.pull (const key)

instance elaborated (keys : List (Key (ZMod p))) :
    ElaboratedCircuit (ZMod p) unit unit (main keys) := by elaborate_circuit

/-- Fixed inventory demand; authenticity is enforced by balance in the enclosing ensemble. -/
def circuit (keys : List (Key (ZMod p))) : GeneralFormalCircuit (ZMod p) unit unit where
  main := main keys
  elaborated := elaborated keys
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  channelsWithRequirements := [channel.toRaw]
  soundness := by circuit_proof_start [channel]
  completeness := by circuit_proof_start [channel]

theorem operations (keys : List (Key (ZMod p))) (offset : ℕ) :
    (main keys ()).operations offset =
      keys.map (fun key => Operation.interact (channel.pulled (const key)).toRaw) := by
  simp only [main, forEach.operations_eq, circuit_norm]
  exact List.ofFn_getElem_eq_map keys (fun key => Operation.interact (channel.pulled (const key)).toRaw)

/-- The fixed demand retains one literal interaction per supplied key. -/
theorem raw_interactions (keys : List (Key (ZMod p))) (offset : ℕ) :
    ((main keys ()).operations offset).interactions =
      keys.map (fun key => (channel.pulled (const key)).toRaw) := by
  rw [operations]
  induction keys with
  | nil => rfl
  | cons key rest ih => simpa only [List.map_cons, Operations.interactions] using congrArg (List.cons _) ih

/-- Fixed demand contains only interactions, so it adds no assertion-channel occurrences. -/
theorem raw_constraints (keys : List (Key (ZMod p))) (offset : ℕ) :
    ((main keys ()).operations offset).constraints = [] := by
  rw [operations]
  induction keys with
  | nil => rfl
  | cons key rest ih => simpa only [List.map_cons, Operations.constraints] using ih

theorem values (keys : List (Key (ZMod p))) (offset : ℕ) (env : Environment (ZMod p))
    (selected : RawChannel (ZMod p)) :
    ((main keys ()).operations offset).interactionValuesWith selected env =
      if selected = channel.toRaw then keys.map channel.pulledValue else [] := by
  rw [operations]
  by_cases same : selected = channel.toRaw
  · subst selected
    induction keys with
    | nil => simp [Operations.interactionValuesWith, circuit_norm]
    | cons key rest ih =>
        simp only [List.map_cons, Operations.interactionValuesWith, circuit_norm,
          List.map_cons, ↓reduceIte, List.cons.injEq]
        constructor
        · exact (Channel.eval_pulled (channel := channel) (msg := const key) (env := env)).trans
            (congrArg channel.pulledValue (show eval env (const key) = key from ProvableType.eval_const))
        · simpa only [Operations.interactionValuesWith, Channel.pulled, ↓reduceIte] using ih
  · induction keys with
    | nil => simp [Operations.interactionValuesWith, circuit_norm, same]
    | cons key rest ih =>
        simpa only [List.map_cons, Operations.interactionValuesWith, circuit_norm,
          Ne.symm same, same, ↓reduceIte] using ih

/-- Fixed demand has no local assertions or lookups; its force comes entirely from balance. -/
theorem constraints_hold (keys : List (Key (ZMod p))) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main keys ()).operations offset).ConstraintsHold env := by
  rw [operations, Operations.ConstraintsHold]
  induction keys with
  | nil => simp [circuit_norm]
  | cons key rest ih => simpa [circuit_norm] using ih

/-- Invoke the canonical source-to-target change inventory exactly once in a verifier. -/
def closed (source target : MemorySnapshot) : ClosedVerifier (ZMod p) where
  name := "final-memory-change"
  circuit := circuit ((source.changes target).map encode)
  assumptions := by intros; trivial
  lookups := by
    simp only [circuit, operations]
    induction (source.changes target).map (encode (p := p)) with
    | nil => rfl
    | cons _ _ ih => exact ih
  public_interactions := by
    intro interaction member env
    simp only [circuit, raw_interactions] at member
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
    simp [circuit_norm, AbstractInteraction.Requirements, ChannelInteraction.toRaw, Channel.toRaw,
      Expression.eval]
  length_zero := by simp only [circuit, circuit_norm]
  constraints := by
    intro offset env
    simp only [circuit, operations, Operations.ConstraintsHold]
    generalize (source.changes target).map (encode (p := p)) = keys
    induction keys with
    | nil => simp [circuit_norm]
    | cons key rest ih => simpa [circuit_norm] using ih
  interactions := by
    intro offset env selected
    exact (values _ offset env selected).trans (values _ 0 _ selected).symm

/-- The exactly-once fixed demand contributes no additional assertion or lookup premise. -/
theorem closed_constraints (source target : MemorySnapshot) (data : ProverData (ZMod p)) :
    (closed source target).singleton.Constraints data := by
  rw [ClosedVerifier.singleton_constraints]
  exact constraints_hold ((source.changes target).map encode) 0
    (Environment.fromInput (Input := unit) () data)

end SP1Clean.FinalMemoryChangeBoundary
