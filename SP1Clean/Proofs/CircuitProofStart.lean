import Clean.Utils.Tactics.CircuitProofStart

/-! # Proof-start variants for large circuits

`circuit_proof_start_early_struct` reuses Clean's standard introduction core and normal forms, but
destructures input structs before unfolding a large monadic `main`.  This avoids repeatedly scanning
the fully expanded Shift-chip constraint tree while producing the same local names and hypotheses.
It is intentionally a narrow proof-elaboration optimization, not a second circuit semantics. -/

open Lean Elab Tactic

namespace SP1Clean.CircuitNormalization

open Circuit

variable {F : Type} [FiniteField F]

/-!
Clean already derives the explicit operations, length, and output of `witnessNative`; these three
lemmas merely expose those existing class fields to `circuit_norm`.  They are candidates for
upstream Clean and carry no independent witness representation or semantics.
-/

@[circuit_norm] lemma witnessNative_operations_eq
    {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var]
    (compute : ProverEnvironment F → value F) (offset : ℕ) :
    (witnessNative (F := F) (var := var) compute).operations offset =
      [.witness (size value) (.nativeValue compute)] :=
  ExplicitCircuits.operations_eq compute offset

@[circuit_norm] lemma witnessNative_localLength_eq
    {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var]
    (compute : ProverEnvironment F → value F) (offset : ℕ) :
    (witnessNative (F := F) (var := var) compute).localLength offset = size value :=
  ExplicitCircuits.localLength_eq compute offset

@[circuit_norm] lemma witnessNative_output_eq
    {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var]
    (compute : ProverEnvironment F → value F) (offset : ℕ) :
    (witnessNative (F := F) (var := var) compute).output offset =
      inst.var_eq ▸ varFromOffset value offset :=
  ExplicitCircuits.output_eq compute offset

/-- Pair form used while reducing monadic binds; assembled from the same explicit-circuit fields. -/
@[circuit_norm] lemma witnessNative_apply_eq
    {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var]
    (compute : ProverEnvironment F → value F) (offset : ℕ) :
    witnessNative (F := F) (var := var) compute offset =
      (inst.var_eq ▸ varFromOffset value offset,
        [.witness (size value) (.nativeValue compute)]) :=
  Prod.ext (ExplicitCircuits.output_eq compute offset)
    (ExplicitCircuits.operations_eq compute offset)

end SP1Clean.CircuitNormalization

private def tryTactic (tactic : TSyntax `tactic) : TacticM Unit := do
  try evalTactic tactic catch _ => pure ()

/-- Clean's standard proof start with `provable_struct_simp` moved before `main` expansion. -/
elab "circuit_proof_start_early_struct" : tactic => do
  circuitProofStartCore
  tryTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `input_var):ident))
  tryTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `input):ident))
  tryTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `h_input):ident))

  tryTactic (← `(tactic| dsimp only [$(mkIdent `Assumptions):ident] at *))
  tryTactic (← `(tactic| dsimp only [$(mkIdent `Spec):ident] at *))
  tryTactic (← `(tactic| dsimp only [$(mkIdent `ProverAssumptions):ident] at *))
  tryTactic (← `(tactic| dsimp only [$(mkIdent `ProverSpec):ident] at *))
  tryTactic (← `(tactic| dsimp +instances only [$(mkIdent `elaborated):ident] at *))

  tryTactic (← `(tactic| dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *))
  tryTactic (← `(tactic| provable_struct_simp))

  tryTactic (← `(tactic| dsimp +instances only [$(mkIdent `main):ident] at *))
  tryTactic (← `(tactic| dsimp only [ElaboratedCircuit.withData, ElaboratedCircuit.output] at *))

  tryTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `h_input):ident))
  tryTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `h_assumptions):ident))
  tryTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident]
    at $(mkIdent `h_holds):ident))
  tryTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident]
    at $(mkIdent `h_env):ident))
  tryTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident]))
  tryTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `h_spec):ident))

  tryTactic (← `(tactic| dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *))
