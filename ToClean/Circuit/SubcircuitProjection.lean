module

public import Clean.Circuit.Subcircuit
public import Clean.Circuit.Loops

/-! # Assertion and lookup lists across a general subcircuit boundary

Clean already exposes `GeneralFormalCircuit.toSubcircuit_interactions`. The corresponding
assertion, lookup, and full flat-operation equalities are missing. These companions cover
ordinary, hint-bearing, and assertion subcircuits, letting a component extension preserve
the original algebra without unfolding a proof-bearing subcircuit inside its consumer. They are
intended for the same upstream module and require no application-specific assumptions.
Flattening and loop projections compose these lists without duplicating normalization in consumers.
-/

@[expose] public section

variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- Flattening discards a general subcircuit's proof-bearing wrapper. -/
theorem GeneralFormalCircuit.toSubcircuit_toFlat
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    (circuit.toSubcircuit offset input).ops.toFlat = (circuit.main input |>.operations offset).toFlat := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

/-- The same flattening equation for a formal assertion, without unfolding its proof fields. -/
theorem FormalAssertion.toSubcircuit_toFlat
    (circuit : FormalAssertion F Input) (input : Var Input F) (offset : ℕ) :
    (circuit.toSubcircuit offset input).ops.toFlat = (circuit.main input |>.operations offset).toFlat := by
  simp only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat]

/-- Flattening a formal circuit retains the complete original operation list. -/
theorem FormalCircuit.toSubcircuit_toFlat
    (circuit : FormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    (circuit.toSubcircuit offset input).ops.toFlat = (circuit.main input |>.operations offset).toFlat := by
  simp only [FormalCircuit.toSubcircuit, Operations.toNested_toFlat]

/-- Fixed lookups survive a formal-circuit boundary without inspecting its proof fields. -/
@[circuit_norm] theorem FormalCircuit.toSubcircuit_lookups
    (circuit : FormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    FlatOperation.lookups (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.lookups) := by
  rw [FormalCircuit.toSubcircuit_toFlat, Operations.lookups_toFlat]

/-- Fixed lookups survive a formal assertion's subcircuit wrapper. -/
@[circuit_norm] theorem FormalAssertion.toSubcircuit_lookups
    (circuit : FormalAssertion F Input) (input : Var Input F) (offset : ℕ) :
    FlatOperation.lookups (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.lookups) := by
  rw [FormalAssertion.toSubcircuit_toFlat, Operations.lookups_toFlat]

section WithHint

variable {HintInput HintOutput : TypeMap} [CircuitType HintInput] [CircuitType HintOutput]

/-- A hint-bearing subcircuit has the same flattened operations as its underlying main circuit. -/
theorem GeneralFormalCircuit.WithHint.toSubcircuit_toFlat
    (circuit : GeneralFormalCircuit.WithHint F HintInput HintOutput)
    (input : Var HintInput F) (offset : ℕ) :
    (circuit.toSubcircuit offset input).ops.toFlat = (circuit.main input |>.operations offset).toFlat := by
  simp only [GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

/-- Hint-bearing wrappers preserve every fixed lookup occurrence and its original table. -/
theorem GeneralFormalCircuit.WithHint.toSubcircuit_lookups
    (circuit : GeneralFormalCircuit.WithHint F HintInput HintOutput)
    (input : Var HintInput F) (offset : ℕ) :
    FlatOperation.lookups (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.lookups) := by
  rw [GeneralFormalCircuit.WithHint.toSubcircuit_toFlat, Operations.lookups_toFlat]

end WithHint

@[circuit_norm] theorem GeneralFormalCircuit.toSubcircuit_constraints
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    FlatOperation.constraints (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.constraints) := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat]

@[circuit_norm] theorem GeneralFormalCircuit.toSubcircuit_lookups
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    FlatOperation.lookups (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.lookups) := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Operations.lookups_toFlat]

/-- Assertions survive a formal-circuit boundary without inspecting its proof fields. -/
@[circuit_norm] theorem FormalCircuit.toSubcircuit_constraints
    (circuit : FormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    FlatOperation.constraints (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.constraints) := by
  rw [FormalCircuit.toSubcircuit_toFlat, Operations.constraints_toFlat]

/-- A formal assertion contributes the assertion list of its underlying circuit. -/
@[circuit_norm] theorem FormalAssertion.toSubcircuit_constraints
    (circuit : FormalAssertion F Input) (input : Var Input F) (offset : ℕ) :
    FlatOperation.constraints (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.constraints) := by
  rw [FormalAssertion.toSubcircuit_toFlat, Operations.constraints_toFlat]

@[circuit_norm] theorem Operations.constraints_flatten
    {F : Type} [FiniteField F] (opss : List (Operations F)) :
    Operations.constraints opss.flatten = (opss.map Operations.constraints).flatten := by
  induction opss with
  | nil => rfl
  | cons ops opss ih =>
      simp only [List.flatten_cons, Operations.constraints_append, List.map_cons,
        List.flatten_cons, ih]

@[circuit_norm] theorem Operations.lookups_flatten
    {F : Type} [FiniteField F] (opss : List (Operations F)) :
    Operations.lookups opss.flatten = (opss.map Operations.lookups).flatten := by
  induction opss with
  | nil => rfl
  | cons ops opss ih =>
      simp only [List.flatten_cons, Operations.lookups_append, List.map_cons,
        List.flatten_cons, ih]

/-- Mapping a fixed range preserves each iteration's lookup occurrences. -/
@[circuit_norm] theorem Circuit.mapFinRange_lookups
    {F : Type} [FiniteField F] {β : Type} {m : ℕ} [NeZero m]
    (body : Fin m → Circuit F β) (constant : Circuit.ConstantLength body) (offset : ℕ) :
    ((Circuit.mapFinRange m body constant).operations offset).lookups =
      (List.ofFn fun (i : Fin m) =>
        ((body i).operations (offset + i * (body 0).localLength)).lookups).flatten := by
  rw [Circuit.mapFinRange.operations_eq, Operations.lookups_flatten, List.map_ofFn]
  rfl

@[circuit_norm] theorem Circuit.forEach_constraints
    {F : Type} [FiniteField F] {α : Type} {m : ℕ} [Inhabited α]
    (xs : Vector α m) (body : α → Circuit F Unit) (constant : Circuit.ConstantLength body)
    (offset : ℕ) :
    ((Circuit.forEach xs body constant).operations offset).constraints =
      (List.ofFn fun (i : Fin m) =>
        ((body xs[i]).operations
          (offset + i * (body default).localLength)).constraints).flatten := by
  rw [Circuit.forEach.operations_eq, Operations.constraints_flatten, List.map_ofFn]
  rfl

@[circuit_norm] theorem Circuit.forEach_lookups
    {F : Type} [FiniteField F] {α : Type} {m : ℕ} [Inhabited α]
    (xs : Vector α m) (body : α → Circuit F Unit) (constant : Circuit.ConstantLength body)
    (offset : ℕ) :
    ((Circuit.forEach xs body constant).operations offset).lookups =
      (List.ofFn fun (i : Fin m) =>
        ((body xs[i]).operations
          (offset + i * (body default).localLength)).lookups).flatten := by
  rw [Circuit.forEach.operations_eq, Operations.lookups_flatten, List.map_ofFn]
  rfl
