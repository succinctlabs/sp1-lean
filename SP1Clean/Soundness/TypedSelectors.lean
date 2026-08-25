import SP1Clean.Soundness.SP1Ensemble

/-! # Selector binary facts from physical chip constraints

The active-row selector is structural AIR data, not execution semantics.  This module derives it from
the shallow top-level gate of each actual Clean chip, independently of the chip's semantic `Spec`.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The physical constraints of a circuit force the selector exposed by its row view to be binary. -/
def CircuitSelectorBinary {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ data physical,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    component.operations.ConstraintsHold env →
      (view (component.rowInput env) (component.rowOutput env)).is_real = 0 ∨
        (view (component.rowInput env) (component.rowOutput env)).is_real = 1

/-- A supported descriptor's physical constraints force the selector of the row decoded from those
same physical columns to be binary. -/
def SelectorConstraintShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    let env := Environment.fromArray physical data
    chip.table.operations.ConstraintsHold env →
      (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real = 0 ∨
        (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real = 1

/-- The shallow selector contract at the typed `main` boundary.  Every supported `RowView` obtains
its gate from the typed input, so neither the circuit output nor the completed circuit's proof fields
belong in this local AIR fact. -/
structure MainSelectorBinary {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (main : Var Input (ZMod p) → Circuit (ZMod p) (Var Output (ZMod p)))
    (selector : Input (ZMod p) → ZMod p) : Prop where
  binary : ∀ input offset env,
    ConstraintsHold.Shallow env ((main input).operations offset) →
      selector (Eval.eval env input) = 0 ∨ selector (Eval.eval env input) = 1

omit [Fact (2 ^ 24 < p)] in
/-- Flat constraint satisfaction exposes the shallow assertions of the original typed row circuit. -/
theorem shallowConstraints_of_componentConstraints {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (env : Environment (ZMod p))
    (constraints : (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ConstraintsHold.Shallow env
      ((circuit.main (varFromOffset Input 0)).operations (size Input)) := by
  apply FlatOperation.shallowConstraints_of_constraintsHoldFlat
  apply Circuit.constraintsHold_toFlat_iff.mpr
  exact (Component.constraintsHold_iff env).mp constraints

/-- Add's shallow top-level gate forces the evaluated input selector to be binary.  Stating the
lemma against `main` (rather than normalizing the completed `GeneralFormalCircuit` record) keeps this
local AIR fact independent of the large soundness/completeness proof fields. -/
theorem AddChip.selectorBinary_of_shallow
    (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((AddChip.main input).operations offset)) :
    Expression.eval env input.is_real = 0 ∨ Expression.eval env input.is_real = 1 := by
  simp only [AddChip.main, circuit_norm] at shallow
  have inputRealEq : (ProvableStruct.eval env input).is_real =
      Expression.eval env input.is_real := by
    calc
      _ = (Eval.eval env input).is_real :=
        congrArg (fun value => value.is_real) (ProvableStruct.eval_eq_eval env input).symm
      _ = Expression.eval env input.is_real := by simp only [circuit_norm]
  rw [inputRealEq] at shallow
  exact bool_of_mul_pred shallow

omit [Fact (2 ^ 24 < p)] in
/-- Evaluation of Add's input selector, exposed once for downstream typed-interaction proofs. -/
theorem AddChip.eval_isReal (env : Environment (ZMod p))
    (input : Var AddChip.Inputs (ZMod p)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simp only [circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- Transport a cheap `main`-local selector proof to the completed circuit without unfolding the
completed record's proof fields. -/
theorem circuitSelectorBinary_of_main {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Input (ZMod p) → ZMod p)
    (selector_eq : ∀ input output, (view input output).is_real = selector input)
    (contract : MainSelectorBinary circuit.main selector) :
    CircuitSelectorBinary circuit view := by
  unfold CircuitSelectorBinary
  intro data physical
  dsimp only
  intro constraints
  let env := Environment.fromArray physical data
  let input : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  have shallow := shallowConstraints_of_componentConstraints circuit env constraints
  have binary := contract.binary input offset env shallow
  have inputEq : Eval.eval env input = (⟨circuit⟩ : Component (ZMod p)).rowInput env := by
    exact eval_varFromOffset_valueFromOffset Input 0 env
  rw [inputEq] at binary
  simpa only [selector_eq] using binary

/-- A circuit-level selector theorem transports definitionally to its supported descriptor. -/
theorem selectorConstraintShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (id : InstructionChipId)
    (shape : @CircuitSelectorBinary p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    SelectorConstraintShape ⟨id, kind, circuit, spec_eq⟩ := by
  exact shape

theorem AddChip.mainSelectorBinary : @MainSelectorBinary p _ AddChip.Inputs AddChip.Columns
    inferInstance inferInstance AddChip.main (fun input => input.is_real) := by
  constructor
  intro input offset env shallow
  have binary := AddChip.selectorBinary_of_shallow input offset env shallow
  change (Eval.eval env input).is_real = 0 ∨ (Eval.eval env input).is_real = 1
  rw [AddChip.eval_isReal]
  exact binary

/-- Boilerplate for chips whose row selector is the input's `is_real` field and whose shallow tail
contains that field's standard boolean gate. -/
local macro "simpleInputSelectorBinary" main:term : tactic =>
  `(tactic| (
    constructor
    intro input offset env shallow
    change (Eval.eval env input).is_real = 0 ∨ (Eval.eval env input).is_real = 1
    simp only [$main:term, circuit_norm] at shallow
    rw [← ProvableStruct.eval_eq_eval env input] at shallow
    exact bool_of_mul_pred (by tauto)))

/-- Boilerplate for chips whose `is_real` boolean gate is the *first* shallow assert of `main`.
Extracting the gate by list position keeps the proof from unfolding the whole chip circuit. -/
local macro "headGateSelectorBinary" main:term : tactic =>
  `(tactic| (
    constructor
    intro input offset env shallow
    have allConstraints := (constraintsHold_shallow_iff_forall_mem.mp shallow).1
    have gateMem : input.is_real * (input.is_real - 1) ∈
        (($main:term input).operations offset).shallowConstraints := by
      change input.is_real * (input.is_real - 1) ∈
        input.is_real * (input.is_real - 1) :: _
      exact List.mem_cons_self
    have binary : Expression.eval env input.is_real = 0 ∨
        Expression.eval env input.is_real = 1 := by
      apply bool_of_mul_pred
      simpa only [circuit_norm] using allConstraints _ gateMem
    have inputRealEq : (Eval.eval env input).is_real = Expression.eval env input.is_real := by
      simp only [circuit_norm]
    rw [inputRealEq]
    exact binary))

/-- As `headGateSelectorBinary`, for chips whose gate is the *second* shallow assert. -/
local macro "secondGateSelectorBinary" main:term : tactic =>
  `(tactic| (
    constructor
    intro input offset env shallow
    have allConstraints := (constraintsHold_shallow_iff_forall_mem.mp shallow).1
    have gateMem : input.is_real * (input.is_real - 1) ∈
        (($main:term input).operations offset).shallowConstraints := by
      change input.is_real * (input.is_real - 1) ∈
        _ :: input.is_real * (input.is_real - 1) :: _
      exact List.mem_cons_of_mem _ List.mem_cons_self
    have binary : Expression.eval env input.is_real = 0 ∨
        Expression.eval env input.is_real = 1 := by
      apply bool_of_mul_pred
      simpa only [circuit_norm] using allConstraints _ gateMem
    have inputRealEq : (Eval.eval env input).is_real = Expression.eval env input.is_real := by
      simp only [circuit_norm]
    rw [inputRealEq]
    exact binary))

theorem AddiChip.mainSelectorBinary :
    MainSelectorBinary (p := p) AddiChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary AddiChip.main

theorem AddwChip.mainSelectorBinary :
    MainSelectorBinary (p := p) AddwChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary AddwChip.main

theorem SubChip.mainSelectorBinary :
    MainSelectorBinary (p := p) SubChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary SubChip.main

theorem SubwChip.mainSelectorBinary :
    MainSelectorBinary (p := p) SubwChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary SubwChip.main

theorem BitwiseChip.mainSelectorBinary :
    MainSelectorBinary (p := p) BitwiseChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary BitwiseChip.main

theorem LtChip.mainSelectorBinary :
    MainSelectorBinary (p := p) LtChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary LtChip.main

theorem ShiftLeftChip.mainSelectorBinary :
    MainSelectorBinary (p := p) ShiftLeftChip.main (fun input => input.is_real) := by
  headGateSelectorBinary ShiftLeftChip.main

theorem ShiftRightChip.mainSelectorBinary :
    MainSelectorBinary (p := p) ShiftRightChip.main (fun input => input.is_real) := by
  headGateSelectorBinary ShiftRightChip.main

theorem JalChip.mainSelectorBinary :
    MainSelectorBinary (p := p) JalChip.main (fun input => input.is_real) := by
  secondGateSelectorBinary JalChip.main

theorem JalrChip.mainSelectorBinary :
    MainSelectorBinary (p := p) JalrChip.main (fun input => input.is_real) := by
  secondGateSelectorBinary JalrChip.main

theorem BranchChip.mainSelectorBinary :
    MainSelectorBinary (p := p) BranchChip.main (fun input => input.is_real) := by
  constructor
  intro input offset env shallow
  let flagSum : Expression (ZMod p) :=
    var { index := offset } + var { index := offset + 1 } + var { index := offset + 2 } +
      var { index := offset + 3 } + var { index := offset + 4 } + var { index := offset + 5 }
  have allConstraints := (constraintsHold_shallow_iff_forall_mem.mp shallow).1
  have linkMem : input.is_real - flagSum ∈
      ((BranchChip.main input).operations offset).shallowConstraints := by
    change (input.is_real - flagSum) ∈ (input.is_real - flagSum) :: _
    exact List.mem_cons_self
  have gateMem : flagSum * (flagSum - 1) ∈
      ((BranchChip.main input).operations offset).shallowConstraints := by
    change (flagSum * (flagSum - 1)) ∈
      (input.is_real - flagSum) :: (flagSum * (flagSum - 1)) :: _
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have link := allConstraints _ linkMem
  have gate := allConstraints _ gateMem
  simp only [circuit_norm] at link gate
  rw [← ProvableStruct.eval_eq_eval env input] at link
  rcases bool_of_mul_pred gate with selectorZero | selectorOne
  · left
    linear_combination link + selectorZero
  · right
    linear_combination link + selectorOne

theorem UTypeChip.mainSelectorBinary :
    MainSelectorBinary (p := p) UTypeChip.main (fun input => input.is_real) := by
  secondGateSelectorBinary UTypeChip.main

theorem LoadByteChip.mainSelectorBinary : MainSelectorBinary (p := p) LoadByteChip.main
    LoadByteChip.isReal := by
  constructor
  intro input offset env shallow
  simp only [LoadByteChip.main, circuit_norm] at shallow
  rw [← ProvableStruct.eval_eq_eval env input] at shallow
  simpa only [LoadByteChip.isReal] using bool_of_mul_pred shallow.2

theorem LoadHalfChip.mainSelectorBinary : MainSelectorBinary (p := p) LoadHalfChip.main
    LoadHalfChip.isReal := by
  constructor
  intro input offset env shallow
  simp only [LoadHalfChip.main, circuit_norm] at shallow
  rw [← ProvableStruct.eval_eq_eval env input] at shallow
  simpa only [LoadHalfChip.isReal] using bool_of_mul_pred shallow

theorem LoadWordChip.mainSelectorBinary : MainSelectorBinary (p := p) LoadWordChip.main
    LoadWordChip.isReal := by
  constructor
  intro input offset env shallow
  simp only [LoadWordChip.main, circuit_norm] at shallow
  rw [← ProvableStruct.eval_eq_eval env input] at shallow
  simpa only [LoadWordChip.isReal] using bool_of_mul_pred shallow

theorem LoadDoubleChip.mainSelectorBinary :
    MainSelectorBinary (p := p) LoadDoubleChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary LoadDoubleChip.main

theorem LoadX0Chip.mainSelectorBinary : MainSelectorBinary (p := p) LoadX0Chip.main
    LoadX0Chip.isReal := by
  constructor
  intro input offset env shallow
  simp only [LoadX0Chip.main, circuit_norm] at shallow
  rw [← ProvableStruct.eval_eq_eval env input] at shallow
  simpa only [LoadX0Chip.isReal] using bool_of_mul_pred shallow

theorem StoreByteChip.mainSelectorBinary :
    MainSelectorBinary (p := p) StoreByteChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary StoreByteChip.main

theorem StoreHalfChip.mainSelectorBinary :
    MainSelectorBinary (p := p) StoreHalfChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary StoreHalfChip.main

theorem StoreWordChip.mainSelectorBinary :
    MainSelectorBinary (p := p) StoreWordChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary StoreWordChip.main

theorem StoreDoubleChip.mainSelectorBinary :
    MainSelectorBinary (p := p) StoreDoubleChip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary StoreDoubleChip.main

theorem MulChip.mainSelectorBinary :
    MainSelectorBinary (p := p) MulChip.main (fun input => input.is_real) := by
  constructor
  intro input offset env shallow
  have gateMem : input.is_real * (input.is_real - 1) ∈
      ((MulChip.main input).operations offset).shallowConstraints := by
    simp only [MulChip.main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      subcircuitWithAssertion, assertion, assertZero,
      Operations.localLength, Operations.shallowConstraints, List.mem_cons, List.not_mem_nil,
      or_false, circuit_norm]
  have gateZero :=
    (constraintsHold_shallow_iff_forall_mem.mp shallow).1 _ gateMem
  change (Eval.eval env input).is_real = 0 ∨ (Eval.eval env input).is_real = 1
  rw [MulChip.eval_inputs]
  apply bool_of_mul_pred
  simpa only [circuit_norm] using gateZero

omit [Fact (2 ^ 24 < p)] in
/-- Any shallow (top-level) assert of an operations list is among its deep constraints. -/
private lemma mem_constraints_of_mem_shallowConstraints {e : Expression (ZMod p)}
    {ops : Operations (ZMod p)} (h : e ∈ ops.shallowConstraints) : e ∈ ops.constraints :=
  ((Operations.forall_constraints_iff (motive := (· ∈ ops.constraints))).mp
    (fun _ he => he)).1 e h

omit [Fact (2 ^ 24 < p)] in
/-- Membership transport into a composed `FormalAssertion` subcircuit's flat constraint list. -/
private lemma mem_flatConstraints_of_assertion {Input : TypeMap} [ProvableType Input]
    {circuit : FormalAssertion (ZMod p) Input} {input : Var Input (ZMod p)} {n : ℕ}
    {e : Expression (ZMod p)}
    (h : e ∈ ((circuit.main input).operations n).constraints) :
    e ∈ FlatOperation.constraints (circuit.toSubcircuit n input).ops.toFlat := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]
  exact h

/-- The selector gate `is_real·(is_real−1)` (`E355`) sits in the `DivRemCore` cluster's own-assert
tail — a shallow assert of the gadget's `main`, hence one of its deep constraints. -/
private lemma divRemCore_isReal_gate_mem_constraints
    (cols : Var DivRemChip.Columns (ZMod p)) (n : ℕ) :
    cols.is_real * (cols.is_real - 1) ∈ ((DivRemCore.main cols).operations n).constraints := by
  apply mem_constraints_of_mem_shallowConstraints
  change cols.is_real * (cols.is_real - 1) ∈ DivRemChip.ownAsserts cols ++ _
  exact List.mem_append_left _ (DivRemChip.isReal_gate_mem_ownAsserts cols)

/-- The selector gate is a deep constraint of the chip `main`: its deep constraint list is
`CPUState ++ (RTypeReader ++ (Compare ++ (Core ++ (RegisterWrite ++ []))))`, and the gate lives in
the `DivRemCore` segment. Stated over an abstract `input` so the definitional peel never
instantiates the chip's concrete `varFromOffset` row. -/
private lemma divRemChip_isReal_gate_mem_main_constraints
    (input : Var DivRemChip.Inputs (ZMod p)) (n : ℕ) :
    input.is_real * (input.is_real - 1) ∈
      ((DivRemChip.main input).operations n).constraints := by
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact mem_flatConstraints_of_assertion (divRemCore_isReal_gate_mem_constraints _ _)

/-- DivRem's selector booleanity from the physical row constraints. The boolean gate is no longer
a shallow assert of the chip `main` — it moved into the `DivRemCore` whole-row assertion cluster —
so this bypasses the `MainSelectorBinary` shallow interface and extracts the gate from the deep
constraint list through the `DivRemCore` subcircuit. -/
theorem DivRemChip.circuitSelectorBinary :
    CircuitSelectorBinary (p := p) DivRemChip.circuit DivRemChip.rowView := by
  unfold CircuitSelectorBinary
  intro data physical
  dsimp only
  intro constraints
  have deep : ∀ e ∈ ((DivRemChip.main (varFromOffset DivRemChip.Inputs 0)).operations
      (size DivRemChip.Inputs)).constraints,
      Environment.fromArray physical data e = 0 :=
    ((Component.constraintsHold_iff (Environment.fromArray physical data)).mp constraints).1
  have gate : Environment.fromArray physical data
      ((varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p)).is_real *
        ((varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p)).is_real - 1)) = 0 :=
    deep _ (divRemChip_isReal_gate_mem_main_constraints _ _)
  have binary : Expression.eval (Environment.fromArray physical data)
      (varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p)).is_real = 0 ∨
      Expression.eval (Environment.fromArray physical data)
        (varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p)).is_real = 1 := by
    apply bool_of_mul_pred
    simpa only [circuit_norm] using gate
  have selEq : ∀ (i : DivRemChip.Inputs (ZMod p)) (o : DivRemChip.Columns (ZMod p)),
      (DivRemChip.rowView i o).is_real = i.is_real := fun _ _ => rfl
  have inputEq : Eval.eval (Environment.fromArray physical data)
      (varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p))
      = (⟨DivRemChip.circuit⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data) :=
    eval_varFromOffset_valueFromOffset DivRemChip.Inputs 0 _
  have evalReal : (Eval.eval (Environment.fromArray physical data)
      (varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p))).is_real
      = Expression.eval (Environment.fromArray physical data)
        (varFromOffset DivRemChip.Inputs 0 : Var DivRemChip.Inputs (ZMod p)).is_real := by
    simp only [circuit_norm]
  rw [selEq, ← inputEq, evalReal]
  exact binary

theorem AluX0Chip.mainSelectorBinary :
    MainSelectorBinary (p := p) AluX0Chip.main (fun input => input.is_real) := by
  simpleInputSelectorBinary AluX0Chip.main

/-- Registry-case boilerplate: install the descriptor's retained dependent instances, transport its
typed shallow contract to the physical circuit, and identify the `RowView` selector by reflexivity. -/
local macro "selectorRegistryCase " kind:term ", " selector:term ", " contract:term : tactic =>
  `(tactic| (
    letI := ($kind:term).provableInputs
    letI := ($kind:term).provableCols
    apply selectorConstraintShape_of_circuit
    apply circuitSelectorBinary_of_main (selector := $selector:term)
    · intros
      rfl
    · exact $contract:term))

/-- Every descriptor in the single supported-machine registry derives its selector from the actual
shallow AIR constraints of the circuit retained by that descriptor. -/
theorem supportedChip_selectorConstraintShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : SelectorConstraintShape chip := by
  fin_cases chipMem
  · selectorRegistryCase (AddChip.kind (p := p)), (fun input => input.is_real),
      (AddChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (AddiChip.kind (p := p)), (fun input => input.is_real),
      (AddiChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (AddwChip.kind (p := p)), (fun input => input.is_real),
      (AddwChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (SubChip.kind (p := p)), (fun input => input.is_real),
      (SubChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (SubwChip.kind (p := p)), (fun input => input.is_real),
      (SubwChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (BitwiseChip.kind (p := p)), (fun input => input.is_real),
      (BitwiseChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (LtChip.kind (p := p)), (fun input => input.is_real),
      (LtChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (ShiftLeftChip.kind (p := p)), (fun input => input.is_real),
      (ShiftLeftChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (ShiftRightChip.kind (p := p)), (fun input => input.is_real),
      (ShiftRightChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (JalChip.kind (p := p)), (fun input => input.is_real),
      (JalChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (JalrChip.kind (p := p)), (fun input => input.is_real),
      (JalrChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (BranchChip.kind (p := p)), (fun input => input.is_real),
      (BranchChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (UTypeChip.kind (p := p)), (fun input => input.is_real),
      (UTypeChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (LoadByteChip.kind (p := p)), LoadByteChip.isReal,
      (LoadByteChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (LoadHalfChip.kind (p := p)), LoadHalfChip.isReal,
      (LoadHalfChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (LoadWordChip.kind (p := p)), LoadWordChip.isReal,
      (LoadWordChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (LoadDoubleChip.kind (p := p)), (fun input => input.is_real),
      (LoadDoubleChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (LoadX0Chip.kind (p := p)), LoadX0Chip.isReal,
      (LoadX0Chip.mainSelectorBinary (p := p))
  · selectorRegistryCase (StoreByteChip.kind (p := p)), (fun input => input.is_real),
      (StoreByteChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (StoreHalfChip.kind (p := p)), (fun input => input.is_real),
      (StoreHalfChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (StoreWordChip.kind (p := p)), (fun input => input.is_real),
      (StoreWordChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (StoreDoubleChip.kind (p := p)), (fun input => input.is_real),
      (StoreDoubleChip.mainSelectorBinary (p := p))
  · selectorRegistryCase (MulChip.kind (p := p)), (fun input => input.is_real),
      (MulChip.mainSelectorBinary (p := p))
  · -- DivRem: the gate is inside the `DivRemCore` subcircuit, so the shallow `MainSelectorBinary`
    -- route does not apply; use the direct deep-constraints theorem.
    letI := (DivRemChip.kind (p := p)).provableInputs
    letI := (DivRemChip.kind (p := p)).provableCols
    apply selectorConstraintShape_of_circuit
    exact DivRemChip.circuitSelectorBinary (p := p)
  · selectorRegistryCase (AluX0Chip.kind (p := p)), (fun input => input.is_real),
      (AluX0Chip.mainSelectorBinary (p := p))

/-- A canonical typed decoded row inherits selector booleanity from its retained descriptor and the
constraints of that exact physical row. -/
theorem DecodedInstructionRow.selectorBinary_of_constraints
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    (decoded.toChipRow data).is_real = 0 ∨ (decoded.toChipRow data).is_real = 1 := by
  have binary := supportedChip_selectorConstraintShape decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem) data decoded.physical constraints
  exact binary

/-- Witness constraints alone discharge selector booleanity for every canonical instruction row. -/
theorem witness_decodedInstructionRows_selectorBinary
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real = 0 ∨
        (decoded.toChipRow witness.data).is_real = 1 := by
  intro decoded decodedMem
  exact decoded.selectorBinary_of_constraints witness.data witness.tables decodedMem
    (decodedInstructionRow_constraints witness constraints decoded decodedMem)

end SP1Clean.Soundness
