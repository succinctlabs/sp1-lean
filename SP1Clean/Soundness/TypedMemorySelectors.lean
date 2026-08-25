import SP1Clean.Soundness.TypedSelectors
import SP1Clean.Soundness.TypedMemory

/-! # Memory multiplicities are gated by the physical row selector

Memory balance is useful as a permutation only when every interaction has signed multiplicity in
`{-1, 0, 1}`, and padding rows must contribute no active message.  Both conclusions come from one
local AIR fact: after evaluation, every Memory interaction multiplicity is either the row selector,
its negation, or zero.

This module states that fact at the whole-chip boundary.  Registry cases are proved from each chip's
exact `interactionsWith_memory_eq` theorem; no hand-written lookup shadow or semantic execution
assumption is involved. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Every actual Memory interaction of a constrained physical circuit row evaluates to `-is_real`,
`0`, or `is_real`, where `is_real` is the selector exposed by that same row. -/
def CircuitMemorySelectorGated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ data physical,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    component.operations.ConstraintsHold env →
      ∀ interaction ∈ component.operations.interactionsWith memoryChannel.toRaw,
        let selector := (view (component.rowInput env) (component.rowOutput env)).is_real
        Expression.eval env interaction.mult = -selector ∨
          Expression.eval env interaction.mult = 0 ∨
            Expression.eval env interaction.mult = selector

/-- Proof-sized form of selector gating at the typed `main` boundary.  Concrete chips reason only
about their named interaction list; the generic theorem below handles the flattened component. -/
def MainMemorySelectorGated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (main : Var Input (ZMod p) → Circuit (ZMod p) (Var Output (ZMod p)))
    (selector : Var Input (ZMod p) → ℕ → Expression (ZMod p)) : Prop :=
  ∀ input offset env,
    ((main input).operations offset).ConstraintsHold env →
      ∀ interaction ∈ ((main input).operations offset).interactionsWith memoryChannel.toRaw,
        Expression.eval env interaction.mult = -Expression.eval env (selector input offset) ∨
          Expression.eval env interaction.mult = 0 ∨
            Expression.eval env interaction.mult = Expression.eval env (selector input offset)

omit [Fact (2 ^ 24 < p)] in
/-- Reduce a `main`-local gating proof to a chip's exact typed Memory exposure.  Concrete cases now
inspect the short exposed list rather than the flattened operation tree. -/
theorem mainMemorySelectorGated_of_exposed {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (main : Var Input (ZMod p) → Circuit (ZMod p) (Var Output (ZMod p)))
    (selector : Var Input (ZMod p) → ℕ → Expression (ZMod p))
    (exposed : Var Input (ZMod p) → ℕ →
      List (ChannelInteraction (memoryChannel (p := p))))
    (exact : ∀ input offset,
      ((main input).operations offset).interactionsWith memoryChannel.toRaw =
        (exposed input offset).map ChannelInteraction.toRaw)
    (gated : ∀ input offset env,
      ((main input).operations offset).ConstraintsHold env →
        ∀ interaction ∈ exposed input offset,
          Expression.eval env interaction.mult = -Expression.eval env (selector input offset) ∨
            Expression.eval env interaction.mult = 0 ∨
              Expression.eval env interaction.mult = Expression.eval env (selector input offset)) :
    MainMemorySelectorGated main selector := by
  intro input offset env constraints interaction interactionMem
  rw [exact input offset] at interactionMem
  obtain ⟨typed, typedMem, rfl⟩ := List.mem_map.mp interactionMem
  simpa only [ChannelInteraction.toRaw_mult] using
    gated input offset env constraints typed typedMem

/-- Close a concrete list after its definition has been unfolded. -/
local macro "finish_uniform_memory_gating" : tactic =>
  `(tactic| (
    simp only [List.forall_mem_cons, Channel.pulledIf, Channel.pushedIf,
      pulledIf_mult, pushedIf_mult, Expression.eval, neg_one_mul, List.not_mem_nil,
      false_implies, true_and, true_or, or_true]
    intro
    trivial))

/-- Registry boilerplate for a chip whose exact Memory list is uniformly gated by its typed
selector, with no extra source-gate hypothesis. -/
local macro "uniformMemoryGating " main:term ", " selector:term ", "
    exposed:term ", " exactEq:term : tactic =>
  `(tactic| (
    apply mainMemorySelectorGated_of_exposed $main:term $selector:term $exposed:term $exactEq:term
    intro input offset env _constraints
    simp only [$exposed:term]
    finish_uniform_memory_gating))

/-- Registry boilerplate for a chip whose Memory list needs the immediate-aware source-C gate. -/
local macro "subGateMemoryGating " main:term ", " exposed:term ", " exactEq:term ", "
    subGateThm:term : tactic =>
  `(tactic| (
    apply mainMemorySelectorGated_of_exposed $main:term (fun input _ => input.is_real)
      $exposed:term $exactEq:term
    intro input offset env constraints
    have subGate := $subGateThm:term input offset env constraints
    rcases subGate with subGate | subGate <;>
      simp only [$exposed:term, List.forall_mem_cons,
        Channel.pulledIf, Channel.pushedIf, pulledIf_mult, pushedIf_mult,
        Expression.eval, neg_one_mul, List.not_mem_nil, false_implies, true_and,
        subGate, true_or, or_true]
    all_goals simp))


/-! ## Immediate-aware ALU reader gate -/

omit [Fact (2 ^ 24 < p)] in
/-- Project full constraints to the left side of a Clean bind. -/
private theorem constraintsHold_bind_left {α β}
    {left : Circuit (ZMod p) α} {right : α → Circuit (ZMod p) β} {offset : ℕ}
    {env : Environment (ZMod p)}
    (constraints : ((left >>= right).operations offset).ConstraintsHold env) :
    (left.operations offset).ConstraintsHold env := by
  rw [Circuit.bind_operations_eq, operationsConstraintsHold_append] at constraints
  exact constraints.1

omit [Fact (2 ^ 24 < p)] in
/-- Project full constraints to the right side of a Clean bind. -/
private theorem constraintsHold_bind_right {α β}
    {left : Circuit (ZMod p) α} {right : α → Circuit (ZMod p) β} {offset : ℕ}
    {env : Environment (ZMod p)}
    (constraints : ((left >>= right).operations offset).ConstraintsHold env) :
    ((right (left.output offset)).operations
      (offset + left.localLength offset)).ConstraintsHold env := by
  rw [Circuit.bind_operations_eq, operationsConstraintsHold_append] at constraints
  exact constraints.2

omit [Fact (2 ^ 24 < p)] in
/-- Evaluation respects the expression-level subtraction encoding.  Clean represents negation as
multiplication by `-1`, so keeping this tiny rewrite named avoids asking `circuit_norm` to inspect a
large structured reader input. -/
private theorem expression_eval_sub (env : Environment (ZMod p))
    (left right : Expression (ZMod p)) :
    env (left - right) = env left - env right := by
  change env (Expression.add left (Expression.mul (Expression.const (-1)) right)) = _
  simp only [Expression.eval, sub_eq_add_neg, neg_one_mul]

/-- The immediate-padding and source-gate boolean equations extracted from the reader's own AIR. -/
private theorem aluTypeReader_gateFacts_of_constraints
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((Readers.ALUTypeReader.main input).operations offset).ConstraintsHold env) :
    env ((input.is_real - 1) * input.cols.imm_c) = 0 ∧
      env ((input.is_real - input.cols.imm_c) *
        (input.is_real - input.cols.imm_c - 1)) = 0 := by
  simp only [Readers.ALUTypeReader.main, Circuit.operations, Circuit.bind_def,
    assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Operations.localLength,
    operationsConstraintsHold_append] at constraints
  obtain ⟨_, _, _, _, paddingConstraints, subGateConstraints, _⟩ := constraints
  have paddingEq :=
    equality_of_singleton_constraintsHold env _ _ _ paddingConstraints
  have subGateEq :=
    equality_of_singleton_constraintsHold env _ _ _ subGateConstraints
  simpa only [Expression.eval] using And.intro paddingEq subGateEq

/-- The immutable ALU reader carries the same immediate-padding and source-gate equations. -/
private theorem aluTypeReaderImmutable_gateFacts_of_constraints
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((Readers.ALUTypeReaderImmutable.main input).operations offset).ConstraintsHold env) :
    env ((input.is_real - 1) * input.cols.imm_c) = 0 ∧
      env ((input.is_real - input.cols.imm_c) *
        (input.is_real - input.cols.imm_c - 1)) = 0 := by
  simp only [Readers.ALUTypeReaderImmutable.main, Circuit.operations, Circuit.bind_def,
    assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Operations.localLength,
    operationsConstraintsHold_append] at constraints
  obtain ⟨_, _, _, _, paddingConstraints, subGateConstraints, _⟩ := constraints
  have paddingEq :=
    equality_of_singleton_constraintsHold env _ _ _ paddingConstraints
  have subGateEq :=
    equality_of_singleton_constraintsHold env _ _ _ subGateConstraints
  simpa only [Expression.eval] using And.intro paddingEq subGateEq

omit [Fact (2 ^ 24 < p)] in
/-- Full parent constraints restrict to any named nested subcircuit.  This is the structural seam used
to recover the immediate-reader equations from a composed chip without unfolding the reader in the
parent proof. -/
private theorem generalSubcircuit_constraints_of_mem {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (ops : Operations (ZMod p))
    (subcircuitMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  rw [Operations.ConstraintsHold, Operations.forall_constraints_iff,
    Operations.forall_lookups_iff] at constraints
  have nestedConstraints : ConstraintsHoldFlat env
      (circuit.toSubcircuit offset input).ops.toFlat := by
    rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨constraints.1.2 _ subcircuitMem, constraints.2.2 _ subcircuitMem⟩
  rw [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nestedConstraints
  exact nestedConstraints

omit [Fact (2 ^ 24 < p)] in
/-- Full parent constraints restrict to any named formal-assertion subcircuit. -/
private theorem assertionSubcircuit_constraints_of_mem {Input : TypeMap}
    [ProvableType Input] (circuit : FormalAssertion (ZMod p) Input)
    (input : Var Input (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (ops : Operations (ZMod p))
    (subcircuitMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  rw [Operations.ConstraintsHold, Operations.forall_constraints_iff,
    Operations.forall_lookups_iff] at constraints
  have nestedConstraints : ConstraintsHoldFlat env
      (circuit.toSubcircuit offset input).ops.toFlat := by
    rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨constraints.1.2 _ subcircuitMem, constraints.2.2 _ subcircuitMem⟩
  rw [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nestedConstraints
  exact nestedConstraints

omit [Fact (2 ^ 24 < p)] in
/-- Constraint satisfaction of one composed general assertion is exactly satisfaction of its
underlying `main` at the same offset. -/
private theorem constraintsHold_generalAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((subcircuitWithAssertion circuit input).operations offset).ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  apply generalSubcircuit_constraints_of_mem circuit input offset env
    ((subcircuitWithAssertion circuit input).operations offset) _ constraints
  simp only [subcircuitWithAssertion, Circuit.operations,
    Operations.subcircuits_subcircuit, Operations.subcircuits_nil,
    List.mem_singleton]

omit [Fact (2 ^ 24 < p)] in
/-- Constraint satisfaction of one composed formal assertion is exactly satisfaction of its
underlying `main` at the same offset. -/
private theorem constraintsHold_assertion {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion (ZMod p) Input) (input : Var Input (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((assertion circuit input).operations offset).ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  apply assertionSubcircuit_constraints_of_mem circuit input offset env
    ((assertion circuit input).operations offset) _ constraints
  simp only [assertion, Circuit.operations, Operations.subcircuits_subcircuit,
    Operations.subcircuits_nil, List.mem_singleton]

omit [Fact (2 ^ 24 < p)] in
/-- The nested constraints of Clean's equality assertion recover its field equality. -/
private theorem equality_of_constraints (env : Environment (ZMod p))
    (left right : Expression (ZMod p)) (offset : ℕ)
    (constraints : (((@Gadgets.Equality.main (ZMod p) inferInstance field
      instProvableTypeField (left, right))).operations offset).ConstraintsHold env) :
    env left = env right := by
  have difference : env (toElements (M := field) left)[0] -
      env (toElements (M := field) right)[0] = 0 := by
    simpa [Operations.ConstraintsHold, Gadgets.Equality.main, Gadgets.allZero,
      Circuit.forEach.operations_eq, FlatOperation.constraints, FlatOperation.lookups,
      eval_sub, circuit_norm] using constraints
  have leftEq : env (toElements (M := field) left)[0] = env left := rfl
  have rightEq : env (toElements (M := field) right)[0] = env right := rfl
  rw [leftEq, rightEq] at difference
  exact sub_eq_zero.mp difference

omit [Fact (2 ^ 24 < p)] in
/-- A subcircuit in the left side of a Clean bind remains a subcircuit of the composite. -/
private theorem subcircuit_mem_bind_left {F α β} [FiniteField F]
    {subOffset : ℕ} {sub : Subcircuit F subOffset}
    (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (mem : ⟨subOffset, sub⟩ ∈ (left.operations offset).subcircuits) :
    ⟨subOffset, sub⟩ ∈ ((left >>= right).operations offset).subcircuits := by
  rw [Circuit.bind_operations_eq, Operations.subcircuits_append, List.mem_append]
  exact Or.inl mem

omit [Fact (2 ^ 24 < p)] in
/-- A subcircuit in the right side of a Clean bind remains a subcircuit of the composite. -/
private theorem subcircuit_mem_bind_right {F α β} [FiniteField F]
    {subOffset : ℕ} {sub : Subcircuit F subOffset}
    (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (mem : ⟨subOffset, sub⟩ ∈
      ((right (left.output offset)).operations (offset + left.localLength offset)).subcircuits) :
    ⟨subOffset, sub⟩ ∈ ((left >>= right).operations offset).subcircuits := by
  rw [Circuit.bind_operations_eq, Operations.subcircuits_append, List.mem_append]
  exact Or.inr mem

omit [Fact (2 ^ 24 < p)] in
/-- Field-level payoff of the two immediate gates.  On padding the register-source gate is zero;
on a real row its boolean value is either zero (immediate) or the row selector (register). -/
private theorem subGate_eq_zero_or_selector {selector immediate : ZMod p}
    (selectorBinary : selector = 0 ∨ selector = 1)
    (paddingGate : (selector - 1) * immediate = 0)
    (subGateBinary : selector - immediate = 0 ∨ selector - immediate = 1) :
    selector - immediate = 0 ∨ selector - immediate = selector := by
  rcases selectorBinary with rfl | rfl
  · left
    simpa using paddingGate
  · rcases subGateBinary with subZero | subOne
    · exact Or.inl subZero
    · exact Or.inr subOne

/-- Semantic payoff of the immediate-capable ALU reader's two gate equations. -/
private theorem aluTypeReader_subGate_eq_zero_or_isReal
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (selectorBinary : env input.is_real = 0 ∨ env input.is_real = 1)
    (constraints : ((Readers.ALUTypeReader.main input).operations offset).ConstraintsHold env) :
    env (input.is_real - input.cols.imm_c) = 0 ∨
      env (input.is_real - input.cols.imm_c) = env input.is_real := by
  obtain ⟨paddingGate, subGatePolynomial⟩ :=
    aluTypeReader_gateFacts_of_constraints input offset env constraints
  have paddingGate' : (env input.is_real - 1) * env input.cols.imm_c = 0 := by
    simpa only [eval_mul, expression_eval_sub, Expression.eval] using paddingGate
  have subGatePolynomial' :
      (env input.is_real - env input.cols.imm_c) *
        (env input.is_real - env input.cols.imm_c - 1) = 0 := by
    simpa only [eval_mul, expression_eval_sub, Expression.eval] using subGatePolynomial
  have subGateBinary : env input.is_real - env input.cols.imm_c = 0 ∨
      env input.is_real - env input.cols.imm_c = 1 := by
    exact bool_of_mul_pred subGatePolynomial'
  have subGateField :=
    subGate_eq_zero_or_selector selectorBinary paddingGate' subGateBinary
  simpa only [expression_eval_sub] using subGateField

omit [Fact (2 ^ 24 < p)] in
/-- Transport a small `main`-local gating proof to the exact flattened circuit.  This is the sole
place where `Component.rowInput`, `rowOutput`, and the typed circuit output are identified. -/
theorem circuitMemorySelectorGated_of_main {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (selector : Var Input (ZMod p) → ℕ → Expression (ZMod p))
    (selectorEval : ∀ env input offset,
      Expression.eval env (selector input offset) =
        (view (Eval.eval env input)
          (Eval.eval env (circuit.output input offset))).is_real)
    (shape : MainMemorySelectorGated circuit.main selector) :
    CircuitMemorySelectorGated circuit view := by
  intro data physical
  dsimp only
  intro constraints interaction interactionMem
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let input : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  have mainConstraints : ((circuit.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have interactionMem' : interaction ∈
      ((circuit.main input).operations offset).interactionsWith memoryChannel.toRaw := by
    simpa only [component, Component.interactionsWith_eq,
      Component.rowOperations_mk] using interactionMem
  have gated := shape input offset env mainConstraints interaction interactionMem'
  have inputEq : Eval.eval env input = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output input offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  have selectorEq := selectorEval env input offset
  rw [inputEq, outputEq] at selectorEq
  rw [← selectorEq]
  exact gated

/-- Descriptor-level form of `CircuitMemorySelectorGated`. -/
def MemorySelectorConstraintShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    let env := Environment.fromArray physical data
    chip.table.operations.ConstraintsHold env →
      ∀ interaction ∈ chip.table.operations.interactionsWith memoryChannel.toRaw,
        let selector :=
          (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real
        Expression.eval env interaction.mult = -selector ∨
          Expression.eval env interaction.mult = 0 ∨
            Expression.eval env interaction.mult = selector

/-- A whole-circuit selector-gating theorem transports definitionally to its supported descriptor. -/
theorem memorySelectorConstraintShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (specEq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (id : InstructionChipId)
    (shape : @CircuitMemorySelectorGated p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    MemorySelectorConstraintShape ⟨id, kind, circuit, specEq⟩ :=
  shape

/-- Lift a chip's `main`-local Memory gating theorem to its completed whole-chip circuit. -/
local macro "liftMemoryGating " circuit:term ", " rowView:term ", " selector:term ", "
    gated:term : tactic =>
  `(tactic| (
    apply circuitMemorySelectorGated_of_main $circuit:term $rowView:term $selector:term
    · intro env input offset
      simp only [$rowView:term, circuit_norm]
    · exact $gated:term))

/-- As `liftMemoryGating`, for chips whose `RowView` selector is a named `isReal` abbreviation. -/
local macro "liftMemoryGatingWith " circuit:term ", " rowView:term ", " isReal:term ", "
    selector:term ", " gated:term : tactic =>
  `(tactic| (
    apply circuitMemorySelectorGated_of_main $circuit:term $rowView:term $selector:term
    · intro env input offset
      simp only [$rowView:term, $isReal:term, circuit_norm]
    · exact $gated:term))

/-! ## Initial registry anchor -/

/-- Add's exact six-entry Memory list is uniformly gated by its typed input selector. -/
theorem AddChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) AddChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating AddChip.main, (fun input _ => input.is_real),
    AddChip.exposedMemoryInteractions, AddChip.interactionsWith_memory_eq

/-- Add's local selector theorem lifted to its completed whole-chip circuit. -/
theorem AddChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) AddChip.circuit AddChip.rowView := by
  liftMemoryGating AddChip.circuit, AddChip.rowView,
    (fun input _ => input.is_real), AddChip.mainMemorySelectorGated

/-! ## Uniform-selector instruction chips -/

theorem AddiChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) AddiChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating AddiChip.main, (fun input _ => input.is_real),
    AddiChip.exposedMemoryInteractions, AddiChip.interactionsWith_memory_eq

theorem AddiChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) AddiChip.circuit AddiChip.rowView := by
  liftMemoryGating AddiChip.circuit, AddiChip.rowView,
    (fun input _ => input.is_real), AddiChip.mainMemorySelectorGated

theorem SubChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) SubChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating SubChip.main, (fun input _ => input.is_real),
    SubChip.exposedMemoryInteractions, SubChip.interactionsWith_memory_eq

theorem SubChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) SubChip.circuit SubChip.rowView := by
  liftMemoryGating SubChip.circuit, SubChip.rowView,
    (fun input _ => input.is_real), SubChip.mainMemorySelectorGated

theorem SubwChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) SubwChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating SubwChip.main, (fun input _ => input.is_real),
    SubwChip.exposedMemoryInteractions, SubwChip.interactionsWith_memory_eq

theorem SubwChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) SubwChip.circuit SubwChip.rowView := by
  liftMemoryGating SubwChip.circuit, SubwChip.rowView,
    (fun input _ => input.is_real), SubwChip.mainMemorySelectorGated

theorem MulChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) MulChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating MulChip.main, (fun input _ => input.is_real),
    MulChip.exposedMemoryInteractions, MulChip.interactionsWith_memory_eq

theorem MulChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) MulChip.circuit MulChip.rowView := by
  liftMemoryGating MulChip.circuit, MulChip.rowView,
    (fun input _ => input.is_real), MulChip.mainMemorySelectorGated

theorem DivRemChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) DivRemChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating DivRemChip.main, (fun input _ => input.is_real),
    DivRemChip.exposedMemoryInteractions, DivRemChip.interactionsWith_memory_eq

theorem DivRemChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) DivRemChip.circuit DivRemChip.rowView := by
  liftMemoryGating DivRemChip.circuit, DivRemChip.rowView,
    (fun input _ => input.is_real), DivRemChip.mainMemorySelectorGated

theorem JalChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) JalChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating JalChip.main, (fun input _ => input.is_real),
    JalChip.exposedMemoryInteractions, JalChip.interactionsWith_memory_eq

theorem JalChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) JalChip.circuit JalChip.rowView := by
  liftMemoryGating JalChip.circuit, JalChip.rowView,
    (fun input _ => input.is_real), JalChip.mainMemorySelectorGated

theorem JalrChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) JalrChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating JalrChip.main, (fun input _ => input.is_real),
    JalrChip.exposedMemoryInteractions, JalrChip.interactionsWith_memory_eq

theorem JalrChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) JalrChip.circuit JalrChip.rowView := by
  liftMemoryGating JalrChip.circuit, JalrChip.rowView,
    (fun input _ => input.is_real), JalrChip.mainMemorySelectorGated

theorem BranchChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) BranchChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating BranchChip.main, (fun input _ => input.is_real),
    BranchChip.exposedMemoryInteractions, BranchChip.interactionsWith_memory_eq

theorem BranchChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) BranchChip.circuit BranchChip.rowView := by
  liftMemoryGating BranchChip.circuit, BranchChip.rowView,
    (fun input _ => input.is_real), BranchChip.mainMemorySelectorGated

theorem UTypeChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) UTypeChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating UTypeChip.main, (fun input _ => input.is_real),
    UTypeChip.exposedMemoryInteractions, UTypeChip.interactionsWith_memory_eq

theorem UTypeChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) UTypeChip.circuit UTypeChip.rowView := by
  liftMemoryGating UTypeChip.circuit, UTypeChip.rowView,
    (fun input _ => input.is_real), UTypeChip.mainMemorySelectorGated

theorem LoadDoubleChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) LoadDoubleChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating LoadDoubleChip.main, (fun input _ => input.is_real),
    LoadDoubleChip.exposedMemoryInteractions, LoadDoubleChip.interactionsWith_memory_eq

theorem LoadDoubleChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) LoadDoubleChip.circuit LoadDoubleChip.rowView := by
  liftMemoryGating LoadDoubleChip.circuit, LoadDoubleChip.rowView,
    (fun input _ => input.is_real), LoadDoubleChip.mainMemorySelectorGated

theorem LoadByteChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) LoadByteChip.main
      (fun input _ => input.is_lb + input.is_lbu) := by
  uniformMemoryGating LoadByteChip.main, (fun input _ => input.is_lb + input.is_lbu),
    LoadByteChip.exposedMemoryInteractions, LoadByteChip.interactionsWith_memory_eq

theorem LoadByteChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) LoadByteChip.circuit LoadByteChip.rowView := by
  liftMemoryGatingWith LoadByteChip.circuit, LoadByteChip.rowView, LoadByteChip.isReal,
    (fun input _ => input.is_lb + input.is_lbu), LoadByteChip.mainMemorySelectorGated

theorem LoadHalfChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) LoadHalfChip.main
      (fun input _ => input.is_lh + input.is_lhu) := by
  uniformMemoryGating LoadHalfChip.main, (fun input _ => input.is_lh + input.is_lhu),
    LoadHalfChip.exposedMemoryInteractions, LoadHalfChip.interactionsWith_memory_eq

theorem LoadHalfChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) LoadHalfChip.circuit LoadHalfChip.rowView := by
  liftMemoryGatingWith LoadHalfChip.circuit, LoadHalfChip.rowView, LoadHalfChip.isReal,
    (fun input _ => input.is_lh + input.is_lhu), LoadHalfChip.mainMemorySelectorGated

theorem LoadWordChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) LoadWordChip.main
      (fun input _ => input.is_lw + input.is_lwu) := by
  uniformMemoryGating LoadWordChip.main, (fun input _ => input.is_lw + input.is_lwu),
    LoadWordChip.exposedMemoryInteractions, LoadWordChip.interactionsWith_memory_eq

theorem LoadWordChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) LoadWordChip.circuit LoadWordChip.rowView := by
  liftMemoryGatingWith LoadWordChip.circuit, LoadWordChip.rowView, LoadWordChip.isReal,
    (fun input _ => input.is_lw + input.is_lwu), LoadWordChip.mainMemorySelectorGated

theorem LoadX0Chip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) LoadX0Chip.main
      (fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
        + input.is_lw + input.is_lwu + input.is_ld) := by
  uniformMemoryGating LoadX0Chip.main, (fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld),
    LoadX0Chip.exposedMemoryInteractions, LoadX0Chip.interactionsWith_memory_eq

theorem LoadX0Chip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) LoadX0Chip.circuit LoadX0Chip.rowView := by
  liftMemoryGatingWith LoadX0Chip.circuit, LoadX0Chip.rowView, LoadX0Chip.isReal,
    (fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld), LoadX0Chip.mainMemorySelectorGated

theorem StoreByteChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) StoreByteChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating StoreByteChip.main, (fun input _ => input.is_real),
    StoreByteChip.exposedMemoryInteractions, StoreByteChip.interactionsWith_memory_eq

theorem StoreByteChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) StoreByteChip.circuit StoreByteChip.rowView := by
  liftMemoryGating StoreByteChip.circuit, StoreByteChip.rowView,
    (fun input _ => input.is_real), StoreByteChip.mainMemorySelectorGated

theorem StoreHalfChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) StoreHalfChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating StoreHalfChip.main, (fun input _ => input.is_real),
    StoreHalfChip.exposedMemoryInteractions, StoreHalfChip.interactionsWith_memory_eq

theorem StoreHalfChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) StoreHalfChip.circuit StoreHalfChip.rowView := by
  liftMemoryGating StoreHalfChip.circuit, StoreHalfChip.rowView,
    (fun input _ => input.is_real), StoreHalfChip.mainMemorySelectorGated

theorem StoreWordChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) StoreWordChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating StoreWordChip.main, (fun input _ => input.is_real),
    StoreWordChip.exposedMemoryInteractions, StoreWordChip.interactionsWith_memory_eq

theorem StoreWordChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) StoreWordChip.circuit StoreWordChip.rowView := by
  liftMemoryGating StoreWordChip.circuit, StoreWordChip.rowView,
    (fun input _ => input.is_real), StoreWordChip.mainMemorySelectorGated

theorem StoreDoubleChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) StoreDoubleChip.main (fun input _ => input.is_real) := by
  uniformMemoryGating StoreDoubleChip.main, (fun input _ => input.is_real),
    StoreDoubleChip.exposedMemoryInteractions, StoreDoubleChip.interactionsWith_memory_eq

theorem StoreDoubleChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) StoreDoubleChip.circuit StoreDoubleChip.rowView := by
  liftMemoryGating StoreDoubleChip.circuit, StoreDoubleChip.rowView,
    (fun input _ => input.is_real), StoreDoubleChip.mainMemorySelectorGated

/-! ## Immediate-aware instruction chips -/

/-- The exact ALU-reader input assembled by Addw's `main`.  Keeping this value folded separates
subcircuit-list normalization from the reader's own constraints. -/
private def AddwChip.aluReaderInput (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 19,
    var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩ * 65535,
    var ⟨offset + 2⟩ * 65535⟩

/-- Addw's full row constraints restrict to its composed ALU reader. -/
private theorem AddwChip.aluReaderConstraints
    (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((AddwChip.main input).operations offset).ConstraintsHold env) :
    ((Readers.ALUTypeReader.main (AddwChip.aluReaderInput input offset)).operations
      (offset + 3)).ConstraintsHold env := by
  have readerMem : ⟨offset + 3,
      Readers.ALUTypeReader.circuit.toSubcircuit (offset + 3)
        (AddwChip.aluReaderInput input offset)⟩ ∈
      ((AddwChip.main input).operations offset).subcircuits := by
    simp only [AddwChip.main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
      Operations.localLength]
    simp only [GeneralFormalCircuit.toSubcircuit_localLength,
      FormalAssertion.toSubcircuit_localLength, FormalCircuitBase.localLength_def,
      Readers.CPUState.circuit,
      Readers.CPUState.localLength_eq, AddwOperation.circuit,
      AddwOperation.localLength_eq, Readers.ALUTypeReader.circuit,
      Readers.ALUTypeReader.localLength_eq, Readers.RegisterWrite.circuit,
      Operations.subcircuits_subcircuit, Operations.subcircuits_witness,
      AddwChip.aluReaderInput, Nat.add_zero, add_zero, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons,
      ProvableType.varFromOffset_fields,
      Vector.getElem_mapRange, Nat.add_one, eq_self, true_or]
    simp only [or_true]
  exact generalSubcircuit_constraints_of_mem
    Readers.ALUTypeReader.circuit (AddwChip.aluReaderInput input offset) (offset + 3) env
      ((AddwChip.main input).operations offset) readerMem constraints

/-- Addw's full constraints imply binaryity of its physical input selector. -/
private theorem AddwChip.selectorBinary_of_constraints
    (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((AddwChip.main input).operations offset).ConstraintsHold env) :
    env input.is_real = 0 ∨ env input.is_real = 1 := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have selectorBinary := AddwChip.mainSelectorBinary.binary input offset env shallow
  simpa only [circuit_norm] using selectorBinary

/-- The two field equations relevant to Addw's immediate-aware source-C gate. -/
private theorem AddwChip.readerGateFacts
    (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((AddwChip.main input).operations offset).ConstraintsHold env) :
    (env input.is_real - 1) * env input.adapter.imm_c = 0 ∧
      (env input.is_real - env input.adapter.imm_c) *
        (env input.is_real - env input.adapter.imm_c - 1) = 0 := by
  have readerConstraints := AddwChip.aluReaderConstraints input offset env constraints
  obtain ⟨paddingGate, subGatePolynomial⟩ :=
    aluTypeReader_gateFacts_of_constraints (AddwChip.aluReaderInput input offset)
      (offset + 3) env readerConstraints
  dsimp only [AddwChip.aluReaderInput] at paddingGate subGatePolynomial
  constructor
  · simpa only [eval_mul, expression_eval_sub, Expression.eval] using paddingGate
  · simpa only [eval_mul, expression_eval_sub, Expression.eval] using subGatePolynomial

/-- Addw's ALU reader forces the immediate-aware source-C gate to be either zero or the physical
row selector. -/
private theorem AddwChip.subGate_eq_zero_or_isReal
    (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((AddwChip.main input).operations offset).ConstraintsHold env) :
    env (input.is_real - input.adapter.imm_c) = 0 ∨
      env (input.is_real - input.adapter.imm_c) = env input.is_real := by
  have selectorBinary := AddwChip.selectorBinary_of_constraints input offset env constraints
  obtain ⟨paddingGate, subGatePolynomial⟩ := AddwChip.readerGateFacts input offset env constraints
  have subGateBinary : env input.is_real - env input.adapter.imm_c = 0 ∨
      env input.is_real - env input.adapter.imm_c = 1 := by
    apply bool_of_mul_pred
    exact subGatePolynomial
  have subGateField :=
    subGate_eq_zero_or_selector selectorBinary paddingGate subGateBinary
  simpa only [expression_eval_sub] using subGateField

theorem AddwChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) AddwChip.main (fun input _ => input.is_real) := by
  subGateMemoryGating AddwChip.main, AddwChip.exposedMemoryInteractions,
    AddwChip.interactionsWith_memory_eq, AddwChip.subGate_eq_zero_or_isReal

theorem AddwChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) AddwChip.circuit AddwChip.rowView := by
  liftMemoryGating AddwChip.circuit, AddwChip.rowView,
    (fun input _ => input.is_real), AddwChip.mainMemorySelectorGated

/-- The exact ALU-reader input assembled by Bitwise's `main`. -/
private def BitwiseChip.aluReaderInput
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    var ⟨offset⟩ * 3 + var ⟨offset + 1⟩ * 4 + var ⟨offset + 2⟩ * 5,
    var ⟨offset + 11⟩ + var ⟨offset + 12⟩ * 256,
    var ⟨offset + 13⟩ + var ⟨offset + 14⟩ * 256,
    var ⟨offset + 15⟩ + var ⟨offset + 16⟩ * 256,
    var ⟨offset + 17⟩ + var ⟨offset + 18⟩ * 256⟩

/-- Bitwise's full row constraints restrict to its composed ALU reader. -/
private theorem BitwiseChip.aluReaderConstraints
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env) :
    ((Readers.ALUTypeReader.main (BitwiseChip.aluReaderInput input offset)).operations
      (offset + 19)).ConstraintsHold env := by
  have readerMem : ⟨offset + 19,
      Readers.ALUTypeReader.circuit.toSubcircuit (offset + 19)
        (BitwiseChip.aluReaderInput input offset)⟩ ∈
      ((BitwiseChip.main input).operations offset).subcircuits := by
    simp only [BitwiseChip.main, BitwiseChip.aluReaderInput, circuit_norm]
  exact generalSubcircuit_constraints_of_mem Readers.ALUTypeReader.circuit
    (BitwiseChip.aluReaderInput input offset) (offset + 19) env
      ((BitwiseChip.main input).operations offset) readerMem constraints

/-- Bitwise's immediate-aware source-C gate is zero or the physical row selector. -/
private theorem BitwiseChip.subGate_eq_zero_or_isReal
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((BitwiseChip.main input).operations offset).ConstraintsHold env) :
    env (input.is_real - input.adapter.imm_c) = 0 ∨
      env (input.is_real - input.adapter.imm_c) = env input.is_real := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have selectorBinary := BitwiseChip.mainSelectorBinary.binary input offset env shallow
  have selectorBinary' : env input.is_real = 0 ∨ env input.is_real = 1 := by
    simpa only [circuit_norm] using selectorBinary
  have readerSelectorBinary :
      env (BitwiseChip.aluReaderInput input offset).is_real = 0 ∨
        env (BitwiseChip.aluReaderInput input offset).is_real = 1 := by
    simpa only [BitwiseChip.aluReaderInput] using selectorBinary'
  have readerConstraints := BitwiseChip.aluReaderConstraints input offset env constraints
  have subGate := aluTypeReader_subGate_eq_zero_or_isReal
    (BitwiseChip.aluReaderInput input offset) (offset + 19) env
      readerSelectorBinary readerConstraints
  simpa only [BitwiseChip.aluReaderInput] using subGate

theorem BitwiseChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) BitwiseChip.main (fun input _ => input.is_real) := by
  subGateMemoryGating BitwiseChip.main, BitwiseChip.exposedMemoryInteractions,
    BitwiseChip.interactionsWith_memory_eq, BitwiseChip.subGate_eq_zero_or_isReal

theorem BitwiseChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) BitwiseChip.circuit BitwiseChip.rowView := by
  liftMemoryGating BitwiseChip.circuit, BitwiseChip.rowView,
    (fun input _ => input.is_real), BitwiseChip.mainMemorySelectorGated

/-- The exact ALU-reader input assembled by Lt's `main`. -/
private def LtChip.aluReaderInput (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    var ⟨offset⟩ * 9 + var ⟨offset + 1⟩ * 10,
    var ⟨offset + 2⟩, 0, 0, 0⟩

/-- Lt's full row constraints restrict to its composed ALU reader. -/
private theorem LtChip.aluReaderConstraints
    (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((LtChip.main input).operations offset).ConstraintsHold env) :
    ((Readers.ALUTypeReader.main (LtChip.aluReaderInput input offset)).operations
      (offset + 12)).ConstraintsHold env := by
  have readerMem : ⟨offset + 12,
      Readers.ALUTypeReader.circuit.toSubcircuit (offset + 12)
        (LtChip.aluReaderInput input offset)⟩ ∈
      ((LtChip.main input).operations offset).subcircuits := by
    simp only [LtChip.main, LtChip.aluReaderInput, circuit_norm]
  exact generalSubcircuit_constraints_of_mem Readers.ALUTypeReader.circuit
    (LtChip.aluReaderInput input offset) (offset + 12) env
      ((LtChip.main input).operations offset) readerMem constraints

/-- Lt's immediate-aware source-C gate is zero or the physical row selector. -/
private theorem LtChip.subGate_eq_zero_or_isReal
    (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((LtChip.main input).operations offset).ConstraintsHold env) :
    env (input.is_real - input.adapter.imm_c) = 0 ∨
      env (input.is_real - input.adapter.imm_c) = env input.is_real := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have selectorBinary := LtChip.mainSelectorBinary.binary input offset env shallow
  have selectorBinary' : env input.is_real = 0 ∨ env input.is_real = 1 := by
    simpa only [circuit_norm] using selectorBinary
  have readerSelectorBinary : env (LtChip.aluReaderInput input offset).is_real = 0 ∨
      env (LtChip.aluReaderInput input offset).is_real = 1 := by
    simpa only [LtChip.aluReaderInput] using selectorBinary'
  have readerConstraints := LtChip.aluReaderConstraints input offset env constraints
  have subGate := aluTypeReader_subGate_eq_zero_or_isReal
    (LtChip.aluReaderInput input offset) (offset + 12) env
      readerSelectorBinary readerConstraints
  simpa only [LtChip.aluReaderInput] using subGate

theorem LtChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) LtChip.main (fun input _ => input.is_real) := by
  subGateMemoryGating LtChip.main, LtChip.exposedMemoryInteractions,
    LtChip.interactionsWith_memory_eq, LtChip.subGate_eq_zero_or_isReal

theorem LtChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) LtChip.circuit LtChip.rowView := by
  liftMemoryGating LtChip.circuit, LtChip.rowView,
    (fun input _ => input.is_real), LtChip.mainMemorySelectorGated

/-! ## ShiftLeft's derived selector -/

/-- ShiftLeft's full row constraints restrict to its composed ALU reader. -/
private theorem ShiftLeftChip.aluReaderConstraints
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env) :
    ((Readers.ALUTypeReader.main (ShiftLeftChip.aluReaderInput input offset)).operations
      (offset + 33)).ConstraintsHold env := by
  exact generalSubcircuit_constraints_of_mem Readers.ALUTypeReader.circuit
    (ShiftLeftChip.aluReaderInput input offset) (offset + 33) env
      ((ShiftLeftChip.main input).operations offset)
      (ShiftLeftChip.aluReader_mem_subcircuits input offset) constraints

/-- ShiftLeft's immediate-aware source-C gate is zero or its witnessed variant selector. -/
private theorem ShiftLeftChip.subGate_eq_zero_or_exposedGate
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env) :
    env (ShiftLeftChip.exposedGate offset - input.adapter.imm_c) = 0 ∨
      env (ShiftLeftChip.exposedGate offset - input.adapter.imm_c) =
        env (ShiftLeftChip.exposedGate offset) := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have selectorBinary := ShiftLeftChip.mainSelectorBinary.binary input offset env shallow
  have selectorBinary' : env input.is_real = 0 ∨ env input.is_real = 1 := by
    simpa only [circuit_norm] using selectorBinary
  have gateEq := ShiftLeftChip.isReal_eq_exposedGate input offset env constraints
  rw [gateEq] at selectorBinary'
  have readerSelectorBinary :
      env (ShiftLeftChip.aluReaderInput input offset).is_real = 0 ∨
        env (ShiftLeftChip.aluReaderInput input offset).is_real = 1 := by
    simpa only [ShiftLeftChip.aluReaderInput, ShiftLeftChip.exposedGate] using selectorBinary'
  have readerConstraints := ShiftLeftChip.aluReaderConstraints input offset env constraints
  have subGate := aluTypeReader_subGate_eq_zero_or_isReal
    (ShiftLeftChip.aluReaderInput input offset) (offset + 33) env
      readerSelectorBinary readerConstraints
  simpa only [ShiftLeftChip.aluReaderInput, ShiftLeftChip.exposedGate] using subGate

theorem ShiftLeftChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) ShiftLeftChip.main (fun input _ => input.is_real) := by
  apply mainMemorySelectorGated_of_exposed ShiftLeftChip.main (fun input _ => input.is_real)
    ShiftLeftChip.exposedMemoryInteractions ShiftLeftChip.interactionsWith_memory_eq
  intro input offset env constraints
  have gateEq := ShiftLeftChip.isReal_eq_exposedGate input offset env constraints
  have subGate := ShiftLeftChip.subGate_eq_zero_or_exposedGate input offset env constraints
  rcases subGate with subGate | subGate <;>
    simp only [ShiftLeftChip.exposedMemoryInteractions, List.forall_mem_cons,
      Channel.pulledIf, Channel.pushedIf, pulledIf_mult, pushedIf_mult,
      Expression.eval, neg_one_mul, List.not_mem_nil, false_implies, true_and,
      gateEq, subGate, true_or, or_true]
  all_goals simp

theorem ShiftLeftChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) ShiftLeftChip.circuit ShiftLeftChip.rowView := by
  liftMemoryGating ShiftLeftChip.circuit, ShiftLeftChip.rowView,
    (fun input _ => input.is_real), ShiftLeftChip.mainMemorySelectorGated

/-- The ShiftRight row's explicit binding assertion identifies its public selector with the
variant-flag sum used by the factored register write. -/
theorem ShiftRightChip.isReal_eq_exposedWriteGate
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env) :
    env input.is_real = env (ShiftRightChip.exposedWriteGate offset) := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have allConstraints := (constraintsHold_shallow_iff_forall_mem.mp shallow).1
  have bindingMem : input.is_real - ShiftRightChip.exposedWriteGate offset ∈
      ((ShiftRightChip.main input).operations offset).shallowConstraints := by
    change input.is_real - ShiftRightChip.exposedWriteGate offset ∈
      input.is_real * (input.is_real - 1) ::
        (input.is_real - ShiftRightChip.exposedWriteGate offset) :: _
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have binding := allConstraints _ bindingMem
  rw [expression_eval_sub] at binding
  exact sub_eq_zero.mp binding

/-- ShiftRight's full row constraints restrict to its composed ALU reader. -/
private theorem ShiftRightChip.aluReaderGateFacts
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env) :
    env (((ShiftRightChip.aluReaderInput input offset).is_real - 1) *
        (ShiftRightChip.aluReaderInput input offset).cols.imm_c) = 0 ∧
      env (((ShiftRightChip.aluReaderInput input offset).is_real -
        (ShiftRightChip.aluReaderInput input offset).cols.imm_c) *
          ((ShiftRightChip.aluReaderInput input offset).is_real -
            (ShiftRightChip.aluReaderInput input offset).cols.imm_c - 1)) = 0 := by
  have readerConstraints := generalSubcircuit_constraints_of_mem
    Readers.ALUTypeReader.circuit (ShiftRightChip.aluReaderInput input offset) (offset + 37) env
      ((ShiftRightChip.main input).operations offset)
      (ShiftRightChip.aluReader_mem_subcircuits input offset) constraints
  exact aluTypeReader_gateFacts_of_constraints
    (ShiftRightChip.aluReaderInput input offset) (offset + 37) env readerConstraints

/-- ShiftRight's immediate-aware source-C gate is zero or the physical row selector. -/
private theorem ShiftRightChip.subGate_eq_zero_or_isReal
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env) :
    env (input.is_real - input.adapter.imm_c) = 0 ∨
      env (input.is_real - input.adapter.imm_c) = env input.is_real := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have selectorBinary := ShiftRightChip.mainSelectorBinary.binary input offset env shallow
  have selectorBinary' : env input.is_real = 0 ∨ env input.is_real = 1 := by
    simpa only [circuit_norm] using selectorBinary
  have readerSelectorBinary :
      env (ShiftRightChip.aluReaderInput input offset).is_real = 0 ∨
        env (ShiftRightChip.aluReaderInput input offset).is_real = 1 := by
    simpa only [ShiftRightChip.aluReaderInput] using selectorBinary'
  obtain ⟨paddingGate, subGatePolynomial⟩ :=
    ShiftRightChip.aluReaderGateFacts input offset env constraints
  have paddingGate' :
      (env input.is_real - 1) * env input.adapter.imm_c = 0 := by
    simpa only [ShiftRightChip.aluReaderInput, eval_mul, expression_eval_sub,
      Expression.eval] using paddingGate
  have subGatePolynomial' :
      (env input.is_real - env input.adapter.imm_c) *
        (env input.is_real - env input.adapter.imm_c - 1) = 0 := by
    simpa only [ShiftRightChip.aluReaderInput, eval_mul, expression_eval_sub,
      Expression.eval] using subGatePolynomial
  have subGateBinary : env input.is_real - env input.adapter.imm_c = 0 ∨
      env input.is_real - env input.adapter.imm_c = 1 :=
    bool_of_mul_pred subGatePolynomial'
  have subGate := subGate_eq_zero_or_selector selectorBinary' paddingGate' subGateBinary
  simpa only [expression_eval_sub] using subGate

theorem ShiftRightChip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) ShiftRightChip.main (fun input _ => input.is_real) := by
  apply mainMemorySelectorGated_of_exposed ShiftRightChip.main (fun input _ => input.is_real)
    ShiftRightChip.exposedMemoryInteractions ShiftRightChip.interactionsWith_memory_eq
  intro input offset env constraints
  have subGate := ShiftRightChip.subGate_eq_zero_or_isReal input offset env constraints
  have writeGate := (ShiftRightChip.isReal_eq_exposedWriteGate input offset env constraints).symm
  rcases subGate with subGate | subGate <;>
    simp only [ShiftRightChip.exposedMemoryInteractions, List.forall_mem_cons,
      Channel.pulledIf, Channel.pushedIf, pulledIf_mult, pushedIf_mult,
      Expression.eval, neg_one_mul, List.not_mem_nil, false_implies, true_and,
      subGate, writeGate, true_or, or_true]
  all_goals simp

theorem ShiftRightChip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) ShiftRightChip.circuit ShiftRightChip.rowView := by
  liftMemoryGating ShiftRightChip.circuit, ShiftRightChip.rowView,
    (fun input _ => input.is_real), ShiftRightChip.mainMemorySelectorGated

/-! ## Immutable ALU reader (`AluX0`) -/

private def AluX0Chip.aluReaderInput (input : Var AluX0Chip.Inputs (ZMod p)) :
    Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, input.opcode⟩

/-- AluX0's full row constraints restrict to its composed immutable ALU reader. -/
private theorem AluX0Chip.aluReaderConstraints
    (input : Var AluX0Chip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((AluX0Chip.main input).operations offset).ConstraintsHold env) :
    ((Readers.ALUTypeReaderImmutable.main (AluX0Chip.aluReaderInput input)).operations
      offset).ConstraintsHold env := by
  have readerMem : ⟨offset,
      Readers.ALUTypeReaderImmutable.circuit.toSubcircuit offset
        (AluX0Chip.aluReaderInput input)⟩ ∈
      ((AluX0Chip.main input).operations offset).subcircuits := by
    simp only [AluX0Chip.main, AluX0Chip.aluReaderInput, circuit_norm, Nat.add_zero]
  exact generalSubcircuit_constraints_of_mem Readers.ALUTypeReaderImmutable.circuit
    (AluX0Chip.aluReaderInput input) offset env
      ((AluX0Chip.main input).operations offset) readerMem constraints

/-- AluX0's immediate-aware source-C gate is zero or the physical row selector. -/
private theorem AluX0Chip.subGate_eq_zero_or_isReal
    (input : Var AluX0Chip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((AluX0Chip.main input).operations offset).ConstraintsHold env) :
    env (input.is_real - input.adapter.imm_c) = 0 ∨
      env (input.is_real - input.adapter.imm_c) = env input.is_real := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr constraints)
  have selectorBinary := AluX0Chip.mainSelectorBinary.binary input offset env shallow
  have selectorBinary' : env input.is_real = 0 ∨ env input.is_real = 1 := by
    simpa only [circuit_norm] using selectorBinary
  have readerConstraints := AluX0Chip.aluReaderConstraints input offset env constraints
  obtain ⟨paddingGate, subGatePolynomial⟩ :=
    aluTypeReaderImmutable_gateFacts_of_constraints
      (AluX0Chip.aluReaderInput input) offset env readerConstraints
  have paddingGate' : (env input.is_real - 1) * env input.adapter.imm_c = 0 := by
    simpa only [AluX0Chip.aluReaderInput, eval_mul, expression_eval_sub,
      Expression.eval] using paddingGate
  have subGatePolynomial' :
      (env input.is_real - env input.adapter.imm_c) *
        (env input.is_real - env input.adapter.imm_c - 1) = 0 := by
    simpa only [AluX0Chip.aluReaderInput, eval_mul, expression_eval_sub,
      Expression.eval] using subGatePolynomial
  have subGateBinary : env input.is_real - env input.adapter.imm_c = 0 ∨
      env input.is_real - env input.adapter.imm_c = 1 :=
    bool_of_mul_pred subGatePolynomial'
  have subGate := subGate_eq_zero_or_selector selectorBinary' paddingGate' subGateBinary
  simpa only [expression_eval_sub] using subGate

theorem AluX0Chip.mainMemorySelectorGated :
    MainMemorySelectorGated (p := p) AluX0Chip.main (fun input _ => input.is_real) := by
  subGateMemoryGating AluX0Chip.main, AluX0Chip.exposedMemoryInteractions,
    AluX0Chip.interactionsWith_memory_eq, AluX0Chip.subGate_eq_zero_or_isReal

theorem AluX0Chip.circuitMemorySelectorGated :
    CircuitMemorySelectorGated (p := p) AluX0Chip.circuit AluX0Chip.rowView := by
  liftMemoryGating AluX0Chip.circuit, AluX0Chip.rowView,
    (fun input _ => input.is_real), AluX0Chip.mainMemorySelectorGated

/-! ## Registry closure -/

/-- Registry-case boilerplate: restore the descriptor's retained dependent instances and transport
the corresponding whole-chip Memory selector theorem to the descriptor-level contract. -/
local macro "memorySelectorRegistryCase " kind:term ", " shape:term : tactic =>
  `(tactic| (
    letI := ($kind:term).provableInputs
    letI := ($kind:term).provableCols
    apply memorySelectorConstraintShape_of_circuit
    exact $shape:term))

/-- Every descriptor in the single supported-machine registry gates each of its actual Memory
interactions by the selector exposed from that same constrained physical row. -/
theorem supportedChip_memorySelectorConstraintShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : MemorySelectorConstraintShape chip := by
  fin_cases chipMem
  · memorySelectorRegistryCase (AddChip.kind (p := p)),
      (AddChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (AddiChip.kind (p := p)),
      (AddiChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (AddwChip.kind (p := p)),
      (AddwChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (SubChip.kind (p := p)),
      (SubChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (SubwChip.kind (p := p)),
      (SubwChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (BitwiseChip.kind (p := p)),
      (BitwiseChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (LtChip.kind (p := p)),
      (LtChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (ShiftLeftChip.kind (p := p)),
      (ShiftLeftChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (ShiftRightChip.kind (p := p)),
      (ShiftRightChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (JalChip.kind (p := p)),
      (JalChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (JalrChip.kind (p := p)),
      (JalrChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (BranchChip.kind (p := p)),
      (BranchChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (UTypeChip.kind (p := p)),
      (UTypeChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (LoadByteChip.kind (p := p)),
      (LoadByteChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (LoadHalfChip.kind (p := p)),
      (LoadHalfChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (LoadWordChip.kind (p := p)),
      (LoadWordChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (LoadDoubleChip.kind (p := p)),
      (LoadDoubleChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (LoadX0Chip.kind (p := p)),
      (LoadX0Chip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (StoreByteChip.kind (p := p)),
      (StoreByteChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (StoreHalfChip.kind (p := p)),
      (StoreHalfChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (StoreWordChip.kind (p := p)),
      (StoreWordChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (StoreDoubleChip.kind (p := p)),
      (StoreDoubleChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (MulChip.kind (p := p)),
      (MulChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (DivRemChip.kind (p := p)),
      (DivRemChip.circuitMemorySelectorGated (p := p))
  · memorySelectorRegistryCase (AluX0Chip.kind (p := p)),
      (AluX0Chip.circuitMemorySelectorGated (p := p))

/-! ## Canonical decoded-row consequences -/

/-- A field multiplicity gated by a binary selector has the signed integer range required by Clean's
typed balance theorem. -/
private theorem signedVal_binary_of_selector_gated (selector mult : ZMod p)
    (selectorBinary : selector = 0 ∨ selector = 1)
    (gated : mult = -selector ∨ mult = 0 ∨ mult = selector) :
    signedVal mult = -1 ∨ signedVal mult = 0 ∨ signedVal mult = 1 := by
  have hp : 2 < p := by
    have := Fact.out (p := 2 ^ 24 < p)
    omega
  rcases selectorBinary with selectorZero | selectorOne
  · subst selector
    simp only [neg_zero] at gated
    rcases gated with multZero | multZero | multZero <;> subst mult
    all_goals
      right
      left
      simp [signedVal, ZMod.val_zero]
  · subst selector
    have oneVal : (1 : ZMod p).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    rcases gated with multNegative | multZero | multPositive
    · left
      rw [multNegative, signedVal_neg_is_real hp (Or.inr rfl), oneVal]
      norm_num
    · right
      left
      rw [multZero]
      simp [signedVal, ZMod.val_zero]
    · right
      right
      rw [multPositive, signedVal_is_real hp (Or.inr rfl), oneVal]
      norm_num

/-- Every evaluated Memory interaction of a constrained canonical instruction row is literally the
negative selector, zero, or the selector exposed by that same decoded row. -/
theorem DecodedInstructionRow.memoryInteractionMult_selectorGated
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    ∀ interaction ∈ decoded.interactionsWith data memoryChannel,
      interaction.mult = -(decoded.toChipRow data).is_real ∨
        interaction.mult = 0 ∨ interaction.mult = (decoded.toChipRow data).is_real := by
  intro interaction interactionMem
  have shape := supportedChip_memorySelectorConstraintShape decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem) data decoded.physical constraints
  unfold DecodedInstructionRow.interactionsWith typedInteractionValuesWith at interactionMem
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp interactionMem
  have gated := shape source.1 source.2
  simpa only [TypedInteraction.mult, TypedInteraction.eval, AbstractInteraction.eval,
    DecodedInstructionRow.environment, ChipRow.is_real,
    DecodedInstructionRow.toChipRow_view] using gated

/-- Selector booleanity plus the registry-wide gating theorem gives signed-binary multiplicity for
every actual Memory interaction of a canonical instruction row. -/
theorem DecodedInstructionRow.memoryInteractions_signedBinary
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    ∀ interaction ∈ decoded.interactionsWith data memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1 := by
  intro interaction interactionMem
  apply signedVal_binary_of_selector_gated (decoded.toChipRow data).is_real interaction.mult
  · exact decoded.selectorBinary_of_constraints data tables decodedMem constraints
  · exact decoded.memoryInteractionMult_selectorGated data tables decodedMem constraints
      interaction interactionMem

/-- A constrained padding instruction row emits no active Memory message on either side. -/
theorem DecodedInstructionRow.paddingMemoryMessages_eq_nil
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (padding : (decoded.toChipRow data).is_real ≠ 1) :
    decoded.producedMemoryMessages data = [] ∧ decoded.consumedMemoryMessages data = [] := by
  have selectorZero : (decoded.toChipRow data).is_real = 0 := by
    rcases decoded.selectorBinary_of_constraints data tables decodedMem constraints with zero | one
    · exact zero
    · exact (padding one).elim
  have multZero : ∀ interaction ∈ decoded.interactionsWith data memoryChannel,
      interaction.mult = 0 := by
    intro interaction interactionMem
    rcases decoded.memoryInteractionMult_selectorGated data tables decodedMem constraints
      interaction interactionMem with negative | zero | positive
    · simpa only [selectorZero, neg_zero] using negative
    · exact zero
    · simpa only [selectorZero] using positive
  have signedValZero : signedVal (0 : ZMod p) = 0 := by
    simp [signedVal, ZMod.val_zero]
  constructor
  · unfold DecodedInstructionRow.producedMemoryMessages producedMessages
    have filtered : (decoded.interactionsWith data memoryChannel).filter
        (fun interaction => signedVal interaction.mult = 1) = [] := by
      rw [List.filter_eq_nil_iff]
      intro interaction interactionMem
      simp only [decide_eq_true_eq]
      rw [multZero interaction interactionMem, signedValZero]
      norm_num
    rw [filtered, List.map_nil]
  · unfold DecodedInstructionRow.consumedMemoryMessages consumedMessages
    have filtered : (decoded.interactionsWith data memoryChannel).filter
        (fun interaction => signedVal interaction.mult = -1) = [] := by
      rw [List.filter_eq_nil_iff]
      intro interaction interactionMem
      simp only [decide_eq_true_eq]
      rw [multZero interaction interactionMem, signedValZero]
      norm_num
    rw [filtered, List.map_nil]

end SP1Clean.Soundness
