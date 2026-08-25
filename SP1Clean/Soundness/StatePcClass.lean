import SP1Clean.Soundness.TypedTime
import SP1Clean.Soundness.RowSoundness

/-! # Per-row pc-limb classification of decoded State edges

Every active instruction row falls into one of two classes on its State edge:

* **preservation** — a straight-line chip commits `next_pc = #v[pc[0] + 4, pc[1], pc[2]]`, so the
  two upper pc limbs of its State push equal those of its State pull *definitionally*; or
* **bounded target** — a control-flow chip (Jal, Jalr, Branch) commits a data-dependent target
  whose upper limbs are 16-bit range-checked by the chip's own Byte pulls (inside the retained
  jump-target `AddOperation` for Jal/Jalr, at the top level of `main` for Branch).

The registry-wide theorem `witness_realDecodedRows_pcClass` derives this classification for every
active canonically decoded row from physical constraints and channel balance alone — no chip
`Assumptions`, Memory currency, or grounding position is involved, so it is available to the W3
StateBump goodness-filter pass before the timed walk is constructed. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The Byte-pull leaf: one active 16-bit `Range` pull bounds its checked scalar -/

/-- A raw byte-channel `Range 16` pull guarantee at an active gate yields the 16-bit bound on the
checked scalar.  This is the shared scalar leaf under both the `AddOperation` descent (Jal, Jalr)
and the chip-level extraction (Branch). -/
theorem val_lt_of_byteRangePull_guarantee
    (gate limb : Expression (ZMod p)) (env : Environment (ZMod p))
    (guarantee : ((byteChannel (p := p)).pulledIf gate
      (⟨6, limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
        ByteRow (Expression (ZMod p)))).toRaw.Guarantees env)
    (real : Expression.eval env gate = 1) :
    (Expression.eval env limb).val < 2 ^ 16 := by
  have typed := (ChannelInteraction.toRaw_guarantees env
    ((byteChannel (p := p)).pulledIf gate
      (⟨6, limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
        ByteRow (Expression (ZMod p))))).mp guarantee
  have negReal : -(Expression.eval env gate) = -1 := by rw [real]
  have spec := typed (by rfl) (by simpa only [circuit_norm] using negReal)
  change ByteRowSpec (Eval.eval env ((byteChannel (p := p)).pulledIf gate
    (⟨6, limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))).msg) at spec
  have msgEq : Eval.eval env ((byteChannel (p := p)).pulledIf gate
      (⟨6, limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
        ByteRow (Expression (ZMod p)))).msg =
      (⟨6, Expression.eval env limb, ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (ZMod p)) := by
    dsimp only [Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc, Expression.eval]
  rw [msgEq] at spec
  exact (byteRowSpec_range _ sixteen_lt).mp spec

/-- The addition gadget's second and third Byte `Range 16` pulls bound its upper result limbs on
an active row.  Only the finished Byte channel is consumed — not the gadget's `Spec` — so the
bound is available before Memory currency exists. -/
theorem AddOperation.upperLimbBounds_of_byteGuarantees
    (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((AddOperation.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env (input.cols.value[1])).val < 2 ^ 16 ∧
      (Expression.eval env (input.cols.value[2])).val < 2 ^ 16 := by
  rw [FlatOperation.channelGuarantees_iff_forall_mem,
    FormalAssertion.toSubcircuit_interactions] at guarantees
  refine ⟨val_lt_of_byteRangePull_guarantee input.is_real (input.cols.value[1]) env ?_ real,
    val_lt_of_byteRangePull_guarantee input.is_real (input.cols.value[2]) env ?_ real⟩
  · apply guarantees
    · simp only [AddOperation.circuit, AddOperation.main, circuit_norm, List.mem_cons]
    · rfl
  · apply guarantees
    · simp only [AddOperation.circuit, AddOperation.main, circuit_norm, List.mem_cons]
    · rfl

/-! ## Chip-local contracts for the three control-flow chips -/

/-- Scalar binding between a located range-checked gate/limb triple and the public semantic row
view: the gate is the row selector and the two limbs are the committed upper next-pc limbs. -/
structure PushedPcBinding (gate limb1 limb2 : ZMod p)
    (view : Trace.RowView (ZMod p)) : Prop where
  real_eq : gate = view.is_real
  limb1_eq : limb1 = view.next_pc[1]
  limb2_eq : limb2 = view.next_pc[2]

/-- Chip-local contract for a jump chip (Jal, Jalr): the retained jump-target `AddOperation`
subcircuit is gated by the row selector and its upper result limbs are the committed upper next-pc
limbs.  A named `Prop` inductive, like `CircuitRTypeTimestampContract`, so recognizing its result
sort never forces `whnf` through a completed chip circuit. -/
inductive CircuitJumpTargetContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (addOffset : ℕ) (addInput : Var AddOperation.Inputs (ZMod p))
      (add_mem : ⟨addOffset,
          (AddOperation.circuit (p := p)).toSubcircuit addOffset addInput⟩ ∈
        ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
          (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        PushedPcBinding (Expression.eval env addInput.is_real)
          (Expression.eval env (addInput.cols.value[1]))
          (Expression.eval env (addInput.cols.value[2]))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env (circuit.output (varFromOffset (F := ZMod p) Input 0)
              (size Input))))) :
      CircuitJumpTargetContract circuit view

/-- Chip-local contract for a chip whose own `main` emits the two upper next-pc `Range 16` pulls
directly (Branch): both pulls are shallow interactions of the chip's operation list. -/
inductive CircuitShallowNextPcContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (gate limb1 limb2 : Expression (ZMod p))
      (mem1 : ((byteChannel (p := p)).pulledIf gate
          (⟨6, limb1, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw ∈
        ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
          (size Input)).shallowInteractions)
      (mem2 : ((byteChannel (p := p)).pulledIf gate
          (⟨6, limb2, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw ∈
        ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
          (size Input)).shallowInteractions)
      (binding : ∀ env : Environment (ZMod p),
        PushedPcBinding (Expression.eval env gate) (Expression.eval env limb1)
          (Expression.eval env limb2)
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env (circuit.output (varFromOffset (F := ZMod p) Input 0)
              (size Input))))) :
      CircuitShallowNextPcContract circuit view

/-- A chip circuit's Byte range checks bound the committed upper next-pc limbs of every active
physical row.  One-field structure, like `CircuitStateTimeStep`, so applying it never weak-head
normalizes a completed chip circuit. -/
structure CircuitPushedPcBound {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  bound : ∀ data physical,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    let rowView := view (component.rowInput env) (component.rowOutput env)
    component.operations.ChannelGuarantees byteChannel.toRaw env →
    rowView.is_real = 1 →
    (rowView.next_pc[1]).val < 2 ^ 16 ∧ (rowView.next_pc[2]).val < 2 ^ 16

/-- A retained jump-target `AddOperation` plus the finished Byte guarantees bound the committed
upper next-pc limbs of the completed chip circuit. -/
theorem circuitPushedPcBound_of_jumpTargetContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitJumpTargetContract circuit view) :
    CircuitPushedPcBound circuit view := by
  constructor
  obtain ⟨addOffset, addInput, addMem, binding⟩ := contract
  intro data physical
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  change component.operations.ChannelGuarantees byteChannel.toRaw env → rowView.is_real = 1 →
    (rowView.next_pc[1]).val < 2 ^ 16 ∧ (rowView.next_pc[2]).val < 2 ^ 16
  intro guarantees real
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have addGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((AddOperation.circuit (p := p)).toSubcircuit addOffset addInput) addMem rowGuarantees
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have addReal : Expression.eval env addInput.is_real = 1 := bound.real_eq.trans real
  have limbBounds := AddOperation.upperLimbBounds_of_byteGuarantees addInput addOffset env
    addGuarantees addReal
  constructor
  · rw [← bound.limb1_eq]
    exact limbBounds.1
  · rw [← bound.limb2_eq]
    exact limbBounds.2

/-- Two shallow next-pc `Range 16` pulls plus the finished Byte guarantees bound the committed
upper next-pc limbs of the completed chip circuit. -/
theorem circuitPushedPcBound_of_shallowNextPcContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitShallowNextPcContract circuit view) :
    CircuitPushedPcBound circuit view := by
  constructor
  obtain ⟨gate, limb1, limb2, mem1, mem2, binding⟩ := contract
  intro data physical
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  change component.operations.ChannelGuarantees byteChannel.toRaw env → rowView.is_real = 1 →
    (rowView.next_pc[1]).val < 2 ^ 16 ∧ (rowView.next_pc[2]).val < 2 ^ 16
  intro guarantees real
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  rw [Operations.ChannelGuarantees, Operations.forall_interactions_iff] at rowGuarantees
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have gateReal : Expression.eval env gate = 1 := bound.real_eq.trans real
  constructor
  · rw [← bound.limb1_eq]
    exact val_lt_of_byteRangePull_guarantee gate limb1 env
      (rowGuarantees.1 _ mem1 rfl) gateReal
  · rw [← bound.limb2_eq]
    exact val_lt_of_byteRangePull_guarantee gate limb2 env
      (rowGuarantees.1 _ mem2 rfl) gateReal

/-! ## The three control-flow instances -/

/-- The jump-target `AddOperation` input retained by the JAL row: base `pc ++ 0`, addend the J-type
immediate, result the four target witness cells, gate the row selector. -/
def jalTargetAddInput (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    Var AddOperation.Inputs (ZMod p) :=
  ⟨#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0],
    input.adapter.op_b_imm,
    ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩,
    input.is_real⟩

theorem jalChip_jumpTargetContract :
    CircuitJumpTargetContract (p := p) (JalChip.circuit (p := p)) JalChip.rowView := by
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  refine ⟨offset + 8, jalTargetAddInput input offset, ?_, ?_⟩
  · simp only [input, offset, jalTargetAddInput, JalChip.circuit, JalChip.main,
      AddOperation.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, offset, jalTargetAddInput, JalChip.circuit, JalChip.rowView, circuit_norm]

/-- The jump-target `AddOperation` input retained by the JALR row: base the rs1 register read-back,
addend the I-type immediate, result the four target witness cells, gate the row selector. -/
def jalrTargetAddInput (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    Var AddOperation.Inputs (ZMod p) :=
  ⟨#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
      input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]],
    input.adapter.op_c_imm,
    ⟨Vector.mapRange 4 fun i => var { index := offset + i }⟩,
    input.is_real⟩

theorem jalrChip_jumpTargetContract :
    CircuitJumpTargetContract (p := p) (JalrChip.circuit (p := p)) JalrChip.rowView := by
  let input : Var JalrChip.Inputs (ZMod p) := varFromOffset JalrChip.Inputs 0
  let offset := size JalrChip.Inputs
  refine ⟨offset + 9, jalrTargetAddInput input offset, ?_, ?_⟩
  · -- The `lsb` booleanity `===` precedes the target add, so its (defeq-zero) local length blocks
    -- full arithmetic normalization of the retained offsets; select the disjunct and close by
    -- definitional unfolding, as the CPUState clock contract does for this chip.
    simp only [input, offset, jalrTargetAddInput, JalrChip.circuit, JalrChip.main,
      AddOperation.circuit, circuit_norm]
    right
    right
    left
    rfl
  · intro env
    constructor <;>
      simp only [input, offset, jalrTargetAddInput, JalrChip.circuit, JalrChip.rowView,
        circuit_norm]

theorem branchChip_shallowNextPcContract :
    CircuitShallowNextPcContract (p := p) (BranchChip.circuit (p := p)) BranchChip.rowView := by
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  let offset := size BranchChip.Inputs
  refine ⟨input.is_real, var { index := offset + 8 }, var { index := offset + 9 }, ?_, ?_, ?_⟩
  · simp only [input, offset, BranchChip.circuit, BranchChip.main,
      Operations.shallowInteractions, circuit_norm, List.mem_cons]
  · simp only [input, offset, BranchChip.circuit, BranchChip.main,
      Operations.shallowInteractions, circuit_norm, List.mem_cons]
  · intro env
    constructor <;>
      simp only [input, offset, BranchChip.circuit, BranchChip.rowView, circuit_norm]

/-! ## Registry and decoded-witness consequences -/

/-- A supported descriptor's active physical rows either preserve both upper pc limbs across their
State edge (straight-line chips, definitionally) or push genuinely 16-bit upper limbs (control-flow
chips, from their own Byte range checks). -/
def StatePcClassShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (Environment.fromArray physical data) →
    (chip.decodeRow data physical).is_real = 1 →
    ((statePushMessage (chip.decodeRow data physical)).pc1 =
        (statePullMessage (chip.decodeRow data physical)).pc1 ∧
      (statePushMessage (chip.decodeRow data physical)).pc2 =
        (statePullMessage (chip.decodeRow data physical)).pc2) ∨
    ((statePushMessage (chip.decodeRow data physical)).pc1.val < 2 ^ 16 ∧
      (statePushMessage (chip.decodeRow data physical)).pc2.val < 2 ^ 16)

/-- A chip whose committed view preserves the two upper pc limbs — for every input/column pair,
not just constrained ones — satisfies the preservation disjunct outright.  The straight-line chips
all discharge the hypothesis by `⟨rfl, rfl⟩` over abstract rows: keeping `inp`/`cols` opaque here
is what stops the definitional check from ever normalizing a decoded `valueFromOffset` row. -/
theorem statePcClassShape_preserve_of_view (chip : SupportedChip p)
    (h : ∀ (inp : chip.kind.Inputs (ZMod p)) (cols : chip.kind.Cols (ZMod p)),
      (chip.kind.view inp cols).next_pc[1] = (chip.kind.view inp cols).state.pc[1] ∧
      (chip.kind.view inp cols).next_pc[2] = (chip.kind.view inp cols).state.pc[2]) :
    StatePcClassShape chip :=
  fun _ _ _ _ => Or.inl (h _ _)

/-- Transport a circuit-level pushed-pc bound to its supported descriptor without unfolding the
dependent registry record. -/
theorem statePcClassShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (id : InstructionChipId)
    (shape : @CircuitPushedPcBound p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    StatePcClassShape ⟨id, kind, circuit, spec_eq⟩ := by
  letI := kind.provableInputs
  letI := kind.provableCols
  intro data physical guarantees real
  exact Or.inr (shape.bound data physical guarantees real)

/-- A straight-line chip commits `next_pc = #v[pc[0] + 4, pc[1], pc[2]]`, so both upper pc limbs of
its push equal those of its pull definitionally. -/
theorem addChip_statePcClassShape : StatePcClassShape
    (⟨.add, AddChip.kind, AddChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem addiChip_statePcClassShape : StatePcClassShape
    (⟨.addi, AddiChip.kind, AddiChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem addwChip_statePcClassShape : StatePcClassShape
    (⟨.addw, AddwChip.kind, AddwChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem subChip_statePcClassShape : StatePcClassShape
    (⟨.sub, SubChip.kind, SubChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem subwChip_statePcClassShape : StatePcClassShape
    (⟨.subw, SubwChip.kind, SubwChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem bitwiseChip_statePcClassShape : StatePcClassShape
    (⟨.bitwise, BitwiseChip.kind, BitwiseChip.circuit, rfl⟩ :
      SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem ltChip_statePcClassShape : StatePcClassShape
    (⟨.lt, LtChip.kind, LtChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem shiftLeftChip_statePcClassShape : StatePcClassShape
    (⟨.shiftLeft, ShiftLeftChip.kind, ShiftLeftChip.circuit, rfl⟩ :
      SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem shiftRightChip_statePcClassShape : StatePcClassShape
    (⟨.shiftRight, ShiftRightChip.kind, ShiftRightChip.circuit, rfl⟩ :
      SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

/-- JAL pushes its committed jump target; the retained target `AddOperation` range-checks its upper
limbs. -/
theorem jalChip_statePcClassShape : StatePcClassShape
    (⟨.jal, JalChip.kind, JalChip.circuit, rfl⟩ : SupportedChip p) := by
  letI := (JalChip.kind (p := p)).provableInputs
  letI := (JalChip.kind (p := p)).provableCols
  apply statePcClassShape_of_circuit
  apply circuitPushedPcBound_of_jumpTargetContract
  exact jalChip_jumpTargetContract

/-- JALR pushes its committed LSB-cleared jump target; limbs 1 and 2 are the retained target
`AddOperation` result limbs, range-checked there. -/
theorem jalrChip_statePcClassShape : StatePcClassShape
    (⟨.jalr, JalrChip.kind, JalrChip.circuit, rfl⟩ : SupportedChip p) := by
  letI := (JalrChip.kind (p := p)).provableInputs
  letI := (JalrChip.kind (p := p)).provableCols
  apply statePcClassShape_of_circuit
  apply circuitPushedPcBound_of_jumpTargetContract
  exact jalrChip_jumpTargetContract

/-- BRANCH pushes its committed taken/fall-through target, whose upper limbs its own `main`
range-checks; no case split on the branching decision is needed. -/
theorem branchChip_statePcClassShape : StatePcClassShape
    (⟨.branch, BranchChip.kind, BranchChip.circuit, rfl⟩ : SupportedChip p) := by
  letI := (BranchChip.kind (p := p)).provableInputs
  letI := (BranchChip.kind (p := p)).provableCols
  apply statePcClassShape_of_circuit
  apply circuitPushedPcBound_of_shallowNextPcContract
  exact branchChip_shallowNextPcContract

theorem uTypeChip_statePcClassShape : StatePcClassShape
    (⟨.uType, UTypeChip.kind, UTypeChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem loadByteChip_statePcClassShape : StatePcClassShape
    (⟨.loadByte, LoadByteChip.kind, LoadByteChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem loadHalfChip_statePcClassShape : StatePcClassShape
    (⟨.loadHalf, LoadHalfChip.kind, LoadHalfChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem loadWordChip_statePcClassShape : StatePcClassShape
    (⟨.loadWord, LoadWordChip.kind, LoadWordChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem loadDoubleChip_statePcClassShape : StatePcClassShape
    (⟨.loadDouble, LoadDoubleChip.kind, LoadDoubleChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem loadX0Chip_statePcClassShape : StatePcClassShape
    (⟨.loadX0, LoadX0Chip.kind, LoadX0Chip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem storeByteChip_statePcClassShape : StatePcClassShape
    (⟨.storeByte, StoreByteChip.kind, StoreByteChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem storeHalfChip_statePcClassShape : StatePcClassShape
    (⟨.storeHalf, StoreHalfChip.kind, StoreHalfChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem storeWordChip_statePcClassShape : StatePcClassShape
    (⟨.storeWord, StoreWordChip.kind, StoreWordChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem storeDoubleChip_statePcClassShape : StatePcClassShape
    (⟨.storeDouble, StoreDoubleChip.kind, StoreDoubleChip.circuit, rfl⟩ : SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem mulChip_statePcClassShape : StatePcClassShape
    (⟨.mul, MulChip.kind, MulChip.circuit, rfl⟩ :
      SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem divRemChip_statePcClassShape : StatePcClassShape
    (⟨.divRem, DivRemChip.kind, DivRemChip.circuit, rfl⟩ :
      SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

theorem aluX0Chip_statePcClassShape : StatePcClassShape
    (⟨.aluX0, AluX0Chip.kind, AluX0Chip.circuit, rfl⟩ :
      SupportedChip p) :=
  statePcClassShape_preserve_of_view _ fun _ _ => ⟨rfl, rfl⟩

/-- Every chip in the stable supported-machine registry classifies its active State edges: the 22
straight-line chips preserve the upper pc limbs definitionally, and Jal/Jalr/Branch bound their
pushed upper limbs by their own Byte range checks. -/
theorem supportedChip_statePcClassShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : StatePcClassShape chip := by
  fin_cases chipMem
  · exact addChip_statePcClassShape
  · exact addiChip_statePcClassShape
  · exact addwChip_statePcClassShape
  · exact subChip_statePcClassShape
  · exact subwChip_statePcClassShape
  · exact bitwiseChip_statePcClassShape
  · exact ltChip_statePcClassShape
  · exact shiftLeftChip_statePcClassShape
  · exact shiftRightChip_statePcClassShape
  · exact jalChip_statePcClassShape
  · exact jalrChip_statePcClassShape
  · exact branchChip_statePcClassShape
  · exact uTypeChip_statePcClassShape
  · exact loadByteChip_statePcClassShape
  · exact loadHalfChip_statePcClassShape
  · exact loadWordChip_statePcClassShape
  · exact loadDoubleChip_statePcClassShape
  · exact loadX0Chip_statePcClassShape
  · exact storeByteChip_statePcClassShape
  · exact storeHalfChip_statePcClassShape
  · exact storeWordChip_statePcClassShape
  · exact storeDoubleChip_statePcClassShape
  · exact mulChip_statePcClassShape
  · exact divRemChip_statePcClassShape
  · exact aluX0Chip_statePcClassShape

/-- **Every active canonically decoded instruction row either preserves the two upper pc limbs
across its State edge or pushes genuine 16-bit upper limbs.**  Straight-line rows land in the left
disjunct definitionally; Jal/Jalr/Branch rows (taken or fall-through alike) land in the right
disjunct via their in-circuit target range checks.  Only physical constraints and channel balance
are consumed. -/
theorem witness_realDecodedRows_pcClass
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      ((statePushMessage (decoded.toChipRow witness.data)).pc1 =
          (statePullMessage (decoded.toChipRow witness.data)).pc1 ∧
        (statePushMessage (decoded.toChipRow witness.data)).pc2 =
          (statePullMessage (decoded.toChipRow witness.data)).pc2) ∨
      ((statePushMessage (decoded.toChipRow witness.data)).pc1.val < 2 ^ 16 ∧
        (statePushMessage (decoded.toChipRow witness.data)).pc2.val < 2 ^ 16) := by
  intro decoded decodedMem
  rw [realDecodedInstructionRows, List.mem_filter] at decodedMem
  simp only [decide_eq_true_eq] at decodedMem
  exact supportedChip_statePcClassShape decoded.chip
    (decodedInstructionRows_chip_mem witness.tables decodedMem.1) witness.data decoded.physical
    ((witness_decodedRow_finishedChannelGuarantees witness constraints balanced decoded
      decodedMem.1).1)
    decodedMem.2

end SP1Clean.Soundness
