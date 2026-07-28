import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.TimeExtraction
import SP1Clean.Soundness.TypedState
import SP1Clean.Native.Readers.MemoryAccess

/-! # Row-local clock facts from the actual chip interactions

This module connects the generic no-wraparound arithmetic in `TimeExtraction` to the physical Clean
rows.  The contract is intentionally chip-level: it assumes the Byte-channel guarantees on the
chip's actual flattened operations and concludes the exact time step denoted by its State edge.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Active scalar content of SP1's generic RAM-access timestamp gadget. Unlike the register-only
timestamp contract, `compare_low` selects either the low or high component and both difference
limbs are explicit columns. Keeping the seven scalars separate prevents chip-level applications
from weak-head normalizing a large evaluated load/store row. -/
structure ActiveMemoryTimestampFacts
    (compare prevHigh prevLow diffLow diffHigh clkHigh clkLow : ZMod p) : Prop where
  compareBinary : compare = 0 ∨ compare = 1
  sameHigh : compare * (clkHigh - prevHigh) = 0
  gap : compare * (clkLow + 1) + (1 - compare) * clkHigh -
      (compare * prevLow + (1 - compare) * prevHigh) - 1 =
    diffLow + diffHigh * 65536
  diffLowBound : diffLow.val < 2 ^ 16
  diffHighBound : diffHigh.val < 2 ^ 8

/-- A chip circuit's Byte range checks force its semantic State edge to advance by eight ticks.
Kept as a one-field structure so applying the contract never asks the elaborator to weak-head
normalize a large completed chip circuit. -/
structure CircuitStateTimeStep {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  step : ∀ data physical,
    let component : Component (ZMod p) := ⟨circuit⟩
    let env := Environment.fromArray physical data
    let rowView := view (component.rowInput env) (component.rowOutput env)
    component.operations.ChannelGuarantees byteChannel.toRaw env →
    rowView.is_real = 1 →
    Semantics.StateMsg.timeNat (statePushOfView rowView) =
      Semantics.StateMsg.timeNat (statePullOfView rowView) + 8

/-- A channel guarantee for an operation list restricts to its leading subcircuit. -/
theorem channelGuarantees_head_subcircuit {F : Type} [FiniteField F]
    (channel : RawChannel F) (env : Environment F) {n : ℕ}
    (sub : Subcircuit F n) (rest : Operations F)
    (guarantees : Operations.ChannelGuarantees channel env (.subcircuit sub :: rest)) :
    FlatOperation.ChannelGuarantees channel env sub.ops.toFlat := by
  rw [FlatOperation.channelGuarantees_iff_forall_mem]
  intro interaction interactionMem channelEq
  apply guarantees interaction
  · rw [Operations.interactions_subcircuit]
    exact List.mem_append_left _ interactionMem
  · exact channelEq

/-- A channel guarantee on a nested operation list restricts to any retained top-level
subcircuit.  This is the general form needed by chips that witness arithmetic columns before
composing their `CPUState` reader. -/
theorem channelGuarantees_subcircuit_of_mem {F : Type} [FiniteField F]
    (channel : RawChannel F) (env : Environment F) (ops : Operations F)
    {n : ℕ} (sub : Subcircuit F n)
    (subMem : ⟨n, sub⟩ ∈ ops.subcircuits)
    (guarantees : ops.ChannelGuarantees channel env) :
    FlatOperation.ChannelGuarantees channel env sub.ops.toFlat := by
  rw [Operations.ChannelGuarantees, Operations.forall_interactions_iff] at guarantees
  rw [FlatOperation.channelGuarantees_iff_forall_mem]
  intro interaction interactionMem channelEq
  exact guarantees.2 ⟨n, sub⟩ subMem interaction interactionMem channelEq

/-- Recover the structured operation-list guarantee hidden by a `FormalAssertion` subcircuit.

Clean stores a composed circuit as one `NestedOperations.nested` node, but its `toFlat` operation
list is definitionally the original circuit's recursively flattened operations.  Exposing this
equivalence lets callers descend through more than one retained subcircuit boundary without
unfolding the parent circuit's entire interaction list. -/
theorem channelGuarantees_toSubcircuit_formalAssertion {F : Type} [FiniteField F]
    {Input : TypeMap} [ProvableType Input] (channel : RawChannel F) (env : Environment F)
    (circuit : FormalAssertion F Input) (offset : ℕ) (input : Var Input F) :
    FlatOperation.ChannelGuarantees channel env
        (circuit.toSubcircuit offset input).ops.toFlat ↔
      ((circuit.main input).operations offset).ChannelGuarantees channel env := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, FlatOperation.channelGuarantees_toFlat]

/-- `GeneralFormalCircuit` twin of `channelGuarantees_toSubcircuit_formalAssertion`. -/
theorem channelGuarantees_toSubcircuit_generalFormalCircuit {F : Type} [FiniteField F]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (channel : RawChannel F) (env : Environment F)
    (circuit : GeneralFormalCircuit F Input Output) (offset : ℕ) (input : Var Input F) :
    FlatOperation.ChannelGuarantees channel env
        (circuit.toSubcircuit offset input).ops.toFlat ↔
      ((circuit.main input).operations offset).ChannelGuarantees channel env := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]
  rw [Operations.toNested_toFlat, FlatOperation.channelGuarantees_toFlat]

/-- The evaluated clock/selector expressions fed to `CPUState` are the corresponding portion of
the semantic row view.  Keeping the four scalar expressions explicit is important: evaluating the
whole reader input would normalize its irrelevant PC and successor-PC vectors in every use. -/
structure CPUStateTimeBinding (cpuReal cpuClkHigh cpuClk0 cpuClk1 : ZMod p)
    (view : Trace.RowView (ZMod p)) : Prop where
  real_eq : cpuReal = view.is_real
  clkHigh_eq : cpuClkHigh = view.state.clk_high
  clk0_eq : cpuClk0 = view.state.clk_0_16
  clk1_eq : cpuClk1 = view.state.clk_16_24

/-- Chip-local audit contract for clock extraction.  It pins an actual `CPUState.circuit`
subcircuit in the chip's canonical physical row and relates that reader's clock inputs to the
public semantic row view.  No operation-level Rust bridge or chip `Spec` is involved. -/
def CircuitCPUStateTimeContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  ∃ (cpuOffset : ℕ) (cpuInput : Var Readers.CPUState.Inputs (ZMod p)),
    ⟨cpuOffset, (Readers.CPUState.circuit (p := p)).toSubcircuit cpuOffset cpuInput⟩ ∈
      ((circuit.main inputVar).operations offset).subcircuits ∧
    ∀ env : Environment (ZMod p),
      CPUStateTimeBinding (Expression.eval env cpuInput.is_real)
        (Expression.eval env cpuInput.cols.clk_high)
        (Expression.eval env cpuInput.cols.clk_0_16)
        (Expression.eval env cpuInput.cols.clk_16_24)
        (view (Eval.eval env inputVar) (Eval.eval env (circuit.output inputVar offset)))

set_option maxHeartbeats 1000000 in
/-- The CPUState reader's two Byte pulls imply the two evaluated clock bounds on an active row.
State is absent from the premise: its channel guarantee is structurally `True` and does not justify
clock arithmetic.  Keeping this at the expression boundary avoids a costly, irrelevant normalization
of the reader's entire nested input structure. -/
theorem Readers.CPUState.bounds_of_byteGuarantees
    (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.CPUState.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ((Expression.eval env input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      (Expression.eval env input.cols.clk_16_24).val < 2 ^ 8 := by
  rw [FlatOperation.channelGuarantees_iff_forall_mem,
    GeneralFormalCircuit.toSubcircuit_interactions] at guarantees
  let first := byteChannel.pulledIf input.is_real
    (⟨6, (input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0⟩ :
      ByteRow (Expression (ZMod p)))
  let second := byteChannel.pulledIf input.is_real
    (⟨3, 0, input.cols.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))
  have firstGuarantee : first.toRaw.Guarantees env := by
    apply guarantees first.toRaw
    · simp only [Readers.CPUState.circuit, Readers.CPUState.main, circuit_norm,
        first, List.mem_cons]
      tauto
    · rfl
  have secondGuarantee : second.toRaw.Guarantees env := by
    apply guarantees second.toRaw
    · simp only [Readers.CPUState.circuit, Readers.CPUState.main, circuit_norm,
        second, List.mem_cons]
    · rfl
  have h13p : (13 : ℕ) < p := lt_trans (Nat.lt_two_pow_self) Readers.CPUState.hn13
  have negReal : -(Expression.eval env input.is_real) = -1 := by rw [real]
  have firstMult : (fun x => Expression.eval env x) first.toRaw.mult = -1 := by
    simpa only [first, circuit_norm] using negReal
  have secondMult : (fun x => Expression.eval env x) second.toRaw.mult = -1 := by
    simpa only [second, circuit_norm] using negReal
  have firstSpec : ByteRowSpec (Eval.eval env first.msg) := by
    have typed := (ChannelInteraction.toRaw_guarantees env first).mp firstGuarantee
    have guarantee := typed (by rfl) (by simpa only [circuit_norm] using firstMult)
    change ByteRowSpec (Eval.eval env first.msg) at guarantee
    exact guarantee
  have secondSpec : ByteRowSpec (Eval.eval env second.msg) := by
    have typed := (ChannelInteraction.toRaw_guarantees env second).mp secondGuarantee
    have guarantee := typed (by rfl) (by simpa only [circuit_norm] using secondMult)
    change ByteRowSpec (Eval.eval env second.msg) at guarantee
    exact guarantee
  have firstMsgEq : Eval.eval env first.msg =
      (⟨6, (Expression.eval env input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0⟩ :
        ByteRow (ZMod p)) := by
    dsimp only [first, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      eval_sub, Expression.eval]
  have secondMsgEq : Eval.eval env second.msg =
      (⟨3, 0, Expression.eval env input.cols.clk_16_24, 0⟩ : ByteRow (ZMod p)) := by
    dsimp only [second, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc, Expression.eval]
  rw [firstMsgEq] at firstSpec
  rw [secondMsgEq] at secondSpec
  constructor
  · have range := (byteRowSpec_range _ h13p).mp firstSpec
    exact range
  · have range := ((byteRowSpec_u8range_pair _ _).mp secondSpec).1
    exact range

/-- **The RegisterAccessTimestamp reader's two Byte pulls imply its two timestamp bounds** — the
register-column analogue of `CPUState.bounds_of_byteGuarantees`.  This is the byteG-only leaf that makes
`RegisterAccessCols.Spec` (the `RowOK.slot` timestamp bound) *upfront-derivable*: the reader does only
Byte pulls (no Memory), so the bounds follow from the finished Byte channel alone, never the
grounding-time memory pull currency.  Two pulls: a 16-bit `Range` on `diff_low_limb` and a `U8Range` on
the scaled high part `(clk_target - prev_low - 1 - diff) * 65536⁻¹`.

**Refactor status (rowAligned-upfront, in progress).**  This leaf is step 1 of making
`Soundness/ChipContracts.lean`'s `rowAligned` field derivable from `byteG` + `decodedInROM` instead of the
grounding-time chip `Spec` (so the walk's per-row `RowOK` is available before grounding).  What remains is the
NAVIGATION: from a chip row's whole-circuit `byteG`, reach each of the three nested `RegisterAccessTimestamp`
subcircuits and apply this leaf, then relate the reader's input columns to the row `view` (a
`CPUStateTimeBinding`-style binding) and wrap as the three `RegisterAccessCols.Spec`s.  The clean multi-level
*structured* descent does not chain (a subcircuit's `.ops` is `NestedOperations`, and the bridge
`channelGuarantees_toFlat` is over `Operations`); the working route is a direct extraction from the
recursively-flattened interaction list (`circuit_norm`'s `toFlat_subcircuit`/`interactions_subcircuit`), i.e.
this leaf's byte-pull pattern applied to all six register pulls at the flattened level.  Then
`addChip_rowAligned`/`rowAligned_rtype` drop their `spec`/`openInputs` argument in favour of `byteG` +
`decodedInROM_rtype_operand_lt` (`Soundness/Decode.lean`, the decode-intrinsic `op_a/op_b/op_c < 32`). -/
theorem Readers.RegisterAccessTimestamp.bounds_of_byteGuarantees
    (input : Var Readers.RegisterAccessTimestamp.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.RegisterAccessTimestamp.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env input.cols.diff_low_limb).val < 2 ^ 16 ∧
      ((Expression.eval env input.clk_target - Expression.eval env input.cols.prev_low - 1 -
        Expression.eval env input.cols.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8 := by
  rw [FlatOperation.channelGuarantees_iff_forall_mem,
    FormalAssertion.toSubcircuit_interactions] at guarantees
  let first := byteChannel.pulledIf input.is_real
    (⟨6, input.cols.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  let second := byteChannel.pulledIf input.is_real
    (⟨3, 0, (input.clk_target - input.cols.prev_low - 1 - input.cols.diff_low_limb) *
      (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))
  have firstGuarantee : first.toRaw.Guarantees env := by
    apply guarantees first.toRaw
    · simp only [Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        circuit_norm, first, List.mem_cons]
    · rfl
  have secondGuarantee : second.toRaw.Guarantees env := by
    apply guarantees second.toRaw
    · simp only [Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        circuit_norm, second, List.mem_cons]
    · rfl
  have negReal : -(Expression.eval env input.is_real) = -1 := by rw [real]
  have firstMult : (fun x => Expression.eval env x) first.toRaw.mult = -1 := by
    simpa only [first, circuit_norm] using negReal
  have secondMult : (fun x => Expression.eval env x) second.toRaw.mult = -1 := by
    simpa only [second, circuit_norm] using negReal
  have firstSpec : ByteRowSpec (Eval.eval env first.msg) := by
    have typed := (ChannelInteraction.toRaw_guarantees env first).mp firstGuarantee
    have guarantee := typed (by rfl) (by simpa only [circuit_norm] using firstMult)
    change ByteRowSpec (Eval.eval env first.msg) at guarantee
    exact guarantee
  have secondSpec : ByteRowSpec (Eval.eval env second.msg) := by
    have typed := (ChannelInteraction.toRaw_guarantees env second).mp secondGuarantee
    have guarantee := typed (by rfl) (by simpa only [circuit_norm] using secondMult)
    change ByteRowSpec (Eval.eval env second.msg) at guarantee
    exact guarantee
  have firstMsgEq : Eval.eval env first.msg =
      (⟨6, Expression.eval env input.cols.diff_low_limb, ((16 : ℕ) : ZMod p), 0⟩ :
        ByteRow (ZMod p)) := by
    dsimp only [first, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      Expression.eval]
  have secondMsgEq : Eval.eval env second.msg =
      (⟨3, 0, (Expression.eval env input.clk_target - Expression.eval env input.cols.prev_low - 1 -
        Expression.eval env input.cols.diff_low_limb) * (65536 : ZMod p)⁻¹, 0⟩ :
        ByteRow (ZMod p)) := by
    dsimp only [second, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      eval_sub, Expression.eval]
  rw [firstMsgEq] at firstSpec
  rw [secondMsgEq] at secondSpec
  constructor
  · exact (byteRowSpec_range _ sixteen_lt).mp firstSpec
  · exact ((byteRowSpec_u8range_pair _ _).mp secondSpec).1

/-- The generic RAM `MemoryAccess` reader's two Byte pulls range-check its explicit 16/8-bit
difference limbs. This leaf deliberately uses only the finished Byte channel; Memory pull
currency is not yet available while the timed grounding walk is being constructed. -/
theorem Readers.MemoryAccess.diffBounds_of_byteGuarantees
    (input : Var Readers.MemoryAccess.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.MemoryAccess.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env input.mem.access_timestamp.diff_low_limb).val < 2 ^ 16 ∧
      (Expression.eval env input.mem.access_timestamp.diff_high_limb).val < 2 ^ 8 := by
  rw [FlatOperation.channelGuarantees_iff_forall_mem,
    GeneralFormalCircuit.toSubcircuit_interactions] at guarantees
  let first := byteChannel.pulledIf input.is_real
    (⟨6, input.mem.access_timestamp.diff_low_limb,
      Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  let second := byteChannel.pulledIf input.is_real
    (⟨3, 0, input.mem.access_timestamp.diff_high_limb, 0⟩ :
      ByteRow (Expression (ZMod p)))
  have firstGuarantee : first.toRaw.Guarantees env := by
    apply guarantees first.toRaw
    · simp only [Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
        circuit_norm, first, List.mem_cons]
    · rfl
  have secondGuarantee : second.toRaw.Guarantees env := by
    apply guarantees second.toRaw
    · simp only [Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
        circuit_norm, second, List.mem_cons]
    · rfl
  have negReal : -(Expression.eval env input.is_real) = -1 := by rw [real]
  have firstMult : (fun x => Expression.eval env x) first.toRaw.mult = -1 := by
    simpa only [first, circuit_norm] using negReal
  have secondMult : (fun x => Expression.eval env x) second.toRaw.mult = -1 := by
    simpa only [second, circuit_norm] using negReal
  have firstSpec : ByteRowSpec (Eval.eval env first.msg) := by
    have typed := (ChannelInteraction.toRaw_guarantees env first).mp firstGuarantee
    have guarantee := typed (by rfl) (by simpa only [circuit_norm] using firstMult)
    change ByteRowSpec (Eval.eval env first.msg) at guarantee
    exact guarantee
  have secondSpec : ByteRowSpec (Eval.eval env second.msg) := by
    have typed := (ChannelInteraction.toRaw_guarantees env second).mp secondGuarantee
    have guarantee := typed (by rfl) (by simpa only [circuit_norm] using secondMult)
    change ByteRowSpec (Eval.eval env second.msg) at guarantee
    exact guarantee
  have firstMsgEq : Eval.eval env first.msg =
      (⟨6, Expression.eval env input.mem.access_timestamp.diff_low_limb,
        ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (ZMod p)) := by
    dsimp only [first, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      Expression.eval]
  have secondMsgEq : Eval.eval env second.msg =
      (⟨3, 0, Expression.eval env input.mem.access_timestamp.diff_high_limb, 0⟩ :
        ByteRow (ZMod p)) := by
    dsimp only [second, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      Expression.eval]
  rw [firstMsgEq] at firstSpec
  rw [secondMsgEq] at secondSpec
  exact ⟨(byteRowSpec_range _ sixteen_lt).mp firstSpec,
    ((byteRowSpec_u8range_pair _ _).mp secondSpec).1⟩

/-- The retained RAM reader's three equality constraints and two Byte pulls imply exactly its
active timestamp facts, without asking for its Memory-channel guarantee or full `Spec`.

This is the non-circular semantic boundary needed by `ChipGroundingContracts.rowAligned`: the
timed walk needs timestamp order before it can establish the Memory pull currency from which the
reader's remaining `Spec` conjuncts follow. -/
theorem Readers.MemoryAccess.timestampFacts_of_constraintsAndByteGuarantees
    (input : Var Readers.MemoryAccess.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints :
      ((Readers.MemoryAccess.main input).operations offset).ConstraintsHold env)
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.MemoryAccess.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveMemoryTimestampFacts
      (Expression.eval env input.mem.access_timestamp.compare_low)
      (Expression.eval env input.mem.access_timestamp.prev_high)
      (Expression.eval env input.mem.access_timestamp.prev_low)
      (Expression.eval env input.mem.access_timestamp.diff_low_limb)
      (Expression.eval env input.mem.access_timestamp.diff_high_limb)
      (Expression.eval env input.clk_high)
      (Expression.eval env input.clk_low) := by
  simp only [Readers.MemoryAccess.main, Circuit.operations, Circuit.bind_def,
    assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Channel.pushIf, Operations.localLength,
    operationsConstraintsHold_append] at constraints
  obtain ⟨_, compareConstraints, highConstraints, gapConstraints, _⟩ := constraints
  have compareEq :=
    equality_of_singleton_constraintsHold env _ _ _ compareConstraints
  have highEq :=
    equality_of_singleton_constraintsHold env _ _ _ highConstraints
  have gapEq :=
    equality_of_singleton_constraintsHold env _ _ _ gapConstraints
  have bounds := Readers.MemoryAccess.diffBounds_of_byteGuarantees input offset env guarantees real
  dsimp only at compareEq highEq gapEq
  simp only [Expression.eval, eval_sub, real, one_mul] at compareEq highEq gapEq
  refine ⟨bool_of_mul_pred compareEq, highEq, ?_, bounds.1, bounds.2⟩
  exact sub_eq_zero.mp gapEq

/-- The generic RAM timestamp payoff at the bus layer. The low-component branch uses the ordinary
Memory `ClkBound`; the high-component branch uses the separately disclosed physical high bound.
In both branches strict order is derived from `ActiveMemoryTimestampFacts`, not assumed. -/
theorem memoryTimeNat_lt_of_memoryAccessFacts
    (prior pushed : MemoryMsg (ZMod p))
    (compare prevHigh prevLow diffLow diffHigh clkHigh clkLow : ZMod p)
    (prevLowBound : MemoryMsg.ClkBound prior)
    (prevHighBound : prior.clk_high.val < 2 ^ 24)
    (facts : ActiveMemoryTimestampFacts
      compare prevHigh prevLow diffLow diffHigh clkHigh clkLow)
    (priorHigh : prior.clk_high = prevHigh)
    (priorLow : prior.clk_low = prevLow)
    (pushedHigh : pushed.clk_high = clkHigh)
    (pushedLow : pushed.clk_low = clkLow + 1) :
    Semantics.MemoryMsg.timeNat prior < Semantics.MemoryMsg.timeNat pushed := by
  rcases facts with ⟨compareBinary, sameHigh, gap, diffLowBound, diffHighBound⟩
  rcases compareBinary with compareZero | compareOne
  · rw [compareZero] at sameHigh gap
    have highComponent : prevHigh.val < clkHigh.val := by
      apply TimeExtraction.component_val_lt_of_accessTimestampGap
        clkHigh prevHigh diffLow diffHigh
      · rw [← priorHigh]
        exact prevHighBound
      · exact diffLowBound
      · exact diffHighBound
      · simpa using gap
    simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat, priorHigh, priorLow,
      pushedHigh, pushedLow]
    have lowBound : prevLow.val < 2 ^ 24 := by
      rw [← priorLow]
      exact prevLowBound
    omega
  · rw [compareOne] at sameHigh gap
    have highEq : clkHigh = prevHigh := by
      exact sub_eq_zero.mp (by simpa using sameHigh)
    have lowComponent : prevLow.val < (clkLow + 1).val := by
      apply TimeExtraction.component_val_lt_of_accessTimestampGap
        (clkLow + 1) prevLow diffLow diffHigh
      · rw [← priorLow]
        exact prevLowBound
      · exact diffLowBound
      · exact diffHighBound
      · simpa using gap
    simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat, priorHigh, priorLow,
      pushedHigh, pushedLow, highEq]
    omega

/-- The outer `RegisterAccessCols` assertion inherits the timestamp bounds from its retained inner
`RegisterAccessTimestamp` assertion using only Byte-channel guarantees.  This is the reusable
two-level descent missing from the original grounding prototype: no Memory guarantee or completed
reader `Spec` is involved. -/
theorem Readers.RegisterAccessCols.bounds_of_byteGuarantees
    (input : Var Readers.RegisterAccessCols.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env input.cols.access_timestamp.diff_low_limb).val < 2 ^ 16 ∧
      ((Expression.eval env input.clk_target -
        Expression.eval env input.cols.access_timestamp.prev_low - 1 -
        Expression.eval env input.cols.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹).val < 2 ^ 8 := by
  let timestampInput : Var Readers.RegisterAccessTimestamp.Inputs (ZMod p) :=
    ⟨input.cols.access_timestamp, input.is_real, input.clk_target⟩
  have outerGuarantees :
      ((Readers.RegisterAccessCols.main input).operations offset).ChannelGuarantees
        byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_formalAssertion byteChannel.toRaw env
      Readers.RegisterAccessCols.circuit offset input).mp guarantees
  have timestampGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.RegisterAccessCols.main input).operations offset)
    ((Readers.RegisterAccessTimestamp.circuit (p := p)).toSubcircuit offset timestampInput)
    (by simp only [timestampInput, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, circuit_norm]) outerGuarantees
  exact Readers.RegisterAccessTimestamp.bounds_of_byteGuarantees timestampInput offset env
    timestampGuarantees real

/-- All three R-type register-access timestamp contracts follow from the Byte guarantees of the
retained `RTypeReader` subcircuit.  The result is intentionally stated only on evaluated scalar
fields, so chip-level bindings can rewrite it to their independent semantic row layouts without
asking unification to unfold either a completed chip `Spec` or an evaluated nested reader struct. -/
theorem Readers.RTypeReader.timestampSpecs_of_byteGuarantees
    (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.RTypeReader.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveTimestampBounds
        (Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 4)) ∧
      ActiveTimestampBounds
        (Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 3)) ∧
      ActiveTimestampBounds
        (Expression.eval env input.cols.op_c_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_c_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 2)) := by
  let inputA : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  let inputB : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  let inputC : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_c_memory, input.is_real, input.clk_low + 2⟩
  have readerGuarantees :
      ((Readers.RTypeReader.main input).operations offset).ChannelGuarantees byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
      Readers.RTypeReader.circuit offset input).mp guarantees
  have guaranteesA := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.RTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset inputA)
    (by simp only [inputA, Readers.RTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have guaranteesB := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.RTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0) inputB)
    (by simp only [inputB, Readers.RTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have guaranteesC := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.RTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0 + 0) inputC)
    (by simp only [inputC, Readers.RTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have boundsA := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputA offset env
    guaranteesA real
  have boundsB := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputB (offset + 0) env
    guaranteesB real
  have boundsC := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputC (offset + 0 + 0) env
    guaranteesC real
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ActiveTimestampBounds, inputA] using boundsA
  · simpa only [ActiveTimestampBounds, inputB] using boundsB
  · simpa only [ActiveTimestampBounds, inputC] using boundsC

/-- Both I-type register-access timestamp contracts follow from the Byte guarantees of the retained
`ITypeReader`.  The destination prior record is checked against the `+4` write slot and the sole
register source against its `+3` read-back slot; the immediate operand has no Memory access. -/
theorem Readers.ITypeReader.timestampSpecs_of_byteGuarantees
    (input : Var Readers.ITypeReader.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.ITypeReader.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveTimestampBounds
        (Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 4)) ∧
      ActiveTimestampBounds
        (Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 3)) := by
  let inputA : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  let inputB : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  have readerGuarantees :
      ((Readers.ITypeReader.main input).operations offset).ChannelGuarantees byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
      Readers.ITypeReader.circuit offset input).mp guarantees
  have guaranteesA := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ITypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset inputA)
    (by simp only [inputA, Readers.ITypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have guaranteesB := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ITypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0) inputB)
    (by simp only [inputB, Readers.ITypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have boundsA := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputA offset env
    guaranteesA real
  have boundsB := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputB (offset + 0) env
    guaranteesB real
  constructor
  · simpa only [ActiveTimestampBounds, inputA] using boundsA
  · simpa only [ActiveTimestampBounds, inputB] using boundsB

/-- The sole J-type register-access timestamp contract follows from the retained reader's Byte
guarantees.  The `op_a` prior record is checked against the `+4` destination slot; whether that slot
is an architectural write (`rd ≠ x0`) or a zero-register read-back (`rd = x0`) is decided by the
enclosing chip's semantic `CommitEffect`, not by the timestamp reader. -/
theorem Readers.JTypeReader.timestampSpec_of_byteGuarantees
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.JTypeReader.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveTimestampBounds
      (Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low)
      (Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb)
      (Expression.eval env (input.clk_low + 4)) := by
  let inputA : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  have readerGuarantees :
      ((Readers.JTypeReader.main input).operations offset).ChannelGuarantees
        byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
      Readers.JTypeReader.circuit offset input).mp guarantees
  have guaranteesA := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.JTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset inputA)
    (by simp only [inputA, Readers.JTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have boundsA := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputA offset env
    guaranteesA real
  simpa only [ActiveTimestampBounds, inputA] using boundsA

/-- The immutable I-type reader has the same two timestamp checks as `ITypeReader`; only the
destination slot's value policy changes from write to read-back. -/
theorem Readers.ITypeReaderImmutable.timestampSpecs_of_byteGuarantees
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveTimestampBounds
        (Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 4)) ∧
      ActiveTimestampBounds
        (Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 3)) := by
  let inputA : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  let inputB : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  have readerGuarantees :
      ((Readers.ITypeReaderImmutable.main input).operations offset).ChannelGuarantees
        byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
      Readers.ITypeReaderImmutable.circuit offset input).mp guarantees
  have guaranteesA := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ITypeReaderImmutable.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset inputA)
    (by simp only [inputA, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, circuit_norm]) readerGuarantees
  have guaranteesB := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ITypeReaderImmutable.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0) inputB)
    (by simp only [inputB, Readers.ITypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, circuit_norm]) readerGuarantees
  have boundsA := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputA offset env
    guaranteesA real
  have boundsB := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputB (offset + 0) env
    guaranteesB real
  constructor
  · simpa only [ActiveTimestampBounds, inputA] using boundsA
  · simpa only [ActiveTimestampBounds, inputB] using boundsB

/-- The three ALU-reader timestamp contracts follow from its retained Byte guarantees.  The
destination and source-B slots are active on every real row; source C is required only on the
register form (`imm_c = 0`), exactly matching its `is_real - imm_c` interaction gate. -/
theorem Readers.ALUTypeReader.timestampSpecs_of_byteGuarantees
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.ALUTypeReader.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveTimestampBounds
        (Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 4)) ∧
      ActiveTimestampBounds
        (Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 3)) ∧
      (Expression.eval env input.cols.imm_c = 0 →
        ActiveTimestampBounds
          (Expression.eval env input.cols.op_c_memory.access_timestamp.prev_low)
          (Expression.eval env input.cols.op_c_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (input.clk_low + 2))) := by
  let inputA : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  let inputB : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  let inputC : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_c_memory, input.is_real - input.cols.imm_c, input.clk_low + 2⟩
  have readerGuarantees :
      ((Readers.ALUTypeReader.main input).operations offset).ChannelGuarantees
        byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
      Readers.ALUTypeReader.circuit offset input).mp guarantees
  have guaranteesA := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ALUTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset inputA)
    (by simp only [inputA, Readers.ALUTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have guaranteesB := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ALUTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0) inputB)
    (by simp only [inputB, Readers.ALUTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have guaranteesC := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ALUTypeReader.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0 + 0) inputC)
    (by simp only [inputC, Readers.ALUTypeReader.main, Readers.RegisterAccessCols.circuit,
      circuit_norm]) readerGuarantees
  have boundsA := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputA offset env
    guaranteesA real
  have boundsB := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputB (offset + 0) env
    guaranteesB real
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ActiveTimestampBounds, inputA] using boundsA
  · simpa only [ActiveTimestampBounds, inputB] using boundsB
  · intro immediate
    have activeC : Expression.eval env (input.is_real - input.cols.imm_c) = 1 := by
      simp only [eval_sub, real, immediate, sub_zero]
    have boundsC := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputC (offset + 0 + 0) env
      guaranteesC activeC
    simpa only [ActiveTimestampBounds, inputC] using boundsC

/-- The immutable ALU reader has the same timestamp gates as `ALUTypeReader`; its `op_a` access is
a read-back rather than a write. -/
theorem Readers.ALUTypeReaderImmutable.timestampSpecs_of_byteGuarantees
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.ALUTypeReaderImmutable.circuit (p := p)).toSubcircuit offset input).ops.toFlat)
    (real : Expression.eval env input.is_real = 1) :
    ActiveTimestampBounds
        (Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_a_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 4)) ∧
      ActiveTimestampBounds
        (Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low)
        (Expression.eval env input.cols.op_b_memory.access_timestamp.diff_low_limb)
        (Expression.eval env (input.clk_low + 3)) ∧
      (Expression.eval env input.cols.imm_c = 0 →
        ActiveTimestampBounds
          (Expression.eval env input.cols.op_c_memory.access_timestamp.prev_low)
          (Expression.eval env input.cols.op_c_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (input.clk_low + 2))) := by
  let inputA : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  let inputB : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  let inputC : Var Readers.RegisterAccessCols.Inputs (ZMod p) :=
    ⟨input.cols.op_c_memory, input.is_real - input.cols.imm_c, input.clk_low + 2⟩
  have readerGuarantees :
      ((Readers.ALUTypeReaderImmutable.main input).operations offset).ChannelGuarantees
        byteChannel.toRaw env :=
    (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
      Readers.ALUTypeReaderImmutable.circuit offset input).mp guarantees
  have guaranteesA := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ALUTypeReaderImmutable.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit offset inputA)
    (by simp only [inputA, Readers.ALUTypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, circuit_norm]) readerGuarantees
  have guaranteesB := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ALUTypeReaderImmutable.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0) inputB)
    (by simp only [inputB, Readers.ALUTypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, circuit_norm]) readerGuarantees
  have guaranteesC := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    ((Readers.ALUTypeReaderImmutable.main input).operations offset)
    ((Readers.RegisterAccessCols.circuit (p := p)).toSubcircuit (offset + 0 + 0) inputC)
    (by simp only [inputC, Readers.ALUTypeReaderImmutable.main,
      Readers.RegisterAccessCols.circuit, circuit_norm]) readerGuarantees
  have boundsA := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputA offset env
    guaranteesA real
  have boundsB := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputB (offset + 0) env
    guaranteesB real
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ActiveTimestampBounds, inputA] using boundsA
  · simpa only [ActiveTimestampBounds, inputB] using boundsB
  · intro immediate
    have activeC : Expression.eval env (input.is_real - input.cols.imm_c) = 1 := by
      simp only [eval_sub, real, immediate, sub_zero]
    have boundsC := Readers.RegisterAccessCols.bounds_of_byteGuarantees inputC
      (offset + 0 + 0) env guaranteesC activeC
    simpa only [ActiveTimestampBounds, inputC] using boundsC

/-- The scalar end of clock extraction: once a chip has isolated its CPU reader's Byte guarantees
and four field bindings, no circuit structure remains in the no-wraparound argument. -/
theorem stateTimeStep_of_cpuState_byteGuarantees
    (cpuInput : Var Readers.CPUState.Inputs (ZMod p)) (cpuOffset : ℕ)
    (env : Environment (ZMod p)) (rowView : Trace.RowView (ZMod p))
    (guarantees : FlatOperation.ChannelGuarantees byteChannel.toRaw env
      ((Readers.CPUState.circuit (p := p)).toSubcircuit cpuOffset cpuInput).ops.toFlat)
    (binding : CPUStateTimeBinding (Expression.eval env cpuInput.is_real)
      (Expression.eval env cpuInput.cols.clk_high)
      (Expression.eval env cpuInput.cols.clk_0_16)
      (Expression.eval env cpuInput.cols.clk_16_24) rowView)
    (real : rowView.is_real = 1) :
    Semantics.StateMsg.timeNat (statePushOfView rowView) =
      Semantics.StateMsg.timeNat (statePullOfView rowView) + 8 := by
  have cpuReal : Expression.eval env cpuInput.is_real = 1 := binding.real_eq.trans real
  obtain ⟨clk0Bound, clk1Bound⟩ :=
    Readers.CPUState.bounds_of_byteGuarantees cpuInput cpuOffset env guarantees cpuReal
  change Semantics.clkNat rowView.state.clk_high
      (rowView.state.clk_0_16 + rowView.state.clk_16_24 * 65536 + 8) =
    Semantics.clkNat rowView.state.clk_high
      (rowView.state.clk_0_16 + rowView.state.clk_16_24 * 65536) + 8
  rw [← binding.clkHigh_eq, ← binding.clk0_eq, ← binding.clk1_eq]
  exact TimeExtraction.clkNat_add_eight_of_cpuState_bounds
    (Expression.eval env cpuInput.cols.clk_high)
    (Expression.eval env cpuInput.cols.clk_0_16)
    (Expression.eval env cpuInput.cols.clk_16_24) clk0Bound clk1Bound

set_option maxHeartbeats 1000000 in
/-- A retained `CPUState` reader plus the finished Byte guarantees proves exact eight-tick progress
for the completed chip circuit.  This is the reusable bridge from local chip composition to the
natural-number ranking used by the State trail. -/
theorem circuitStateTimeStep_of_cpuStateContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitCPUStateTimeContract circuit view) :
    CircuitStateTimeStep circuit view := by
  constructor
  unfold CircuitCPUStateTimeContract at contract
  dsimp only at contract
  obtain ⟨cpuOffset, cpuInput, cpuMem, binding⟩ := contract
  intro data physical
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  change component.operations.ChannelGuarantees byteChannel.toRaw env → rowView.is_real = 1 →
    Semantics.StateMsg.timeNat (statePushOfView rowView) =
      Semantics.StateMsg.timeNat (statePullOfView rowView) + 8
  intro guarantees real
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have cpuGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.CPUState.circuit (p := p)).toSubcircuit cpuOffset cpuInput) cpuMem rowGuarantees
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  have bound := binding env
  rw [inputEq, outputEq] at bound
  exact stateTimeStep_of_cpuState_byteGuarantees cpuInput cpuOffset env rowView
    cpuGuarantees bound real

end SP1Clean.Soundness
