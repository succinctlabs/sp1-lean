import SP1Clean.Soundness.GroundingAdapter
import SP1Clean.Proofs.Chips.JalChip.Bridge
import SP1Clean.Proofs.Chips.UTypeChip.Bridge

/-! # Canonical J-type grounding

JAL and U-type rows share SP1's one-access `JTypeReader`: a destination prior pull and a
`RegisterWrite` push at `clk + 4`; both remaining operands are immediates.  The destination may be
`x0`.  In that case the physical push still exists, but carries the reader-zeroed result rather
than a syntactic copy of the prior-value column.  The generic `RowWiring` x0 arm records precisely
that upstream behavior.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Functions
open Air.Flat Circuit
open SP1Clean.Soundness.Target
open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

section Shape

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The retained J-type reader's zero-register gates force the factored destination-write word to
zero.  This is the value half of the physical `rd = x0` push case; it is derived from the folded
reader `Spec`, not postulated by the grounding layer. -/
theorem jtypeWrite_zero_of_spec (input : Readers.JTypeReader.Inputs (ZMod p))
    (spec : Readers.JTypeReader.Spec input) (flag : input.cols.op_a_0 = 1) :
    Word.toBitVec64 (#v[input.wv0, input.wv1, input.wv2, input.wv3] : Word (ZMod p)) = 0 := by
  obtain ⟨⟨z0, z1, z2, z3⟩, -⟩ := spec
  rw [flag, one_mul] at z0 z1 z2 z3
  simp [Word.toBitVec64, Word.toNat_def, z0, z1, z2, z3]

/-- The exact two Memory interactions of a J-type row. -/
noncomputable def jtypeMemoryInteractions (view : Trace.RowView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (rtypeWriteMessage view)]

/-- Descriptor-level J-type shape, including the two immediate markers used by operand binding. -/
structure JTypeMemoryInteractionShape (chip : SupportedChip p) : Prop where
  interactions : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        jtypeMemoryInteractions (decoded.toChipRow data).view
  imm_b_eq_one : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip → (decoded.toChipRow data).view.adapter.imm_b = 1
  imm_c_eq_one : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip → (decoded.toChipRow data).view.adapter.imm_c = 1

omit [Fact (2 ^ 25 < p)] in
private theorem jtypePull_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 msg).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem jtypePush_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 1 msg).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_jtypeTwo (a w : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [a] := by
  unfold consumedMessages
  simp only [List.filter_cons, List.filter_nil, jtypePull_one_signed,
    jtypePush_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_jtypeTwo (a w : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [w] := by
  unfold producedMessages
  simp only [List.filter_cons, List.filter_nil, jtypePull_one_signed,
    jtypePush_one_signed]
  norm_num

/-- An active J-type row consumes exactly its destination prior record. -/
theorem consumedMemoryMessages_eq_of_jtypeShape {chip : SupportedChip p}
    (shape : JTypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold jtypeMemoryInteractions
  rw [real]
  exact consumedMessages_jtypeTwo _ _

/-- An active J-type row produces exactly its destination-slot push. -/
theorem producedMemoryMessages_eq_of_jtypeShape {chip : SupportedChip p}
    (shape : JTypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data = [rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold jtypeMemoryInteractions
  rw [real]
  exact producedMessages_jtypeTwo _ _

/-- Wiring for the one-access J-type window, including its honest `rd = x0` push case. -/
theorem rowWiring_jtype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.destination view.adapter.op_a_0)
    (op_a_0_binary : view.adapter.op_a_0 = 0 ∨ view.adapter.op_a_0 = 1)
    (imm_b_eq : view.adapter.imm_b = 1)
    (imm_c_eq : view.adapter.imm_c = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 view.rdWrite)
    (zero_index : view.adapter.op_a_0 = 1 → view.adapter.op_a = 0)
    (zero_value : view.adapter.op_a_0 = 1 → Word.toBitVec64 view.rdWrite = 0)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes = [rtypeWriteMessage view]) :
    RowWiring view rf where
  statePull_eq := statePull_eq
  statePush_eq := statePush_eq
  time8 := by
    rw [statePull_eq, statePush_eq]
    exact timeNat_statePushOfView_eight bounds
  readTime := by
    intro mp hmp
    rw [pulls_eq] at hmp
    simp only [List.mem_singleton] at hmp
    subst mp
    rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · simp [pulls_eq]
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index immediate indexEq
    rw [imm_b_eq] at immediate
    exact absurd immediate one_ne_zero
  opC_pull := by
    intro index immediate indexEq
    rw [imm_c_eq] at immediate
    exact absurd immediate one_ne_zero
  write_push := by
    intro _ index indexEq
    refine ⟨rtypeWriteMessage view, ?_, ?_, rfl⟩
    · simp [pushes_eq]
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  push_classified := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_singleton] at messageMem
    subst message
    rcases op_a_0_binary with opA0 | opA0
    · refine Or.inr (Or.inl ?_)
      have indexEq : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
          view.adapter.op_a := by
        rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
        exact ZMod.natCast_zmod_val _
      refine ⟨?_, write_isU64, ?_, rfl, ?_⟩
      · rw [commit_eq]
        unfold Trace.CommitEffect.destination
        rw [if_pos opA0]
        rfl
      · exact ⟨BitVec.ofNat 5 view.adapter.op_a.val,
          MemoryMsg.locOf_register _ _ indexEq rfl rfl, indexEq⟩
      · rw [timeNat_rtypeWriteMessage bounds, ← statePull_eq]
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have indexEq : (((0#5 : BitVec 5).toNat : ℕ) : ZMod p) = view.adapter.op_a := by
        simp [zero_index opA0]
      refine ⟨?_, write_isU64, MemoryMsg.locOf_register _ 0#5 indexEq rfl rfl,
        zero_value opA0, ?_⟩
      · rw [commit_eq]
        unfold Trace.CommitEffect.destination
        rw [if_neg (by simp [opA0])]
        rfl
      · rw [timeNat_rtypeWriteMessage bounds, ← statePull_eq]
  push_clkBound := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_singleton] at messageMem
    subst message
    exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
      (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program s s' heff _ cell v _ hcontent
    rw [locContent_ram_congr (heff.mem.1 (by
      rw [commit_eq]
      unfold Trace.CommitEffect.destination
      split <;> rfl)) cell]
    exact hcontent

/-- The sole J-type touch, at the destination effect slot. -/
def jtypeTouches (view : Trace.RowView (ZMod p)) (rf : Semantics.RowFacts p) : List (Touch p) :=
  [((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
       StateMsg.timeNat rf.statePull),
     rtypeWriteMessage view)]

/-- Aligned carrier for the one-access J-type window. -/
theorem rowAligned_jtype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (_real : view.is_real = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes = [rtypeWriteMessage view])
    (hslot : SP1Clean.Channels.MemoryMsg.ClkBound
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) →
      MemoryMsg.timeNat
          (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) <
        MemoryMsg.timeNat (rtypeWriteMessage view)) :
    AlignsWith (alignedOf rf (jtypeTouches view rf)) rf ∧
      (∀ tc ∈ jtypeTouches view rf,
        TouchOK (StateMsg.timeNat rf.statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((jtypeTouches view rf).filter (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ jtypeTouches view rf, SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ jtypeTouches view rf,
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have indexEq : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
      view.adapter.op_a := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  have priorLoc : MemoryMsg.locOf
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
    MemoryMsg.locOf_register _ _ indexEq rfl rfl
  have pushLoc : MemoryMsg.locOf (rtypeWriteMessage view) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
    MemoryMsg.locOf_register _ _ indexEq rfl rfl
  have pushTime : MemoryMsg.timeNat (rtypeWriteMessage view) =
      StateMsg.timeNat rf.statePull + 4 := by
    rw [statePull_eq]
    exact timeNat_rtypeWriteMessage bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine alignsWith_alignedOf rf (jtypeTouches view rf) ?_ ?_ ?_ ?_ ?_
    · rw [pushes_eq]
      simp [jtypeTouches]
    · rw [pulls_eq]
      simp [jtypeTouches]
    · intro mp mpMem
      rw [pulls_eq] at mpMem
      simp only [List.mem_singleton] at mpMem
      subst mp
      exact ⟨_, priorLoc⟩
    · intro mp mpMem
      rw [pulls_eq] at mpMem
      simp only [List.mem_singleton] at mpMem
      subst mp
      rfl
    · intro mp mpMem
      rw [pulls_eq] at mpMem
      simp only [List.mem_singleton] at mpMem
      subst mp
      refine ⟨((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
        StateMsg.timeNat rf.statePull), rtypeWriteMessage view), ?_, rfl, le_refl _, ?_⟩
      · simp [jtypeTouches]
      · dsimp only
        omega
  · intro tc tcMem
    simp only [jtypeTouches, List.mem_singleton] at tcMem
    subst tc
    refine ⟨?_, le_refl _, ?_, Or.inr ?_⟩
    · exact pushLoc.trans priorLoc.symm
    · simp only [priorLoc, readWindow_reg]
      omega
    · rw [pushLoc, writeOffset_reg]
      exact pushTime
  · intro loc
    by_cases sameLoc : MemoryMsg.locOf (rtypeWriteMessage view) = loc
    · simp [jtypeTouches, sameLoc]
    · simp [jtypeTouches, sameLoc]
  · intro tc tcMem
    simp only [jtypeTouches, List.mem_singleton] at tcMem
    subst tc
    exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
      (by omega) bounds.clk0 bounds.clk1
  · intro tc tcMem pullBound
    simp only [jtypeTouches, List.mem_singleton] at tcMem
    subst tc
    exact hslot pullBound

/-- Construct `RowWiring` from a descriptor's exact J-type shape. -/
theorem rowWiring_jtype_of_shape {chip : SupportedChip p}
    (shape : JTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq : (decoded.toChipRow data).view.commit =
      Trace.CommitEffect.destination (decoded.toChipRow data).view.adapter.op_a_0)
    (op_a_0_binary : (decoded.toChipRow data).view.adapter.op_a_0 = 0 ∨
      (decoded.toChipRow data).view.adapter.op_a_0 = 1)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 (decoded.toChipRow data).view.rdWrite)
    (zero_index : (decoded.toChipRow data).view.adapter.op_a_0 = 1 →
      (decoded.toChipRow data).view.adapter.op_a = 0)
    (zero_value : (decoded.toChipRow data).view.adapter.op_a_0 = 1 →
      Word.toBitVec64 (decoded.toChipRow data).view.rdWrite = 0) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  have consumed := consumedMemoryMessages_eq_of_jtypeShape shape decoded data hchip real
  have produced := producedMemoryMessages_eq_of_jtypeShape shape decoded data hchip real
  refine rowWiring_jtype bounds commit_eq op_a_0_binary
    (shape.imm_b_eq_one decoded data hchip) (shape.imm_c_eq_one decoded data hchip)
    opa_lt write_isU64 zero_index zero_value rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]

/-- The active J-type destination timestamp. -/
def JTypeTimestampBound (view : Trace.RowView (ZMod p)) : Prop :=
  ActiveTimestampBounds view.adapter.op_a_memory.access_timestamp.prev_low
    view.adapter.op_a_memory.access_timestamp.diff_low_limb
    (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4)

/-- Scalar binding between a retained `JTypeReader` and its semantic row view. -/
structure JTypeTimestampBinding (readerReal prev diff target : ZMod p)
    (view : Trace.RowView (ZMod p)) : Prop where
  real_eq : readerReal = view.is_real
  prev_eq : prev = view.adapter.op_a_memory.access_timestamp.prev_low
  diff_eq : diff = view.adapter.op_a_memory.access_timestamp.diff_low_limb
  target_eq : target = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4

/-- A chip-local retained J-type reader contract, kept folded at the chip boundary. -/
inductive CircuitJTypeTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (readerOffset : ℕ) (readerInput : Var Readers.JTypeReader.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.JTypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        JTypeTimestampBinding
          (Expression.eval env readerInput.is_real)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (readerInput.clk_low + 4))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env
              (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))) :
      CircuitJTypeTimestampContract circuit view

/-- Finished Byte guarantees specialize a retained J-type reader to the row view. -/
theorem jtypeTimestampBound_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitJTypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    JTypeTimestampBound (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.JTypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput)
    readerMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env
      (circuit.output (varFromOffset Input 0) (size Input)) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have readerReal : Expression.eval env readerInput.is_real = 1 :=
    bound.real_eq.trans real
  have timestamp := Readers.JTypeReader.timestampSpec_of_byteGuarantees readerInput
    readerOffset env readerGuarantees readerReal
  unfold JTypeTimestampBound
  rwa [bound.prev_eq, bound.diff_eq, bound.target_eq] at timestamp

/-- Construct the aligned carrier of an exact J-type row. -/
theorem rowAligned_jtype_of_shape {chip : SupportedChip p}
    (shape : JTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestamp : JTypeTimestampBound (decoded.toChipRow data).view)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32) :
    AlignsWith (alignedOf (decoded.ordinaryRowFacts data)
        (jtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data)))
        (decoded.ordinaryRowFacts data) ∧
      (∀ tc ∈ jtypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((jtypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data)).filter
            (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ jtypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ jtypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have consumed := consumedMemoryMessages_eq_of_jtypeShape shape decoded data hchip real
  have produced := producedMemoryMessages_eq_of_jtypeShape shape decoded data hchip real
  have slot : SP1Clean.Channels.MemoryMsg.ClkBound
      (rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory) →
    MemoryMsg.timeNat
        (rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory) <
      MemoryMsg.timeNat (rtypeWriteMessage (decoded.toChipRow data).view) := by
    intro pullBound
    exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
      _ _ _ _ _ pullBound timestamp rfl rfl rfl
  refine rowAligned_jtype bounds real opa_lt rfl ?_ ?_ slot
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]

end Shape

section Jal

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- JAL's descriptor in the supported Core registry. -/
def jalChipDescriptor : SupportedChip p :=
  ⟨JalChip.kind, JalChip.circuit, rfl, [.JAL], .any⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def jalViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  JalChip.rowView
    ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem jalViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((jalChipDescriptor (p := p)).decodeRow data physical).view =
      jalViewOf (Environment.fromArray physical data) := rfl

theorem jalChipDescriptor_table :
    (jalChipDescriptor (p := p)).table =
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

/-- Folded descriptor projection for JAL's circuit assumptions.  Consumers rewrite through this
small theorem instead of asking unification to normalize the complete circuit-bearing descriptor. -/
theorem jalChipDescriptor_assumptions_iff (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    (jalChipDescriptor (p := p)).table.Assumptions
        (Environment.fromArray physical data) ↔
      JalChip.Assumptions
        ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data)) data := by
  rw [jalChipDescriptor_table]
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem jalEqualityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

omit [Fact (2 ^ 25 < p)] in
/-- JAL's explicit high-limb assertion is the `advanceReady` fact connecting its four-limb add
result to the three-limb architectural next-PC view. -/
theorem JalChip.addValueHigh_eq_zero_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
      env).add_operation.value[3] = 0 := by
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  let addValue : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  have mainConstraints : ((JalChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have highConstraint : Expression.eval env (addValue[3] - 0) = 0 := by
    apply mainConstraints.1
    simp only [input, offset, addValue, JalChip.main, circuit_norm]
    right
    right
    left
    simpa only [offset, circuit_norm, FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      jalEqualityConstraint_mem (var { index := offset + 3 }) 0 _
  rw [eval_sub] at highConstraint
  have highEq : Expression.eval env addValue[3] = 0 := by
    simpa only [Expression.eval, sub_zero] using highConstraint
  have outputEq : Eval.eval env
      ((JalChip.circuit (p := p)).output input offset) =
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  rw [← outputEq]
  simpa only [input, offset, addValue, JalChip.circuit, circuit_norm] using highEq

omit [Fact (2 ^ 25 < p)] in
theorem jalViewOf_state (env : Environment (ZMod p)) :
    (jalViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) JalChip.Inputs 0)).state := by
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  have outputEq : Eval.eval env ((JalChip.circuit (p := p)).output input offset) =
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [jalViewOf, JalChip.rowView]
  rw [← outputEq]
  simp only [input, offset, JalChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem jalViewOf_adapter (env : Environment (ZMod p)) :
    (jalViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) JalChip.Inputs 0)).adapter.toAdapterView := by
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  have outputEq : Eval.eval env ((JalChip.circuit (p := p)).output input offset) =
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [jalViewOf, JalChip.rowView]
  rw [← outputEq]
  simp only [input, offset, JalChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem jalViewOf_isReal (env : Environment (ZMod p)) :
    (jalViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) JalChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset JalChip.Inputs 0) =
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset JalChip.Inputs 0 env
  simpa only [jalViewOf, JalChip.rowView] using
    congrArg (fun input : JalChip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] in
theorem jalViewOf_rdWrite (env : Environment (ZMod p)) :
    (jalViewOf env).rdWrite =
      Eval.eval env ((Vector.mapRange 4 fun i =>
        var { index := size JalChip.Inputs + 4 + i }) : Word (Expression (ZMod p))) := by
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  have outputEq : Eval.eval env ((JalChip.circuit (p := p)).output input offset) =
      (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [jalViewOf, JalChip.rowView]
  rw [← outputEq]
  simp only [input, offset, JalChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- JAL's completed exposed Memory list evaluates to the canonical J-type pair. -/
theorem jalChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (jtypeMemoryInteractions (jalViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((JalChip.main (varFromOffset JalChip.Inputs 0)).operations
        (size JalChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [JalChip.interactionsWith_memory_eq]
  simp only [JalChip.exposedMemoryInteractions, jtypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeWriteMessage, jalViewOf_state, jalViewOf_adapter,
    jalViewOf_isReal, jalViewOf_rdWrite, Extracted.JTypeReader.toAdapterView, circuit_norm]

/-- Lift JAL's evaluated pair to the typed decoded-row boundary. -/
theorem jalChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = jalChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      jtypeMemoryInteractions (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    jalViewOf_decodeRow, jalChipDescriptor_table] using
    jalChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- JAL instantiates the canonical J-type Memory shape. -/
theorem jalChip_jtypeMemoryInteractionShape :
    JTypeMemoryInteractionShape (jalChipDescriptor (p := p)) where
  interactions := jalChip_typedMemoryInteractions_eq
  imm_b_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = jalChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = jalChipDescriptor (p := p) := hchip
    subst hchip'
    rfl

/-- The exact J-type reader input retained after JAL's two four-limb witness vectors. -/
def jalChipJTypeInput (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.JTypeReader.Inputs (ZMod p) :=
  let opAValue : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 4 + i }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 46,
    opAValue[0], opAValue[1], opAValue[2], opAValue[3]⟩

omit [Fact (2 ^ 25 < p)] in
theorem JalChip.jtypeTimestampContract :
    CircuitJTypeTimestampContract (p := p) (JalChip.circuit (p := p))
      JalChip.rowView := by
  let input : Var JalChip.Inputs (ZMod p) := varFromOffset JalChip.Inputs 0
  let offset := size JalChip.Inputs
  let readerInput : Var Readers.JTypeReader.Inputs (ZMod p) :=
    jalChipJTypeInput input offset
  refine .intro (offset + 8) readerInput ?_ ?_
  · simp only [input, offset, readerInput, jalChipJTypeInput, JalChip.circuit,
      JalChip.main, Readers.JTypeReader.circuit, circuit_norm]
    right
    right
    right
    right
    right
    left
    rfl
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, jalChipJTypeInput, JalChip.circuit,
        JalChip.rowView, Extracted.JTypeReader.toAdapterView, circuit_norm]

theorem jalChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = jalChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (JalChip.circuit (p := p)) JalChip.rowView
    JalChip.cpuStateTimeContract data physical guarantees real

theorem jalChip_activeTimestampBound (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = jalChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    JTypeTimestampBound (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  exact jtypeTimestampBound_of_contract (JalChip.circuit (p := p)) JalChip.rowView
    JalChip.jtypeTimestampContract data physical guarantees real

end Jal

section UType

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- U-type's descriptor in the supported Core registry. -/
def uTypeChipDescriptor : SupportedChip p :=
  ⟨UTypeChip.kind, UTypeChip.circuit, rfl, [.AUIPC, .LUI], .any⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def uTypeViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  UTypeChip.rowView
    ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem uTypeViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((uTypeChipDescriptor (p := p)).decodeRow data physical).view =
      uTypeViewOf (Environment.fromArray physical data) := rfl

theorem uTypeChipDescriptor_table :
    (uTypeChipDescriptor (p := p)).table =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

/-- Folded descriptor projection for U-type's circuit assumptions. -/
theorem uTypeChipDescriptor_assumptions_iff (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    (uTypeChipDescriptor (p := p)).table.Assumptions
        (Environment.fromArray physical data) ↔
      UTypeChip.Assumptions
        ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data)) data := by
  rw [uTypeChipDescriptor_table]
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem uTypeEqualityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The two canonical bit-vector presentations of a U-type immediate agree: sign-extend then shift
by twelve, or append twelve zero bits then sign-extend. -/
theorem uTypeSignExtend_shiftLeft (imm : BitVec 20) :
    imm.signExtend 64 <<< 12 = BitVec.signExtend 64 (imm +++ 0#12) := by
  change imm.signExtend 64 <<< 12 = (imm.append 0#12).signExtend 64
  ext i hi
  by_cases low : i < 12
  · have i32 : i < 32 := by omega
    have appendElem := BitVec.getElem_append (x := imm) (y := 0#12) (i := i) (by omega)
    change (imm.append 0#12)[i] =
      if h : i < 12 then (0#12)[i] else imm[i - 12] at appendElem
    simp only [BitVec.getElem_shiftLeft, BitVec.getElem_signExtend]
    rw [dif_pos i32, appendElem]
    simp [low]
  · by_cases mid : i < 32
    · have delta : i - 12 < 20 := by omega
      have appendElem := BitVec.getElem_append (x := imm) (y := 0#12) (i := i) (by omega)
      change (imm.append 0#12)[i] =
        if h : i < 12 then (0#12)[i] else imm[i - 12] at appendElem
      simp only [BitVec.getElem_shiftLeft, BitVec.getElem_signExtend]
      rw [dif_pos delta, dif_pos mid, appendElem]
      simp [low]
    · have delta : ¬i - 12 < 20 := by omega
      have appendMsb := BitVec.msb_append (x := imm) (y := 0#12)
      change (imm.append 0#12).msb = if 20 = 0 then (0#12).msb else imm.msb at appendMsb
      simp only [BitVec.getElem_shiftLeft, BitVec.getElem_signExtend]
      rw [dif_neg delta, dif_neg mid, appendMsb]
      simp [low]

omit [Fact (2 ^ 25 < p)] in
/-- The physical U-type selector gate makes the LUI/AUIPC discriminator binary. -/
theorem UTypeChip.isAuipc_binary_of_constraints (env : Environment (ZMod p))
    (constraints :
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env) :
    ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_auipc = 0 ∨
      ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_auipc = 1 := by
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  let gate := input.is_auipc * (input.is_auipc - 1)
  have mainConstraints : ((UTypeChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have gateConstraint : Expression.eval env (gate - 0) = 0 := by
    apply mainConstraints.1
    simp only [input, offset, gate, UTypeChip.main, circuit_norm]
    right
    right
    right
    right
    right
    right
    right
    left
    simpa only [input, offset, gate, circuit_norm, FormalAssertion.toSubcircuit,
      Operations.toNested_toFlat, Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      uTypeEqualityConstraint_mem gate 0 _
  have binary : Expression.eval env input.is_auipc = 0 ∨
      Expression.eval env input.is_auipc = 1 := by
    apply bool_of_mul_pred
    simpa only [gate, eval_sub, Expression.eval, sub_zero] using gateConstraint
  have inputEq : Eval.eval env input =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset UTypeChip.Inputs 0 env
  rw [← inputEq]
  simpa only [input, circuit_norm] using binary

omit [Fact (2 ^ 25 < p)] in
theorem uTypeViewOf_state (env : Environment (ZMod p)) :
    (uTypeViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) UTypeChip.Inputs 0)).state := by
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  have outputEq : Eval.eval env ((UTypeChip.circuit (p := p)).output input offset) =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [uTypeViewOf, UTypeChip.rowView]
  rw [← outputEq]
  simp only [input, offset, UTypeChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem uTypeViewOf_adapter (env : Environment (ZMod p)) :
    (uTypeViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) UTypeChip.Inputs 0)).adapter.toAdapterView := by
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  have outputEq : Eval.eval env ((UTypeChip.circuit (p := p)).output input offset) =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [uTypeViewOf, UTypeChip.rowView]
  rw [← outputEq]
  simp only [input, offset, UTypeChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem uTypeViewOf_isReal (env : Environment (ZMod p)) :
    (uTypeViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) UTypeChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset UTypeChip.Inputs 0) =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset UTypeChip.Inputs 0 env
  simpa only [uTypeViewOf, UTypeChip.rowView] using
    congrArg (fun input : UTypeChip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] in
theorem uTypeViewOf_rdWrite (env : Environment (ZMod p)) :
    (uTypeViewOf env).rdWrite =
      Eval.eval env ((Vector.mapRange 4 fun i =>
        var { index := size UTypeChip.Inputs + 3 + i }) : Word (Expression (ZMod p))) := by
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  have outputEq : Eval.eval env ((UTypeChip.circuit (p := p)).output input offset) =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [uTypeViewOf, UTypeChip.rowView]
  rw [← outputEq]
  simp only [input, offset, UTypeChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- U-type's completed exposed Memory list evaluates to the canonical J-type pair. -/
theorem uTypeChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (jtypeMemoryInteractions (uTypeViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((UTypeChip.main (varFromOffset UTypeChip.Inputs 0)).operations
        (size UTypeChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [UTypeChip.interactionsWith_memory_eq]
  simp only [UTypeChip.exposedMemoryInteractions, jtypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeWriteMessage, uTypeViewOf_state, uTypeViewOf_adapter,
    uTypeViewOf_isReal, uTypeViewOf_rdWrite, Extracted.JTypeReader.toAdapterView, circuit_norm]

/-- Lift U-type's evaluated pair to the typed decoded-row boundary. -/
theorem uTypeChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = uTypeChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      jtypeMemoryInteractions (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    uTypeViewOf_decodeRow, uTypeChipDescriptor_table] using
    uTypeChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- U-type instantiates the canonical J-type Memory shape. -/
theorem uTypeChip_jtypeMemoryInteractionShape :
    JTypeMemoryInteractionShape (uTypeChipDescriptor (p := p)) where
  interactions := uTypeChip_typedMemoryInteractions_eq
  imm_b_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
    subst hchip'
    rfl

/-- The exact J-type reader input retained after U-type's seven witness cells. -/
def uTypeChipJTypeInput (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.JTypeReader.Inputs (ZMod p) :=
  let addValue : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 3 + i }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    input.is_auipc * 48 + (1 - input.is_auipc) * 49,
    addValue[0], addValue[1], addValue[2], addValue[3]⟩

omit [Fact (2 ^ 25 < p)] in
theorem UTypeChip.jtypeTimestampContract :
    CircuitJTypeTimestampContract (p := p) (UTypeChip.circuit (p := p))
      UTypeChip.rowView := by
  let input : Var UTypeChip.Inputs (ZMod p) := varFromOffset UTypeChip.Inputs 0
  let offset := size UTypeChip.Inputs
  let readerInput : Var Readers.JTypeReader.Inputs (ZMod p) :=
    uTypeChipJTypeInput input offset
  refine .intro (offset + 7) readerInput ?_ ?_
  · simp only [input, offset, readerInput, uTypeChipJTypeInput, UTypeChip.circuit,
      UTypeChip.main, Readers.JTypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, uTypeChipJTypeInput, UTypeChip.circuit,
        UTypeChip.rowView, Extracted.JTypeReader.toAdapterView, circuit_norm]

theorem uTypeChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = uTypeChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (UTypeChip.circuit (p := p)) UTypeChip.rowView
    UTypeChip.cpuStateTimeContract data physical guarantees real

theorem uTypeChip_activeTimestampBound (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = uTypeChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    JTypeTimestampBound (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  exact jtypeTimestampBound_of_contract (UTypeChip.circuit (p := p)) UTypeChip.rowView
    UTypeChip.jtypeTimestampContract data physical guarantees real

end UType

end SP1Clean.Soundness
