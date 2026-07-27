import SP1Clean.Soundness.Grounding.ITypeChips
import SP1Clean.Proofs.Chips.JalrChip.Bridge
import SP1Clean.Proofs.Chips.BranchChip.Bridge

/-! # Control-flow chip grounding

JALR uses the ordinary I-type four-message layout, but its destination effect is conditional:
`rd = x0` still emits the factored `RegisterWrite` push, whose value is forced to zero by the
retained reader.  Branch uses the immutable I-type layout and treats both register slots as
sources.  This module keeps those two upstream layouts explicit instead of weakening them into a
single permissive interaction schema.
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

section ConditionalIType

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The retained mutable I-type reader forces the factored destination value to zero when `rd` is
`x0`.  This is the value half of JALR's physical no-write push. -/
theorem itypeWrite_zero_of_spec (input : Readers.ITypeReader.Inputs (ZMod p))
    (spec : Readers.ITypeReader.Spec input) (flag : input.cols.op_a_0 = 1) :
    Word.toBitVec64 (#v[input.wv0, input.wv1, input.wv2, input.wv3] : Word (ZMod p)) = 0 := by
  obtain ⟨⟨z0, z1, z2, z3⟩, -⟩ := spec
  rw [flag, one_mul] at z0 z1 z2 z3
  simp [Word.toBitVec64, Word.toNat_def, z0, z1, z2, z3]

/-- Wiring for an I-type row whose destination may be `x0`.  The source-B read-back remains at
`+3`; the destination-slot push at `+4` is either the committed write or the canonical x0 value. -/
theorem rowWiring_itypeDestination {view : Trace.RowView (ZMod p)}
    {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.destination view.adapter.op_a_0)
    (op_a_0_binary : view.adapter.op_a_0 = 0 ∨ view.adapter.op_a_0 = 1)
    (imm_c_eq : view.adapter.imm_c = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 view.rdWrite)
    (zero_index : view.adapter.op_a_0 = 1 → view.adapter.op_a = 0)
    (zero_value : view.adapter.op_a_0 = 1 → Word.toBitVec64 view.rdWrite = 0)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3,
       rtypeWriteMessage view]) :
    RowWiring view rf where
  statePull_eq := statePull_eq
  statePush_eq := statePush_eq
  time8 := by
    rw [statePull_eq, statePush_eq]
    exact timeNat_statePushOfView_eight bounds
  readTime := by
    intro mp hmp
    rw [pulls_eq] at hmp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
    rcases hmp with rfl | rfl <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opC_pull := by
    intro index immediate indexEq
    rw [imm_c_eq] at immediate
    exact absurd immediate one_ne_zero
  write_push := by
    intro _ index indexEq
    refine ⟨rtypeWriteMessage view, ?_, ?_, rfl⟩
    · rw [pushes_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  push_classified := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        unfold Trace.CommitEffect.destination
        split <;> rfl
    · rcases op_a_0_binary with opA0 | opA0
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
        have indexEq : (((0#5 : BitVec 5).toNat : ℕ) : ZMod p) =
            view.adapter.op_a := by
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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program s s' heff _ cell v _ hcontent
    rw [locContent_ram_congr (heff.mem.1 (by
      rw [commit_eq]
      unfold Trace.CommitEffect.destination
      split <;> rfl)) cell]
    exact hcontent

/-- Construct the conditional-destination wiring from the ordinary exact I-type shape. -/
theorem rowWiring_itypeDestination_of_shape {chip : SupportedChip p}
    (shape : ITypeMemoryInteractionShape chip)
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
  have consumed := consumedMemoryMessages_eq_of_itypeShape shape decoded data hchip real
  have produced := producedMemoryMessages_eq_of_itypeShape shape decoded data hchip real
  refine rowWiring_itypeDestination bounds commit_eq op_a_0_binary
    (shape.imm_c_eq_one decoded data hchip) opa_lt write_isU64 zero_index zero_value
    rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]

end ConditionalIType

section Jalr

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- JALR's descriptor in the supported Core registry. -/
def jalrChipDescriptor : SupportedChip p :=
  ⟨JalrChip.kind, JalrChip.circuit, rfl, [.JALR], .any⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def jalrViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  JalrChip.rowView
    ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem jalrViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((jalrChipDescriptor (p := p)).decodeRow data physical).view =
      jalrViewOf (Environment.fromArray physical data) := rfl

theorem jalrChipDescriptor_table :
    (jalrChipDescriptor (p := p)).table =
      (⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

/-- Folded descriptor projection for JALR's circuit assumptions. -/
theorem jalrChipDescriptor_assumptions_iff (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    (jalrChipDescriptor (p := p)).table.Assumptions
        (Environment.fromArray physical data) ↔
      JalrChip.Assumptions
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data)) data := by
  rw [jalrChipDescriptor_table]
  rfl

omit [Fact (2 ^ 25 < p)] in
theorem jalrViewOf_state (env : Environment (ZMod p)) :
    (jalrViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) JalrChip.Inputs 0)).state := by
  let input : Var JalrChip.Inputs (ZMod p) := varFromOffset JalrChip.Inputs 0
  let offset := size JalrChip.Inputs
  have outputEq : Eval.eval env ((JalrChip.circuit (p := p)).output input offset) =
      (⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [jalrViewOf, JalrChip.rowView]
  rw [← outputEq]
  simp only [input, offset, JalrChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem jalrViewOf_adapter (env : Environment (ZMod p)) :
    (jalrViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) JalrChip.Inputs 0)).adapter.toAdapterView := by
  let input : Var JalrChip.Inputs (ZMod p) := varFromOffset JalrChip.Inputs 0
  let offset := size JalrChip.Inputs
  have outputEq : Eval.eval env ((JalrChip.circuit (p := p)).output input offset) =
      (⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [jalrViewOf, JalrChip.rowView]
  rw [← outputEq]
  simp only [input, offset, JalrChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem jalrViewOf_isReal (env : Environment (ZMod p)) :
    (jalrViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) JalrChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset JalrChip.Inputs 0) =
      (⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset JalrChip.Inputs 0 env
  simpa only [jalrViewOf, JalrChip.rowView] using
    congrArg (fun input : JalrChip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] in
theorem jalrViewOf_rdWrite (env : Environment (ZMod p)) :
    (jalrViewOf env).rdWrite =
      Eval.eval env ((Vector.mapRange 4 fun i =>
        var { index := size JalrChip.Inputs + 4 + i }) : Word (Expression (ZMod p))) := by
  let input : Var JalrChip.Inputs (ZMod p) := varFromOffset JalrChip.Inputs 0
  let offset := size JalrChip.Inputs
  have outputEq : Eval.eval env ((JalrChip.circuit (p := p)).output input offset) =
      (⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [jalrViewOf, JalrChip.rowView]
  rw [← outputEq]
  simp only [input, offset, JalrChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- JALR's exposed Memory list evaluates to the canonical I-type four-pack. -/
theorem jalrChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (itypeMemoryInteractions (jalrViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((JalrChip.main (varFromOffset JalrChip.Inputs 0)).operations
        (size JalrChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [JalrChip.interactionsWith_memory_eq]
  simp only [JalrChip.exposedMemoryInteractions, itypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    jalrViewOf_state, jalrViewOf_adapter, jalrViewOf_isReal, jalrViewOf_rdWrite,
    Extracted.ITypeReader.toAdapterView, circuit_norm]

/-- Lift JALR's evaluated four-pack to the typed decoded-row boundary. -/
theorem jalrChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = jalrChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      itypeMemoryInteractions (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    jalrViewOf_decodeRow, jalrChipDescriptor_table] using
    jalrChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- JALR instantiates the canonical I-type Memory shape. -/
theorem jalrChip_itypeMemoryInteractionShape :
    ITypeMemoryInteractionShape (jalrChipDescriptor (p := p)) where
  interactions := jalrChip_typedMemoryInteractions_eq
  imm_c_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = jalrChipDescriptor (p := p) := hchip
    subst hchip'
    rfl

/-- The retained JALR I-type reader after the two add words and LSB witness. -/
def jalrChipITypeInput (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ITypeReader.Inputs (ZMod p) :=
  let opAValue : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 4 + i }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 47,
    opAValue[0], opAValue[1], opAValue[2], opAValue[3]⟩

omit [Fact (2 ^ 25 < p)] in
theorem JalrChip.itypeTimestampContract :
    CircuitITypeTimestampContract (p := p) (JalrChip.circuit (p := p))
      JalrChip.rowView := by
  let input : Var JalrChip.Inputs (ZMod p) := varFromOffset JalrChip.Inputs 0
  let offset := size JalrChip.Inputs
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    jalrChipITypeInput input offset
  refine .intro (offset + 9) readerInput ?_ ?_
  · simp only [input, offset, readerInput, jalrChipITypeInput, JalrChip.circuit,
      JalrChip.main, Readers.ITypeReader.circuit, circuit_norm]
    right
    right
    right
    right
    right
    right
    left
    rfl
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, jalrChipITypeInput, JalrChip.circuit,
        JalrChip.rowView, Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem jalrChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = jalrChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (JalrChip.circuit (p := p)) JalrChip.rowView
    JalrChip.cpuStateTimeContract data physical guarantees real

theorem jalrChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = jalrChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ITypeTimestampBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  exact itypeTimestampBounds_of_contract JalrChip.circuit JalrChip.rowView
    JalrChip.itypeTimestampContract data physical guarantees real

end Jalr

section ImmutableIType

variable [Fact (2 ^ 25 < p)]

/-- The exact four Memory interactions of an immutable I-type row: source A is read back at `+4`
and source B at `+3`. -/
noncomputable def immutableItypeMemoryInteractions (view : Trace.RowView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3)]

/-- Descriptor-level immutable I-type shape. -/
structure ImmutableITypeMemoryInteractionShape (chip : SupportedChip p) : Prop where
  interactions : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        immutableItypeMemoryInteractions (decoded.toChipRow data).view
  imm_b_eq_zero : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip → (decoded.toChipRow data).view.adapter.imm_b = 0
  imm_c_eq_one : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip → (decoded.toChipRow data).view.adapter.imm_c = 1

omit [Fact (2 ^ 25 < p)] in
private theorem immutableItypePull_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 msg).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem immutableItypePush_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 1 msg).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_immutableItypeFour (a ra b rb : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb] = [a, b] := by
  have filtered : List.filter (fun i => signedVal i.mult = -1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb] =
      [TypedInteraction.pulledIfValue memoryChannel 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b] := by
    simp only [List.filter_cons, List.filter_nil, immutableItypePull_one_signed,
      immutableItypePush_one_signed]
    norm_num
  rw [consumedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_immutableItypeFour (a ra b rb : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb] = [ra, rb] := by
  have filtered : List.filter (fun i => signedVal i.mult = 1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb] =
      [TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pushedIfValue memoryChannel 1 rb] := by
    simp only [List.filter_cons, List.filter_nil, immutableItypePull_one_signed,
      immutableItypePush_one_signed]
    norm_num
  rw [producedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]

/-- An active immutable I-type row consumes its two source-register priors. -/
theorem consumedMemoryMessages_eq_of_immutableItypeShape {chip : SupportedChip p}
    (shape : ImmutableITypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableItypeMemoryInteractions
  rw [real]
  exact consumedMessages_immutableItypeFour _ _ _ _

/-- An active immutable I-type row produces the two source read-backs. -/
theorem producedMemoryMessages_eq_of_immutableItypeShape {chip : SupportedChip p}
    (shape : ImmutableITypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory 4,
       rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory 3] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableItypeMemoryInteractions
  rw [real]
  exact producedMessages_immutableItypeFour _ _ _ _

/-- Both source words of an active immutable I-type row inherit `isU64` from their exact pulls. -/
theorem immutableItypeOperandWords_isU64_of_shape {chip : SupportedChip p}
    (shape : ImmutableITypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data)) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_a_memory.prev_value ∧
      Word.isU64 (decoded.toChipRow data).view.adapter.op_b_memory.prev_value := by
  let view := (decoded.toChipRow data).view
  let pullA := TypedInteraction.pulledIfValue memoryChannel view.is_real
    (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory)
  let pullB := TypedInteraction.pulledIfValue memoryChannel view.is_real
    (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory)
  have pullAMem : pullA ∈ decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_self
  have pullBMem : pullB ∈ decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self))
  have pullANegative : pullA.mult = -1 := by
    simp only [pullA, TypedInteraction.pulledIfValue_mult, view, real]
  have pullBNegative : pullB.mult = -1 := by
    simp only [pullB, TypedInteraction.pulledIfValue_mult, view, real]
  have guaranteeA := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations memoryChannel (decoded.environment data) pullA pullAMem
    guarantees (by rfl) pullANegative
  have guaranteeB := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations memoryChannel (decoded.environment data) pullB pullBMem
    guarantees (by rfl) pullBNegative
  constructor
  · simpa only [Channels.memoryChannel, pullA, TypedInteraction.pulledIfValue_message,
      MemoryMsg.isU64, rtypePriorMessage] using guaranteeA.1
  · simpa only [Channels.memoryChannel, pullB, TypedInteraction.pulledIfValue_message,
      MemoryMsg.isU64, rtypePriorMessage] using guaranteeB.1

/-- Wiring for a no-write immutable I-type register window. -/
theorem rowWiring_immutableItype {view : Trace.RowView (ZMod p)}
    {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.noWrite)
    (imm_c_eq : view.adapter.imm_c = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4,
       rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3]) :
    RowWiring view rf where
  statePull_eq := statePull_eq
  statePush_eq := statePush_eq
  time8 := by
    rw [statePull_eq, statePush_eq]
    exact timeNat_statePushOfView_eight bounds
  readTime := by
    intro mp hmp
    rw [pulls_eq] at hmp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
    rcases hmp with rfl | rfl <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opC_pull := by
    intro index immediate indexEq
    rw [imm_c_eq] at immediate
    exact absurd immediate one_ne_zero
  write_push := by
    intro writes
    rw [commit_eq] at writes
    exact Bool.noConfusion writes
  push_classified := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl
    · refine Or.inr (Or.inr (Or.inl ?_))
      refine ⟨by rw [commit_eq]; rfl,
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull), ?_, ?_, rfl, rfl, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_self
      · have indexEq : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
            view.adapter.op_a := by
          rw [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
          exact ZMod.natCast_zmod_val _
        exact ⟨BitVec.ofNat 5 view.adapter.op_a.val,
          MemoryMsg.locOf_register _ _ indexEq rfl rfl⟩
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega),
          ← statePull_eq]
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
  push_clkBound := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program s s' heff _ cell v _ hcontent
    rw [locContent_ram_congr (heff.mem.1 (by rw [commit_eq]; rfl)) cell]
    exact hcontent

/-- Immutable I-type touches ordered by their `+3`, `+4` push times. -/
def immutableItypeTouches (view : Trace.RowView (ZMod p))
    (rf : Semantics.RowFacts p) : List (Touch p) :=
  [((rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
       StateMsg.timeNat rf.statePull + 3),
     rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   ((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
       StateMsg.timeNat rf.statePull),
     rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4)]

/-- Aligned carrier for the immutable I-type register window. -/
theorem rowAligned_immutableItype {view : Trace.RowView (ZMod p)}
    {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (_real : view.is_real = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (opb_lt : view.adapter.op_b[0].val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4,
       rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3])
    (hslots : ∀ tc ∈ immutableItypeTouches view rf,
      SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    AlignsWith (alignedOf rf (immutableItypeTouches view rf)) rf ∧
      (∀ tc ∈ immutableItypeTouches view rf,
        TouchOK (StateMsg.timeNat rf.statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((immutableItypeTouches view rf).filter
          (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ immutableItypeTouches view rf,
        SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ immutableItypeTouches view rf,
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have hidxA : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
      view.adapter.op_a := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  have hidxB : ((BitVec.ofNat 5 view.adapter.op_b[0].val).toNat : ZMod p) =
      view.adapter.op_b[0] := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show view.adapter.op_b[0].val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  have hlocPriorA : MemoryMsg.locOf
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
    MemoryMsg.locOf_register _ _ hidxA rfl rfl
  have hlocPriorB : MemoryMsg.locOf
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_b[0].val) :=
    MemoryMsg.locOf_register _ _ hidxB rfl rfl
  have hlocReadA : MemoryMsg.locOf
      (rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
    MemoryMsg.locOf_register _ _ hidxA rfl rfl
  have hlocReadB : MemoryMsg.locOf
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_b[0].val) :=
    MemoryMsg.locOf_register _ _ hidxB rfl rfl
  have tb : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3) =
      StateMsg.timeNat rf.statePull + 3 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega)
  have ta : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4) =
      StateMsg.timeNat rf.statePull + 4 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine alignsWith_alignedOf rf (immutableItypeTouches view rf) ?_ ?_ ?_ ?_ ?_
    · rw [pushes_eq]
      simp only [immutableItypeTouches, List.map_cons, List.map_nil]
      exact List.Perm.swap _ _ []
    · rw [pulls_eq]
      simp only [immutableItypeTouches, List.map_cons, List.map_nil]
      exact List.Perm.swap _ _ []
    · intro mp hmp
      rw [pulls_eq] at hmp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
      rcases hmp with rfl | rfl
      · exact ⟨_, hlocPriorA⟩
      · exact ⟨_, hlocPriorB⟩
    · intro mp hmp
      rw [pulls_eq] at hmp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
      rcases hmp with rfl | rfl <;> rfl
    · intro mp hmp
      rw [pulls_eq] at hmp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
      rcases hmp with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
  · intro tc htc
    simp only [immutableItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl
    · refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tb⟩⟩
      · dsimp only; rw [hlocReadB, hlocPriorB]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorB, readWindow_reg]; omega
    · refine ⟨?_, ?_, ?_, Or.inr ?_⟩
      · dsimp only; rw [hlocReadA, hlocPriorA]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorA, readWindow_reg]; omega
      · dsimp only; rw [hlocReadA, writeOffset_reg]; exact ta
  · have hpair : List.Pairwise
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        (immutableItypeTouches view rf) := by
      simp only [immutableItypeTouches]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl
        dsimp only
        rw [tb, ta]
        omega
      · intro x hx
        simp only [List.not_mem_nil] at hx
    intro loc
    exact (List.Pairwise.sublist List.filter_sublist hpair).isChain
  · intro tc htc
    simp only [immutableItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  · exact hslots

/-- Construct immutable I-type wiring from its exact interaction shape. -/
theorem rowWiring_immutableItype_of_shape {chip : SupportedChip p}
    (shape : ImmutableITypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq : (decoded.toChipRow data).view.commit = Trace.CommitEffect.noWrite)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  have consumed :=
    consumedMemoryMessages_eq_of_immutableItypeShape shape decoded data hchip real
  have produced :=
    producedMemoryMessages_eq_of_immutableItypeShape shape decoded data hchip real
  refine rowWiring_immutableItype bounds commit_eq
    (shape.imm_c_eq_one decoded data hchip) opa_lt rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]

/-- Construct the aligned carrier of an exact immutable I-type row. -/
theorem rowAligned_immutableItype_of_shape {chip : SupportedChip p}
    (shape : ImmutableITypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestampBounds : ImmutableITypeTimestampBounds (decoded.toChipRow data).view)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : (decoded.toChipRow data).view.adapter.op_b[0].val < 32) :
    AlignsWith (alignedOf (decoded.ordinaryRowFacts data)
        (immutableItypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data)))
        (decoded.ordinaryRowFacts data) ∧
      (∀ tc ∈ immutableItypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((immutableItypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data)).filter
            (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ immutableItypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ immutableItypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have consumed :=
    consumedMemoryMessages_eq_of_immutableItypeShape shape decoded data hchip real
  have produced :=
    producedMemoryMessages_eq_of_immutableItypeShape shape decoded data hchip real
  obtain ⟨timestampA, timestampB⟩ := timestampBounds
  have hslots : ∀ tc ∈ immutableItypeTouches (decoded.toChipRow data).view
      (decoded.ordinaryRowFacts data),
      SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
    intro tc htc hclk
    simp only [immutableItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampB rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampA rfl rfl rfl
  refine rowAligned_immutableItype bounds real opa_lt opb_lt rfl ?_ ?_ hslots
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]

end ImmutableIType

section Branch

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- Branch's descriptor in the supported Core registry. -/
def branchChipDescriptor : SupportedChip p :=
  ⟨BranchChip.kind, BranchChip.circuit, rfl,
    [.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU], .any⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def branchViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  BranchChip.rowView
    ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem branchViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((branchChipDescriptor (p := p)).decodeRow data physical).view =
      branchViewOf (Environment.fromArray physical data) := rfl

theorem branchChipDescriptor_table :
    (branchChipDescriptor (p := p)).table =
      (⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

/-- Folded descriptor projection for Branch's circuit assumptions. -/
theorem branchChipDescriptor_assumptions_iff (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    (branchChipDescriptor (p := p)).table.Assumptions
        (Environment.fromArray physical data) ↔
      BranchChip.Assumptions
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data)) data := by
  rw [branchChipDescriptor_table]
  rfl

omit [Fact (2 ^ 25 < p)] in
theorem branchViewOf_state (env : Environment (ZMod p)) :
    (branchViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) BranchChip.Inputs 0)).state := by
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  let offset := size BranchChip.Inputs
  have outputEq : Eval.eval env ((BranchChip.circuit (p := p)).output input offset) =
      (⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [branchViewOf, BranchChip.rowView]
  rw [← outputEq]
  simp only [input, offset, BranchChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem branchViewOf_adapter (env : Environment (ZMod p)) :
    (branchViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) BranchChip.Inputs 0)).adapter.toAdapterView := by
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  let offset := size BranchChip.Inputs
  have outputEq : Eval.eval env ((BranchChip.circuit (p := p)).output input offset) =
      (⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, input, offset, circuit_norm]
  simp only [branchViewOf, BranchChip.rowView]
  rw [← outputEq]
  simp only [input, offset, BranchChip.circuit, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem branchViewOf_isReal (env : Environment (ZMod p)) :
    (branchViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) BranchChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset BranchChip.Inputs 0) =
      (⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset BranchChip.Inputs 0 env
  simpa only [branchViewOf, BranchChip.rowView] using
    congrArg (fun input : BranchChip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] in
/-- Branch's exposed Memory list evaluates to the immutable I-type four-pack. -/
theorem branchChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableItypeMemoryInteractions (branchViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((BranchChip.main (varFromOffset BranchChip.Inputs 0)).operations
        (size BranchChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [BranchChip.interactionsWith_memory_eq]
  simp only [BranchChip.exposedMemoryInteractions, immutableItypeMemoryInteractions,
    List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw, Channel.eval_pulledIf, Channel.eval_pushedIf,
    eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, branchViewOf_state,
    branchViewOf_adapter, branchViewOf_isReal, Extracted.ITypeReader.toAdapterView,
    circuit_norm]

/-- Lift Branch's evaluated four-pack to the typed decoded-row boundary. -/
theorem branchChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = branchChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableItypeMemoryInteractions (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = branchChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    branchViewOf_decodeRow, branchChipDescriptor_table] using
    branchChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Branch instantiates the exact immutable I-type Memory shape. -/
theorem branchChip_immutableItypeMemoryInteractionShape :
    ImmutableITypeMemoryInteractionShape (branchChipDescriptor (p := p)) where
  interactions := branchChip_typedMemoryInteractions_eq
  imm_b_eq_zero := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = branchChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = branchChipDescriptor (p := p) := hchip
    subst hchip'
    rfl

/-- The retained immutable I-type reader after Branch's 28 witness cells. -/
def branchChipITypeInput (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
  let opcode :=
    var { index := offset } * 40 + var { index := offset + 1 } * 41 +
      var { index := offset + 2 } * 42 + var { index := offset + 3 } * 43 +
      var { index := offset + 4 } * 44 + var { index := offset + 5 } * 45
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, opcode⟩

omit [Fact (2 ^ 25 < p)] in
theorem BranchChip.immutableItypeTimestampContract :
    CircuitImmutableITypeTimestampContract (p := p) (BranchChip.circuit (p := p))
      BranchChip.rowView := by
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  let offset := size BranchChip.Inputs
  let readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
    branchChipITypeInput input offset
  refine .intro (offset + 20) readerInput ?_ ?_
  · simp only [input, offset, readerInput, branchChipITypeInput, BranchChip.circuit,
      BranchChip.main, Readers.ITypeReaderImmutable.circuit, circuit_norm]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rfl
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, branchChipITypeInput, BranchChip.circuit,
        BranchChip.rowView, BranchChip.branchOpcode, Extracted.ITypeReader.toAdapterView,
        circuit_norm]

theorem branchChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = branchChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = branchChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (BranchChip.circuit (p := p)) BranchChip.rowView
    BranchChip.cpuStateTimeContract data physical guarantees real

theorem branchChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = branchChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ImmutableITypeTimestampBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = branchChipDescriptor (p := p) := hchip
  subst hchip'
  exact immutableItypeTimestampBounds_of_contract BranchChip.circuit BranchChip.rowView
    BranchChip.immutableItypeTimestampContract data physical guarantees real

end Branch

end SP1Clean.Soundness
