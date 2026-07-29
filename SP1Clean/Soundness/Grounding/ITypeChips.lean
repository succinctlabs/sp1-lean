import SP1Clean.Soundness.GroundingAdapter
import SP1Clean.Proofs.Chips.AddiChip.Contracts
import SP1Clean.Native.Readers.ITypeReaderImmutable

/-! # Canonical I-type grounding

The register-plus-immediate chips share a four-message Memory shape: destination prior pull,
source-B prior pull/read-back at `+3`, and destination write at `+4`.  This file states that shape
once, builds its timed wiring/aligned carrier, and instantiates it for Addi.
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

section ITypeShape

variable [Fact (2 ^ 25 < p)]

/-- The canonical typed Memory interactions of a register-plus-immediate row. -/
noncomputable def itypeMemoryInteractions (view : Trace.RowView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (rtypeWriteMessage view)]

/-- Descriptor-level I-type shape: the exact four interactions and the immediate-C marker. -/
structure ITypeMemoryInteractionShape (chip : SupportedChip p) : Prop where
  interactions : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        itypeMemoryInteractions (decoded.toChipRow data).view
  imm_c_eq_one : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip → (decoded.toChipRow data).view.adapter.imm_c = 1

omit [Fact (2 ^ 25 < p)] in
private theorem itypePull_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 msg).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem itypePush_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 1 msg).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_itypeFour (a b rb w : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [a, b] := by
  have filtered : List.filter (fun i => signedVal i.mult = -1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pushedIfValue memoryChannel 1 w] =
      [TypedInteraction.pulledIfValue memoryChannel 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b] := by
    simp only [List.filter_cons, List.filter_nil, itypePull_one_signed,
      itypePush_one_signed]
    norm_num
  rw [consumedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_itypeFour (a b rb w : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [rb, w] := by
  have filtered : List.filter (fun i => signedVal i.mult = 1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pushedIfValue memoryChannel 1 w] =
      [TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pushedIfValue memoryChannel 1 w] := by
    simp only [List.filter_cons, List.filter_nil, itypePull_one_signed,
      itypePush_one_signed]
    norm_num
  rw [producedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]

/-- An active I-type row consumes exactly its destination and source-B prior records. -/
theorem consumedMemoryMessages_eq_of_itypeShape {chip : SupportedChip p}
    (shape : ITypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
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
  unfold itypeMemoryInteractions
  rw [real]
  exact consumedMessages_itypeFour _ _ _ _

/-- An active I-type row produces its source read-back and destination write. -/
theorem producedMemoryMessages_eq_of_itypeShape {chip : SupportedChip p}
    (shape : ITypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold itypeMemoryInteractions
  rw [real]
  exact producedMessages_itypeFour _ _ _ _

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- A register index below 32 round-trips through its canonical five-bit encoding. -/
private theorem itypeRegisterIndexCast (x : ZMod p) (bound : x.val < 32) :
    ((BitVec.ofNat 5 x.val).toNat : ZMod p) = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.val < 2 ^ 5 by omega)]
  exact ZMod.natCast_zmod_val _

/-- Split a membership hypothesis against an exact two-element pull/push list.  The `rfl` patterns
are built with `mkIdent`: a quotation-local `rfl` is renamed by hygiene and then binds a *name*
instead of substituting. -/
local macro "twoElementCases " h:ident ", " listEq:term : tactic => do
  let rfl' := Lean.mkIdent `rfl
  `(tactic| (
    rw [$listEq:term] at $h:ident
    simp only [List.mem_cons, List.not_mem_nil, or_false] at $h:ident
    rcases $h:ident with $rfl':ident | $rfl':ident))

/-- Wiring for the canonical I-type register window. -/
theorem rowWiring_itype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.regWrite)
    (imm_c_eq : view.adapter.imm_c = 1)
    (opa_lt : view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 view.rdWrite)
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
    twoElementCases hmp, pulls_eq <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index immediate indexEq
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
    intro message hmessage
    twoElementCases hmessage, pushes_eq
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
    · refine Or.inr (Or.inl ?_)
      have hidx := itypeRegisterIndexCast _ opa_lt
      refine ⟨by rw [commit_eq]; rfl, write_isU64, ?_, rfl, ?_⟩
      · exact ⟨BitVec.ofNat 5 view.adapter.op_a.val,
          MemoryMsg.locOf_register _ _ hidx rfl rfl, hidx⟩
      · rw [timeNat_rtypeWriteMessage bounds, ← statePull_eq]
  push_clkBound := by
    intro message hmessage
    twoElementCases hmessage, pushes_eq
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program s s' heff _ cell v _ hcontent
    rw [locContent_ram_congr (heff.mem.1 (by rw [commit_eq]; rfl)) cell]
    exact hcontent

/-- I-type touches ordered by their `+3`, `+4` push times. -/
def itypeTouches (view : Trace.RowView (ZMod p)) (rf : Semantics.RowFacts p) : List (Touch p) :=
  [((rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
       StateMsg.timeNat rf.statePull + 3),
     rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   ((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
       StateMsg.timeNat rf.statePull),
     rtypeWriteMessage view)]

/-- Aligned carrier for the canonical I-type register window. -/
theorem rowAligned_itype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
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
      [rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3,
       rtypeWriteMessage view])
    (hslots : ∀ tc ∈ itypeTouches view rf,
      SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    AlignsWith (alignedOf rf (itypeTouches view rf)) rf ∧
      (∀ tc ∈ itypeTouches view rf,
        TouchOK (StateMsg.timeNat rf.statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((itypeTouches view rf).filter (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ itypeTouches view rf, SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ itypeTouches view rf,
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have hidxA := itypeRegisterIndexCast _ opa_lt
  have hidxB := itypeRegisterIndexCast _ opb_lt
  have hlocPriorA : MemoryMsg.locOf
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
    MemoryMsg.locOf_register _ _ hidxA rfl rfl
  have hlocPriorB : MemoryMsg.locOf
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_b[0].val) :=
    MemoryMsg.locOf_register _ _ hidxB rfl rfl
  have hlocReadB : MemoryMsg.locOf
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_b[0].val) :=
    MemoryMsg.locOf_register _ _ hidxB rfl rfl
  have hlocWrite : MemoryMsg.locOf (rtypeWriteMessage view) =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val) :=
    MemoryMsg.locOf_register _ _ hidxA rfl rfl
  have tb : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3) =
      StateMsg.timeNat rf.statePull + 3 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega)
  have tw : MemoryMsg.timeNat (rtypeWriteMessage view) =
      StateMsg.timeNat rf.statePull + 4 := by
    rw [statePull_eq]
    exact timeNat_rtypeWriteMessage bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine alignsWith_alignedOf rf (itypeTouches view rf) ?_ ?_ ?_ ?_ ?_
    · rw [pushes_eq]
      simp only [itypeTouches, List.map_cons, List.map_nil]
      exact List.Perm.refl _
    · rw [pulls_eq]
      simp only [itypeTouches, List.map_cons, List.map_nil]
      exact List.Perm.swap _ _ []
    · intro mp hmp
      twoElementCases hmp, pulls_eq
      · exact ⟨_, hlocPriorA⟩
      · exact ⟨_, hlocPriorB⟩
    · intro mp hmp
      twoElementCases hmp, pulls_eq <;> rfl
    · intro mp hmp
      twoElementCases hmp, pulls_eq
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_self, rfl,
          by dsimp only; omega, by dsimp only; omega⟩
  · intro tc htc
    simp only [itypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl
    · refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tb⟩⟩
      · dsimp only; rw [hlocReadB, hlocPriorB]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorB, readWindow_reg]; omega
    · refine ⟨?_, ?_, ?_, Or.inr ?_⟩
      · dsimp only; rw [hlocWrite, hlocPriorA]
      · dsimp only; omega
      · dsimp only; simp only [hlocPriorA, readWindow_reg]; omega
      · dsimp only; rw [hlocWrite, writeOffset_reg]; exact tw
  · have hpair : List.Pairwise
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        (itypeTouches view rf) := by
      simp only [itypeTouches]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl
        dsimp only
        rw [tb, tw]
        omega
      · intro x hx
        simp only [List.not_mem_nil] at hx
    intro loc
    exact (List.Pairwise.sublist List.filter_sublist hpair).isChain
  · intro tc htc
    simp only [itypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  · exact hslots

/-- The exact source-B pull supplies the register operand; immediate C is vacuous. -/
theorem registerOperandPullShape_of_itypeShape {chip : SupportedChip p}
    (shape : ITypeMemoryInteractionShape chip) :
    DecodedInstructionRow.RegisterOperandPullShape chip := by
  constructor
  · intro data physical program state
    dsimp only
    intro ready _constraints real index immediate indexEq
    let decoded : DecodedInstructionRow p := ⟨chip, physical⟩
    let view := (decoded.toChipRow data).view
    have consumed := consumedMemoryMessages_eq_of_itypeShape shape decoded data rfl real
    let message := rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory
    refine ⟨message, ?_, ?_, rfl⟩
    · change message ∈ decoded.consumedMemoryMessages data
      rw [consumed]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl
  · intro data physical program state
    dsimp only
    intro ready _constraints real index immediate indexEq
    let decoded : DecodedInstructionRow p := ⟨chip, physical⟩
    have immOne := shape.imm_c_eq_one decoded data rfl
    change (decoded.toChipRow data).view.adapter.imm_c = 0 at immediate
    rw [immOne] at immediate
    exact absurd immediate one_ne_zero

/-- The active source-B word inherits `isU64` from its exact pull and Memory guarantee. -/
theorem itypeOperandB_isU64_of_shape {chip : SupportedChip p}
    (shape : ITypeMemoryInteractionShape chip) (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data)) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_b_memory.prev_value := by
  let view := (decoded.toChipRow data).view
  let pullB := TypedInteraction.pulledIfValue memoryChannel view.is_real
    (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory)
  have pullBMem : pullB ∈ decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have pullBNegative : pullB.mult = -1 := by
    simp only [pullB, TypedInteraction.pulledIfValue_mult, view, real]
  have guarantee := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations memoryChannel (decoded.environment data) pullB pullBMem
    guarantees (by rfl) pullBNegative
  simpa only [Channels.memoryChannel, pullB, TypedInteraction.pulledIfValue_message,
    MemoryMsg.isU64, rtypePriorMessage] using guarantee.1

/-- The two active timestamp decompositions of an I-type row. -/
def ITypeTimestampBounds (view : Trace.RowView (ZMod p)) : Prop :=
  ActiveTimestampBounds view.adapter.op_a_memory.access_timestamp.prev_low
      view.adapter.op_a_memory.access_timestamp.diff_low_limb
      (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4) ∧
    ActiveTimestampBounds view.adapter.op_b_memory.access_timestamp.prev_low
      view.adapter.op_b_memory.access_timestamp.diff_low_limb
      (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 3)

/-- Scalar binding from a retained `ITypeReader` to the public row view. -/
structure ITypeTimestampBinding
    (readerReal aPrev aDiff bPrev bDiff targetA targetB : ZMod p)
    (view : Trace.RowView (ZMod p)) : Prop where
  real_eq : readerReal = view.is_real
  aPrev_eq : aPrev = view.adapter.op_a_memory.access_timestamp.prev_low
  aDiff_eq : aDiff = view.adapter.op_a_memory.access_timestamp.diff_low_limb
  bPrev_eq : bPrev = view.adapter.op_b_memory.access_timestamp.prev_low
  bDiff_eq : bDiff = view.adapter.op_b_memory.access_timestamp.diff_low_limb
  targetA_eq : targetA = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4
  targetB_eq : targetB = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 3

/-- Locate the retained I-type reader without unfolding a completed circuit in consumers. -/
inductive CircuitITypeTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (readerOffset : ℕ) (readerInput : Var Readers.ITypeReader.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.ITypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        ITypeTimestampBinding
          (Expression.eval env readerInput.is_real)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (readerInput.clk_low + 4))
          (Expression.eval env (readerInput.clk_low + 3))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env
              (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))) :
      CircuitITypeTimestampContract circuit view

/-- Finished Byte guarantees specialize a retained I-type reader to the semantic row. -/
theorem itypeTimestampBounds_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitITypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    ITypeTimestampBounds (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.ITypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput)
    readerMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env
      (circuit.output (varFromOffset Input 0) (size Input)) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have readerReal : Expression.eval env readerInput.is_real = 1 := bound.real_eq.trans real
  have timestampBounds := Readers.ITypeReader.timestampSpecs_of_byteGuarantees readerInput
    readerOffset env readerGuarantees readerReal
  unfold ITypeTimestampBounds
  rwa [bound.aPrev_eq, bound.aDiff_eq, bound.bPrev_eq, bound.bDiff_eq,
    bound.targetA_eq, bound.targetB_eq] at timestampBounds

/-! ### Immutable I-type timestamp retention -/

/-- The active timestamp decompositions of an immutable I-type row. -/
abbrev ImmutableITypeTimestampBounds (view : Trace.RowView (ZMod p)) : Prop :=
  ITypeTimestampBounds view

/-- Locate a retained immutable I-type reader without unfolding the completed parent circuit.
This is the immutable twin of `CircuitITypeTimestampContract`; it belongs at the shared I-type
boundary because both control-flow and memory chips compose this reader. -/
inductive CircuitImmutableITypeTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (readerOffset : ℕ)
      (readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit
            readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        ITypeTimestampBinding
          (Expression.eval env readerInput.is_real)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (readerInput.clk_low + 4))
          (Expression.eval env (readerInput.clk_low + 3))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env
              (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))) :
      CircuitImmutableITypeTimestampContract circuit view

/-- Finished Byte guarantees specialize a retained immutable I-type reader to the semantic row. -/
theorem immutableItypeTimestampBounds_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitImmutableITypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    ImmutableITypeTimestampBounds (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit readerOffset readerInput)
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
  have timestamps := Readers.ITypeReaderImmutable.timestampSpecs_of_byteGuarantees
    readerInput readerOffset env readerGuarantees readerReal
  unfold ImmutableITypeTimestampBounds ITypeTimestampBounds
  rwa [bound.aPrev_eq, bound.aDiff_eq, bound.bPrev_eq, bound.bDiff_eq,
    bound.targetA_eq, bound.targetB_eq] at timestamps

/-- Assemble a decoded I-type row's wiring from its exact interaction shape. -/
theorem rowWiring_itype_of_decoded (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq : (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite)
    (imm_c_eq : (decoded.toChipRow data).view.adapter.imm_c = 1)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 (decoded.toChipRow data).view.rdWrite)
    (consumed_eq : decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory])
    (produced_eq : decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeWriteMessage (decoded.toChipRow data).view]) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  refine rowWiring_itype bounds commit_eq imm_c_eq opa_lt write_isU64 rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed_eq]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
    exact produced_eq

/-- Construct the aligned carrier of an exact I-type row. -/
theorem rowAligned_itype_of_shape {chip : SupportedChip p}
    (shape : ITypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestampBounds : ITypeTimestampBounds (decoded.toChipRow data).view)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : (decoded.toChipRow data).view.adapter.op_b[0].val < 32) :
    AlignsWith (alignedOf (decoded.ordinaryRowFacts data)
        (itypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data)))
        (decoded.ordinaryRowFacts data) ∧
      (∀ tc ∈ itypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((itypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data)).filter
            (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ itypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ itypeTouches (decoded.toChipRow data).view
          (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have consumed_eq := consumedMemoryMessages_eq_of_itypeShape shape decoded data hchip real
  have produced_eq := producedMemoryMessages_eq_of_itypeShape shape decoded data hchip real
  obtain ⟨timestampA, timestampB⟩ := timestampBounds
  have hslots : ∀ tc ∈ itypeTouches (decoded.toChipRow data).view
      (decoded.ordinaryRowFacts data),
      SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
    intro tc htc hclk
    simp only [itypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampB rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampA rfl rfl rfl
  refine rowAligned_itype bounds real opa_lt opb_lt rfl ?_ ?_ hslots
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed_eq]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
    exact produced_eq

end ITypeShape

section Addi

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The Addi descriptor in the supported Core registry. -/
def addiChipDescriptor : SupportedChip p :=
  ⟨AddiChip.kind, AddiChip.circuit, rfl, [.ADDI], .nonX0⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def addiViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  AddiChip.rowView
    ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem addiViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((addiChipDescriptor (p := p)).decodeRow data physical).view =
      addiViewOf (Environment.fromArray physical data) := rfl

theorem addiChipDescriptor_table :
    (addiChipDescriptor (p := p)).table =
      (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem addiViewOf_state (env : Environment (ZMod p)) :
    (addiViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) AddiChip.Inputs 0)).state := by
  have inputEq : Eval.eval env (varFromOffset AddiChip.Inputs 0) =
      (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddiChip.Inputs 0 env
  simp only [addiViewOf, AddiChip.rowView]
  exact (AddiChip.inputOutputState env).symm.trans
    (congrArg (fun input : AddiChip.Inputs (ZMod p) => input.state) inputEq.symm)

omit [Fact (2 ^ 25 < p)] in
theorem addiViewOf_adapter (env : Environment (ZMod p)) :
    (addiViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) AddiChip.Inputs 0)).adapter.toAdapterView := by
  have inputEq : Eval.eval env (varFromOffset AddiChip.Inputs 0) =
      (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddiChip.Inputs 0 env
  simp only [addiViewOf, AddiChip.rowView]
  exact congrArg Extracted.ITypeReader.toAdapterView
    ((AddiChip.inputOutputAdapter env).symm.trans
      (congrArg (fun input : AddiChip.Inputs (ZMod p) => input.adapter) inputEq.symm))

omit [Fact (2 ^ 25 < p)] in
/-- Scalar form of `addiViewOf_adapter` used at the routing boundary.  Keeping this projection
opaque prevents Lean from normalizing the completed Addi row merely to compare the routing flag. -/
theorem addiViewOf_opA0 (env : Environment (ZMod p)) :
    (addiViewOf env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) AddiChip.Inputs 0).adapter.op_a_0 := by
  rw [addiViewOf_adapter]
  change (Eval.eval env
    (varFromOffset (F := ZMod p) AddiChip.Inputs 0)).adapter.op_a_0 = _
  rw [AddiChip.eval_inputAdapter]
  exact Readers.ITypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
theorem addiViewOf_isReal (env : Environment (ZMod p)) :
    (addiViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) AddiChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset AddiChip.Inputs 0) =
      (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddiChip.Inputs 0 env
  simpa only [addiViewOf, AddiChip.rowView] using
    congrArg (fun input : AddiChip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] in
theorem addiViewOf_rdWrite (env : Environment (ZMod p)) :
    (addiViewOf env).rdWrite =
      Eval.eval env ((Vector.mapRange 4 fun i =>
        var { index := size AddiChip.Inputs + i }) : Word (Expression (ZMod p))) := by
  let input : Var AddiChip.Inputs (ZMod p) := varFromOffset AddiChip.Inputs 0
  let offset := size AddiChip.Inputs
  have outputEq : Eval.eval env ((AddiChip.circuit (p := p)).output input offset) =
      (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  simp only [addiViewOf, AddiChip.rowView]
  rw [← outputEq]
  change (Eval.eval env
    ((AddiChip.elaborated (p := p)).output input offset)).add_operation.value = _
  rw [AddiChip.directOutput_eq, AddiChip.eval_columns]
  simp only [offset, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- Addi's completed exposed Memory list evaluates to the canonical I-type four-pack. -/
theorem addiChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (itypeMemoryInteractions (addiViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((AddiChip.main (varFromOffset AddiChip.Inputs 0)).operations
        (size AddiChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [AddiChip.interactionsWith_memory_eq]
  simp only [AddiChip.exposedMemoryInteractions, itypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    addiViewOf_state, addiViewOf_adapter, addiViewOf_isReal, addiViewOf_rdWrite,
    Extracted.ITypeReader.toAdapterView, circuit_norm]

/-- Lift Addi's evaluated four-pack to the typed decoded-row boundary. -/
theorem addiChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addiChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      itypeMemoryInteractions (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addiChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    addiViewOf_decodeRow, addiChipDescriptor_table] using
    addiChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Addi instantiates the canonical I-type Memory shape. -/
theorem addiChip_itypeMemoryInteractionShape :
    ITypeMemoryInteractionShape (addiChipDescriptor (p := p)) where
  interactions := addiChip_typedMemoryInteractions_eq
  imm_c_eq_one := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addiChipDescriptor (p := p) := hchip
    subst hchip'
    rfl

/-- The exact I-type reader input retained after Addi's four result-witness cells. -/
def addiChipITypeInput (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ITypeReader.Inputs (ZMod p) :=
  let value : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 1,
    value[0], value[1], value[2], value[3]⟩

omit [Fact (2 ^ 25 < p)] in
/-- Addi's retained reader through the scalar I-type timestamp contract. -/
theorem AddiChip.itypeTimestampContract :
    CircuitITypeTimestampContract (p := p) (AddiChip.circuit (p := p))
      AddiChip.rowView := by
  let input : Var AddiChip.Inputs (ZMod p) := varFromOffset AddiChip.Inputs 0
  let offset := size AddiChip.Inputs
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    addiChipITypeInput input offset
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, addiChipITypeInput, AddiChip.circuit,
      AddiChip.main, Readers.ITypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, addiChipITypeInput, AddiChip.circuit,
        AddiChip.rowView, Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem addiChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addiChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addiChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (AddiChip.circuit (p := p)) AddiChip.rowView
    AddiChip.cpuStateTimeContract data physical guarantees real

theorem addiChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addiChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ITypeTimestampBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addiChipDescriptor (p := p) := hchip
  subst hchip'
  exact itypeTimestampBounds_of_contract AddiChip.circuit AddiChip.rowView
    AddiChip.itypeTimestampContract data physical guarantees real

/-- The committed Addi decode makes its immediate a canonical 64-bit word. -/
theorem addiChip_immediate_isU64 {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = addiChipDescriptor (p := p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_c := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addiChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical data
  have decode' : decodedInROM program (programAccess (addiViewOf env)).toRow := by
    simpa only [DecodedInstructionRow.toChipRow, addiViewOf_decodeRow, env] using decode
  have opcodeEq :
      (programAccess (addiViewOf env)).toRow.opcode =
        ((iopToOpcode iop.ADDI).toNat : ZMod p) := by
    simp only [programAccess, ProgramAccess.toRow, addiViewOf, AddiChip.rowView,
      iopToOpcode, Opcode.toNat]
    norm_num
  have immediateEq :
      (programAccess (addiViewOf env)).toRow.imm_c = 1 := by
    change (addiViewOf env).adapter.imm_c = 1
    rw [addiViewOf_adapter]
    rfl
  obtain ⟨word, imm, rs1, rd, fetch, decodedAll, opA, opB, opC⟩ :=
    decodesIType iop.ADDI decode' opcodeEq immediateEq
  have immediateU64 : Word.isU64 (programAccess (addiViewOf env)).toRow.op_c := by
    rw [opC]
    exact isU64_bitVecToWord _
  change Word.isU64
    ((addiChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_c
  rw [addiViewOf_decodeRow]
  simpa only [programAccess, ProgramAccess.toRow] using immediateU64

end Addi

end SP1Clean.Soundness
