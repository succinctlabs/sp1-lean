import SP1Clean.Soundness.CoreRowBalance
import SP1Clean.Soundness.SystemTouches
import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.FetchDiscriminant

/-! # Shared local Memory-touch alignment

Component contracts and authenticated fetches give paired touches for every execution-row kind.
Alignment preserves complete Memory multisets, State edges, and fetches. Received clock bounds
remain explicit until the enclosing assembly derives them from balance. No host execution or
initial-state semantics is assumed by these component-level alignment lemmas.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance coreTouchesField24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance coreTouchesField17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Local touch alignment, with the prior-clock conditions explicitly retained for grounding. -/
structure AlignedFacts (aligned original : RowFacts p) : Prop where
  statePull : aligned.statePull = original.statePull
  statePush : aligned.statePush = original.statePush
  fetch : aligned.fetch = original.fetch
  memory : RowMemoryPermutation aligned original
  touches : List.Forall₂ (TouchOK (StateMsg.timeNat aligned.statePull)) aligned.memPulls aligned.memPushes
  chain : ∀ loc, List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
    (rowTouchesAt aligned loc)
  pushBound : ∀ message ∈ aligned.memPushes, MemoryMsg.ClkBound message
  slot : ∀ touch ∈ aligned.memPulls.zip aligned.memPushes,
    MemoryMsg.ClkBound touch.1.1 → touch.1.1.clk_high.val < 2 ^ 24 →
      MemoryMsg.timeNat touch.1.1 < MemoryMsg.timeNat touch.2

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- Once Memory balance supplies the prior high-clock bounds, the alignment is the timed
engine's complete local core. The remaining low-clock premise is the engine's own received fact. -/
theorem AlignedFacts.rowOKCore {aligned original : RowFacts p} (facts : AlignedFacts aligned original)
    (initialClock : ℕ)
    (gap : StateMsg.timeNat original.statePull + 8 ≤ StateMsg.timeNat original.statePush)
    (align : StateMsg.timeNat original.statePull % 8 = initialClock % 8)
    (priorHigh : ∀ touch ∈ aligned.memPulls.zip aligned.memPushes, touch.1.1.clk_high.val < 2 ^ 24) :
    RowOKCore initialClock aligned where
  timeGap := by rw [facts.statePull, facts.statePush]; exact gap
  align8 := by rw [facts.statePull]; exact align
  touches := facts.touches
  chain_mono := facts.chain
  pushClkBound := facts.pushBound
  slotOfClkBound := fun touch member bound => facts.slot touch member bound (priorHigh touch member)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
theorem alignedFacts_of_touches (original : RowFacts p) (touches : List (Touch p))
    (projection : RowMemoryPermutation (alignedOf original touches) original)
    (localOK : ∀ touch ∈ touches, TouchOK (StateMsg.timeNat original.statePull) touch.1 touch.2)
    (chain : ∀ loc, List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (touches.filter (fun touch => MemoryMsg.locOf touch.2 = loc)))
    (pushBound : ∀ touch ∈ touches, MemoryMsg.ClkBound touch.2)
    (slot : ∀ touch ∈ touches, MemoryMsg.ClkBound touch.1.1 → touch.1.1.clk_high.val < 2 ^ 24 →
      MemoryMsg.timeNat touch.1.1 < MemoryMsg.timeNat touch.2) :
    AlignedFacts (alignedOf original touches) original where
  statePull := rfl
  statePush := rfl
  fetch := rfl
  memory := projection
  touches := List.forall₂_map_left_iff.mpr
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr localOK))
  chain := by intro loc; rw [rowTouchesAt_alignedOf]; exact chain loc
  pushBound := by
    intro message member
    obtain ⟨touch, touchMem, rfl⟩ := List.mem_map.mp member
    exact pushBound touch touchMem
  slot := by
    have zipped : (touches.map Prod.fst).zip (touches.map Prod.snd) = touches := by
      simp [List.zip_map']
    change ∀ touch ∈ (touches.map Prod.fst).zip (touches.map Prod.snd), _
    rw [zipped]
    exact slot

theorem syscall_operands_of_committed (row : SyscallInstrsChip.Inputs (ZMod p)) (program : Target.GuestProgram)
    (committed : Target.committedInROM program (rowOfMsg (SyscallInstrsChip.programMessage row))) :
    row.op_a = 5 ∧ row.op_b = 10 ∧ row.op_c = 11 := by
  have shape := (committed.ecall_of_opcode rfl).2
  exact ⟨congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_a) shape,
    congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape,
    congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape⟩

theorem halt_aligned (row : HaltChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8)
    (timestamps : SystemTouches.TimestampBounds row.state row.x5_memory row.x10_memory row.x11_memory) :
    ∃ aligned, AlignedFacts aligned (haltRowFacts row) := by
  let touches := SystemTouches.touches row.state row.x5_memory row.x10_memory row.x11_memory row.x5_memory.prev_value
  have facts := SystemTouches.touches_spec row.state row.x5_memory row.x10_memory row.x11_memory
    row.x5_memory.prev_value clock timestamps
  refine ⟨alignedOf (haltRowFacts row) touches, ?_⟩
  apply alignedFacts_of_touches (haltRowFacts row) touches
  · -- Unfold both message spellings to the same literals before `Perm.refl`: identifying them by
    -- unification alone recurses through `List.map` past the depth limit.
    constructor <;>
      simp only [alignedOf, touches, SystemTouches.touches, haltRowFacts, HaltChip.memoryPairs,
        List.map_cons, List.map_nil, SystemTouches.prior, SystemTouches.push,
        HaltChip.memPulledMessage, HaltChip.memPushedMessage] <;>
      exact List.Perm.refl _
  · change ∀ touch ∈ touches, TouchOK (SystemTouches.start row.state) touch.1 touch.2
    exact facts.1
  · exact facts.2.1
  · exact facts.2.2.1
  · exact fun touch member bound _ => facts.2.2.2 touch member bound

theorem syscall_aligned (row : SyscallInstrsChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8)
    (timestamps : SystemTouches.TimestampBounds row.state row.op_a_memory row.op_b_memory row.op_c_memory)
    (operands : row.op_a = 5 ∧ row.op_b = 10 ∧ row.op_c = 11) :
    ∃ aligned, AlignedFacts aligned (syscallRowFacts row) := by
  let touches := SystemTouches.touches row.state row.op_a_memory row.op_b_memory row.op_c_memory row.op_a_value
  have facts := SystemTouches.touches_spec row.state row.op_a_memory row.op_b_memory row.op_c_memory
    row.op_a_value clock timestamps
  refine ⟨alignedOf (syscallRowFacts row) touches, alignedFacts_of_touches (syscallRowFacts row) touches ?_ facts.1 facts.2.1 facts.2.2.1
    (fun touch member bound _ => facts.2.2.2 touch member bound)⟩
  constructor
  · simp only [alignedOf, syscallRowFacts, operands.1, operands.2.1, operands.2.2]
    exact List.Perm.refl _
  · simp only [alignedOf, syscallRowFacts, operands.1, operands.2.1, operands.2.2]
    exact List.Perm.refl _

theorem align_rows (data : ProverData (ZMod p)) (ordered : List (ExecutionRow p))
    (available : ∀ row ∈ ordered, ∃ aligned, AlignedFacts aligned (row.facts data)) :
    ∃ rows, List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts data)) := by
  induction ordered with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
    obtain ⟨aligned, headOK⟩ := available head List.mem_cons_self
    obtain ⟨rows, tailOK⟩ := ih (fun row member => available row (List.mem_cons_of_mem _ member))
    exact ⟨aligned :: rows, .cons headOK tailOK⟩

/-- Any supported ordinary row with its actual constraints, Byte facts, and authenticated fetch
admits alignment through its registered chip contract. -/
theorem ordinary_aligned (data : ProverData (ZMod p)) (row : DecodedInstructionRow p)
    (chipMem : row.chip ∈ supportedChips) (active : (row.toChipRow data).is_real = 1)
    (checked : row.chip.table.operations.ConstraintsHold (row.environment data))
    (byte : row.chip.table.operations.ChannelGuarantees byteChannel.toRaw (row.environment data))
    (program : Target.GuestProgram)
    (committed : Target.committedInROM program (programAccess (row.toChipRow data).view).toRow) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.instruction row).facts data) := by
  have decode := committed.decoded_of_opcode_ne
    (supportedChip_fetchDiscriminantShape row.chip chipMem data row.physical checked byte active)
  obtain ⟨touches, projection, localOK, chain, pushBound, slot⟩ :=
    (supportedChip_groundingContracts row.chip chipMem).rowAlignedLocal data row rfl active
      checked byte program decode
  exact ⟨alignedOf _ touches, alignedFacts_of_touches _ _ (RowMemoryPermutation.of_alignsWith projection)
    localOK chain pushBound slot⟩

end SP1Clean.Soundness.NativeCore
