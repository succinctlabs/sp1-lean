import SP1Clean.Soundness.Grounding.MemoryCell
import SP1Clean.Soundness.Grounding.ITypeChips
import SP1Clean.Soundness.TypedTimeContracts

/-! # Load/store grounding over the generic RAM-access projection

The nine Core memory chips all compose the same upstream `MemoryAccess` block and differ only in
their byte-selection/read-modify-write arithmetic. This module owns their shared whole-machine
surface:

* the exact aligned RAM pull/push messages derived from `Trace.RamAccessView`;
* the normal-load and immutable-register six-message layouts;
* the corresponding ordinary-row pull/push lists;
* the retained `MemoryAccess` timestamp contract; and
* the common RAM/register timed carrier and wiring.

Concrete chip sections below authenticate these abstractions against each chip's
`interactionsWith_memory_eq` theorem. No generated operation circuit or operation-level
faithfulness anchor enters this boundary.
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

section MemoryShape

variable [Fact (2 ^ 25 < p)]

/-- The prior aligned RAM-cell record consumed by a generic `MemoryAccess`. -/
def ramPriorMessage (access : Trace.RamAccessView (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨access.prevHigh, access.prevLow, access.address[0], access.address[1],
    access.address[2], access.priorValue⟩

/-- The current aligned RAM-cell record produced at SP1's `+1` memory slot. -/
def ramPushMessage (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high,
    view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 1,
    access.address[0], access.address[1], access.address[2], access.newValue⟩

/-- The six Memory interactions of a normal load: RAM pull/push, destination prior, source-B
prior/read-back, and destination write. -/
noncomputable def loadMemoryInteractions (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real (ramPriorMessage access),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (ramPushMessage view access),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (rtypeWriteMessage view)]

/-- The six Memory interactions shared by LoadX0 and stores: RAM pull/push followed by immutable
read/read-back pairs for source A at `+4` and source B at `+3`. -/
noncomputable def immutableRamMemoryInteractions (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real (ramPriorMessage access),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (ramPushMessage view access),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3)]

/-- Descriptor-level normal-load Memory shape. `access_eq` pins the shared semantic projection to
the exact heterogeneous chip row; `interactions` authenticates it against the evaluated circuit. -/
structure LoadMemoryInteractionShape (chip : SupportedChip p) where
  access : DecodedInstructionRow p → ProverData (ZMod p) → Trace.RamAccessView (ZMod p)
  access_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).ramAccess = some (access decoded data)
  interactions : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        loadMemoryInteractions (decoded.toChipRow data).view (access decoded data)

/-- Descriptor-level Memory shape shared by LoadX0 and stores. -/
structure ImmutableRamMemoryInteractionShape (chip : SupportedChip p) where
  access : DecodedInstructionRow p → ProverData (ZMod p) → Trace.RamAccessView (ZMod p)
  access_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).ramAccess = some (access decoded data)
  interactions : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        immutableRamMemoryInteractions (decoded.toChipRow data).view (access decoded data)

omit [Fact (2 ^ 25 < p)] in
private theorem ramPull_one_signed (message : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue
      (memoryChannel (p := p)) 1 message).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem ramPush_one_signed (message : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue
      (memoryChannel (p := p)) 1 message).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_loadSix
    (ramPrior ramPush priorA priorB readB writeA : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 ramPrior,
       TypedInteraction.pushedIfValue memoryChannel 1 ramPush,
       TypedInteraction.pulledIfValue memoryChannel 1 priorA,
       TypedInteraction.pulledIfValue memoryChannel 1 priorB,
       TypedInteraction.pushedIfValue memoryChannel 1 readB,
       TypedInteraction.pushedIfValue memoryChannel 1 writeA] =
      [ramPrior, priorA, priorB] := by
  simp only [consumedMessages, List.filter_cons, List.filter_nil,
    ramPull_one_signed, ramPush_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_loadSix
    (ramPrior ramPush priorA priorB readB writeA : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 ramPrior,
       TypedInteraction.pushedIfValue memoryChannel 1 ramPush,
       TypedInteraction.pulledIfValue memoryChannel 1 priorA,
       TypedInteraction.pulledIfValue memoryChannel 1 priorB,
       TypedInteraction.pushedIfValue memoryChannel 1 readB,
       TypedInteraction.pushedIfValue memoryChannel 1 writeA] =
      [ramPush, readB, writeA] := by
  simp only [producedMessages, List.filter_cons, List.filter_nil,
    ramPull_one_signed, ramPush_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_immutableRamSix
    (ramPrior ramPush priorA readA priorB readB : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 ramPrior,
       TypedInteraction.pushedIfValue memoryChannel 1 ramPush,
       TypedInteraction.pulledIfValue memoryChannel 1 priorA,
       TypedInteraction.pushedIfValue memoryChannel 1 readA,
       TypedInteraction.pulledIfValue memoryChannel 1 priorB,
       TypedInteraction.pushedIfValue memoryChannel 1 readB] =
      [ramPrior, priorA, priorB] := by
  simp only [consumedMessages, List.filter_cons, List.filter_nil,
    ramPull_one_signed, ramPush_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_immutableRamSix
    (ramPrior ramPush priorA readA priorB readB : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 ramPrior,
       TypedInteraction.pushedIfValue memoryChannel 1 ramPush,
       TypedInteraction.pulledIfValue memoryChannel 1 priorA,
       TypedInteraction.pushedIfValue memoryChannel 1 readA,
       TypedInteraction.pulledIfValue memoryChannel 1 priorB,
       TypedInteraction.pushedIfValue memoryChannel 1 readB] =
      [ramPush, readA, readB] := by
  simp only [producedMessages, List.filter_cons, List.filter_nil,
    ramPull_one_signed, ramPush_one_signed]
  norm_num

/-- An active normal load consumes the RAM prior plus destination/source-B register priors. -/
theorem consumedMemoryMessages_eq_of_loadShape {chip : SupportedChip p}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [ramPriorMessage (shape.access decoded data),
       rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold loadMemoryInteractions
  rw [real]
  exact consumedMessages_loadSix _ _ _ _ _ _

/-- An active normal load produces the RAM current cell, source-B read-back, and destination write. -/
theorem producedMemoryMessages_eq_of_loadShape {chip : SupportedChip p}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [ramPushMessage (decoded.toChipRow data).view (shape.access decoded data),
       rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold loadMemoryInteractions
  rw [real]
  exact producedMessages_loadSix _ _ _ _ _ _

/-- An active immutable-register RAM row consumes the RAM prior and both register priors. -/
theorem consumedMemoryMessages_eq_of_immutableRamShape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [ramPriorMessage (shape.access decoded data),
       rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableRamMemoryInteractions
  rw [real]
  exact consumedMessages_immutableRamSix _ _ _ _ _ _

/-- An active immutable-register RAM row produces the RAM current cell and both read-backs. -/
theorem producedMemoryMessages_eq_of_immutableRamShape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [ramPushMessage (decoded.toChipRow data).view (shape.access decoded data),
       rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_a
        (decoded.toChipRow data).view.adapter.op_a_memory 4,
       rtypeReadBackMessage (decoded.toChipRow data).view
        (decoded.toChipRow data).view.adapter.op_b[0]
        (decoded.toChipRow data).view.adapter.op_b_memory 3] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableRamMemoryInteractions
  rw [real]
  exact producedMessages_immutableRamSix _ _ _ _ _ _

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- A concrete active pull inherits the Memory channel's word-range guarantee.  This small helper
keeps the three-word load/store lemmas below about the authenticated interaction layout rather
than the mechanics of `TypedInteraction.guarantee_of_channelGuarantees`. -/
private theorem pulledWord_isU64_of_guarantees
    (operations : Operations (ZMod p))
    (env : Environment (ZMod p))
    (message : MemoryMsg (ZMod p))
    (pull : TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 message ∈
      typedInteractionValuesWith operations memoryChannel env)
    (guarantees : operations.ChannelGuarantees memoryChannel.toRaw env) :
    Word.isU64 message.value := by
  let interaction := TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 message
  have negative : interaction.mult = -1 := by
    simp only [interaction, TypedInteraction.pulledIfValue_mult]
  have guarantee := TypedInteraction.guarantee_of_channelGuarantees
    operations memoryChannel env interaction pull guarantees (by rfl) negative
  simpa only [Channels.memoryChannel, interaction,
    TypedInteraction.pulledIfValue_message, MemoryMsg.isU64] using guarantee.1

/-- The RAM prior and both register-source words of an active normal-load row are genuine 64-bit
words.  These are bus guarantees authenticated by the exact six-interaction shape, not arithmetic
assumptions smuggled into the chip contract. -/
theorem loadPulledWords_isU64_of_shape {chip : SupportedChip p}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data)) :
    Word.isU64 (shape.access decoded data).priorValue ∧
      Word.isU64 (decoded.toChipRow data).view.adapter.op_a_memory.prev_value ∧
      Word.isU64 (decoded.toChipRow data).view.adapter.op_b_memory.prev_value := by
  let view := (decoded.toChipRow data).view
  have ramMem :
      TypedInteraction.pulledIfValue memoryChannel view.is_real
        (ramPriorMessage (shape.access decoded data)) ∈
        decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_self
  have aMem :
      TypedInteraction.pulledIfValue memoryChannel view.is_real
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) ∈
        decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have bMem :
      TypedInteraction.pulledIfValue memoryChannel view.is_real
        (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory) ∈
        decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [real] at ramMem aMem bMem
  exact ⟨
    pulledWord_isU64_of_guarantees decoded.chip.table.operations
      (decoded.environment data) _ ramMem guarantees,
    pulledWord_isU64_of_guarantees decoded.chip.table.operations
      (decoded.environment data) _ aMem guarantees,
    pulledWord_isU64_of_guarantees decoded.chip.table.operations
      (decoded.environment data) _ bMem guarantees⟩

/-- LoadX0 and the four stores have the same three authenticated pull words: the prior RAM cell,
source A, and source B. -/
theorem immutableRamPulledWords_isU64_of_shape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data)) :
    Word.isU64 (shape.access decoded data).priorValue ∧
      Word.isU64 (decoded.toChipRow data).view.adapter.op_a_memory.prev_value ∧
      Word.isU64 (decoded.toChipRow data).view.adapter.op_b_memory.prev_value := by
  let view := (decoded.toChipRow data).view
  have ramMem :
      TypedInteraction.pulledIfValue memoryChannel view.is_real
        (ramPriorMessage (shape.access decoded data)) ∈
        decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_self
  have aMem :
      TypedInteraction.pulledIfValue memoryChannel view.is_real
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory) ∈
        decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have bMem :
      TypedInteraction.pulledIfValue memoryChannel view.is_real
        (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory) ∈
        decoded.interactionsWith data memoryChannel := by
    rw [shape.interactions decoded data hchip]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))
  rw [real] at ramMem aMem bMem
  exact ⟨
    pulledWord_isU64_of_guarantees decoded.chip.table.operations
      (decoded.environment data) _ ramMem guarantees,
    pulledWord_isU64_of_guarantees decoded.chip.table.operations
      (decoded.environment data) _ aMem guarantees,
    pulledWord_isU64_of_guarantees decoded.chip.table.operations
      (decoded.environment data) _ bMem guarantees⟩

/-! ## Retained RAM timestamp contract -/

/-- Scalar binding from one retained `MemoryAccess` reader to the chip-independent row and RAM
views. Only fields consumed by timestamp ordering appear here. -/
structure RamAccessTimestampBinding
    (readerReal compare prevHigh prevLow diffLow diffHigh clkHigh clkLow : ZMod p)
    (view : Trace.RowView (ZMod p)) (access : Trace.RamAccessView (ZMod p)) : Prop where
  real_eq : readerReal = view.is_real
  compare_eq : compare = access.compareLow
  prevHigh_eq : prevHigh = access.prevHigh
  prevLow_eq : prevLow = access.prevLow
  diffLow_eq : diffLow = access.diffLow
  diffHigh_eq : diffHigh = access.diffHigh
  clkHigh_eq : clkHigh = view.state.clk_high
  clkLow_eq : clkLow =
    view.state.clk_0_16 + view.state.clk_16_24 * 65536

/-- Locate the retained generic RAM reader and bind it to the descriptor's optional
`RamAccessView`, without unfolding the completed chip in consumers. -/
inductive CircuitRamAccessTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (ramAccess :
      Input (ZMod p) → Output (ZMod p) → Option (Trace.RamAccessView (ZMod p))) : Prop where
  | intro (readerOffset : ℕ) (readerInput : Var Readers.MemoryAccess.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.MemoryAccess.circuit (p := p)).toSubcircuit readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        ∀ access : Trace.RamAccessView (ZMod p),
          ramAccess
              (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
              (Eval.eval env
                (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))) =
            some access →
          RamAccessTimestampBinding
            (Expression.eval env readerInput.is_real)
            (Expression.eval env readerInput.mem.access_timestamp.compare_low)
            (Expression.eval env readerInput.mem.access_timestamp.prev_high)
            (Expression.eval env readerInput.mem.access_timestamp.prev_low)
            (Expression.eval env readerInput.mem.access_timestamp.diff_low_limb)
            (Expression.eval env readerInput.mem.access_timestamp.diff_high_limb)
            (Expression.eval env readerInput.clk_high)
            (Expression.eval env readerInput.clk_low)
            (view
              (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
              (Eval.eval env
                (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))
            access) :
      CircuitRamAccessTimestampContract circuit view ramAccess

/-- Whole-chip constraints plus finished Byte guarantees specialize the retained generic RAM
reader to `ActiveMemoryTimestampFacts`. The reader's Memory guarantee is deliberately absent. -/
theorem ramAccessTimestampFacts_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (ramAccess :
      Input (ZMod p) → Output (ZMod p) → Option (Trace.RamAccessView (ZMod p)))
    (contract : CircuitRamAccessTimestampContract circuit view ramAccess)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (access : Trace.RamAccessView (ZMod p))
    (accessEq : ramAccess
      ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data)) = some access)
    (real : (view
      ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    ActiveMemoryTimestampFacts access.compareLow access.prevHigh access.prevLow
      access.diffLow access.diffHigh
      (view
        ((⟨circuit⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data))
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput
          (Environment.fromArray physical data))).state.clk_high
      ((view
        ((⟨circuit⟩ : Component (ZMod p)).rowInput
          (Environment.fromArray physical data))
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput
          (Environment.fromArray physical data))).state.clk_0_16 +
        (view
          ((⟨circuit⟩ : Component (ZMod p)).rowInput
            (Environment.fromArray physical data))
          ((⟨circuit⟩ : Component (ZMod p)).rowOutput
            (Environment.fromArray physical data))).state.clk_16_24 * 65536) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowConstraints : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have readerConstraints := constraintsHold_generalSubcircuit_of_mem env
    component.rowOperations Readers.MemoryAccess.circuit readerInput readerOffset
    readerMem rowConstraints
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.MemoryAccess.circuit (p := p)).toSubcircuit readerOffset readerInput)
    readerMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env
      (circuit.output (varFromOffset Input 0) (size Input)) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env access
  rw [inputEq, outputEq] at bound
  have fields := bound accessEq
  have readerReal : Expression.eval env readerInput.is_real = 1 := fields.real_eq.trans real
  have facts := Readers.MemoryAccess.timestampFacts_of_constraintsAndByteGuarantees
    readerInput readerOffset env readerConstraints readerGuarantees readerReal
  rwa [fields.compare_eq, fields.prevHigh_eq, fields.prevLow_eq, fields.diffLow_eq,
    fields.diffHigh_eq, fields.clkHigh_eq, fields.clkLow_eq] at facts

/-! ## Retained address-operation contract -/

/-- The aligned address is outside the register-file encoding. The retained `AddressOperation`
inverse gate is the physical source of this fact for each concrete load/store chip. -/
def RamAccessIsRam (access : Trace.RamAccessView (ZMod p)) : Prop :=
  ¬ (access.address[0].val < 32 ∧ access.address[1] = 0 ∧ access.address[2] = 0)

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem memoryEqualityConstraint_mem
    (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈
      ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

omit [Fact (2 ^ 25 < p)] in
/-- The three retained `AddressOperation` selector gates prove that the evaluated byte-offset
columns are Boolean. This physical projection needs neither operand assumptions nor the operation
`Spec`; store grounding uses it before the parent chip's assumptions are available. -/
theorem AddressOperation.offsetBits_bool_of_constraints
    (input : Var AddressOperation.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((AddressOperation.main input).operations offset)) :
    (Expression.eval env input.offset_bit0 = 0 ∨
        Expression.eval env input.offset_bit0 = 1) ∧
      (Expression.eval env input.offset_bit1 = 0 ∨
        Expression.eval env input.offset_bit1 = 1) ∧
      (Expression.eval env input.offset_bit2 = 0 ∨
        Expression.eval env input.offset_bit2 = 1) := by
  have gate0 : Expression.eval env
      (input.offset_bit0 * (input.offset_bit0 - 1) - 0) = 0 := by
    apply constraints.1
    simp only [AddressOperation.main, circuit_norm]
    iterate 2 right
    left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      memoryEqualityConstraint_mem (input.offset_bit0 * (input.offset_bit0 - 1)) 0 _
  have gate1 : Expression.eval env
      (input.offset_bit1 * (input.offset_bit1 - 1) - 0) = 0 := by
    apply constraints.1
    simp only [AddressOperation.main, circuit_norm]
    iterate 3 right
    left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      memoryEqualityConstraint_mem (input.offset_bit1 * (input.offset_bit1 - 1)) 0 _
  have gate2 : Expression.eval env
      (input.offset_bit2 * (input.offset_bit2 - 1) - 0) = 0 := by
    apply constraints.1
    simp only [AddressOperation.main, circuit_norm]
    iterate 4 right
    left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      memoryEqualityConstraint_mem (input.offset_bit2 * (input.offset_bit2 - 1)) 0 _
  simp only [eval_sub, Expression.eval, sub_zero] at gate0 gate1 gate2
  exact ⟨bool_of_mul_pred gate0, bool_of_mul_pred gate1, bool_of_mul_pred gate2⟩

omit [Fact (2 ^ 25 < p)] in
/-- The physical inverse constraint of `AddressOperation` forces at least one upper 16-bit
address limb to be nonzero. This is the precise local fact which separates a load/store RAM access
from the register-file encoding; it uses neither the operation `Spec` nor Memory guarantees. -/
theorem AddressOperation.upperLimbs_not_both_zero_of_constraints
    (input : Var AddressOperation.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((AddressOperation.main input).operations offset).ConstraintsHold env) :
    Expression.eval env input.is_real = 1 →
    ¬ (Expression.eval env (var { index := offset + 1 }) = 0 ∧
      Expression.eval env (var { index := offset + 2 }) = 0) := by
  intro real
  have inverseEq : Expression.eval env
      (var { index := offset + 3 } *
        (var { index := offset + 1 } + var { index := offset + 2 }) - input.is_real) = 0 := by
    let inverse : Expression (ZMod p) :=
      var { index := offset + 3 } *
        (var { index := offset + 1 } + var { index := offset + 2 }) - input.is_real
    have inverseDiffEq : Expression.eval env
        ((toElements (M := field) inverse)[0] -
          (toElements (M := field) (0 : Expression (ZMod p)))[0]) = 0 := by
      apply constraints.1
      simp only [AddressOperation.main, circuit_norm]
      iterate 5 right
      simp [inverse, FormalAssertion.toSubcircuit, Gadgets.Equality.main,
        Circuit.forEach.operations_eq, FlatOperation.constraints, circuit_norm]
    have element (x : Expression (ZMod p)) : (toElements (M := field) x)[0] = x := rfl
    rw [element, element] at inverseDiffEq
    simpa only [inverse, eval_sub, Expression.eval, sub_zero] using inverseDiffEq
  intro upperZero
  change env.get (offset + 1) = 0 ∧ env.get (offset + 2) = 0 at upperZero
  simp only [eval_sub, Expression.eval] at inverseEq
  rw [real] at inverseEq
  rw [upperZero.1, upperZero.2] at inverseEq
  simp only [add_zero, mul_zero, zero_sub, neg_eq_zero] at inverseEq
  exact one_ne_zero inverseEq

/-- Locate the retained `AddressOperation` and bind its aligned output to the generic RAM view. -/
inductive CircuitRamAddressContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (ramAccess :
      Input (ZMod p) → Output (ZMod p) → Option (Trace.RamAccessView (ZMod p)))
    (selector : Input (ZMod p) → ZMod p) : Prop where
  | intro (addressOffset : ℕ) (addressInput : Var AddressOperation.Inputs (ZMod p))
      (address_mem :
        ⟨addressOffset,
          (AddressOperation.circuit (p := p)).toSubcircuit addressOffset addressInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        ∀ access : Trace.RamAccessView (ZMod p),
          ramAccess
              (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
              (Eval.eval env
                (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))) =
            some access →
          access.address = Eval.eval env
            (AddressOperation.alignedValue addressInput
              ((AddressOperation.circuit (p := p)).output addressInput addressOffset)))
      (selector_binding : ∀ env : Environment (ZMod p),
        Eval.eval env addressInput.is_real =
          selector (Eval.eval env (varFromOffset (F := ZMod p) Input 0))) :
      CircuitRamAddressContract circuit ramAccess selector

omit [Fact (2 ^ 25 < p)] in
/-- Whole-chip constraints specialize the retained address inverse gate to the public RAM view. -/
theorem ramAccessIsRam_of_addressContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (ramAccess :
      Input (ZMod p) → Output (ZMod p) → Option (Trace.RamAccessView (ZMod p)))
    (selector : Input (ZMod p) → ZMod p)
    (contract : CircuitRamAddressContract circuit ramAccess selector)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data))
    (real : selector ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) = 1)
    (access : Trace.RamAccessView (ZMod p))
    (accessEq : ramAccess
      ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data)) = some access) :
    RamAccessIsRam access := by
  obtain ⟨addressOffset, addressInput, addressMem, binding, selectorBinding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowConstraints : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have addressConstraints := constraintsHold_generalSubcircuit_of_mem env
    component.rowOperations AddressOperation.circuit addressInput addressOffset
    addressMem rowConstraints
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have selectorEq := selectorBinding env
  rw [inputEq] at selectorEq
  have addressReal : Expression.eval env addressInput.is_real = 1 := by
    simpa only [CircuitType.eval_expr] using selectorEq.trans real
  have upper :=
    AddressOperation.upperLimbs_not_both_zero_of_constraints
      addressInput addressOffset env addressConstraints addressReal
  have outputEq : Eval.eval env
      (circuit.output (varFromOffset Input 0) (size Input)) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env access
  rw [inputEq, outputEq] at bound
  have addressEq := bound accessEq
  unfold RamAccessIsRam
  intro registerShape
  apply upper
  have upperOne := congrArg (fun address : Vector (ZMod p) 3 => address[1]) addressEq
  have upperTwo := congrArg (fun address : Vector (ZMod p) 3 => address[2]) addressEq
  constructor
  · rw [registerShape.2.1] at upperOne
    simpa only [AddressOperation.alignedValue, AddressOperation.circuit, circuit_norm] using
      upperOne.symm
  · rw [registerShape.2.2] at upperTwo
    simpa only [AddressOperation.alignedValue, AddressOperation.circuit, circuit_norm] using
      upperTwo.symm

/-! ## Shared RAM/I-type timed carrier -/

/-- The canonical cell named by the three-limb aligned RAM address. -/
def ramCellOfAccess (access : Trace.RamAccessView (ZMod p)) : RamCell :=
  BitVec.ofNat 61
    ((access.address[0].val + access.address[1].val * 2 ^ 16 +
      access.address[2].val * 2 ^ 32) / 8)

/-- Natural interpretation of SP1's canonical three-limb 48-bit address. -/
def address48Nat (address : Vector (ZMod p) 3) : ℕ :=
  address[0].val + address[1].val * 2 ^ 16 + address[2].val * 2 ^ 32

/-- Natural byte offset represented by `AddressOperation`'s three boolean columns. -/
def addressOffset (input : AddressOperation.Inputs (ZMod p)) : ℕ :=
  input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val

omit [Fact (2 ^ 25 < p)] in
/-- The aligned Memory-bus cell and the raw Sail-visible byte address are two views of the same
AIR address: `raw = cellBase + offset`. The proof consumes only the folded semantic
`AddressOperation.Spec`; in particular the newly explicit limb bounds prevent a non-canonical
three-field representation from reaching the machine layer. -/
theorem rawAddress_eq_ramCellBase_add_offset
    (input : AddressOperation.Inputs (ZMod p))
    (cols : Extracted.AddressOperation (ZMod p))
    (access : Trace.RamAccessView (ZMod p))
    (addressEq : access.address = AddressOperation.alignedValue input cols)
    (spec : AddressOperation.Spec input cols) :
    address48Nat cols.addr_operation.value =
      (ramCellOfAccess access).baseAddr.toNat + addressOffset input := by
  have hp : 2 ^ 17 < p := Fact.out
  have bounds := AddressOperation.limbBounds_of_spec spec
  have offsetEq :
      addressOffset input = address48Nat cols.addr_operation.value % 8 := by
    have h := spec.2.2.2.2.2.2.1
    rw [← spec.1] at h
    norm_num [addressOffset, address48Nat, Nat.add_mod] at h ⊢
    omega
  have rawModLow :
      address48Nat cols.addr_operation.value % 8 = cols.addr_operation.value[0].val % 8 := by
    norm_num [address48Nat, Nat.add_mod]
    omega
  have offsetLe : addressOffset input ≤ cols.addr_operation.value[0].val := by
    rw [offsetEq, rawModLow]
    exact Nat.mod_le _ _
  have offsetLt : addressOffset input < 8 := by
    rw [offsetEq]
    exact Nat.mod_lt _ (by norm_num)
  have offsetCast :
      ((addressOffset input : ℕ) : ZMod p) =
        4 * input.offset_bit2 + 2 * input.offset_bit1 + input.offset_bit0 := by
    rcases spec.2.1 with h0 | h0 <;>
      rcases spec.2.2.1 with h1 | h1 <;>
      rcases spec.2.2.2.1 with h2 | h2 <;>
      simp [addressOffset, h0, h1, h2] <;> ring_nf
  have aligned0 :
      (AddressOperation.alignedValue input cols)[0].val =
        cols.addr_operation.value[0].val - addressOffset input := by
    have fieldEq :
        (AddressOperation.alignedValue input cols)[0] =
          cols.addr_operation.value[0] - (addressOffset input : ZMod p) := by
      change cols.addr_operation.value[0] - 4 * input.offset_bit2 -
          2 * input.offset_bit1 - input.offset_bit0 =
        cols.addr_operation.value[0] - (addressOffset input : ZMod p)
      rw [offsetCast]
      ring_nf
    have castEq :
        ((cols.addr_operation.value[0].val - addressOffset input : ℕ) : ZMod p) =
          cols.addr_operation.value[0] - (addressOffset input : ZMod p) := by
      rw [Nat.cast_sub offsetLe, ZMod.natCast_zmod_val]
    rw [fieldEq, ← castEq, ZMod.val_natCast_of_lt]
    omega
  have alignedNat :
      address48Nat access.address =
        address48Nat cols.addr_operation.value - addressOffset input := by
    rw [addressEq]
    change (AddressOperation.alignedValue input cols)[0].val +
        cols.addr_operation.value[1].val * 2 ^ 16 +
        cols.addr_operation.value[2].val * 2 ^ 32 =
      (cols.addr_operation.value[0].val +
          cols.addr_operation.value[1].val * 2 ^ 16 +
          cols.addr_operation.value[2].val * 2 ^ 32) -
        addressOffset input
    rw [aligned0]
    omega
  have alignedMod : address48Nat access.address % 8 = 0 := by
    rw [alignedNat]
    exact Nat.sub_mod_eq_zero_of_mod_eq (offsetEq.symm.trans (Nat.mod_eq_of_lt offsetLt).symm)
  have alignedLt : address48Nat access.address < 2 ^ 48 := by
    have rawLt : address48Nat cols.addr_operation.value < 2 ^ 48 := by
      simp only [address48Nat]
      omega
    rw [alignedNat]
    omega
  have cellNat :
      (ramCellOfAccess access).baseAddr.toNat = address48Nat access.address := by
    have quotientLt : address48Nat access.address / 8 < 2 ^ 61 := by omega
    rw [RamCell.baseAddr_toNat]
    unfold ramCellOfAccess
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      simpa only [address48Nat] using quotientLt)]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero alignedMod)
  rw [cellNat, alignedNat]
  omega

omit [Fact (2 ^ 25 < p)] in
/-- The address used by Sail/Rust (`u64::wrapping_add`) is the raw byte address represented by the
AIR columns, hence the aligned RAM-cell base plus its three-bit offset. -/
theorem effectiveAddress_eq_ramCellBase_add_offset
    (input : AddressOperation.Inputs (ZMod p))
    (cols : Extracted.AddressOperation (ZMod p))
    (access : Trace.RamAccessView (ZMod p))
    (addressEq : access.address = AddressOperation.alignedValue input cols)
    (spec : AddressOperation.Spec input cols)
    (baseBound : Word.isU64 input.b) (immediateBound : Word.isU64 input.cc) :
    (AddressOperation.effectiveAddress input).toNat =
      (ramCellOfAccess access).baseAddr.toNat + addressOffset input := by
  have valid := AddressOperation.validAddress_of_spec spec
  calc
    (AddressOperation.effectiveAddress input).toNat =
        (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 :=
      (AddressOperation.addressMod48_eq_effectiveAddress_toNat
        baseBound immediateBound valid).symm
    _ = address48Nat cols.addr_operation.value := by
      rw [← spec.1]
      simp only [address48Nat]
      omega
    _ = (ramCellOfAccess access).baseAddr.toNat + addressOffset input :=
      rawAddress_eq_ramCellBase_add_offset input cols access addressEq spec

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem locOf_ramPriorMessage (access : Trace.RamAccessView (ZMod p))
    (isRam : RamAccessIsRam access) :
    MemoryMsg.locOf (ramPriorMessage access) = MemLoc.ram (ramCellOfAccess access) := by
  unfold RamAccessIsRam at isRam
  simp only [MemoryMsg.locOf, ramPriorMessage]
  rw [if_neg isRam]
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- Turn membership of the authenticated generic RAM pull into a live Sail-state cell read. -/
theorem ramPriorContent_of_member
    {rf : Semantics.RowFacts p} {state : SailState}
    (access : Trace.RamAccessView (ZMod p)) (isRam : RamAccessIsRam access)
    (pulls : MemoryPullsBound rf state)
    (member : (ramPriorMessage access, StateMsg.timeNat rf.statePull) ∈ rf.memPulls) :
    ramWord64? state (ramCellOfAccess access).baseAddr =
      some (Word.toBitVec64 access.priorValue) := by
  have content := pulls _ member
  rw [locOf_ramPriorMessage access isRam] at content
  simpa only [locContent, ramPriorMessage] using content

/-- The head RAM pull of a normal-load interaction shape authenticates the complete live Sail
cell.  This is the common readiness bridge for LB/LH/LW/LD: the concrete chip only has to select
the relevant byte(s) from the returned canonical word decomposition. -/
theorem ramPriorContent_of_loadShape {chip : SupportedChip p}
    {state : SailState}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (pulls : MemoryPullsBound (decoded.ordinaryRowFacts data) state) :
    ramWord64? state (ramCellOfAccess (shape.access decoded data)).baseAddr =
      some (Word.toBitVec64 (shape.access decoded data).priorValue) := by
  apply ramPriorContent_of_member (shape.access decoded data) isRam pulls
  rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
    consumedMemoryMessages_eq_of_loadShape shape decoded data hchip real]
  simp only [List.map_cons, List.map_nil, List.mem_cons]
  left
  rfl

/-- Immutable-RAM rows (LoadX0 and stores) expose the same authenticated prior cell at the head of
their six-message Memory layout. -/
theorem ramPriorContent_of_immutableRamShape {chip : SupportedChip p}
    {state : SailState}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (pulls : MemoryPullsBound (decoded.ordinaryRowFacts data) state) :
    ramWord64? state (ramCellOfAccess (shape.access decoded data)).baseAddr =
      some (Word.toBitVec64 (shape.access decoded data).priorValue) := by
  apply ramPriorContent_of_member (shape.access decoded data) isRam pulls
  rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
    consumedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real]
  simp only [List.map_cons, List.map_nil, List.mem_cons]
  left
  rfl

/-- Pointwise byte form of `ramPriorContent_of_loadShape`. -/
theorem ramPriorByte_of_loadShape {chip : SupportedChip p}
    {state : SailState}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (pulls : MemoryPullsBound (decoded.ordinaryRowFacts data) state) (i : Fin 8) :
    state.mem.get?
        ((ramCellOfAccess (shape.access decoded data)).baseAddr.toNat + i.val) =
      some (wordBytes (Word.toBitVec64 (shape.access decoded data).priorValue))[i] :=
  byte_of_ramWord64?_eq_some
    (ramPriorContent_of_loadShape shape decoded data hchip real isRam pulls) i

/-- Pointwise byte form of `ramPriorContent_of_immutableRamShape`. -/
theorem ramPriorByte_of_immutableRamShape {chip : SupportedChip p}
    {state : SailState}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (pulls : MemoryPullsBound (decoded.ordinaryRowFacts data) state) (i : Fin 8) :
    state.mem.get?
        ((ramCellOfAccess (shape.access decoded data)).baseAddr.toNat + i.val) =
      some (wordBytes (Word.toBitVec64 (shape.access decoded data).priorValue))[i] :=
  byte_of_ramWord64?_eq_some
    (ramPriorContent_of_immutableRamShape shape decoded data hchip real isRam pulls) i

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem locOf_ramPushMessage (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) (isRam : RamAccessIsRam access) :
    MemoryMsg.locOf (ramPushMessage view access) = MemLoc.ram (ramCellOfAccess access) := by
  unfold RamAccessIsRam at isRam
  simp only [MemoryMsg.locOf, ramPushMessage]
  rw [if_neg isRam]
  rfl

/-- The generic RAM push occupies SP1's `+1` cell-write slot. -/
theorem timeNat_ramPushMessage {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) (access : Trace.RamAccessView (ZMod p)) :
    MemoryMsg.timeNat (ramPushMessage view access) =
      StateMsg.timeNat (statePullOfView view) + 1 := by
  exact clkNat_add_delta_of_cpuState_bounds _ _ _ _ 1 (by simp [ZMod.val_one])
    (by omega) bounds.clk0 bounds.clk1

/-! ## Shared load/store wiring -/

/-- Wiring for a register-writing load with one unchanged RAM-cell read-back. The generic RAM push
is classified as a pre-effect read-back at `+1`; the source-B read-back and destination write use
the ordinary I-type `+3`/`+4` slots. -/
theorem rowWiring_loadRam {view : Trace.RowView (ZMod p)}
    {access : Trace.RamAccessView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.regWrite)
    (imm_c_eq : view.adapter.imm_c = 1)
    (isRam : RamAccessIsRam access)
    (unchanged : access.newValue = access.priorValue)
    (opa_lt : view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 view.rdWrite)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(ramPriorMessage access, StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [ramPushMessage view access,
       rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3,
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
    rcases hmp with rfl | rfl | rfl <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opC_pull := by
    intro _ immediate _
    rw [imm_c_eq] at immediate
    exact absurd immediate one_ne_zero
  write_push := by
    intro _ index indexEq
    refine ⟨rtypeWriteMessage view, ?_, ?_, rfl⟩
    · rw [pushes_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  push_classified := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl | rfl
    · left
      refine ⟨(ramPriorMessage access, StateMsg.timeNat rf.statePull), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_self
      · rw [locOf_ramPushMessage view access isRam, locOf_ramPriorMessage access isRam]
      · simpa only [ramPushMessage, ramPriorMessage] using unchanged
      · rw [timeNat_ramPushMessage bounds access, ← statePull_eq]
        omega
      · rw [timeNat_ramPushMessage bounds access, ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
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
      have indexEq : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
          view.adapter.op_a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
        exact ZMod.natCast_zmod_val _
      refine ⟨by rw [commit_eq]; rfl, write_isU64, ?_, rfl, ?_⟩
      · exact ⟨BitVec.ofNat 5 view.adapter.op_a.val,
          MemoryMsg.locOf_register _ _ indexEq rfl rfl, indexEq⟩
      · rw [timeNat_rtypeWriteMessage bounds, ← statePull_eq]
  push_clkBound := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 1
        (by simp [ZMod.val_one]) (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program state state' effect _ cell value _ prior
    rw [locContent_ram_congr (effect.mem.1 (by rw [commit_eq]; rfl)) cell]
    exact prior

/-- Wiring for LoadX0: the RAM cell and both register operands are read back unchanged, and the
architectural row commits neither a register write nor a memory write. -/
theorem rowWiring_immutableLoadRam {view : Trace.RowView (ZMod p)}
    {access : Trace.RamAccessView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.noWrite)
    (imm_c_eq : view.adapter.imm_c = 1)
    (isRam : RamAccessIsRam access)
    (unchanged : access.newValue = access.priorValue)
    (opa_lt : view.adapter.op_a.val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(ramPriorMessage access, StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [ramPushMessage view access,
       rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4,
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
    rcases hmp with rfl | rfl | rfl <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opC_pull := by
    intro _ immediate _
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
    rcases messageMem with rfl | rfl | rfl
    · left
      refine ⟨(ramPriorMessage access, StateMsg.timeNat rf.statePull), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_self
      · rw [locOf_ramPushMessage view access isRam, locOf_ramPriorMessage access isRam]
      · simpa only [ramPushMessage, ramPriorMessage] using unchanged
      · rw [timeNat_ramPushMessage bounds access, ← statePull_eq]
        omega
      · rw [timeNat_ramPushMessage bounds access, ← statePull_eq]
        omega
      · intro _ _
        rw [commit_eq]
        rfl
    · refine Or.inr (Or.inr (Or.inl ?_))
      refine ⟨by rw [commit_eq]; rfl,
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull), ?_, ?_, rfl, rfl, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · have indexEq : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
            view.adapter.op_a := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
          exact ZMod.natCast_zmod_val _
        exact ⟨BitVec.ofNat 5 view.adapter.op_a.val, MemoryMsg.locOf_register _ _ indexEq rfl rfl⟩
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega), ← statePull_eq]
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
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
    rcases messageMem with rfl | rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 1
        (by simp [ZMod.val_one]) (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program state state' effect _ cell value _ prior
    rw [locContent_ram_congr (effect.mem.1 (by rw [commit_eq]; rfl)) cell]
    exact prior

/-- Wiring for a store: both register accesses are immutable read-backs, while the RAM push is the
authenticated full-cell image of the committed byte-addressed store. -/
theorem rowWiring_storeRam {view : Trace.RowView (ZMod p)}
    {access : Trace.RamAccessView (ZMod p)} {rf : Semantics.RowFacts p}
    {write : Trace.MemWrite (ZMod p)}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.store write)
    (imm_c_eq : view.adapter.imm_c = 1)
    (isRam : RamAccessIsRam access)
    (inCell : write.InCell (ramCellOfAccess access))
    (update : RamCellUpdate write (ramCellOfAccess access)
      (Word.toBitVec64 access.priorValue) (Word.toBitVec64 access.newValue))
    (opa_lt : view.adapter.op_a.val < 32)
    (opb_lt : view.adapter.op_b[0].val < 32)
    (new_isU64 : Word.isU64 access.newValue)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(ramPriorMessage access, StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [ramPushMessage view access,
       rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4,
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
    rcases hmp with rfl | rfl | rfl <;> rfl
  opA_pull := by
    intro index indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opB_pull := by
    intro index _immediate indexEq
    refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index indexEq rfl rfl
  opC_pull := by
    intro _ immediate _
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
    rcases messageMem with rfl | rfl | rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      refine ⟨ramCellOfAccess access, ?_, locOf_ramPushMessage view access isRam, ?_, ?_⟩
      · simpa only [MemoryMsg.isU64, ramPushMessage] using new_isU64
      · rw [timeNat_ramPushMessage bounds access, ← statePull_eq]
      · intro program state state' effect pulls
        apply ramCellPost_of_update effect (by rw [commit_eq]; rfl) pulls ?_ update
        refine ⟨(ramPriorMessage access, StateMsg.timeNat rf.statePull), ?_,
          locOf_ramPriorMessage access isRam, rfl⟩
        rw [pulls_eq]
        exact List.mem_cons_self
    · refine Or.inr (Or.inr (Or.inl ?_))
      refine ⟨by rw [commit_eq]; rfl,
        (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull), ?_, ?_, rfl, rfl, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · have indexEq : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
            view.adapter.op_a := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
          exact ZMod.natCast_zmod_val _
        exact ⟨BitVec.ofNat 5 view.adapter.op_a.val, MemoryMsg.locOf_register _ _ indexEq rfl rfl⟩
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega), ← statePull_eq]
    · left
      refine ⟨(rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega),
          ← statePull_eq]
        omega
      · intro cell ramLoc
        have indexEq : ((BitVec.ofNat 5 view.adapter.op_b[0].val).toNat : ZMod p) =
            view.adapter.op_b[0] := by
          rw [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show view.adapter.op_b[0].val < 2 ^ 5 by omega)]
          exact ZMod.natCast_zmod_val _
        rw [MemoryMsg.locOf_register _ _ indexEq rfl rfl] at ramLoc
        contradiction
  push_clkBound := by
    intro message messageMem
    rw [pushes_eq] at messageMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 1
        (by simp [ZMod.val_one]) (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
  ram_frame := by
    intro program state state' effect pulls cell value pushValues prior
    apply ramFrame_of_update effect (by rw [commit_eq]; rfl) pulls ?_ ?_ inCell update
      cell value pushValues prior
    · refine ⟨(ramPriorMessage access, StateMsg.timeNat rf.statePull), ?_,
        locOf_ramPriorMessage access isRam, rfl⟩
      rw [pulls_eq]
      exact List.mem_cons_self
    · refine ⟨ramPushMessage view access, ?_,
        locOf_ramPushMessage view access isRam, rfl⟩
      rw [pushes_eq]
      exact List.mem_cons_self

/-- Specialize the shared load wiring to an authenticated decoded-row interaction shape. -/
theorem rowWiring_loadRam_of_shape {chip : SupportedChip p}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq :
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite)
    (imm_c_eq : (decoded.toChipRow data).view.adapter.imm_c = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (unchanged :
      (shape.access decoded data).newValue = (shape.access decoded data).priorValue)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 (decoded.toChipRow data).view.rdWrite) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  refine rowWiring_loadRam bounds commit_eq imm_c_eq isRam unchanged opa_lt write_isU64
    rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
      consumedMemoryMessages_eq_of_loadShape shape decoded data hchip real]
    simp only [List.map_cons, List.map_nil, DecodedInstructionRow.ordinaryRowFacts_statePull]
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes,
      producedMemoryMessages_eq_of_loadShape shape decoded data hchip real]

/-- Specialize the shared LoadX0 wiring to an authenticated immutable RAM interaction shape. -/
theorem rowWiring_immutableLoadRam_of_shape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq :
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.noWrite)
    (imm_c_eq : (decoded.toChipRow data).view.adapter.imm_c = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (unchanged :
      (shape.access decoded data).newValue = (shape.access decoded data).priorValue)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  refine rowWiring_immutableLoadRam bounds commit_eq imm_c_eq isRam unchanged opa_lt
    rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
      consumedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real]
    simp only [List.map_cons, List.map_nil, DecodedInstructionRow.ordinaryRowFacts_statePull]
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes,
      producedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real]

/-- Specialize the shared genuine-store wiring to an authenticated decoded-row interaction shape. -/
theorem rowWiring_storeRam_of_shape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (write : Trace.MemWrite (ZMod p))
    (commit_eq :
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.store write)
    (imm_c_eq : (decoded.toChipRow data).view.adapter.imm_c = 1)
    (isRam : RamAccessIsRam (shape.access decoded data))
    (inCell : write.InCell (ramCellOfAccess (shape.access decoded data)))
    (update : RamCellUpdate write (ramCellOfAccess (shape.access decoded data))
      (Word.toBitVec64 (shape.access decoded data).priorValue)
      (Word.toBitVec64 (shape.access decoded data).newValue))
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : (decoded.toChipRow data).view.adapter.op_b[0].val < 32)
    (new_isU64 : Word.isU64 (shape.access decoded data).newValue) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  refine rowWiring_storeRam bounds commit_eq imm_c_eq isRam inCell update opa_lt opb_lt
    new_isU64 rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
      consumedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real]
    simp only [List.map_cons, List.map_nil, DecodedInstructionRow.ordinaryRowFacts_statePull]
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes,
      producedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real]

/-- The explicit witness-level high-timestamp premise specializes to the RAM prior message selected
by an authenticated normal-load shape. -/
theorem ramPrevHigh_lt_of_loadShape {chip : SupportedChip p}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (high : MemoryPullTimestampHighBound (decoded.ordinaryRowFacts data)) :
    (shape.access decoded data).prevHigh.val < 2 ^ 24 := by
  have member : (ramPriorMessage (shape.access decoded data),
      StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) ∈
      (decoded.ordinaryRowFacts data).memPulls := by
    rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
      consumedMemoryMessages_eq_of_loadShape shape decoded data hchip real]
    rw [DecodedInstructionRow.ordinaryRowFacts_statePull]
    exact List.mem_cons_self
  simpa only [ramPriorMessage] using high _ member

/-- Immutable RAM/I-type rows use the same first RAM pull and therefore the same specialization of
the explicit high-timestamp premise. -/
theorem ramPrevHigh_lt_of_immutableRamShape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (high : MemoryPullTimestampHighBound (decoded.ordinaryRowFacts data)) :
    (shape.access decoded data).prevHigh.val < 2 ^ 24 := by
  have member : (ramPriorMessage (shape.access decoded data),
      StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) ∈
      (decoded.ordinaryRowFacts data).memPulls := by
    rw [DecodedInstructionRow.ordinaryRowFacts_memPulls,
      consumedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real]
    rw [DecodedInstructionRow.ordinaryRowFacts_statePull]
    exact List.mem_cons_self
  simpa only [ramPriorMessage] using high _ member

/-- The three touches of a memory instruction in increasing effect-slot order: RAM at `+1`,
source B at `+3`, and the destination/source-A slot at `+4`. -/
def ramItypeTouches (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) (rf : Semantics.RowFacts p)
    (aPush : MemoryMsg (ZMod p)) : List (Touch p) :=
  [((ramPriorMessage access, StateMsg.timeNat rf.statePull),
      ramPushMessage view access),
   ((rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
       StateMsg.timeNat rf.statePull + 3),
      rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   ((rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
       StateMsg.timeNat rf.statePull), aPush)]

/-- Common aligned carrier for all nine Core memory chips.

The caller chooses the `+4` A-slot push (a destination write for ordinary loads, a read-back for
LoadX0/stores) and proves only its register location, time, and clock bound. The RAM and B-slot
facts are shared. -/
theorem rowAligned_ramItype {view : Trace.RowView (ZMod p)}
    {access : Trace.RamAccessView (ZMod p)} {rf : Semantics.RowFacts p}
    (aPush : MemoryMsg (ZMod p))
    (bounds : ViewClockBounds view)
    (_real : view.is_real = 1)
    (isRam : RamAccessIsRam access)
    (opa_lt : view.adapter.op_a.val < 32)
    (opb_lt : view.adapter.op_b[0].val < 32)
    (statePull_eq : rf.statePull = statePullOfView view)
    (pulls_eq : rf.memPulls =
      [(ramPriorMessage access, StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_perm :
      [ramPushMessage view access,
       rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3,
       aPush].Perm rf.memPushes)
    (aPushLoc : MemoryMsg.locOf aPush =
      MemLoc.reg (BitVec.ofNat 5 view.adapter.op_a.val))
    (aPushTime : MemoryMsg.timeNat aPush = StateMsg.timeNat rf.statePull + 4)
    (aPushClk : Channels.MemoryMsg.ClkBound aPush)
    (hslots : ∀ tc ∈ ramItypeTouches view access rf aPush,
      Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    AlignsWith (alignedOf rf (ramItypeTouches view access rf aPush)) rf ∧
      (∀ tc ∈ ramItypeTouches view access rf aPush,
        TouchOK (StateMsg.timeNat rf.statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((ramItypeTouches view access rf aPush).filter
          (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ ramItypeTouches view access rf aPush,
        Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ ramItypeTouches view access rf aPush,
        Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  have hidxA : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
      view.adapter.op_a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  have hidxB : ((BitVec.ofNat 5 view.adapter.op_b[0].val).toNat : ZMod p) =
      view.adapter.op_b[0] := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_b[0].val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  have hlocRamPrior := locOf_ramPriorMessage access isRam
  have hlocRamPush := locOf_ramPushMessage view access isRam
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
  have tr : MemoryMsg.timeNat (ramPushMessage view access) =
      StateMsg.timeNat rf.statePull + 1 := by
    rw [statePull_eq]
    exact timeNat_ramPushMessage bounds access
  have tb : MemoryMsg.timeNat
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3) =
      StateMsg.timeNat rf.statePull + 3 := by
    rw [statePull_eq]
    exact timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega)
  refine ⟨?_, ?_, ?_, ?_, hslots⟩
  · refine alignsWith_alignedOf_general rf (ramItypeTouches view access rf aPush)
      pushes_perm ?_ ?_ ?_
    · rw [pulls_eq]
      simp only [ramItypeTouches, List.map_cons, List.map_nil]
      exact List.Perm.cons _ (List.Perm.swap _ _ [])
    · intro mp hmp
      rw [pulls_eq] at hmp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
      rcases hmp with rfl | rfl | rfl <;> rfl
    · intro mp hmp
      rw [pulls_eq] at hmp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
      rcases hmp with rfl | rfl | rfl
      · refine ⟨_, List.mem_cons_self, rfl, ?_, ?_⟩
        · exact le_rfl
        · dsimp only
          rw [hlocRamPrior, readWindow_ram]
          simp only [Nat.add_zero]
          exact Nat.le_refl _
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          rfl, ?_, ?_⟩
        · exact le_rfl
        · dsimp only
          rw [hlocPriorA, readWindow_reg]
          omega
      · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, ?_, ?_⟩
        · dsimp only
          omega
        · dsimp only
          rw [hlocPriorB, readWindow_reg]
  · intro tc htc
    simp only [ramItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · refine ⟨?_, ?_, ?_, Or.inr ?_⟩
      · dsimp only
        rw [hlocRamPush, hlocRamPrior]
      · exact le_rfl
      · dsimp only
        rw [hlocRamPrior, readWindow_ram]
        simp only [Nat.add_zero]
        exact Nat.le_refl _
      · dsimp only
        rw [tr, hlocRamPush, writeOffset_ram]
    · refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, tb⟩⟩
      · dsimp only
        rw [hlocReadB, hlocPriorB]
      · dsimp only
        omega
      · dsimp only
        rw [hlocPriorB, readWindow_reg]
    · refine ⟨?_, ?_, ?_, Or.inr ?_⟩
      · dsimp only
        rw [aPushLoc, hlocPriorA]
      · exact le_rfl
      · dsimp only
        rw [hlocPriorA, readWindow_reg]
        omega
      · dsimp only
        rw [aPushTime, aPushLoc, writeOffset_reg]
  · have hpair : List.Pairwise
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        (ramItypeTouches view access rf aPush) := by
      simp only [ramItypeTouches]
      refine List.Pairwise.cons ?_
        (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · dsimp only
          rw [tr, tb]
          omega
        · dsimp only
          rw [tr, aPushTime]
          omega
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl
        dsimp only
        rw [tb, aPushTime]
        omega
      · intro x hx
        simp only [List.not_mem_nil] at hx
    intro loc
    exact (List.Pairwise.sublist List.filter_sublist hpair).isChain
  · intro tc htc
    simp only [ramItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 1
        (by simp [ZMod.val_one]) (by omega) bounds.clk0 bounds.clk1
    · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 3 val_3_zmod_p
        (by omega) bounds.clk0 bounds.clk1
    · exact aPushClk

/-- The three independent timestamp facts used by a normal load: its generic RAM reader and the
destination/source-B register readers. -/
def LoadMemoryTimestampBounds (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) : Prop :=
  ActiveMemoryTimestampFacts access.compareLow access.prevHigh access.prevLow
      access.diffLow access.diffHigh view.state.clk_high
      (view.state.clk_0_16 + view.state.clk_16_24 * 65536) ∧
    ITypeTimestampBounds view

/-- LoadX0 and stores use the same scalar timestamp facts; their I-type reader merely re-posts A
instead of committing a destination write. -/
abbrev ImmutableRamTimestampBounds (view : Trace.RowView (ZMod p))
    (access : Trace.RamAccessView (ZMod p)) : Prop :=
  LoadMemoryTimestampBounds view access

/-- Combine the retained RAM reader and ordinary I-type reader contracts into the timestamp
surface consumed by normal load rows. -/
theorem loadMemoryTimestampBounds_of_contracts {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (access : Input (ZMod p) → Output (ZMod p) → Trace.RamAccessView (ZMod p))
    (ramContract : CircuitRamAccessTimestampContract circuit view
      (fun input output => some (access input output)))
    (itypeContract : CircuitITypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    LoadMemoryTimestampBounds
      (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput
          (Environment.fromArray physical data)))
      (access ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput
          (Environment.fromArray physical data))) := by
  constructor
  · exact ramAccessTimestampFacts_of_contract circuit view
      (fun input output => some (access input output)) ramContract data physical
      constraints guarantees _ rfl real
  · exact itypeTimestampBounds_of_contract circuit view itypeContract data physical
      guarantees real

/-- Immutable I-type twin of `loadMemoryTimestampBounds_of_contracts`, used by `LoadX0` and all
four stores. -/
theorem immutableRamTimestampBounds_of_contracts {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (access : Input (ZMod p) → Output (ZMod p) → Trace.RamAccessView (ZMod p))
    (ramContract : CircuitRamAccessTimestampContract circuit view
      (fun input output => some (access input output)))
    (itypeContract : CircuitImmutableITypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    ImmutableRamTimestampBounds
      (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput
          (Environment.fromArray physical data)))
      (access ((⟨circuit⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray physical data))
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput
          (Environment.fromArray physical data))) := by
  constructor
  · exact ramAccessTimestampFacts_of_contract circuit view
      (fun input output => some (access input output)) ramContract data physical
      constraints guarantees _ rfl real
  · exact immutableItypeTimestampBounds_of_contract circuit view itypeContract data physical
      guarantees real

/-- Construct the aligned timed carrier of any exact normal-load row. -/
theorem rowAligned_loadRam_of_shape {chip : SupportedChip p}
    (shape : LoadMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestamps : LoadMemoryTimestampBounds (decoded.toChipRow data).view
      (shape.access decoded data))
    (isRam : RamAccessIsRam (shape.access decoded data))
    (ramHighBound : (shape.access decoded data).prevHigh.val < 2 ^ 24)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : (decoded.toChipRow data).view.adapter.op_b[0].val < 32) :
    AlignsWith
        (alignedOf (decoded.ordinaryRowFacts data)
          (ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
            (decoded.ordinaryRowFacts data)
            (rtypeWriteMessage (decoded.toChipRow data).view)))
        (decoded.ordinaryRowFacts data) ∧
      (∀ tc ∈ ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeWriteMessage (decoded.toChipRow data).view),
        TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeWriteMessage (decoded.toChipRow data).view)).filter
            (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeWriteMessage (decoded.toChipRow data).view),
        Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeWriteMessage (decoded.toChipRow data).view),
        Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  let view := (decoded.toChipRow data).view
  let access := shape.access decoded data
  let rf := decoded.ordinaryRowFacts data
  have consumed := consumedMemoryMessages_eq_of_loadShape shape decoded data hchip real
  have produced := producedMemoryMessages_eq_of_loadShape shape decoded data hchip real
  obtain ⟨ramTimestamp, timestampA, timestampB⟩ := timestamps
  have hslots : ∀ tc ∈ ramItypeTouches view access rf (rtypeWriteMessage view),
      Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
    intro tc htc hclk
    simp only [ramItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · exact memoryTimeNat_lt_of_memoryAccessFacts
        (ramPriorMessage access) (ramPushMessage view access)
        access.compareLow access.prevHigh access.prevLow access.diffLow access.diffHigh
        view.state.clk_high
        (view.state.clk_0_16 + view.state.clk_16_24 * 65536)
        hclk ramHighBound ramTimestamp rfl rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampB rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampA rfl rfl rfl
  have hidxA : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
      view.adapter.op_a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  refine rowAligned_ramItype (rtypeWriteMessage view) bounds real isRam opa_lt opb_lt
    rfl ?_ ?_ (MemoryMsg.locOf_register _ _ hidxA rfl rfl) ?_ ?_ hslots
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]
  · exact timeNat_rtypeWriteMessage bounds
  · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
      (by omega) bounds.clk0 bounds.clk1

/-- Construct the aligned timed carrier shared by LoadX0 and the four stores. -/
theorem rowAligned_immutableRam_of_shape {chip : SupportedChip p}
    (shape : ImmutableRamMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestamps : ImmutableRamTimestampBounds (decoded.toChipRow data).view
      (shape.access decoded data))
    (isRam : RamAccessIsRam (shape.access decoded data))
    (ramHighBound : (shape.access decoded data).prevHigh.val < 2 ^ 24)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : (decoded.toChipRow data).view.adapter.op_b[0].val < 32) :
    AlignsWith
        (alignedOf (decoded.ordinaryRowFacts data)
          (ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
            (decoded.ordinaryRowFacts data)
            (rtypeReadBackMessage (decoded.toChipRow data).view
              (decoded.toChipRow data).view.adapter.op_a
              (decoded.toChipRow data).view.adapter.op_a_memory 4)))
        (decoded.ordinaryRowFacts data) ∧
      (∀ tc ∈ ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeReadBackMessage (decoded.toChipRow data).view
            (decoded.toChipRow data).view.adapter.op_a
            (decoded.toChipRow data).view.adapter.op_a_memory 4),
        TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
      (∀ loc : MemLoc, List.IsChain
        (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
        ((ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeReadBackMessage (decoded.toChipRow data).view
            (decoded.toChipRow data).view.adapter.op_a
            (decoded.toChipRow data).view.adapter.op_a_memory 4)).filter
              (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
      (∀ tc ∈ ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeReadBackMessage (decoded.toChipRow data).view
            (decoded.toChipRow data).view.adapter.op_a
            (decoded.toChipRow data).view.adapter.op_a_memory 4),
        Channels.MemoryMsg.ClkBound tc.2) ∧
      (∀ tc ∈ ramItypeTouches (decoded.toChipRow data).view (shape.access decoded data)
          (decoded.ordinaryRowFacts data)
          (rtypeReadBackMessage (decoded.toChipRow data).view
            (decoded.toChipRow data).view.adapter.op_a
            (decoded.toChipRow data).view.adapter.op_a_memory 4),
        Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  let view := (decoded.toChipRow data).view
  let access := shape.access decoded data
  let rf := decoded.ordinaryRowFacts data
  let aPush := rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4
  have consumed := consumedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real
  have produced := producedMemoryMessages_eq_of_immutableRamShape shape decoded data hchip real
  obtain ⟨ramTimestamp, timestampA, timestampB⟩ := timestamps
  have hslots : ∀ tc ∈ ramItypeTouches view access rf aPush,
      Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
        MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
    intro tc htc hclk
    simp only [ramItypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
    rcases htc with rfl | rfl | rfl
    · exact memoryTimeNat_lt_of_memoryAccessFacts
        (ramPriorMessage access) (ramPushMessage view access)
        access.compareLow access.prevHigh access.prevLow access.diffLow access.diffHigh
        view.state.clk_high
        (view.state.clk_0_16 + view.state.clk_16_24 * 65536)
        hclk ramHighBound ramTimestamp rfl rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampB rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
        _ _ _ _ _ hclk timestampA rfl rfl rfl
  have hidxA : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
      view.adapter.op_a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
    exact ZMod.natCast_zmod_val _
  refine rowAligned_ramItype aPush bounds real isRam opa_lt opb_lt rfl ?_ ?_
    (MemoryMsg.locOf_register _ _ hidxA rfl rfl) ?_ ?_ hslots
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes, produced]
    exact List.Perm.cons _ (List.Perm.swap _ _ [])
  · exact timeNat_rtypeReadBackMessage bounds _ _ val_4_zmod_p (by omega)
  · exact Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ 4 val_4_zmod_p
      (by omega) bounds.clk0 bounds.clk1

/-! ## Concrete Memory interaction shapes -/

/-! ### Per-chip boilerplate macros

The nine memory chips below instantiate the same generic transports, so their proof *bodies* are
byte-identical modulo the chip's name. Each macro takes the descriptor root (`loadByte`,
`storeWord`, …) and derives the `…ChipDescriptor_table` / `…Chip_viewOf_decoded` / `…Chip_*_env`
lemma names from it; the irregular LoadByte lemmas (`loadByteViewOf_decoded` and friends, named
before the `…Chip_` convention settled) keep their spelled-out bodies. Macros are not
declarations, so no statement, name, or axiom set moves. -/

/-- Rewrite a chip descriptor's component-level `Assumptions` to its folded row-input form. -/
local macro "chipAssumptionsIff " r:ident : tactic => do
  let tbl := Lean.mkIdent (.mkSimple (r.getId.toString ++ "ChipDescriptor_table"))
  `(tactic|
    (rw [$tbl:ident]
     unfold Component.Assumptions
     rw [$(Lean.mkIdent `circuitRowInputOf_eq_component):ident]
     rfl))

/-- Discharge an interaction-shape bundle's `access_eq` field at a literal chip descriptor. -/
local macro "chipShapeAccessEq" : tactic =>
  `(tactic|
    (intro decoded data hchip
     obtain ⟨chip, physical⟩ := decoded
     have hchip' : chip = _ := hchip
     subst hchip'
     rfl))

/-- Transport a chip's environment-level `ViewClockBounds` to the decoded-row boundary. -/
local macro "chipViewClockBounds " r:ident : tactic => do
  let s := r.getId.toString
  let tbl := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_table"))
  let vof := Lean.mkIdent (.mkSimple (s ++ "Chip_viewOf_decoded"))
  let bounds := Lean.mkIdent (.mkSimple (s ++ "Chip_viewClockBounds_env"))
  let (decoded, data) := (Lean.mkIdent `decoded, Lean.mkIdent `data)
  let (hchip, guarantees, real) :=
    (Lean.mkIdent `hchip, Lean.mkIdent `guarantees, Lean.mkIdent `real)
  `(tactic|
    (obtain ⟨chip, physical⟩ := $decoded
     have hchip' : chip = _ := $hchip
     subst hchip'
     rw [$tbl:ident] at $guarantees:ident
     rw [$vof:ident] at $real:ident ⊢
     exact $bounds:ident $data physical $guarantees $real))

/-- Transport a chip's environment-level memory timestamp bounds to the decoded-row boundary. -/
local macro "chipTimestampBounds " r:ident : tactic => do
  let s := r.getId.toString
  let tbl := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_table"))
  let vof := Lean.mkIdent (.mkSimple (s ++ "Chip_viewOf_decoded"))
  let raof := Lean.mkIdent (.mkSimple (s ++ "Chip_ramAccessOf_decoded"))
  let bounds := Lean.mkIdent (.mkSimple (s ++ "Chip_timestampBounds_env"))
  let (decoded, data, hchip) := (Lean.mkIdent `decoded, Lean.mkIdent `data, Lean.mkIdent `hchip)
  let (constraints, guarantees, real) :=
    (Lean.mkIdent `constraints, Lean.mkIdent `guarantees, Lean.mkIdent `real)
  `(tactic|
    (obtain ⟨chip, physical⟩ := $decoded
     have hchip' : chip = _ := $hchip
     subst hchip'
     rw [$tbl:ident] at $constraints:ident $guarantees:ident
     rw [$vof:ident] at $real:ident ⊢
     rw [$raof:ident]
     exact $bounds:ident $data physical $constraints $guarantees $real))

/-- Transport a chip's environment-level `RamAccessIsRam` to the decoded-row boundary. -/
local macro "chipIsRam " r:ident : tactic => do
  let s := r.getId.toString
  let tbl := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_table"))
  let vof := Lean.mkIdent (.mkSimple (s ++ "Chip_viewOf_decoded"))
  let raof := Lean.mkIdent (.mkSimple (s ++ "Chip_ramAccessOf_decoded"))
  let isRam := Lean.mkIdent (.mkSimple (s ++ "Chip_isRam_env"))
  let (decoded, data, hchip) := (Lean.mkIdent `decoded, Lean.mkIdent `data, Lean.mkIdent `hchip)
  let (constraints, real) := (Lean.mkIdent `constraints, Lean.mkIdent `real)
  `(tactic|
    (obtain ⟨chip, physical⟩ := $decoded
     have hchip' : chip = _ := $hchip
     subst hchip'
     rw [$tbl:ident] at $constraints:ident
     rw [$vof:ident] at $real:ident
     rw [$raof:ident]
     exact $isRam:ident $data physical $constraints $real))

/-- Fold a decoded row's view down to the chip's opaque `circuitRowViewOf` projection. -/
local macro "chipViewOfDecoded " r:ident : tactic => do
  let s := r.getId.toString
  let tbl := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_table"))
  let vw := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_view"))
  `(tactic|
    (rw [DecodedInstructionRow.toChipRow_view]
     simp only [$tbl:ident, $vw:ident]
     unfold $(Lean.mkIdent `circuitRowViewOf):ident
     rfl))

/-- RAM companion of `chipViewOfDecoded`. -/
local macro "chipRamAccessOfDecoded " r:ident : tactic => do
  let s := r.getId.toString
  let tbl := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_table"))
  let ra := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_ramAccess"))
  `(tactic|
    (unfold $(Lean.mkIdent `decodedRamAccess):ident
     rw [DecodedInstructionRow.toChipRow_ramAccess]
     simp only [$tbl:ident, $ra:ident, Option.getD_some]
     unfold $(Lean.mkIdent `circuitRamAccessOf):ident
     rfl))

/-- Read a chip's `ViewClockBounds` off its retained CPU-state time contract. -/
local macro "chipViewClockBoundsEnv " r:ident : tactic => do
  let s := r.getId.toString
  let ns := Lean.Name.mkSimple (s.capitalize ++ "Chip")
  let (circ, rv) := (Lean.mkIdent (ns ++ `circuit), Lean.mkIdent (ns ++ `rowView))
  let contract := Lean.mkIdent (ns ++ `cpuStateTimeContract)
  let (data, physical) := (Lean.mkIdent `data, Lean.mkIdent `physical)
  let (guarantees, real) := (Lean.mkIdent `guarantees, Lean.mkIdent `real)
  `(tactic|
    (rw [$(Lean.mkIdent `circuitRowViewOf_eq):ident] at $real:ident ⊢
     exact viewClockBounds_of_cpuStateContract $circ $rv $contract $data $physical
       $guarantees $real))

/-- Read a chip's `RamAccessIsRam` off its retained address contract; `sel` is the chip's
`is_real` selector, spelled either as a named projection or as an explicit lambda. -/
local macro "chipIsRamEnv " r:ident sel:term : tactic => do
  let s := r.getId.toString
  let ns := Lean.Name.mkSimple (s.capitalize ++ "Chip")
  let (circ, rv) := (Lean.mkIdent (ns ++ `circuit), Lean.mkIdent (ns ++ `rowView))
  let rav := Lean.mkIdent (ns ++ `ramAccessView)
  let contract := Lean.mkIdent (ns ++ `ramAddressContract)
  let (data, physical) := (Lean.mkIdent `data, Lean.mkIdent `physical)
  let (constraints, real) := (Lean.mkIdent `constraints, Lean.mkIdent `real)
  `(tactic|
    (rw [$(Lean.mkIdent `circuitRowViewOf_eq):ident] at $real:ident
     rw [$(Lean.mkIdent `circuitRamAccessOf_eq):ident]
     exact ramAccessIsRam_of_addressContract $circ
       (fun input cols => some ($rav input cols))
       $sel $contract $data $physical $constraints
       (by simpa only [$rv:ident] using $real) _ rfl))

/-- Discharge a normal load's `Assumptions` from its folded base/immediate/RAM premises. -/
local macro "chipLoadAssumptionsEnv " r:ident : tactic => do
  let s := r.getId.toString
  let ns := Lean.Name.mkSimple (s.capitalize ++ "Chip")
  let (assumptions, rv) := (Lean.mkIdent (ns ++ `Assumptions), Lean.mkIdent (ns ++ `rowView))
  let rav := Lean.mkIdent (ns ++ `ramAccessView)
  let opB := Lean.mkIdent (ns ++ `Inputs ++ `op_b_val)
  let opC := Lean.mkIdent (ns ++ `Inputs ++ `op_c_imm)
  let (base, immediate, ram) :=
    (Lean.mkIdent `base, Lean.mkIdent `immediate, Lean.mkIdent `ram)
  `(tactic|
    (rw [$(Lean.mkIdent `circuitRowViewOf_eq_typed):ident] at $base:ident $immediate:ident
     rw [$(Lean.mkIdent `circuitRamAccessOf_eq_typed):ident] at $ram:ident
     unfold $assumptions:ident
     refine ⟨?_, ?_, ?_⟩
     · simpa only [$opB:ident, $rv:ident, Extracted.ITypeReader.toAdapterView] using $base
     · simpa only [$opC:ident, $rv:ident, Extracted.ITypeReader.toAdapterView] using $immediate
     · simpa only [$rav:ident] using $ram))

/-- Peel a chip's exposed Memory interaction list down to `layout`'s message constructors. The
per-chip closing `simp only` over the message projections stays at the call site: its lemma list
is what differs between the register-writing loads, `LoadX0`, and the stores. -/
local macro "chipMemoryValues " r:ident layout:ident : tactic => do
  let s := r.getId.toString
  let ns := Lean.Name.mkSimple (s.capitalize ++ "Chip")
  let inputs := Lean.mkIdent (ns ++ `Inputs)
  let (main, iwm) :=
    (Lean.mkIdent (ns ++ `main), Lean.mkIdent (ns ++ `interactionsWith_memory_eq))
  let emi := Lean.mkIdent (ns ++ `exposedMemoryInteractions)
  let env := Lean.mkIdent `env
  `(tactic|
    (rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
     change List.map (AbstractInteraction.eval $env)
         ((($main (varFromOffset $inputs 0)).operations
           (size $inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
     rw [$iwm:ident]
     simp only [$emi:ident, $layout:ident, List.map_cons, List.map_nil,
       TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
       Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]))

/-- Lift a chip's evaluated Memory list to the folded decoded-row boundary against `layout`. -/
local macro "chipTypedMemoryInteractions " r:ident layout:ident : tactic => do
  let s := r.getId.toString
  let ns := Lean.Name.mkSimple (s.capitalize ++ "Chip")
  let (circ, inputs) := (Lean.mkIdent (ns ++ `circuit), Lean.mkIdent (ns ++ `Inputs))
  let desc := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor"))
  let tbl := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_table"))
  let vw := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_view"))
  let ra := Lean.mkIdent (.mkSimple (s ++ "ChipDescriptor_ramAccess"))
  let values := Lean.mkIdent (.mkSimple (s ++ "Chip_memoryInteractionValues_eq"))
  let (decoded, data, hchip) := (Lean.mkIdent `decoded, Lean.mkIdent `data, Lean.mkIdent `hchip)
  `(tactic|
    (apply $(Lean.mkIdent `typedMemoryInteractions_of_values):ident $desc $layout ?_
       $decoded $data $hchip
     intro env
     have inputEq : Eval.eval env (varFromOffset $inputs 0) =
         (⟨$circ (p := p)⟩ : Component (ZMod p)).rowInput env :=
       eval_varFromOffset_valueFromOffset $inputs 0 env
     have outputEq : Eval.eval env
         (($circ (p := p)).output (varFromOffset $inputs 0) (size $inputs)) =
         (⟨$circ (p := p)⟩ : Component (ZMod p)).rowOutput env := by
       simp only [Component.rowOutput, circuit_norm]
     simp only [$tbl:ident, $vw:ident, $ra:ident, Option.getD_some]
     rw [← inputEq, ← outputEq]
     exact $values:ident env))

section LoadByte

/-- The LoadByte descriptor in the supported Core registry. -/
def loadByteChipDescriptor : SupportedChip p :=
  ⟨LoadByteChip.kind, LoadByteChip.circuit, rfl, [.LB, .LBU], .nonX0⟩

/-- Small descriptor projections kept symbolic so decoded-row proofs never normalize the full
dependent component merely to identify its circuit, row view, or RAM access. -/
theorem loadByteChipDescriptor_table :
    (loadByteChipDescriptor (p := p)).table =
      (⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadByteChipDescriptor_rdGuard :
    (loadByteChipDescriptor (p := p)).rdGuard = .nonX0 := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadByteChipDescriptor_view (input : LoadByteChip.Inputs (ZMod p))
    (output : LoadByteChip.Columns (ZMod p)) :
    (loadByteChipDescriptor (p := p)).kind.view input output =
      LoadByteChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadByteChipDescriptor_ramAccess (input : LoadByteChip.Inputs (ZMod p))
    (output : LoadByteChip.Columns (ZMod p)) :
    (loadByteChipDescriptor (p := p)).kind.ramAccess input output =
      some (LoadByteChip.ramAccessView input output) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadByteChipDescriptor_chipSpec
    (input : LoadByteChip.Inputs (ZMod p))
    (output : LoadByteChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    (loadByteChipDescriptor (p := p)).kind.chipSpec input output data =
      LoadByteChip.Spec input output data := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadByteChipDescriptor_advanceReady
    (input : LoadByteChip.Inputs (ZMod p))
    (output : LoadByteChip.Columns (ZMod p))
    (program : GuestProgram) (state : SailState) :
    (loadByteChipDescriptor (p := p)).kind.advanceReady input output program state =
      LoadByteChip.AdvanceReady input output program state := rfl

/-- An inert default used only to totalize the descriptor-independent shape projection. Concrete
memory descriptors immediately rewrite their registered projection to `some`; no theorem treats
this value as an authenticated RAM access. -/
def zeroRamAccess : Trace.RamAccessView (ZMod p) :=
  ⟨0, 0, 0, 0, 0, #v[0, 0, 0], #v[0, 0, 0, 0], #v[0, 0, 0, 0]⟩

noncomputable def decodedRamAccess (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : Trace.RamAccessView (ZMod p) :=
  (decoded.toChipRow data).ramAccess.getD zeroRamAccess

/-- Opaque typed input of a completed circuit. This is the safe projection boundary for facts that
depend only on the committed input: its explicit result type prevents `whnf` from normalizing the
completed output merely to discover a field of the input. -/
@[irreducible] noncomputable def circuitRowInputOf {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (env : Environment (ZMod p)) : Input (ZMod p) :=
  (⟨circuit⟩ : Component (ZMod p)).rowInput env

/-- Opaque typed output paired with `circuitRowInputOf`. -/
@[irreducible] noncomputable def circuitRowOutputOf {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (env : Environment (ZMod p)) : Output (ZMod p) :=
  (⟨circuit⟩ : Component (ZMod p)).rowOutput env

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem circuitRowInputOf_eq_component {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (env : Environment (ZMod p)) :
    circuitRowInputOf circuit env =
      (⟨circuit⟩ : Component (ZMod p)).rowInput env := by
  unfold circuitRowInputOf
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem circuitRowOutputOf_eq_component {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (env : Environment (ZMod p)) :
    circuitRowOutputOf circuit env =
      (⟨circuit⟩ : Component (ZMod p)).rowOutput env := by
  unfold circuitRowOutputOf
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem circuitRowInputOf_eq_eval {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (env : Environment (ZMod p)) :
    circuitRowInputOf circuit env =
      Eval.eval env (varFromOffset (F := ZMod p) Input 0) := by
  rw [circuitRowInputOf_eq_component]
  exact (eval_varFromOffset_valueFromOffset Input 0 env).symm

/-- Transport a semantic row fact from a literal supported-chip descriptor to the opaque typed
input/output projections. Keeping `kind` and `circuit` as variables prevents dependent unification
from reducing a completed concrete circuit. -/
theorem chipSpec_of_literalDescriptor
    (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (specEq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((⟨kind, circuit, specEq, opcodes, rdGuard⟩ : SupportedChip p).decodeRow
      data physical).chipSpec data) :
    kind.chipSpec
      (@circuitRowInputOf p inferInstance kind.Inputs kind.Cols
        kind.provableInputs kind.provableCols circuit
        (Environment.fromArray physical data))
      (@circuitRowOutputOf p inferInstance kind.Inputs kind.Cols
        kind.provableInputs kind.provableCols circuit
        (Environment.fromArray physical data))
      data := by
  letI : ProvableType kind.Inputs := kind.provableInputs
  letI : ProvableType kind.Cols := kind.provableCols
  rw [circuitRowInputOf_eq_component, circuitRowOutputOf_eq_component]
  exact h

/-- `advanceReady` companion to `chipSpec_of_literalDescriptor`. -/
theorem advanceReady_of_literalDescriptor
    (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (specEq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (opcodes : List Opcode) (rdGuard : RdGuard)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : kind.advanceReady
      (@circuitRowInputOf p inferInstance kind.Inputs kind.Cols
        kind.provableInputs kind.provableCols circuit
        (Environment.fromArray physical data))
      (@circuitRowOutputOf p inferInstance kind.Inputs kind.Cols
        kind.provableInputs kind.provableCols circuit
        (Environment.fromArray physical data))
      program state) :
    ((⟨kind, circuit, specEq, opcodes, rdGuard⟩ : SupportedChip p).decodeRow
      data physical).kind.advanceReady
      ((⟨kind, circuit, specEq, opcodes, rdGuard⟩ : SupportedChip p).decodeRow
        data physical).inputs
      ((⟨kind, circuit, specEq, opcodes, rdGuard⟩ : SupportedChip p).decodeRow
        data physical).cols
      program state := by
  letI : ProvableType kind.Inputs := kind.provableInputs
  letI : ProvableType kind.Cols := kind.provableCols
  rw [circuitRowInputOf_eq_component, circuitRowOutputOf_eq_component] at h
  exact h

theorem loadByteChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (loadByteChipDescriptor (p := p)).table.Assumptions env ↔
      LoadByteChip.Assumptions
        (circuitRowInputOf LoadByteChip.circuit env) env.data := by
  chipAssumptionsIff loadByte

/-- Opaque evaluation spelling shared by concrete memory chips. Keeping a completed chip's output
folded is essential at the dependent decoder boundary: unification must not normalize the whole
`GeneralFormalCircuit` merely to compare two row-view expressions. -/
@[irreducible] noncomputable def circuitRowViewOf {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  view ((⟨circuit⟩ : Component (ZMod p)).rowInput env)
    ((⟨circuit⟩ : Component (ZMod p)).rowOutput env)

/-- Opaque evaluated RAM projection paired with `circuitRowViewOf`. -/
@[irreducible] noncomputable def circuitRamAccessOf {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (access : Input (ZMod p) → Output (ZMod p) → Trace.RamAccessView (ZMod p))
    (env : Environment (ZMod p)) : Trace.RamAccessView (ZMod p) :=
  access ((⟨circuit⟩ : Component (ZMod p)).rowInput env)
    ((⟨circuit⟩ : Component (ZMod p)).rowOutput env)

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem circuitRowViewOf_eq {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (env : Environment (ZMod p)) :
    circuitRowViewOf circuit view env =
      view ((⟨circuit⟩ : Component (ZMod p)).rowInput env)
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput env) := by
  unfold circuitRowViewOf
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
theorem circuitRamAccessOf_eq {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (access : Input (ZMod p) → Output (ZMod p) → Trace.RamAccessView (ZMod p))
    (env : Environment (ZMod p)) :
    circuitRamAccessOf circuit access env =
      access ((⟨circuit⟩ : Component (ZMod p)).rowInput env)
        ((⟨circuit⟩ : Component (ZMod p)).rowOutput env) := by
  unfold circuitRamAccessOf
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- Rewrite a folded row view to the opaque typed input/output projections without exposing the
completed circuit. -/
theorem circuitRowViewOf_eq_typed {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (env : Environment (ZMod p)) :
    circuitRowViewOf circuit view env =
      view (circuitRowInputOf circuit env) (circuitRowOutputOf circuit env) := by
  rw [circuitRowViewOf_eq, circuitRowInputOf_eq_component, circuitRowOutputOf_eq_component]

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- RAM-access companion to `circuitRowViewOf_eq_typed`. -/
theorem circuitRamAccessOf_eq_typed {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (access : Input (ZMod p) → Output (ZMod p) → Trace.RamAccessView (ZMod p))
    (env : Environment (ZMod p)) :
    circuitRamAccessOf circuit access env =
      access (circuitRowInputOf circuit env) (circuitRowOutputOf circuit env) := by
  rw [circuitRamAccessOf_eq, circuitRowInputOf_eq_component, circuitRowOutputOf_eq_component]

/-! ### LoadByte's retained circuit contracts -/

omit [Fact (2 ^ 25 < p)] in
/-- LoadByte retains the generic RAM timestamp reader immediately after its four-cell address
operation. -/
theorem LoadByteChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (LoadByteChip.circuit (p := p))
      LoadByteChip.rowView
      (fun input cols => some (LoadByteChip.ramAccessView input cols)) := by
  let input : Var LoadByteChip.Inputs (ZMod p) := varFromOffset LoadByteChip.Inputs 0
  let offset := size LoadByteChip.Inputs
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], input.is_lb + input.is_lbu⟩
        ((AddressOperation.circuit (p := p)).output
          ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
            input.offset_bit[2], input.is_lb + input.is_lbu⟩ offset))[0],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], input.is_lb + input.is_lbu⟩
        ((AddressOperation.circuit (p := p)).output
          ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
            input.offset_bit[2], input.is_lb + input.is_lbu⟩ offset))[1],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], input.is_lb + input.is_lbu⟩
        ((AddressOperation.circuit (p := p)).output
          ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
            input.offset_bit[2], input.is_lb + input.is_lbu⟩ offset))[2],
      input.memory_access.prev_value, input.is_lb + input.is_lbu⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, LoadByteChip.circuit, LoadByteChip.main,
      Readers.MemoryAccess.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, LoadByteChip.circuit, LoadByteChip.rowView,
        LoadByteChip.ramAccessView, LoadByteChip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- LoadByte's public RAM address is the output of its retained address operation. -/
theorem LoadByteChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (LoadByteChip.circuit (p := p))
      (fun input cols => some (LoadByteChip.ramAccessView input cols))
      LoadByteChip.isReal := by
  let input : Var LoadByteChip.Inputs (ZMod p) := varFromOffset LoadByteChip.Inputs 0
  let offset := size LoadByteChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], input.is_lb + input.is_lbu⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, LoadByteChip.circuit, LoadByteChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, LoadByteChip.circuit,
      LoadByteChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, LoadByteChip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- LoadByte retains the ordinary I-type register timestamp reader at the same zero-output
boundary as its RAM reader. -/
theorem LoadByteChip.itypeTimestampContract :
    CircuitITypeTimestampContract (p := p) (LoadByteChip.circuit (p := p))
      LoadByteChip.rowView := by
  let input : Var LoadByteChip.Inputs (ZMod p) := varFromOffset LoadByteChip.Inputs 0
  let offset := size LoadByteChip.Inputs
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_lb + input.is_lbu, input.is_lb + input.is_lbu,
      input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.is_lb * 29 + input.is_lbu * 32,
      input.selected_byte + 65280 * input.msb, 65535 * input.msb,
      65535 * input.msb, 65535 * input.msb⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, LoadByteChip.circuit, LoadByteChip.main,
      Readers.ITypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, LoadByteChip.rowView, LoadByteChip.isReal,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

/-- Opaque row-view spelling used at LoadByte's dependent decoder boundary. Keeping this value
folded prevents descriptor rewriting from normalizing the completed chip output. -/
@[irreducible] noncomputable def loadByteViewOf (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  LoadByteChip.rowView
    (circuitRowInputOf LoadByteChip.circuit env)
    (circuitRowOutputOf LoadByteChip.circuit env)

/-- Opaque RAM-view spelling paired with `loadByteViewOf`. -/
@[irreducible] noncomputable def loadByteRamAccessOf (env : Environment (ZMod p)) :
    Trace.RamAccessView (ZMod p) :=
  LoadByteChip.ramAccessView
    (circuitRowInputOf LoadByteChip.circuit env)
    (circuitRowOutputOf LoadByteChip.circuit env)

omit [Fact (2 ^ 25 < p)] in
/-- Assemble LoadByte's concrete circuit assumptions from the three grounded 64-bit words while
the completed circuit input remains opaque. -/
theorem loadByteAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64 (loadByteViewOf env).adapter.op_b_memory.prev_value)
    (immediate : Word.isU64 (loadByteViewOf env).adapter.op_c)
    (ram : Word.isU64 (loadByteRamAccessOf env).priorValue) :
    LoadByteChip.Assumptions
      (circuitRowInputOf LoadByteChip.circuit env) data := by
  unfold LoadByteChip.Assumptions
  constructor
  · simpa only [LoadByteChip.Inputs.op_b_val, loadByteViewOf,
      LoadByteChip.rowView, Extracted.ITypeReader.toAdapterView] using base
  constructor
  · simpa only [LoadByteChip.Inputs.op_c_imm, loadByteViewOf,
      LoadByteChip.rowView, Extracted.ITypeReader.toAdapterView] using immediate
  · simpa only [loadByteRamAccessOf, LoadByteChip.ramAccessView] using ram

omit [Fact (2 ^ 25 < p)] in
/-- LoadByte's limb and byte mux selects exactly the byte indexed by its authenticated address
offset. This is the arithmetic seam between the whole-chip contract and Sail's byte memory. -/
theorem loadByte_selectedMemoryByte
    (input : LoadByteChip.Inputs (ZMod p))
    (cols : LoadByteChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadByteChip.Spec input cols data)
    (real : LoadByteChip.isReal input = 1)
    (priorBound : Word.isU64 input.memory_access.prev_value) :
    ∃ i : Fin 8,
      i.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
          input.offset_bit[1], input.offset_bit[2], LoadByteChip.isReal input⟩ ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i] =
        BitVec.ofNat 8 input.selected_byte.val := by
  obtain ⟨address, _memory, _reader, byteBounds, _msb, limbSelect, mux,
    _route, _unsigned, _lbBinary, _lbuBinary, _realBinary⟩ := spec
  obtain ⟨lowBound, highBound, _selectedBound⟩ := byteBounds real
  have decomposed := U16toU8OperationSafe.reassemble
    input.selected_limb input.selected_limb_low_byte
  have lowByte := lowByte_eq lowBound highBound decomposed
  have highByte := highByte_eq lowBound highBound decomposed
  have selectedZero
      (bitOne : input.offset_bit[1] = 0)
      (bitTwo : input.offset_bit[2] = 0) :
      input.selected_limb = input.memory_access.prev_value[0] := by
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.1
  have selectedOne
      (bitOne : input.offset_bit[1] = 1)
      (bitTwo : input.offset_bit[2] = 0) :
      input.selected_limb = input.memory_access.prev_value[1] := by
    symm
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.2.1
  have selectedTwo
      (bitOne : input.offset_bit[1] = 0)
      (bitTwo : input.offset_bit[2] = 1) :
      input.selected_limb = input.memory_access.prev_value[2] := by
    symm
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.2.2.1
  have selectedThree
      (bitOne : input.offset_bit[1] = 1)
      (bitTwo : input.offset_bit[2] = 1) :
      input.selected_limb = input.memory_access.prev_value[3] := by
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.2.2.2
  have lowMux (bitZero : input.offset_bit[0] = 0) :
      input.selected_byte = input.selected_limb_low_byte := by
    simpa [bitZero] using mux
  have highMux (bitZero : input.offset_bit[0] = 1) :
      input.selected_byte = LoadByteChip.highByte input := by
    simpa [bitZero] using mux
  have bitZeroBinary := address.1
  have bitOneBinary := address.2.1
  have bitTwoBinary := address.2.2.1
  change (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) at bitZeroBinary
  change (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) at bitOneBinary
  change (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) at bitTwoBinary
  have valOne : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt]
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  rcases bitTwoBinary with bitTwo | bitTwo
  · rcases bitOneBinary with bitOne | bitOne
    · rcases bitZeroBinary with bitZero | bitZero
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[0] = _
          rw [wordBytes_zero _ priorBound, ← selectedZero bitOne bitTwo, lowMux bitZero]
          exact lowByte
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[1] = _
          rw [wordBytes_one _ priorBound, ← selectedZero bitOne bitTwo, highMux bitZero]
          exact highByte
    · rcases bitZeroBinary with bitZero | bitZero
      · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[2] = _
          rw [wordBytes_two _ priorBound, ← selectedOne bitOne bitTwo, lowMux bitZero]
          exact lowByte
      · refine ⟨⟨3, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[3] = _
          rw [wordBytes_three _ priorBound, ← selectedOne bitOne bitTwo, highMux bitZero]
          exact highByte
  · rcases bitOneBinary with bitOne | bitOne
    · rcases bitZeroBinary with bitZero | bitZero
      · refine ⟨⟨4, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[4] = _
          rw [wordBytes_four _ priorBound, ← selectedTwo bitOne bitTwo, lowMux bitZero]
          exact lowByte
      · refine ⟨⟨5, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[5] = _
          rw [wordBytes_five _ priorBound, ← selectedTwo bitOne bitTwo, highMux bitZero]
          exact highByte
    · rcases bitZeroBinary with bitZero | bitZero
      · refine ⟨⟨6, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[6] = _
          rw [wordBytes_six _ priorBound, ← selectedThree bitOne bitTwo, lowMux bitZero]
          exact lowByte
      · refine ⟨⟨7, by omega⟩, ?_, ?_⟩
        · simp [addressOffset, bitZero, bitOne, bitTwo, valOne]
        · change (wordBytes
            (Word.toBitVec64 input.memory_access.prev_value))[7] = _
          rw [wordBytes_seven _ priorBound, ← selectedThree bitOne bitTwo, highMux bitZero]
          exact highByte

omit [Fact (2 ^ 25 < p)] in
/-- A real LoadByte row selects exactly one of LB and LBU. -/
theorem loadByte_oneHot
    (input : LoadByteChip.Inputs (ZMod p))
    (cols : LoadByteChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadByteChip.Spec input cols data)
    (real : LoadByteChip.isReal input = 1) :
    (input.is_lb = 1 ∧ input.is_lbu = 0) ∨
      (input.is_lbu = 1 ∧ input.is_lb = 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, lbBinary, lbuBinary, _⟩ := spec
  rcases lbBinary with lbZero | lbOne
  · rcases lbuBinary with lbuZero | lbuOne
    · rw [LoadByteChip.isReal, lbZero, lbuZero] at real
      simp at real
    · exact Or.inr ⟨lbuOne, lbZero⟩
  · rcases lbuBinary with lbuZero | lbuOne
    · exact Or.inl ⟨lbOne, lbuZero⟩
    · rw [LoadByteChip.isReal, lbOne, lbuOne] at real
      have oneZero : (1 : ZMod p) = 0 := by linear_combination real
      exact (one_ne_zero oneZero).elim

/-- Specialize the generic literal-descriptor transport to LoadByte without unfolding its
completed circuit. -/
theorem loadByteSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h :
      ((loadByteChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    LoadByteChip.Spec
      (circuitRowInputOf LoadByteChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadByteChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold loadByteChipDescriptor at h
  exact chipSpec_of_literalDescriptor LoadByteChip.kind LoadByteChip.circuit
    rfl [.LB, .LBU] .nonX0 data physical h

/-- Specialize the folded `advanceReady` transport to LoadByte. -/
theorem loadByteAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : LoadByteChip.AdvanceReady
      (circuitRowInputOf LoadByteChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadByteChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((loadByteChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((loadByteChipDescriptor (p := p)).decodeRow data physical).inputs
      ((loadByteChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold loadByteChipDescriptor
  apply advanceReady_of_literalDescriptor LoadByteChip.kind LoadByteChip.circuit
    rfl [.LB, .LBU] .nonX0 data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
theorem loadByteViewOf_eq (env : Environment (ZMod p)) :
    loadByteViewOf env =
      LoadByteChip.rowView
        ((⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
        ((⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
  unfold loadByteViewOf
  rw [circuitRowInputOf_eq_component, circuitRowOutputOf_eq_component]

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem loadByteEvalInputAdapter
    (env : Environment (ZMod p)) (input : Var LoadByteChip.Inputs (ZMod p)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [ProvableStruct.eval_var_eq_eval]
  rfl

omit [Fact (2 ^ 25 < p)] in
/-- LoadByte's folded completed row exposes the physical `op_a_0` input without unfolding its
output. This is the scalar bridge from the literal route assertion to the semantic Program row. -/
theorem loadByteViewOf_opA0 (env : Environment (ZMod p)) :
    (loadByteViewOf env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) LoadByteChip.Inputs 0).adapter.op_a_0 := by
  unfold loadByteViewOf
  simp only [LoadByteChip.rowView]
  rw [circuitRowInputOf_eq_eval]
  change (Eval.eval env (varFromOffset (F := ZMod p) LoadByteChip.Inputs 0)).adapter.op_a_0 = _
  rw [loadByteEvalInputAdapter]
  exact Readers.ITypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
theorem loadByteRamAccessOf_eq (env : Environment (ZMod p)) :
    loadByteRamAccessOf env =
      LoadByteChip.ramAccessView
        ((⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
        ((⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) := by
  unfold loadByteRamAccessOf
  rw [circuitRowInputOf_eq_component, circuitRowOutputOf_eq_component]

theorem loadByteRamAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨loadByteChipDescriptor (p := p), physical⟩ data =
      loadByteRamAccessOf (Environment.fromArray physical data) := by
  unfold decodedRamAccess
  rw [DecodedInstructionRow.toChipRow_ramAccess]
  simp only [loadByteChipDescriptor_table, loadByteChipDescriptor_ramAccess, Option.getD_some]
  rw [loadByteRamAccessOf_eq]
  rfl

theorem loadByteViewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨loadByteChipDescriptor (p := p), physical⟩ data).view =
      loadByteViewOf (Environment.fromArray physical data) := by
  rw [DecodedInstructionRow.toChipRow_view]
  simp only [loadByteChipDescriptor_table, loadByteChipDescriptor_view]
  rw [loadByteViewOf_eq]
  rfl

theorem loadByteViewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨LoadByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (loadByteViewOf (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (loadByteViewOf (Environment.fromArray physical data)) := by
  rw [loadByteViewOf_eq] at real ⊢
  exact viewClockBounds_of_cpuStateContract LoadByteChip.circuit LoadByteChip.rowView
    LoadByteChip.cpuStateTimeContract data physical guarantees real

theorem loadByteTimestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨LoadByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (loadByteViewOf (Environment.fromArray physical data)).is_real = 1) :
    LoadMemoryTimestampBounds
      (loadByteViewOf (Environment.fromArray physical data))
      (loadByteRamAccessOf (Environment.fromArray physical data)) := by
  rw [loadByteViewOf_eq] at real ⊢
  rw [loadByteRamAccessOf_eq]
  exact loadMemoryTimestampBounds_of_contracts LoadByteChip.circuit
    LoadByteChip.rowView LoadByteChip.ramAccessView LoadByteChip.ramTimestampContract
    LoadByteChip.itypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem loadByteIsRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (loadByteViewOf
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam (loadByteRamAccessOf (Environment.fromArray physical data)) := by
  rw [loadByteViewOf_eq] at real
  rw [loadByteRamAccessOf_eq]
  exact ramAccessIsRam_of_addressContract LoadByteChip.circuit
    (fun input cols => some (LoadByteChip.ramAccessView input cols))
    LoadByteChip.isReal LoadByteChip.ramAddressContract data physical constraints
    (by simpa only [LoadByteChip.rowView] using real) _ rfl

theorem loadByteChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadByteChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
  subst hchip'
  rw [loadByteChipDescriptor_table] at guarantees
  rw [loadByteViewOf_decoded] at real ⊢
  exact loadByteViewClockBounds_env data physical guarantees real

theorem loadByteChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadByteChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    LoadMemoryTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
  subst hchip'
  rw [loadByteChipDescriptor_table] at constraints guarantees
  rw [loadByteViewOf_decoded] at real ⊢
  rw [loadByteRamAccessOf_decoded]
  exact loadByteTimestampBounds_env data physical constraints guarantees real

theorem loadByteChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadByteChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
  subst hchip'
  rw [loadByteChipDescriptor_table] at constraints
  rw [loadByteViewOf_decoded] at real
  rw [loadByteRamAccessOf_decoded]
  exact loadByteIsRam_env data physical constraints real

/-- Lift a descriptor-level equality for evaluated Memory interactions to the exact typed
decoded-row boundary. The proof rewrites only the folded `view`/`ramAccess` decoder interfaces, so
concrete memory chips never unfold the large dependent `decodeRow` term. -/
theorem typedMemoryInteractions_of_values (chip : SupportedChip p)
    (layout : Trace.RowView (ZMod p) → Trace.RamAccessView (ZMod p) →
      List (TypedInteraction (memoryChannel (p := p))))
    (values : ∀ env : Environment (ZMod p),
      chip.table.operations.interactionValuesWith memoryChannel.toRaw env =
        (layout
          (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env))
          ((chip.kind.ramAccess
            (chip.table.rowInput env) (chip.table.rowOutput env)).getD
              zeroRamAccess)).map TypedInteraction.raw)
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = chip) :
    decoded.interactionsWith data memoryChannel =
      layout (decoded.toChipRow data).view (decodedRamAccess decoded data) := by
  rw [DecodedInstructionRow.toChipRow_view]
  unfold decodedRamAccess
  rw [DecodedInstructionRow.toChipRow_ramAccess]
  obtain ⟨actualChip, physical⟩ := decoded
  have hchip' : actualChip = chip := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment] using
    values (Environment.fromArray physical data)

omit [Fact (2 ^ 25 < p)] in
/-- LoadByte's public exposed Memory list evaluates to the normal-load six-message layout. -/
theorem loadByteChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (loadMemoryInteractions
        (LoadByteChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadByteChip.Inputs 0))
          (Eval.eval env ((LoadByteChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadByteChip.Inputs 0) (size LoadByteChip.Inputs))))
        (LoadByteChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadByteChip.Inputs 0))
          (Eval.eval env ((LoadByteChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadByteChip.Inputs 0)
            (size LoadByteChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues loadByte loadMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, LoadByteChip.rowView, LoadByteChip.ramAccessView,
    LoadByteChip.isReal, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, LoadByteChip.circuit, circuit_norm]

/-- Lift LoadByte's evaluated six-message list to the folded decoded-row boundary. -/
theorem loadByteChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadByteChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      loadMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions loadByte loadMemoryInteractions

/-- LoadByte instantiates the authenticated normal-load interaction shape. -/
noncomputable def loadByteChip_loadMemoryInteractionShape :
    LoadMemoryInteractionShape (loadByteChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := loadByteChip_typedMemoryInteractions_eq

end LoadByte

section LoadHalf

/-- The LoadHalf descriptor in the supported Core registry. -/
def loadHalfChipDescriptor : SupportedChip p :=
  ⟨LoadHalfChip.kind, LoadHalfChip.circuit, rfl, [.LH, .LHU], .nonX0⟩

theorem loadHalfChipDescriptor_table :
    (loadHalfChipDescriptor (p := p)).table =
      (⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadHalfChipDescriptor_rdGuard :
    (loadHalfChipDescriptor (p := p)).rdGuard = .nonX0 := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadHalfChipDescriptor_view (input : LoadHalfChip.Inputs (ZMod p))
    (output : LoadHalfChip.Columns (ZMod p)) :
    (loadHalfChipDescriptor (p := p)).kind.view input output =
      LoadHalfChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadHalfChipDescriptor_ramAccess (input : LoadHalfChip.Inputs (ZMod p))
    (output : LoadHalfChip.Columns (ZMod p)) :
    (loadHalfChipDescriptor (p := p)).kind.ramAccess input output =
      some (LoadHalfChip.ramAccessView input output) := rfl

theorem loadHalfChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (loadHalfChipDescriptor (p := p)).table.Assumptions env ↔
      LoadHalfChip.Assumptions
        (circuitRowInputOf LoadHalfChip.circuit env) env.data := by
  chipAssumptionsIff loadHalf

omit [Fact (2 ^ 25 < p)] in
/-- Assemble LoadHalf's assumptions from the grounded base, immediate, and prior RAM word. -/
theorem loadHalfAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView env).adapter.op_c)
    (ram : Word.isU64
      (circuitRamAccessOf LoadHalfChip.circuit LoadHalfChip.ramAccessView env).priorValue) :
    LoadHalfChip.Assumptions
      (circuitRowInputOf LoadHalfChip.circuit env) data := by
  chipLoadAssumptionsEnv loadHalf

/-- Specialize the folded semantic-row transport to LoadHalf. -/
theorem loadHalfSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((loadHalfChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    LoadHalfChip.Spec
      (circuitRowInputOf LoadHalfChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadHalfChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold loadHalfChipDescriptor at h
  exact chipSpec_of_literalDescriptor LoadHalfChip.kind LoadHalfChip.circuit
    rfl [.LH, .LHU] .nonX0 data physical h

/-- Specialize the folded readiness transport to LoadHalf. -/
theorem loadHalfAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : LoadHalfChip.AdvanceReady
      (circuitRowInputOf LoadHalfChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadHalfChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((loadHalfChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((loadHalfChipDescriptor (p := p)).decodeRow data physical).inputs
      ((loadHalfChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold loadHalfChipDescriptor
  apply advanceReady_of_literalDescriptor LoadHalfChip.kind LoadHalfChip.circuit
    rfl [.LH, .LHU] .nonX0 data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
/-- LoadHalf's folded view exposes its physical non-x0 route flag without evaluating the output. -/
theorem loadHalfView_opA0 (env : Environment (ZMod p)) :
    (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) LoadHalfChip.Inputs 0).adapter.op_a_0 := by
  rw [circuitRowViewOf_eq_typed]
  simp only [LoadHalfChip.rowView]
  rw [circuitRowInputOf_eq_eval]
  change (Eval.eval env (varFromOffset (F := ZMod p) LoadHalfChip.Inputs 0)).adapter.op_a_0 = _
  rw [ProvableStruct.eval_var_eq_eval]
  exact Readers.ITypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
/-- A real LoadHalf row selects exactly one of LH and LHU. -/
theorem loadHalf_oneHot
    (input : LoadHalfChip.Inputs (ZMod p))
    (cols : LoadHalfChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadHalfChip.Spec input cols data)
    (real : LoadHalfChip.isReal input = 1) :
    (input.is_lh = 1 ∧ input.is_lhu = 0) ∨
      (input.is_lhu = 1 ∧ input.is_lh = 0) := by
  obtain ⟨_, _, _, _, _, _, _, lhBinary, lhuBinary, _⟩ := spec
  rcases lhBinary with lhZero | lhOne
  · rcases lhuBinary with lhuZero | lhuOne
    · rw [LoadHalfChip.isReal, lhZero, lhuZero] at real
      simp at real
    · exact Or.inr ⟨lhuOne, lhZero⟩
  · rcases lhuBinary with lhuZero | lhuOne
    · exact Or.inl ⟨lhOne, lhuZero⟩
    · rw [LoadHalfChip.isReal, lhOne, lhuOne] at real
      have oneZero : (1 : ZMod p) = 0 := by linear_combination real
      exact (one_ne_zero oneZero).elim

omit [Fact (2 ^ 25 < p)] in
/-- LoadHalf's selector equations identify the two architectural bytes at its aligned effective
address. -/
theorem loadHalf_selectedBytes
    (input : LoadHalfChip.Inputs (ZMod p))
    (cols : LoadHalfChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadHalfChip.Spec input cols data)
    (priorBound : Word.isU64 input.memory_access.prev_value) :
    ∃ i₀ i₁ : Fin 8,
      i₀.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0],
          input.offset_bit[1], LoadHalfChip.isReal input⟩ ∧
      i₁.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0],
          input.offset_bit[1], LoadHalfChip.isReal input⟩ + 1 ∧
      input.selected_half.val < 65536 ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i₀] =
        BitVec.ofNat 8 input.selected_half.val ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i₁] =
        BitVec.ofNat 8 (input.selected_half.val >>> 8) := by
  obtain ⟨address, _memory, _msb, _reader, limbSelect, _route, _unsigned,
    _lhBinary, _lhuBinary, _realBinary⟩ := spec
  have bitOneBinary := address.2.1
  have bitTwoBinary := address.2.2.1
  change (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) at bitOneBinary
  change (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) at bitTwoBinary
  have selectedZero
      (bitOne : input.offset_bit[0] = 0)
      (bitTwo : input.offset_bit[1] = 0) :
      input.selected_half = input.memory_access.prev_value[0] := by
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.1
  have selectedOne
      (bitOne : input.offset_bit[0] = 1)
      (bitTwo : input.offset_bit[1] = 0) :
      input.selected_half = input.memory_access.prev_value[1] := by
    symm
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.2.1
  have selectedTwo
      (bitOne : input.offset_bit[0] = 0)
      (bitTwo : input.offset_bit[1] = 1) :
      input.selected_half = input.memory_access.prev_value[2] := by
    symm
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.2.2.1
  have selectedThree
      (bitOne : input.offset_bit[0] = 1)
      (bitTwo : input.offset_bit[1] = 1) :
      input.selected_half = input.memory_access.prev_value[3] := by
    apply sub_eq_zero.mp
    simpa [bitOne, bitTwo] using limbSelect.2.2.2
  have limbBounds := Word.lt_cases_of_isU64 priorBound
  have valOne : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt]
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  rcases bitTwoBinary with bitTwo | bitTwo
  · rcases bitOneBinary with bitOne | bitOne
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addressOffset, bitOne, bitTwo]
      · simp [addressOffset, bitOne, bitTwo]
      · rw [selectedZero bitOne bitTwo]
        exact limbBounds.1
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[0] = _
        rw [wordBytes_zero _ priorBound, selectedZero bitOne bitTwo]
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[1] = _
        rw [wordBytes_one _ priorBound, selectedZero bitOne bitTwo]
    · refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addressOffset, bitOne, bitTwo, valOne]
      · simp [addressOffset, bitOne, bitTwo, valOne]
      · rw [selectedOne bitOne bitTwo]
        exact limbBounds.2.1
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[2] = _
        rw [wordBytes_two _ priorBound, selectedOne bitOne bitTwo]
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[3] = _
        rw [wordBytes_three _ priorBound, selectedOne bitOne bitTwo]
  · rcases bitOneBinary with bitOne | bitOne
    · refine ⟨⟨4, by omega⟩, ⟨5, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addressOffset, bitOne, bitTwo, valOne]
      · simp [addressOffset, bitOne, bitTwo, valOne]
      · rw [selectedTwo bitOne bitTwo]
        exact limbBounds.2.2.1
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[4] = _
        rw [wordBytes_four _ priorBound, selectedTwo bitOne bitTwo]
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[5] = _
        rw [wordBytes_five _ priorBound, selectedTwo bitOne bitTwo]
    · refine ⟨⟨6, by omega⟩, ⟨7, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addressOffset, bitOne, bitTwo, valOne]
      · simp [addressOffset, bitOne, bitTwo, valOne]
      · rw [selectedThree bitOne bitTwo]
        exact limbBounds.2.2.2
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[6] = _
        rw [wordBytes_six _ priorBound, selectedThree bitOne bitTwo]
      · change (wordBytes
          (Word.toBitVec64 input.memory_access.prev_value))[7] = _
        rw [wordBytes_seven _ priorBound, selectedThree bitOne bitTwo]

omit [Fact (2 ^ 25 < p)] in
/-- LoadHalf retains the generic RAM timestamp reader after its address operation. -/
theorem LoadHalfChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (LoadHalfChip.circuit (p := p))
      LoadHalfChip.rowView
      (fun input cols => some (LoadHalfChip.ramAccessView input cols)) := by
  let input : Var LoadHalfChip.Inputs (ZMod p) := varFromOffset LoadHalfChip.Inputs 0
  let offset := size LoadHalfChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1],
      input.is_lh + input.is_lhu⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.memory_access.prev_value, input.is_lh + input.is_lhu⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, LoadHalfChip.circuit,
      LoadHalfChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, LoadHalfChip.circuit,
        LoadHalfChip.rowView, LoadHalfChip.ramAccessView, LoadHalfChip.isReal,
        circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- LoadHalf's RAM address is the retained address operation's aligned output. -/
theorem LoadHalfChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (LoadHalfChip.circuit (p := p))
      (fun input cols => some (LoadHalfChip.ramAccessView input cols))
      LoadHalfChip.isReal := by
  let input : Var LoadHalfChip.Inputs (ZMod p) := varFromOffset LoadHalfChip.Inputs 0
  let offset := size LoadHalfChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1],
      input.is_lh + input.is_lhu⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, LoadHalfChip.circuit, LoadHalfChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, LoadHalfChip.circuit,
      LoadHalfChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, LoadHalfChip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- LoadHalf retains the ordinary I-type register timestamp reader. -/
theorem LoadHalfChip.itypeTimestampContract :
    CircuitITypeTimestampContract (p := p) (LoadHalfChip.circuit (p := p))
      LoadHalfChip.rowView := by
  let input : Var LoadHalfChip.Inputs (ZMod p) := varFromOffset LoadHalfChip.Inputs 0
  let offset := size LoadHalfChip.Inputs
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_lh + input.is_lhu, input.is_lh + input.is_lhu,
      input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.is_lh * 30 + input.is_lhu * 33,
      input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, LoadHalfChip.circuit, LoadHalfChip.main,
      Readers.ITypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, LoadHalfChip.rowView, LoadHalfChip.isReal,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem loadHalfChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨loadHalfChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded loadHalf

theorem loadHalfChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨loadHalfChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf LoadHalfChip.circuit LoadHalfChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded loadHalf

theorem loadHalfChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨LoadHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv loadHalf

theorem loadHalfChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨LoadHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    LoadMemoryTimestampBounds
      (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf LoadHalfChip.circuit LoadHalfChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact loadMemoryTimestampBounds_of_contracts LoadHalfChip.circuit
    LoadHalfChip.rowView LoadHalfChip.ramAccessView LoadHalfChip.ramTimestampContract
    LoadHalfChip.itypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem loadHalfChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf LoadHalfChip.circuit LoadHalfChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv loadHalf LoadHalfChip.isReal

theorem loadHalfChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadHalfChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds loadHalf

theorem loadHalfChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadHalfChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    LoadMemoryTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds loadHalf

theorem loadHalfChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadHalfChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam loadHalf

omit [Fact (2 ^ 25 < p)] in
/-- LoadHalf's public exposed Memory list evaluates to the normal-load six-message layout. -/
theorem loadHalfChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (loadMemoryInteractions
        (LoadHalfChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadHalfChip.Inputs 0))
          (Eval.eval env ((LoadHalfChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadHalfChip.Inputs 0) (size LoadHalfChip.Inputs))))
        (LoadHalfChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadHalfChip.Inputs 0))
          (Eval.eval env ((LoadHalfChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadHalfChip.Inputs 0)
            (size LoadHalfChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues loadHalf loadMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, LoadHalfChip.rowView, LoadHalfChip.ramAccessView,
    LoadHalfChip.isReal, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, LoadHalfChip.circuit, circuit_norm]

/-- Lift LoadHalf's evaluated six-message list to the folded decoded-row boundary. -/
theorem loadHalfChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadHalfChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      loadMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions loadHalf loadMemoryInteractions

/-- LoadHalf instantiates the authenticated normal-load interaction shape. -/
noncomputable def loadHalfChip_loadMemoryInteractionShape :
    LoadMemoryInteractionShape (loadHalfChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := loadHalfChip_typedMemoryInteractions_eq

end LoadHalf

section LoadWord

/-- The LoadWord descriptor in the supported Core registry. -/
def loadWordChipDescriptor : SupportedChip p :=
  ⟨LoadWordChip.kind, LoadWordChip.circuit, rfl, [.LW, .LWU], .nonX0⟩

theorem loadWordChipDescriptor_table :
    (loadWordChipDescriptor (p := p)).table =
      (⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadWordChipDescriptor_rdGuard :
    (loadWordChipDescriptor (p := p)).rdGuard = .nonX0 := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadWordChipDescriptor_view (input : LoadWordChip.Inputs (ZMod p))
    (output : LoadWordChip.Columns (ZMod p)) :
    (loadWordChipDescriptor (p := p)).kind.view input output =
      LoadWordChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadWordChipDescriptor_ramAccess (input : LoadWordChip.Inputs (ZMod p))
    (output : LoadWordChip.Columns (ZMod p)) :
    (loadWordChipDescriptor (p := p)).kind.ramAccess input output =
      some (LoadWordChip.ramAccessView input output) := rfl

theorem loadWordChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (loadWordChipDescriptor (p := p)).table.Assumptions env ↔
      LoadWordChip.Assumptions
        (circuitRowInputOf LoadWordChip.circuit env) env.data := by
  chipAssumptionsIff loadWord

omit [Fact (2 ^ 25 < p)] in
/-- Assemble LoadWord's assumptions from the grounded base, immediate, and prior RAM word. -/
theorem loadWordAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView env).adapter.op_c)
    (ram : Word.isU64
      (circuitRamAccessOf LoadWordChip.circuit LoadWordChip.ramAccessView env).priorValue) :
    LoadWordChip.Assumptions
      (circuitRowInputOf LoadWordChip.circuit env) data := by
  chipLoadAssumptionsEnv loadWord

/-- Specialize the folded semantic-row transport to LoadWord. -/
theorem loadWordSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((loadWordChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    LoadWordChip.Spec
      (circuitRowInputOf LoadWordChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadWordChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold loadWordChipDescriptor at h
  exact chipSpec_of_literalDescriptor LoadWordChip.kind LoadWordChip.circuit
    rfl [.LW, .LWU] .nonX0 data physical h

/-- Specialize the folded readiness transport to LoadWord. -/
theorem loadWordAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : LoadWordChip.AdvanceReady
      (circuitRowInputOf LoadWordChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadWordChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((loadWordChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((loadWordChipDescriptor (p := p)).decodeRow data physical).inputs
      ((loadWordChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold loadWordChipDescriptor
  apply advanceReady_of_literalDescriptor LoadWordChip.kind LoadWordChip.circuit
    rfl [.LW, .LWU] .nonX0 data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
/-- LoadWord's folded view exposes its physical non-x0 route flag without evaluating the output. -/
theorem loadWordView_opA0 (env : Environment (ZMod p)) :
    (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) LoadWordChip.Inputs 0).adapter.op_a_0 := by
  rw [circuitRowViewOf_eq_typed]
  simp only [LoadWordChip.rowView]
  rw [circuitRowInputOf_eq_eval]
  change (Eval.eval env (varFromOffset (F := ZMod p) LoadWordChip.Inputs 0)).adapter.op_a_0 = _
  rw [ProvableStruct.eval_var_eq_eval]
  exact Readers.ITypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
/-- A real LoadWord row selects exactly one of LW and LWU. -/
theorem loadWord_oneHot
    (input : LoadWordChip.Inputs (ZMod p))
    (cols : LoadWordChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadWordChip.Spec input cols data)
    (real : LoadWordChip.isReal input = 1) :
    (input.is_lw = 1 ∧ input.is_lwu = 0) ∨
      (input.is_lwu = 1 ∧ input.is_lw = 0) := by
  obtain ⟨_, _, _, _, _, _, _, lwBinary, lwuBinary, _⟩ := spec
  rcases lwBinary with lwZero | lwOne
  · rcases lwuBinary with lwuZero | lwuOne
    · rw [LoadWordChip.isReal, lwZero, lwuZero] at real
      simp at real
    · exact Or.inr ⟨lwuOne, lwZero⟩
  · rcases lwuBinary with lwuZero | lwuOne
    · exact Or.inl ⟨lwOne, lwuZero⟩
    · rw [LoadWordChip.isReal, lwOne, lwuOne] at real
      have oneZero : (1 : ZMod p) = 0 := by linear_combination real
      exact (one_ne_zero oneZero).elim

omit [Fact (2 ^ 25 < p)] in
/-- LoadWord's selector equations identify the four architectural bytes at its aligned effective
address. -/
theorem loadWord_selectedBytes
    (input : LoadWordChip.Inputs (ZMod p))
    (cols : LoadWordChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadWordChip.Spec input cols data)
    (priorBound : Word.isU64 input.memory_access.prev_value) :
    ∃ i₀ i₁ i₂ i₃ : Fin 8,
      i₀.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit,
          LoadWordChip.isReal input⟩ ∧
      i₁.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit,
          LoadWordChip.isReal input⟩ + 1 ∧
      i₂.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit,
          LoadWordChip.isReal input⟩ + 2 ∧
      i₃.val = addressOffset
        ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit,
          LoadWordChip.isReal input⟩ + 3 ∧
      input.selected_word[0].val < 65536 ∧ input.selected_word[1].val < 65536 ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i₀] =
        BitVec.ofNat 8 input.selected_word[0].val ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i₁] =
        BitVec.ofNat 8 (input.selected_word[0].val >>> 8) ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i₂] =
        BitVec.ofNat 8 input.selected_word[1].val ∧
      (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i₃] =
        BitVec.ofNat 8 (input.selected_word[1].val >>> 8) := by
  obtain ⟨address, _memory, _msb, _reader, limbSelect, _route, _unsigned,
    _lwBinary, _lwuBinary, _realBinary⟩ := spec
  have bitBinary := address.2.2.1
  change (input.offset_bit = 0 ∨ input.offset_bit = 1) at bitBinary
  have selectedLow
      (bit : input.offset_bit = 0) :
      input.selected_word[0] = input.memory_access.prev_value[0] ∧
        input.selected_word[1] = input.memory_access.prev_value[1] := by
    constructor
    · symm
      apply sub_eq_zero.mp
      simpa [bit] using limbSelect.1
    · symm
      apply sub_eq_zero.mp
      simpa [bit] using limbSelect.2.1
  have selectedHigh
      (bit : input.offset_bit = 1) :
      input.selected_word[0] = input.memory_access.prev_value[2] ∧
        input.selected_word[1] = input.memory_access.prev_value[3] := by
    constructor
    · apply sub_eq_zero.mp
      simpa [bit] using limbSelect.2.2.1
    · apply sub_eq_zero.mp
      simpa [bit] using limbSelect.2.2.2
  have limbBounds := Word.lt_cases_of_isU64 priorBound
  have valOne : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt]
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  rcases bitBinary with bit | bit
  · obtain ⟨selected₀, selected₁⟩ := selectedLow bit
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [addressOffset, bit]
    · simp [addressOffset, bit]
    · simp [addressOffset, bit]
    · simp [addressOffset, bit]
    · rw [selected₀]
      exact limbBounds.1
    · rw [selected₁]
      exact limbBounds.2.1
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[0] = _
      rw [wordBytes_zero _ priorBound, selected₀]
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[1] = _
      rw [wordBytes_one _ priorBound, selected₀]
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[2] = _
      rw [wordBytes_two _ priorBound, selected₁]
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[3] = _
      rw [wordBytes_three _ priorBound, selected₁]
  · obtain ⟨selected₂, selected₃⟩ := selectedHigh bit
    refine ⟨⟨4, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [addressOffset, bit, valOne]
    · simp [addressOffset, bit, valOne]
    · simp [addressOffset, bit, valOne]
    · simp [addressOffset, bit, valOne]
    · rw [selected₂]
      exact limbBounds.2.2.1
    · rw [selected₃]
      exact limbBounds.2.2.2
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[4] = _
      rw [wordBytes_four _ priorBound, selected₂]
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[5] = _
      rw [wordBytes_five _ priorBound, selected₂]
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[6] = _
      rw [wordBytes_six _ priorBound, selected₃]
    · change (wordBytes
        (Word.toBitVec64 input.memory_access.prev_value))[7] = _
      rw [wordBytes_seven _ priorBound, selected₃]

omit [Fact (2 ^ 25 < p)] in
theorem LoadWordChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (LoadWordChip.circuit (p := p))
      LoadWordChip.rowView
      (fun input cols => some (LoadWordChip.ramAccessView input cols)) := by
  let input : Var LoadWordChip.Inputs (ZMod p) := varFromOffset LoadWordChip.Inputs 0
  let offset := size LoadWordChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_lw + input.is_lwu⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.memory_access.prev_value, input.is_lw + input.is_lwu⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, LoadWordChip.circuit,
      LoadWordChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, LoadWordChip.circuit, LoadWordChip.rowView,
        LoadWordChip.ramAccessView, LoadWordChip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem LoadWordChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (LoadWordChip.circuit (p := p))
      (fun input cols => some (LoadWordChip.ramAccessView input cols))
      LoadWordChip.isReal := by
  let input : Var LoadWordChip.Inputs (ZMod p) := varFromOffset LoadWordChip.Inputs 0
  let offset := size LoadWordChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_lw + input.is_lwu⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, LoadWordChip.circuit, LoadWordChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, LoadWordChip.circuit,
      LoadWordChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, LoadWordChip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem LoadWordChip.itypeTimestampContract :
    CircuitITypeTimestampContract (p := p) (LoadWordChip.circuit (p := p))
      LoadWordChip.rowView := by
  let input : Var LoadWordChip.Inputs (ZMod p) := varFromOffset LoadWordChip.Inputs 0
  let offset := size LoadWordChip.Inputs
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_lw + input.is_lwu, input.is_lw + input.is_lwu,
      input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, input.is_lw * 31 + input.is_lwu * 34,
      input.selected_word[0], input.selected_word[1],
      65535 * input.msb, 65535 * input.msb⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, LoadWordChip.circuit, LoadWordChip.main,
      Readers.ITypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, LoadWordChip.rowView, LoadWordChip.isReal,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem loadWordChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨loadWordChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded loadWord

theorem loadWordChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨loadWordChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf LoadWordChip.circuit LoadWordChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded loadWord

theorem loadWordChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨LoadWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv loadWord

theorem loadWordChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨LoadWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    LoadMemoryTimestampBounds
      (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf LoadWordChip.circuit LoadWordChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact loadMemoryTimestampBounds_of_contracts LoadWordChip.circuit
    LoadWordChip.rowView LoadWordChip.ramAccessView LoadWordChip.ramTimestampContract
    LoadWordChip.itypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem loadWordChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf LoadWordChip.circuit LoadWordChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv loadWord LoadWordChip.isReal

theorem loadWordChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadWordChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds loadWord

theorem loadWordChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadWordChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    LoadMemoryTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds loadWord

theorem loadWordChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadWordChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam loadWord

omit [Fact (2 ^ 25 < p)] in
/-- LoadWord's public exposed Memory list evaluates to the normal-load six-message layout. -/
theorem loadWordChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (loadMemoryInteractions
        (LoadWordChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadWordChip.Inputs 0))
          (Eval.eval env ((LoadWordChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadWordChip.Inputs 0) (size LoadWordChip.Inputs))))
        (LoadWordChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadWordChip.Inputs 0))
          (Eval.eval env ((LoadWordChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadWordChip.Inputs 0)
            (size LoadWordChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues loadWord loadMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, LoadWordChip.rowView, LoadWordChip.ramAccessView,
    LoadWordChip.isReal, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, LoadWordChip.circuit, circuit_norm]

/-- Lift LoadWord's evaluated six-message list to the folded decoded-row boundary. -/
theorem loadWordChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadWordChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      loadMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions loadWord loadMemoryInteractions

/-- LoadWord instantiates the authenticated normal-load interaction shape. -/
noncomputable def loadWordChip_loadMemoryInteractionShape :
    LoadMemoryInteractionShape (loadWordChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := loadWordChip_typedMemoryInteractions_eq

end LoadWord

section LoadDouble

/-- The LoadDouble descriptor in the supported Core registry. -/
def loadDoubleChipDescriptor : SupportedChip p :=
  ⟨LoadDoubleChip.kind, LoadDoubleChip.circuit, rfl, [.LD], .nonX0⟩

theorem loadDoubleChipDescriptor_table :
    (loadDoubleChipDescriptor (p := p)).table =
      (⟨LoadDoubleChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadDoubleChipDescriptor_rdGuard :
    (loadDoubleChipDescriptor (p := p)).rdGuard = .nonX0 := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadDoubleChipDescriptor_view (input : LoadDoubleChip.Inputs (ZMod p))
    (output : LoadDoubleChip.Columns (ZMod p)) :
    (loadDoubleChipDescriptor (p := p)).kind.view input output =
      LoadDoubleChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadDoubleChipDescriptor_ramAccess (input : LoadDoubleChip.Inputs (ZMod p))
    (output : LoadDoubleChip.Columns (ZMod p)) :
    (loadDoubleChipDescriptor (p := p)).kind.ramAccess input output =
      some (LoadDoubleChip.ramAccessView input output) := rfl

theorem loadDoubleChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (loadDoubleChipDescriptor (p := p)).table.Assumptions env ↔
      LoadDoubleChip.Assumptions
        (circuitRowInputOf LoadDoubleChip.circuit env) env.data := by
  chipAssumptionsIff loadDouble

omit [Fact (2 ^ 25 < p)] in
/-- Assemble LoadDouble's assumptions from the grounded base, immediate, and prior RAM word. -/
theorem loadDoubleAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView env).adapter.op_c)
    (ram : Word.isU64
      (circuitRamAccessOf LoadDoubleChip.circuit LoadDoubleChip.ramAccessView env).priorValue) :
    LoadDoubleChip.Assumptions
      (circuitRowInputOf LoadDoubleChip.circuit env) data := by
  chipLoadAssumptionsEnv loadDouble

/-- Specialize the folded semantic-row transport to LoadDouble. -/
theorem loadDoubleSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((loadDoubleChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    LoadDoubleChip.Spec
      (circuitRowInputOf LoadDoubleChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadDoubleChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold loadDoubleChipDescriptor at h
  exact chipSpec_of_literalDescriptor LoadDoubleChip.kind LoadDoubleChip.circuit
    rfl [.LD] .nonX0 data physical h

/-- Specialize the folded readiness transport to LoadDouble. -/
theorem loadDoubleAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : LoadDoubleChip.AdvanceReady
      (circuitRowInputOf LoadDoubleChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadDoubleChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((loadDoubleChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((loadDoubleChipDescriptor (p := p)).decodeRow data physical).inputs
      ((loadDoubleChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold loadDoubleChipDescriptor
  apply advanceReady_of_literalDescriptor LoadDoubleChip.kind LoadDoubleChip.circuit
    rfl [.LD] .nonX0 data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
/-- LoadDouble's folded view exposes its physical non-x0 route flag without evaluating the output. -/
theorem loadDoubleView_opA0 (env : Environment (ZMod p)) :
    (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) LoadDoubleChip.Inputs 0).adapter.op_a_0 := by
  rw [circuitRowViewOf_eq_typed]
  simp only [LoadDoubleChip.rowView]
  rw [circuitRowInputOf_eq_eval]
  change (Eval.eval env (varFromOffset (F := ZMod p) LoadDoubleChip.Inputs 0)).adapter.op_a_0 = _
  rw [ProvableStruct.eval_var_eq_eval]
  exact Readers.ITypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
theorem LoadDoubleChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (LoadDoubleChip.circuit (p := p))
      LoadDoubleChip.rowView
      (fun input cols => some (LoadDoubleChip.ramAccessView input cols)) := by
  let input : Var LoadDoubleChip.Inputs (ZMod p) := varFromOffset LoadDoubleChip.Inputs 0
  let offset := size LoadDoubleChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.memory_access.prev_value, input.is_real⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, LoadDoubleChip.circuit,
      LoadDoubleChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, LoadDoubleChip.circuit, LoadDoubleChip.rowView,
        LoadDoubleChip.ramAccessView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem LoadDoubleChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (LoadDoubleChip.circuit (p := p))
      (fun input cols => some (LoadDoubleChip.ramAccessView input cols))
      (fun input => input.is_real) := by
  let input : Var LoadDoubleChip.Inputs (ZMod p) := varFromOffset LoadDoubleChip.Inputs 0
  let offset := size LoadDoubleChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, LoadDoubleChip.circuit, LoadDoubleChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, LoadDoubleChip.circuit,
      LoadDoubleChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem LoadDoubleChip.itypeTimestampContract :
    CircuitITypeTimestampContract (p := p) (LoadDoubleChip.circuit (p := p))
      LoadDoubleChip.rowView := by
  let input : Var LoadDoubleChip.Inputs (ZMod p) := varFromOffset LoadDoubleChip.Inputs 0
  let offset := size LoadDoubleChip.Inputs
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 35, input.memory_access.prev_value[0],
      input.memory_access.prev_value[1], input.memory_access.prev_value[2],
      input.memory_access.prev_value[3]⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, LoadDoubleChip.circuit, LoadDoubleChip.main,
      Readers.ITypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, LoadDoubleChip.rowView,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem loadDoubleChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨loadDoubleChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded loadDouble

theorem loadDoubleChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨loadDoubleChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf LoadDoubleChip.circuit LoadDoubleChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded loadDouble

theorem loadDoubleChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨LoadDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv loadDouble

theorem loadDoubleChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨LoadDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    LoadMemoryTimestampBounds
      (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf LoadDoubleChip.circuit LoadDoubleChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact loadMemoryTimestampBounds_of_contracts LoadDoubleChip.circuit
    LoadDoubleChip.rowView LoadDoubleChip.ramAccessView
    LoadDoubleChip.ramTimestampContract LoadDoubleChip.itypeTimestampContract
    data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem loadDoubleChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf LoadDoubleChip.circuit LoadDoubleChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv loadDouble (fun input => input.is_real)

theorem loadDoubleChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadDoubleChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds loadDouble

theorem loadDoubleChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadDoubleChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    LoadMemoryTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds loadDouble

theorem loadDoubleChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadDoubleChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam loadDouble

omit [Fact (2 ^ 25 < p)] in
/-- LoadDouble's public exposed Memory list evaluates to the normal-load six-message layout. -/
theorem loadDoubleChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨LoadDoubleChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (loadMemoryInteractions
        (LoadDoubleChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadDoubleChip.Inputs 0))
          (Eval.eval env ((LoadDoubleChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadDoubleChip.Inputs 0)
            (size LoadDoubleChip.Inputs))))
        (LoadDoubleChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadDoubleChip.Inputs 0))
          (Eval.eval env ((LoadDoubleChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadDoubleChip.Inputs 0)
            (size LoadDoubleChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues loadDouble loadMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, LoadDoubleChip.rowView, LoadDoubleChip.ramAccessView,
    AddressOperation.alignedValue, Extracted.ITypeReader.toAdapterView,
    LoadDoubleChip.circuit, circuit_norm]

/-- Lift LoadDouble's evaluated six-message list to the folded decoded-row boundary. -/
theorem loadDoubleChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadDoubleChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      loadMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions loadDouble loadMemoryInteractions

/-- LoadDouble instantiates the authenticated normal-load interaction shape. -/
noncomputable def loadDoubleChip_loadMemoryInteractionShape :
    LoadMemoryInteractionShape (loadDoubleChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := loadDoubleChip_typedMemoryInteractions_eq

end LoadDouble

section LoadX0

/-- The LoadX0 descriptor in the supported Core registry. -/
def loadX0ChipDescriptor : SupportedChip p :=
  ⟨LoadX0Chip.kind, LoadX0Chip.circuit, rfl,
    [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD], .onlyX0⟩

theorem loadX0ChipDescriptor_table :
    (loadX0ChipDescriptor (p := p)).table =
      (⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadX0ChipDescriptor_rdGuard :
    (loadX0ChipDescriptor (p := p)).rdGuard = .onlyX0 := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadX0ChipDescriptor_view (input : LoadX0Chip.Inputs (ZMod p))
    (output : LoadX0Chip.Columns (ZMod p)) :
    (loadX0ChipDescriptor (p := p)).kind.view input output =
      LoadX0Chip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem loadX0ChipDescriptor_ramAccess (input : LoadX0Chip.Inputs (ZMod p))
    (output : LoadX0Chip.Columns (ZMod p)) :
    (loadX0ChipDescriptor (p := p)).kind.ramAccess input output =
      some (LoadX0Chip.ramAccessView input output) := rfl

theorem loadX0ChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (loadX0ChipDescriptor (p := p)).table.Assumptions env ↔
      LoadX0Chip.Assumptions
        (circuitRowInputOf LoadX0Chip.circuit env) env.data := by
  chipAssumptionsIff loadX0

omit [Fact (2 ^ 25 < p)] in
/-- Assemble LoadX0's assumptions from the grounded base, immediate, and prior RAM word. -/
theorem loadX0Assumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView env).adapter.op_c)
    (ram : Word.isU64
      (circuitRamAccessOf LoadX0Chip.circuit LoadX0Chip.ramAccessView env).priorValue) :
    LoadX0Chip.Assumptions
      (circuitRowInputOf LoadX0Chip.circuit env) data := by
  chipLoadAssumptionsEnv loadX0

/-- Specialize the folded semantic-row transport to LoadX0. -/
theorem loadX0Spec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((loadX0ChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    LoadX0Chip.Spec
      (circuitRowInputOf LoadX0Chip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadX0Chip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold loadX0ChipDescriptor at h
  exact chipSpec_of_literalDescriptor LoadX0Chip.kind LoadX0Chip.circuit
    rfl [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD] .onlyX0 data physical h

/-- Specialize the folded readiness transport to LoadX0. -/
theorem loadX0AdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : LoadX0Chip.advanceReady
      (circuitRowInputOf LoadX0Chip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf LoadX0Chip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((loadX0ChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((loadX0ChipDescriptor (p := p)).decodeRow data physical).inputs
      ((loadX0ChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold loadX0ChipDescriptor
  apply advanceReady_of_literalDescriptor LoadX0Chip.kind LoadX0Chip.circuit
    rfl [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD] .onlyX0
    data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
/-- LoadX0's folded view exposes its physical `x0` route flag without evaluating the output. -/
theorem loadX0View_opA0 (env : Environment (ZMod p)) :
    (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).adapter.op_a_0 := by
  rw [circuitRowViewOf_eq_typed]
  simp only [LoadX0Chip.rowView]
  rw [circuitRowInputOf_eq_eval]
  change (Eval.eval env (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0)).adapter.op_a_0 = _
  rw [ProvableStruct.eval_var_eq_eval]
  exact Readers.ITypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
/-- LoadX0's folded view exposes the seven-selector activity sum. -/
theorem loadX0View_isReal (env : Environment (ZMod p)) :
    (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView env).is_real =
      Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_lb +
        Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_lbu +
        Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_lh +
        Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_lhu +
        Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_lw +
        Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_lwu +
        Expression.eval env
          (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0).is_ld := by
  rw [circuitRowViewOf_eq_typed]
  simp only [LoadX0Chip.rowView, LoadX0Chip.isReal]
  rw [circuitRowInputOf_eq_eval]
  change LoadX0Chip.isReal (Eval.eval env (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0)) = _
  rw [LoadX0Chip.isReal, ProvableStruct.eval_var_eq_eval]
  simp only [circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem loadX0Val_of_binary {b : ZMod p} (h : b = 0 ∨ b = 1) :
    b.val = 0 ∨ b.val = 1 := by
  haveI : Fact (1 < p) := ⟨by
    have := Fact.out (p := 2 ^ 17 < p)
    omega⟩
  rcases h with h | h <;> rw [h] <;> simp [ZMod.val_one]

omit [Fact (2 ^ 25 < p)] in
private theorem loadX0OneHot7_atMost {b0 b1 b2 b3 b4 b5 b6 : ZMod p}
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1)
    (h2 : b2 = 0 ∨ b2 = 1) (h3 : b3 = 0 ∨ b3 = 1)
    (h4 : b4 = 0 ∨ b4 = 1) (h5 : b5 = 0 ∨ b5 = 1)
    (h6 : b6 = 0 ∨ b6 = 1)
    (hsum : (b0 + b1 + b2 + b3 + b4 + b5 + b6) *
      (b0 + b1 + b2 + b3 + b4 + b5 + b6 - 1) = 0) :
    b0.val + b1.val + b2.val + b3.val + b4.val + b5.val + b6.val ≤ 1 := by
  haveI : Fact (1 < p) := ⟨by
    have := Fact.out (p := 2 ^ 17 < p)
    omega⟩
  have hp : 8 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  set total := b0 + b1 + b2 + b3 + b4 + b5 + b6 with totalEq
  have hvals :
      (b0.val = 0 ∨ b0.val = 1) ∧ (b1.val = 0 ∨ b1.val = 1) ∧
      (b2.val = 0 ∨ b2.val = 1) ∧ (b3.val = 0 ∨ b3.val = 1) ∧
      (b4.val = 0 ∨ b4.val = 1) ∧ (b5.val = 0 ∨ b5.val = 1) ∧
      (b6.val = 0 ∨ b6.val = 1) :=
    ⟨loadX0Val_of_binary h0, loadX0Val_of_binary h1, loadX0Val_of_binary h2,
      loadX0Val_of_binary h3, loadX0Val_of_binary h4, loadX0Val_of_binary h5,
      loadX0Val_of_binary h6⟩
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := hvals
  have totalCast :
      total = ((b0.val + b1.val + b2.val + b3.val + b4.val + b5.val + b6.val : ℕ) : ZMod p) := by
    rw [totalEq]
    push_cast [ZMod.natCast_zmod_val]
    ring
  have totalVal :
      total.val = b0.val + b1.val + b2.val + b3.val + b4.val + b5.val + b6.val := by
    rw [totalCast]
    exact ZMod.val_natCast_of_lt (by omega)
  have totalBinary : total.val = 0 ∨ total.val = 1 := by
    rcases bool_of_mul_pred hsum with h | h
    · left
      rw [h, ZMod.val_zero]
    · right
      rw [h, ZMod.val_one]
  omega

omit [Fact (2 ^ 25 < p)] in
private theorem loadX0OneHot7 {b0 b1 b2 b3 b4 b5 b6 : ZMod p}
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1)
    (h2 : b2 = 0 ∨ b2 = 1) (h3 : b3 = 0 ∨ b3 = 1)
    (h4 : b4 = 0 ∨ b4 = 1) (h5 : b5 = 0 ∨ b5 = 1)
    (h6 : b6 = 0 ∨ b6 = 1)
    (hsum : b0 + b1 + b2 + b3 + b4 + b5 + b6 = 1) :
    (b0 = 1 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0) ∨
      (b1 = 1 ∧ b0 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0) ∨
      (b2 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0) ∨
      (b3 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0) ∨
      (b4 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b5 = 0 ∧ b6 = 0) ∨
      (b5 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b6 = 0) ∨
      (b6 = 1 ∧ b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0) := by
  have atMost := loadX0OneHot7_atMost h0 h1 h2 h3 h4 h5 h6 (by
    rw [hsum]
    simp)
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
    rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl <;>
    rcases h6 with rfl | rfl
  all_goals
    simp only [ZMod.val_zero, ZMod.val_one] at atMost
    first | omega | simp at hsum ⊢

omit [Fact (2 ^ 25 < p)] in
/-- An active LoadX0 row selects exactly one of its seven upstream load opcodes. -/
theorem loadX0_oneHot
    (input : LoadX0Chip.Inputs (ZMod p))
    (cols : LoadX0Chip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (spec : LoadX0Chip.Spec input cols data)
    (real : LoadX0Chip.isReal input = 1) :
    (input.is_lb = 1 ∧ input.is_lbu = 0 ∧ input.is_lh = 0 ∧ input.is_lhu = 0 ∧
      input.is_lw = 0 ∧ input.is_lwu = 0 ∧ input.is_ld = 0) ∨
    (input.is_lbu = 1 ∧ input.is_lb = 0 ∧ input.is_lh = 0 ∧ input.is_lhu = 0 ∧
      input.is_lw = 0 ∧ input.is_lwu = 0 ∧ input.is_ld = 0) ∨
    (input.is_lh = 1 ∧ input.is_lb = 0 ∧ input.is_lbu = 0 ∧ input.is_lhu = 0 ∧
      input.is_lw = 0 ∧ input.is_lwu = 0 ∧ input.is_ld = 0) ∨
    (input.is_lhu = 1 ∧ input.is_lb = 0 ∧ input.is_lbu = 0 ∧ input.is_lh = 0 ∧
      input.is_lw = 0 ∧ input.is_lwu = 0 ∧ input.is_ld = 0) ∨
    (input.is_lw = 1 ∧ input.is_lb = 0 ∧ input.is_lbu = 0 ∧ input.is_lh = 0 ∧
      input.is_lhu = 0 ∧ input.is_lwu = 0 ∧ input.is_ld = 0) ∨
    (input.is_lwu = 1 ∧ input.is_lb = 0 ∧ input.is_lbu = 0 ∧ input.is_lh = 0 ∧
      input.is_lhu = 0 ∧ input.is_lw = 0 ∧ input.is_ld = 0) ∨
    (input.is_ld = 1 ∧ input.is_lb = 0 ∧ input.is_lbu = 0 ∧ input.is_lh = 0 ∧
      input.is_lhu = 0 ∧ input.is_lw = 0 ∧ input.is_lwu = 0) := by
  obtain ⟨_, _, _, lb, lbu, lh, lhu, lw, lwu, ld, _⟩ := spec
  exact loadX0OneHot7 lb lbu lh lhu lw lwu ld (by
    simpa only [LoadX0Chip.isReal] using real)

omit [Fact (2 ^ 25 < p)] in
/-- The `AddressOperation` input physically composed by LoadX0. -/
def loadX0AddressInput (input : LoadX0Chip.Inputs (ZMod p)) :
    AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
    input.offset_bit[1], input.offset_bit[2], LoadX0Chip.isReal input⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem loadX0ByteEvidence
    (input : LoadX0Chip.Inputs (ZMod p)) (state : SailState) (opcode : ZMod p)
    (opcodeEq : LoadX0Chip.opcodeVal input = opcode)
    (rawLt :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat < 2 ^ 48)
    (low : 2 ^ 16 ≤
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat)
    (offsetEq :
      addressOffset (loadX0AddressInput input) =
        (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8)
    (memoryAt : ∀ k, addressOffset (loadX0AddressInput input) + k < 8 →
      ∃ byte : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + k]? =
            some byte) :
    LoadX0Chip.opcodeVal input = opcode ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 1 ≤ 2 ^ 48 ∧
      2 ^ 16 ≤ (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat ∧
      ∃ byte : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat]? = some byte := by
  have offsetLt : addressOffset (loadX0AddressInput input) < 8 := by
    rw [offsetEq]
    exact Nat.mod_lt _ (by norm_num)
  obtain ⟨byte, memory⟩ := memoryAt 0 (by simpa only [Nat.add_zero] using offsetLt)
  rw [Nat.add_zero] at memory
  exact ⟨opcodeEq, Nat.add_one_le_iff.mpr rawLt, low, byte, memory⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem loadX0HalfEvidence
    (input : LoadX0Chip.Inputs (ZMod p)) (state : SailState) (opcode : ZMod p)
    (opcodeEq : LoadX0Chip.opcodeVal input = opcode)
    (bit₀ : input.offset_bit[0] = 0)
    (rawLt :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat < 2 ^ 48)
    (low : 2 ^ 16 ≤
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat)
    (offsetEq :
      addressOffset (loadX0AddressInput input) =
        (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8)
    (memoryAt : ∀ k, addressOffset (loadX0AddressInput input) + k < 8 →
      ∃ byte : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + k]? =
            some byte) :
    LoadX0Chip.opcodeVal input = opcode ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 2 = 0 ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 2 ≤ 2 ^ 48 ∧
      2 ^ 16 ≤ (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat ∧
      ∃ byte₀ byte₁ : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat]? =
            some byte₀ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 1]? =
            some byte₁ := by
  have alignment :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8)]
    rw [← offsetEq]
    simp only [addressOffset, loadX0AddressInput, bit₀, ZMod.val_zero]
    omega
  have offsetAlignment : addressOffset (loadX0AddressInput input) % 2 = 0 := by
    rw [offsetEq, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8)]
    exact alignment
  have offsetLt : addressOffset (loadX0AddressInput input) < 8 := by
    rw [offsetEq]
    exact Nat.mod_lt _ (by norm_num)
  have high :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 2 ≤ 2 ^ 48 := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero alignment
    omega
  obtain ⟨byte₀, memory₀⟩ := memoryAt 0 (by omega)
  obtain ⟨byte₁, memory₁⟩ := memoryAt 1 (by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero offsetAlignment
    omega)
  rw [Nat.add_zero] at memory₀
  exact ⟨opcodeEq, alignment, high, low, byte₀, byte₁, memory₀, memory₁⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem loadX0WordEvidence
    (input : LoadX0Chip.Inputs (ZMod p)) (state : SailState) (opcode : ZMod p)
    (opcodeEq : LoadX0Chip.opcodeVal input = opcode)
    (bit₀ : input.offset_bit[0] = 0) (bit₁ : input.offset_bit[1] = 0)
    (rawLt :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat < 2 ^ 48)
    (low : 2 ^ 16 ≤
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat)
    (offsetEq :
      addressOffset (loadX0AddressInput input) =
        (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8)
    (memoryAt : ∀ k, addressOffset (loadX0AddressInput input) + k < 8 →
      ∃ byte : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + k]? =
            some byte) :
    LoadX0Chip.opcodeVal input = opcode ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 4 = 0 ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 4 ≤ 2 ^ 48 ∧
      2 ^ 16 ≤ (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat ∧
      ∃ byte₀ byte₁ byte₂ byte₃ : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat]? =
            some byte₀ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 1]? =
            some byte₁ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 2]? =
            some byte₂ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 3]? =
            some byte₃ := by
  have alignment :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 4 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 8)]
    rw [← offsetEq]
    simp only [addressOffset, loadX0AddressInput, bit₀, bit₁, ZMod.val_zero]
    omega
  have offsetAlignment : addressOffset (loadX0AddressInput input) % 4 = 0 := by
    rw [offsetEq, Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 8)]
    exact alignment
  have high :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 4 ≤ 2 ^ 48 := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero alignment
    omega
  obtain ⟨byte₀, memory₀⟩ := memoryAt 0 (by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero offsetAlignment
    omega)
  obtain ⟨byte₁, memory₁⟩ := memoryAt 1 (by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero offsetAlignment
    omega)
  obtain ⟨byte₂, memory₂⟩ := memoryAt 2 (by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero offsetAlignment
    omega)
  obtain ⟨byte₃, memory₃⟩ := memoryAt 3 (by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero offsetAlignment
    omega)
  rw [Nat.add_zero] at memory₀
  exact ⟨opcodeEq, alignment, high, low, byte₀, byte₁, byte₂, byte₃,
    memory₀, memory₁, memory₂, memory₃⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem loadX0DoubleEvidence
    (input : LoadX0Chip.Inputs (ZMod p)) (state : SailState) (opcode : ZMod p)
    (opcodeEq : LoadX0Chip.opcodeVal input = opcode)
    (bit₀ : input.offset_bit[0] = 0) (bit₁ : input.offset_bit[1] = 0)
    (bit₂ : input.offset_bit[2] = 0)
    (rawLt :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat < 2 ^ 48)
    (low : 2 ^ 16 ≤
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat)
    (offsetEq :
      addressOffset (loadX0AddressInput input) =
        (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8)
    (memoryAt : ∀ k, addressOffset (loadX0AddressInput input) + k < 8 →
      ∃ byte : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + k]? =
            some byte) :
    LoadX0Chip.opcodeVal input = opcode ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8 = 0 ∧
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 8 ≤ 2 ^ 48 ∧
      2 ^ 16 ≤ (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat ∧
      ∃ byte₀ byte₁ byte₂ byte₃ byte₄ byte₅ byte₆ byte₇ : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat]? =
            some byte₀ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 1]? =
            some byte₁ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 2]? =
            some byte₂ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 3]? =
            some byte₃ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 4]? =
            some byte₄ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 5]? =
            some byte₅ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 6]? =
            some byte₆ ∧
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 7]? =
            some byte₇ := by
  have alignment :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8 = 0 := by
    rw [← offsetEq]
    simp [addressOffset, loadX0AddressInput, bit₀, bit₁, bit₂]
  have high :
      (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + 8 ≤ 2 ^ 48 := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero alignment
    omega
  have offsetZero : addressOffset (loadX0AddressInput input) = 0 := by
    simp [addressOffset, loadX0AddressInput, bit₀, bit₁, bit₂]
  obtain ⟨byte₀, memory₀⟩ := memoryAt 0 (by omega)
  obtain ⟨byte₁, memory₁⟩ := memoryAt 1 (by omega)
  obtain ⟨byte₂, memory₂⟩ := memoryAt 2 (by omega)
  obtain ⟨byte₃, memory₃⟩ := memoryAt 3 (by omega)
  obtain ⟨byte₄, memory₄⟩ := memoryAt 4 (by omega)
  obtain ⟨byte₅, memory₅⟩ := memoryAt 5 (by omega)
  obtain ⟨byte₆, memory₆⟩ := memoryAt 6 (by omega)
  obtain ⟨byte₇, memory₇⟩ := memoryAt 7 (by omega)
  rw [Nat.add_zero] at memory₀
  exact ⟨opcodeEq, alignment, high, low, byte₀, byte₁, byte₂, byte₃,
    byte₄, byte₅, byte₆, byte₇, memory₀, memory₁, memory₂, memory₃,
    memory₄, memory₅, memory₆, memory₇⟩

omit [Fact (2 ^ 25 < p)] in
/-- Turn LoadX0's semantic chip contract and an authenticated aligned RAM cell into the exact
seven-opcode readiness disjunction consumed by its Sail bridge. The width-specific helpers above
keep the large disjunction out of the dependent whole-chip grounding proof. -/
theorem loadX0AdvanceReady_of_semanticFacts
    (input : LoadX0Chip.Inputs (ZMod p))
    (cols : LoadX0Chip.Columns (ZMod p))
    (data : ProverData (ZMod p)) (program : GuestProgram) (state : SailState)
    (spec : LoadX0Chip.Spec input cols data)
    (real : LoadX0Chip.isReal input = 1)
    (guard : input.adapter.op_a = 0)
    (pcBound : input.state.pc[0].val < 2 ^ 16)
    (baseBound : Word.isU64 input.op_b_val)
    (immediateBound : Word.isU64 input.op_c_imm)
    (memoryAt : ∀ k, addressOffset (loadX0AddressInput input) + k < 8 →
      ∃ byte : BitVec 8,
        state.mem[
          (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat + k]? =
            some byte) :
    LoadX0Chip.advanceReady input cols program state := by
  have oneHot := loadX0_oneHot input cols data spec real
  have addressFacts := AddressOperation.effectiveAddress_facts
    baseBound immediateBound (AddressOperation.validAddress_of_spec (spec.1.2.2.2 real))
  have offsetEq :
      addressOffset (loadX0AddressInput input) =
        (AddressOperation.effectiveAddress (loadX0AddressInput input)).toNat % 8 := by
    simpa only [addressOffset, loadX0AddressInput] using addressFacts.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ldGate, wordGate, halfGate, _, _⟩ := spec
  unfold LoadX0Chip.advanceReady
  refine ⟨guard, pcBound, ?_⟩
  rcases oneHot with lb | lbu | lh | lhu | lw | lwu | ld
  · apply Or.inl
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0ByteEvidence input state ((loadOpcode 1 false).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, lb.1, lb.2.1,
          lb.2.2.1, lb.2.2.2.1, lb.2.2.2.2.1, lb.2.2.2.2.2.1,
          lb.2.2.2.2.2.2]) addressFacts.1 addressFacts.2.1 offsetEq memoryAt
  · apply Or.inr
    apply Or.inl
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0ByteEvidence input state ((loadOpcode 1 true).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, lbu.1, lbu.2.1,
          lbu.2.2.1, lbu.2.2.2.1, lbu.2.2.2.2.1, lbu.2.2.2.2.2.1,
          lbu.2.2.2.2.2.2]) addressFacts.1 addressFacts.2.1 offsetEq memoryAt
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    have bit₀ : input.offset_bit[0] = 0 := by
      simpa [lh.1, lh.2.1, lh.2.2.1, lh.2.2.2.1, lh.2.2.2.2.1,
        lh.2.2.2.2.2.1, lh.2.2.2.2.2.2] using halfGate
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0HalfEvidence input state ((loadOpcode 2 false).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, lh.1, lh.2.1,
          lh.2.2.1, lh.2.2.2.1, lh.2.2.2.2.1, lh.2.2.2.2.2.1,
          lh.2.2.2.2.2.2]) bit₀ addressFacts.1 addressFacts.2.1 offsetEq memoryAt
  · apply Or.inr
    iterate 2 apply Or.inr
    apply Or.inl
    have bit₀ : input.offset_bit[0] = 0 := by
      simpa [lhu.1, lhu.2.1, lhu.2.2.1, lhu.2.2.2.1, lhu.2.2.2.2.1,
        lhu.2.2.2.2.2.1, lhu.2.2.2.2.2.2] using halfGate
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0HalfEvidence input state ((loadOpcode 2 true).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, lhu.1, lhu.2.1,
          lhu.2.2.1, lhu.2.2.2.1, lhu.2.2.2.2.1, lhu.2.2.2.2.2.1,
          lhu.2.2.2.2.2.2]) bit₀ addressFacts.1 addressFacts.2.1 offsetEq memoryAt
  · apply Or.inr
    iterate 3 apply Or.inr
    apply Or.inl
    have bit₀ : input.offset_bit[0] = 0 := by
      simpa [lw.1, lw.2.1, lw.2.2.1, lw.2.2.2.1, lw.2.2.2.2.1,
        lw.2.2.2.2.2.1, lw.2.2.2.2.2.2] using halfGate
    have bit₁ : input.offset_bit[1] = 0 := by
      simpa [lw.1, lw.2.1, lw.2.2.1, lw.2.2.2.1, lw.2.2.2.2.1,
        lw.2.2.2.2.2.1, lw.2.2.2.2.2.2] using wordGate
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0WordEvidence input state ((loadOpcode 4 false).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, lw.1, lw.2.1,
          lw.2.2.1, lw.2.2.2.1, lw.2.2.2.2.1, lw.2.2.2.2.2.1,
          lw.2.2.2.2.2.2]) bit₀ bit₁ addressFacts.1 addressFacts.2.1 offsetEq memoryAt
  · apply Or.inr
    iterate 4 apply Or.inr
    apply Or.inl
    have bit₀ : input.offset_bit[0] = 0 := by
      simpa [lwu.1, lwu.2.1, lwu.2.2.1, lwu.2.2.2.1, lwu.2.2.2.2.1,
        lwu.2.2.2.2.2.1, lwu.2.2.2.2.2.2] using halfGate
    have bit₁ : input.offset_bit[1] = 0 := by
      simpa [lwu.1, lwu.2.1, lwu.2.2.1, lwu.2.2.2.1, lwu.2.2.2.2.1,
        lwu.2.2.2.2.2.1, lwu.2.2.2.2.2.2] using wordGate
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0WordEvidence input state ((loadOpcode 4 true).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, lwu.1, lwu.2.1,
          lwu.2.2.1, lwu.2.2.2.1, lwu.2.2.2.2.1, lwu.2.2.2.2.2.1,
          lwu.2.2.2.2.2.2]) bit₀ bit₁ addressFacts.1 addressFacts.2.1 offsetEq memoryAt
  · apply Or.inr
    iterate 5 apply Or.inr
    have bit₀ : input.offset_bit[0] = 0 := by
      simpa [ld.1, ld.2.1, ld.2.2.1, ld.2.2.2.1, ld.2.2.2.2.1,
        ld.2.2.2.2.2.1, ld.2.2.2.2.2.2] using halfGate
    have bit₁ : input.offset_bit[1] = 0 := by
      simpa [ld.1, ld.2.1, ld.2.2.1, ld.2.2.2.1, ld.2.2.2.2.1,
        ld.2.2.2.2.2.1, ld.2.2.2.2.2.2] using wordGate
    have bit₂ : input.offset_bit[2] = 0 := by
      simpa [ld.1] using ldGate
    simpa only [loadX0AddressInput, AddressOperation.effectiveAddress,
      LoadX0Chip.Inputs.op_b_val, LoadX0Chip.Inputs.op_c_imm] using
      loadX0DoubleEvidence input state ((loadOpcode 8 false).toNat : ZMod p) (by
        simp [LoadX0Chip.opcodeVal, loadOpcode, Opcode.toNat, ld.1, ld.2.1,
          ld.2.2.1, ld.2.2.2.1, ld.2.2.2.2.1, ld.2.2.2.2.2.1,
          ld.2.2.2.2.2.2]) bit₀ bit₁ bit₂ addressFacts.1 addressFacts.2.1 offsetEq memoryAt

omit [Fact (2 ^ 25 < p)] in
theorem LoadX0Chip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (LoadX0Chip.circuit (p := p))
      LoadX0Chip.rowView
      (fun input cols => some (LoadX0Chip.ramAccessView input cols)) := by
  let input : Var LoadX0Chip.Inputs (ZMod p) := varFromOffset LoadX0Chip.Inputs 0
  let offset := size LoadX0Chip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
        input.is_lw + input.is_lwu + input.is_ld⟩
  let isReal := input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
    input.is_lw + input.is_lwu + input.is_ld
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.memory_access.prev_value, isReal⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, isReal, readerInput, LoadX0Chip.circuit,
      LoadX0Chip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, isReal, readerInput, LoadX0Chip.circuit, LoadX0Chip.rowView,
        LoadX0Chip.ramAccessView, LoadX0Chip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem LoadX0Chip.ramAddressContract :
    CircuitRamAddressContract (p := p) (LoadX0Chip.circuit (p := p))
      (fun input cols => some (LoadX0Chip.ramAccessView input cols))
      LoadX0Chip.isReal := by
  let input : Var LoadX0Chip.Inputs (ZMod p) := varFromOffset LoadX0Chip.Inputs 0
  let offset := size LoadX0Chip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
        input.is_lw + input.is_lwu + input.is_ld⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, LoadX0Chip.circuit, LoadX0Chip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, LoadX0Chip.circuit,
      LoadX0Chip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, LoadX0Chip.isReal, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem LoadX0Chip.immutableItypeTimestampContract :
    CircuitImmutableITypeTimestampContract (p := p) (LoadX0Chip.circuit (p := p))
      LoadX0Chip.rowView := by
  let input : Var LoadX0Chip.Inputs (ZMod p) := varFromOffset LoadX0Chip.Inputs 0
  let offset := size LoadX0Chip.Inputs
  let isReal := input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
    input.is_lw + input.is_lwu + input.is_ld
  let opcode := 29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh +
    33 * input.is_lhu + 31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld
  let readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
    ⟨input.adapter, isReal, isReal, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, opcode⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, isReal, opcode, readerInput, LoadX0Chip.circuit,
      LoadX0Chip.main, Readers.ITypeReaderImmutable.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, isReal, readerInput, LoadX0Chip.rowView,
        LoadX0Chip.isReal, LoadX0Chip.opcodeVal, Extracted.ITypeReader.toAdapterView,
        circuit_norm]

theorem loadX0Chip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨loadX0ChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded loadX0

theorem loadX0Chip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨loadX0ChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf LoadX0Chip.circuit LoadX0Chip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded loadX0

theorem loadX0Chip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨LoadX0Chip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv loadX0

theorem loadX0Chip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadX0Chip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨LoadX0Chip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ImmutableRamTimestampBounds
      (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf LoadX0Chip.circuit LoadX0Chip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact immutableRamTimestampBounds_of_contracts LoadX0Chip.circuit
    LoadX0Chip.rowView LoadX0Chip.ramAccessView LoadX0Chip.ramTimestampContract
    LoadX0Chip.immutableItypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem loadX0Chip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨LoadX0Chip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf LoadX0Chip.circuit LoadX0Chip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv loadX0 LoadX0Chip.isReal

theorem loadX0Chip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadX0ChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds loadX0

theorem loadX0Chip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadX0ChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ImmutableRamTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds loadX0

theorem loadX0Chip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadX0ChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam loadX0

omit [Fact (2 ^ 25 < p)] in
/-- LoadX0's public exposed Memory list evaluates to the immutable RAM/I-type six-message layout. -/
theorem loadX0Chip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableRamMemoryInteractions
        (LoadX0Chip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0))
          (Eval.eval env ((LoadX0Chip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0) (size LoadX0Chip.Inputs))))
        (LoadX0Chip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0))
          (Eval.eval env ((LoadX0Chip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) LoadX0Chip.Inputs 0)
            (size LoadX0Chip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues loadX0 immutableRamMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    LoadX0Chip.rowView, LoadX0Chip.ramAccessView, LoadX0Chip.isReal,
    AddressOperation.alignedValue, Extracted.ITypeReader.toAdapterView,
    LoadX0Chip.circuit, circuit_norm]

/-- Lift LoadX0's evaluated six-message list to the folded decoded-row boundary. -/
theorem loadX0Chip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = loadX0ChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableRamMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions loadX0 immutableRamMemoryInteractions

/-- LoadX0 instantiates the authenticated immutable RAM/I-type interaction shape. -/
noncomputable def loadX0Chip_immutableRamMemoryInteractionShape :
    ImmutableRamMemoryInteractionShape (loadX0ChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := loadX0Chip_typedMemoryInteractions_eq

end LoadX0

section StoreByte

/-- The StoreByte descriptor in the supported Core registry. -/
def storeByteChipDescriptor : SupportedChip p :=
  ⟨StoreByteChip.kind, StoreByteChip.circuit, rfl, [.SB], .any⟩

theorem storeByteChipDescriptor_table :
    (storeByteChipDescriptor (p := p)).table =
      (⟨StoreByteChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeByteChipDescriptor_view (input : StoreByteChip.Inputs (ZMod p))
    (output : StoreByteChip.Columns (ZMod p)) :
    (storeByteChipDescriptor (p := p)).kind.view input output =
      StoreByteChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeByteChipDescriptor_ramAccess (input : StoreByteChip.Inputs (ZMod p))
    (output : StoreByteChip.Columns (ZMod p)) :
    (storeByteChipDescriptor (p := p)).kind.ramAccess input output =
      some (StoreByteChip.ramAccessView input output) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeByteChipDescriptor_rdGuard :
    (storeByteChipDescriptor (p := p)).rdGuard = .any := rfl

theorem storeByteChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (storeByteChipDescriptor (p := p)).table.Assumptions env ↔
      StoreByteChip.Assumptions
        (circuitRowInputOf StoreByteChip.circuit env) env.data := by
  chipAssumptionsIff storeByte

omit [Fact (2 ^ 25 < p)] in
theorem storeByteAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf StoreByteChip.circuit
        StoreByteChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView env).adapter.op_c)
    (storeValue : Word.isU64
      (circuitRowInputOf StoreByteChip.circuit env).store_value) :
    StoreByteChip.Assumptions
      (circuitRowInputOf StoreByteChip.circuit env) data := by
  rw [circuitRowViewOf_eq_typed] at base immediate
  unfold StoreByteChip.Assumptions
  refine ⟨?_, ?_, fun _ => storeValue⟩
  · simpa only [StoreByteChip.Inputs.op_b_val, StoreByteChip.rowView,
      Extracted.ITypeReader.toAdapterView] using base
  · simpa only [StoreByteChip.Inputs.op_c_imm, StoreByteChip.rowView,
      Extracted.ITypeReader.toAdapterView] using immediate

theorem storeByteSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((storeByteChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    StoreByteChip.Spec
      (circuitRowInputOf StoreByteChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreByteChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold storeByteChipDescriptor at h
  exact chipSpec_of_literalDescriptor StoreByteChip.kind StoreByteChip.circuit
    rfl [.SB] .any data physical h

theorem storeByteAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : StoreByteChip.AdvanceReady
      (circuitRowInputOf StoreByteChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreByteChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((storeByteChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((storeByteChipDescriptor (p := p)).decodeRow data physical).inputs
      ((storeByteChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold storeByteChipDescriptor
  apply advanceReady_of_literalDescriptor StoreByteChip.kind StoreByteChip.circuit
    rfl [.SB] .any data physical program state
  exact h

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The two high v6.3.1 SB offset bits select one prior 16-bit cell limb. The four
read-modify-write equations add the byte-sized increment to exactly that limb. -/
theorem StoreByteChip.limbFacts
    (input : StoreByteChip.Inputs (ZMod p))
    (selection :
      (input.mem_limb - input.memory_access.prev_value[0])
          * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[1])
          * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[2])
          * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[3])
          * input.offset_bit[1] * input.offset_bit[2] = 0)
    (rmw :
      input.store_value[0] = input.memory_access.prev_value[0]
          + input.increment * (1 - input.offset_bit[1]) * (1 - input.offset_bit[2]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
          + input.increment * input.offset_bit[1] * (1 - input.offset_bit[2]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
          + input.increment * (1 - input.offset_bit[1]) * input.offset_bit[2] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
          + input.increment * input.offset_bit[1] * input.offset_bit[2])
    (bit1 : input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1)
    (bit2 : input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) :
    ∃ limb : Fin 4,
      addressOffset
          ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
            input.offset_bit[1], input.offset_bit[2], input.is_real⟩ =
        input.offset_bit[0].val + 2 * limb.val ∧
      input.mem_limb = input.memory_access.prev_value[limb] ∧
      ∀ i : Fin 4,
        input.store_value[i] =
          if i = limb then input.memory_access.prev_value[i] + input.increment
          else input.memory_access.prev_value[i] := by
  obtain ⟨select0, select1, select2, select3⟩ := selection
  obtain ⟨rmw0, rmw1, rmw2, rmw3⟩ := rmw
  rcases bit1 with bit1Zero | bit1One <;>
    rcases bit2 with bit2Zero | bit2One
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp [addressOffset, bit1Zero, bit2Zero]
    · rw [bit1Zero, bit2Zero] at select0 select1 select2 select3
      ring_nf at select0 select1 select2 select3
      exact sub_eq_zero.mp select0
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit1Zero, bit2Zero] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        assumption
  · refine ⟨2, ?_, ?_, ?_⟩
    · simp [addressOffset, bit1Zero, bit2One, ZMod.val_one]
    · rw [bit1Zero, bit2One] at select0 select1 select2 select3
      ring_nf at select0 select1 select2 select3
      have h :
          input.memory_access.prev_value[2] - input.mem_limb = 0 := by
        simpa only [sub_eq_add_neg, add_comm] using select2
      exact (sub_eq_zero.mp h).symm
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit1Zero, bit2One] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        try assumption
      all_goals exact rmw2.trans (add_comm _ _)
  · refine ⟨1, ?_, ?_, ?_⟩
    · simp [addressOffset, bit1One, bit2Zero, ZMod.val_one]
    · rw [bit1One, bit2Zero] at select0 select1 select2 select3
      ring_nf at select0 select1 select2 select3
      have h :
          input.memory_access.prev_value[1] - input.mem_limb = 0 := by
        simpa only [sub_eq_add_neg, add_comm] using select1
      exact (sub_eq_zero.mp h).symm
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit1One, bit2Zero] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        try assumption
      all_goals exact rmw1.trans (add_comm _ _)
  · refine ⟨3, ?_, ?_, ?_⟩
    · simp [addressOffset, bit1One, bit2One, ZMod.val_one]
    · rw [bit1One, bit2One] at select0 select1 select2 select3
      ring_nf at select0 select1 select2 select3
      exact sub_eq_zero.mp select3
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit1One, bit2One] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        try assumption
      all_goals exact rmw3.trans (add_comm _ _)

omit [Fact (2 ^ 25 < p)] in
/-- The v6.3.1 SB byte selectors and read-modify-write equations describe exactly one
byte replacement in the authenticated aligned cell. -/
theorem StoreByteChip.mergeFacts
    (input : StoreByteChip.Inputs (ZMod p))
    (registerLowBound : input.register_low_byte.val < 256)
    (registerHighBound : (StoreByteChip.regHigh input).val < 256)
    (memoryLowBound : input.mem_limb_low_byte.val < 256)
    (memoryHighBound : (StoreByteChip.memHigh input).val < 256)
    (selection :
      (input.mem_limb - input.memory_access.prev_value[0])
          * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[1])
          * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[2])
          * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[3])
          * input.offset_bit[1] * input.offset_bit[2] = 0)
    (increment :
      input.increment =
        (input.register_low_byte - input.mem_limb_low_byte)
            * (1 - input.offset_bit[0]) +
          256 * (input.register_low_byte - StoreByteChip.memHigh input)
            * input.offset_bit[0])
    (rmw :
      input.store_value[0] = input.memory_access.prev_value[0]
          + input.increment * (1 - input.offset_bit[1]) * (1 - input.offset_bit[2]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
          + input.increment * input.offset_bit[1] * (1 - input.offset_bit[2]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
          + input.increment * (1 - input.offset_bit[1]) * input.offset_bit[2] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
          + input.increment * input.offset_bit[1] * input.offset_bit[2])
    (bit0 : input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1)
    (bit1 : input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1)
    (bit2 : input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1)
    (priorBound : Word.isU64 input.memory_access.prev_value)
    (sourceBound : Word.isU64 input.adapter.op_a_memory.prev_value) :
    ∃ selected : Fin 8,
      addressOffset
          ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
            input.offset_bit[1], input.offset_bit[2], input.is_real⟩ =
        selected.val ∧
      Word.isU64 input.store_value ∧
      ∀ i : Fin 8,
        (wordBytes (Word.toBitVec64 input.store_value))[i] =
          if i = selected then
            (wordBytes
              (Word.toBitVec64 input.adapter.op_a_memory.prev_value))[0]
          else
            (wordBytes
              (Word.toBitVec64 input.memory_access.prev_value))[i] := by
  obtain ⟨limb, offsetEq, memSelected, merged⟩ :=
    StoreByteChip.limbFacts input selection rmw bit1 bit2
  have storedDecomp :
      input.adapter.op_a_memory.prev_value[0] =
        input.register_low_byte + StoreByteChip.regHigh input * 256 := by
    simpa only [StoreByteChip.regHigh] using
      byteQuotient_reassembles input.adapter.op_a_memory.prev_value[0] input.register_low_byte
  have memoryDecomp :
      input.mem_limb = input.mem_limb_low_byte + StoreByteChip.memHigh input * 256 := by
    simpa only [StoreByteChip.memHigh] using
      byteQuotient_reassembles input.mem_limb input.mem_limb_low_byte
  have oldDecomp :
      input.memory_access.prev_value[limb] =
        input.mem_limb_low_byte + StoreByteChip.memHigh input * 256 := by
    rw [← memSelected]
    exact memoryDecomp
  rcases bit0 with bit0Zero | bit0One
  · have incrementLow :
        input.increment = input.register_low_byte - input.mem_limb_low_byte := by
      rw [increment, bit0Zero]
      ring
    have newEq : ∀ i : Fin 4,
        input.store_value[i] =
          if i = limb then input.register_low_byte + StoreByteChip.memHigh input * 256
          else input.memory_access.prev_value[i] := by
      intro i
      rw [merged i]
      split
      · rename_i same
        subst i
        rw [incrementLow, oldDecomp]
        ring
      · rfl
    obtain ⟨selected, selectedEq, storeBound, bytes⟩ :=
      lowByteUpdateFacts input.memory_access.prev_value
        input.adapter.op_a_memory.prev_value input.store_value limb
        input.register_low_byte (StoreByteChip.regHigh input)
        input.mem_limb_low_byte (StoreByteChip.memHigh input)
        priorBound sourceBound registerLowBound registerHighBound
        memoryLowBound memoryHighBound storedDecomp oldDecomp newEq
    refine ⟨selected, ?_, storeBound, bytes⟩
    rw [offsetEq, bit0Zero, selectedEq]
    simp only [ZMod.val_zero]
    omega
  · have incrementHigh :
        input.increment = 256 * (input.register_low_byte - StoreByteChip.memHigh input) := by
      rw [increment, bit0One]
      ring
    have newEq : ∀ i : Fin 4,
        input.store_value[i] =
          if i = limb then input.mem_limb_low_byte + input.register_low_byte * 256
          else input.memory_access.prev_value[i] := by
      intro i
      rw [merged i]
      split
      · rename_i same
        subst i
        rw [incrementHigh, oldDecomp]
        ring
      · rfl
    obtain ⟨selected, selectedEq, storeBound, bytes⟩ :=
      highByteUpdateFacts input.memory_access.prev_value
        input.adapter.op_a_memory.prev_value input.store_value limb
        input.register_low_byte (StoreByteChip.regHigh input)
        input.mem_limb_low_byte (StoreByteChip.memHigh input)
        priorBound sourceBound registerLowBound registerHighBound
        memoryLowBound memoryHighBound storedDecomp oldDecomp newEq
    refine ⟨selected, ?_, storeBound, bytes⟩
    rw [offsetEq, bit0One, selectedEq]
    simp only [ZMod.val_one]
    omega

omit [Fact (2 ^ 25 < p)] in
/-- The SB read-modify-write equations alone make the pushed full-cell word canonical once the
selected prior cell and the three byte-sized values used by the update are range-bounded. Unlike
`mergeFacts`, this pre-soundness lemma intentionally does not claim byte equality with rs2. -/
private theorem StoreByteChip.storeValue_isU64_of_mergeFacts
    (input : StoreByteChip.Inputs (ZMod p))
    (registerLowBound : input.register_low_byte.val < 256)
    (memoryLowBound : input.mem_limb_low_byte.val < 256)
    (memoryHighBound : (StoreByteChip.memHigh input).val < 256)
    (selection :
      (input.mem_limb - input.memory_access.prev_value[0])
          * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[1])
          * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[2])
          * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[3])
          * input.offset_bit[1] * input.offset_bit[2] = 0)
    (increment :
      input.increment =
        (input.register_low_byte - input.mem_limb_low_byte)
            * (1 - input.offset_bit[0]) +
          256 * (input.register_low_byte - StoreByteChip.memHigh input)
            * input.offset_bit[0])
    (rmw :
      input.store_value[0] = input.memory_access.prev_value[0]
          + input.increment * (1 - input.offset_bit[1]) * (1 - input.offset_bit[2]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
          + input.increment * input.offset_bit[1] * (1 - input.offset_bit[2]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
          + input.increment * (1 - input.offset_bit[1]) * input.offset_bit[2] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
          + input.increment * input.offset_bit[1] * input.offset_bit[2])
    (bit0 : input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1)
    (bit1 : input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1)
    (bit2 : input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1)
    (priorBound : Word.isU64 input.memory_access.prev_value) :
    Word.isU64 input.store_value := by
  obtain ⟨limb, _offsetEq, memSelected, merged⟩ :=
    StoreByteChip.limbFacts input selection rmw bit1 bit2
  have memoryDecomp :
      input.mem_limb = input.mem_limb_low_byte + StoreByteChip.memHigh input * 256 := by
    simpa only [StoreByteChip.memHigh] using
      byteQuotient_reassembles input.mem_limb input.mem_limb_low_byte
  have oldDecomp :
      input.memory_access.prev_value[limb] =
        input.mem_limb_low_byte + StoreByteChip.memHigh input * 256 := by
    rw [← memSelected]
    exact memoryDecomp
  rcases bit0 with bit0Zero | bit0One
  · have incrementLow :
        input.increment = input.register_low_byte - input.mem_limb_low_byte := by
      rw [increment, bit0Zero]
      ring
    intro i
    rw [merged i]
    split
    · rename_i same
      subst i
      have newValue :
          input.memory_access.prev_value[limb] + input.increment =
            input.register_low_byte + StoreByteChip.memHigh input * 256 := by
        rw [incrementLow, oldDecomp]
        ring
      rw [newValue, val_lo_add_hi registerLowBound memoryHighBound]
      omega
    · exact priorBound i
  · have incrementHigh :
        input.increment = 256 * (input.register_low_byte - StoreByteChip.memHigh input) := by
      rw [increment, bit0One]
      ring
    intro i
    rw [merged i]
    split
    · rename_i same
      subst i
      have newValue :
          input.memory_access.prev_value[limb] + input.increment =
            input.mem_limb_low_byte + input.register_low_byte * 256 := by
        rw [incrementHigh, oldDecomp]
        ring
      rw [newValue, val_lo_add_hi memoryLowBound registerLowBound]
      omega
    · exact priorBound i

omit [Fact (2 ^ 25 < p)] in
/-- StoreByte's semantic row writes rs2's low byte into the selector-chosen byte of the
authenticated RAM cell. -/
theorem storeByteChip_storeFacts
    (input : StoreByteChip.Inputs (ZMod p))
    (cols : StoreByteChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (real : (StoreByteChip.rowView input cols).is_real = 1)
    (spec : StoreByteChip.Spec input cols data) :
    ∃ write : Trace.MemWrite (ZMod p),
      (StoreByteChip.rowView input cols).commit = Trace.CommitEffect.store write ∧
      write.InCell (ramCellOfAccess (StoreByteChip.ramAccessView input cols)) ∧
      RamCellUpdate write (ramCellOfAccess (StoreByteChip.ramAccessView input cols))
        (Word.toBitVec64 (StoreByteChip.ramAccessView input cols).priorValue)
        (Word.toBitVec64 (StoreByteChip.ramAccessView input cols).newValue) := by
  let addressInput : AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
      input.offset_bit[1], input.offset_bit[2], input.is_real⟩
  let access := StoreByteChip.ramAccessView input cols
  let write : Trace.MemWrite (ZMod p) :=
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 1⟩
  obtain ⟨addressSpec, memorySpec, readerSpec, byteBounds, selection,
    increment, rmw, _gate⟩ := spec
  have realInput : input.is_real = 1 := by
    simpa only [StoreByteChip.rowView] using real
  have addressEq :
      access.address = AddressOperation.alignedValue addressInput cols.address_operation := by
    rfl
  have address :
      write.addrNat = (ramCellOfAccess access).baseAddr.toNat + addressOffset addressInput := by
    have raw := rawAddress_eq_ramCellBase_add_offset
      addressInput cols.address_operation access addressEq (addressSpec.2.2.2 realInput)
    simpa only [write, Trace.MemWrite.addrNat, address48Nat] using raw
  have priorBound : Word.isU64 input.memory_access.prev_value :=
    (memorySpec realInput).2.2.2.2.2.1
  have sourceBound : Word.isU64 input.adapter.op_a_memory.prev_value :=
    (readerSpec.2.2.2.2.2 realInput).1
  obtain ⟨registerLowBound, registerHighBound,
    memoryLowBound, memoryHighBound⟩ := byteBounds realInput
  have bit0 : input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1 := addressSpec.1
  have bit1 : input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1 := addressSpec.2.1
  have bit2 : input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1 := addressSpec.2.2.1
  obtain ⟨selected, offsetEq, _storeBound, bytes⟩ :=
    StoreByteChip.mergeFacts input registerLowBound registerHighBound
      memoryLowBound memoryHighBound selection increment rmw bit0 bit1 bit2
      priorBound sourceBound
  have offsetEq' : addressOffset addressInput = selected.val := by
    simpa only [addressInput] using offsetEq
  have addressSelected :
      write.addrNat = (ramCellOfAccess access).baseAddr.toNat + selected.val := by
    simpa only [offsetEq'] using address
  refine ⟨write, rfl,
    Trace.MemWrite.inCell_of_address_width
      (offset := selected.val) (width := 1) addressSelected rfl (by
      have := selected.isLt
      omega), ?_⟩
  apply ramCellUpdate_of_patchedCell (offset := selected.val) (width := 1) addressSelected rfl
  symm
  simpa only [access, write, StoreByteChip.ramAccessView] using
    patchedCellBytes_one cols.address_operation.addr_operation.value
      input.memory_access.prev_value input.adapter.op_a_memory.prev_value
      input.store_value selected bytes

omit [Fact (2 ^ 25 < p)] in
/-- The two direct SB byte pulls range-check the low/high decomposition of rs2's low limb and
the selected prior-memory limb. This physical fact is available before parent-chip soundness. -/
theorem StoreByteChip.byteBounds_of_mainGuarantees
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (guarantees : ((StoreByteChip.main input).operations offset).ChannelGuarantees
      byteChannel.toRaw env)
    (real : Expression.eval env input.is_real = 1) :
    (Expression.eval env input.register_low_byte).val < 256 ∧
      ((Expression.eval env input.adapter.op_a_memory.prev_value[0] -
        Expression.eval env input.register_low_byte) * (256 : ZMod p)⁻¹).val < 256 ∧
      (Expression.eval env input.mem_limb_low_byte).val < 256 ∧
      ((Expression.eval env input.mem_limb -
        Expression.eval env input.mem_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256 := by
  let registerPull := byteChannel.pulledIf input.is_real
    (⟨3, 0, input.register_low_byte,
      (input.adapter.op_a_memory.prev_value[0] - input.register_low_byte) *
        Expression.const ((256 : ZMod p)⁻¹)⟩ : ByteRow (Expression (ZMod p)))
  let memoryPull := byteChannel.pulledIf input.is_real
    (⟨3, 0, input.mem_limb_low_byte,
      (input.mem_limb - input.mem_limb_low_byte) *
        Expression.const ((256 : ZMod p)⁻¹)⟩ : ByteRow (Expression (ZMod p)))
  have registerMem :
      registerPull.toRaw ∈
        ((StoreByteChip.main input).operations offset).shallowInteractions := by
    simp only [StoreByteChip.main, registerPull, circuit_norm, Operations.shallowInteractions]
  have memoryMem :
      memoryPull.toRaw ∈ ((StoreByteChip.main input).operations offset).shallowInteractions := by
    simp only [StoreByteChip.main, memoryPull, circuit_norm, Operations.shallowInteractions]
  have registerRaw := guarantees registerPull.toRaw
    (Operations.mem_interactions_of_mem_shallowInteractions registerMem) (by rfl)
  have memoryRaw := guarantees memoryPull.toRaw
    (Operations.mem_interactions_of_mem_shallowInteractions memoryMem) (by rfl)
  have registerGuarantee := (ChannelInteraction.toRaw_guarantees env registerPull).mp registerRaw
  have memoryGuarantee := (ChannelInteraction.toRaw_guarantees env memoryPull).mp memoryRaw
  have negReal : -(Expression.eval env input.is_real) = -1 := by rw [real]
  have registerMult :
      (fun x => Expression.eval env x) registerPull.toRaw.mult = -1 := by
    simpa only [registerPull, circuit_norm] using negReal
  have memoryMult :
      (fun x => Expression.eval env x) memoryPull.toRaw.mult = -1 := by
    simpa only [memoryPull, circuit_norm] using negReal
  have registerSpec : ByteRowSpec (Eval.eval env registerPull.msg) := by
    have guarantee := registerGuarantee (by rfl) (by simpa only [circuit_norm] using registerMult)
    change ByteRowSpec (Eval.eval env registerPull.msg) at guarantee
    exact guarantee
  have memorySpec : ByteRowSpec (Eval.eval env memoryPull.msg) := by
    have guarantee := memoryGuarantee (by rfl) (by simpa only [circuit_norm] using memoryMult)
    change ByteRowSpec (Eval.eval env memoryPull.msg) at guarantee
    exact guarantee
  have registerMsgEq : Eval.eval env registerPull.msg =
      (⟨3, 0, Expression.eval env input.register_low_byte,
        (Expression.eval env input.adapter.op_a_memory.prev_value[0] -
          Expression.eval env input.register_low_byte) * (256 : ZMod p)⁻¹⟩ :
        ByteRow (ZMod p)) := by
    dsimp only [registerPull, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      eval_sub, Expression.eval]
  have memoryMsgEq : Eval.eval env memoryPull.msg =
      (⟨3, 0, Expression.eval env input.mem_limb_low_byte,
        (Expression.eval env input.mem_limb -
          Expression.eval env input.mem_limb_low_byte) * (256 : ZMod p)⁻¹⟩ :
        ByteRow (ZMod p)) := by
    dsimp only [memoryPull, Channel.pulledIf, pulledIf]
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.structEvalLiteralProc,
      eval_sub, Expression.eval]
  rw [registerMsgEq] at registerSpec
  rw [memoryMsgEq] at memorySpec
  have registerBounds := (byteRowSpec_u8range_pair _ _).mp registerSpec
  have memoryBounds := (byteRowSpec_u8range_pair _ _).mp memorySpec
  exact ⟨registerBounds.1, registerBounds.2, memoryBounds.1, memoryBounds.2⟩

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteSelect0Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    (input.mem_limb - input.memory_access.prev_value[0])
        * (input.offset_bit[1] - (1 : Expression (ZMod p)))
        * (input.offset_bit[2] - (1 : Expression (ZMod p))) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 4 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      ((input.mem_limb - input.memory_access.prev_value[0])
        * (input.offset_bit[1] - (1 : Expression (ZMod p)))
        * (input.offset_bit[2] - (1 : Expression (ZMod p)))) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteSelect1Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    (input.mem_limb - input.memory_access.prev_value[1])
        * input.offset_bit[1]
        * (input.offset_bit[2] - (1 : Expression (ZMod p))) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 5 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      ((input.mem_limb - input.memory_access.prev_value[1])
        * input.offset_bit[1]
        * (input.offset_bit[2] - (1 : Expression (ZMod p)))) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteSelect2Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    (input.mem_limb - input.memory_access.prev_value[2])
        * (input.offset_bit[1] - (1 : Expression (ZMod p)))
        * input.offset_bit[2] - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 6 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      ((input.mem_limb - input.memory_access.prev_value[2])
        * (input.offset_bit[1] - (1 : Expression (ZMod p)))
        * input.offset_bit[2]) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteSelect3Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    (input.mem_limb - input.memory_access.prev_value[3])
        * input.offset_bit[1] * input.offset_bit[2] - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 7 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      ((input.mem_limb - input.memory_access.prev_value[3])
        * input.offset_bit[1] * input.offset_bit[2]) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteIncrementConstraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.increment -
        ((input.register_low_byte - input.mem_limb_low_byte)
            * ((1 : Expression (ZMod p)) - input.offset_bit[0]) +
          Expression.const (256 : ZMod p) * (input.register_low_byte -
            (input.mem_limb - input.mem_limb_low_byte) *
              Expression.const ((256 : ZMod p)⁻¹)) * input.offset_bit[0]) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 8 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.increment -
        ((input.register_low_byte - input.mem_limb_low_byte)
            * ((1 : Expression (ZMod p)) - input.offset_bit[0]) +
          Expression.const (256 : ZMod p) * (input.register_low_byte -
            (input.mem_limb - input.mem_limb_low_byte) *
              Expression.const ((256 : ZMod p)⁻¹)) * input.offset_bit[0])) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteRmw0Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[0] -
        (input.memory_access.prev_value[0] +
          input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) *
            ((1 : Expression (ZMod p)) - input.offset_bit[2])) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 9 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[0] -
        (input.memory_access.prev_value[0] +
          input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) *
            ((1 : Expression (ZMod p)) - input.offset_bit[2]))) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteRmw1Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[1] -
        (input.memory_access.prev_value[1] +
          input.increment * input.offset_bit[1] *
            ((1 : Expression (ZMod p)) - input.offset_bit[2])) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 10 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[1] -
        (input.memory_access.prev_value[1] +
          input.increment * input.offset_bit[1] *
            ((1 : Expression (ZMod p)) - input.offset_bit[2]))) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteRmw2Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[2] -
        (input.memory_access.prev_value[2] +
          input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) *
            input.offset_bit[2]) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 11 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[2] -
        (input.memory_access.prev_value[2] +
          input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) *
            input.offset_bit[2])) 0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteRmw3Constraint_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[3] -
        (input.memory_access.prev_value[3] +
          input.increment * input.offset_bit[1] * input.offset_bit[2]) - 0 ∈
      ((StoreByteChip.main input).operations offset).constraints := by
  simp only [StoreByteChip.main, circuit_norm]
  iterate 12 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[3] -
        (input.memory_access.prev_value[3] +
          input.increment * input.offset_bit[1] * input.offset_bit[2])) 0 _

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- Scalar projections of an evaluated SB input agree with direct expression evaluation.
`ProvableStruct.eval` deliberately preserves component boundaries, so these four projections are
made explicit once instead of repeatedly unfolding the derived structure instance. -/
private theorem StoreByteChip.evalScalarFields
    (input : Var StoreByteChip.Inputs (ZMod p)) (env : Environment (ZMod p)) :
    Expression.eval env input.mem_limb = (Eval.eval env input).mem_limb ∧
      Expression.eval env input.mem_limb_low_byte =
        (Eval.eval env input).mem_limb_low_byte ∧
      Expression.eval env input.register_low_byte =
        (Eval.eval env input).register_low_byte ∧
      Expression.eval env input.increment = (Eval.eval env input).increment ∧
      Expression.eval env input.is_real = (Eval.eval env input).is_real := by
  rcases input with ⟨isReal, state, adapter, memoryAccess, offsetBit,
    memLimb, memLow, registerLow, increment, storeValue⟩
  let row : Var StoreByteChip.Inputs (ZMod p) :=
    ⟨isReal, state, adapter, memoryAccess, offsetBit, memLimb, memLow,
      registerLow, increment, storeValue⟩
  have evaluated := ProvableStruct.eval_var_eq_eval env row
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have field := congrArg StoreByteChip.Inputs.mem_limb evaluated
    simp only [ProvableStruct.eval, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.fromComponents] at field
    change (Eval.eval env row).mem_limb = Eval.eval env memLimb at field
    rw [CircuitType.eval_expr] at field
    exact field.symm
  · have field := congrArg StoreByteChip.Inputs.mem_limb_low_byte evaluated
    simp only [ProvableStruct.eval, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.fromComponents] at field
    change (Eval.eval env row).mem_limb_low_byte = Eval.eval env memLow at field
    rw [CircuitType.eval_expr] at field
    exact field.symm
  · have field := congrArg StoreByteChip.Inputs.register_low_byte evaluated
    simp only [ProvableStruct.eval, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.fromComponents] at field
    change (Eval.eval env row).register_low_byte = Eval.eval env registerLow at field
    rw [CircuitType.eval_expr] at field
    exact field.symm
  · have field := congrArg StoreByteChip.Inputs.increment evaluated
    simp only [ProvableStruct.eval, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.fromComponents] at field
    change (Eval.eval env row).increment = Eval.eval env increment at field
    rw [CircuitType.eval_expr] at field
    exact field.symm
  · have field := congrArg StoreByteChip.Inputs.is_real evaluated
    simp only [ProvableStruct.eval, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.fromComponents] at field
    change (Eval.eval env row).is_real = Eval.eval env isReal at field
    rw [CircuitType.eval_expr] at field
    exact field.symm

omit [Fact (2 ^ 25 < p)] in
/-- Project SB's four limb selectors, increment identity, and four read-modify-write equations
from the exact folded chip constraints. -/
theorem StoreByteChip.rawFacts_of_mainConstraints
    (inputVar : Var StoreByteChip.Inputs (ZMod p))
    (input : StoreByteChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (inputEq : Eval.eval env inputVar = input)
    (constraints : Operations.ConstraintsHold env
      ((StoreByteChip.main inputVar).operations offset)) :
    ((input.mem_limb - input.memory_access.prev_value[0])
        * (input.offset_bit[1] - (1 : ZMod p))
        * (input.offset_bit[2] - (1 : ZMod p)) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[1])
        * input.offset_bit[1] * (input.offset_bit[2] - (1 : ZMod p)) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[2])
        * (input.offset_bit[1] - (1 : ZMod p)) * input.offset_bit[2] = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[3])
        * input.offset_bit[1] * input.offset_bit[2] = 0) ∧
    input.increment =
      (input.register_low_byte - input.mem_limb_low_byte)
          * ((1 : ZMod p) - input.offset_bit[0]) +
        (256 : ZMod p) * (input.register_low_byte - StoreByteChip.memHigh input)
          * input.offset_bit[0] ∧
    (input.store_value[0] = input.memory_access.prev_value[0]
        + input.increment * ((1 : ZMod p) - input.offset_bit[1])
          * ((1 : ZMod p) - input.offset_bit[2]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
        + input.increment * input.offset_bit[1]
          * ((1 : ZMod p) - input.offset_bit[2]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
        + input.increment * ((1 : ZMod p) - input.offset_bit[1])
          * input.offset_bit[2] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
        + input.increment * input.offset_bit[1] * input.offset_bit[2]) := by
  have select0 := constraints.1 _ (storeByteSelect0Constraint_mem inputVar offset)
  have select1 := constraints.1 _ (storeByteSelect1Constraint_mem inputVar offset)
  have select2 := constraints.1 _ (storeByteSelect2Constraint_mem inputVar offset)
  have select3 := constraints.1 _ (storeByteSelect3Constraint_mem inputVar offset)
  have increment := constraints.1 _ (storeByteIncrementConstraint_mem inputVar offset)
  have rmw0 := constraints.1 _ (storeByteRmw0Constraint_mem inputVar offset)
  have rmw1 := constraints.1 _ (storeByteRmw1Constraint_mem inputVar offset)
  have rmw2 := constraints.1 _ (storeByteRmw2Constraint_mem inputVar offset)
  have rmw3 := constraints.1 _ (storeByteRmw3Constraint_mem inputVar offset)
  simp only [eval_sub, Expression.eval, sub_zero] at select0 select1 select2 select3
  simp only [eval_sub, Expression.eval, sub_zero] at increment rmw0 rmw1 rmw2 rmw3
  have evalStore :
      Eval.eval env inputVar.store_value = (Eval.eval env inputVar).store_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapStore := evalStore.trans (congrArg StoreByteChip.Inputs.store_value inputEq)
  rw [CircuitType.eval_var_fields] at hmapStore
  have evalPriorWord :
      Eval.eval env inputVar.memory_access.prev_value =
        (Eval.eval env inputVar).memory_access.prev_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    have hMemory :
        (ProvableStruct.eval env inputVar).memory_access =
          Eval.eval env inputVar.memory_access := rfl
    rw [hMemory, ProvableStruct.eval_eq_eval]
    rfl
  have hmapPrior := evalPriorWord.trans (congrArg
    (fun x : StoreByteChip.Inputs (ZMod p) => x.memory_access.prev_value) inputEq)
  rw [CircuitType.eval_var_fields] at hmapPrior
  have evalOffsetWord :
      Eval.eval env inputVar.offset_bit = (Eval.eval env inputVar).offset_bit := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapOffset := evalOffsetWord.trans (congrArg StoreByteChip.Inputs.offset_bit inputEq)
  rw [CircuitType.eval_var_fields] at hmapOffset
  have evalStoreAt : ∀ i (hi : i < 4),
      Expression.eval env inputVar.store_value[i] = input.store_value[i] :=
    fun i hi => by rw [← hmapStore]; simp only [Vector.getElem_map]
  have evalPrior : ∀ i (hi : i < 4),
      Expression.eval env inputVar.memory_access.prev_value[i] =
        input.memory_access.prev_value[i] :=
    fun i hi => by rw [← hmapPrior]; simp only [Vector.getElem_map]
  have evalOffset : ∀ i (hi : i < 3),
      Expression.eval env inputVar.offset_bit[i] = input.offset_bit[i] :=
    fun i hi => by rw [← hmapOffset]; simp only [Vector.getElem_map]
  obtain ⟨evalMemLimbField, evalMemLowField,
    evalRegisterLowField, evalIncrementField, _evalRealField⟩ :=
    StoreByteChip.evalScalarFields inputVar env
  have evalMemLimb :
      Expression.eval env inputVar.mem_limb = input.mem_limb :=
    evalMemLimbField.trans (congrArg StoreByteChip.Inputs.mem_limb inputEq)
  have evalMemLow :
      Expression.eval env inputVar.mem_limb_low_byte = input.mem_limb_low_byte :=
    evalMemLowField.trans (congrArg StoreByteChip.Inputs.mem_limb_low_byte inputEq)
  have evalRegisterLow :
      Expression.eval env inputVar.register_low_byte = input.register_low_byte :=
    evalRegisterLowField.trans (congrArg StoreByteChip.Inputs.register_low_byte inputEq)
  have evalIncrement :
      Expression.eval env inputVar.increment = input.increment :=
    evalIncrementField.trans (congrArg StoreByteChip.Inputs.increment inputEq)
  simp only [
    evalPrior 0 (by omega), evalPrior 1 (by omega),
    evalPrior 2 (by omega), evalPrior 3 (by omega),
    evalOffset 1 (by omega), evalOffset 2 (by omega),
    evalMemLimb] at select0 select1 select2 select3
  simp only [evalOffset 0 (by omega), evalMemLimb, evalMemLow,
    evalRegisterLow, evalIncrement] at increment
  simp only [evalStoreAt 0 (by omega), evalStoreAt 1 (by omega),
    evalStoreAt 2 (by omega), evalStoreAt 3 (by omega),
    evalPrior 0 (by omega), evalPrior 1 (by omega),
    evalPrior 2 (by omega), evalPrior 3 (by omega),
    evalOffset 1 (by omega), evalOffset 2 (by omega),
    evalIncrement] at rmw0 rmw1 rmw2 rmw3
  exact ⟨⟨(by simpa using select0), (by simpa using select1),
      (by simpa using select2), (by simpa using select3)⟩,
    sub_eq_zero.mp (by
      simpa only [StoreByteChip.memHigh] using increment),
    ⟨sub_eq_zero.mp (by simpa using rmw0),
      sub_eq_zero.mp (by simpa using rmw1),
      sub_eq_zero.mp (by simpa using rmw2),
      sub_eq_zero.mp rmw3⟩⟩

private def storeByteAddressInput
    (input : StoreByteChip.Inputs (Expression (ZMod p))) :
    AddressOperation.Inputs (Expression (ZMod p)) :=
  ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
    input.offset_bit[1], input.offset_bit[2], input.is_real⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem storeByteAddressInput_offsetBit0
    (env : Environment (ZMod p))
    (input : StoreByteChip.Inputs (Expression (ZMod p))) :
    Expression.eval env (storeByteAddressInput input).offset_bit0 =
      Expression.eval env input.offset_bit[0] := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem storeByteAddressInput_offsetBit1
    (env : Environment (ZMod p))
    (input : StoreByteChip.Inputs (Expression (ZMod p))) :
    Expression.eval env (storeByteAddressInput input).offset_bit1 =
      Expression.eval env input.offset_bit[1] := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem storeByteAddressInput_offsetBit2
    (env : Environment (ZMod p))
    (input : StoreByteChip.Inputs (Expression (ZMod p))) :
    Expression.eval env (storeByteAddressInput input).offset_bit2 =
      Expression.eval env input.offset_bit[2] := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem storeByteAddress_mem
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset, (AddressOperation.circuit (p := p)).toSubcircuit offset
      (storeByteAddressInput input)⟩ ∈
        ((StoreByteChip.main input).operations offset).subcircuits := by
  simp only [StoreByteChip.main, storeByteAddressInput,
    AddressOperation.circuit, circuit_norm, Nat.add_zero]

omit [Fact (2 ^ 25 < p)] in
/-- SB's full-cell write word is range-canonical before parent-chip soundness is opened.
The proof uses only the exact folded constraints, the two direct Byte pulls, and the grounded
prior Memory word. -/
theorem StoreByteChip.storeValue_isU64_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨StoreByteChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (guarantees :
      (⟨StoreByteChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw env)
    (real :
      ((⟨StoreByteChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).is_real = 1)
    (prior : Word.isU64
      ((⟨StoreByteChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).memory_access.prev_value) :
    Word.isU64
      ((⟨StoreByteChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).store_value := by
  let input : Var StoreByteChip.Inputs (ZMod p) := varFromOffset StoreByteChip.Inputs 0
  let offset := size StoreByteChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) := storeByteAddressInput input
  let component : Component (ZMod p) := ⟨StoreByteChip.circuit⟩
  have rowConstraints : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have mainConstraints :
      ((StoreByteChip.main input).operations offset).ConstraintsHold env := by
    exact rowConstraints
  have rowGuarantees :
      component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have mainGuarantees :
      ((StoreByteChip.main input).operations offset).ChannelGuarantees byteChannel.toRaw env := by
    exact rowGuarantees
  have addressConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((StoreByteChip.main input).operations offset) AddressOperation.circuit
    addressInput offset (storeByteAddress_mem input offset) mainConstraints
  have offsetBools :=
    AddressOperation.offsetBits_bool_of_constraints addressInput offset env addressConstraints
  have inputEq : Eval.eval env input = component.rowInput env :=
    eval_varFromOffset_valueFromOffset StoreByteChip.Inputs 0 env
  obtain ⟨evalMemLimbField, evalMemLowField, evalRegisterLowField,
    _evalIncrementField, evalRealField⟩ :=
    StoreByteChip.evalScalarFields input env
  have evalMemLimb :
      Expression.eval env input.mem_limb = (component.rowInput env).mem_limb :=
    evalMemLimbField.trans (congrArg StoreByteChip.Inputs.mem_limb inputEq)
  have evalMemLow :
      Expression.eval env input.mem_limb_low_byte = (component.rowInput env).mem_limb_low_byte :=
    evalMemLowField.trans (congrArg StoreByteChip.Inputs.mem_limb_low_byte inputEq)
  have evalRegisterLow :
      Expression.eval env input.register_low_byte = (component.rowInput env).register_low_byte :=
    evalRegisterLowField.trans (congrArg StoreByteChip.Inputs.register_low_byte inputEq)
  have evalReal :
      Expression.eval env input.is_real = (component.rowInput env).is_real :=
    evalRealField.trans (congrArg StoreByteChip.Inputs.is_real inputEq)
  have byteBounds := StoreByteChip.byteBounds_of_mainGuarantees
    input offset env mainGuarantees (evalReal.trans real)
  obtain ⟨registerLowBound, _registerHighBound, memoryLowBound, memoryHighBound⟩ := byteBounds
  rw [evalRegisterLow] at registerLowBound
  rw [evalMemLow] at memoryLowBound
  rw [evalMemLimb, evalMemLow] at memoryHighBound
  have rawFacts := StoreByteChip.rawFacts_of_mainConstraints
    input (component.rowInput env) offset env inputEq mainConstraints
  obtain ⟨selection, increment, rmw⟩ := rawFacts
  have evalOffsetWord :
      Eval.eval env input.offset_bit = (Eval.eval env input).offset_bit := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapOffset := evalOffsetWord.trans (congrArg StoreByteChip.Inputs.offset_bit inputEq)
  rw [CircuitType.eval_var_fields] at hmapOffset
  have evalOffset : ∀ i (hi : i < 3),
      Expression.eval env input.offset_bit[i] = (component.rowInput env).offset_bit[i] :=
    fun i hi => by rw [← hmapOffset]; simp only [Vector.getElem_map]
  have bit0 :
      (component.rowInput env).offset_bit[0] = 0 ∨
        (component.rowInput env).offset_bit[0] = 1 := by
    have raw := offsetBools.1
    rw [storeByteAddressInput_offsetBit0 env input, evalOffset 0 (by omega)] at raw
    exact raw
  have bit1 :
      (component.rowInput env).offset_bit[1] = 0 ∨
        (component.rowInput env).offset_bit[1] = 1 := by
    have raw := offsetBools.2.1
    rw [storeByteAddressInput_offsetBit1 env input, evalOffset 1 (by omega)] at raw
    exact raw
  have bit2 :
      (component.rowInput env).offset_bit[2] = 0 ∨
        (component.rowInput env).offset_bit[2] = 1 := by
    have raw := offsetBools.2.2
    rw [storeByteAddressInput_offsetBit2 env input, evalOffset 2 (by omega)] at raw
    exact raw
  exact StoreByteChip.storeValue_isU64_of_mergeFacts
    (component.rowInput env) registerLowBound memoryLowBound
    (by simpa only [StoreByteChip.memHigh] using memoryHighBound)
    (by simpa using selection) (by simpa using increment) (by simpa using rmw)
    bit0 bit1 bit2 prior

omit [Fact (2 ^ 25 < p)] in
theorem StoreByteChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (StoreByteChip.circuit (p := p))
      StoreByteChip.rowView
      (fun input cols => some (StoreByteChip.ramAccessView input cols)) := by
  let input : Var StoreByteChip.Inputs (ZMod p) := varFromOffset StoreByteChip.Inputs 0
  let offset := size StoreByteChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], input.is_real⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.store_value, input.is_real⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, StoreByteChip.circuit,
      StoreByteChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, StoreByteChip.circuit, StoreByteChip.rowView,
        StoreByteChip.ramAccessView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreByteChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (StoreByteChip.circuit (p := p))
      (fun input cols => some (StoreByteChip.ramAccessView input cols))
      (fun input => input.is_real) := by
  let input : Var StoreByteChip.Inputs (ZMod p) := varFromOffset StoreByteChip.Inputs 0
  let offset := size StoreByteChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], input.is_real⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, StoreByteChip.circuit, StoreByteChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, StoreByteChip.circuit,
      StoreByteChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreByteChip.immutableItypeTimestampContract :
    CircuitImmutableITypeTimestampContract (p := p) (StoreByteChip.circuit (p := p))
      StoreByteChip.rowView := by
  let input : Var StoreByteChip.Inputs (ZMod p) := varFromOffset StoreByteChip.Inputs 0
  let offset := size StoreByteChip.Inputs
  let readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 36⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, StoreByteChip.circuit, StoreByteChip.main,
      Readers.ITypeReaderImmutable.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, StoreByteChip.rowView,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem storeByteChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨storeByteChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded storeByte

theorem storeByteChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨storeByteChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf StoreByteChip.circuit StoreByteChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded storeByte

theorem storeByteChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨StoreByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv storeByte

theorem storeByteChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨StoreByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ImmutableRamTimestampBounds
      (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf StoreByteChip.circuit StoreByteChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact immutableRamTimestampBounds_of_contracts StoreByteChip.circuit
    StoreByteChip.rowView StoreByteChip.ramAccessView StoreByteChip.ramTimestampContract
    StoreByteChip.immutableItypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem storeByteChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreByteChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf StoreByteChip.circuit StoreByteChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv storeByte (fun input => input.is_real)

theorem storeByteChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeByteChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds storeByte

theorem storeByteChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeByteChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ImmutableRamTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds storeByte

theorem storeByteChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeByteChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam storeByte

omit [Fact (2 ^ 25 < p)] in
/-- StoreByte's public exposed Memory list evaluates to the immutable RAM/I-type layout. -/
theorem storeByteChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨StoreByteChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableRamMemoryInteractions
        (StoreByteChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreByteChip.Inputs 0))
          (Eval.eval env ((StoreByteChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreByteChip.Inputs 0)
            (size StoreByteChip.Inputs))))
        (StoreByteChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreByteChip.Inputs 0))
          (Eval.eval env ((StoreByteChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreByteChip.Inputs 0)
            (size StoreByteChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues storeByte immutableRamMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    StoreByteChip.rowView, StoreByteChip.ramAccessView, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, StoreByteChip.circuit, circuit_norm]

/-- Lift StoreByte's evaluated six-message list to the folded decoded-row boundary. -/
theorem storeByteChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeByteChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableRamMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions storeByte immutableRamMemoryInteractions

/-- StoreByte instantiates the authenticated immutable RAM/I-type interaction shape. -/
noncomputable def storeByteChip_immutableRamMemoryInteractionShape :
    ImmutableRamMemoryInteractionShape (storeByteChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := storeByteChip_typedMemoryInteractions_eq

end StoreByte

section StoreHalf

/-- The StoreHalf descriptor in the supported Core registry. -/
def storeHalfChipDescriptor : SupportedChip p :=
  ⟨StoreHalfChip.kind, StoreHalfChip.circuit, rfl, [.SH], .any⟩

theorem storeHalfChipDescriptor_table :
    (storeHalfChipDescriptor (p := p)).table =
      (⟨StoreHalfChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeHalfChipDescriptor_view (input : StoreHalfChip.Inputs (ZMod p))
    (output : StoreHalfChip.Columns (ZMod p)) :
    (storeHalfChipDescriptor (p := p)).kind.view input output =
      StoreHalfChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeHalfChipDescriptor_ramAccess (input : StoreHalfChip.Inputs (ZMod p))
    (output : StoreHalfChip.Columns (ZMod p)) :
    (storeHalfChipDescriptor (p := p)).kind.ramAccess input output =
      some (StoreHalfChip.ramAccessView input output) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeHalfChipDescriptor_rdGuard :
    (storeHalfChipDescriptor (p := p)).rdGuard = .any := rfl

theorem storeHalfChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (storeHalfChipDescriptor (p := p)).table.Assumptions env ↔
      StoreHalfChip.Assumptions
        (circuitRowInputOf StoreHalfChip.circuit env) env.data := by
  chipAssumptionsIff storeHalf

omit [Fact (2 ^ 25 < p)] in
theorem storeHalfAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf StoreHalfChip.circuit
        StoreHalfChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView env).adapter.op_c)
    (storeValue : Word.isU64
      (circuitRowInputOf StoreHalfChip.circuit env).store_value) :
    StoreHalfChip.Assumptions
      (circuitRowInputOf StoreHalfChip.circuit env) data := by
  rw [circuitRowViewOf_eq_typed] at base immediate
  unfold StoreHalfChip.Assumptions
  refine ⟨?_, ?_, fun _ => storeValue⟩
  · simpa only [StoreHalfChip.Inputs.op_b_val, StoreHalfChip.rowView,
      Extracted.ITypeReader.toAdapterView] using base
  · simpa only [StoreHalfChip.Inputs.op_c_imm, StoreHalfChip.rowView,
      Extracted.ITypeReader.toAdapterView] using immediate

theorem storeHalfSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((storeHalfChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    StoreHalfChip.Spec
      (circuitRowInputOf StoreHalfChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreHalfChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold storeHalfChipDescriptor at h
  exact chipSpec_of_literalDescriptor StoreHalfChip.kind StoreHalfChip.circuit
    rfl [.SH] .any data physical h

theorem storeHalfAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : StoreHalfChip.AdvanceReady
      (circuitRowInputOf StoreHalfChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreHalfChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((storeHalfChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((storeHalfChipDescriptor (p := p)).decodeRow data physical).inputs
      ((storeHalfChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold storeHalfChipDescriptor
  apply advanceReady_of_literalDescriptor StoreHalfChip.kind StoreHalfChip.circuit
    rfl [.SH] .any data physical program state
  exact h

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The two v6.3.1 SH selector bits identify one 16-bit cell limb, and the four read-modify-write
equations replace exactly that limb with rs2's low limb. -/
theorem StoreHalfChip.mergeFacts
    (input : StoreHalfChip.Inputs (ZMod p))
    (rmw :
      input.store_value[0] = input.memory_access.prev_value[0]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0])
            * (1 - input.offset_bit[0]) * (1 - input.offset_bit[1]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[1])
            * input.offset_bit[0] * (1 - input.offset_bit[1]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2])
            * (1 - input.offset_bit[0]) * input.offset_bit[1] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[3])
            * input.offset_bit[0] * input.offset_bit[1])
    (bit0 : input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1)
    (bit1 : input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) :
    ∃ selected : Fin 4,
      addressOffset
          ⟨input.op_b_val, input.op_c_imm, 0,
            input.offset_bit[0], input.offset_bit[1], input.is_real⟩ =
        2 * selected.val ∧
      ∀ i : Fin 4,
        input.store_value[i] =
          if i = selected then input.adapter.op_a_memory.prev_value[0]
          else input.memory_access.prev_value[i] := by
  obtain ⟨rmw0, rmw1, rmw2, rmw3⟩ := rmw
  rcases bit0 with bit0Zero | bit0One <;>
    rcases bit1 with bit1Zero | bit1One
  · refine ⟨0, ?_, ?_⟩
    · simp [addressOffset, bit0Zero, bit1Zero]
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit0Zero, bit1Zero] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        assumption
  · refine ⟨2, ?_, ?_⟩
    · simp [addressOffset, bit0Zero, bit1One, ZMod.val_one]
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit0Zero, bit1One] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        assumption
  · refine ⟨1, ?_, ?_⟩
    · simp [addressOffset, bit0One, bit1Zero, ZMod.val_one]
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit0One, bit1Zero] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        assumption
  · refine ⟨3, ?_, ?_⟩
    · simp [addressOffset, bit0One, bit1One, ZMod.val_one]
    · intro i
      fin_cases i <;> simp
      all_goals
        rw [bit0One, bit1One] at rmw0 rmw1 rmw2 rmw3
        ring_nf at rmw0 rmw1 rmw2 rmw3
        assumption

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem StoreHalfChip.storeValue_isU64_of_mergeFacts
    (input : StoreHalfChip.Inputs (ZMod p))
    (selected : Fin 4)
    (merged : ∀ i : Fin 4,
      input.store_value[i] =
        if i = selected then input.adapter.op_a_memory.prev_value[0]
        else input.memory_access.prev_value[i])
    (prior : Word.isU64 input.memory_access.prev_value)
    (source : Word.isU64 input.adapter.op_a_memory.prev_value) :
    Word.isU64 input.store_value := by
  intro i
  rw [merged i]
  split
  · exact source 0
  · exact prior i

omit [Fact (2 ^ 25 < p)] in
private theorem storeHalfRmw0Constraint_mem
    (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[0] -
        (input.memory_access.prev_value[0] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0])
            * ((1 : Expression (ZMod p)) - input.offset_bit[0])
            * ((1 : Expression (ZMod p)) - input.offset_bit[1])) - 0 ∈
      ((StoreHalfChip.main input).operations offset).constraints := by
  simp only [StoreHalfChip.main, circuit_norm]
  iterate 4 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[0] -
        (input.memory_access.prev_value[0] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0])
            * ((1 : Expression (ZMod p)) - input.offset_bit[0])
            * ((1 : Expression (ZMod p)) - input.offset_bit[1])))
      0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeHalfRmw1Constraint_mem
    (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[1] -
        (input.memory_access.prev_value[1] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[1])
            * input.offset_bit[0]
            * ((1 : Expression (ZMod p)) - input.offset_bit[1])) - 0 ∈
      ((StoreHalfChip.main input).operations offset).constraints := by
  simp only [StoreHalfChip.main, circuit_norm]
  iterate 5 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[1] -
        (input.memory_access.prev_value[1] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[1])
            * input.offset_bit[0]
            * ((1 : Expression (ZMod p)) - input.offset_bit[1])))
      0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeHalfRmw2Constraint_mem
    (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[2] -
        (input.memory_access.prev_value[2] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2])
            * ((1 : Expression (ZMod p)) - input.offset_bit[0])
            * input.offset_bit[1]) - 0 ∈
      ((StoreHalfChip.main input).operations offset).constraints := by
  simp only [StoreHalfChip.main, circuit_norm]
  iterate 6 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[2] -
        (input.memory_access.prev_value[2] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2])
            * ((1 : Expression (ZMod p)) - input.offset_bit[0])
            * input.offset_bit[1]))
      0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeHalfRmw3Constraint_mem
    (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[3] -
        (input.memory_access.prev_value[3] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[3])
            * input.offset_bit[0] * input.offset_bit[1]) - 0 ∈
      ((StoreHalfChip.main input).operations offset).constraints := by
  simp only [StoreHalfChip.main, circuit_norm]
  iterate 7 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[3] -
        (input.memory_access.prev_value[3] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[3])
            * input.offset_bit[0] * input.offset_bit[1]))
      0 _

omit [Fact (2 ^ 25 < p)] in
/-- The four SH read-modify-write equations projected from the exact folded chip constraints. -/
theorem StoreHalfChip.rmwFacts_of_mainConstraints
    (inputVar : Var StoreHalfChip.Inputs (ZMod p))
    (input : StoreHalfChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (inputEq : Eval.eval env inputVar = input)
    (constraints : Operations.ConstraintsHold env
      ((StoreHalfChip.main inputVar).operations offset)) :
    input.store_value[0] = input.memory_access.prev_value[0]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0])
            * (1 - input.offset_bit[0]) * (1 - input.offset_bit[1]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[1])
            * input.offset_bit[0] * (1 - input.offset_bit[1]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2])
            * (1 - input.offset_bit[0]) * input.offset_bit[1] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
          + (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[3])
            * input.offset_bit[0] * input.offset_bit[1] := by
  have raw0 := constraints.1 _ (storeHalfRmw0Constraint_mem inputVar offset)
  have raw1 := constraints.1 _ (storeHalfRmw1Constraint_mem inputVar offset)
  have raw2 := constraints.1 _ (storeHalfRmw2Constraint_mem inputVar offset)
  have raw3 := constraints.1 _ (storeHalfRmw3Constraint_mem inputVar offset)
  simp only [eval_sub, Expression.eval, sub_zero] at raw0 raw1 raw2 raw3
  have evalStore :
      Eval.eval env inputVar.store_value = (Eval.eval env inputVar).store_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapStore := evalStore.trans (congrArg StoreHalfChip.Inputs.store_value inputEq)
  rw [CircuitType.eval_var_fields] at hmapStore
  have evalPriorWord :
      Eval.eval env inputVar.memory_access.prev_value =
        (Eval.eval env inputVar).memory_access.prev_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    have hMemory :
        (ProvableStruct.eval env inputVar).memory_access =
          Eval.eval env inputVar.memory_access := rfl
    rw [hMemory, ProvableStruct.eval_eq_eval]
    rfl
  have hmapPrior := evalPriorWord.trans (congrArg
    (fun x : StoreHalfChip.Inputs (ZMod p) => x.memory_access.prev_value) inputEq)
  rw [CircuitType.eval_var_fields] at hmapPrior
  have evalSourceWord :
      Eval.eval env inputVar.adapter.op_a_memory.prev_value =
        (Eval.eval env inputVar).adapter.op_a_memory.prev_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    have hAdapter :
        (ProvableStruct.eval env inputVar).adapter = Eval.eval env inputVar.adapter := rfl
    rw [hAdapter, ProvableStruct.eval_eq_eval]
    have hMemory :
        (ProvableStruct.eval env inputVar.adapter).op_a_memory =
          Eval.eval env inputVar.adapter.op_a_memory := rfl
    rw [hMemory, ProvableStruct.eval_eq_eval]
    rfl
  have hmapSource := evalSourceWord.trans (congrArg
    (fun x : StoreHalfChip.Inputs (ZMod p) => x.adapter.op_a_memory.prev_value) inputEq)
  rw [CircuitType.eval_var_fields] at hmapSource
  have evalOffsetWord :
      Eval.eval env inputVar.offset_bit = (Eval.eval env inputVar).offset_bit := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapOffset := evalOffsetWord.trans (congrArg StoreHalfChip.Inputs.offset_bit inputEq)
  rw [CircuitType.eval_var_fields] at hmapOffset
  have evalStoreAt : ∀ i (hi : i < 4),
      Expression.eval env inputVar.store_value[i] = input.store_value[i] :=
    fun i hi => by rw [← hmapStore]; simp only [Vector.getElem_map]
  have evalPrior : ∀ i (hi : i < 4),
      Expression.eval env inputVar.memory_access.prev_value[i] =
        input.memory_access.prev_value[i] :=
    fun i hi => by rw [← hmapPrior]; simp only [Vector.getElem_map]
  have evalSource :
      Expression.eval env inputVar.adapter.op_a_memory.prev_value[0] =
        input.adapter.op_a_memory.prev_value[0] := by
    rw [← hmapSource]
    simp only [Vector.getElem_map]
  have evalOffset : ∀ i (hi : i < 2),
      Expression.eval env inputVar.offset_bit[i] = input.offset_bit[i] :=
    fun i hi => by rw [← hmapOffset]; simp only [Vector.getElem_map]
  simp only [evalStoreAt 0 (by omega), evalStoreAt 1 (by omega),
    evalStoreAt 2 (by omega), evalStoreAt 3 (by omega),
    evalPrior 0 (by omega), evalPrior 1 (by omega),
    evalPrior 2 (by omega), evalPrior 3 (by omega), evalSource,
    evalOffset 0 (by omega), evalOffset 1 (by omega)] at raw0 raw1 raw2 raw3
  exact ⟨sub_eq_zero.mp (by simpa using raw0),
    sub_eq_zero.mp (by simpa using raw1),
    sub_eq_zero.mp (by simpa using raw2),
    sub_eq_zero.mp raw3⟩

private def storeHalfAddressInput
    (input : StoreHalfChip.Inputs (Expression (ZMod p))) :
    AddressOperation.Inputs (Expression (ZMod p)) :=
  ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1],
    input.is_real⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem storeHalfAddressInput_offsetBit1
    (env : Environment (ZMod p))
    (input : StoreHalfChip.Inputs (Expression (ZMod p))) :
    Expression.eval env (storeHalfAddressInput input).offset_bit1 =
      Expression.eval env input.offset_bit[0] := rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem storeHalfAddressInput_offsetBit2
    (env : Environment (ZMod p))
    (input : StoreHalfChip.Inputs (Expression (ZMod p))) :
    Expression.eval env (storeHalfAddressInput input).offset_bit2 =
      Expression.eval env input.offset_bit[1] := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem storeHalfAddress_mem
    (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset, (AddressOperation.circuit (p := p)).toSubcircuit offset
      (storeHalfAddressInput input)⟩ ∈
        ((StoreHalfChip.main input).operations offset).subcircuits := by
  simp only [StoreHalfChip.main, storeHalfAddressInput,
    AddressOperation.circuit, circuit_norm, Nat.add_zero]

omit [Fact (2 ^ 25 < p)] in
/-- SH's full-cell write word is range-canonical before parent-chip soundness is opened. -/
theorem StoreHalfChip.storeValue_isU64_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨StoreHalfChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (prior : Word.isU64
      ((⟨StoreHalfChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).memory_access.prev_value)
    (source : Word.isU64
      ((⟨StoreHalfChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).adapter.op_a_memory.prev_value) :
    Word.isU64
      ((⟨StoreHalfChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).store_value := by
  let input : Var StoreHalfChip.Inputs (ZMod p) := varFromOffset StoreHalfChip.Inputs 0
  let offset := size StoreHalfChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) := storeHalfAddressInput input
  let component : Component (ZMod p) := ⟨StoreHalfChip.circuit⟩
  have rowConstraints : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have mainConstraints :
      ((StoreHalfChip.main input).operations offset).ConstraintsHold env := by
    exact rowConstraints
  have addressConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((StoreHalfChip.main input).operations offset) AddressOperation.circuit
    addressInput offset (storeHalfAddress_mem input offset) mainConstraints
  have offsetBools :=
    AddressOperation.offsetBits_bool_of_constraints addressInput offset env addressConstraints
  have inputEq : Eval.eval env input = component.rowInput env :=
    eval_varFromOffset_valueFromOffset StoreHalfChip.Inputs 0 env
  have rmw := StoreHalfChip.rmwFacts_of_mainConstraints
    input (component.rowInput env) offset env inputEq mainConstraints
  have evalOffsetWord :
      Eval.eval env input.offset_bit = (Eval.eval env input).offset_bit := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapOffset := evalOffsetWord.trans (congrArg StoreHalfChip.Inputs.offset_bit inputEq)
  rw [CircuitType.eval_var_fields] at hmapOffset
  have evalOffset : ∀ i (hi : i < 2),
      Expression.eval env input.offset_bit[i] = (component.rowInput env).offset_bit[i] :=
    fun i hi => by rw [← hmapOffset]; simp only [Vector.getElem_map]
  have bit0 :
      (component.rowInput env).offset_bit[0] = 0 ∨
        (component.rowInput env).offset_bit[0] = 1 := by
    have raw := offsetBools.2.1
    rw [storeHalfAddressInput_offsetBit1 env input, evalOffset 0 (by omega)] at raw
    exact raw
  have bit1 :
      (component.rowInput env).offset_bit[1] = 0 ∨
        (component.rowInput env).offset_bit[1] = 1 := by
    have raw := offsetBools.2.2
    rw [storeHalfAddressInput_offsetBit2 env input, evalOffset 1 (by omega)] at raw
    exact raw
  obtain ⟨selected, _offset, merged⟩ :=
    StoreHalfChip.mergeFacts (component.rowInput env) rmw bit0 bit1
  exact StoreHalfChip.storeValue_isU64_of_mergeFacts
    (component.rowInput env) selected merged prior source

omit [Fact (2 ^ 25 < p)] in
/-- StoreHalf's semantic row writes rs2's low two bytes into the selector-chosen halfword of the
authenticated RAM cell. -/
theorem storeHalfChip_storeFacts
    (input : StoreHalfChip.Inputs (ZMod p))
    (cols : StoreHalfChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (real : (StoreHalfChip.rowView input cols).is_real = 1)
    (spec : StoreHalfChip.Spec input cols data) :
    ∃ write : Trace.MemWrite (ZMod p),
      (StoreHalfChip.rowView input cols).commit = Trace.CommitEffect.store write ∧
      write.InCell (ramCellOfAccess (StoreHalfChip.ramAccessView input cols)) ∧
      RamCellUpdate write (ramCellOfAccess (StoreHalfChip.ramAccessView input cols))
        (Word.toBitVec64 (StoreHalfChip.ramAccessView input cols).priorValue)
        (Word.toBitVec64 (StoreHalfChip.ramAccessView input cols).newValue) := by
  let addressInput : AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1], input.is_real⟩
  let access := StoreHalfChip.ramAccessView input cols
  let write : Trace.MemWrite (ZMod p) :=
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 2⟩
  have addressEq :
      access.address = AddressOperation.alignedValue addressInput cols.address_operation := by
    rfl
  have realInput : input.is_real = 1 := by
    simpa only [StoreHalfChip.rowView] using real
  have address :
      write.addrNat = (ramCellOfAccess access).baseAddr.toNat + addressOffset addressInput := by
    have raw := rawAddress_eq_ramCellBase_add_offset
      addressInput cols.address_operation access addressEq (spec.1.2.2.2 realInput)
    simpa only [write, Trace.MemWrite.addrNat, address48Nat] using raw
  have priorBound : Word.isU64 input.memory_access.prev_value := (spec.2.1 realInput).2.2.2.2.2.1
  have sourceBound : Word.isU64 input.adapter.op_a_memory.prev_value :=
    ((spec.2.2.1).2.2.2.2.2 realInput).1
  have bit0 : input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1 := spec.1.2.1
  have bit1 : input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1 := spec.1.2.2.1
  obtain ⟨selected, offsetEq, merged⟩ := StoreHalfChip.mergeFacts input spec.2.2.2.1 bit0 bit1
  have storeBound : Word.isU64 input.store_value :=
    StoreHalfChip.storeValue_isU64_of_mergeFacts input selected merged priorBound sourceBound
  have offsetEq' : addressOffset addressInput = 2 * selected.val := by
    simpa only [addressInput] using offsetEq
  have addressSelected :
      write.addrNat = (ramCellOfAccess access).baseAddr.toNat + 2 * selected.val := by
    simpa only [offsetEq'] using address
  refine ⟨write, rfl,
    Trace.MemWrite.inCell_of_address_width
      (offset := 2 * selected.val) (width := 2) addressSelected rfl (by
      have := selected.isLt
      omega), ?_⟩
  apply ramCellUpdate_of_patchedCell (offset := 2 * selected.val) (width := 2) addressSelected rfl
  symm
  simpa only [access, write, StoreHalfChip.ramAccessView] using
    patchedCellBytes_two cols.address_operation.addr_operation.value
      input.memory_access.prev_value input.adapter.op_a_memory.prev_value input.store_value
      selected priorBound sourceBound storeBound merged

omit [Fact (2 ^ 25 < p)] in
theorem StoreHalfChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (StoreHalfChip.circuit (p := p))
      StoreHalfChip.rowView
      (fun input cols => some (StoreHalfChip.ramAccessView input cols)) := by
  let input : Var StoreHalfChip.Inputs (ZMod p) := varFromOffset StoreHalfChip.Inputs 0
  let offset := size StoreHalfChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1], input.is_real⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.store_value, input.is_real⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, StoreHalfChip.circuit,
      StoreHalfChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, StoreHalfChip.circuit, StoreHalfChip.rowView,
        StoreHalfChip.ramAccessView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreHalfChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (StoreHalfChip.circuit (p := p))
      (fun input cols => some (StoreHalfChip.ramAccessView input cols))
      (fun input => input.is_real) := by
  let input : Var StoreHalfChip.Inputs (ZMod p) := varFromOffset StoreHalfChip.Inputs 0
  let offset := size StoreHalfChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1], input.is_real⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, StoreHalfChip.circuit, StoreHalfChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, StoreHalfChip.circuit,
      StoreHalfChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreHalfChip.immutableItypeTimestampContract :
    CircuitImmutableITypeTimestampContract (p := p) (StoreHalfChip.circuit (p := p))
      StoreHalfChip.rowView := by
  let input : Var StoreHalfChip.Inputs (ZMod p) := varFromOffset StoreHalfChip.Inputs 0
  let offset := size StoreHalfChip.Inputs
  let readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 37⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, StoreHalfChip.circuit, StoreHalfChip.main,
      Readers.ITypeReaderImmutable.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, StoreHalfChip.rowView,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem storeHalfChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨storeHalfChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded storeHalf

theorem storeHalfChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨storeHalfChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf StoreHalfChip.circuit StoreHalfChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded storeHalf

theorem storeHalfChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨StoreHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv storeHalf

theorem storeHalfChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨StoreHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ImmutableRamTimestampBounds
      (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf StoreHalfChip.circuit StoreHalfChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact immutableRamTimestampBounds_of_contracts StoreHalfChip.circuit
    StoreHalfChip.rowView StoreHalfChip.ramAccessView StoreHalfChip.ramTimestampContract
    StoreHalfChip.immutableItypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem storeHalfChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreHalfChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf StoreHalfChip.circuit StoreHalfChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv storeHalf (fun input => input.is_real)

theorem storeHalfChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeHalfChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds storeHalf

theorem storeHalfChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeHalfChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ImmutableRamTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds storeHalf

theorem storeHalfChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeHalfChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam storeHalf

omit [Fact (2 ^ 25 < p)] in
/-- StoreHalf's public exposed Memory list evaluates to the immutable RAM/I-type layout. -/
theorem storeHalfChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨StoreHalfChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableRamMemoryInteractions
        (StoreHalfChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreHalfChip.Inputs 0))
          (Eval.eval env ((StoreHalfChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreHalfChip.Inputs 0)
            (size StoreHalfChip.Inputs))))
        (StoreHalfChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreHalfChip.Inputs 0))
          (Eval.eval env ((StoreHalfChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreHalfChip.Inputs 0)
            (size StoreHalfChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues storeHalf immutableRamMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    StoreHalfChip.rowView, StoreHalfChip.ramAccessView, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, StoreHalfChip.circuit, circuit_norm]

theorem storeHalfChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeHalfChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableRamMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions storeHalf immutableRamMemoryInteractions

/-- StoreHalf instantiates the authenticated immutable RAM/I-type interaction shape. -/
noncomputable def storeHalfChip_immutableRamMemoryInteractionShape :
    ImmutableRamMemoryInteractionShape (storeHalfChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := storeHalfChip_typedMemoryInteractions_eq

end StoreHalf

section StoreWord

/-- The StoreWord descriptor in the supported Core registry. -/
def storeWordChipDescriptor : SupportedChip p :=
  ⟨StoreWordChip.kind, StoreWordChip.circuit, rfl, [.SW], .any⟩

theorem storeWordChipDescriptor_table :
    (storeWordChipDescriptor (p := p)).table =
      (⟨StoreWordChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeWordChipDescriptor_view (input : StoreWordChip.Inputs (ZMod p))
    (output : StoreWordChip.Columns (ZMod p)) :
    (storeWordChipDescriptor (p := p)).kind.view input output =
      StoreWordChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeWordChipDescriptor_ramAccess (input : StoreWordChip.Inputs (ZMod p))
    (output : StoreWordChip.Columns (ZMod p)) :
    (storeWordChipDescriptor (p := p)).kind.ramAccess input output =
      some (StoreWordChip.ramAccessView input output) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeWordChipDescriptor_rdGuard :
    (storeWordChipDescriptor (p := p)).rdGuard = .any := rfl

theorem storeWordChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (storeWordChipDescriptor (p := p)).table.Assumptions env ↔
      StoreWordChip.Assumptions
        (circuitRowInputOf StoreWordChip.circuit env) env.data := by
  chipAssumptionsIff storeWord

omit [Fact (2 ^ 25 < p)] in
theorem storeWordAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf StoreWordChip.circuit
        StoreWordChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView env).adapter.op_c)
    (storeValue : Word.isU64
      (circuitRowInputOf StoreWordChip.circuit env).store_value) :
    StoreWordChip.Assumptions
      (circuitRowInputOf StoreWordChip.circuit env) data := by
  rw [circuitRowViewOf_eq_typed] at base immediate
  unfold StoreWordChip.Assumptions
  refine ⟨?_, ?_, fun _ => storeValue⟩
  · simpa only [StoreWordChip.Inputs.op_b_val, StoreWordChip.rowView,
      Extracted.ITypeReader.toAdapterView] using base
  · simpa only [StoreWordChip.Inputs.op_c_imm, StoreWordChip.rowView,
      Extracted.ITypeReader.toAdapterView] using immediate

theorem storeWordSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((storeWordChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    StoreWordChip.Spec
      (circuitRowInputOf StoreWordChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreWordChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold storeWordChipDescriptor at h
  exact chipSpec_of_literalDescriptor StoreWordChip.kind StoreWordChip.circuit
    rfl [.SW] .any data physical h

theorem storeWordAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : StoreWordChip.AdvanceReady
      (circuitRowInputOf StoreWordChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreWordChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((storeWordChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((storeWordChipDescriptor (p := p)).decodeRow data physical).inputs
      ((storeWordChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold storeWordChipDescriptor
  apply advanceReady_of_literalDescriptor StoreWordChip.kind StoreWordChip.circuit
    rfl [.SW] .any data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
private theorem storeWordRmw0Constraint_mem
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[0] -
        (input.memory_access.prev_value[0] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0]) * (1 - input.offset_bit)) - 0 ∈
      ((StoreWordChip.main input).operations offset).constraints := by
  simp only [StoreWordChip.main, circuit_norm]
  iterate 4 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[0] -
        (input.memory_access.prev_value[0] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0]) * (1 - input.offset_bit)))
      0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeWordRmw1Constraint_mem
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[1] -
        (input.memory_access.prev_value[1] +
          (input.adapter.op_a_memory.prev_value[1] -
            input.memory_access.prev_value[1]) * (1 - input.offset_bit)) - 0 ∈
      ((StoreWordChip.main input).operations offset).constraints := by
  simp only [StoreWordChip.main, circuit_norm]
  iterate 5 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[1] -
        (input.memory_access.prev_value[1] +
          (input.adapter.op_a_memory.prev_value[1] -
            input.memory_access.prev_value[1]) * (1 - input.offset_bit)))
      0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeWordRmw2Constraint_mem
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[2] -
        (input.memory_access.prev_value[2] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2]) * input.offset_bit) - 0 ∈
      ((StoreWordChip.main input).operations offset).constraints := by
  simp only [StoreWordChip.main, circuit_norm]
  iterate 6 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[2] -
        (input.memory_access.prev_value[2] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2]) * input.offset_bit))
      0 _

omit [Fact (2 ^ 25 < p)] in
private theorem storeWordRmw3Constraint_mem
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    input.store_value[3] -
        (input.memory_access.prev_value[3] +
          (input.adapter.op_a_memory.prev_value[1] -
            input.memory_access.prev_value[3]) * input.offset_bit) - 0 ∈
      ((StoreWordChip.main input).operations offset).constraints := by
  simp only [StoreWordChip.main, circuit_norm]
  iterate 7 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    memoryEqualityConstraint_mem
      (input.store_value[3] -
        (input.memory_access.prev_value[3] +
          (input.adapter.op_a_memory.prev_value[1] -
            input.memory_access.prev_value[3]) * input.offset_bit))
      0 _

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem StoreWordChip.evalOffsetBit
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    Expression.eval env input.offset_bit =
      (Eval.eval env input).offset_bit := by
  rw [ProvableStruct.eval_var_eq_eval]
  have hOffset :
      (ProvableStruct.eval env input).offset_bit = Eval.eval env input.offset_bit := rfl
  rw [hOffset, ProvableType.eval_field]

private def storeWordAddressInput
    (input : StoreWordChip.Inputs (Expression (ZMod p))) :
    AddressOperation.Inputs (Expression (ZMod p)) :=
  ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem storeWordAddressInput_offsetBit2
    (env : Environment (ZMod p))
    (input : StoreWordChip.Inputs (Expression (ZMod p))) :
    Expression.eval env (storeWordAddressInput input).offset_bit2 =
      Expression.eval env input.offset_bit := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem storeWordAddress_mem
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset, (AddressOperation.circuit (p := p)).toSubcircuit offset
      (storeWordAddressInput input)⟩ ∈
        ((StoreWordChip.main input).operations offset).subcircuits := by
  simp only [StoreWordChip.main, storeWordAddressInput,
    AddressOperation.circuit, circuit_norm, Nat.add_zero]

omit [Fact (2 ^ 25 < p)] in
/-- The four SW read-modify-write equations, projected from the exact folded chip constraints.
This deliberately precedes the chip `Spec`: machine grounding needs these equations to derive the
`store_value` range precondition required by the `MemoryAccess` subcircuit. -/
theorem StoreWordChip.rmwFacts_of_mainConstraints
    (inputVar : Var StoreWordChip.Inputs (ZMod p))
    (input : StoreWordChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (inputEq : Eval.eval env inputVar = input)
    (constraints : Operations.ConstraintsHold env
      ((StoreWordChip.main inputVar).operations offset)) :
    input.store_value[0] =
        input.memory_access.prev_value[0] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[0]) * (1 - input.offset_bit) ∧
      input.store_value[1] =
        input.memory_access.prev_value[1] +
          (input.adapter.op_a_memory.prev_value[1] -
            input.memory_access.prev_value[1]) * (1 - input.offset_bit) ∧
      input.store_value[2] =
        input.memory_access.prev_value[2] +
          (input.adapter.op_a_memory.prev_value[0] -
            input.memory_access.prev_value[2]) * input.offset_bit ∧
      input.store_value[3] =
        input.memory_access.prev_value[3] +
          (input.adapter.op_a_memory.prev_value[1] -
            input.memory_access.prev_value[3]) * input.offset_bit := by
  have raw0 := constraints.1 _ (storeWordRmw0Constraint_mem inputVar offset)
  have raw1 := constraints.1 _ (storeWordRmw1Constraint_mem inputVar offset)
  have raw2 := constraints.1 _ (storeWordRmw2Constraint_mem inputVar offset)
  have raw3 := constraints.1 _ (storeWordRmw3Constraint_mem inputVar offset)
  simp only [eval_sub, Expression.eval, sub_zero] at raw0 raw1 raw2 raw3
  have evalStore :
      Eval.eval env inputVar.store_value = (Eval.eval env inputVar).store_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    rfl
  have hmapSv := evalStore.trans (congrArg StoreWordChip.Inputs.store_value inputEq)
  rw [CircuitType.eval_var_fields] at hmapSv
  have evalPriorWord :
      Eval.eval env inputVar.memory_access.prev_value =
        (Eval.eval env inputVar).memory_access.prev_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    have hMemory :
        (ProvableStruct.eval env inputVar).memory_access =
          Eval.eval env inputVar.memory_access := rfl
    rw [hMemory, ProvableStruct.eval_eq_eval]
    rfl
  have hmapPrior := evalPriorWord.trans (congrArg
    (fun x : StoreWordChip.Inputs (ZMod p) => x.memory_access.prev_value) inputEq)
  rw [CircuitType.eval_var_fields] at hmapPrior
  have evalSourceWord :
      Eval.eval env inputVar.adapter.op_a_memory.prev_value =
        (Eval.eval env inputVar).adapter.op_a_memory.prev_value := by
    rw [ProvableStruct.eval_var_eq_eval]
    have hAdapter :
        (ProvableStruct.eval env inputVar).adapter = Eval.eval env inputVar.adapter := rfl
    rw [hAdapter, ProvableStruct.eval_eq_eval]
    have hMemory :
        (ProvableStruct.eval env inputVar.adapter).op_a_memory =
          Eval.eval env inputVar.adapter.op_a_memory := rfl
    rw [hMemory, ProvableStruct.eval_eq_eval]
    rfl
  have hmapSource := evalSourceWord.trans (congrArg
    (fun x : StoreWordChip.Inputs (ZMod p) => x.adapter.op_a_memory.prev_value) inputEq)
  rw [CircuitType.eval_var_fields] at hmapSource
  have evalSv : ∀ i (hi : i < 4),
      Expression.eval env inputVar.store_value[i] = input.store_value[i] :=
    fun i hi => by rw [← hmapSv]; simp only [Vector.getElem_map]
  have evalPrior : ∀ i (hi : i < 4),
      Expression.eval env inputVar.memory_access.prev_value[i] =
        input.memory_access.prev_value[i] :=
    fun i hi => by rw [← hmapPrior]; simp only [Vector.getElem_map]
  have evalSource : ∀ i (hi : i < 2),
      Expression.eval env inputVar.adapter.op_a_memory.prev_value[i] =
        input.adapter.op_a_memory.prev_value[i] :=
    fun i hi => by rw [← hmapSource]; simp only [Vector.getElem_map]
  have evalOffsetInput := StoreWordChip.evalOffsetBit env inputVar
  have evalOffset := evalOffsetInput.trans (congrArg StoreWordChip.Inputs.offset_bit inputEq)
  simp only [evalSv 0 (by omega), evalSv 1 (by omega), evalSv 2 (by omega),
    evalSv 3 (by omega), evalPrior 0 (by omega), evalPrior 1 (by omega),
    evalPrior 2 (by omega), evalPrior 3 (by omega), evalSource 0 (by omega),
    evalSource 1 (by omega), evalOffset] at raw0 raw1 raw2 raw3
  exact ⟨sub_eq_zero.mp raw0, sub_eq_zero.mp raw1, sub_eq_zero.mp raw2, sub_eq_zero.mp raw3⟩

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem StoreWordChip.storeValue_isU64_of_rmwFacts
    (input : StoreWordChip.Inputs (ZMod p))
    (rmw :
      input.store_value[0] =
          input.memory_access.prev_value[0] +
            (input.adapter.op_a_memory.prev_value[0] -
              input.memory_access.prev_value[0]) * (1 - input.offset_bit) ∧
        input.store_value[1] =
          input.memory_access.prev_value[1] +
            (input.adapter.op_a_memory.prev_value[1] -
              input.memory_access.prev_value[1]) * (1 - input.offset_bit) ∧
        input.store_value[2] =
          input.memory_access.prev_value[2] +
            (input.adapter.op_a_memory.prev_value[0] -
              input.memory_access.prev_value[2]) * input.offset_bit ∧
        input.store_value[3] =
          input.memory_access.prev_value[3] +
            (input.adapter.op_a_memory.prev_value[1] -
              input.memory_access.prev_value[3]) * input.offset_bit)
    (offsetBool : input.offset_bit = 0 ∨ input.offset_bit = 1)
    (prior : Word.isU64 input.memory_access.prev_value)
    (source : Word.isU64 input.adapter.op_a_memory.prev_value) :
    Word.isU64 input.store_value := by
  obtain ⟨rmw0, rmw1, rmw2, rmw3⟩ := rmw
  rcases offsetBool with offsetZero | offsetOne
  · rw [offsetZero] at rmw0 rmw1 rmw2 rmw3
    ring_nf at rmw0 rmw1 rmw2 rmw3
    exact Word.isU64_of_cases
      (rmw0 ▸ source 0) (rmw1 ▸ source 1)
      (rmw2 ▸ prior 2) (rmw3 ▸ prior 3)
  · rw [offsetOne] at rmw0 rmw1 rmw2 rmw3
    ring_nf at rmw0 rmw1 rmw2 rmw3
    exact Word.isU64_of_cases
      (rmw0 ▸ prior 0) (rmw1 ▸ prior 1)
      (rmw2 ▸ source 0) (rmw3 ▸ source 1)

omit [Fact (2 ^ 25 < p)] in
/-- SW's full-cell write word is range-canonical before parent-chip soundness is opened. The proof
uses only the exact row constraints, the retained address selector gate, and the two authenticated
pull words; it therefore closes the otherwise circular `MemoryAccess` push precondition. -/
theorem StoreWordChip.storeValue_isU64_of_constraints
    (env : Environment (ZMod p))
    (constraints :
      (⟨StoreWordChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env)
    (prior : Word.isU64
      ((⟨StoreWordChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).memory_access.prev_value)
    (source : Word.isU64
      ((⟨StoreWordChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).adapter.op_a_memory.prev_value) :
    Word.isU64
      ((⟨StoreWordChip.circuit (p := p)⟩ :
        Component (ZMod p)).rowInput env).store_value := by
  let input : Var StoreWordChip.Inputs (ZMod p) := varFromOffset StoreWordChip.Inputs 0
  let offset := size StoreWordChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) := storeWordAddressInput input
  let component : Component (ZMod p) := ⟨StoreWordChip.circuit⟩
  have rowConstraints : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have mainConstraints :
      ((StoreWordChip.main input).operations offset).ConstraintsHold env := by
    exact rowConstraints
  have addressMem := storeWordAddress_mem input offset
  have addressConstraints := constraintsHold_generalSubcircuit_of_mem env
    ((StoreWordChip.main input).operations offset) AddressOperation.circuit
    addressInput offset addressMem mainConstraints
  have offsetBoolRaw :=
    (AddressOperation.offsetBits_bool_of_constraints
      addressInput offset env addressConstraints).2.2
  have inputEq : Eval.eval env input = component.rowInput env :=
    eval_varFromOffset_valueFromOffset StoreWordChip.Inputs 0 env
  have rmw := StoreWordChip.rmwFacts_of_mainConstraints
    input (component.rowInput env) offset env inputEq mainConstraints
  have evalOffsetInput := StoreWordChip.evalOffsetBit env input
  have offsetEq : Expression.eval env input.offset_bit =
      (component.rowInput env).offset_bit :=
    evalOffsetInput.trans (congrArg StoreWordChip.Inputs.offset_bit inputEq)
  have offsetBool :
      (component.rowInput env).offset_bit = 0 ∨ (component.rowInput env).offset_bit = 1 := by
    rw [storeWordAddressInput_offsetBit2 env input] at offsetBoolRaw
    rw [offsetEq] at offsetBoolRaw
    exact offsetBoolRaw
  exact StoreWordChip.storeValue_isU64_of_rmwFacts
    (component.rowInput env) rmw offsetBool prior source

omit [Fact (2 ^ 25 < p)] in
/-- StoreWord's semantic row writes the low four source bytes into the selected half of the
authenticated RAM cell. The two cases are exactly the v6.3.1 AIR's `offset_bit`-selected
read-modify-write equations. -/
theorem storeWordChip_storeFacts
    (input : StoreWordChip.Inputs (ZMod p))
    (cols : StoreWordChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (real : (StoreWordChip.rowView input cols).is_real = 1)
    (spec : StoreWordChip.Spec input cols data) :
    ∃ write : Trace.MemWrite (ZMod p),
      (StoreWordChip.rowView input cols).commit = Trace.CommitEffect.store write ∧
      write.InCell (ramCellOfAccess (StoreWordChip.ramAccessView input cols)) ∧
      RamCellUpdate write (ramCellOfAccess (StoreWordChip.ramAccessView input cols))
        (Word.toBitVec64 (StoreWordChip.ramAccessView input cols).priorValue)
        (Word.toBitVec64 (StoreWordChip.ramAccessView input cols).newValue) := by
  let addressInput : AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
  let access := StoreWordChip.ramAccessView input cols
  let write : Trace.MemWrite (ZMod p) :=
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 4⟩
  have addressEq :
      access.address = AddressOperation.alignedValue addressInput cols.address_operation := by
    rfl
  have realInput : input.is_real = 1 := by
    simpa only [StoreWordChip.rowView] using real
  have address :
      write.addrNat = (ramCellOfAccess access).baseAddr.toNat + addressOffset addressInput := by
    have raw := rawAddress_eq_ramCellBase_add_offset
      addressInput cols.address_operation access addressEq (spec.1.2.2.2 realInput)
    simpa only [write, Trace.MemWrite.addrNat, address48Nat] using raw
  have priorBound : Word.isU64 input.memory_access.prev_value := (spec.2.1 realInput).2.2.2.2.2.1
  have sourceBound : Word.isU64 input.adapter.op_a_memory.prev_value :=
    ((spec.2.2.1).2.2.2.2.2 realInput).1
  have offsetBool : input.offset_bit = 0 ∨ input.offset_bit = 1 := spec.1.2.2.1
  have storeBound : Word.isU64 input.store_value :=
    StoreWordChip.storeValue_isU64_of_rmwFacts input spec.2.2.2.1
      offsetBool priorBound sourceBound
  obtain ⟨rmw0, rmw1, rmw2, rmw3⟩ := spec.2.2.2.1
  rcases offsetBool with offsetZero | offsetOne
  · have offsetZeroNat : addressOffset addressInput = 0 := by
      simp [addressOffset, addressInput, offsetZero]
    have addressZero :
        write.addrNat = (ramCellOfAccess access).baseAddr.toNat + 0 := by
      simpa only [offsetZeroNat] using address
    rw [offsetZero] at rmw0 rmw1 rmw2 rmw3
    ring_nf at rmw0 rmw1 rmw2 rmw3
    refine ⟨write, rfl, Trace.MemWrite.inCell_of_address_width addressZero rfl (by norm_num), ?_⟩
    apply ramCellUpdate_of_patchedCell addressZero rfl
    symm
    simpa only [access, write, StoreWordChip.ramAccessView] using
      patchedCellBytes_zero_four cols.address_operation.addr_operation.value
        input.memory_access.prev_value input.adapter.op_a_memory.prev_value input.store_value
        priorBound sourceBound storeBound rmw0 rmw1 rmw2 rmw3
  · have offsetFour : addressOffset addressInput = 4 := by
      simp [addressOffset, addressInput, offsetOne, ZMod.val_one]
    have addressFour :
        write.addrNat = (ramCellOfAccess access).baseAddr.toNat + 4 := by
      simpa only [offsetFour] using address
    rw [offsetOne] at rmw0 rmw1 rmw2 rmw3
    ring_nf at rmw0 rmw1 rmw2 rmw3
    refine ⟨write, rfl, Trace.MemWrite.inCell_of_address_width addressFour rfl (by norm_num), ?_⟩
    apply ramCellUpdate_of_patchedCell addressFour rfl
    symm
    simpa only [access, write, StoreWordChip.ramAccessView] using
      patchedCellBytes_four_four cols.address_operation.addr_operation.value
        input.memory_access.prev_value input.adapter.op_a_memory.prev_value input.store_value
        priorBound sourceBound storeBound rmw0 rmw1 rmw2 rmw3

omit [Fact (2 ^ 25 < p)] in
theorem StoreWordChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (StoreWordChip.circuit (p := p))
      StoreWordChip.rowView
      (fun input cols => some (StoreWordChip.ramAccessView input cols)) := by
  let input : Var StoreWordChip.Inputs (ZMod p) := varFromOffset StoreWordChip.Inputs 0
  let offset := size StoreWordChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.store_value, input.is_real⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, StoreWordChip.circuit,
      StoreWordChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, StoreWordChip.circuit, StoreWordChip.rowView,
        StoreWordChip.ramAccessView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreWordChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (StoreWordChip.circuit (p := p))
      (fun input cols => some (StoreWordChip.ramAccessView input cols))
      (fun input => input.is_real) := by
  let input : Var StoreWordChip.Inputs (ZMod p) := varFromOffset StoreWordChip.Inputs 0
  let offset := size StoreWordChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, StoreWordChip.circuit, StoreWordChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, StoreWordChip.circuit,
      StoreWordChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreWordChip.immutableItypeTimestampContract :
    CircuitImmutableITypeTimestampContract (p := p) (StoreWordChip.circuit (p := p))
      StoreWordChip.rowView := by
  let input : Var StoreWordChip.Inputs (ZMod p) := varFromOffset StoreWordChip.Inputs 0
  let offset := size StoreWordChip.Inputs
  let readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 38⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, StoreWordChip.circuit, StoreWordChip.main,
      Readers.ITypeReaderImmutable.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, StoreWordChip.rowView,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem storeWordChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨storeWordChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded storeWord

theorem storeWordChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨storeWordChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf StoreWordChip.circuit StoreWordChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded storeWord

theorem storeWordChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨StoreWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv storeWord

theorem storeWordChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨StoreWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ImmutableRamTimestampBounds
      (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf StoreWordChip.circuit StoreWordChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact immutableRamTimestampBounds_of_contracts StoreWordChip.circuit
    StoreWordChip.rowView StoreWordChip.ramAccessView StoreWordChip.ramTimestampContract
    StoreWordChip.immutableItypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem storeWordChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreWordChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf StoreWordChip.circuit StoreWordChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv storeWord (fun input => input.is_real)

theorem storeWordChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeWordChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds storeWord

theorem storeWordChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeWordChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ImmutableRamTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds storeWord

theorem storeWordChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeWordChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam storeWord

omit [Fact (2 ^ 25 < p)] in
/-- StoreWord's public exposed Memory list evaluates to the immutable RAM/I-type layout. -/
theorem storeWordChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨StoreWordChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableRamMemoryInteractions
        (StoreWordChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreWordChip.Inputs 0))
          (Eval.eval env ((StoreWordChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreWordChip.Inputs 0)
            (size StoreWordChip.Inputs))))
        (StoreWordChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreWordChip.Inputs 0))
          (Eval.eval env ((StoreWordChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreWordChip.Inputs 0)
            (size StoreWordChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues storeWord immutableRamMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    StoreWordChip.rowView, StoreWordChip.ramAccessView, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, StoreWordChip.circuit, circuit_norm]

theorem storeWordChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeWordChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableRamMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions storeWord immutableRamMemoryInteractions

/-- StoreWord instantiates the authenticated immutable RAM/I-type interaction shape. -/
noncomputable def storeWordChip_immutableRamMemoryInteractionShape :
    ImmutableRamMemoryInteractionShape (storeWordChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := storeWordChip_typedMemoryInteractions_eq

end StoreWord

section StoreDouble

/-- The StoreDouble descriptor in the supported Core registry. -/
def storeDoubleChipDescriptor : SupportedChip p :=
  ⟨StoreDoubleChip.kind, StoreDoubleChip.circuit, rfl, [.SD], .any⟩

theorem storeDoubleChipDescriptor_table :
    (storeDoubleChipDescriptor (p := p)).table =
      (⟨StoreDoubleChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeDoubleChipDescriptor_view (input : StoreDoubleChip.Inputs (ZMod p))
    (output : StoreDoubleChip.Columns (ZMod p)) :
    (storeDoubleChipDescriptor (p := p)).kind.view input output =
      StoreDoubleChip.rowView input output := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeDoubleChipDescriptor_ramAccess (input : StoreDoubleChip.Inputs (ZMod p))
    (output : StoreDoubleChip.Columns (ZMod p)) :
    (storeDoubleChipDescriptor (p := p)).kind.ramAccess input output =
      some (StoreDoubleChip.ramAccessView input output) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem storeDoubleChipDescriptor_rdGuard :
    (storeDoubleChipDescriptor (p := p)).rdGuard = .any := rfl

theorem storeDoubleChipDescriptor_assumptions_iff
    (env : Environment (ZMod p)) :
    (storeDoubleChipDescriptor (p := p)).table.Assumptions env ↔
      StoreDoubleChip.Assumptions
        (circuitRowInputOf StoreDoubleChip.circuit env) env.data := by
  chipAssumptionsIff storeDouble

omit [Fact (2 ^ 25 < p)] in
theorem storeDoubleAssumptions_env
    (env : Environment (ZMod p)) (data : ProverData (ZMod p))
    (base : Word.isU64
      ((circuitRowViewOf StoreDoubleChip.circuit
        StoreDoubleChip.rowView env).adapter.op_b_memory.prev_value))
    (immediate : Word.isU64
      (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView env).adapter.op_c) :
    StoreDoubleChip.Assumptions
      (circuitRowInputOf StoreDoubleChip.circuit env) data := by
  rw [circuitRowViewOf_eq_typed] at base immediate
  unfold StoreDoubleChip.Assumptions
  constructor
  · simpa only [StoreDoubleChip.Inputs.op_b_val, StoreDoubleChip.rowView,
      Extracted.ITypeReader.toAdapterView] using base
  · simpa only [StoreDoubleChip.Inputs.op_c_imm, StoreDoubleChip.rowView,
      Extracted.ITypeReader.toAdapterView] using immediate

theorem storeDoubleSpec_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (h : ((storeDoubleChipDescriptor (p := p)).decodeRow data physical).chipSpec data) :
    StoreDoubleChip.Spec
      (circuitRowInputOf StoreDoubleChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreDoubleChip.circuit
        (Environment.fromArray physical data))
      data := by
  unfold storeDoubleChipDescriptor at h
  exact chipSpec_of_literalDescriptor StoreDoubleChip.kind StoreDoubleChip.circuit
    rfl [.SD] .any data physical h

theorem storeDoubleAdvanceReady_of_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (program : GuestProgram) (state : SailState)
    (h : StoreDoubleChip.AdvanceReady
      (circuitRowInputOf StoreDoubleChip.circuit
        (Environment.fromArray physical data))
      (circuitRowOutputOf StoreDoubleChip.circuit
        (Environment.fromArray physical data))
      program state) :
    ((storeDoubleChipDescriptor (p := p)).decodeRow data physical).kind.advanceReady
      ((storeDoubleChipDescriptor (p := p)).decodeRow data physical).inputs
      ((storeDoubleChipDescriptor (p := p)).decodeRow data physical).cols
      program state := by
  unfold storeDoubleChipDescriptor
  apply advanceReady_of_literalDescriptor StoreDoubleChip.kind StoreDoubleChip.circuit
    rfl [.SD] .any data physical program state
  exact h

omit [Fact (2 ^ 25 < p)] in
/-- StoreDouble's semantic row writes the complete authenticated RAM cell. -/
theorem storeDoubleChip_storeFacts
    (input : StoreDoubleChip.Inputs (ZMod p))
    (cols : StoreDoubleChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (real : (StoreDoubleChip.rowView input cols).is_real = 1)
    (_spec : StoreDoubleChip.Spec input cols data) :
    ∃ write : Trace.MemWrite (ZMod p),
      (StoreDoubleChip.rowView input cols).commit = Trace.CommitEffect.store write ∧
      write.InCell (ramCellOfAccess (StoreDoubleChip.ramAccessView input cols)) ∧
      RamCellUpdate write (ramCellOfAccess (StoreDoubleChip.ramAccessView input cols))
        (Word.toBitVec64 (StoreDoubleChip.ramAccessView input cols).priorValue)
        (Word.toBitVec64 (StoreDoubleChip.ramAccessView input cols).newValue) := by
  let addressInput : AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
  let access := StoreDoubleChip.ramAccessView input cols
  let write : Trace.MemWrite (ZMod p) :=
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 8⟩
  have addressEq :
      access.address = AddressOperation.alignedValue addressInput cols.address_operation := by
    rfl
  have realInput : input.is_real = 1 := by
    simpa only [StoreDoubleChip.rowView] using real
  have address :
      write.addrNat = (ramCellOfAccess access).baseAddr.toNat + addressOffset addressInput := by
    have raw := rawAddress_eq_ramCellBase_add_offset
      addressInput cols.address_operation access addressEq (_spec.1.2.2.2 realInput)
    simpa only [write, Trace.MemWrite.addrNat, address48Nat] using raw
  have offsetZero : addressOffset addressInput = 0 := by
    simp [addressOffset, addressInput]
  have addressZero : write.addrNat = (ramCellOfAccess access).baseAddr.toNat + 0 := by
    simpa only [offsetZero] using address
  refine ⟨write, rfl, Trace.MemWrite.inCell_of_address_width addressZero rfl (by norm_num), ?_⟩
  apply ramCellUpdate_of_patchedCell addressZero rfl
  rw [patchedCellBytes_zero_eight, cellBytesToWord_wordBytes]
  rfl

omit [Fact (2 ^ 25 < p)] in
theorem StoreDoubleChip.ramTimestampContract :
    CircuitRamAccessTimestampContract (p := p) (StoreDoubleChip.circuit (p := p))
      StoreDoubleChip.rowView
      (fun input cols => some (StoreDoubleChip.ramAccessView input cols)) := by
  let input : Var StoreDoubleChip.Inputs (ZMod p) := varFromOffset StoreDoubleChip.Inputs 0
  let offset := size StoreDoubleChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
  let readerInput : Var Readers.MemoryAccess.Inputs (ZMod p) :=
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[0],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[1],
      (AddressOperation.alignedValue addressInput
        ((AddressOperation.circuit (p := p)).output addressInput offset))[2],
      input.adapter.op_a_memory.prev_value, input.is_real⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, addressInput, readerInput, StoreDoubleChip.circuit,
      StoreDoubleChip.main, Readers.MemoryAccess.circuit, AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    constructor <;>
      simp only [input, readerInput, StoreDoubleChip.circuit, StoreDoubleChip.rowView,
        StoreDoubleChip.ramAccessView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreDoubleChip.ramAddressContract :
    CircuitRamAddressContract (p := p) (StoreDoubleChip.circuit (p := p))
      (fun input cols => some (StoreDoubleChip.ramAccessView input cols))
      (fun input => input.is_real) := by
  let input : Var StoreDoubleChip.Inputs (ZMod p) := varFromOffset StoreDoubleChip.Inputs 0
  let offset := size StoreDoubleChip.Inputs
  let addressInput : Var AddressOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
  refine .intro offset addressInput ?_ ?_ ?_
  · simp only [input, offset, addressInput, StoreDoubleChip.circuit, StoreDoubleChip.main,
      AddressOperation.circuit, circuit_norm]
  · intro env access haccess
    obtain rfl := Option.some.inj haccess
    simp only [input, offset, addressInput, StoreDoubleChip.circuit,
      StoreDoubleChip.ramAccessView, AddressOperation.alignedValue,
      AddressOperation.circuit, circuit_norm]
  · intro env
    simp only [input, addressInput, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem StoreDoubleChip.immutableItypeTimestampContract :
    CircuitImmutableITypeTimestampContract (p := p) (StoreDoubleChip.circuit (p := p))
      StoreDoubleChip.rowView := by
  let input : Var StoreDoubleChip.Inputs (ZMod p) := varFromOffset StoreDoubleChip.Inputs 0
  let offset := size StoreDoubleChip.Inputs
  let readerInput : Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 39⟩
  refine .intro (offset + 4) readerInput ?_ ?_
  · simp only [input, offset, readerInput, StoreDoubleChip.circuit, StoreDoubleChip.main,
      Readers.ITypeReaderImmutable.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, StoreDoubleChip.rowView,
        Extracted.ITypeReader.toAdapterView, circuit_norm]

theorem storeDoubleChip_viewOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    (DecodedInstructionRow.toChipRow
      ⟨storeDoubleChipDescriptor (p := p), physical⟩ data).view =
      circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView
        (Environment.fromArray physical data) := by
  chipViewOfDecoded storeDouble

theorem storeDoubleChip_ramAccessOf_decoded
    (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    decodedRamAccess ⟨storeDoubleChipDescriptor (p := p), physical⟩ data =
      circuitRamAccessOf StoreDoubleChip.circuit StoreDoubleChip.ramAccessView
        (Environment.fromArray physical data) := by
  chipRamAccessOfDecoded storeDouble

theorem storeDoubleChip_viewClockBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ViewClockBounds (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView
      (Environment.fromArray physical data)) := by
  chipViewClockBoundsEnv storeDouble

theorem storeDoubleChip_timestampBounds_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (guarantees : (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    ImmutableRamTimestampBounds
      (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView
        (Environment.fromArray physical data))
      (circuitRamAccessOf StoreDoubleChip.circuit StoreDoubleChip.ramAccessView
        (Environment.fromArray physical data)) := by
  rw [circuitRowViewOf_eq] at real ⊢
  rw [circuitRamAccessOf_eq]
  exact immutableRamTimestampBounds_of_contracts StoreDoubleChip.circuit
    StoreDoubleChip.rowView StoreDoubleChip.ramAccessView StoreDoubleChip.ramTimestampContract
    StoreDoubleChip.immutableItypeTimestampContract data physical constraints guarantees real

omit [Fact (2 ^ 25 < p)] in
theorem storeDoubleChip_isRam_env
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Component (ZMod p)).operations.ConstraintsHold
        (Environment.fromArray physical data))
    (real : (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView
      (Environment.fromArray physical data)).is_real = 1) :
    RamAccessIsRam
      (circuitRamAccessOf StoreDoubleChip.circuit StoreDoubleChip.ramAccessView
        (Environment.fromArray physical data)) := by
  chipIsRamEnv storeDouble (fun input => input.is_real)

theorem storeDoubleChip_viewClockBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeDoubleChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  chipViewClockBounds storeDouble

theorem storeDoubleChip_timestampBounds
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeDoubleChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ImmutableRamTimestampBounds (decoded.toChipRow data).view
      (decodedRamAccess decoded data) := by
  chipTimestampBounds storeDouble

theorem storeDoubleChip_isRam
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeDoubleChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RamAccessIsRam (decodedRamAccess decoded data) := by
  chipIsRam storeDouble

omit [Fact (2 ^ 25 < p)] in
/-- StoreDouble's public exposed Memory list evaluates to the immutable RAM/I-type layout. -/
theorem storeDoubleChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨StoreDoubleChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableRamMemoryInteractions
        (StoreDoubleChip.rowView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreDoubleChip.Inputs 0))
          (Eval.eval env ((StoreDoubleChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreDoubleChip.Inputs 0)
            (size StoreDoubleChip.Inputs))))
        (StoreDoubleChip.ramAccessView
          (Eval.eval env (varFromOffset (F := ZMod p) StoreDoubleChip.Inputs 0))
          (Eval.eval env ((StoreDoubleChip.circuit (p := p)).output
            (varFromOffset (F := ZMod p) StoreDoubleChip.Inputs 0)
            (size StoreDoubleChip.Inputs))))).map TypedInteraction.raw := by
  chipMemoryValues storeDouble immutableRamMemoryInteractions
  simp only [ramPriorMessage, ramPushMessage, rtypePriorMessage, rtypeReadBackMessage,
    StoreDoubleChip.rowView, StoreDoubleChip.ramAccessView, AddressOperation.alignedValue,
    Extracted.ITypeReader.toAdapterView, StoreDoubleChip.circuit, circuit_norm]

theorem storeDoubleChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = storeDoubleChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableRamMemoryInteractions (decoded.toChipRow data).view
        (decodedRamAccess decoded data) := by
  chipTypedMemoryInteractions storeDouble immutableRamMemoryInteractions

/-- StoreDouble instantiates the authenticated immutable RAM/I-type interaction shape. -/
noncomputable def storeDoubleChip_immutableRamMemoryInteractionShape :
    ImmutableRamMemoryInteractionShape (storeDoubleChipDescriptor (p := p)) where
  access := decodedRamAccess
  access_eq := by
    chipShapeAccessEq
  interactions := storeDoubleChip_typedMemoryInteractions_eq

end StoreDouble

end MemoryShape

end SP1Clean.Soundness
