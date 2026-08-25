import SP1Clean.Soundness.Grounding.ITypeChips
import SP1Clean.Proofs.Chips.AddwChip.Contracts
import SP1Clean.Proofs.Chips.BitwiseChip.Contracts
import SP1Clean.Proofs.Chips.LtChip.Contracts
import SP1Clean.Proofs.Chips.ShiftLeftChip.Contracts
import SP1Clean.Proofs.Chips.ShiftRightChip.Contracts

/-! # Canonical immediate-capable ALU grounding

`Addw`, Bitwise, Lt, ShiftLeft, and ShiftRight share SP1's `ALUTypeReader`.  Their source-C
Memory pull/read-back pair is present exactly on the register form (`imm_c = 0`) and absent on the
immediate form (`imm_c = 1`).  This module states that physical shape once and reduces the two cases
to the already-audited R-type and I-type timed wiring.
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

/-- Substitute a decoded row's descriptor.  This removes only the constructor/substitution preamble
every per-chip lemma below repeats; the caller's `decoded`/`hchip` binders are referenced by name
and the destructured `physical` stays visible to the closer, so a signature mismatch is a loud
`unknown identifier`. -/
local macro "descriptorSubst " desc:term : tactic => do
  let decoded := Lean.mkIdent `decoded
  let hchip := Lean.mkIdent `hchip
  let physical := Lean.mkIdent `physical
  `(tactic| (
    obtain ⟨chip, $physical:ident⟩ := $decoded
    have descriptorEq : chip = $desc := $hchip
    subst descriptorEq))

/-- Discharge a `viewOf` state projection from the chip's own input/output state binding.  Only the
chip names and the `viewOf`/`rowView` unfold set vary. -/
local macro "aluViewState " inputs:term ", " circuit:term ", " inputOutput:term ", "
    unfolds:Lean.Parser.Tactic.simpLemma,* : tactic => do
  let env := Lean.mkIdent `env
  `(tactic| (
    have inputEq : Eval.eval $env (varFromOffset $inputs 0) =
        (⟨$circuit (p := p)⟩ : Component (ZMod p)).rowInput $env :=
      eval_varFromOffset_valueFromOffset $inputs 0 $env
    simp only [$unfolds,*]
    exact ($inputOutput $env).symm.trans
      (congrArg (fun input : $inputs (ZMod p) => input.state) inputEq.symm)))

/-- As `aluViewState`, for the adapter projection through the shared `ALUTypeReader` view map. -/
local macro "aluViewAdapter " inputs:term ", " circuit:term ", " inputOutput:term ", "
    unfolds:Lean.Parser.Tactic.simpLemma,* : tactic => do
  let env := Lean.mkIdent `env
  `(tactic| (
    have inputEq : Eval.eval $env (varFromOffset $inputs 0) =
        (⟨$circuit (p := p)⟩ : Component (ZMod p)).rowInput $env :=
      eval_varFromOffset_valueFromOffset $inputs 0 $env
    simp only [$unfolds,*]
    exact congrArg Extracted.ALUTypeReader.toAdapterView
      (($inputOutput $env).symm.trans
        (congrArg (fun input : $inputs (ZMod p) => input.adapter) inputEq.symm))))

/-- Open a chip's Memory-interaction evaluation at its own `main`, without unfolding the completed
circuit: rewrite the component list, restate it at `main`, then apply the chip's exposed list. -/
local macro "memoryValuesPreamble " inputs:term ", " main:term ", " interEq:term : tactic => do
  let env := Lean.mkIdent `env
  `(tactic| (
    rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
    change List.map (AbstractInteraction.eval $env)
        ((($main (varFromOffset $inputs 0)).operations
          (size $inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
    rw [$interEq:term]))

section Shape

variable [Fact (2 ^ 25 < p)]

/-- The exact six physical Memory interactions of an immediate-capable ALU reader.  Zero-gated
source-C entries remain in this physical list; `consumedMessages`/`producedMessages` erase them. -/
noncomputable def aluViewMemoryInteractions (view : Trace.RowView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   TypedInteraction.pulledIfValue memoryChannel (view.is_real - view.adapter.imm_c)
      (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory),
   TypedInteraction.pushedIfValue memoryChannel (view.is_real - view.adapter.imm_c)
      (rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2),
   TypedInteraction.pushedIfValue memoryChannel view.is_real (rtypeWriteMessage view)]

/-- Descriptor-level physical shape of an immediate-capable ALU chip. -/
def ALUTypeMemoryInteractionShape (chip : SupportedChip p) : Prop :=
  ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        aluViewMemoryInteractions (decoded.toChipRow data).view

/-- Canonical ALU Memory shape on a constraint-satisfying physical row. Shift chips need this
honest form because upstream gates some accesses by the opcode-flag sum, which the AIR equates to
the independent `is_real` input but which is not definitionally equal on an arbitrary row. -/
def ConstrainedALUTypeMemoryInteractionShape (chip : SupportedChip p) : Prop :=
  ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
      decoded.interactionsWith data memoryChannel =
        aluViewMemoryInteractions (decoded.toChipRow data).view

/-- The exact physical six-pack of an immutable ALU reader. All three slots are reads; C is gated
off on immediate instructions, while A is read back at `+4` instead of becoming a destination
write. -/
noncomputable def immutableAluViewMemoryInteractions (view : Trace.RowView (ZMod p)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  [TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_a view.adapter.op_a_memory 4),
   TypedInteraction.pulledIfValue memoryChannel view.is_real
      (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory),
   TypedInteraction.pushedIfValue memoryChannel view.is_real
      (rtypeReadBackMessage view view.adapter.op_b[0] view.adapter.op_b_memory 3),
   TypedInteraction.pulledIfValue memoryChannel (view.is_real - view.adapter.imm_c)
      (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory),
   TypedInteraction.pushedIfValue memoryChannel (view.is_real - view.adapter.imm_c)
      (rtypeReadBackMessage view view.adapter.op_c[0] view.adapter.op_c_memory 2)]

/-- Descriptor-level structural contract for an immutable immediate-capable ALU reader. -/
structure ImmutableALUTypeMemoryInteractionShape (chip : SupportedChip p) : Prop where
  interactions : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      decoded.interactionsWith data memoryChannel =
        immutableAluViewMemoryInteractions (decoded.toChipRow data).view
  imm_b_eq_zero : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip → (decoded.toChipRow data).view.adapter.imm_b = 0

/-- An unconditional physical six-pack is, in particular, canonical on satisfying rows. -/
theorem ALUTypeMemoryInteractionShape.constrained {chip : SupportedChip p}
    (shape : ALUTypeMemoryInteractionShape chip) :
    ConstrainedALUTypeMemoryInteractionShape chip := by
  intro decoded data hchip _
  exact shape decoded data hchip

omit [Fact (2 ^ 25 < p)] in
private theorem pull_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 msg).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem push_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 1 msg).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] [Fact (2 ^ 17 < p)] in
private theorem pull_zero_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 0 msg).mult = 0 := by
  simp [TypedInteraction.pulledIfValue_mult, signedVal, ZMod.val_zero]

omit [Fact (2 ^ 25 < p)] [Fact (2 ^ 17 < p)] in
private theorem push_zero_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 0 msg).mult = 0 := by
  simp [TypedInteraction.pushedIfValue_mult, signedVal, ZMod.val_zero]

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_registerSix (a b rb c rc w : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 1 c,
       TypedInteraction.pushedIfValue memoryChannel 1 rc,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [a, b, c] := by
  unfold consumedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_registerSix (a b rb c rc w : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 1 c,
       TypedInteraction.pushedIfValue memoryChannel 1 rc,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [rb, rc, w] := by
  unfold producedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_immediateSix (a b rb c rc w : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 0 c,
       TypedInteraction.pushedIfValue memoryChannel 0 rc,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [a, b] := by
  unfold consumedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed,
    pull_zero_signed, push_zero_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_immediateSix (a b rb c rc w : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 0 c,
       TypedInteraction.pushedIfValue memoryChannel 0 rc,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [rb, w] := by
  unfold producedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed,
    pull_zero_signed, push_zero_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_immutableAluRegister
    (a ra b rb c rc : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 1 c,
       TypedInteraction.pushedIfValue memoryChannel 1 rc] = [a, b, c] := by
  unfold consumedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_immutableAluRegister
    (a ra b rb c rc : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 1 c,
       TypedInteraction.pushedIfValue memoryChannel 1 rc] = [ra, rb, rc] := by
  unfold producedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem consumedMessages_immutableAluImmediate
    (a ra b rb c rc : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 0 c,
       TypedInteraction.pushedIfValue memoryChannel 0 rc] = [a, b] := by
  unfold consumedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed,
    pull_zero_signed, push_zero_signed]
  norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem producedMessages_immutableAluImmediate
    (a ra b rb c rc : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 a,
       TypedInteraction.pushedIfValue memoryChannel 1 ra,
       TypedInteraction.pulledIfValue memoryChannel 1 b,
       TypedInteraction.pushedIfValue memoryChannel 1 rb,
       TypedInteraction.pulledIfValue memoryChannel 0 c,
       TypedInteraction.pushedIfValue memoryChannel 0 rc] = [ra, rb] := by
  unfold producedMessages
  simp only [List.filter_cons, List.filter_nil, pull_one_signed, push_one_signed,
    pull_zero_signed, push_zero_signed]
  norm_num

/-- Active register-form ALU rows consume destination, B, and C prior records. -/
theorem consumedMemoryMessages_eq_of_aluType_register {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (register : (decoded.toChipRow data).view.adapter.imm_c = 0) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_c[0]
          (decoded.toChipRow data).view.adapter.op_c_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape decoded data hchip constraints]
  unfold aluViewMemoryInteractions
  rw [real, register]
  simp only [sub_zero]
  exact consumedMessages_registerSix _ _ _ _ _ _

/-- Active register-form ALU rows produce B/C read-backs and the destination write. -/
theorem producedMemoryMessages_eq_of_aluType_register {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (register : (decoded.toChipRow data).view.adapter.imm_c = 0) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_c[0]
          (decoded.toChipRow data).view.adapter.op_c_memory 2,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape decoded data hchip constraints]
  unfold aluViewMemoryInteractions
  rw [real, register]
  simp only [sub_zero]
  exact producedMessages_registerSix _ _ _ _ _ _

/-- Active immediate-form ALU rows consume only destination and source-B prior records. -/
theorem consumedMemoryMessages_eq_of_aluType_immediate {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape decoded data hchip constraints]
  unfold aluViewMemoryInteractions
  rw [real, immediate]
  simp only [sub_self]
  exact consumedMessages_immediateSix _ _ _ _ _ _

/-- Active immediate-form ALU rows produce B's read-back and the destination write. -/
theorem producedMemoryMessages_eq_of_aluType_immediate {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape decoded data hchip constraints]
  unfold aluViewMemoryInteractions
  rw [real, immediate]
  simp only [sub_self]
  exact producedMessages_immediateSix _ _ _ _ _ _

/-- An active immutable register-form ALU row consumes all three register priors. -/
theorem consumedMemoryMessages_eq_of_immutableAlu_register {chip : SupportedChip p}
    (shape : ImmutableALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (register : (decoded.toChipRow data).view.adapter.imm_c = 0) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_c[0]
          (decoded.toChipRow data).view.adapter.op_c_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableAluViewMemoryInteractions
  rw [real, register]
  simp only [sub_zero]
  exact consumedMessages_immutableAluRegister _ _ _ _ _ _

/-- An active immutable register-form ALU row produces three source read-backs. -/
theorem producedMemoryMessages_eq_of_immutableAlu_register {chip : SupportedChip p}
    (shape : ImmutableALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (register : (decoded.toChipRow data).view.adapter.imm_c = 0) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory 4,
       rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_c[0]
          (decoded.toChipRow data).view.adapter.op_c_memory 2] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableAluViewMemoryInteractions
  rw [real, register]
  simp only [sub_zero]
  exact producedMessages_immutableAluRegister _ _ _ _ _ _

/-- An active immutable immediate-form ALU row consumes A and B; C is an immediate. -/
theorem consumedMemoryMessages_eq_of_immutableAlu_immediate {chip : SupportedChip p}
    (shape : ImmutableALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableAluViewMemoryInteractions
  rw [real, immediate]
  simp only [sub_self]
  exact consumedMessages_immutableAluImmediate _ _ _ _ _ _

/-- An active immutable immediate-form ALU row produces A and B read-backs. -/
theorem producedMemoryMessages_eq_of_immutableAlu_immediate {chip : SupportedChip p}
    (shape : ImmutableALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (real : (decoded.toChipRow data).view.is_real = 1)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_a
          (decoded.toChipRow data).view.adapter.op_a_memory 4,
       rtypeReadBackMessage (decoded.toChipRow data).view
          (decoded.toChipRow data).view.adapter.op_b[0]
          (decoded.toChipRow data).view.adapter.op_b_memory 3] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [shape.interactions decoded data hchip]
  unfold immutableAluViewMemoryInteractions
  rw [real, immediate]
  simp only [sub_self]
  exact producedMessages_immutableAluImmediate _ _ _ _ _ _

/-- Exact register pulls for both ALU reader modes. -/
theorem registerOperandPullShape_of_aluTypeShape {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip) :
    DecodedInstructionRow.RegisterOperandPullShape chip := by
  constructor
  · intro data physical program state
    dsimp only
    intro ready constraints real index immediate indexEq
    let decoded : DecodedInstructionRow p := ⟨chip, physical⟩
    let view := (decoded.toChipRow data).view
    change view.is_real = 1 at real
    let message := rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory
    let pullB := TypedInteraction.pulledIfValue memoryChannel view.is_real message
    have pullBMem : pullB ∈ decoded.interactionsWith data memoryChannel := by
      rw [shape decoded data rfl constraints]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    have pullBNegative : signedVal pullB.mult = -1 := by
      simpa only [pullB, real] using (pull_one_signed (p := p) message)
    refine ⟨message, ?_, ?_, rfl⟩
    · have member := TypedInteraction.message_mem_consumedMessages pullB _ pullBMem pullBNegative
      change message ∈ decoded.consumedMemoryMessages data
      unfold DecodedInstructionRow.consumedMemoryMessages
      simpa only [pullB, TypedInteraction.pulledIfValue_message] using member
    · exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl
  · intro data physical program state
    dsimp only
    intro ready constraints real index immediate indexEq
    let decoded : DecodedInstructionRow p := ⟨chip, physical⟩
    let view := (decoded.toChipRow data).view
    change view.is_real = 1 at real
    change view.adapter.imm_c = 0 at immediate
    have consumed := consumedMemoryMessages_eq_of_aluType_register shape decoded data rfl
      constraints real immediate
    let message := rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory
    refine ⟨message, ?_, ?_, rfl⟩
    · change message ∈ decoded.consumedMemoryMessages data
      rw [consumed]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Semantics.MemoryMsg.locOf_register message index indexEq rfl rfl

/-- Source-B is always range-grounded; source C is range-grounded on the register form. -/
theorem aluTypeOperandWords_isU64_of_shape {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (guarantees : decoded.chip.table.operations.ChannelGuarantees memoryChannel.toRaw
      (decoded.environment data)) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_b_memory.prev_value ∧
      ((decoded.toChipRow data).view.adapter.imm_c = 0 →
        Word.isU64 (decoded.toChipRow data).view.adapter.op_c_memory.prev_value) := by
  let view := (decoded.toChipRow data).view
  let pullB := TypedInteraction.pulledIfValue memoryChannel view.is_real
    (rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory)
  have pullBMem : pullB ∈ decoded.interactionsWith data memoryChannel := by
    rw [shape decoded data hchip constraints]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have pullBNegative : pullB.mult = -1 := by
    simp only [pullB, TypedInteraction.pulledIfValue_mult, view, real]
  have bGuarantee := TypedInteraction.guarantee_of_channelGuarantees
    decoded.chip.table.operations memoryChannel (decoded.environment data) pullB pullBMem
    guarantees (by rfl) pullBNegative
  constructor
  · simpa only [Channels.memoryChannel, pullB, TypedInteraction.pulledIfValue_message,
      MemoryMsg.isU64, rtypePriorMessage] using bGuarantee.1
  · intro register
    let pullC := TypedInteraction.pulledIfValue memoryChannel
      (view.is_real - view.adapter.imm_c)
      (rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory)
    have pullCMem : pullC ∈ decoded.interactionsWith data memoryChannel := by
      rw [shape decoded data hchip constraints]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have pullCNegative : pullC.mult = -1 := by
      simp only [pullC, TypedInteraction.pulledIfValue_mult, view, real, register, sub_zero]
    have cGuarantee := TypedInteraction.guarantee_of_channelGuarantees
      decoded.chip.table.operations memoryChannel (decoded.environment data) pullC pullCMem
      guarantees (by rfl) pullCNegative
    simpa only [Channels.memoryChannel, pullC, TypedInteraction.pulledIfValue_message,
      MemoryMsg.isU64, rtypePriorMessage] using cGuarantee.1

/-- Byte-derived timestamp bounds for an ALU reader.  The C bound is conditional on the register
form because the immediate form gates that reader slot off. -/
def ALUTypeTimestampBounds (view : Trace.RowView (ZMod p)) : Prop :=
  ActiveTimestampBounds view.adapter.op_a_memory.access_timestamp.prev_low
      view.adapter.op_a_memory.access_timestamp.diff_low_limb
      (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4) ∧
    ActiveTimestampBounds view.adapter.op_b_memory.access_timestamp.prev_low
      view.adapter.op_b_memory.access_timestamp.diff_low_limb
      (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 3) ∧
    (view.adapter.imm_c = 0 →
      ActiveTimestampBounds view.adapter.op_c_memory.access_timestamp.prev_low
        view.adapter.op_c_memory.access_timestamp.diff_low_limb
        (view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 2))

/-- Scalar binding from the retained ALU reader to its public row view. -/
structure ALUTypeTimestampBinding
    (readerReal readerImm aPrev aDiff bPrev bDiff cPrev cDiff targetA targetB targetC : ZMod p)
    (view : Trace.RowView (ZMod p)) : Prop where
  real_eq : readerReal = view.is_real
  imm_eq : readerImm = view.adapter.imm_c
  aPrev_eq : aPrev = view.adapter.op_a_memory.access_timestamp.prev_low
  aDiff_eq : aDiff = view.adapter.op_a_memory.access_timestamp.diff_low_limb
  bPrev_eq : bPrev = view.adapter.op_b_memory.access_timestamp.prev_low
  bDiff_eq : bDiff = view.adapter.op_b_memory.access_timestamp.diff_low_limb
  cPrev_eq : cPrev = view.adapter.op_c_memory.access_timestamp.prev_low
  cDiff_eq : cDiff = view.adapter.op_c_memory.access_timestamp.diff_low_limb
  targetA_eq : targetA = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4
  targetB_eq : targetB = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 3
  targetC_eq : targetC = view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 2

/-- Locate the retained ALU reader without exposing a completed chip circuit to consumers. -/
inductive CircuitALUTypeTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (readerOffset : ℕ) (readerInput : Var Readers.ALUTypeReader.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.ALUTypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold env →
        ALUTypeTimestampBinding
          (Expression.eval env readerInput.is_real)
          (Expression.eval env readerInput.cols.imm_c)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_c_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_c_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (readerInput.clk_low + 4))
          (Expression.eval env (readerInput.clk_low + 3))
          (Expression.eval env (readerInput.clk_low + 2))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env
              (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))) :
      CircuitALUTypeTimestampContract circuit view

/-- Finished Byte guarantees specialize a retained ALU reader to its semantic row. -/
theorem aluTypeTimestampBounds_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitALUTypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (constraints : (⟨circuit⟩ : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromArray physical data))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    ALUTypeTimestampBounds (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.ALUTypeReader.circuit (p := p)).toSubcircuit readerOffset readerInput)
    readerMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env
      (circuit.output (varFromOffset Input 0) (size Input)) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env constraints
  rw [inputEq, outputEq] at bound
  have readerReal : Expression.eval env readerInput.is_real = 1 := bound.real_eq.trans real
  have timestampBounds := Readers.ALUTypeReader.timestampSpecs_of_byteGuarantees readerInput
    readerOffset env readerGuarantees readerReal
  unfold ALUTypeTimestampBounds
  rwa [bound.imm_eq, bound.aPrev_eq, bound.aDiff_eq, bound.bPrev_eq, bound.bDiff_eq,
    bound.cPrev_eq, bound.cDiff_eq, bound.targetA_eq, bound.targetB_eq,
    bound.targetC_eq] at timestampBounds

/-- Locate a retained immutable ALU reader without unfolding the completed parent circuit. -/
inductive CircuitImmutableALUTypeTimestampContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop where
  | intro (readerOffset : ℕ)
      (readerInput : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p))
      (reader_mem :
        ⟨readerOffset,
          (Readers.ALUTypeReaderImmutable.circuit (p := p)).toSubcircuit
            readerOffset readerInput⟩ ∈
          ((circuit.main (varFromOffset (F := ZMod p) Input 0)).operations
            (size Input)).subcircuits)
      (binding : ∀ env : Environment (ZMod p),
        ALUTypeTimestampBinding
          (Expression.eval env readerInput.is_real)
          (Expression.eval env readerInput.cols.imm_c)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_a_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_b_memory.access_timestamp.diff_low_limb)
          (Expression.eval env readerInput.cols.op_c_memory.access_timestamp.prev_low)
          (Expression.eval env readerInput.cols.op_c_memory.access_timestamp.diff_low_limb)
          (Expression.eval env (readerInput.clk_low + 4))
          (Expression.eval env (readerInput.clk_low + 3))
          (Expression.eval env (readerInput.clk_low + 2))
          (view (Eval.eval env (varFromOffset (F := ZMod p) Input 0))
            (Eval.eval env
              (circuit.output (varFromOffset (F := ZMod p) Input 0) (size Input))))) :
      CircuitImmutableALUTypeTimestampContract circuit view

/-- Finished Byte guarantees specialize a retained immutable ALU reader to its semantic row. -/
theorem immutableAluTypeTimestampBounds_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitImmutableALUTypeTimestampContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))).is_real = 1) :
    ALUTypeTimestampBounds (view ((⟨circuit⟩ : Component (ZMod p)).rowInput
      (Environment.fromArray physical data)) ((⟨circuit⟩ : Component (ZMod p)).rowOutput
        (Environment.fromArray physical data))) := by
  obtain ⟨readerOffset, readerInput, readerMem, binding⟩ := contract
  let component : Component (ZMod p) := ⟨circuit⟩
  let env := Environment.fromArray physical data
  have rowGuarantees : component.rowOperations.ChannelGuarantees byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env byteChannel.toRaw).mp guarantees
  have readerGuarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env
    component.rowOperations
    ((Readers.ALUTypeReaderImmutable.circuit (p := p)).toSubcircuit readerOffset readerInput)
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
  have timestampBounds :=
    Readers.ALUTypeReaderImmutable.timestampSpecs_of_byteGuarantees readerInput
      readerOffset env readerGuarantees readerReal
  unfold ALUTypeTimestampBounds
  rwa [bound.imm_eq, bound.aPrev_eq, bound.aDiff_eq, bound.bPrev_eq, bound.bDiff_eq,
    bound.cPrev_eq, bound.cDiff_eq, bound.targetA_eq, bound.targetB_eq,
    bound.targetC_eq] at timestampBounds

/-- Conditional ALU wiring: register rows reuse the six-pack, immediate rows the four-pack. -/
theorem rowWiring_aluType_of_shape {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq : (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite)
    (immBinary : (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 (decoded.toChipRow data).view.rdWrite) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  rcases immBinary with register | immediate
  · have consumed := consumedMemoryMessages_eq_of_aluType_register shape decoded data hchip
      constraints real register
    have produced := producedMemoryMessages_eq_of_aluType_register shape decoded data hchip
      constraints real register
    exact rowWiring_rtype_of_decoded decoded data bounds commit_eq opa_lt write_isU64 consumed produced
  · have consumed := consumedMemoryMessages_eq_of_aluType_immediate shape decoded data hchip
      constraints real immediate
    have produced := producedMemoryMessages_eq_of_aluType_immediate shape decoded data hchip
      constraints real immediate
    exact rowWiring_itype_of_decoded decoded data bounds commit_eq immediate opa_lt write_isU64
      consumed produced

/-- Conditional aligned carrier for the two ALU reader modes. -/
theorem rowAligned_aluType_of_shape {chip : SupportedChip p}
    (shape : ConstrainedALUTypeMemoryInteractionShape chip)
    (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = chip)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (timestamps : ALUTypeTimestampBounds (decoded.toChipRow data).view)
    (immBinary : (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (opb_lt : (decoded.toChipRow data).view.adapter.op_b[0].val < 32)
    (opc_lt : (decoded.toChipRow data).view.adapter.imm_c = 0 →
      (decoded.toChipRow data).view.adapter.op_c[0].val < 32) :
    ∃ touches : List (Touch p),
      AlignsWith (alignedOf (decoded.ordinaryRowFacts data) touches)
          (decoded.ordinaryRowFacts data) ∧
        (∀ tc ∈ touches,
          TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts data).statePull) tc.1 tc.2) ∧
        (∀ loc : MemLoc, List.IsChain
          (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
          (touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
        (∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
        (∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          (tc : Touch p).1.1.clk_high.val < 2 ^ 24 →
            MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) := by
  rcases immBinary with register | immediate
  · refine ⟨rtypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data), ?_⟩
    have consumed := consumedMemoryMessages_eq_of_aluType_register shape decoded data hchip
      constraints real register
    have produced := producedMemoryMessages_eq_of_aluType_register shape decoded data hchip
      constraints real register
    obtain ⟨timestampA, timestampB, timestampCOf⟩ := timestamps
    have timestampC := timestampCOf register
    have slots : ∀ tc ∈ rtypeTouches (decoded.toChipRow data).view
        (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          (tc : Touch p).1.1.clk_high.val < 2 ^ 24 →
            MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
      intro tc htc hclk _
      simp only [rtypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl
      · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
          _ _ _ _ _ hclk timestampC rfl rfl rfl
      · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
          _ _ _ _ _ hclk timestampB rfl rfl rfl
      · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
          _ _ _ _ _ hclk timestampA rfl rfl rfl
    refine rowAligned_rtype bounds real opa_lt opb_lt (opc_lt register) rfl ?_ ?_ slots
    · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
      rfl
    · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
      exact produced
  · refine ⟨itypeTouches (decoded.toChipRow data).view (decoded.ordinaryRowFacts data), ?_⟩
    have consumed := consumedMemoryMessages_eq_of_aluType_immediate shape decoded data hchip
      constraints real immediate
    have produced := producedMemoryMessages_eq_of_aluType_immediate shape decoded data hchip
      constraints real immediate
    obtain ⟨timestampA, timestampB, -⟩ := timestamps
    have slots : ∀ tc ∈ itypeTouches (decoded.toChipRow data).view
        (decoded.ordinaryRowFacts data),
        SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
          (tc : Touch p).1.1.clk_high.val < 2 ^ 24 →
            MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
      intro tc htc hclk _
      simp only [itypeTouches, List.mem_cons, List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl
      · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
          _ _ _ _ _ hclk timestampB rfl rfl rfl
      · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
          _ _ _ _ _ hclk timestampA rfl rfl rfl
    refine rowAligned_itype bounds real opa_lt opb_lt rfl ?_ ?_ slots
    · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
      rfl
    · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
      exact produced

end Shape

section Addw

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The immediate-capable Addw descriptor in the supported Core registry. -/
def addwChipDescriptor : SupportedChip p :=
  ⟨.addw, AddwChip.kind, AddwChip.circuit, rfl⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def addwViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  AddwChip.rowView
    ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem addwViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((addwChipDescriptor (p := p)).decodeRow data physical).view =
      addwViewOf (Environment.fromArray physical data) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem addwChipDescriptor_table :
    (addwChipDescriptor (p := p)).table =
      (⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem addwViewOf_state (env : Environment (ZMod p)) :
    (addwViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) AddwChip.Inputs 0)).state := by
  aluViewState AddwChip.Inputs, AddwChip.circuit, AddwChip.inputOutputState,
    addwViewOf, AddwChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem addwViewOf_adapter (env : Environment (ZMod p)) :
    (addwViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) AddwChip.Inputs 0)).adapter.toAdapterView := by
  aluViewAdapter AddwChip.Inputs, AddwChip.circuit, AddwChip.inputOutputAdapter,
    addwViewOf, AddwChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem addwViewOf_opA0 (env : Environment (ZMod p)) :
    (addwViewOf env).adapter.op_a_0 =
      Expression.eval env
        (varFromOffset (F := ZMod p) AddwChip.Inputs 0).adapter.op_a_0 := by
  rw [addwViewOf_adapter]
  change (Eval.eval env
    (varFromOffset (F := ZMod p) AddwChip.Inputs 0)).adapter.op_a_0 = _
  rw [AddwChip.eval_inputAdapter]
  exact Readers.ALUTypeReader.eval_opA0 env _

omit [Fact (2 ^ 25 < p)] in
theorem addwViewOf_isReal (env : Environment (ZMod p)) :
    (addwViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) AddwChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset AddwChip.Inputs 0) =
      (⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddwChip.Inputs 0 env
  simpa only [addwViewOf, AddwChip.rowView] using
    congrArg (fun input : AddwChip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] in
theorem addwViewOf_rdWrite (env : Environment (ZMod p)) :
    (addwViewOf env).rdWrite =
      Eval.eval env
        (#v[var { index := size AddwChip.Inputs },
            var { index := size AddwChip.Inputs + 1 },
            var { index := size AddwChip.Inputs + 2 } * 65535,
            var { index := size AddwChip.Inputs + 2 } * 65535] :
          Word (Expression (ZMod p))) := by
  let input : Var AddwChip.Inputs (ZMod p) := varFromOffset AddwChip.Inputs 0
  let offset := size AddwChip.Inputs
  have outputEq : Eval.eval env ((AddwChip.circuit (p := p)).output input offset) =
      (⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  simp only [addwViewOf, AddwChip.rowView, AddwChip.resultWord]
  rw [← outputEq]
  change AddwChip.resultWord
    (Eval.eval env ((AddwChip.elaborated (p := p)).output input offset)) = _
  rw [AddwChip.directOutput_eq, AddwChip.eval_columns]
  apply Vector.ext; intro i hi
  interval_cases i <;> simp only [offset, AddwChip.resultWord,
    Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- Addw's completed exposed Memory list evaluates to the canonical conditional six-pack. -/
theorem addwChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (aluViewMemoryInteractions (addwViewOf env)).map TypedInteraction.raw := by
  memoryValuesPreamble AddwChip.Inputs, AddwChip.main, AddwChip.interactionsWith_memory_eq
  simp only [AddwChip.exposedMemoryInteractions, aluViewMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    addwViewOf_state, addwViewOf_adapter, addwViewOf_isReal, addwViewOf_rdWrite,
    Extracted.ALUTypeReader.toAdapterView, circuit_norm]

/-- Lift Addw's evaluated conditional six-pack to the typed decoded-row boundary. -/
theorem addwChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addwChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      aluViewMemoryInteractions (decoded.toChipRow data).view := by
  descriptorSubst addwChipDescriptor (p := p)
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    addwViewOf_decodeRow, addwChipDescriptor_table] using
    addwChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Addw instantiates the canonical immediate-capable ALU Memory shape. -/
theorem addwChip_aluTypeMemoryInteractionShape :
    ALUTypeMemoryInteractionShape (addwChipDescriptor (p := p)) :=
  addwChip_typedMemoryInteractions_eq

omit [Fact (2 ^ 25 < p)] in
/-- Addw's retained reader through the scalar ALU timestamp contract. -/
theorem AddwChip.aluTypeTimestampContract :
    CircuitALUTypeTimestampContract (p := p) (AddwChip.circuit (p := p))
      AddwChip.rowView := by
  let input : Var AddwChip.Inputs (ZMod p) := varFromOffset AddwChip.Inputs 0
  let offset := size AddwChip.Inputs
  let readerInput := AddwChip.aluTypeReaderInput input offset
  refine .intro (offset + 3) readerInput (AddwChip.aluTypeReader_mem input offset) ?_
  intro env _constraints
  constructor <;>
    simp only [input, offset, readerInput, AddwChip.aluTypeReaderInput, AddwChip.circuit,
      AddwChip.rowView, Extracted.ALUTypeReader.toAdapterView, circuit_norm]

theorem addwChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addwChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  descriptorSubst addwChipDescriptor (p := p)
  exact viewClockBounds_of_cpuStateContract (AddwChip.circuit (p := p)) AddwChip.rowView
    AddwChip.cpuStateTimeContract data physical guarantees real

theorem addwChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addwChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ALUTypeTimestampBounds (decoded.toChipRow data).view := by
  descriptorSubst addwChipDescriptor (p := p)
  exact aluTypeTimestampBounds_of_contract AddwChip.circuit AddwChip.rowView
    AddwChip.aluTypeTimestampContract data physical constraints guarantees real

/-- The committed decode supplies Addw's register/immediate selector bit. -/
theorem addwChip_immBinary {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow) :
    (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1 := by
  simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2

/-- On Addw's immediate form, the committed operand is a canonical 64-bit word. -/
theorem addwChip_immediate_isU64 {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_c :=
  decode.immediate_words_isU64.2 (by
    simpa only [programAccess, ProgramAccess.toRow] using immediate)

/-- Descriptor-level form of Addw's physical immediate-consistency binding. -/
theorem addwChip_opCBinding_of_constraints (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addwChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    (decoded.toChipRow data).view.adapter.op_c_memory.prev_value =
      (decoded.toChipRow data).view.adapter.op_c := by
  descriptorSubst addwChipDescriptor (p := p)
  exact AddwChip.rowViewOpCBinding_of_constraints
    (Environment.fromArray physical data) constraints immediate

end Addw

section Bitwise

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The immediate-capable Bitwise descriptor in the supported Core registry. -/
def bitwiseChipDescriptor : SupportedChip p :=
  ⟨.bitwise, BitwiseChip.kind, BitwiseChip.circuit, rfl⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def bitwiseViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  BitwiseChip.physicalView env

theorem bitwiseViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((bitwiseChipDescriptor (p := p)).decodeRow data physical).view =
      bitwiseViewOf (Environment.fromArray physical data) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem bitwiseChipDescriptor_table :
    (bitwiseChipDescriptor (p := p)).table =
      (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem bitwiseViewOf_state (env : Environment (ZMod p)) :
    (bitwiseViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) BitwiseChip.Inputs 0)).state := by
  aluViewState BitwiseChip.Inputs, BitwiseChip.circuit, BitwiseChip.inputOutputState,
    bitwiseViewOf, BitwiseChip.physicalView, BitwiseChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem bitwiseViewOf_adapter (env : Environment (ZMod p)) :
    (bitwiseViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) BitwiseChip.Inputs 0)).adapter.toAdapterView := by
  aluViewAdapter BitwiseChip.Inputs, BitwiseChip.circuit, BitwiseChip.inputOutputAdapter,
    bitwiseViewOf, BitwiseChip.physicalView, BitwiseChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem bitwiseViewOf_isReal (env : Environment (ZMod p)) :
    (bitwiseViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) BitwiseChip.Inputs 0)).is_real :=
  BitwiseChip.physicalView_isReal env

omit [Fact (2 ^ 25 < p)] in
theorem bitwiseViewOf_rdWrite (env : Environment (ZMod p)) :
    (bitwiseViewOf env).rdWrite =
      Eval.eval env
        (#v[var { index := size BitwiseChip.Inputs + 11 } +
              var { index := size BitwiseChip.Inputs + 12 } * 256,
            var { index := size BitwiseChip.Inputs + 13 } +
              var { index := size BitwiseChip.Inputs + 14 } * 256,
            var { index := size BitwiseChip.Inputs + 15 } +
              var { index := size BitwiseChip.Inputs + 16 } * 256,
            var { index := size BitwiseChip.Inputs + 17 } +
              var { index := size BitwiseChip.Inputs + 18 } * 256] :
          Word (Expression (ZMod p))) := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  have outputEq : Eval.eval env ((BitwiseChip.circuit (p := p)).output input offset) =
      BitwiseChip.physicalCols env := by
    simp only [input, offset, BitwiseChip.physicalCols, Component.rowOutput, circuit_norm]
  simp only [bitwiseViewOf, BitwiseChip.physicalView, BitwiseChip.rowView]
  rw [← outputEq]
  change BitwiseU16Operation.resultWord
      ((Eval.eval env ((BitwiseChip.elaborated (p := p)).output input offset)).bitwise_operation.bitwise_operation.result) = _
  rw [BitwiseChip.directOutput_eq, BitwiseChip.eval_columns]
  apply Vector.ext; intro i hi
  interval_cases i <;> simp only [offset, BitwiseU16Operation.resultWord,
    Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- Bitwise's completed exposed Memory list evaluates to the canonical conditional six-pack. -/
theorem bitwiseChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (aluViewMemoryInteractions (bitwiseViewOf env)).map TypedInteraction.raw := by
  memoryValuesPreamble BitwiseChip.Inputs, BitwiseChip.main, BitwiseChip.interactionsWith_memory_eq
  simp only [BitwiseChip.exposedMemoryInteractions, aluViewMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    bitwiseViewOf_state, bitwiseViewOf_adapter, bitwiseViewOf_isReal, bitwiseViewOf_rdWrite,
    Extracted.ALUTypeReader.toAdapterView, circuit_norm]

/-- Lift Bitwise's evaluated conditional six-pack to the typed decoded-row boundary. -/
theorem bitwiseChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = bitwiseChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      aluViewMemoryInteractions (decoded.toChipRow data).view := by
  descriptorSubst bitwiseChipDescriptor (p := p)
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    bitwiseViewOf_decodeRow, bitwiseChipDescriptor_table] using
    bitwiseChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Bitwise instantiates the canonical immediate-capable ALU Memory shape. -/
theorem bitwiseChip_aluTypeMemoryInteractionShape :
    ALUTypeMemoryInteractionShape (bitwiseChipDescriptor (p := p)) :=
  bitwiseChip_typedMemoryInteractions_eq

omit [Fact (2 ^ 25 < p)] in
/-- Bitwise's retained reader through the scalar ALU timestamp contract. -/
theorem BitwiseChip.aluTypeTimestampContract :
    CircuitALUTypeTimestampContract (p := p) (BitwiseChip.circuit (p := p))
      BitwiseChip.rowView := by
  let input : Var BitwiseChip.Inputs (ZMod p) := varFromOffset BitwiseChip.Inputs 0
  let offset := size BitwiseChip.Inputs
  let readerInput := BitwiseChip.aluTypeReaderInput input offset
  refine .intro (offset + 19) readerInput (BitwiseChip.aluTypeReader_mem input offset) ?_
  intro env _constraints
  constructor <;>
    simp only [input, offset, readerInput, BitwiseChip.aluTypeReaderInput, BitwiseChip.circuit,
      BitwiseChip.rowView, Extracted.ALUTypeReader.toAdapterView, circuit_norm]

theorem bitwiseChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = bitwiseChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  descriptorSubst bitwiseChipDescriptor (p := p)
  exact viewClockBounds_of_cpuStateContract (BitwiseChip.circuit (p := p)) BitwiseChip.rowView
    BitwiseChip.cpuStateTimeContract data physical guarantees real

theorem bitwiseChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = bitwiseChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ALUTypeTimestampBounds (decoded.toChipRow data).view := by
  descriptorSubst bitwiseChipDescriptor (p := p)
  exact aluTypeTimestampBounds_of_contract BitwiseChip.circuit BitwiseChip.rowView
    BitwiseChip.aluTypeTimestampContract data physical constraints guarantees real

/-- The committed decode supplies Bitwise's register/immediate selector bit. -/
theorem bitwiseChip_immBinary {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow) :
    (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1 := by
  simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2

/-- On Bitwise's immediate form, the committed operand is a canonical 64-bit word. -/
theorem bitwiseChip_immediate_isU64 {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_c :=
  decode.immediate_words_isU64.2 (by
    simpa only [programAccess, ProgramAccess.toRow] using immediate)

/-- Descriptor-level form of Bitwise's physical immediate-consistency binding. -/
theorem bitwiseChip_opCBinding_of_constraints (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = bitwiseChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    (decoded.toChipRow data).view.adapter.op_c_memory.prev_value =
      (decoded.toChipRow data).view.adapter.op_c := by
  descriptorSubst bitwiseChipDescriptor (p := p)
  exact BitwiseChip.rowViewOpCBinding_of_constraints
    (Environment.fromArray physical data) constraints immediate

end Bitwise

section Lt

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The immediate-capable Lt descriptor in the supported Core registry. -/
def ltChipDescriptor : SupportedChip p :=
  ⟨.lt, LtChip.kind, LtChip.circuit, rfl⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def ltViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  LtChip.physicalView env

theorem ltViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((ltChipDescriptor (p := p)).decodeRow data physical).view =
      ltViewOf (Environment.fromArray physical data) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem ltChipDescriptor_table :
    (ltChipDescriptor (p := p)).table =
      (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem ltViewOf_state (env : Environment (ZMod p)) :
    (ltViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) LtChip.Inputs 0)).state := by
  aluViewState LtChip.Inputs, LtChip.circuit, LtChip.inputOutputState,
    ltViewOf, LtChip.physicalView, LtChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem ltViewOf_adapter (env : Environment (ZMod p)) :
    (ltViewOf env).adapter =
      (Eval.eval env (varFromOffset (F := ZMod p) LtChip.Inputs 0)).adapter.toAdapterView := by
  aluViewAdapter LtChip.Inputs, LtChip.circuit, LtChip.inputOutputAdapter,
    ltViewOf, LtChip.physicalView, LtChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem ltViewOf_isReal (env : Environment (ZMod p)) :
    (ltViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) LtChip.Inputs 0)).is_real :=
  LtChip.physicalView_isReal env

omit [Fact (2 ^ 25 < p)] in
theorem ltViewOf_rdWrite (env : Environment (ZMod p)) :
    (ltViewOf env).rdWrite =
      Eval.eval env
        (#v[var { index := size LtChip.Inputs + 2 }, 0, 0, 0] :
          Word (Expression (ZMod p))) := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  have outputEq : Eval.eval env ((LtChip.circuit (p := p)).output input offset) =
      LtChip.physicalCols env := by
    simp only [input, offset, LtChip.physicalCols, Component.rowOutput, circuit_norm]
  simp only [ltViewOf, LtChip.physicalView, LtChip.rowView, LtChip.resultWord]
  rw [← outputEq]
  change LtChip.resultWord
    (Eval.eval env ((LtChip.elaborated (p := p)).output input offset)) = _
  rw [LtChip.directOutput_eq, LtChip.eval_columns]
  apply Vector.ext; intro i hi
  interval_cases i <;> simp only [offset, LtChip.resultWord, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- Lt's completed exposed Memory list evaluates to the canonical conditional six-pack. -/
theorem ltChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (aluViewMemoryInteractions (ltViewOf env)).map TypedInteraction.raw := by
  memoryValuesPreamble LtChip.Inputs, LtChip.main, LtChip.interactionsWith_memory_eq
  simp only [LtChip.exposedMemoryInteractions, aluViewMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    ltViewOf_state, ltViewOf_adapter, ltViewOf_isReal, ltViewOf_rdWrite,
    Extracted.ALUTypeReader.toAdapterView, circuit_norm]

/-- Lift Lt's evaluated conditional six-pack to the typed decoded-row boundary. -/
theorem ltChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = ltChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      aluViewMemoryInteractions (decoded.toChipRow data).view := by
  descriptorSubst ltChipDescriptor (p := p)
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    ltViewOf_decodeRow, ltChipDescriptor_table] using
    ltChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- Lt instantiates the canonical immediate-capable ALU Memory shape. -/
theorem ltChip_aluTypeMemoryInteractionShape :
    ALUTypeMemoryInteractionShape (ltChipDescriptor (p := p)) :=
  ltChip_typedMemoryInteractions_eq

omit [Fact (2 ^ 25 < p)] in
/-- Lt's retained reader through the scalar ALU timestamp contract. -/
theorem LtChip.aluTypeTimestampContract :
    CircuitALUTypeTimestampContract (p := p) (LtChip.circuit (p := p)) LtChip.rowView := by
  let input : Var LtChip.Inputs (ZMod p) := varFromOffset LtChip.Inputs 0
  let offset := size LtChip.Inputs
  let readerInput := LtChip.aluTypeReaderInput input offset
  refine .intro (offset + 12) readerInput (LtChip.aluTypeReader_mem input offset) ?_
  intro env _constraints
  constructor <;>
    simp only [input, offset, readerInput, LtChip.aluTypeReaderInput, LtChip.circuit,
      LtChip.rowView, Extracted.ALUTypeReader.toAdapterView, circuit_norm]

theorem ltChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = ltChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  descriptorSubst ltChipDescriptor (p := p)
  exact viewClockBounds_of_cpuStateContract (LtChip.circuit (p := p)) LtChip.rowView
    LtChip.cpuStateTimeContract data physical guarantees real

theorem ltChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = ltChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ALUTypeTimestampBounds (decoded.toChipRow data).view := by
  descriptorSubst ltChipDescriptor (p := p)
  exact aluTypeTimestampBounds_of_contract LtChip.circuit LtChip.rowView
    LtChip.aluTypeTimestampContract data physical constraints guarantees real

/-- The committed decode supplies Lt's register/immediate selector bit. -/
theorem ltChip_immBinary {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow) :
    (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1 := by
  simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2

/-- On Lt's immediate form, the committed operand is a canonical 64-bit word. -/
theorem ltChip_immediate_isU64 {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_c :=
  decode.immediate_words_isU64.2 (by
    simpa only [programAccess, ProgramAccess.toRow] using immediate)

/-- Descriptor-level form of Lt's physical immediate-consistency binding. -/
theorem ltChip_opCBinding_of_constraints (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = ltChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    (decoded.toChipRow data).view.adapter.op_c_memory.prev_value =
      (decoded.toChipRow data).view.adapter.op_c := by
  descriptorSubst ltChipDescriptor (p := p)
  exact LtChip.rowViewOpCBinding_of_constraints
    (Environment.fromArray physical data) constraints immediate

end Lt

section ShiftLeft

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The immediate-capable ShiftLeft descriptor in the supported Core registry. -/
def shiftLeftChipDescriptor : SupportedChip p :=
  ⟨.shiftLeft, ShiftLeftChip.kind, ShiftLeftChip.circuit, rfl⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def shiftLeftViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  ShiftLeftChip.physicalView env

theorem shiftLeftViewOf_decodeRow (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    ((shiftLeftChipDescriptor (p := p)).decodeRow data physical).view =
      shiftLeftViewOf (Environment.fromArray physical data) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem shiftLeftChipDescriptor_table :
    (shiftLeftChipDescriptor (p := p)).table =
      (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem shiftLeftViewOf_state (env : Environment (ZMod p)) :
    (shiftLeftViewOf env).state =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftLeftChip.Inputs 0)).state := by
  aluViewState ShiftLeftChip.Inputs, ShiftLeftChip.circuit, ShiftLeftChip.inputOutputState,
    shiftLeftViewOf, ShiftLeftChip.physicalView, ShiftLeftChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem shiftLeftViewOf_adapter (env : Environment (ZMod p)) :
    (shiftLeftViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftLeftChip.Inputs 0)).adapter.toAdapterView := by
  aluViewAdapter ShiftLeftChip.Inputs, ShiftLeftChip.circuit, ShiftLeftChip.inputOutputAdapter,
    shiftLeftViewOf, ShiftLeftChip.physicalView, ShiftLeftChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem shiftLeftViewOf_isReal (env : Environment (ZMod p)) :
    (shiftLeftViewOf env).is_real =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftLeftChip.Inputs 0)).is_real :=
  ShiftLeftChip.physicalView_isReal env

omit [Fact (2 ^ 25 < p)] in
theorem shiftLeftViewOf_rdWrite (env : Environment (ZMod p)) :
    (shiftLeftViewOf env).rdWrite =
      Eval.eval env
        (#v[var { index := size ShiftLeftChip.Inputs },
            var { index := size ShiftLeftChip.Inputs + 1 },
            var { index := size ShiftLeftChip.Inputs + 2 },
            var { index := size ShiftLeftChip.Inputs + 3 }] :
          Word (Expression (ZMod p))) := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  have outputEq : Eval.eval env ((ShiftLeftChip.circuit (p := p)).output input offset) =
      ShiftLeftChip.physicalCols env := by
    simp only [input, offset, ShiftLeftChip.physicalCols,
      Component.rowOutput, circuit_norm]
  simp only [shiftLeftViewOf, ShiftLeftChip.physicalView, ShiftLeftChip.rowView]
  rw [← outputEq]
  change
    (Eval.eval env ((ShiftLeftChip.elaborated (p := p)).output input offset)).a = _
  rw [ShiftLeftChip.directOutput_eq, ShiftLeftChip.eval_columns]
  apply Vector.ext; intro i hi
  interval_cases i <;> simp only [offset, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- On satisfying rows, ShiftLeft's witnessed flag-sum gate equals its public row selector. -/
theorem shiftLeftGate_eval_eq_isReal (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftLeftChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env) :
    Expression.eval env (ShiftLeftChip.exposedGate (p := p) (size ShiftLeftChip.Inputs)) =
      (shiftLeftViewOf env).is_real := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  have mainConstraints : ((ShiftLeftChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have link :=
    (ShiftLeftChip.controlFacts_of_mainConstraints input offset env mainConstraints).selectorLink
  calc
    _ = Expression.eval env (var { index := offset + 30 }) +
        Expression.eval env (var { index := offset + 31 }) := by
      simp only [ShiftLeftChip.exposedGate, offset, Expression.eval]
    _ = Expression.eval env input.is_real := link.symm
    _ = (Eval.eval env input).is_real := (ShiftLeftChip.eval_inputIsReal env input).symm
    _ = (shiftLeftViewOf env).is_real := (shiftLeftViewOf_isReal env).symm

omit [Fact (2 ^ 25 < p)] in
/-- ShiftLeft's completed Memory list is canonical after its selector-link constraint fires. -/
theorem shiftLeftChip_memoryInteractionValues_eq (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftLeftChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env) :
    (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (aluViewMemoryInteractions (shiftLeftViewOf env)).map TypedInteraction.raw := by
  memoryValuesPreamble ShiftLeftChip.Inputs, ShiftLeftChip.main,
    ShiftLeftChip.interactionsWith_main_memory_eq
  simp only [ShiftLeftChip.exposedMemoryInteractions, aluViewMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [CircuitType.eval_expr, eval_sub]
  rw [shiftLeftGate_eval_eq_isReal env constraints]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    shiftLeftViewOf_state, shiftLeftViewOf_adapter, shiftLeftViewOf_isReal,
    shiftLeftViewOf_rdWrite, Extracted.ALUTypeReader.toAdapterView, circuit_norm]
  simp only [← vec4_eval, Vector.getElem_mapRange, Expression.eval]

/-- Lift ShiftLeft's constraint-normalized six-pack to the typed decoded-row boundary. -/
theorem shiftLeftChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftLeftChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    decoded.interactionsWith data memoryChannel =
      aluViewMemoryInteractions (decoded.toChipRow data).view := by
  descriptorSubst shiftLeftChipDescriptor (p := p)
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    shiftLeftViewOf_decodeRow, shiftLeftChipDescriptor_table] using
    shiftLeftChip_memoryInteractionValues_eq (Environment.fromArray physical data) constraints

/-- ShiftLeft instantiates the constraint-normalized immediate-capable ALU Memory shape. -/
theorem shiftLeftChip_aluTypeMemoryInteractionShape :
    ConstrainedALUTypeMemoryInteractionShape (shiftLeftChipDescriptor (p := p)) :=
  shiftLeftChip_typedMemoryInteractions_eq

omit [Fact (2 ^ 25 < p)] in
/-- ShiftLeft's retained reader through the constraint-aware scalar timestamp contract.
The former 4M ceiling measured ~100x over; floor is at or below 40000. -/
theorem ShiftLeftChip.aluTypeTimestampContract :
    CircuitALUTypeTimestampContract (p := p) (ShiftLeftChip.circuit (p := p))
      ShiftLeftChip.rowView := by
  let input : Var ShiftLeftChip.Inputs (ZMod p) :=
    varFromOffset ShiftLeftChip.Inputs 0
  let offset := size ShiftLeftChip.Inputs
  let readerInput := ShiftLeftChip.aluReaderInput input offset
  refine .intro (offset + 33) readerInput
    (ShiftLeftChip.aluReader_mem_subcircuits input offset) ?_
  intro env constraints
  have inputEq : Eval.eval env input =
      (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset ShiftLeftChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((ShiftLeftChip.circuit (p := p)).output input offset) =
      (⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  have viewEq :
      ShiftLeftChip.rowView (Eval.eval env input)
          (Eval.eval env ((ShiftLeftChip.circuit (p := p)).output input offset)) =
        shiftLeftViewOf env := by
    rw [inputEq, outputEq]
    rfl
  rw [viewEq]
  constructor <;>
    simp only [input, offset, readerInput, ShiftLeftChip.aluReaderInput,
      shiftLeftViewOf_state, shiftLeftViewOf_adapter,
      Extracted.ALUTypeReader.toAdapterView, circuit_norm]
  simpa only [ShiftLeftChip.exposedGate, Expression.eval, circuit_norm] using
    shiftLeftGate_eval_eq_isReal env constraints

theorem shiftLeftChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftLeftChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  descriptorSubst shiftLeftChipDescriptor (p := p)
  exact viewClockBounds_of_cpuStateContract
    (ShiftLeftChip.circuit (p := p)) ShiftLeftChip.rowView
    ShiftLeftChip.cpuStateTimeContract data physical guarantees real

theorem shiftLeftChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftLeftChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ALUTypeTimestampBounds (decoded.toChipRow data).view := by
  descriptorSubst shiftLeftChipDescriptor (p := p)
  exact aluTypeTimestampBounds_of_contract ShiftLeftChip.circuit ShiftLeftChip.rowView
    ShiftLeftChip.aluTypeTimestampContract data physical constraints guarantees real

/-- The committed decode supplies ShiftLeft's register/immediate selector bit. -/
theorem shiftLeftChip_immBinary {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow) :
    (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1 := by
  simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2

/-- On ShiftLeft's immediate form, the committed operand is a canonical 64-bit word. -/
theorem shiftLeftChip_immediate_isU64 {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_c :=
  decode.immediate_words_isU64.2 (by
    simpa only [programAccess, ProgramAccess.toRow] using immediate)

/-- Descriptor-level form of ShiftLeft's physical immediate-consistency binding. -/
theorem shiftLeftChip_opCBinding_of_constraints (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftLeftChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    (decoded.toChipRow data).view.adapter.op_c_memory.prev_value =
      (decoded.toChipRow data).view.adapter.op_c := by
  descriptorSubst shiftLeftChipDescriptor (p := p)
  exact ShiftLeftChip.rowViewOpCBinding_of_constraints
    (Environment.fromArray physical data) constraints immediate

end ShiftLeft

section ShiftRight

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The immediate-capable ShiftRight descriptor in the supported Core registry. -/
def shiftRightChipDescriptor : SupportedChip p :=
  ⟨.shiftRight, ShiftRightChip.kind, ShiftRightChip.circuit, rfl⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def shiftRightViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  ShiftRightChip.physicalView env

theorem shiftRightViewOf_decodeRow (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    ((shiftRightChipDescriptor (p := p)).decodeRow data physical).view =
      shiftRightViewOf (Environment.fromArray physical data) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem shiftRightChipDescriptor_table :
    (shiftRightChipDescriptor (p := p)).table =
      (⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem shiftRightViewOf_state (env : Environment (ZMod p)) :
    (shiftRightViewOf env).state =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftRightChip.Inputs 0)).state := by
  aluViewState ShiftRightChip.Inputs, ShiftRightChip.circuit, ShiftRightChip.inputOutputState,
    shiftRightViewOf, ShiftRightChip.physicalView, ShiftRightChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem shiftRightViewOf_adapter (env : Environment (ZMod p)) :
    (shiftRightViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftRightChip.Inputs 0)).adapter.toAdapterView := by
  aluViewAdapter ShiftRightChip.Inputs, ShiftRightChip.circuit, ShiftRightChip.inputOutputAdapter,
    shiftRightViewOf, ShiftRightChip.physicalView, ShiftRightChip.rowView

omit [Fact (2 ^ 25 < p)] in
theorem shiftRightViewOf_isReal (env : Environment (ZMod p)) :
    (shiftRightViewOf env).is_real =
      (Eval.eval env
        (varFromOffset (F := ZMod p) ShiftRightChip.Inputs 0)).is_real :=
  ShiftRightChip.physicalView_isReal env

omit [Fact (2 ^ 25 < p)] in
theorem shiftRightViewOf_rdWrite (env : Environment (ZMod p)) :
    (shiftRightViewOf env).rdWrite =
      Eval.eval env
        (#v[var { index := size ShiftRightChip.Inputs },
            var { index := size ShiftRightChip.Inputs + 1 },
            var { index := size ShiftRightChip.Inputs + 2 },
            var { index := size ShiftRightChip.Inputs + 3 }] :
          Word (Expression (ZMod p))) := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  have outputEq : Eval.eval env ((ShiftRightChip.circuit (p := p)).output input offset) =
      ShiftRightChip.physicalCols env := by
    simp only [input, offset, ShiftRightChip.physicalCols,
      Component.rowOutput, circuit_norm]
  simp only [shiftRightViewOf, ShiftRightChip.physicalView, ShiftRightChip.rowView]
  rw [← outputEq]
  change
    (Eval.eval env ((ShiftRightChip.elaborated (p := p)).output input offset)).a = _
  rw [ShiftRightChip.directOutput_eq, ShiftRightChip.eval_columns]
  apply Vector.ext; intro i hi
  interval_cases i <;> simp only [offset, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- On satisfying rows, ShiftRight's witnessed write gate equals its public row selector. -/
theorem shiftRightWriteGate_eval_eq_isReal (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftRightChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env) :
    Expression.eval env
        (ShiftRightChip.exposedWriteGate (p := p) (size ShiftRightChip.Inputs)) =
      (shiftRightViewOf env).is_real := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  have mainConstraints : ((ShiftRightChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have link :=
    (ShiftRightChip.controlFacts_of_mainConstraints input offset env mainConstraints).selectorLink
  calc
    _ = Expression.eval env (var { index := offset + 32 }) +
          Expression.eval env (var { index := offset + 33 }) +
          Expression.eval env (var { index := offset + 34 }) +
          Expression.eval env (var { index := offset + 35 }) := by
      simp only [ShiftRightChip.exposedWriteGate, offset, Expression.eval]
    _ = Expression.eval env input.is_real := link.symm
    _ = (Eval.eval env input).is_real := (ShiftRightChip.eval_inputIsReal env input).symm
    _ = (shiftRightViewOf env).is_real := (shiftRightViewOf_isReal env).symm

omit [Fact (2 ^ 25 < p)] in
/-- ShiftRight's completed Memory list is canonical after its write-gate link fires. -/
theorem shiftRightChip_memoryInteractionValues_eq (env : Environment (ZMod p))
    (constraints :
      (⟨ShiftRightChip.circuit (p := p)⟩ :
        Component (ZMod p)).operations.ConstraintsHold env) :
    (⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (aluViewMemoryInteractions (shiftRightViewOf env)).map TypedInteraction.raw := by
  memoryValuesPreamble ShiftRightChip.Inputs, ShiftRightChip.main,
    ShiftRightChip.interactionsWith_main_memory_eq
  simp only [ShiftRightChip.exposedMemoryInteractions, aluViewMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage,
    CircuitType.eval_expr, eval_sub]
  rw [shiftRightWriteGate_eval_eq_isReal env constraints]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    shiftRightViewOf_state, shiftRightViewOf_adapter, shiftRightViewOf_isReal,
    shiftRightViewOf_rdWrite, Extracted.ALUTypeReader.toAdapterView, circuit_norm]
  simp only [← vec4_eval, Vector.getElem_mapRange, Expression.eval]

/-- Lift ShiftRight's constraint-normalized six-pack to the typed decoded-row boundary. -/
theorem shiftRightChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftRightChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    decoded.interactionsWith data memoryChannel =
      aluViewMemoryInteractions (decoded.toChipRow data).view := by
  descriptorSubst shiftRightChipDescriptor (p := p)
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    shiftRightViewOf_decodeRow, shiftRightChipDescriptor_table] using
    shiftRightChip_memoryInteractionValues_eq (Environment.fromArray physical data) constraints

/-- ShiftRight instantiates the constraint-normalized immediate-capable ALU Memory shape. -/
theorem shiftRightChip_aluTypeMemoryInteractionShape :
    ConstrainedALUTypeMemoryInteractionShape (shiftRightChipDescriptor (p := p)) :=
  shiftRightChip_typedMemoryInteractions_eq

omit [Fact (2 ^ 25 < p)] in
/-- ShiftRight's retained reader through the scalar timestamp contract. -/
theorem ShiftRightChip.aluTypeTimestampContract :
    CircuitALUTypeTimestampContract (p := p) (ShiftRightChip.circuit (p := p))
      ShiftRightChip.rowView := by
  let input : Var ShiftRightChip.Inputs (ZMod p) :=
    varFromOffset ShiftRightChip.Inputs 0
  let offset := size ShiftRightChip.Inputs
  let readerInput := ShiftRightChip.aluReaderInput input offset
  refine .intro (offset + 37) readerInput
    (ShiftRightChip.aluReader_mem_subcircuits input offset) ?_
  intro env _constraints
  constructor <;>
    simp only [input, offset, readerInput, ShiftRightChip.aluReaderInput,
      ShiftRightChip.circuit, ShiftRightChip.rowView,
      Extracted.ALUTypeReader.toAdapterView, circuit_norm]

theorem shiftRightChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftRightChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  descriptorSubst shiftRightChipDescriptor (p := p)
  exact viewClockBounds_of_cpuStateContract
    (ShiftRightChip.circuit (p := p)) ShiftRightChip.rowView
    ShiftRightChip.cpuStateTimeContract data physical guarantees real

theorem shiftRightChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftRightChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ALUTypeTimestampBounds (decoded.toChipRow data).view := by
  descriptorSubst shiftRightChipDescriptor (p := p)
  exact aluTypeTimestampBounds_of_contract ShiftRightChip.circuit ShiftRightChip.rowView
    ShiftRightChip.aluTypeTimestampContract data physical constraints guarantees real

/-- The committed decode supplies ShiftRight's register/immediate selector bit. -/
theorem shiftRightChip_immBinary {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow) :
    (decoded.toChipRow data).view.adapter.imm_c = 0 ∨
      (decoded.toChipRow data).view.adapter.imm_c = 1 := by
  simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2

/-- On ShiftRight's immediate form, the committed operand is a canonical 64-bit word. -/
theorem shiftRightChip_immediate_isU64 {program : GuestProgram}
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (decode : decodedInROM program (programAccess (decoded.toChipRow data).view).toRow)
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    Word.isU64 (decoded.toChipRow data).view.adapter.op_c :=
  decode.immediate_words_isU64.2 (by
    simpa only [programAccess, ProgramAccess.toRow] using immediate)

/-- Descriptor-level form of ShiftRight's physical immediate-consistency binding. -/
theorem shiftRightChip_opCBinding_of_constraints (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = shiftRightChipDescriptor (p := p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (immediate : (decoded.toChipRow data).view.adapter.imm_c = 1) :
    (decoded.toChipRow data).view.adapter.op_c_memory.prev_value =
      (decoded.toChipRow data).view.adapter.op_c := by
  descriptorSubst shiftRightChipDescriptor (p := p)
  exact ShiftRightChip.rowViewOpCBinding_of_constraints
    (Environment.fromArray physical data) constraints immediate

end ShiftRight

section AluX0

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- AluX0's descriptor in the supported Core registry. -/
def aluX0ChipDescriptor : SupportedChip p :=
  ⟨.aluX0, AluX0Chip.kind, AluX0Chip.circuit, rfl⟩

omit [Fact (2 ^ 25 < p)] in
noncomputable def aluX0ViewOf (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  AluX0Chip.rowView
    ((⟨AluX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨AluX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem aluX0ViewOf_decodeRow (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) :
    ((aluX0ChipDescriptor (p := p)).decodeRow data physical).view =
      aluX0ViewOf (Environment.fromArray physical data) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem aluX0ChipDescriptor_table :
    (aluX0ChipDescriptor (p := p)).table =
      (⟨AluX0Chip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
theorem aluX0ViewOf_state (env : Environment (ZMod p)) :
    (aluX0ViewOf env).state =
      (Eval.eval env
        (varFromOffset (F := ZMod p) AluX0Chip.Inputs 0)).state := by
  simp only [aluX0ViewOf, AluX0Chip.circuit, AluX0Chip.rowView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem aluX0ViewOf_adapter (env : Environment (ZMod p)) :
    (aluX0ViewOf env).adapter =
      (Eval.eval env
        (varFromOffset (F := ZMod p) AluX0Chip.Inputs 0)).adapter.toAdapterView := by
  simp only [aluX0ViewOf, AluX0Chip.circuit, AluX0Chip.rowView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
/-- AluX0's view opcode is the threaded input opcode.  Naming this cheap projection keeps
readiness proofs from asking unification to unfold the completed circuit merely to compare the
identical input/output opcode fields. -/
theorem aluX0ViewOf_opcode (env : Environment (ZMod p)) :
    (aluX0ViewOf env).opcode =
      (Eval.eval env
        (varFromOffset (F := ZMod p) AluX0Chip.Inputs 0)).opcode := by
  simp only [aluX0ViewOf, AluX0Chip.circuit, AluX0Chip.rowView, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
theorem aluX0ViewOf_isReal (env : Environment (ZMod p)) :
    (aluX0ViewOf env).is_real =
      (Eval.eval env
        (varFromOffset (F := ZMod p) AluX0Chip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset AluX0Chip.Inputs 0) =
      (⟨AluX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AluX0Chip.Inputs 0 env
  simpa only [aluX0ViewOf, AluX0Chip.rowView] using
    congrArg (fun input : AluX0Chip.Inputs (ZMod p) => input.is_real) inputEq.symm

omit [Fact (2 ^ 25 < p)] [Fact (2 ^ 17 < p)] in
private theorem immutableAlu_constraintsHold_append
    (env : Environment (ZMod p)) (left right : Operations (ZMod p)) :
    (left ++ right).ConstraintsHold env ↔
      left.ConstraintsHold env ∧ right.ConstraintsHold env := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.forall_mem_append]
  tauto

omit [Fact (2 ^ 25 < p)] [Fact (2 ^ 17 < p)] in
private theorem immutableAlu_equality_of_constraints
    (env : Environment (ZMod p)) (left right : Expression (ZMod p)) (offset : ℕ) :
    Operations.ConstraintsHold env
        [.subcircuit (@FormalAssertion.toSubcircuit (ZMod p) _ (ProvablePair field field)
          ProvablePair.instance (Gadgets.Equality.circuit field) offset (left, right))] →
      env left = env right := by
  intro constraints
  have difference :
      env (toElements (M := field) left)[0] -
        env (toElements (M := field) right)[0] = 0 := by
    simpa [Operations.ConstraintsHold, FormalAssertion.toSubcircuit,
      Gadgets.Equality.main, Gadgets.allZero, Circuit.forEach.operations_eq,
      FlatOperation.constraints, FlatOperation.lookups, eval_sub, circuit_norm] using
      constraints
  have leftEq : env (toElements (M := field) left)[0] = env left := rfl
  have rightEq : env (toElements (M := field) right)[0] = env right := rfl
  rw [leftEq, rightEq, sub_eq_zero] at difference
  exact difference

omit [Fact (2 ^ 25 < p)] in
/-- AluX0's top-level forcing equality pins `op_a_0` high on every active row. -/
theorem AluX0Chip.opA0_eq_one_of_constraints
    (input : Var AluX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((AluX0Chip.main input).operations offset))
    (real : (Eval.eval env input).is_real = 1) :
    (Eval.eval env input).adapter.op_a_0 = 1 := by
  let left := input.is_real * (input.adapter.op_a_0 - 1)
  let right : Expression (ZMod p) := 0
  simp only [AluX0Chip.main, Circuit.operations, Circuit.bind_def, assertion,
    assertZero, HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf,
    Operations.localLength, immutableAlu_constraintsHold_append] at constraints
  obtain ⟨_, _, _, _, equalityConstraints, _⟩ := constraints
  have difference := immutableAlu_equality_of_constraints env left right _ equalityConstraints
  have gate :
      Expression.eval env input.is_real *
        (Expression.eval env input.adapter.op_a_0 - 1) = 0 := by
    simpa only [left, right, Expression.eval, eval_mul, eval_sub] using difference
  have realEval :
      (Eval.eval env input).is_real = Expression.eval env input.is_real := by
    simp only [circuit_norm]
  have opA0Eval :
      (Eval.eval env input).adapter.op_a_0 =
        Expression.eval env input.adapter.op_a_0 := by
    rw [ProvableStruct.eval_eq_eval]
    exact Readers.ALUTypeReader.eval_opA0 env input.adapter
  rw [← realEval, ← opA0Eval] at gate
  rw [real, one_mul] at gate
  exact sub_eq_zero.mp gate

omit [Fact (2 ^ 25 < p)] in
/-- AluX0's completed exposed Memory list evaluates to the immutable conditional six-pack. -/
theorem aluX0Chip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨AluX0Chip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (immutableAluViewMemoryInteractions (aluX0ViewOf env)).map
        TypedInteraction.raw := by
  memoryValuesPreamble AluX0Chip.Inputs, AluX0Chip.main, AluX0Chip.interactionsWith_memory_eq
  simp only [AluX0Chip.exposedMemoryInteractions, immutableAluViewMemoryInteractions,
    List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw, Channel.eval_pulledIf, Channel.eval_pushedIf,
    eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, aluX0ViewOf_state,
    aluX0ViewOf_adapter, aluX0ViewOf_isReal,
    Extracted.ALUTypeReader.toAdapterView, circuit_norm]

/-- Lift AluX0's evaluated Memory list to the typed decoded-row boundary. -/
theorem aluX0Chip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = aluX0ChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      immutableAluViewMemoryInteractions (decoded.toChipRow data).view := by
  descriptorSubst aluX0ChipDescriptor (p := p)
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
    aluX0ViewOf_decodeRow, aluX0ChipDescriptor_table] using
    aluX0Chip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-- AluX0 instantiates the immutable immediate-capable ALU Memory shape. -/
theorem aluX0Chip_immutableALUTypeMemoryInteractionShape :
    ImmutableALUTypeMemoryInteractionShape (aluX0ChipDescriptor (p := p)) where
  interactions := aluX0Chip_typedMemoryInteractions_eq
  imm_b_eq_zero := by
    intro decoded data hchip
    descriptorSubst aluX0ChipDescriptor (p := p)
    rfl

private def AluX0Chip.immutableAluReaderInput
    (input : Var AluX0Chip.Inputs (ZMod p)) :
    Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    input.opcode⟩

omit [Fact (2 ^ 25 < p)] in
/-- AluX0's retained immutable reader through the scalar timestamp contract. -/
theorem AluX0Chip.immutableAluTypeTimestampContract :
    CircuitImmutableALUTypeTimestampContract (p := p)
      (AluX0Chip.circuit (p := p)) AluX0Chip.rowView := by
  let input : Var AluX0Chip.Inputs (ZMod p) :=
    varFromOffset AluX0Chip.Inputs 0
  let offset := size AluX0Chip.Inputs
  let readerInput := AluX0Chip.immutableAluReaderInput input
  refine .intro offset readerInput ?_ ?_
  · simp only [input, offset, readerInput, AluX0Chip.immutableAluReaderInput,
      AluX0Chip.circuit, AluX0Chip.main, Readers.CPUState.circuit,
      Readers.ALUTypeReaderImmutable.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, readerInput, AluX0Chip.immutableAluReaderInput,
        AluX0Chip.circuit, AluX0Chip.rowView,
        Extracted.ALUTypeReader.toAdapterView, circuit_norm]

theorem aluX0Chip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = aluX0ChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  descriptorSubst aluX0ChipDescriptor (p := p)
  exact viewClockBounds_of_cpuStateContract (AluX0Chip.circuit (p := p))
    AluX0Chip.rowView AluX0Chip.cpuStateTimeContract data physical guarantees real

theorem aluX0Chip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = aluX0ChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ALUTypeTimestampBounds (decoded.toChipRow data).view := by
  descriptorSubst aluX0ChipDescriptor (p := p)
  exact immutableAluTypeTimestampBounds_of_contract AluX0Chip.circuit
    AluX0Chip.rowView AluX0Chip.immutableAluTypeTimestampContract
      data physical guarantees real

end AluX0

end SP1Clean.Soundness
