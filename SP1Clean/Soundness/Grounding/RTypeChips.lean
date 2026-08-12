import SP1Clean.Soundness.GroundingAdapter
import SP1Clean.Proofs.Chips.SubwChip.Contracts
import SP1Clean.Proofs.Chips.DivRemChip.Contracts

/-! # Canonical R-type grounding instances

Chip-specific structural facts for register-register chips sharing the six-message `RTypeReader`
Memory shape.  The family constructor (`RTypeChipGroundingData.toContracts`) lives in
`Soundness/ChipContracts.lean`, and the Add anchor material in `Soundness/GroundingAdapter.lean`;
this module extends the family without making those central modules normalize
every concrete chip circuit.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels (memoryChannel byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Substitute a decoded row's descriptor and discharge one Byte-guarantee contract at the exposed
row.  This removes only the constructor/substitution preamble that every per-chip lemma below
repeats; each expansion still proves that concrete chip's own obligation.  The caller's binders are
referenced by name (`decoded`, `data`, `hchip`, `guarantees`, `real`), so the macro is usable only
at a lemma with exactly that signature — a mismatch is a loud `unknown identifier`. -/
local macro "byteGuaranteeContract " desc:term ", " closer:term : tactic => do
  let decoded := Lean.mkIdent `decoded
  let data := Lean.mkIdent `data
  let hchip := Lean.mkIdent `hchip
  let guarantees := Lean.mkIdent `guarantees
  let real := Lean.mkIdent `real
  `(tactic| (
    obtain ⟨chip, physical⟩ := $decoded
    have descriptorEq : chip = $desc := $hchip
    subst descriptorEq
    exact $closer $data physical $guarantees $real))

/-- Lift a chip's evaluated Memory interaction list to the typed decoded-row boundary. -/
local macro "typedMemoryLift " desc:term ", " decodeRow:term ", " table:term ", "
    valuesEq:term : tactic => do
  let decoded := Lean.mkIdent `decoded
  let data := Lean.mkIdent `data
  let hchip := Lean.mkIdent `hchip
  `(tactic| (
    obtain ⟨chip, physical⟩ := $decoded
    have descriptorEq : chip = $desc := $hchip
    subst descriptorEq
    apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
    rw [DecodedInstructionRow.interactionsWith_raw]
    simpa only [DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow,
      $decodeRow:term, $table:term] using $valuesEq (Environment.fromArray physical $data)))

section Subw

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- The SUBW instruction descriptor in the supported Core registry. -/
def subwChipDescriptor : SupportedChip p :=
  ⟨SubwChip.kind, SubwChip.circuit, rfl, [.SUBW], .nonX0⟩

omit [Fact (2 ^ 25 < p)] in
/-- The SUBW semantic row view denoted by a physical circuit environment. -/
noncomputable def subwViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  SubwChip.rowView ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

theorem subwViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((subwChipDescriptor (p := p)).decodeRow data physical).view =
      subwViewOf (Environment.fromArray physical data) := rfl

theorem subwChipDescriptor_table :
    (subwChipDescriptor (p := p)).table =
      (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
/-- SUBW's explicit sign-extended output row, kept as a symbolic rewrite boundary. -/
theorem subwChip_circuit_output_eq (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ) :
    (SubwChip.circuit (p := p)).output input offset =
      (⟨input.is_real, input.state, input.adapter,
        ⟨Vector.mapRange 2 fun i => var { index := offset + i },
          ⟨var { index := offset + 2 }⟩⟩⟩ : Var SubwChip.Columns (ZMod p)) := rfl

omit [Fact (2 ^ 25 < p)] in
/-- SUBW's public exposed Memory list evaluates to the canonical R-type six-pack. -/
theorem subwChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (rtypeMemoryInteractions (subwViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((SubwChip.main (varFromOffset SubwChip.Inputs 0)).operations
        (size SubwChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [SubwChip.interactionsWith_memory_eq]
  have inputEq : Eval.eval env (varFromOffset SubwChip.Inputs 0) =
      (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset SubwChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((SubwChip.circuit (p := p)).output (varFromOffset SubwChip.Inputs 0)
        (size SubwChip.Inputs)) =
      (⟨SubwChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, circuit_norm]
  simp only [SubwChip.exposedMemoryInteractions, rtypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [subwViewOf, ← inputEq, ← outputEq, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, SubwChip.rowView, Extracted.RTypeReader.toAdapterView]
  simp only [circuit_norm, subwChip_circuit_output_eq]

/-- Lift SUBW's evaluated six-pack to the typed decoded-row boundary. -/
theorem subwChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = subwChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      rtypeMemoryInteractions (decoded.toChipRow data).view := by
  typedMemoryLift subwChipDescriptor (p := p), subwViewOf_decodeRow, subwChipDescriptor_table,
    subwChip_memoryInteractionValues_eq

/-- SUBW instantiates the common R-type interaction shape. -/
theorem subwChip_rtypeMemoryInteractionShape :
    RTypeMemoryInteractionShape (subwChipDescriptor (p := p)) :=
  subwChip_typedMemoryInteractions_eq

/-- The exact R-type reader input retained after SUBW's three local witness cells. -/
def subwChipRTypeInput (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  let value : Vector (Expression (ZMod p)) 2 :=
    Vector.mapRange 2 fun i => var { index := offset + i }
  let msb : Expression (ZMod p) := var { index := offset + 2 }
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
    value[0], value[1], msb * 65535, msb * 65535⟩

omit [Fact (2 ^ 25 < p)] in
/-- SUBW's retained reader through the family timestamp contract. -/
theorem SubwChip.rtypeTimestampContract :
    CircuitRTypeTimestampContract (p := p) (SubwChip.circuit (p := p)) SubwChip.rowView := by
  let input : Var SubwChip.Inputs (ZMod p) := varFromOffset SubwChip.Inputs 0
  let offset := size SubwChip.Inputs
  let readerInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    subwChipRTypeInput input offset
  refine ⟨offset + 3, readerInput, ?_, ?_⟩
  · simp only [input, offset, readerInput, subwChipRTypeInput, SubwChip.circuit,
      SubwChip.main, Readers.RTypeReader.circuit, circuit_norm]
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, subwChipRTypeInput, SubwChip.circuit,
        SubwChip.rowView, Extracted.RTypeReader.toAdapterView, circuit_norm]

/-- Finished Byte guarantees bound SUBW's view clock limbs. -/
theorem subwChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = subwChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  byteGuaranteeContract subwChipDescriptor (p := p),
    viewClockBounds_of_cpuStateContract (SubwChip.circuit (p := p)) SubwChip.rowView
      SubwChip.cpuStateTimeContract

/-- Finished Byte guarantees supply SUBW's three register timestamp decompositions. -/
theorem subwChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = subwChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RTypeTimestampBounds (decoded.toChipRow data).view := by
  byteGuaranteeContract subwChipDescriptor (p := p),
    rtypeTimestampBounds_of_contract SubwChip.circuit SubwChip.rowView
      SubwChip.rtypeTimestampContract

end Subw

section Mul

variable [Fact (2 ^ 25 < p)]

local instance mulFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The five-opcode multiplication descriptor in the supported Core registry. -/
def mulChipDescriptor : SupportedChip p :=
  ⟨MulChip.kind, MulChip.circuit, rfl, [.MUL, .MULH, .MULHU, .MULHSU, .MULW], .nonX0⟩

noncomputable def mulViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  MulChip.rowView ((⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

omit [Fact (2 ^ 17 < p)] in
/-- MUL's semantic selector is the completed component's input selector.  Naming this projection
prevents readiness consumers from normalizing the multiplication output just to recover `is_real`. -/
theorem mulViewOf_isReal (env : Environment (ZMod p)) :
    (mulViewOf env).is_real =
      ((⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real := by
  simp only [mulViewOf, MulChip.rowView]

theorem mulViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((mulChipDescriptor (p := p)).decodeRow data physical).view =
      mulViewOf (Environment.fromArray physical data) := rfl

theorem mulChipDescriptor_table :
    (mulChipDescriptor (p := p)).table =
      (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 17 < p)] in
/-- MUL's explicit output row over its 54 local cells. -/
theorem mulChip_circuit_output_eq (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) :
    (MulChip.circuit (p := p)).output input offset =
      (⟨input.state, input.adapter,
        Vector.mapRange 4 fun i => var { index := offset + 50 + i },
        varFromOffset Extracted.MulOperation (offset + 5),
        var { index := offset }, var { index := offset + 1 },
        var { index := offset + 2 }, var { index := offset + 3 },
        var { index := offset + 4 }⟩ : Var MulChip.Columns (ZMod p)) := rfl

omit [Fact (2 ^ 17 < p)] in
/-- MUL's exposed Memory list evaluates to the canonical R-type six-pack. -/
theorem mulChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (rtypeMemoryInteractions (mulViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((MulChip.main (varFromOffset MulChip.Inputs 0)).operations
        (size MulChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [MulChip.interactionsWith_memory_eq]
  have inputEq : Eval.eval env (varFromOffset MulChip.Inputs 0) =
      (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset MulChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((MulChip.circuit (p := p)).output (varFromOffset MulChip.Inputs 0)
        (size MulChip.Inputs)) =
      (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, circuit_norm]
  simp only [MulChip.exposedMemoryInteractions, rtypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [mulViewOf, ← inputEq, ← outputEq, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, MulChip.rowView, Extracted.RTypeReader.toAdapterView]
  simp only [circuit_norm, mulChip_circuit_output_eq]

/-- Lift MUL's evaluated six-pack to the typed decoded-row boundary. -/
theorem mulChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = mulChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      rtypeMemoryInteractions (decoded.toChipRow data).view := by
  typedMemoryLift mulChipDescriptor (p := p), mulViewOf_decodeRow, mulChipDescriptor_table,
    mulChip_memoryInteractionValues_eq

theorem mulChip_rtypeMemoryInteractionShape :
    RTypeMemoryInteractionShape (mulChipDescriptor (p := p)) :=
  mulChip_typedMemoryInteractions_eq

theorem MulChip.rtypeTimestampContract :
    CircuitRTypeTimestampContract (p := p) (MulChip.circuit (p := p)) MulChip.rowView := by
  let input : Var MulChip.Inputs (ZMod p) := varFromOffset MulChip.Inputs 0
  let offset := size MulChip.Inputs
  let readerInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    MulChip.rTypeReaderInput input offset
  refine ⟨offset + 54, readerInput, ?_, ?_⟩
  · exact MulChip.rTypeReader_mem input offset
  · intro env
    constructor <;>
      simp only [input, offset, readerInput, MulChip.rTypeReaderInput,
        MulChip.circuit, MulChip.rowView,
        Extracted.RTypeReader.toAdapterView, circuit_norm]

theorem mulChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = mulChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  byteGuaranteeContract mulChipDescriptor (p := p),
    viewClockBounds_of_cpuStateContract (MulChip.circuit (p := p)) MulChip.rowView
      MulChip.cpuStateTimeContract

theorem mulChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = mulChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RTypeTimestampBounds (decoded.toChipRow data).view := by
  byteGuaranteeContract mulChipDescriptor (p := p),
    rtypeTimestampBounds_of_contract MulChip.circuit MulChip.rowView
      MulChip.rtypeTimestampContract

end Mul

section DivRem

variable [Fact (2 ^ 25 < p)]

local instance divRemFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The eight-opcode divide/remainder descriptor in the supported Core registry. -/
def divRemChipDescriptor : SupportedChip p :=
  ⟨DivRemChip.kind, DivRemChip.circuit, rfl,
    [.DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .nonX0⟩

noncomputable def divRemViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  DivRemChip.rowView
    ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

omit [Fact (2 ^ 17 < p)] in
/-- DivRem's semantic selector is the completed component's input selector. -/
theorem divRemViewOf_isReal (env : Environment (ZMod p)) :
    (divRemViewOf env).is_real =
      ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real := by
  simp only [divRemViewOf, DivRemChip.rowView]

theorem divRemViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((divRemChipDescriptor (p := p)).decodeRow data physical).view =
      divRemViewOf (Environment.fromArray physical data) := rfl

theorem divRemChipDescriptor_table :
    (divRemChipDescriptor (p := p)).table =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

omit [Fact (2 ^ 17 < p)] in
/-- Scalar state projection of the completed DivRem view.  This theorem, rather than a whole-row
equality, is the stable rewrite surface for bus proofs. -/
theorem divRemViewOf_state (env : Environment (ZMod p)) :
    (divRemViewOf env).state =
      (Eval.eval env (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)).state := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  have outputEq : Eval.eval env ((DivRemChip.circuit (p := p)).output input offset) =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  simp only [divRemViewOf, DivRemChip.rowView]
  rw [← outputEq]
  exact (DivRemChip.eval_output_state input offset env).symm

omit [Fact (2 ^ 17 < p)] in
/-- Scalar adapter projection of the completed DivRem view. -/
theorem divRemViewOf_adapter (env : Environment (ZMod p)) :
    (divRemViewOf env).adapter =
      (Eval.eval env (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)).adapter.toAdapterView := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  have outputEq : Eval.eval env ((DivRemChip.circuit (p := p)).output input offset) =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  simp only [divRemViewOf, DivRemChip.rowView]
  rw [← outputEq]
  exact congrArg Extracted.RTypeReader.toAdapterView
    (DivRemChip.eval_output_adapter input offset env).symm

omit [Fact (2 ^ 17 < p)] in
/-- Scalar selector projection in the same symbolic evaluator spelling used by the exposed list. -/
theorem divRemViewOf_isReal_eval (env : Environment (ZMod p)) :
    (divRemViewOf env).is_real =
      (Eval.eval env (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)).is_real := by
  have inputEq : Eval.eval env (varFromOffset DivRemChip.Inputs 0) =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset DivRemChip.Inputs 0 env
  rw [divRemViewOf_isReal, inputEq]

omit [Fact (2 ^ 17 < p)] in
/-- Scalar destination-word projection of the completed DivRem view. -/
theorem divRemViewOf_rdWrite (env : Environment (ZMod p)) :
    (divRemViewOf env).rdWrite =
      Eval.eval env
        (DivRemChip.populatedRowAt (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)
          (size DivRemChip.Inputs)).a := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  have outputEq : Eval.eval env ((DivRemChip.circuit (p := p)).output input offset) =
      (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [input, offset, Component.rowOutput, circuit_norm]
  simp only [divRemViewOf, DivRemChip.rowView]
  rw [← outputEq]
  exact DivRemChip.eval_output_a input offset env

omit [Fact (2 ^ 17 < p)] in
/-- DivRem's exposed Memory list evaluates to the canonical R-type six-pack. -/
theorem divRemChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      (rtypeMemoryInteractions (divRemViewOf env)).map TypedInteraction.raw := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((DivRemChip.main (varFromOffset DivRemChip.Inputs 0)).operations
        (size DivRemChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [DivRemChip.interactionsWith_memory_eq]
  simp only [DivRemChip.exposedMemoryInteractions, rtypeMemoryInteractions, List.map_cons,
    List.map_nil, TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [rtypePriorMessage, rtypeReadBackMessage, rtypeWriteMessage,
    divRemViewOf_state, divRemViewOf_adapter, divRemViewOf_isReal_eval,
    divRemViewOf_rdWrite, Extracted.RTypeReader.toAdapterView, circuit_norm]

/-- Lift DivRem's evaluated six-pack to the typed decoded-row boundary. -/
theorem divRemChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = divRemChipDescriptor (p := p)) :
    decoded.interactionsWith data memoryChannel =
      rtypeMemoryInteractions (decoded.toChipRow data).view := by
  typedMemoryLift divRemChipDescriptor (p := p), divRemViewOf_decodeRow, divRemChipDescriptor_table,
    divRemChip_memoryInteractionValues_eq

theorem divRemChip_rtypeMemoryInteractionShape :
    RTypeMemoryInteractionShape (divRemChipDescriptor (p := p)) :=
  divRemChip_typedMemoryInteractions_eq

/-- The DivRem timestamp contract's per-slot adapter projection.  The `simpa` set is fixed; only
the projected `RTypeReader` field varies, so naming the shape keeps the twelve fields readable. -/
local macro "divRemAdapterField " proj:term : tactic => do
  let input := Lean.mkIdent `input
  let offset := Lean.mkIdent `offset
  let readerInput := Lean.mkIdent `readerInput
  let adapterEq := Lean.mkIdent `adapterEq
  `(tactic| simpa only [$input:ident, $offset:ident, $readerInput:ident,
      DivRemChip.rTypeReaderInput, DivRemChip.eval_inputs,
      Extracted.RTypeReader.toAdapterView, circuit_norm] using congrArg $proj $adapterEq)

/-- As `divRemAdapterField`, for the three `clk_low + δ` target slots read off the state block. -/
local macro "divRemTargetField " delta:term : tactic => do
  let input := Lean.mkIdent `input
  let offset := Lean.mkIdent `offset
  let readerInput := Lean.mkIdent `readerInput
  let stateEq := Lean.mkIdent `stateEq
  `(tactic| simpa only [$input:ident, $offset:ident, $readerInput:ident,
      DivRemChip.rTypeReaderInput, DivRemChip.eval_inputs, circuit_norm] using
      congrArg (fun state : Extracted.CPUState (ZMod p) =>
        state.clk_0_16 + state.clk_16_24 * 65536 + $delta) $stateEq)

theorem DivRemChip.rtypeTimestampContract :
    CircuitRTypeTimestampContract (p := p) (DivRemChip.circuit (p := p))
      DivRemChip.rowView := by
  let input : Var DivRemChip.Inputs (ZMod p) := varFromOffset DivRemChip.Inputs 0
  let offset := size DivRemChip.Inputs
  let readerInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    DivRemChip.rTypeReaderInput input offset
  refine .intro (offset + 217) readerInput ?_ ?_
  · simpa only [DivRemChip.circuit_main_eq] using
      DivRemChip.rTypeReader_mem input offset
  · intro env
    have adapterEq := DivRemChip.eval_output_adapter input offset env
    have stateEq := DivRemChip.eval_output_state input offset env
    simp only [DivRemChip.rowView]
    refine {
      real_eq := by
        simp only [input, offset, readerInput, DivRemChip.rTypeReaderInput, circuit_norm]
      aPrev_eq := by divRemAdapterField (·.op_a_memory.access_timestamp.prev_low)
      aDiff_eq := by divRemAdapterField (·.op_a_memory.access_timestamp.diff_low_limb)
      bPrev_eq := by divRemAdapterField (·.op_b_memory.access_timestamp.prev_low)
      bDiff_eq := by divRemAdapterField (·.op_b_memory.access_timestamp.diff_low_limb)
      cPrev_eq := by divRemAdapterField (·.op_c_memory.access_timestamp.prev_low)
      cDiff_eq := by divRemAdapterField (·.op_c_memory.access_timestamp.diff_low_limb)
      targetA_eq := by divRemTargetField 4
      targetB_eq := by divRemTargetField 3
      targetC_eq := by divRemTargetField 2 }

theorem divRemChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = divRemChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  byteGuaranteeContract divRemChipDescriptor (p := p),
    viewClockBounds_of_cpuStateContract (DivRemChip.circuit (p := p)) DivRemChip.rowView
      DivRemChip.cpuStateTimeContract

theorem divRemChip_activeTimestampBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = divRemChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    RTypeTimestampBounds (decoded.toChipRow data).view := by
  byteGuaranteeContract divRemChipDescriptor (p := p),
    rtypeTimestampBounds_of_contract DivRemChip.circuit DivRemChip.rowView
      DivRemChip.rtypeTimestampContract

end DivRem

end SP1Clean.Soundness
