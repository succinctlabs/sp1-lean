import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Chips.ShiftLeftChip.Core
import SP1Clean.Proofs.Chips.ShiftLeftChip.Populate
import SP1Clean.Proofs.Operations.ShiftLeftOperation.Core
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `ShiftLeft` chip row as a `GeneralFormalCircuit`

`SLL`/`SLLW`: SP1's shift logic (the six shift-amount bits `c_bits`, the `v_01/v_012/v_0123` power
encodings, the `shift_u16` byte-shift one-hot selector, the `lower_limb`/`higher_limb` bit-split, the
`limb_result` reassembly, and the SLLW MSB sign-extension) is inlined into
the generated ShiftLeft oracle's `asserts`/`interactions` (`Extracted/ChipOracle/ShiftLeft.lean`) — no separate operation-level extraction.

`AssertSpec` / `InteractSpec` capture the structural meaning of SP1's two extracted constraint lists;
the semantic, flag-gated `Spec` (RV64 `sll`/`sllw` identity) is in `Specs/Chip.lean`.
`Faithful/ShiftLeftChip.lean` anchors both structural specs to SP1's extracted lists.

`main` composes `CPUState`/`ALUTypeReader`/`U16MSBOperation` sub-circuits, witnesses the shift column
block honestly (the `Populate` closures, flags via the `"shift_left_flags"` `ProverHint`), and gates
`is_real`. -/

namespace SP1Clean.ShiftLeftChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The two physical ALU reader operands are canonical 64-bit words. Lives here (not in `Formal`) so
the per-op `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- **Assertion half** — the literal meaning of SP1's `Columns.asserts` own assertZero list.
The three shallow selector constraints stay in the parent chip so Clean's channel-law proof can see
the combined gate; `CoreSpec` is the remaining assertion tail in upstream order. -/
def AssertSpec (cols : Columns (ZMod p)) : Prop :=
  let sll := cols.is_sll
  let sllw := cols.is_sllw
  let gate := sll + sllw
  gate * (gate - 1) = 0 ∧ sll * (sll - 1) = 0 ∧ sllw * (sllw - 1) = 0 ∧ CoreSpec cols

/-- **Interaction half** — the literal meaning of SP1's `Columns.interactions` *own* byte-range
sends (gated by `gate = is_sll + is_sllw`): the shift-amount high bits `< 2^10`, and, per limb, the
`lower_limb` `< 2^(16 - bitShift)` and `higher_limb` `< 2^bitShift` ranges (`bitShift` = low four
shift-amount bits). Each send's meaning is `gate ≠ 0 → value.val < 2 ^ width.val` (`Range.constrain`). -/
def InteractSpec (cols : Columns (ZMod p)) : Prop :=
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let bitShift : ZMod p := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt : ZMod p := bitShift + b4 * 16 + b5 * 32
  let e32 : ZMod p := (cols.adapter.op_c_memory.prev_value[0] - shamt) * (64 : ZMod p)⁻¹
  let gate : ZMod p := cols.is_sll + cols.is_sllw
  (gate ≠ 0 → e32.val < 2 ^ (10 : ZMod p).val) ∧
  (gate ≠ 0 → cols.lower_limb[0].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[0].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.lower_limb[1].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[1].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.lower_limb[2].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[2].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.lower_limb[3].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.higher_limb[3].val < 2 ^ bitShift.val)

/-! ### Folded witness prefix -/

private structure WitnessVars (F : Type) where
  a : Word (Expression F)
  c_bits : Vector (Expression F) 6
  v : Vector (Expression F) 3
  shift_u16 : Word (Expression F)
  lower_limb : Word (Expression F)
  higher_limb : Word (Expression F)
  limb_result : Word (Expression F)
  sllw_msb : Vector (Expression F) 1
  flags : Vector (Expression F) 3

@[circuit_norm] private def witnessPrefix (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (WitnessVars (ZMod p)) := fun offset =>
  let a := varFromOffset (Vector · 4) offset
  let c_bits := varFromOffset (Vector · 6) (offset + 4)
  let v := varFromOffset (Vector · 3) (offset + 4 + 6)
  let shift_u16 := varFromOffset (Vector · 4) (offset + 4 + 6 + 3)
  let lower_limb := varFromOffset (Vector · 4) (offset + 4 + 6 + 3 + 4)
  let higher_limb := varFromOffset (Vector · 4) (offset + 4 + 6 + 3 + 4 + 4)
  let limb_result := varFromOffset (Vector · 4) (offset + 4 + 6 + 3 + 4 + 4 + 4)
  let sllw_msb := varFromOffset (Vector · 1) (offset + 4 + 6 + 3 + 4 + 4 + 4 + 4)
  let flags := varFromOffset (Vector · 3) (offset + 4 + 6 + 3 + 4 + 4 + 4 + 4 + 1)
  (⟨a, c_bits, v, shift_u16, lower_limb, higher_limb, limb_result, sllw_msb, flags⟩,
    [ .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        populateA
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 6 (.native fun env : ProverEnvironment (ZMod p) =>
        cBits (env input.adapter.op_c_memory.prev_value[0])),
      .witness 3 (.native fun env : ProverEnvironment (ZMod p) =>
        vPowers (env input.adapter.op_c_memory.prev_value[0])),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        shiftU16 (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        lowerLimb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0])),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        higherLimb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0])),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        limbResult
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0])),
      .witness 1 (.native fun env : ProverEnvironment (ZMod p) =>
        #v[sllwMsb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)]),
      .witness 3 (.native fun env : ProverEnvironment (ZMod p) =>
        #v[(hintFlags env.hint)[0], (hintFlags env.hint)[1],
           (hintFlags env.hint)[1] * env input.adapter.imm_c]) ])

omit [Fact (2 ^ 17 < p)] in
private theorem witnessListSubcircuitsConsistent
    (offset : ℕ) (c0 : WitgenIR (ZMod p) 4) (c1 : WitgenIR (ZMod p) 6)
    (c2 : WitgenIR (ZMod p) 3) (c3 c4 c5 c6 : WitgenIR (ZMod p) 4)
    (c7 : WitgenIR (ZMod p) 1) (c8 : WitgenIR (ZMod p) 3) :
    Operations.SubcircuitsConsistent offset
      [.witness 4 c0, .witness 6 c1, .witness 3 c2, .witness 4 c3,
       .witness 4 c4, .witness 4 c5, .witness 4 c6, .witness 1 c7,
       .witness 3 c8] := by
  simp only [Operations.SubcircuitsConsistent, Operations.forAll, true_and]

omit [Fact (2 ^ 17 < p)] in
private theorem witnessListChannelsLawful
    (c0 : WitgenIR (ZMod p) 4) (c1 : WitgenIR (ZMod p) 6)
    (c2 : WitgenIR (ZMod p) 3) (c3 c4 c5 c6 : WitgenIR (ZMod p) 4)
    (c7 : WitgenIR (ZMod p) 1) (c8 : WitgenIR (ZMod p) 3) :
    Operations.ChannelsLawful
      [.witness 4 c0, .witness 6 c1, .witness 3 c2, .witness 4 c3,
       .witness 4 c4, .witness 4 c5, .witness 4 c6, .witness 1 c7,
       .witness 3 c8] [] := by
  simp only [Operations.ChannelsLawful,
    Operations.subcircuitChannelsWithGuarantees_witness,
    Operations.subcircuitChannelsWithGuarantees_nil, List.nil_subset, true_and,
    Operations.InChannelsOrGuarantees, Operations.forAllNoOffset,
    Operations.SubcircuitChannelsLawful, Operations.subcircuits_witness,
    Operations.subcircuits_nil, List.not_mem_nil, false_implies]
  exact ⟨fun _ => trivial, fun _ => trivial⟩

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefixSubcircuitsConsistent
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).operations offset).SubcircuitsConsistent offset := by
  unfold witnessPrefix Circuit.operations
  exact witnessListSubcircuitsConsistent offset _ _ _ _ _ _ _ _ _

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefixChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).operations offset).ChannelsLawful [] := by
  unfold witnessPrefix Circuit.operations
  exact witnessListChannelsLawful _ _ _ _ _ _ _ _ _

private instance witnessPrefixExplicit (input : Var Inputs (ZMod p)) :
    ExplicitCircuit (witnessPrefix input) where
  output offset := (witnessPrefix input offset).1
  localLength _ := 33
  operations offset := (witnessPrefix input offset).2
  output_eq _ := rfl
  localLength_eq _ := by rfl
  operations_eq _ := rfl
  subcircuitsConsistent := witnessPrefixSubcircuitsConsistent input
  channelsWithGuarantees _ := []
  channelsLawful := witnessPrefixChannelsLawful input

/-- The ALU-reader input expressed over the opaque witness-prefix result. -/
@[circuit_norm] private def postWitnessReaderInput (input : Var Inputs (ZMod p))
    (witnesses : WitnessVars (ZMod p)) : Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  let gate := witnesses.flags[0] + witnesses.flags[1]
  ⟨input.adapter, gate, gate, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    witnesses.flags[0] * (6 : Expression (ZMod p)) +
      witnesses.flags[1] * (21 : Expression (ZMod p)),
    witnesses.a[0], witnesses.a[1], witnesses.a[2], witnesses.a[3]⟩

/-- The post-witness circuit body. Naming this pure composition keeps the large assertion tail folded
while structural consumers select the early reader boundary. -/
@[circuit_norm] private def postWitness (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) :
    Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let a := witnesses.a
  let c_bits := witnesses.c_bits
  let v := witnesses.v
  let shift_u16 := witnesses.shift_u16
  let lower_limb := witnesses.lower_limb
  let higher_limb := witnesses.higher_limb
  let limb_result := witnesses.limb_result
  let sllw_msb := witnesses.sllw_msb
  let flags := witnesses.flags
  let is_sll := flags[0]; let is_sllw := flags[1]; let is_sllw_imm := flags[2]
  let gate := is_sll + is_sllw
  assertion U16MSBOperation.circuit ⟨a[1], ⟨sllw_msb[0]⟩, is_sllw⟩
  -- `ALUTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ALUTypeReader.circuit (postWitnessReaderInput input witnesses)
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the shift placement, so `isU64 a` (the placed result word's per-limb range, derived from the
  -- `lower/higher_limb` byte pulls) discharges its requirement — breaking the old reader-circularity. The
  -- write access clock is the recombined low clock `+ 4`; `gate = is_sll + is_sllw` matches the reader.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, gate⟩
  -- `is_real` boolean gate emitted **inline** (`assertZero`, not `=== 0`) so the `enabled = is_real`
  -- selector is visible to `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table.
  assertZero (input.is_real * (input.is_real - 1))
  -- Lean-only glue identifying the public selector with SP1's variant sum. This is a parent-level
  -- structural assertion, not an independent proof boundary, and is flat-identical to `=== 0`.
  assertZero (input.is_real - (is_sll + is_sllw))
  -- shorthands for the committed column expressions (pure lets — no operations emitted)
  let b0 := c_bits[0]; let b1 := c_bits[1]; let b2 := c_bits[2]
  let b3 := c_bits[3]; let b4 := c_bits[4]; let b5 := c_bits[5]
  let bitShift := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt := bitShift + b4 * 16 + b5 * 32
  let e32 := (input.adapter.op_c_memory.prev_value[0] - shamt) * Expression.const ((64 : ZMod p)⁻¹)
  -- ## The inline shift assertZero constraints (in the generated oracle `asserts` order)
  -- variant flags. The combined selector `is_sll + is_sllw` (= the byte-pull gate) is boolean-gated
  -- **inline** (`assertZero`, not `=== 0`) so it is visible to `ConstraintsHold.Shallow`, discharging the
  -- off-gate byte-pull `Requirements` without keeping `byteChannel` in `channelsWithRequirements`.
  assertZero ((is_sll + is_sllw) * ((is_sll + is_sllw) - 1))
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  let cols : Var Columns (ZMod p) :=
    ⟨input.state, input.adapter, a, c_bits, v[0], v[1], v[2], shift_u16,
      lower_limb, higher_limb, limb_result, ⟨sllw_msb[0]⟩, is_sll, is_sllw, is_sllw_imm⟩
  assertion ShiftLeftCore.circuit cols
  -- ## The nine byte-range pulls (gated by `gate = is_sll + is_sllw`); **raw** value (`toRaw` (gated post-#398))
  byteChannel.pullIf gate
    (⟨6, e32, Expression.const ((10 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[0], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[0], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[1], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[1], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[2], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[2], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[3], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[3], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  return cols

/-- Compose the threaded `CPUState`/`ALUTypeReader` reader blocks and the `U16MSBOperation` (`sllw_msb`)
gadget as Clean sub-assertions, **witness** the shift column block honestly (the result `a`, the
`c_bits`, the `v_*` powers, the `shift_u16` selector, the `lower/higher_limb`/`limb_result` words, the
`sllw_msb` — the `Populate` closures, ported from SP1's `event_to_row`; the variant flags come from the
`"shift_left_flags"` `ProverHint`), gate `is_real` (`= is_sll + is_sllw`), emit the inline shift
assertZero constraints (`AssertSpec`) and the nine `gate`-gated byte-range pulls (`InteractSpec`), and
assemble the native `Columns` struct. (Soundness ranges over every satisfying assignment
regardless of the generators; the generators carry completeness and the `TraceGenTests` conformance.) -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let witnesses ← witnessPrefix input
  postWitness input witnesses

omit [Fact (2 ^ 17 < p)] in
private theorem subcircuitMem_bind_left {F α β} [FiniteField F]
    {subOffset : ℕ} {sub : Subcircuit F subOffset}
    (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (mem : ⟨subOffset, sub⟩ ∈ (left.operations offset).subcircuits) :
    ⟨subOffset, sub⟩ ∈ ((left >>= right).operations offset).subcircuits := by
  rw [Circuit.bind_operations_eq, Operations.subcircuits_append, List.mem_append]
  exact Or.inl mem

omit [Fact (2 ^ 17 < p)] in
private theorem subcircuitMem_bind_right {F α β} [FiniteField F]
    {subOffset : ℕ} {sub : Subcircuit F subOffset}
    (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (mem : ⟨subOffset, sub⟩ ∈
      ((right (left.output offset)).operations (offset + left.localLength offset)).subcircuits) :
    ⟨subOffset, sub⟩ ∈ ((left >>= right).operations offset).subcircuits := by
  rw [Circuit.bind_operations_eq, Operations.subcircuits_append, List.mem_append]
  exact Or.inr mem

omit [Fact (2 ^ 17 < p)] in
private theorem subcircuitMem_bind_right_zero {F α β} [FiniteField F]
    {subOffset : ℕ} {sub : Subcircuit F subOffset}
    (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (hlen : left.localLength offset = 0)
    (mem : ⟨subOffset, sub⟩ ∈
      ((right (left.output offset)).operations offset).subcircuits) :
    ⟨subOffset, sub⟩ ∈ ((left >>= right).operations offset).subcircuits := by
  rw [Circuit.bind_operations_eq, Operations.subcircuits_append, List.mem_append]
  exact Or.inr (by simpa only [hlen, Nat.add_zero] using mem)

omit [Fact (2 ^ 17 < p)] in
private theorem constraintMem_bind_left {F α β} [FiniteField F]
    {e : Expression F} (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (mem : e ∈ (left.operations offset).constraints) :
    e ∈ ((left >>= right).operations offset).constraints := by
  rw [Circuit.bind_operations_eq, Operations.constraints_append, List.mem_append]
  exact Or.inl mem

omit [Fact (2 ^ 17 < p)] in
private theorem constraintMem_bind_right {F α β} [FiniteField F]
    {e : Expression F} (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ)
    (mem : e ∈
      ((right (left.output offset)).operations
        (offset + left.localLength offset)).constraints) :
    e ∈ ((left >>= right).operations offset).constraints := by
  rw [Circuit.bind_operations_eq, Operations.constraints_append, List.mem_append]
  exact Or.inr mem

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem equalityAssertionConstraint_mem
    (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((x === y).operations offset).constraints := by
  simpa only [HasAssertEq.assert_eq, Expression.assertEquals,
    assertion, subcircuitWithAssertion, Circuit.operations, Operations.constraints_subcircuit,
    Operations.constraints_nil, List.append_nil, FormalAssertion.toSubcircuit,
    Operations.toNested_toFlat, Operations.constraints_toFlat,
    Gadgets.Equality.circuit] using equalityConstraint_mem x y offset

omit [Fact (2 ^ 17 < p)] in
private theorem equalityAssertionLocalLength_eq
    (x y : Expression (ZMod p)) (offset : ℕ) :
    (x === y).localLength offset = 0 := by
  simp only [circuit_norm]

private theorem aluReader_mem_postWitness (input : Var Inputs (ZMod p))
    (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    ⟨offset, Readers.ALUTypeReader.circuit.toSubcircuit offset
      (postWitnessReaderInput input witnesses)⟩ ∈
        ((postWitness input witnesses).operations offset).subcircuits := by
  unfold postWitness
  apply subcircuitMem_bind_right
  apply subcircuitMem_bind_left
  simp only [subcircuitWithAssertion, Circuit.operations,
    Operations.subcircuits_subcircuit, Operations.subcircuits_nil, List.mem_singleton,
    circuit_norm, Nat.add_zero]

/-- The exact ALU-reader input assembled after the folded 33-cell witness prefix. This is a
structural chip interface used by grounding proofs; it does not duplicate the reader's semantics. -/
def aluReaderInput (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  let gate := var ⟨offset + 30⟩ + var ⟨offset + 31⟩
  ⟨input.adapter, gate, gate, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    var ⟨offset + 30⟩ * 6 + var ⟨offset + 31⟩ * 21,
    var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩, var ⟨offset + 3⟩⟩

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefixLocalLength_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (witnessPrefix input).localLength offset = 33 := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem postWitnessReaderInput_witnessPrefixOutput
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    postWitnessReaderInput input ((witnessPrefix input).output offset) =
      aluReaderInput input offset := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem constraints_formalAssertion
    {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion (ZMod p) Input) (offset : ℕ)
    (input : Var Input (ZMod p)) :
    FlatOperation.constraints
        (circuit.toSubcircuit offset input).ops.toFlat =
      ((circuit.main input).operations offset).constraints := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]

omit [Fact (2 ^ 17 < p)] in
private theorem constraints_generalFormalCircuit
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (offset : ℕ) (input : Var Input (ZMod p)) :
    FlatOperation.constraints
        (circuit.toSubcircuit offset input).ops.toFlat =
      ((circuit.main input).operations offset).constraints := by
  simp only [GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]

private theorem postWitness_constraints_decompose
    (env : Environment (ZMod p)) (input : Var Inputs (ZMod p))
    (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (List.map (Expression.eval env)
          ((postWitness input witnesses).operations offset).constraints) ↔
      (List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((U16MSBOperation.main
              ⟨witnesses.a[1], ⟨witnesses.sllw_msb[0]⟩,
                witnesses.flags[1]⟩).operations offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Readers.ALUTypeReader.main
              (postWitnessReaderInput input witnesses)).operations offset).constraints) ∧
       (ProvableStruct.eval env input).is_real *
          ((ProvableStruct.eval env input).is_real - 1) = 0 ∧
       (ProvableStruct.eval env input).is_real -
          (Expression.eval env witnesses.flags[0] +
            Expression.eval env witnesses.flags[1]) = 0 ∧
       Expression.eval env
          ((witnesses.flags[0] + witnesses.flags[1]) *
            (witnesses.flags[0] + witnesses.flags[1] - 1)) = 0 ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (witnesses.flags[0] * (witnesses.flags[0] - 1),
                0)).operations offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (witnesses.flags[1] * (witnesses.flags[1] - 1),
                0)).operations offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((ShiftLeftCore.main
              ((postWitness input witnesses).output offset)).operations
                offset).constraints)) := by
  simp only [postWitness, circuit_norm, List.map_append,
    List.forall_append, List.forall_cons,
    constraints_formalAssertion, constraints_generalFormalCircuit,
    U16MSBOperation.circuit, Readers.ALUTypeReader.circuit,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    ShiftLeftCore.circuit]

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefix_flag0 (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).output offset).flags[0] =
      var { index := offset + 30 } := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefix_flag1 (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).output offset).flags[1] =
      var { index := offset + 31 } := by
  rfl

private theorem cpuCircuitLocalLength_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Readers.CPUState.circuit
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
        8, input.is_real⟩).localLength offset = 0 := by
  simp only [circuit_norm]

/-- Channel projections of the whole chip can discard the witness-only prefix before inspecting
the post-witness body.  This is the structural normalization boundary for consumers that must not
force the 33-cell witness generator chain while merely classifying interactions. -/
theorem interactionsWith_main_decompose (input : Var Inputs (ZMod p)) (offset : ℕ)
    (channel : RawChannel (ZMod p)) :
    ((main input).operations offset).interactionsWith channel =
      ((Readers.CPUState.circuit
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).interactionsWith channel ++
      ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 33)).interactionsWith channel := by
  unfold main
  rw [Circuit.bind_operations_eq, Operations.interactionsWith_append]
  simp only [cpuCircuitLocalLength_eq, Nat.add_zero]
  rw [Circuit.bind_operations_eq, Operations.interactionsWith_append]
  have witnessInteractions :
      ((witnessPrefix input).operations offset).interactionsWith channel = [] := by
    unfold witnessPrefix Circuit.operations
    simp only [Operations.interactionsWith_witness, Operations.interactionsWith_nil]
  rw [witnessInteractions, List.nil_append, witnessPrefixLocalLength_eq]

private theorem postWitness_stateInteractions_eq (input : Var Inputs (ZMod p))
    (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    ((postWitness input witnesses).operations offset).interactionsWith stateChannel.toRaw = [] := by
  unfold postWitness
  simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
    subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
    Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [Operations.interactionsWith_append,
    ShiftLeftCore.interactionsWith_subcircuit_eq_nil,
    InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
    InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
    U16MSBOperation.circuit, U16MSBOperation.channelsWithGuarantees_eq,
    Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    Readers.ALUTypeReader.channelsWithGuarantees_eq,
    Readers.RegisterWrite.channelsWithGuarantees_eq,
    Gadgets.Equality.channelsWithGuarantees_eq, Gadgets.Equality.channelsWithRequirements_eq,
    List.mem_cons, List.not_mem_nil, or_false,
    Channels.stateChannel_eq_byteChannel_false, Channels.stateChannel_eq_programChannel_false,
    Channels.stateChannel_eq_memoryChannel_false, not_false_eq_true,
    Operations.interactionsWith_assert, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel,
    Channels.byteChannel_eq_stateChannel_false, if_false, List.append_nil]

/-- `CPUState` contributes the whole chip's exact State-channel interaction list. -/
theorem interactionsWith_main_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (Readers.CPUState.stateInteractions
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).map ChannelInteraction.toRaw := by
  rw [interactionsWith_main_decompose, postWitness_stateInteractions_eq]
  simp only [Circuit.operations, subcircuitWithAssertion,
    Readers.CPUState.interactionsWith_state_subcircuit,
    Operations.interactionsWith_nil, List.append_nil]

/-- ShiftLeft's State pair written directly over the chip inputs. -/
def exposedStateInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
        input.state.clk_0_16 + input.state.clk_16_24 * 65536,
        input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
        input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
        input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

/-- Direct-input form of ShiftLeft's exact State projection. -/
theorem interactionsWith_main_state_exposed_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input).map ChannelInteraction.toRaw := by
  rw [interactionsWith_main_state_eq]
  simp only [Readers.CPUState.stateInteractions,
    Readers.CPUState.currentMsg, Readers.CPUState.nextMsg,
    exposedStateInteractions, List.map_cons, List.map_nil,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]

/-- The reader's literal witnessed selector `is_sll + is_sllw` (cells `offset+30..31`). -/
def exposedGate (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 30⟩ + var ⟨offset + 31⟩

/-- The witnessed Program opcode `SLL·6 + SLLW·21`. -/
def exposedOpcode (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 30⟩ * 6 + var ⟨offset + 31⟩ * 21

/-- Exact Byte-channel list emitted by ShiftLeft's native composition: the CPU clock checks,
the SLLW-MSB check, the three register timestamp pairs, and the nine shift-range checks. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let a : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  let cBits : Vector (Expression (ZMod p)) 6 :=
    Vector.mapRange 6 fun i => var { index := offset + 4 + i }
  let lowerLimb : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 17 + i }
  let higherLimb : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 21 + i }
  let sllwMsb : Expression (ZMod p) := var { index := offset + 29 }
  let isSllw : Expression (ZMod p) := var { index := offset + 31 }
  let gate : Expression (ZMod p) := exposedGate offset
  let clkLow : Expression (ZMod p) :=
    input.state.clk_0_16 + input.state.clk_16_24 * 65536
  let bitShift : Expression (ZMod p) :=
    cBits[0] * (1 : Expression (ZMod p)) +
      cBits[1] * (2 : Expression (ZMod p)) +
      cBits[2] * (4 : Expression (ZMod p)) +
      cBits[3] * (8 : Expression (ZMod p))
  let shiftHigh : Expression (ZMod p) :=
    (input.adapter.op_c_memory.prev_value[0] -
      (bitShift + cBits[4] * (16 : Expression (ZMod p)) +
        cBits[5] * (32 : Expression (ZMod p)))) *
        Expression.const ((64 : ZMod p)⁻¹)
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
        Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.state.clk_16_24, 0⟩,
    byteChannel.pulledIf isSllw
      ⟨6, (2 : Expression (ZMod p)) * a[1] - sllwMsb * 65536,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf gate
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf gate
      ⟨3, 0,
        (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf gate
      ⟨3, 0,
        (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf (gate - input.adapter.imm_c)
      ⟨6, input.adapter.op_c_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (gate - input.adapter.imm_c)
      ⟨3, 0,
        (clkLow + 2 -
          input.adapter.op_c_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, shiftHigh, Expression.const ((10 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[0], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[0], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[1], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[1], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[2], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[2], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[3], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[3], bitShift, 0⟩ ]

private def cpuByteInteractionsRaw
    (input : Var Readers.CPUState.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, (input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
        Expression.const ((13 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0, input.cols.clk_16_24, 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem cpuByteInteractions_exact
    (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      cpuByteInteractionsRaw input := by
  simp [Readers.CPUState.main, cpuByteInteractionsRaw, circuit_norm]

private theorem cpuByteInteractions_subcircuit
    (input : Var Readers.CPUState.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.CPUState.circuit (p := p)).toSubcircuit offset input) :: ops) =
      cpuByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.CPUState.circuit byteChannel.toRaw input offset ops _
      (cpuByteInteractions_exact input offset)

private theorem cpuByteInteractions_circuit
    (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.circuit input).operations offset).interactionsWith
        byteChannel.toRaw =
      cpuByteInteractionsRaw input := by
  change Operations.interactionsWith byteChannel.toRaw
      [.subcircuit
        ((Readers.CPUState.circuit (p := p)).toSubcircuit offset input)] =
    cpuByteInteractionsRaw input
  rw [cpuByteInteractions_subcircuit]
  simp only [Operations.interactionsWith_nil, List.append_nil]

private def u16MsbByteInteractionsRaw
    (input : Var U16MSBOperation.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, (2 : Expression (ZMod p)) * input.a -
          input.cols.msb * 65536,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem u16MsbByteInteractions_exact
    (input : Var U16MSBOperation.Inputs (ZMod p)) (offset : ℕ) :
    ((U16MSBOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      u16MsbByteInteractionsRaw input := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [U16MSBOperation.main, u16MsbByteInteractionsRaw,
    circuit_norm, heq]

private theorem u16MsbByteInteractions_subcircuit
    (input : Var U16MSBOperation.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((U16MSBOperation.circuit (p := p)).toSubcircuit offset input) :: ops) =
      u16MsbByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
    U16MSBOperation.circuit byteChannel.toRaw input offset ops _
      (u16MsbByteInteractions_exact input offset)

private def aluTypeByteInteractionsRaw
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.op_a_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0,
        (input.clk_low + 4 -
          input.cols.op_a_memory.access_timestamp.prev_low - 1 -
          input.cols.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.op_b_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0,
        (input.clk_low + 3 -
          input.cols.op_b_memory.access_timestamp.prev_low - 1 -
          input.cols.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩).toRaw,
    (byteChannel.pulledIf (input.is_real - input.cols.imm_c)
      ⟨6, input.cols.op_c_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf (input.is_real - input.cols.imm_c)
      ⟨3, 0,
        (input.clk_low + 2 -
          input.cols.op_c_memory.access_timestamp.prev_low - 1 -
          input.cols.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩).toRaw ]

private theorem aluTypeByteInteractions_exact
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ALUTypeReader.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      aluTypeByteInteractionsRaw input := by
  simp [Readers.ALUTypeReader.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    aluTypeByteInteractionsRaw, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions, circuit_norm]

private theorem aluTypeByteInteractions_subcircuit
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.ALUTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      aluTypeByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.ALUTypeReader.circuit byteChannel.toRaw input offset ops _
      (aluTypeByteInteractions_exact input offset)

omit [Fact (2 ^ 17 < p)] in
private theorem registerWriteByteInteractions_exact
    (input : Var Readers.RegisterWrite.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.RegisterWrite.main input).operations offset).interactionsWith
        byteChannel.toRaw = [] := by
  simp [Readers.RegisterWrite.main, circuit_norm]

private theorem registerWriteByteInteractions_subcircuit
    (input : Var Readers.RegisterWrite.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.RegisterWrite.circuit (p := p)).toSubcircuit offset input) :: ops) =
      Operations.interactionsWith byteChannel.toRaw ops := by
  have h :=
    InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
      Readers.RegisterWrite.circuit byteChannel.toRaw input offset ops []
        (registerWriteByteInteractions_exact input offset)
  simpa only [List.nil_append] using h

private def shiftRangeByteInteractionsRaw
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  let gate : Expression (ZMod p) :=
    witnesses.flags[0] + witnesses.flags[1]
  let bitShift : Expression (ZMod p) :=
    witnesses.c_bits[0] * (1 : Expression (ZMod p)) +
      witnesses.c_bits[1] * (2 : Expression (ZMod p)) +
      witnesses.c_bits[2] * (4 : Expression (ZMod p)) +
      witnesses.c_bits[3] * (8 : Expression (ZMod p))
  let shiftHigh : Expression (ZMod p) :=
    (input.adapter.op_c_memory.prev_value[0] -
      (bitShift +
        witnesses.c_bits[4] * (16 : Expression (ZMod p)) +
        witnesses.c_bits[5] * (32 : Expression (ZMod p)))) *
          Expression.const ((64 : ZMod p)⁻¹)
  [ (byteChannel.pulledIf gate
      ⟨6, shiftHigh, Expression.const ((10 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[0], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[0], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[1], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[1], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[2], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[2], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[3], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[3], bitShift, 0⟩).toRaw ]

private theorem postWitness_byteInteractions_eq
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p))
    (offset : ℕ) :
    ((postWitness input witnesses).operations offset).interactionsWith
        byteChannel.toRaw =
      u16MsbByteInteractionsRaw
          ⟨witnesses.a[1], ⟨witnesses.sllw_msb[0]⟩,
            witnesses.flags[1]⟩ ++
        aluTypeByteInteractionsRaw
          (postWitnessReaderInput input witnesses) ++
        shiftRangeByteInteractionsRaw input witnesses := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p))
      (ops : Operations (ZMod p)) =>
    @InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp ops
      List.not_mem_nil List.not_mem_nil
  simp only [postWitness, Circuit.operations, Circuit.bind_def,
    Circuit.pure_def, subcircuitWithAssertion, assertion, assertZero,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Operations.localLength]
  simp only [Operations.interactionsWith_append,
    u16MsbByteInteractions_subcircuit,
    aluTypeByteInteractions_subcircuit,
    registerWriteByteInteractions_subcircuit,
    ShiftLeftCore.interactionsWith_subcircuit_eq_nil,
    heq,
    Operations.interactionsWith_assert,
    Operations.interactionsWith_nil,
    List.nil_append]
  simp only [shiftRangeByteInteractionsRaw, circuit_norm,
    List.cons_append, List.nil_append]

/-- The exact Byte interaction list of the whole folded ShiftLeft chip. -/
theorem interactionsWith_main_byte_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      (exposedByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  rw [interactionsWith_main_decompose,
    cpuByteInteractions_circuit,
    postWitness_byteInteractions_eq]
  simp only [cpuByteInteractionsRaw, u16MsbByteInteractionsRaw,
    aluTypeByteInteractionsRaw, shiftRangeByteInteractionsRaw,
    exposedByteInteractions, postWitnessReaderInput, witnessPrefix,
    Circuit.output, exposedGate, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange,
    List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Nat.reduceAdd, Nat.add_assoc]

/-- ShiftLeft's exact Memory-channel interaction list.  This structural definition lives beside
`main`; the semantic `circuit` bundle merely exposes it. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf (exposedGate offset)
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf (exposedGate offset)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedGate offset)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf (exposedGate offset - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedGate offset - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedGate offset)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + i }⟩ ]

private theorem postWitness_memoryInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 33)).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  unfold postWitness
  simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
    subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
    Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [Soundness.aluTypeReader_memoryInteractions_subcircuit,
    Soundness.registerWrite_memoryInteractions_subcircuit,
    ShiftLeftCore.interactionsWith_subcircuit_eq_nil,
    InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
    U16MSBOperation.circuit, U16MSBOperation.channelsWithGuarantees_eq,
    Gadgets.Equality.channelsWithGuarantees_eq, Gadgets.Equality.channelsWithRequirements_eq,
    FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
    Channels.memoryChannel_eq_byteChannel_false, not_false_eq_true,
    Operations.interactionsWith_assert, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel,
    Channels.byteChannel_eq_memoryChannel_false, if_false, List.append_nil,
    Soundness.aluTypeMemoryInteractions, Soundness.registerWriteMemoryInteractions,
    List.cons_append, List.nil_append]
  simp only [exposedMemoryInteractions, exposedGate, witnessPrefix, Circuit.output,
    Vector.mapRange, List.map_cons, List.map_nil]
  rfl

/-- The exact Memory interaction list of the whole folded ShiftLeft chip. -/
theorem interactionsWith_main_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  rw [interactionsWith_main_decompose, postWitness_memoryInteractions_eq]
  have cpuNil :
      ((Readers.CPUState.circuit
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).interactionsWith memoryChannel.toRaw = [] := by
    change Operations.interactionsWith memoryChannel.toRaw
      [.subcircuit ((Readers.CPUState.circuit (p := p)).toSubcircuit offset
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩)] = []
    exact InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil
      Readers.CPUState.circuit memoryChannel.toRaw _ []
      (by
        change memoryChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
        simp only [List.mem_cons, List.not_mem_nil, or_false,
          Channels.memoryChannel_eq_byteChannel_false,
          Channels.memoryChannel_eq_stateChannel_false, not_false_eq_true])
      (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil)
  rw [cpuNil, List.nil_append]

/-- The exact Program fetch emitted by ShiftLeft's ALU adapter. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf (exposedGate offset)
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], exposedOpcode offset,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
       input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

private theorem postWitness_programInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 33)).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input offset).map ChannelInteraction.toRaw := by
  unfold postWitness
  simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
    subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
    Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [Operations.interactionsWith_append,
    Soundness.aluTypeReader_programInteractions_subcircuit,
    ShiftLeftCore.interactionsWith_subcircuit_eq_nil,
    InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
    U16MSBOperation.circuit, U16MSBOperation.channelsWithGuarantees_eq,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
    Gadgets.Equality.channelsWithGuarantees_eq, Gadgets.Equality.channelsWithRequirements_eq,
    FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
    Channels.programChannel_eq_byteChannel_false,
    Channels.programChannel_eq_memoryChannel_false, not_false_eq_true,
    Operations.interactionsWith_assert, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, ChannelInteraction.toRaw_channel,
    Channels.byteChannel_eq_programChannel_false, if_false, List.append_nil,
    Soundness.aluTypeProgramMessage, List.nil_append]
  simp only [postWitnessReaderInput, exposedProgramInteractions, exposedGate, exposedOpcode,
    witnessPrefix, Circuit.output, List.map_cons, List.map_nil]
  rfl

/-- The exact Program interaction of the whole folded ShiftLeft chip. -/
theorem interactionsWith_main_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input offset).map ChannelInteraction.toRaw := by
  rw [interactionsWith_main_decompose, postWitness_programInteractions_eq]
  have cpuNil :
      ((Readers.CPUState.circuit
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).interactionsWith programChannel.toRaw = [] := by
    change Operations.interactionsWith programChannel.toRaw
      [.subcircuit ((Readers.CPUState.circuit (p := p)).toSubcircuit offset
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩)] = []
    exact InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil
      Readers.CPUState.circuit programChannel.toRaw _ []
      (by
        change programChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
        simp only [List.mem_cons, List.not_mem_nil, or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false, not_false_eq_true])
      (by change programChannel.toRaw ∉ []; exact List.not_mem_nil)
  rw [cpuNil, List.nil_append]

/-- The composed ALU reader occurs at the exact post-witness offset in the whole chip. -/
theorem aluReader_mem_subcircuits (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 33, Readers.ALUTypeReader.circuit.toSubcircuit (offset + 33)
      (aluReaderInput input offset)⟩ ∈ ((main input).operations offset).subcircuits := by
  unfold main
  apply subcircuitMem_bind_right
  apply subcircuitMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    postWitnessReaderInput_witnessPrefixOutput, Nat.add_zero] using
    aluReader_mem_postWitness input ((witnessPrefix input).output offset) (offset + 33)

private theorem selectorLink_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    input.is_real -
        (witnesses.flags[0] + witnesses.flags[1]) ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 4 apply constraintMem_bind_right
  apply constraintMem_bind_left
  simp only [assertZero, Circuit.operations, Operations.constraints_assert,
    Operations.constraints_nil, List.mem_singleton]

private theorem sllBool_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    witnesses.flags[0] * (witnesses.flags[0] - 1) - 0 ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 6 apply constraintMem_bind_right
  apply constraintMem_bind_left
  exact equalityAssertionConstraint_mem
    (witnesses.flags[0] * (witnesses.flags[0] - 1))
    (0 : Expression (ZMod p)) _

private theorem sllwBool_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    witnesses.flags[1] * (witnesses.flags[1] - 1) - 0 ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 7 apply constraintMem_bind_right
  apply constraintMem_bind_left
  exact equalityAssertionConstraint_mem
    (witnesses.flags[1] * (witnesses.flags[1] - 1))
    (0 : Expression (ZMod p)) _

private theorem core_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    ⟨offset, ShiftLeftCore.circuit.toSubcircuit offset
      ((postWitness input witnesses).output offset)⟩ ∈
      ((postWitness input witnesses).operations offset).subcircuits := by
  unfold postWitness
  iterate 6 apply subcircuitMem_bind_right
  apply subcircuitMem_bind_right_zero (hlen := equalityAssertionLocalLength_eq _ _ _)
  apply subcircuitMem_bind_right_zero (hlen := equalityAssertionLocalLength_eq _ _ _)
  apply subcircuitMem_bind_left
  simp only [assertion, Circuit.operations, Operations.subcircuits_subcircuit,
    Operations.subcircuits_nil, List.mem_singleton, circuit_norm, Nat.add_zero]

/-- The exact row passed to the folded arithmetic core after the witness prefix. -/
def coreInput (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Var Columns (ZMod p) :=
  (postWitness input ((witnessPrefix input).output offset)).output (offset + 33)

@[circuit_norm] theorem coreInput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    coreInput input offset =
      (⟨input.state, input.adapter,
        varFromOffset (Vector · 4) offset,
        varFromOffset (Vector · 6) (offset + 4),
        var { index := offset + 10 }, var { index := offset + 11 },
        var { index := offset + 12 },
        varFromOffset (Vector · 4) (offset + 13),
        varFromOffset (Vector · 4) (offset + 17),
        varFromOffset (Vector · 4) (offset + 21),
        varFromOffset (Vector · 4) (offset + 25),
        ⟨var { index := offset + 29 }⟩,
        var { index := offset + 30 }, var { index := offset + 31 },
        var { index := offset + 32 }⟩ : Var Columns (ZMod p)) := rfl

private theorem constraints_main_bind_decompose
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).constraints =
      ((Readers.CPUState.circuit
        ⟨input.state,
          #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).constraints ++
      ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 33)).constraints := by
  unfold main
  rw [Circuit.bind_operations_eq, Operations.constraints_append]
  simp only [cpuCircuitLocalLength_eq, Nat.add_zero]
  rw [Circuit.bind_operations_eq, Operations.constraints_append]
  have witnessConstraints :
      ((witnessPrefix input).operations offset).constraints = [] := by
    unfold witnessPrefix Circuit.operations
    simp only [Operations.constraints_witness,
      Operations.constraints_nil]
  rw [witnessConstraints, List.nil_append,
    witnessPrefixLocalLength_eq]

/-- Exact folded decomposition of every native ShiftLeft assertion.  This is the structural
normalization boundary used by the whole-chip Rust faithfulness proof: the expensive 33-cell
witness generator stays opaque, while the genuine Clean subcircuits and the five parent selector
constraints remain visible as complete blocks. -/
theorem constraints_decompose
    (env : Environment (ZMod p)) (input : Var Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (List.map (Expression.eval env)
          ((main input).operations offset).constraints) ↔
      (List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Readers.CPUState.main
              ⟨input.state,
                #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((U16MSBOperation.main
              ⟨(varFromOffset (Vector · 4) offset)[1],
                ⟨var { index := offset + 29 }⟩,
                var { index := offset + 31 }⟩).operations
                  (offset + 33)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Readers.ALUTypeReader.main
              (aluReaderInput input offset)).operations
                (offset + 33)).constraints) ∧
       (ProvableStruct.eval env input).is_real *
          ((ProvableStruct.eval env input).is_real - 1) = 0 ∧
       (ProvableStruct.eval env input).is_real -
          (Expression.eval env (var { index := offset + 30 }) +
            Expression.eval env (var { index := offset + 31 })) = 0 ∧
       (Expression.eval env (var { index := offset + 30 }) +
          Expression.eval env (var { index := offset + 31 })) *
            (Expression.eval env (var { index := offset + 30 }) +
              Expression.eval env (var { index := offset + 31 }) - 1) = 0 ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (var { index := offset + 30 } *
                  (var { index := offset + 30 } - 1),
                0)).operations (offset + 33)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (var { index := offset + 31 } *
                  (var { index := offset + 31 } - 1),
                0)).operations (offset + 33)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((ShiftLeftCore.main
              (coreInput input offset)).operations
                (offset + 33)).constraints)) := by
  rw [constraints_main_bind_decompose]
  simp only [List.map_append, List.forall_append,
    Circuit.operations, subcircuitWithAssertion,
    Operations.constraints_subcircuit, Operations.constraints_nil,
    List.append_nil, constraints_generalFormalCircuit]
  rw [postWitness_constraints_decompose]
  rw [postWitnessReaderInput_witnessPrefixOutput]
  simp only [witnessPrefix, Circuit.output, aluReaderInput,
    coreInput, Readers.CPUState.circuit,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange,
    eval_sub, Expression.eval,
    Nat.add_assoc, Nat.reduceAdd]

/-- The Lean-side `is_real = is_sll + is_sllw` glue is retained in the whole chip. -/
theorem selectorLink_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    input.is_real -
        (var { index := offset + 30 } + var { index := offset + 31 }) ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag0, witnessPrefix_flag1] using
    selectorLink_mem_postWitness input ((witnessPrefix input).output offset) (offset + 33)

/-- The `is_sll` boolean assertion is retained at the post-witness offset. -/
theorem sllBool_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 30 } * (var { index := offset + 30 } - 1) - 0 ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag0] using
    sllBool_mem_postWitness input ((witnessPrefix input).output offset) (offset + 33)

/-- The `is_sllw` boolean assertion is retained at the post-witness offset. -/
theorem sllwBool_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 31 } * (var { index := offset + 31 } - 1) - 0 ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag1] using
    sllwBool_mem_postWitness input ((witnessPrefix input).output offset) (offset + 33)

/-- The folded arithmetic core is retained at the post-witness offset. -/
theorem core_mem_subcircuits (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 33,
      ShiftLeftCore.circuit.toSubcircuit (offset + 33)
        (coreInput input offset)⟩ ∈
      ((main input).operations offset).subcircuits := by
  unfold main
  apply subcircuitMem_bind_right
  apply subcircuitMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    coreInput, Nat.add_zero] using
    core_mem_postWitness input ((witnessPrefix input).output offset) (offset + 33)

@[implicit_reducible] private def derivedElaborated :
    ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit_with {
    channelsWithGuarantees :=
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  }

/-- Clean owns the output layout and every structural proof.  This thin public record forwards them
while keeping the declared channel order visible at the chip boundary. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  output := derivedElaborated.output
  output_eq := derivedElaborated.output_eq
  localLength := derivedElaborated.localLength
  localLength_eq := derivedElaborated.localLength_eq
  subcircuitsConsistent := derivedElaborated.subcircuitsConsistent
  channelsWithGuarantees :=
    [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := derivedElaborated.channelsLawful

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 33 := rfl

/-- The completed ShiftLeft row, exposed without unfolding the folded witness circuit. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        varFromOffset (Vector · 4) offset,
        varFromOffset (Vector · 6) (offset + 4),
        var { index := offset + 10 }, var { index := offset + 11 },
        var { index := offset + 12 },
        varFromOffset (Vector · 4) (offset + 13),
        varFromOffset (Vector · 4) (offset + 17),
        varFromOffset (Vector · 4) (offset + 21),
        varFromOffset (Vector · 4) (offset + 25),
        ⟨var { index := offset + 29 }⟩,
        var { index := offset + 30 }, var { index := offset + 31 },
        var { index := offset + 32 }⟩ : Var Columns (ZMod p)) := rfl

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real, state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         a := Eval.eval env cols.a, c_bits := Eval.eval env cols.c_bits,
         v_01 := Eval.eval env cols.v_01, v_012 := Eval.eval env cols.v_012,
         v_0123 := Eval.eval env cols.v_0123,
         shift_u16 := Eval.eval env cols.shift_u16,
         lower_limb := Eval.eval env cols.lower_limb,
         higher_limb := Eval.eval env cols.higher_limb,
         limb_result := Eval.eval env cols.limb_result,
         sllw_msb := Eval.eval env cols.sllw_msb,
         is_sll := Eval.eval env cols.is_sll, is_sllw := Eval.eval env cols.is_sllw,
         is_sllw_imm := Eval.eval env cols.is_sllw_imm } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_inputAdapter {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [eval_inputs]

@[circuit_norm] theorem eval_inputIsReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [CircuitType.eval_expr] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

private theorem postWitness_requirementsChannelsLawful (input : Var Inputs (ZMod p))
    (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    ((postWitness input witnesses).operations offset).RequirementsChannelsLawful
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
      [memoryChannel.toRaw] := by
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · unfold postWitness
    simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
      subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
      Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
      FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
      Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
      Gadgets.Equality.localLength_eq, Nat.add_zero]
    simp only [Operations.subcircuitChannelsWithRequirements_append,
      Operations.subcircuitChannelsWithRequirements_subcircuit,
      Operations.subcircuitChannelsWithRequirements_assert,
      Operations.subcircuitChannelsWithRequirements_interact,
      Operations.subcircuitChannelsWithRequirements_nil,
      GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
      FormalAssertion.toSubcircuit_channelsWithRequirements,
      U16MSBOperation.circuit, Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
      Gadgets.Equality.channelsWithRequirements_eq, List.nil_append, List.append_nil]
    simp only [List.subset_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro channel h_channel
    unfold postWitness at h_channel
    simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
      subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
      Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
      FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
      Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
      Gadgets.Equality.localLength_eq, Nat.add_zero,
      Operations.shallowChannels_append, Operations.shallowChannels_subcircuit,
      Operations.shallowChannels_assert, Operations.shallowChannels_interact,
      Operations.shallowChannels_nil, List.nil_append,
      ChannelInteraction.toRaw_channel, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, or_self] at h_channel
    subst channel
    exact Or.inl List.mem_cons_self
  · intro env h_constraints
    unfold postWitness at h_constraints
    simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
      subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
      Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
      FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
      Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
      Gadgets.Equality.localLength_eq, Nat.add_zero,
      ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, true_and, and_true, eval_sub, Expression.eval] at h_constraints
    have h_bool := bool_of_mul_pred h_constraints.2.2
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro interaction h_interaction
    unfold postWitness at h_interaction
    simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
      subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
      Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
      FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
      Readers.RegisterWrite.circuit_localLength, ShiftLeftCore.circuit_localLength,
      Gadgets.Equality.localLength_eq, Nat.add_zero,
      Operations.shallowInteractions_append, Operations.shallowInteractions_subcircuit,
      Operations.shallowInteractions_assert, Operations.shallowInteractions_interact,
      Operations.shallowInteractions_nil, List.nil_append,
      List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      right <;>
      rw [ChannelInteraction.toRaw_requirements] <;>
      intro h1 h0 <;>
      simp only [circuit_norm] at h1 h0 <;>
      exact off_gate_vacuous h_bool h1 h0

/-- The folded witness prefix is structurally invisible to Clean's channel-requirement law; the
law is exactly the post-witness byte/memory argument above. -/
theorem requirementsChannelsLawful_main (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).RequirementsChannelsLawful
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
      [memoryChannel.toRaw] := by
  have postLaw := postWitness_requirementsChannelsLawful input
    ((witnessPrefix input).output offset) (offset + 33)
  dsimp only [Operations.RequirementsChannelsLawful] at postLaw ⊢
  obtain ⟨postSubcircuits, postChannels, postRequirements⟩ := postLaw
  refine ⟨?_, ?_, ?_⟩
  · simpa only [main, Circuit.bind_operations_eq, Circuit.operations,
      Circuit.localLength, Operations.localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      Readers.CPUState.circuit_localLength, Nat.add_zero, witnessPrefixLocalLength_eq,
      subcircuitWithAssertion, witnessPrefix,
      Operations.subcircuitChannelsWithRequirements_append,
      Operations.subcircuitChannelsWithRequirements_subcircuit,
      Operations.subcircuitChannelsWithRequirements_witness,
      Operations.subcircuitChannelsWithRequirements_nil,
      GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
      Readers.CPUState.channelsWithRequirements_eq, List.nil_append] using postSubcircuits
  · intro channel h_channel
    apply postChannels channel
    simpa only [main, Circuit.bind_operations_eq, Circuit.operations,
      Circuit.localLength, Operations.localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      Readers.CPUState.circuit_localLength, Nat.add_zero, witnessPrefixLocalLength_eq,
      subcircuitWithAssertion, witnessPrefix,
      Operations.shallowChannels_append, Operations.shallowChannels_subcircuit,
      Operations.shallowChannels_witness, Operations.shallowChannels_nil,
      List.nil_append] using h_channel
  · intro env h_constraints
    have postConstraints :
        ConstraintsHold.Shallow env
          ((postWitness input ((witnessPrefix input).output offset)).operations (offset + 33)) := by
      simpa only [main, Circuit.bind_operations_eq, Circuit.operations,
        Circuit.localLength, Operations.localLength, GeneralFormalCircuit.toSubcircuit_localLength,
        Readers.CPUState.circuit_localLength, Nat.add_zero, witnessPrefixLocalLength_eq,
        subcircuitWithAssertion, witnessPrefix, ConstraintsHold.Shallow,
        Operations.forAllNoOffset_append, Operations.forAllNoOffset,
        true_and] using h_constraints
    have postResult := postRequirements env postConstraints
    simpa only [main, Circuit.bind_operations_eq, Circuit.operations,
      Circuit.localLength, Operations.localLength, GeneralFormalCircuit.toSubcircuit_localLength,
      Readers.CPUState.circuit_localLength, Nat.add_zero, witnessPrefixLocalLength_eq,
      subcircuitWithAssertion, witnessPrefix, Operations.InChannelsOrRequirements,
      Operations.forAllNoOffset_append, Operations.forAllNoOffset,
      true_and] using postResult

/-! ## Result-word range (`isU64 a`) for the `RegisterWrite` op_a write push

The W11 Option-B memory flip composes `RegisterWrite` *after* the shift placement; its push owes
`isU64` of the placed result word `a`. These pure-field lemmas range-check the placed limbs from the
`lower/higher_limb` byte ranges (`lr` = a `limb_result` entry, `< 2^16`) and the placement asserts (each
`a_i` is `0`, a `limb_result` entry, or `msb·65535`). Shared by both `Soundness/{Sll,Sllw}.lean` tails. -/

set_option linter.unusedSectionVars false in
/-- A reassembled `limb_result` entry `lr = ll·v + hl` is a `u16` (`ll < N`, `hl < M`, `v.val = M`,
`M·N = 65536`). -/
lemma lr_val_lt {M N : ℕ} (hMN : M * N = 65536) {ll hl v : ZMod p}
    (hv : v.val = M) (hll : ll.val < N) (hhl : hl.val < M) :
    (ll * v + hl).val < 2 ^ 16 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_llv : (ll * v).val = ll.val * M := by
    rw [ZMod.val_mul_of_lt, hv]; rw [hv]; nlinarith [hll, hMN]
  have h_sum : (ll * v + hl).val = ll.val * M + hl.val := by
    rw [ZMod.val_add_of_lt, h_llv]; rw [h_llv]; nlinarith [hll, hhl, hMN]
  rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, h_sum]; nlinarith [hll, hhl, hMN]

/-- The low `limb_result` entry `lr0 = ll·v` is a `u16`. -/
lemma lr0_val_lt {M N : ℕ} (hMN : M * N = 65536) (hMpos : 0 < M) {ll v : ZMod p}
    (hv : v.val = M) (hll : ll.val < N) : (ll * v).val < 2 ^ 16 := by
  have := lr_val_lt hMN hv hll (show (0 : ZMod p).val < M by rw [ZMod.val_zero]; exact hMpos)
  rwa [add_zero] at this

set_option linter.unusedSectionVars false in
/-- **SLL result range.** From the one-hot byte-shift selectors (`s_k` boolean, `Σ s_k = 1`), the 16
`is_sll`-collapsed placement asserts, and the four `limb_result` `u16` bounds, every result limb is a
`u16` (each `a_i` is `0` or one `lr_j`). -/
lemma sll_a_isU64 {a0 a1 a2 a3 s0 s1 s2 s3 lr0 lr1 lr2 lr3 : ZMod p}
    (hs0b : s0 = 0 ∨ s0 = 1) (hs1b : s1 = 0 ∨ s1 = 1)
    (hs2b : s2 = 0 ∨ s2 = 1)
    (hssum : s0 + s1 + s2 + s3 = 1)
    (hb0 : lr0.val < 2 ^ 16) (hb1 : lr1.val < 2 ^ 16)
    (hb2 : lr2.val < 2 ^ 16) (hb3 : lr3.val < 2 ^ 16)
    (h00 : s0 * (a0 - lr0) = 0) (h01 : s0 * (a1 - lr1) = 0)
    (h02 : s0 * (a2 - lr2) = 0) (h03 : s0 * (a3 - lr3) = 0)
    (h10 : s1 * a0 = 0) (h11 : s1 * (a1 - lr0) = 0)
    (h12 : s1 * (a2 - lr1) = 0) (h13 : s1 * (a3 - lr2) = 0)
    (h20 : s2 * a0 = 0) (h21 : s2 * a1 = 0)
    (h22 : s2 * (a2 - lr0) = 0) (h23 : s2 * (a3 - lr1) = 0)
    (h30 : s3 * a0 = 0) (h31 : s3 * a1 = 0)
    (h32 : s3 * a2 = 0) (h33 : s3 * (a3 - lr0) = 0) :
    a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 ∧ a2.val < 2 ^ 16 ∧ a3.val < 2 ^ 16 := by
  have hz : (0 : ZMod p).val < 2 ^ 16 := by rw [ZMod.val_zero]; norm_num
  rcases hs0b with e0 | e0
  · rcases hs1b with e1 | e1
    · rcases hs2b with e2 | e2
      · -- s0 = s1 = s2 = 0 ⇒ s3 = 1
        have e3 : s3 = 1 := by rw [e0, e1, e2] at hssum; linear_combination hssum
        rw [e3, one_mul] at h30 h31 h32 h33
        exact ⟨by rw [h30]; exact hz, by rw [h31]; exact hz, by rw [h32]; exact hz,
          by rw [sub_eq_zero.mp h33]; exact hb0⟩
      · rw [e2, one_mul] at h20 h21 h22 h23
        exact ⟨by rw [h20]; exact hz, by rw [h21]; exact hz,
          by rw [sub_eq_zero.mp h22]; exact hb0, by rw [sub_eq_zero.mp h23]; exact hb1⟩
    · rw [e1, one_mul] at h10 h11 h12 h13
      exact ⟨by rw [h10]; exact hz, by rw [sub_eq_zero.mp h11]; exact hb0,
        by rw [sub_eq_zero.mp h12]; exact hb1, by rw [sub_eq_zero.mp h13]; exact hb2⟩
  · rw [e0, one_mul] at h00 h01 h02 h03
    exact ⟨by rw [sub_eq_zero.mp h00]; exact hb0, by rw [sub_eq_zero.mp h01]; exact hb1,
      by rw [sub_eq_zero.mp h02]; exact hb2, by rw [sub_eq_zero.mp h03]; exact hb3⟩

set_option linter.unusedSectionVars false in
/-- **SLLW result range.** From the byte-shift selectors (`cb4 ∈ {0,1}`, so only `s0`/`s1` are hot), the
low-two placement asserts, the `lr0`/`lr1` `u16` bounds, and `msb` boolean (the sign fill `a2 = a3 =
msb·65535`), every result limb is a `u16`. -/
lemma sllw_a_isU64 {a0 a1 a2 a3 s0 s1 s2 s3 cb4 lr0 lr1 msb : ZMod p}
    (hcb4 : cb4 = 0 ∨ cb4 = 1)
    (hs0sel : s0 * (cb4 - 0) = 0) (hs1sel : s1 * (cb4 - 1) = 0)
    (hs2sel : s2 * (cb4 - 2) = 0) (hs3sel : s3 * (cb4 - 3) = 0)
    (hssum : s0 + s1 + s2 + s3 = 1)
    (hb0 : lr0.val < 2 ^ 16) (hb1 : lr1.val < 2 ^ 16)
    (hmsbb : msb = 0 ∨ msb = 1)
    (h00 : s0 * (a0 - lr0) = 0) (h01 : s0 * (a1 - lr1) = 0)
    (h10 : s1 * a0 = 0) (h11 : s1 * (a1 - lr0) = 0)
    (ha2 : a2 = msb * 65535) (ha3 : a3 = msb * 65535) :
    a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 ∧ a2.val < 2 ^ 16 ∧ a3.val < 2 ^ 16 := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have hz : (0 : ZMod p).val < 2 ^ 16 := by rw [ZMod.val_zero]; norm_num
  have hmsb_bound : (msb * 65535).val < 2 ^ 16 := by
    rcases hmsbb with h | h <;> rw [h]
    · rw [zero_mul, ZMod.val_zero]; norm_num
    · rw [one_mul, show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]; norm_num
  have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have hv3 : (3 : ZMod p).val = 3 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    exact ZMod.val_natCast_of_lt (by omega)
  have n1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have n2 : (2 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv2; omega
  have n3 : (3 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv3; omega
  rcases hcb4 with h4 | h4
  · rw [h4] at hs1sel hs2sel hs3sel
    have hs1 : s1 = 0 := ShiftLeftCore.eq_zero_of_mul_const (h := hs1sel)
      (hk := by rw [show ((0 : ZMod p) - 1) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs2 : s2 = 0 := ShiftLeftCore.eq_zero_of_mul_const (h := hs2sel)
      (hk := by rw [show ((0 : ZMod p) - 2) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs3 : s3 = 0 := ShiftLeftCore.eq_zero_of_mul_const (h := hs3sel)
      (hk := by rw [show ((0 : ZMod p) - 3) = -3 from by ring]; exact neg_ne_zero.mpr n3)
    have hs0 : s0 = 1 := by rw [hs1, hs2, hs3] at hssum; linear_combination hssum
    rw [hs0, one_mul] at h00 h01
    exact ⟨by rw [sub_eq_zero.mp h00]; exact hb0, by rw [sub_eq_zero.mp h01]; exact hb1,
      by rw [ha2]; exact hmsb_bound, by rw [ha3]; exact hmsb_bound⟩
  · rw [h4] at hs0sel hs2sel hs3sel
    have hs0 : s0 = 0 := ShiftLeftCore.eq_zero_of_mul_const (h := hs0sel)
      (hk := by rw [show ((1 : ZMod p) - 0) = 1 from by ring]; exact n1)
    have hs2 : s2 = 0 := ShiftLeftCore.eq_zero_of_mul_const (h := hs2sel)
      (hk := by rw [show ((1 : ZMod p) - 2) = -1 from by ring]; exact neg_ne_zero.mpr n1)
    have hs3 : s3 = 0 := ShiftLeftCore.eq_zero_of_mul_const (h := hs3sel)
      (hk := by rw [show ((1 : ZMod p) - 3) = -2 from by ring]; exact neg_ne_zero.mpr n2)
    have hs1 : s1 = 1 := by rw [hs0, hs2, hs3] at hssum; linear_combination hssum
    rw [hs1, one_mul] at h10 h11
    exact ⟨by rw [h10]; exact hz, by rw [sub_eq_zero.mp h11]; exact hb0,
      by rw [ha2]; exact hmsb_bound, by rw [ha3]; exact hmsb_bound⟩

end SP1Clean.ShiftLeftChip
