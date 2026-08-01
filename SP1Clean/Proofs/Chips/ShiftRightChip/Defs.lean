import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Proofs.Operations.ShiftRightOperation.Core
import SP1Clean.Proofs.Chips.ShiftRightChip.Core
import SP1Clean.Proofs.Chips.ShiftRightChip.Populate
import SP1Clean.Proofs.Chips.ShiftRightChip.Dispatch
import SP1Clean.Proofs.Chips.ShiftRightChip.Math
import SP1Clean.Proofs.Chips.ShiftRightChip.Flags
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `ShiftRight` chip row as a `GeneralFormalCircuit`

`SRL`/`SRA`/`SRLW`/`SRAW`: as with `ShiftLeftChip`, no operation-level extraction — the inverted-`v`
power encodings, the `b_msb`/`srw_msb` sign-extension MSB gadgets, the `lower/higher_limb` bit-split,
the `limb_result` reassembly, and the four-variant output placement are inlined into
the generated ShiftRight oracle (`Extracted/ChipOracle/ShiftRight.lean`).

`AssertSpec` / `InteractSpec` capture the structural meaning of SP1's two extracted constraint lists;
the semantic flag-gated RV64 `srl`/`sra`/`srlw`/`sraw` `Spec` is in `Specs/Chip.lean`.
`Faithful/ShiftRightChip.lean` anchors both structural specs.

`main` composes the readers + three `U16MSBOperation` gadgets + the witnessed column block + the
`is_real` gate. Soundness and completeness are proven (honest `Populate` witness closures). -/

namespace SP1Clean.ShiftRightChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The register-read operands the chip decomposes are 64-bit values (received facts from the offline
memory: the writer range-checked them). These are the `rs1`/`rs2` the `Spec` shifts. Lives here (not in
`Formal`) so the per-op `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_memory.prev_value ∧ Word.isU64 input.adapter.op_c_memory.prev_value

/-- **Interaction half** — SP1's `Columns.interactions` byte-range sends (gated by
`gate = is_srl + is_sra + is_srlw + is_sraw`): the shift-amount high bits `< 2^10`, and, per limb, the
`lower_limb` `< 2^bitShift` and `higher_limb` `< 2^(16 - bitShift)` ranges. (Note the lower/higher
widths are swapped versus `ShiftLeftChip`, as the right shift keeps the high bits.) -/
def InteractSpec (cols : Columns (ZMod p)) : Prop :=
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let bitShift : ZMod p := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt : ZMod p := bitShift + b4 * 16 + b5 * 32
  let e84 : ZMod p := (cols.adapter.op_c_memory.prev_value[0] - shamt) * (64 : ZMod p)⁻¹
  let gate : ZMod p := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  (gate ≠ 0 → e84.val < 2 ^ (10 : ZMod p).val) ∧
  (gate ≠ 0 → cols.lower_limb[0].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[0].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.lower_limb[1].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[1].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.lower_limb[2].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[2].val < 2 ^ (16 - bitShift).val) ∧
  (gate ≠ 0 → cols.lower_limb[3].val < 2 ^ bitShift.val) ∧
  (gate ≠ 0 → cols.higher_limb[3].val < 2 ^ (16 - bitShift).val)

/-! ### Folded witness prefix

The eleven consecutive witness allocations are a dangerous value for definitional equality: a
consumer that only wants the later reader or selector-binding constraints can otherwise make Lean
normalize the complete 37-cell bind chain.  This plain `Circuit` helper is a pure repackaging (not a
new AIR subcircuit), so flattening it gives exactly the former witness operations and offsets.  The
three explicit normalization lemmas keep the helper folded until a caller deliberately asks for its
output, length, or operation list. -/

private structure WitnessVars (F : Type) where
  a : Word (Expression F)
  b_msb : Vector (Expression F) 1
  srw_msb : Vector (Expression F) 1
  c_bits : Vector (Expression F) 6
  sra_msb_v0123 : Vector (Expression F) 1
  v : Vector (Expression F) 3
  lower_limb : Word (Expression F)
  higher_limb : Word (Expression F)
  limb_result : Word (Expression F)
  shift_u16 : Word (Expression F)
  flags : Vector (Expression F) 5

@[circuit_norm] private def witnessPrefix (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (WitnessVars (ZMod p)) := fun offset =>
  let a := varFromOffset (Vector · 4) offset
  let b_msb := varFromOffset (Vector · 1) (offset + 4)
  let srw_msb := varFromOffset (Vector · 1) (offset + 4 + 1)
  let c_bits := varFromOffset (Vector · 6) (offset + 4 + 1 + 1)
  let sra_msb_v0123 := varFromOffset (Vector · 1) (offset + 4 + 1 + 1 + 6)
  let v := varFromOffset (Vector · 3) (offset + 4 + 1 + 1 + 6 + 1)
  let lower_limb := varFromOffset (Vector · 4) (offset + 4 + 1 + 1 + 6 + 1 + 3)
  let higher_limb := varFromOffset (Vector · 4) (offset + 4 + 1 + 1 + 6 + 1 + 3 + 4)
  let limb_result := varFromOffset (Vector · 4) (offset + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4)
  let shift_u16 :=
    varFromOffset (Vector · 4) (offset + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4)
  let flags :=
    varFromOffset (Vector · 5) (offset + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
  (⟨a, b_msb, srw_msb, c_bits, sra_msb_v0123, v, lower_limb, higher_limb,
      limb_result, shift_u16, flags⟩,
    [ .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        populateA
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 1 (.native fun env : ProverEnvironment (ZMod p) =>
        #v[bMsb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (hintFlags env.hint)]),
      .witness 1 (.native fun env : ProverEnvironment (ZMod p) =>
        #v[srwMsb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)]),
      .witness 6 (.native fun env : ProverEnvironment (ZMod p) =>
        ShiftLeftChip.cBits (env input.adapter.op_c_memory.prev_value[0])),
      .witness 1 (.native fun env : ProverEnvironment (ZMod p) =>
        #v[sraMsbV0123
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)]),
      .witness 3 (.native fun env : ProverEnvironment (ZMod p) =>
        vPowersInv (env input.adapter.op_c_memory.prev_value[0])),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        lowerLimb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        higherLimb
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        limbResult
          #v[env input.adapter.op_b_memory.prev_value[0],
             env input.adapter.op_b_memory.prev_value[1],
             env input.adapter.op_b_memory.prev_value[2],
             env input.adapter.op_b_memory.prev_value[3]]
          (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 4 (.native fun env : ProverEnvironment (ZMod p) =>
        shiftU16 (env input.adapter.op_c_memory.prev_value[0]) (hintFlags env.hint)),
      .witness 5 (.native fun env : ProverEnvironment (ZMod p) =>
        #v[(hintFlags env.hint)[0], (hintFlags env.hint)[1], (hintFlags env.hint)[2],
           (hintFlags env.hint)[3],
           ((hintFlags env.hint)[2] + (hintFlags env.hint)[3]) * env input.adapter.imm_c]) ])

omit [Fact (2 ^ 17 < p)] in
private theorem witnessListSubcircuitsConsistent
    (offset : ℕ) (c0 : WitgenIR (ZMod p) 4) (c1 c2 : WitgenIR (ZMod p) 1)
    (c3 : WitgenIR (ZMod p) 6) (c4 : WitgenIR (ZMod p) 1)
    (c5 : WitgenIR (ZMod p) 3) (c6 c7 c8 c9 : WitgenIR (ZMod p) 4)
    (c10 : WitgenIR (ZMod p) 5) :
    Operations.SubcircuitsConsistent offset
      [.witness 4 c0, .witness 1 c1, .witness 1 c2, .witness 6 c3,
       .witness 1 c4, .witness 3 c5, .witness 4 c6, .witness 4 c7,
       .witness 4 c8, .witness 4 c9, .witness 5 c10] := by
  simp only [Operations.SubcircuitsConsistent, Operations.forAll, true_and]

omit [Fact (2 ^ 17 < p)] in
private theorem witnessListChannelsLawful
    (c0 : WitgenIR (ZMod p) 4) (c1 c2 : WitgenIR (ZMod p) 1)
    (c3 : WitgenIR (ZMod p) 6) (c4 : WitgenIR (ZMod p) 1)
    (c5 : WitgenIR (ZMod p) 3) (c6 c7 c8 c9 : WitgenIR (ZMod p) 4)
    (c10 : WitgenIR (ZMod p) 5) :
    Operations.ChannelsLawful
      [.witness 4 c0, .witness 1 c1, .witness 1 c2, .witness 6 c3,
       .witness 1 c4, .witness 3 c5, .witness 4 c6, .witness 4 c7,
       .witness 4 c8, .witness 4 c9, .witness 5 c10] [] := by
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
  exact witnessListSubcircuitsConsistent offset _ _ _ _ _ _ _ _ _ _ _

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefixChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).operations offset).ChannelsLawful [] := by
  unfold witnessPrefix Circuit.operations
  exact witnessListChannelsLawful _ _ _ _ _ _ _ _ _ _ _

private instance witnessPrefixExplicit (input : Var Inputs (ZMod p)) :
    ExplicitCircuit (witnessPrefix input) where
  output offset := (witnessPrefix input offset).1
  localLength _ := 37
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
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    witnesses.flags[0] * (7 : Expression (ZMod p)) +
      witnesses.flags[1] * (8 : Expression (ZMod p)) +
      witnesses.flags[2] * (22 : Expression (ZMod p)) +
      witnesses.flags[3] * (23 : Expression (ZMod p)),
    witnesses.a[0], witnesses.a[1], witnesses.a[2], witnesses.a[3]⟩

/-- The post-witness circuit body.  Naming this pure composition keeps the large assertion tail
folded while structural consumers select the early reader boundary. -/
@[circuit_norm] private def postWitness (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) :
    Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let a := witnesses.a
  let b_msb := witnesses.b_msb
  let srw_msb := witnesses.srw_msb
  let c_bits := witnesses.c_bits
  let sra_msb_v0123 := witnesses.sra_msb_v0123
  let v := witnesses.v
  let lower_limb := witnesses.lower_limb
  let higher_limb := witnesses.higher_limb
  let limb_result := witnesses.limb_result
  let shift_u16 := witnesses.shift_u16
  let flags := witnesses.flags
  let is_srl := flags[0]; let is_sra := flags[1]; let is_srlw := flags[2]
  let is_sraw := flags[3]; let is_w_imm := flags[4]
  assertion U16MSBOperation.circuit ⟨input.adapter.op_b_memory.prev_value[3], ⟨b_msb[0]⟩, is_sra⟩
  assertion U16MSBOperation.circuit ⟨input.adapter.op_b_memory.prev_value[1], ⟨b_msb[0]⟩, is_sraw⟩
  assertion U16MSBOperation.circuit ⟨a[1], ⟨srw_msb[0]⟩, is_srlw + is_sraw⟩
  -- `ALUTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ALUTypeReader.circuit (postWitnessReaderInput input witnesses)
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the shift placement, so `isU64 a` (the result range-check, `isU64_sound`) discharges its requirement.
  -- The write access clock is the recombined low clock `+ 4` (matching the reader's op_a `RegisterAccessCols`).
  -- **Gate = the variant flag-sum** `is_srl + is_sra + is_srlw + is_sraw` (= SP1's `is_real`, `sr/mod.rs:335`:
  -- "All interactions are done with multiplicity `is_real`", their sum): the result `a` is range-checked only
  -- when a variant fires (`sum = 1`), so the write's `isU64 a` requirement is sound exactly on those rows.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, is_srl + is_sra + is_srlw + is_sraw⟩
  -- `is_real` boolean gate emitted **inline** (`assertZero`, not `=== 0`) so the `enabled = is_real`
  -- selector is visible to `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table.
  assertZero (input.is_real * (input.is_real - 1))
  -- SP1 has **no** `is_real` column: `is_real` *is* the variant-flag sum (`sr/mod.rs:335`). Our encoding
  -- carries `is_real` as an `Inputs` field, so this assert is the Lean-side glue identifying the two —
  -- exactly `ShiftLeftChip.main`'s `is_real - (is_sll + is_sllw) === 0`. It lets the `RegisterWrite`
  -- write push (composed at the flag sum) inherit the `is_real`-gated `CPUState` clock byte bounds, so
  -- the memory channel's `MemoryMsg.ClkBound` guarantee is derived in-circuit rather than assumed.
  -- This is parent glue rather than an independent proof boundary, so keep it as a shallow inline
  -- assertion. It allocates no witness cell (`localLength` is unchanged at 37) and lives outside
  -- `AssertSpec` (which mirrors only the extracted `Columns.asserts` list over committed columns).
  assertZero (input.is_real - (is_srl + is_sra + is_srlw + is_sraw))
  -- The chip-local assertions retain the exact Rust order.  The four flag booleans and combined
  -- boolean gate stay at parent level: the latter must be visible to `ConstraintsHold.Shallow` to
  -- discharge the off-gate byte requirements.  The remaining 53 assertions form a genuine folded
  -- proof boundary, whose virtual-subcircuit elaboration preserves the flat operation sequence.
  let cols : Var Columns (ZMod p) :=
    ⟨input.state, input.adapter, a, ⟨b_msb[0]⟩, ⟨srw_msb[0]⟩, c_bits, sra_msb_v0123[0],
      v[0], v[1], v[2], lower_limb, higher_limb, limb_result, shift_u16,
      is_srl, is_sra, is_srlw, is_sraw, is_w_imm⟩
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  let gate := is_srl + is_sra + is_srlw + is_sraw
  assertZero (gate * (gate - 1))
  assertion ShiftRightCore.circuit cols
  -- The byte-range pulls (`InteractSpec`), gated by `gate = is_srl+is_sra+is_srlw+is_sraw`.
  let b0 := c_bits[0]; let b1 := c_bits[1]; let b2 := c_bits[2]
  let b3 := c_bits[3]; let b4 := c_bits[4]; let b5 := c_bits[5]
  let bitShift : Expression (ZMod p) := b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8
  let shamt : Expression (ZMod p) := bitShift + b4 * 16 + b5 * 32
  let e84 : Expression (ZMod p) := (input.adapter.op_c_memory.prev_value[0] - shamt) * (64 : ZMod p)⁻¹
  byteChannel.pullIf gate
    (⟨6, e84, Expression.const ((10 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[0], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[0], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[1], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[1], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[2], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[2], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, lower_limb[3], bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf gate
    (⟨6, higher_limb[3], 16 - bitShift, 0⟩ : ByteRow (Expression (ZMod p)))
  return cols

/-- Compose the threaded `CPUState`/`ALUTypeReader` reader blocks and the **three** `U16MSBOperation`
gadgets (`b_msb` on `op_b` limb 3 gated `is_sra` and limb 1 gated `is_sraw`; `srw_msb` on `a[1]` gated
`is_srlw + is_sraw`), witness the shift column block, gate `is_real`, emit the ~58 inline shift
assertions (`AssertSpec`) and the nine byte-range pulls (`InteractSpec`), and assemble the native
`Columns` struct. -/
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
  iterate 3 apply subcircuitMem_bind_right
  apply subcircuitMem_bind_left
  simp only [subcircuitWithAssertion, Circuit.operations,
    Operations.subcircuits_subcircuit, Operations.subcircuits_nil, List.mem_singleton,
    circuit_norm, Nat.add_zero]

/-- The exact ALU-reader input assembled after the folded 37-cell witness prefix.  This is a
structural chip interface used by grounding proofs; it does not duplicate the reader's semantics. -/
def aluReaderInput (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
    var ⟨offset + 32⟩ * 7 + var ⟨offset + 33⟩ * 8 +
      var ⟨offset + 34⟩ * 22 + var ⟨offset + 35⟩ * 23,
    var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩, var ⟨offset + 3⟩⟩

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefixLocalLength_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (witnessPrefix input).localLength offset = 37 := by
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
              ⟨input.adapter.op_b_memory.prev_value[3],
                ⟨witnesses.b_msb[0]⟩, witnesses.flags[1]⟩).operations
                  offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((U16MSBOperation.main
              ⟨input.adapter.op_b_memory.prev_value[1],
                ⟨witnesses.b_msb[0]⟩, witnesses.flags[3]⟩).operations
                  offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((U16MSBOperation.main
              ⟨witnesses.a[1], ⟨witnesses.srw_msb[0]⟩,
                witnesses.flags[2] + witnesses.flags[3]⟩).operations
                  offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Readers.ALUTypeReader.main
              (postWitnessReaderInput input witnesses)).operations offset).constraints) ∧
       (ProvableStruct.eval env input).is_real *
          ((ProvableStruct.eval env input).is_real - 1) = 0 ∧
       (ProvableStruct.eval env input).is_real -
          (Expression.eval env witnesses.flags[0] +
            Expression.eval env witnesses.flags[1] +
            Expression.eval env witnesses.flags[2] +
            Expression.eval env witnesses.flags[3]) = 0 ∧
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
            ((Gadgets.Equality.main (M := field)
              (witnesses.flags[2] * (witnesses.flags[2] - 1),
                0)).operations offset).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (witnesses.flags[3] * (witnesses.flags[3] - 1),
                0)).operations offset).constraints) ∧
       Expression.eval env
          ((witnesses.flags[0] + witnesses.flags[1] +
              witnesses.flags[2] + witnesses.flags[3]) *
            (witnesses.flags[0] + witnesses.flags[1] +
              witnesses.flags[2] + witnesses.flags[3] - 1)) = 0 ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((ShiftRightCore.main
              ((postWitness input witnesses).output offset)).operations
                offset).constraints)) := by
  simp only [postWitness, circuit_norm, List.map_append,
    List.forall_append, List.forall_cons,
    constraints_formalAssertion, constraints_generalFormalCircuit,
    U16MSBOperation.circuit, Readers.ALUTypeReader.circuit,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    ShiftRightCore.circuit]

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefix_flag0 (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).output offset).flags[0] =
      var { index := offset + 32 } := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefix_flag1 (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).output offset).flags[1] =
      var { index := offset + 33 } := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefix_flag2 (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).output offset).flags[2] =
      var { index := offset + 34 } := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem witnessPrefix_flag3 (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((witnessPrefix input).output offset).flags[3] =
      var { index := offset + 35 } := by
  rfl

private theorem cpuCircuitLocalLength_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Readers.CPUState.circuit
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
        8, input.is_real⟩).localLength offset = 0 := by
  simp only [circuit_norm]

/-- Channel projections of the whole chip can discard the witness-only prefix before inspecting
the post-witness body.  This is the structural normalization boundary for consumers that must not
force the 37-cell witness generator chain while merely classifying interactions. -/
theorem interactionsWith_main_decompose (input : Var Inputs (ZMod p)) (offset : ℕ)
    (channel : RawChannel (ZMod p)) :
    ((main input).operations offset).interactionsWith channel =
      ((Readers.CPUState.circuit
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).interactionsWith channel ++
      ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 37)).interactionsWith channel := by
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
    Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [Operations.interactionsWith_append,
    ShiftRightCore.interactionsWith_subcircuit_eq_nil,
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

/-- `CPUState` contributes the whole chip's exact State-channel interaction list; the folded
post-witness body has no State interaction. -/
theorem interactionsWith_main_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (Readers.CPUState.stateInteractions
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).map ChannelInteraction.toRaw := by
  rw [interactionsWith_main_decompose, postWitness_stateInteractions_eq]
  simp only [Circuit.operations, subcircuitWithAssertion,
    Readers.CPUState.interactionsWith_state_subcircuit,
    Operations.interactionsWith_nil, List.append_nil]

/-- ShiftRight's State pair written directly over the chip inputs. -/
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

/-- Direct-input form of ShiftRight's exact State projection. -/
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

/-- The Program-fetch opcode committed by the witnessed variant flags (cells `offset+32..35`). -/
def exposedOpcode (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 32⟩ * 7 + var ⟨offset + 33⟩ * 8 +
    var ⟨offset + 34⟩ * 22 + var ⟨offset + 35⟩ * 23

/-- The `RegisterWrite` gate committed by the witnessed variant flags (cells `offset+32..35`). -/
def exposedWriteGate (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset + 32⟩ + var ⟨offset + 33⟩ + var ⟨offset + 34⟩ + var ⟨offset + 35⟩

/-- Exact Byte-channel list emitted by ShiftRight's native composition. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let a : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  let cBits : Vector (Expression (ZMod p)) 6 :=
    Vector.mapRange 6 fun i => var { index := offset + 6 + i }
  let lowerLimb : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 16 + i }
  let higherLimb : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 20 + i }
  let bMsb : Expression (ZMod p) := var { index := offset + 4 }
  let srwMsb : Expression (ZMod p) := var { index := offset + 5 }
  let isSra : Expression (ZMod p) := var { index := offset + 33 }
  let isSrlw : Expression (ZMod p) := var { index := offset + 34 }
  let isSraw : Expression (ZMod p) := var { index := offset + 35 }
  let gate : Expression (ZMod p) := exposedWriteGate offset
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
    byteChannel.pulledIf isSra
      ⟨6, (2 : Expression (ZMod p)) *
          input.adapter.op_b_memory.prev_value[3] - bMsb * 65536,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf isSraw
      ⟨6, (2 : Expression (ZMod p)) *
          input.adapter.op_b_memory.prev_value[1] - bMsb * 65536,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (isSrlw + isSraw)
      ⟨6, (2 : Expression (ZMod p)) * a[1] - srwMsb * 65536,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
        (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
        (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨6, input.adapter.op_c_memory.access_timestamp.diff_low_limb,
        Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨3, 0,
        (clkLow + 2 -
          input.adapter.op_c_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, shiftHigh, Expression.const ((10 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[0], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[0], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[1], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[1], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[2], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[2], 16 - bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, lowerLimb[3], bitShift, 0⟩,
    byteChannel.pulledIf gate
      ⟨6, higherLimb[3], 16 - bitShift, 0⟩ ]

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
    witnesses.flags[0] + witnesses.flags[1] +
      witnesses.flags[2] + witnesses.flags[3]
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
      ⟨6, witnesses.lower_limb[0], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[0], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[1], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[1], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[2], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[2], 16 - bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.lower_limb[3], bitShift, 0⟩).toRaw,
    (byteChannel.pulledIf gate
      ⟨6, witnesses.higher_limb[3], 16 - bitShift, 0⟩).toRaw ]

private theorem postWitness_byteInteractions_eq
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p))
    (offset : ℕ) :
    ((postWitness input witnesses).operations offset).interactionsWith
        byteChannel.toRaw =
      u16MsbByteInteractionsRaw
          ⟨input.adapter.op_b_memory.prev_value[3],
            ⟨witnesses.b_msb[0]⟩, witnesses.flags[1]⟩ ++
        u16MsbByteInteractionsRaw
          ⟨input.adapter.op_b_memory.prev_value[1],
            ⟨witnesses.b_msb[0]⟩, witnesses.flags[3]⟩ ++
        u16MsbByteInteractionsRaw
          ⟨witnesses.a[1], ⟨witnesses.srw_msb[0]⟩,
            witnesses.flags[2] + witnesses.flags[3]⟩ ++
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
    ShiftRightCore.interactionsWith_subcircuit_eq_nil,
    heq,
    Operations.interactionsWith_assert,
    Operations.interactionsWith_nil,
    List.nil_append]
  simp only [shiftRangeByteInteractionsRaw, circuit_norm,
    List.cons_append, List.nil_append]

/-- The exact Byte interaction list of the whole folded ShiftRight chip. -/
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
    Circuit.output, exposedWriteGate,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange,
    List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Nat.reduceAdd, Nat.add_assoc]

/-- ShiftRight's exact Memory-channel interaction list.  This structural definition lives beside
`main`; the semantic `circuit` bundle merely exposes it. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (exposedWriteGate offset)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + i }⟩ ]

private theorem postWitness_memoryInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 37)).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  unfold postWitness
  simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
    subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
    Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [Soundness.aluTypeReader_memoryInteractions_subcircuit,
    Soundness.registerWrite_memoryInteractions_subcircuit,
    ShiftRightCore.interactionsWith_subcircuit_eq_nil,
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
  simp only [exposedMemoryInteractions, exposedWriteGate, witnessPrefix, Circuit.output,
    Vector.mapRange, List.map_cons, List.map_nil]
  rfl

/-- The exact Memory interaction list of the whole folded ShiftRight chip. -/
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

/-- The exact Program fetch emitted by ShiftRight's ALU adapter. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], exposedOpcode offset,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
       input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

private theorem postWitness_programInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 37)).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input offset).map ChannelInteraction.toRaw := by
  unfold postWitness
  simp only [Circuit.bind_operations_eq, Circuit.pure_operations_eq, Circuit.operations,
    subcircuitWithAssertion, assertion, assertZero, HasAssertEq.assert_eq,
    Expression.assertEquals, Channel.pullIf, Circuit.localLength, Operations.localLength,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    U16MSBOperation.circuit_localLength, Readers.ALUTypeReader.circuit_localLength,
    Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [Operations.interactionsWith_append,
    Soundness.aluTypeReader_programInteractions_subcircuit,
    ShiftRightCore.interactionsWith_subcircuit_eq_nil,
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
  simp only [postWitnessReaderInput, exposedProgramInteractions, exposedOpcode,
    witnessPrefix, Circuit.output, List.map_cons, List.map_nil]
  rfl

/-- The exact Program interaction of the whole folded ShiftRight chip. -/
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
    ⟨offset + 37, Readers.ALUTypeReader.circuit.toSubcircuit (offset + 37)
      (aluReaderInput input offset)⟩ ∈ ((main input).operations offset).subcircuits := by
  unfold main
  apply subcircuitMem_bind_right
  apply subcircuitMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    postWitnessReaderInput_witnessPrefixOutput, Nat.add_zero] using
    aluReader_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

private theorem selectorLink_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    input.is_real -
        (witnesses.flags[0] + witnesses.flags[1] +
          witnesses.flags[2] + witnesses.flags[3]) ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 6 apply constraintMem_bind_right
  apply constraintMem_bind_left
  simp only [assertZero, Circuit.operations, Operations.constraints_assert,
    Operations.constraints_nil, List.mem_singleton]

private theorem srlBool_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    witnesses.flags[0] * (witnesses.flags[0] - 1) - 0 ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 7 apply constraintMem_bind_right
  apply constraintMem_bind_left
  exact equalityAssertionConstraint_mem
    (witnesses.flags[0] * (witnesses.flags[0] - 1))
    (0 : Expression (ZMod p)) _

private theorem sraBool_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    witnesses.flags[1] * (witnesses.flags[1] - 1) - 0 ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 8 apply constraintMem_bind_right
  apply constraintMem_bind_left
  exact equalityAssertionConstraint_mem
    (witnesses.flags[1] * (witnesses.flags[1] - 1))
    (0 : Expression (ZMod p)) _

private theorem srlwBool_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    witnesses.flags[2] * (witnesses.flags[2] - 1) - 0 ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 9 apply constraintMem_bind_right
  apply constraintMem_bind_left
  exact equalityAssertionConstraint_mem
    (witnesses.flags[2] * (witnesses.flags[2] - 1))
    (0 : Expression (ZMod p)) _

private theorem srawBool_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    witnesses.flags[3] * (witnesses.flags[3] - 1) - 0 ∈
      ((postWitness input witnesses).operations offset).constraints := by
  unfold postWitness
  iterate 10 apply constraintMem_bind_right
  apply constraintMem_bind_left
  exact equalityAssertionConstraint_mem
    (witnesses.flags[3] * (witnesses.flags[3] - 1))
    (0 : Expression (ZMod p)) _

private theorem core_mem_postWitness
    (input : Var Inputs (ZMod p)) (witnesses : WitnessVars (ZMod p)) (offset : ℕ) :
    ⟨offset, ShiftRightCore.circuit.toSubcircuit offset
      ((postWitness input witnesses).output offset)⟩ ∈
      ((postWitness input witnesses).operations offset).subcircuits := by
  unfold postWitness
  iterate 7 apply subcircuitMem_bind_right
  iterate 4 apply subcircuitMem_bind_right_zero (hlen := equalityAssertionLocalLength_eq _ _ _)
  apply subcircuitMem_bind_right_zero (hlen := by rfl)
  apply subcircuitMem_bind_left
  simp only [assertion, Circuit.operations, Operations.subcircuits_subcircuit,
    Operations.subcircuits_nil, List.mem_singleton, circuit_norm, Nat.add_zero]

/-- The exact row passed to the folded arithmetic core after the witness prefix. -/
def coreInput (input : Var Inputs (ZMod p)) (offset : ℕ) :
    Var Columns (ZMod p) :=
  (postWitness input ((witnessPrefix input).output offset)).output (offset + 37)

@[circuit_norm] theorem coreInput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    coreInput input offset =
      (⟨input.state, input.adapter,
        varFromOffset (Vector · 4) offset,
        ⟨var { index := offset + 4 }⟩, ⟨var { index := offset + 5 }⟩,
        varFromOffset (Vector · 6) (offset + 6),
        var { index := offset + 12 },
        var { index := offset + 13 }, var { index := offset + 14 },
        var { index := offset + 15 },
        varFromOffset (Vector · 4) (offset + 16),
        varFromOffset (Vector · 4) (offset + 20),
        varFromOffset (Vector · 4) (offset + 24),
        varFromOffset (Vector · 4) (offset + 28),
        var { index := offset + 32 }, var { index := offset + 33 },
        var { index := offset + 34 }, var { index := offset + 35 },
        var { index := offset + 36 }⟩ : Var Columns (ZMod p)) := rfl

private theorem constraints_main_bind_decompose
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).constraints =
      ((Readers.CPUState.circuit
        ⟨input.state,
          #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).constraints ++
      ((postWitness input ((witnessPrefix input).output offset)).operations
        (offset + 37)).constraints := by
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

/-- Exact folded decomposition of every native ShiftRight assertion. The 37-cell witness generator
stays opaque while the canonical readers, three MSB checks, selector gates, and folded 53-assert
arithmetic tail remain visible as complete blocks. -/
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
              ⟨input.adapter.op_b_memory.prev_value[3],
                ⟨var { index := offset + 4 }⟩,
                var { index := offset + 33 }⟩).operations
                  (offset + 37)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((U16MSBOperation.main
              ⟨input.adapter.op_b_memory.prev_value[1],
                ⟨var { index := offset + 4 }⟩,
                var { index := offset + 35 }⟩).operations
                  (offset + 37)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((U16MSBOperation.main
              ⟨(varFromOffset (Vector · 4) offset)[1],
                ⟨var { index := offset + 5 }⟩,
                var { index := offset + 34 } +
                  var { index := offset + 35 }⟩).operations
                  (offset + 37)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Readers.ALUTypeReader.main
              (aluReaderInput input offset)).operations
                (offset + 37)).constraints) ∧
       (ProvableStruct.eval env input).is_real *
          ((ProvableStruct.eval env input).is_real - 1) = 0 ∧
       (ProvableStruct.eval env input).is_real -
          (Expression.eval env (var { index := offset + 32 }) +
            Expression.eval env (var { index := offset + 33 }) +
            Expression.eval env (var { index := offset + 34 }) +
            Expression.eval env (var { index := offset + 35 })) = 0 ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (var { index := offset + 32 } *
                  (var { index := offset + 32 } - 1),
                0)).operations (offset + 37)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (var { index := offset + 33 } *
                  (var { index := offset + 33 } - 1),
                0)).operations (offset + 37)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (var { index := offset + 34 } *
                  (var { index := offset + 34 } - 1),
                0)).operations (offset + 37)).constraints) ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((Gadgets.Equality.main (M := field)
              (var { index := offset + 35 } *
                  (var { index := offset + 35 } - 1),
                0)).operations (offset + 37)).constraints) ∧
       (Expression.eval env (var { index := offset + 32 }) +
          Expression.eval env (var { index := offset + 33 }) +
          Expression.eval env (var { index := offset + 34 }) +
          Expression.eval env (var { index := offset + 35 })) *
            (Expression.eval env (var { index := offset + 32 }) +
              Expression.eval env (var { index := offset + 33 }) +
              Expression.eval env (var { index := offset + 34 }) +
              Expression.eval env (var { index := offset + 35 }) - 1) = 0 ∧
       List.Forall (· = 0)
          (List.map (Expression.eval env)
            ((ShiftRightCore.main
              (coreInput input offset)).operations
                (offset + 37)).constraints)) := by
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

/-- The Lean-side `is_real`/variant-sum glue is retained in the whole chip. -/
theorem selectorLink_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    input.is_real -
        (var { index := offset + 32 } + var { index := offset + 33 } +
          var { index := offset + 34 } + var { index := offset + 35 }) ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag0, witnessPrefix_flag1,
    witnessPrefix_flag2, witnessPrefix_flag3] using
    selectorLink_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

/-- The `is_srl` boolean assertion is retained at the post-witness offset. -/
theorem srlBool_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 32 } * (var { index := offset + 32 } - 1) - 0 ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag0] using
    srlBool_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

/-- The `is_sra` boolean assertion is retained at the post-witness offset. -/
theorem sraBool_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 33 } * (var { index := offset + 33 } - 1) - 0 ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag1] using
    sraBool_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

/-- The `is_srlw` boolean assertion is retained at the post-witness offset. -/
theorem srlwBool_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 34 } * (var { index := offset + 34 } - 1) - 0 ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag2] using
    srlwBool_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

/-- The `is_sraw` boolean assertion is retained at the post-witness offset. -/
theorem srawBool_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 35 } * (var { index := offset + 35 } - 1) - 0 ∈
      ((main input).operations offset).constraints := by
  unfold main
  apply constraintMem_bind_right
  apply constraintMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    Nat.add_zero, witnessPrefix_flag3] using
    srawBool_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

/-- The folded arithmetic core is retained at the post-witness offset. -/
theorem core_mem_subcircuits (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 37,
      ShiftRightCore.circuit.toSubcircuit (offset + 37)
        (coreInput input offset)⟩ ∈
      ((main input).operations offset).subcircuits := by
  unfold main
  apply subcircuitMem_bind_right
  apply subcircuitMem_bind_right
  simpa only [cpuCircuitLocalLength_eq, witnessPrefixLocalLength_eq,
    coreInput, Nat.add_zero] using
    core_mem_postWitness input ((witnessPrefix input).output offset) (offset + 37)

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
    (elaborated (p := p)).localLength x = 37 := rfl

/-- The completed ShiftRight row, exposed without unfolding the folded witness circuit. -/
@[circuit_norm] lemma directOutput_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        varFromOffset (Vector · 4) offset,
        ⟨var { index := offset + 4 }⟩, ⟨var { index := offset + 5 }⟩,
        varFromOffset (Vector · 6) (offset + 6),
        var { index := offset + 12 },
        var { index := offset + 13 }, var { index := offset + 14 },
        var { index := offset + 15 },
        varFromOffset (Vector · 4) (offset + 16),
        varFromOffset (Vector · 4) (offset + 20),
        varFromOffset (Vector · 4) (offset + 24),
        varFromOffset (Vector · 4) (offset + 28),
        var { index := offset + 32 }, var { index := offset + 33 },
        var { index := offset + 34 }, var { index := offset + 35 },
        var { index := offset + 36 }⟩ : Var Columns (ZMod p)) := rfl

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
         a := Eval.eval env cols.a, b_msb := Eval.eval env cols.b_msb,
         srw_msb := Eval.eval env cols.srw_msb, c_bits := Eval.eval env cols.c_bits,
         sra_msb_v0123 := Eval.eval env cols.sra_msb_v0123,
         v_0123 := Eval.eval env cols.v_0123, v_012 := Eval.eval env cols.v_012,
         v_01 := Eval.eval env cols.v_01,
         lower_limb := Eval.eval env cols.lower_limb,
         higher_limb := Eval.eval env cols.higher_limb,
         limb_result := Eval.eval env cols.limb_result,
         shift_u16 := Eval.eval env cols.shift_u16,
         is_srl := Eval.eval env cols.is_srl, is_sra := Eval.eval env cols.is_sra,
         is_srlw := Eval.eval env cols.is_srlw, is_sraw := Eval.eval env cols.is_sraw,
         is_w_imm := Eval.eval env cols.is_w_imm } : Columns F) := by
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
      Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
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
      Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
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
      Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
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
      Readers.RegisterWrite.circuit_localLength, ShiftRightCore.circuit_localLength,
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
    ((witnessPrefix input).output offset) (offset + 37)
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
          ((postWitness input ((witnessPrefix input).output offset)).operations (offset + 37)) := by
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

/-! ## Pure-field result-word range (`isU64 a`) helpers for the op_a `RegisterWrite` push

The W11 Option-B memory flip composes `RegisterWrite` *after* the shift placement; its push owes
`isU64` of the placed result word `a`. These pure-field lemmas range-check the placed limbs from the
`e14`/`e13`-gated placement asserts and the per-limb atomic bounds (each `a_i` is `0`, a `limb_result`
entry, a sign-fill, or `msb·65535`). Shared by `isU64_sound` and all four `Soundness/<Op>.lean` tails. -/

set_option linter.unusedSectionVars false in
/-- **SRL/SRA result range** (`e14 = is_srl + is_sra = 1`). From the one-hot byte-shift selectors
(`su_k` boolean, `Σ su_k = 1`), the 16 `e14`-gated placement asserts, and the per-limb atomic bounds
(`lr0`/`lr1`/`lr2`, the sign-fill `lr3f = limb_result[3] + sraFill`, and `bmsbFill`), every result limb
is a `u16`. -/
lemma srl_sra_a_isU64 {e14 a0 a1 a2 a3 su0 su1 su2 su3 lr0 lr1 lr2 lr3f bmsbFill : ZMod p}
    (he14 : e14 = 1)
    (hsu0b : su0 = 0 ∨ su0 = 1) (hsu1b : su1 = 0 ∨ su1 = 1) (hsu2b : su2 = 0 ∨ su2 = 1)
    (hsum : su0 + su1 + su2 + su3 = 1)
    (hb0 : lr0.val < 2 ^ 16) (hb1 : lr1.val < 2 ^ 16) (hb2 : lr2.val < 2 ^ 16)
    (hbf : lr3f.val < 2 ^ 16) (hbm : bmsbFill.val < 2 ^ 16)
    (h0 : e14 * (su0 * (a0 - lr0)) = 0) (h1 : e14 * (su0 * (a1 - lr1)) = 0)
    (h2 : e14 * (su0 * (a2 - lr2)) = 0) (h3 : e14 * (su0 * (a3 - lr3f)) = 0)
    (h4 : e14 * (su1 * (a0 - lr1)) = 0) (h5 : e14 * (su1 * (a1 - lr2)) = 0)
    (h6 : e14 * (su1 * (a2 - lr3f)) = 0) (h7 : e14 * (su1 * (a3 - bmsbFill)) = 0)
    (h8 : e14 * (su2 * (a0 - lr2)) = 0) (h9 : e14 * (su2 * (a1 - lr3f)) = 0)
    (h10 : e14 * (su2 * (a2 - bmsbFill)) = 0) (h11 : e14 * (su2 * (a3 - bmsbFill)) = 0)
    (h12 : e14 * (su3 * (a0 - lr3f)) = 0) (h13 : e14 * (su3 * (a1 - bmsbFill)) = 0)
    (h14 : e14 * (su3 * (a2 - bmsbFill)) = 0) (h15 : e14 * (su3 * (a3 - bmsbFill)) = 0) :
    a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 ∧ a2.val < 2 ^ 16 ∧ a3.val < 2 ^ 16 := by
  subst he14
  simp only [one_mul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  rcases hsu0b with e0 | e0
  · rcases hsu1b with e1 | e1
    · rcases hsu2b with e2 | e2
      · have e3 : su3 = 1 := by rw [e0, e1, e2] at hsum; linear_combination hsum
        rw [e3, one_mul] at h12 h13 h14 h15
        exact ⟨by rw [sub_eq_zero.mp h12]; exact hbf, by rw [sub_eq_zero.mp h13]; exact hbm,
          by rw [sub_eq_zero.mp h14]; exact hbm, by rw [sub_eq_zero.mp h15]; exact hbm⟩
      · rw [e2, one_mul] at h8 h9 h10 h11
        exact ⟨by rw [sub_eq_zero.mp h8]; exact hb2, by rw [sub_eq_zero.mp h9]; exact hbf,
          by rw [sub_eq_zero.mp h10]; exact hbm, by rw [sub_eq_zero.mp h11]; exact hbm⟩
    · rw [e1, one_mul] at h4 h5 h6 h7
      exact ⟨by rw [sub_eq_zero.mp h4]; exact hb1, by rw [sub_eq_zero.mp h5]; exact hb2,
        by rw [sub_eq_zero.mp h6]; exact hbf, by rw [sub_eq_zero.mp h7]; exact hbm⟩
  · rw [e0, one_mul] at h0 h1 h2 h3
    exact ⟨by rw [sub_eq_zero.mp h0]; exact hb0, by rw [sub_eq_zero.mp h1]; exact hb1,
      by rw [sub_eq_zero.mp h2]; exact hb2, by rw [sub_eq_zero.mp h3]; exact hbf⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **SRLW/SRAW result range** (`e13 = is_srlw + is_sraw = 1`). The byte shift is `cb4 ∈ {0,1}` (so only
`su0`/`su1` are hot); `a0`/`a1` come from the low-two placement asserts (`lr0`, the sign-fill `lr1f`,
`bmsbFill`); `a2 = a3 = srwmsb·65535` (the de-gated word sign fill). The `srw_msb` bit is supplied by
`hsrw_of` (the `U16MSB` gadget, which needs the just-derived `a1 < 2^16`). Every result limb is a `u16`. -/
lemma srlw_sraw_a_isU64 {e13 cb4 a0 a1 a2 a3 su0 su1 su2 su3 lr0 lr1f bmsbFill srwmsb : ZMod p}
    (he13 : e13 = 1) (hcb4 : cb4 = 0 ∨ cb4 = 1)
    (hs0sel : su0 * (cb4 - 0) = 0) (hs1sel : su1 * (cb4 - 1) = 0)
    (hs2sel : su2 * (cb4 - 2) = 0) (hs3sel : su3 * (cb4 - 3) = 0)
    (hsum : su0 + su1 + su2 + su3 = 1)
    (hb0 : lr0.val < 2 ^ 16) (hb1f : lr1f.val < 2 ^ 16) (hbm : bmsbFill.val < 2 ^ 16)
    (hsrw_of : a1.val < 2 ^ 16 → srwmsb = 0 ∨ srwmsb = 1)
    (hw0 : e13 * (su0 * (a0 - lr0)) = 0) (hw1 : e13 * (su0 * (a1 - lr1f)) = 0)
    (hw2 : e13 * (su1 * (a0 - lr1f)) = 0) (hw3 : e13 * (su1 * (a1 - bmsbFill)) = 0)
    (hw4 : e13 * (a2 - srwmsb * 65535) = 0) (hw5 : e13 * (a3 - srwmsb * 65535) = 0) :
    a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 ∧ a2.val < 2 ^ 16 ∧ a3.val < 2 ^ 16 := by
  subst he13
  simp only [one_mul] at hw0 hw1 hw2 hw3 hw4 hw5
  have ha2 : a2 = srwmsb * 65535 := sub_eq_zero.mp hw4
  have ha3 : a3 = srwmsb * 65535 := sub_eq_zero.mp hw5
  have hp : 2 ^ 17 < p := Fact.out
  have hv2 : (2 : ZMod p).val = 2 := val_2_zmod_p
  have hv3 : (3 : ZMod p).val = 3 := val_3_zmod_p
  have n2 : (2 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv2; omega
  have n3 : (3 : ZMod p) ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hv3; omega
  have key : a0.val < 2 ^ 16 ∧ a1.val < 2 ^ 16 := by
    rcases hcb4 with h4 | h4
    · rw [h4] at hs1sel hs2sel hs3sel
      have hs1 : su1 = 0 := by
        have hh := hs1sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs2 : su2 = 0 := by
        have hh := hs2sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs3 : su3 = 0 := by
        have hh := hs3sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n3])
      have hs0 : su0 = 1 := by rw [hs1, hs2, hs3] at hsum; linear_combination hsum
      rw [hs0, one_mul] at hw0 hw1
      exact ⟨by rw [sub_eq_zero.mp hw0]; exact hb0, by rw [sub_eq_zero.mp hw1]; exact hb1f⟩
    · rw [h4] at hs0sel hs2sel hs3sel
      have hs0 : su0 = 0 := by
        have hh := hs0sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs2 : su2 = 0 := by
        have hh := hs2sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs3 : su3 = 0 := by
        have hh := hs3sel; simp at hh; first | exact hh | exact hh.resolve_right (by norm_num [n2])
      have hs1 : su1 = 1 := by rw [hs0, hs2, hs3] at hsum; linear_combination hsum
      rw [hs1, one_mul] at hw2 hw3
      exact ⟨by rw [sub_eq_zero.mp hw2]; exact hb1f, by rw [sub_eq_zero.mp hw3]; exact hbm⟩
  obtain ⟨ha0, ha1⟩ := key
  have hsrwfill : (srwmsb * 65535).val < 2 ^ 16 := by
    rcases hsrw_of ha1 with h | h <;> rw [h]
    · rw [zero_mul, ZMod.val_zero]; norm_num
    · rw [one_mul, show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]; norm_num
  exact ⟨ha0, ha1, by rw [ha2]; exact hsrwfill, by rw [ha3]; exact hsrwfill⟩

/-- **Result range-check.** On a variant-active row (`sum = is_srl + is_sra + is_srlw + is_sraw = 1`, SP1's
`is_real`, `sr/mod.rs:335`) the committed result word `cols.a` is `U64`. This is the obligation the op_a
write `RegisterWrite` push owes (Option B memory flip): the shift result is range-checked exactly when a
variant fires, so the push's `isU64 a` requirement is sound on those rows. Proved as a standalone
`Soundness` (over the same `main`) so the four split per-variant `Soundness/<Op>.lean` files can each
discharge their `RegisterWrite` requirement via `(isU64_sound …).1` without re-deriving the bound. -/
def IsU64Spec (_ : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1 → Word.isU64 cols.a

/-- **Result range-check (callable lemma).** On a variant-active row
(`is_srl + is_sra + is_srlw + is_sraw = 1`, SP1's `is_real`) the committed result word `cols.a` is `U64`
— the obligation the op_a write `RegisterWrite` push owes (W11 Option B memory flip). Packaged as a plain
lemma over the destructured `h_holds` hypotheses so each split per-variant `Soundness/<Op>.lean` can
discharge its `RegisterWrite` requirement by applying it, mirroring green `ShiftLeftChip`'s `sll_a_isU64`. -/
lemma resultA_isU64
    (i₀ : ℕ) (env : Environment (ZMod p))
    {input_var_adapter_op_b_memory_prev_value : Word (Expression (ZMod p))}
    {input_adapter_op_b_memory_prev_value : Word (ZMod p)}
    (h_obmap : Vector.map (Expression.eval env) input_var_adapter_op_b_memory_prev_value = input_adapter_op_b_memory_prev_value)
    (h_rs1U : input_adapter_op_b_memory_prev_value.isU64)
    (h_msb1 : U16MSBOperation.circuit.Assumptions { a := Expression.eval env input_var_adapter_op_b_memory_prev_value[3], cols := { msb := env.get (i₀ + 4) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) } → U16MSBOperation.circuit.Spec { a := Expression.eval env input_var_adapter_op_b_memory_prev_value[3], cols := { msb := env.get (i₀ + 4) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) })
    (h_msb3 : U16MSBOperation.circuit.Assumptions { a := env.get (i₀ + 1), cols := { msb := env.get (i₀ + 4 + 1) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) } → U16MSBOperation.circuit.Spec { a := env.get (i₀ + 1), cols := { msb := env.get (i₀ + 4 + 1) }, is_real := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) })
    (h_srl_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + -1) = 0)
    (h_sra_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + -1) = 0)
    (h_srlw_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + -1) = 0)
    (h_sraw_b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) + -1) = 0)
    (h_sum_b : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) + -1) = 0)
    (h_b0 : env.get (i₀ + 4 + 1 + 1) * (env.get (i₀ + 4 + 1 + 1) + -1) = 0)
    (h_b1 : env.get (i₀ + 4 + 1 + 1 + 1) * (env.get (i₀ + 4 + 1 + 1 + 1) + -1) = 0)
    (h_b2 : env.get (i₀ + 4 + 1 + 1 + 2) * (env.get (i₀ + 4 + 1 + 1 + 2) + -1) = 0)
    (h_b3 : env.get (i₀ + 4 + 1 + 1 + 3) * (env.get (i₀ + 4 + 1 + 1 + 3) + -1) = 0)
    (h_b4 : env.get (i₀ + 4 + 1 + 1 + 4) * (env.get (i₀ + 4 + 1 + 1 + 4) + -1) = 0)
    (h_s0w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1))) = 0)
    (h_s0b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) + -1) = 0)
    (h_s1w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -1) = 0)
    (h_s1b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) + -1) = 0)
    (h_s2w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -2) = 0)
    (h_s2b : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) + -1) = 0)
    (h_s3w : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 4 + 1 + 1 + 4) + env.get (i₀ + 4 + 1 + 1 + 5) * 2 * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -3) = 0)
    (h_onehot : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) + -1) = 0)
    (h_v01 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) + -((1 + -env.get (i₀ + 4 + 1 + 1) + 1) * 2 * ((1 + -env.get (i₀ + 4 + 1 + 1 + 1)) * 3 + 1)) = 0)
    (h_v012 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 2)) * 15 + 1)) = 0)
    (h_v0123 : env.get (i₀ + 4 + 1 + 1 + 6 + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 3)) * 255 + 1)) = 0)
    (h_split2 : input_adapter_op_b_memory_prev_value[2] * env.get (i₀ + 4 + 1 + 1 + 6 + 1) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) * 65536 + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_lr3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) = 0)
    (h_smv : env.get (i₀ + 4 + 1 + 1 + 6) + -(env.get (i₀ + 4) * env.get (i₀ + 4 + 1 + 1 + 6 + 1)) = 0)
    (h_o0 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4))) = 0)
    (h_o1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 1) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1))) = 0)
    (h_o2 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 2) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2))) = 0)
    (h_o3 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 3) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o4 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1))) = 0)
    (h_o5 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 1) + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2))) = 0)
    (h_o6 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 2) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o7 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 3) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o8 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2))) = 0)
    (h_o9 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o10 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 2) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o11 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 3) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o12 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get i₀ + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_o13 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 1) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o14 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 2) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_o15 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 3) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_w0 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get i₀ + -env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4))) = 0)
    (h_w1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 1) + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_w2 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get i₀ + -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) + (env.get (i₀ + 4) * 65536 + -env.get (i₀ + 4 + 1 + 1 + 6))))) = 0)
    (h_w3 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 1) + -(env.get (i₀ + 4) * 65535))) = 0)
    (h_w4 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 2) + -(env.get (i₀ + 4 + 1) * 65535)) = 0)
    (h_w5 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) * (env.get (i₀ + 3) + -(env.get (i₀ + 4 + 1) * 65535)) = 0)
    (h_byte1 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte2 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    (h_byte3 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte4 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    (h_byte5 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte6 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    (h_byte7 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3), b := env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8, c := 0 } env.data)
    (h_byte8 : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 → byteChannel.Guarantees { opcode := 6, a := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3), b := 16 + -(env.get (i₀ + 4 + 1 + 1) * 1 + env.get (i₀ + 4 + 1 + 1 + 1) * 2 + env.get (i₀ + 4 + 1 + 1 + 2) * 4 + env.get (i₀ + 4 + 1 + 1 + 3) * 8), c := 0 } env.data)
    :
    env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 →
      Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + i }) : Word (ZMod p)) := by
  -- Reduce the committed result column `cols.a` to its four `env.get`s.
  have hcolsa : (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + i }) : Word (ZMod p))
      = #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), env.get (i₀ + 3)] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    interval_cases i <;> rfl
  -- **The result range-check.** On a variant-active row the four output limbs are each `< 2^16`. Proved
  -- once here; `spec`/`regwriteA` lift it to `isU64 cols.a` and `msb3A` reads off the `a[1]` bound.
  have hbounds :
      env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 →
        (env.get i₀).val < 2 ^ 16 ∧ (env.get (i₀ + 1)).val < 2 ^ 16 ∧
          (env.get (i₀ + 2)).val < 2 ^ 16 ∧ (env.get (i₀ + 3)).val < 2 ^ 16 := by
    intro hsum1
    -- Normalize the hand-written `x * (x + -1) = 0` boolean-gate parameters to the `- 1` form
    -- `bool_of_mul_pred` now expects (Lean 4.30 `circuit_norm` canonicalized subtraction form).
    simp only [← sub_eq_add_neg] at h_srl_b h_sra_b h_srlw_b h_sraw_b h_sum_b h_b0 h_b1 h_b2 h_b3 h_b4 h_s0b h_s1b h_s2b
    have hp17 : 2 ^ 17 < p := Fact.out
    -- The variant flag-sum is 1, so the nine byte-pull guarantees fire (gated by `-(flag-sum) = -1`).
    have hsumneg : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) +
        env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 := by rw [hsum1]
    have hbyte_fact : ∀ {v w : ZMod p},
        (-(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) +
            env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 →
          byteChannel.Guarantees (⟨6, v, w, 0⟩ : ByteRow (ZMod p)) env.data) → v.val < 2 ^ w.val := by
      intro v w hb
      exact byteRowSpec_range_val (hb hsumneg)
    have lt_ll0 := hbyte_fact h_byte1
    have lt_lh0 := hbyte_fact h_byte2
    have lt_ll1 := hbyte_fact h_byte3
    have lt_lh1 := hbyte_fact h_byte4
    have lt_ll2 := hbyte_fact h_byte5
    have lt_lh2 := hbyte_fact h_byte6
    have lt_ll3 := hbyte_fact h_byte7
    have lt_lh3 := hbyte_fact h_byte8
    have b_cb0 := bool_of_mul_pred h_b0
    have b_cb1 := bool_of_mul_pred h_b1
    have b_cb2 := bool_of_mul_pred h_b2
    have b_cb3 := bool_of_mul_pred h_b3
    -- The three inverted `v_*` power encodings, in `limb_result_lt`'s form.
    have eq_v01 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2)
        = (1 + -env.get (i₀ + 4 + 1 + 1) + 1) * 2 * ((1 + -env.get (i₀ + 4 + 1 + 1 + 1)) * 3 + 1) := by
      linear_combination h_v01
    have eq_v012 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 2)) * 15 + 1) := by
      linear_combination h_v012
    have eq_v0123 : env.get (i₀ + 4 + 1 + 1 + 6 + 1)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) * ((1 + -env.get (i₀ + 4 + 1 + 1 + 3)) * 255 + 1) := by
      linear_combination h_v0123
    -- Bridge the byte-pull range facts to the `limb_result_lt`/`sign_fill_lt` exponent form.
    rw [cb4sum_natCast] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
    rw [cb4sum_sub_natCast] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
    -- limb_result reassemblies + `sra_msb_v0123` witness.
    have eq_lr0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by
      linear_combination h_lr0
    have eq_lr1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by
      linear_combination h_lr1
    have eq_lr2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by
      linear_combination h_lr2
    have eq_lr3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3)
        = env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) := by linear_combination h_lr3
    have eq_smv : env.get (i₀ + 4 + 1 + 1 + 6)
        = env.get (i₀ + 4) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) := by linear_combination h_smv
    -- The byte-shift one-hot of the `shift_u16` selectors.
    have honehot1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) +
          env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) +
        env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) = 1 := by
      have hh := h_onehot; rw [hsum1] at hh; linear_combination hh
    -- `b_msb ∈ {0,1}` unconditionally (the `U16MSBOperation` gadget's ungated booleanness).
    have hb3e : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
        = input_adapter_op_b_memory_prev_value[3] := by rw [← h_obmap]; simp only [Vector.getElem_map]
    have hbmsb_bool : env.get (i₀ + 4) = 0 ∨ env.get (i₀ + 4) = 1 :=
      (h_msb1 ⟨fun _ => by rw [hb3e]; exact h_rs1U 3, bool_of_mul_pred h_sra_b⟩).1
    -- The four `limb_result` atomic `u16` bounds (`lr0`/`lr1`/`lr2` via `limb_result_lt`; the bare high
    -- limbs `hl1`/`hl3` via the `ll = 0` specialisation).
    have B_hl1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1)).val < 2 ^ 16 := by
      have h := ShiftRightMath.limb_result_lt (hl := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1))
        (ll := 0) b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 (by rw [ZMod.val_zero]; positivity)
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num]; simpa using h
    have B_hl3 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3)).val < 2 ^ 16 := by
      have h := ShiftRightMath.limb_result_lt (hl := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3))
        (ll := 0) b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh3 (by rw [ZMod.val_zero]; positivity)
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num]; simpa using h
    have B_lr0 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4)).val < 2 ^ 16 := by
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, eq_lr0]
      exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh0 lt_ll1
    have B_lr1 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1)).val < 2 ^ 16 := by
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, eq_lr1]
      exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 lt_ll2
    have B_lr2 : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2)).val < 2 ^ 16 := by
      rw [show (2 : ℕ) ^ 16 = 65536 from by norm_num, eq_lr2]
      exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh2 lt_ll3
    have B_bmsbFill : (env.get (i₀ + 4) * 65535).val < 2 ^ 16 := by
      rcases hbmsb_bool with h | h <;> rw [h]
      · rw [zero_mul, ZMod.val_zero]; norm_num
      · rw [one_mul, show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast_of_lt (by omega)]; norm_num
    -- The sign-fill `lr3 + (b_msb·65536 - sra_msb_v0123)` is `u16` (`lr3 = hl3`; `b_msb = 0 ⇒ hl3`,
    -- `b_msb = 1 ⇒ hl3 + (65536 - v0123)` via `sign_fill_lt`).
    have B_lr3_fill : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3)
        + (env.get (i₀ + 4) * 65536 - env.get (i₀ + 4 + 1 + 1 + 6))).val < 2 ^ 16 := by
      rcases hbmsb_bool with h0 | h1
      · rw [eq_lr3, h0, show env.get (i₀ + 4 + 1 + 1 + 6) = 0 from by rw [eq_smv, h0, zero_mul]]
        simp only [zero_mul, sub_zero, add_zero]; exact B_hl3
      · rw [eq_lr3, h1, show env.get (i₀ + 4 + 1 + 1 + 6) = env.get (i₀ + 4 + 1 + 1 + 6 + 1) from by
            rw [eq_smv, h1, one_mul],
          show (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) + ((1 : ZMod p) * 65536
                - env.get (i₀ + 4 + 1 + 1 + 6 + 1)))
              = (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3)
                + (((65536 : ℕ) : ZMod p) - env.get (i₀ + 4 + 1 + 1 + 6 + 1))) from by push_cast; ring,
          show (2 : ℕ) ^ 16 = 65536 from by norm_num]
        exact ShiftRightMath.sign_fill_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh3
    -- Dispatch on `e13 = is_srlw + is_sraw ∈ {0,1}`; `e14 = 1` (SRL/SRA) or `e13 = 1` (SRLW/SRAW).
    rcases pair_flag (bool_of_mul_pred h_srl_b) (bool_of_mul_pred h_sra_b) (bool_of_mul_pred h_srlw_b)
      (bool_of_mul_pred h_sraw_b) (bool_of_mul_pred h_sum_b) with he13 | he13
    · -- `e13 = 0 ⇒ e14 = 1` (SRL/SRA): the 16 `e14`-gated placement asserts + atomic bounds.
      have he14 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) = 1 := by
        linear_combination hsum1 - he13
      simp only [← sub_eq_add_neg] at h_o0 h_o1 h_o2 h_o3 h_o4 h_o5 h_o6 h_o7 h_o8 h_o9 h_o10 h_o11 h_o12 h_o13 h_o14 h_o15
      exact srl_sra_a_isU64 he14 (bool_of_mul_pred h_s0b) (bool_of_mul_pred h_s1b)
        (bool_of_mul_pred h_s2b) honehot1 B_lr0 B_lr1 B_lr2 B_lr3_fill B_bmsbFill
        h_o0 h_o1 h_o2 h_o3 h_o4 h_o5 h_o6 h_o7 h_o8 h_o9 h_o10 h_o11 h_o12 h_o13 h_o14 h_o15
    · -- `e13 = 1` (SRLW/SRAW): the low-two placement + the de-gated `a2 = a3 = srw_msb·65535`.
      have he14_0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) = 0 := by
        linear_combination hsum1 - he13
      -- On a word row the limb-2 split is de-gated (`e14 = 0`), forcing `ll2 = 0`.
      have h_split2_dec : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) * 65536
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) * env.get (i₀ + 4 + 1 + 1 + 6 + 1) = 0 := by
        have h := h_split2; rw [he14_0] at h; linear_combination -h
      obtain ⟨-, h_ll2_0⟩ := ShiftRightMath.higher_lower_zero b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012
        eq_v0123 lt_lh2 lt_ll2 h_split2_dec
      -- The sign-fill `lr1 + (b_msb·65536 - sra_msb_v0123)` (with `ll2 = 0`, so `lr1 = hl1`) is `u16`.
      have B_lr1_fill : (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1)
          + (env.get (i₀ + 4) * 65536 - env.get (i₀ + 4 + 1 + 1 + 6))).val < 2 ^ 16 := by
        rw [eq_lr1, h_ll2_0, zero_mul, add_zero]
        rcases hbmsb_bool with h0 | h1
        · rw [h0, show env.get (i₀ + 4 + 1 + 1 + 6) = 0 from by rw [eq_smv, h0, zero_mul]]
          simp only [zero_mul, sub_zero, add_zero]; exact B_hl1
        · rw [h1, show env.get (i₀ + 4 + 1 + 1 + 6) = env.get (i₀ + 4 + 1 + 1 + 6 + 1) from by
              rw [eq_smv, h1, one_mul],
            show (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) + ((1 : ZMod p) * 65536
                  - env.get (i₀ + 4 + 1 + 1 + 6 + 1)))
                = (env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1)
                  + (((65536 : ℕ) : ZMod p) - env.get (i₀ + 4 + 1 + 1 + 6 + 1))) from by push_cast; ring,
            show (2 : ℕ) ^ 16 = 65536 from by norm_num]
          exact ShiftRightMath.sign_fill_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1
      -- `srw_msb ∈ {0,1}` from the `srw_msb` gadget once `a[1] < 2^16` is in hand (supplied by the lemma).
      have hsrw_of : (env.get (i₀ + 1)).val < 2 ^ 16 → env.get (i₀ + 4 + 1) = 0 ∨ env.get (i₀ + 4 + 1) = 1 :=
        fun ha1 => (h_msb3 ⟨fun _ => by show (env.get (i₀ + 1)).val < 2 ^ 16; exact ha1, Or.inr he13⟩).1
      -- The `cb4` byte-shift selectors, de-gated to `e14 = 0`.
      have hs0sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) * (env.get (i₀ + 4 + 1 + 1 + 4) - 0) = 0 := by
        have h := h_s0w; rw [he14_0] at h; linear_combination h
      have hs1sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) * (env.get (i₀ + 4 + 1 + 1 + 4) - 1) = 0 := by
        have h := h_s1w; rw [he14_0] at h; linear_combination h
      have hs2sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) * (env.get (i₀ + 4 + 1 + 1 + 4) - 2) = 0 := by
        have h := h_s2w; rw [he14_0] at h; linear_combination h
      have hs3sel : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) * (env.get (i₀ + 4 + 1 + 1 + 4) - 3) = 0 := by
        have h := h_s3w; rw [he14_0] at h; linear_combination h
      simp only [← sub_eq_add_neg] at h_w0 h_w1 h_w2 h_w3 h_w4 h_w5
      exact srlw_sraw_a_isU64 he13 (bool_of_mul_pred h_b4) hs0sel hs1sel hs2sel hs3sel honehot1
        B_lr0 B_lr1_fill B_bmsbFill hsrw_of h_w0 h_w1 h_w2 h_w3 h_w4 h_w5
  intro hsum1
  obtain ⟨c0, c1, c2, c3⟩ := hbounds hsum1
  rw [hcolsa]
  exact Word.isU64_of_cases c0 c1 c2 c3

end SP1Clean.ShiftRightChip
