import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.MulOperation
import SP1Clean.Proofs.Operations.DivRemOperation.Compare
import SP1Clean.Proofs.Operations.DivRemOperation.Core
import SP1Clean.Native.Operations.DivRemOperation.OwnAsserts
import SP1Clean.Native.Operations.DivRemOperation.AssertZeros
import SP1Clean.Proofs.Chips.DivRemChip.Populate
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.DivRemChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `DivRem` chip row as a `GeneralFormalCircuit`

`DIV`/`DIVU`/`REM`/`REMU`/`DIVW`/`REMW`/`DIVUW`/`REMUW`: flag-gated `Spec` (RV64 div/rem identities on
`cols.a`) in `Specs/Chip.lean`; output is the extracted `DivRemCols` (246 columns).

`main` witnesses the full row (unchanged witness stream, `localLength = 217`), composes the
`CPUState`/`RTypeReader` readers, then asserts the complete constraint set through the two
whole-row `FormalAssertion` gadgets over the assembled `DivRemCols`:
`DivRemCompare.circuit` (`IsEqualWordOperation`×4 overflow, `IsZeroWordOperation` divide-by-zero,
`AddOperation`×2 negation, `LtOperationUnsigned` remainder range, `U16MSBOperation`×7 sign bits) and
`DivRemCore.circuit` (the two `c·quotient` `MulOperation` products, the eight product-glue asserts,
the chip's own assertZero tail `ownAsserts`, and the 34-pull byte-range tail), followed by the op_a
`RegisterWrite` push. The public contract and its isolated family-evidence layer are in
`FormalModel/Contracts/DivRem.lean` and `Cases.lean`; whole-chip evidence extraction and
completeness are explicit deferred seams in `Formal.lean`/`Completeness/Driver.lean`. -/

namespace SP1Clean.DivRemChip

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

-- The chip composes `MulOperation` (the schoolbook product column-sum ≈ 2^24 before the ZMod→ℕ lift),
-- so it carries the `Fact (2 ^ 24 < p)` field bound — subsuming the project-wide `2 ^ 17`, which
-- `MulOperation` re-exports as an instance.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Operand `isU64` contract; lives in `Defs` (not `Formal`) so `Soundness/<Op>.lean` split files can
import it without a cycle. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness: the register-read `isU64`s, the `is_real` binary selector, the
honest `"div_rem_flags"` hint (each flag binary, the sum `= 1` **unconditionally** — E367 is ungated,
and SP1's padding rows carry `is_divu = 1`), the **padding pin** (an `is_real = 0` row is exactly
SP1's "0 divided by 1" template: zero `b` read, `c` read `= Word(1)`, the `is_divu` flag — this is
what makes the ungated lower glue and the flag-gated shape asserts dischargeable off-gate),
`op_a_0 = 0`, the CPUState clock bounds, and the three register-access timestamp `Spec`s (mirrors
`MulChip.ProverAssumptions` — R-type, no immediate machinery). Lives in `Defs` (not `Formal`) so the
`Completeness/` split files can import it without a cycle. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  -- (W11 memory flip) the op_a (`rd`) read-prior pull's `prev_value` is `isU64` on real rows — the
  -- `RTypeReader`'s completeness needs the memory trio (op_a/op_b/op_c reads `isU64`) to emit its pulls;
  -- op_b/op_c come from the two operand `isU64`s above, op_a from this (mirrors `MulChip.ProverAssumptions`).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧ (f[2] = 0 ∨ f[2] = 1) ∧ (f[3] = 0 ∨ f[3] = 1) ∧
  (f[4] = 0 ∨ f[4] = 1) ∧ (f[5] = 0 ∨ f[5] = 1) ∧ (f[6] = 0 ∨ f[6] = 1) ∧ (f[7] = 0 ∨ f[7] = 1) ∧
  f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1 ∧
  (input.is_real = 0 →
    input.op_b_val = #v[0, 0, 0, 0] ∧ input.op_c_val = #v[1, 0, 0, 0] ∧
    f = #v[0, 1, 0, 0, 0, 0, 0, 0]) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state,
      next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  -- (W11 flip) the `RTypeReader` program **pull** now *derives* the decode bounds into its `Spec`
  -- (destination index `< 32`, pc limbs `< 2^16`, on real rows) — completeness must provide them.
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

/-- All-zero `fromElements` placeholder for any column block. -/
@[irreducible] def zc {α : TypeMap} [ProvableType α] : Var α (ZMod p) :=
  ProvableType.fromElements (F := Expression (ZMod p)) (.replicate _ 0)

-- `assertZeros` + its `circuit_norm` normalization lemmas (`*_map_assert`) and `ExplicitCircuits`
-- instance were relocated verbatim to `Native/Operations/DivRemOperation/AssertZeros.lean` (same
-- `SP1Clean.DivRemChip` namespace) so the `DivRemCore` assertion gadget can emit the same
-- own-assert tail without importing this chip skeleton.

set_option maxHeartbeats 4000000 in
/-- `main` — witnesses the full row in the extracted witness-stream order (unchanged from the
pre-gadget shape, so the trace-conformance vectors are stable), composes the `CPUState`/
`RTypeReader` readers, assembles `DivRemCols`, and asserts the complete constraint set through the
two whole-row gadgets `DivRemCompare.circuit` (comparison/sign cluster) and `DivRemCore.circuit`
(products, glue, `ownAsserts`, byte-range tail), then pushes the op_a `RegisterWrite`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var DivRemCols (ZMod p)) := do
  let bpv := input.adapter.op_b_memory.prev_value
  let cpv := input.adapter.op_c_memory.prev_value
  -- The honest variant flags from the `"div_rem_flags"` `ProverHint` (one-hot on real rows;
  -- the key's absence defaults to the `is_divu = 1` padding template — `Populate.hintFlags`).
  let flags ← witnessVectorNative 8 (fun env => hintFlags env.hint)
  let is_div := flags[0]; let is_divu := flags[1]; let is_rem := flags[2]; let is_remu := flags[3]
  let is_divw := flags[4]; let is_remw := flags[5]; let is_divuw := flags[6]; let is_remuw := flags[7]
  let quotient_comp ← witnessVectorNative 4 (fun env =>
    populateQuotComp #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let a ← witnessVectorNative 4 (fun env =>
    populateA #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- The arithmetic **operands** `b`/`c` — committed columns distinct from the raw register reads
  -- (`adapter.op_b/c_memory.prev_value`). The chip's own-asserts E20–E47 tie them to the reads: equal to the
  -- read for the 64-bit variants, the sign/zero-extension of the low 32 bits for the W-variants (`b[i] =
  -- read[i]·(1-isword) + b_neg·isword·0xFFFF`). Witnessed here (before the `MulOperation`s, which multiply by
  -- `c`); populated honestly (`bComp`/`cComp` compute the flag-dependent extension). Soundness does not
  -- depend on the populate value (E20–E47 pin the columns).
  let b ← witnessVectorNative 4 (fun env =>
    bComp #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]] (hintFlags env.hint))
  let c ← witnessVectorNative 4 (fun env =>
    cComp #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- (1,2) The two `c_times_quotient` product structs of `quotient_comp × c`, witnessed via the
  -- gated populates (`mul_lower` on real rows only; `mul_upper` only on the 64-bit variants —
  -- SP1's word rows and padding leave them all-zero). Their `MulOperation` product constraints
  -- (and the limb glue tying them to `c_times_quotient`) are asserted by `DivRemCore.circuit`
  -- over the assembled row below.
  let mul_lower ← witnessNative (var := Var Extracted.MulOperation) (fun env =>
    populateMulLower (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let mul_upper ← witnessNative (var := Var Extracted.MulOperation) (fun env =>
    populateMulUpper (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- Witnessed scalar sign/gate columns + the `c_times_quotient`/`carry` u16-limb vectors, all
  -- honestly populated (`populateScal`/`populateCtq`/`populateCarry`); the own-asserts
  -- `E13/E15/…` and the carry chain `E121…E151` pin them.
  let scal ← witnessVectorNative 7 (fun env =>
    populateScal (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let is_overflow := scal[0]; let b_neg := scal[1]; let b_neg_not_overflow := scal[2]
  let b_not_neg_not_overflow := scal[3]; let is_real_not_word := scal[4]
  let rem_neg := scal[5]; let c_neg := scal[6]
  let c_times_quotient ← witnessVectorNative 8 (fun env =>
    populateCtq #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let carry ← witnessVectorNative 8 (fun env =>
    populateCarry #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- The `IsEqualWordOperation`/`IsZeroWordOperation` nested cols, witnessed flat via
  -- `fromElements (F := …)`; their overflow/divide-by-zero assertions live in
  -- `DivRemCompare.circuit` below.
  let w_ovb ← witnessVectorNative 11 (fun env =>
    (ProvableType.toElements (ovbWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]] (hintFlags env.hint))).cast
        (show size Extracted.IsEqualWordOperation = 11 from rfl))
  let w_ovc ← witnessVectorNative 11 (fun env =>
    (ProvableType.toElements (ovcWitness (env input.is_real)
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))).cast
        (show size Extracted.IsEqualWordOperation = 11 from rfl))
  let w_is_c_0 ← witnessVectorNative 11 (fun env =>
    (ProvableType.toElements (isC0Witness
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))).cast
        (show size Extracted.IsZeroWordOperation = 11 from rfl))
  -- The negation/comparison witness columns (`|c|`, `|remainder|`, `max(|c|,1)`, the two
  -- `AddOperation` nested cols, the `LtOperationUnsigned` comparison columns) via `populate_*`;
  -- the `AddOperation`×2 / `LtOperationUnsigned` assertions live in `DivRemCompare.circuit` below.
  let abs_c ← witnessVectorNative 4 (fun env =>
    populateAbsC #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let abs_remainder ← witnessVectorNative 4 (fun env =>
    populateAbsRem #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let remainder_comp ← witnessVectorNative 4 (fun env =>
    populateRemComp #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let max_abs_c_or_1 ← witnessVectorNative 4 (fun env =>
    populateMaxAbsCOr1 #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let w_cneg ← witnessVectorNative 4 (fun env =>
    wCnegWitness (env input.is_real)
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let w_rneg ← witnessVectorNative 4 (fun env =>
    wRnegWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let misc ← witnessVectorNative 3 (fun env =>
    populateMisc (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let abs_c_alu_event := misc[0]; let abs_rem_alu_event := misc[1]
  let remainder_check_multiplicity := misc[2]
  let cl ← witnessVectorNative 2 (fun env =>
    ltClWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let f ← witnessVectorNative 4 (fun env =>
    ltFlagsWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let not_eq_inv ← witnessVectorNative 1 (fun env =>
    ltNotEqInvWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let bit ← witnessVectorNative 1 (fun env =>
    ltBitWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let lt_out : Var Extracted.LtOperationUnsigned (ZMod p) := ⟨⟨bit[0]⟩, f, not_eq_inv[0], cl⟩
  -- The remainder/quotient result words and the four `U16MSBOperation` sign-bit cells; the seven
  -- MSB assertions live in `DivRemCompare.circuit` below.
  let remainder ← witnessVectorNative 4 (fun env =>
    populateRemainder #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let quotient ← witnessVectorNative 4 (fun env =>
    populateQuotient #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let w_bmsb ← witnessVectorNative 1 (fun env =>
    #v[bMsbCell #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]] (hintFlags env.hint)])
  let w_cmsb ← witnessVectorNative 1 (fun env =>
    #v[cMsbCell #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)])
  let w_remmsb ← witnessVectorNative 1 (fun env =>
    #v[remMsbCell #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)])
  let w_quotmsb ← witnessVectorNative 1 (fun env =>
    #v[quotMsbCell #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)])
  -- Readers (after the witness stream, extracted order — `E382` opcode + result-word write):
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * (65536 : Expression (ZMod p)), input.state.pc,
     is_divu * 16 + is_remu * 18 + is_div * 15 + is_rem * 17 + is_divw * 25 + is_remw * 27
       + is_divuw * 26 + is_remuw * 28,
     a[0], a[1], a[2], a[3]⟩
  -- Assemble `DivRemCols`, then assert the entire non-reader constraint set through the two
  -- whole-row `FormalAssertion` gadgets (each `localLength = 0`, so the witness stream above is
  -- the complete 217-cell row): `DivRemCompare.circuit` (IsEqualWord ×4 / IsZeroWord / Add ×2 /
  -- LtU / U16MSB ×7) and `DivRemCore.circuit` (MulOperation ×2 + the 8 product-glue asserts +
  -- `assertZeros (ownAsserts cols)` — `E13…E367`, `op_a_0`, incl. the binary gates like
  -- `is_real·(is_real-1)` = E355 — + the 34 gated byte-range pulls).
  let cols : Var DivRemCols (ZMod p) := ⟨input.state, input.adapter, a, b, c,
    quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c,
    max_abs_c_or_1, c_times_quotient, mul_lower, mul_upper, ⟨w_cneg⟩, ⟨w_rneg⟩, lt_out,
    carry, fromElements (F := Expression (ZMod p)) w_is_c_0,
    is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw,
    is_overflow, fromElements (F := Expression (ZMod p)) w_ovb,
    fromElements (F := Expression (ZMod p)) w_ovc,
    ⟨w_bmsb[0]⟩, ⟨w_remmsb[0]⟩, ⟨w_cmsb[0]⟩, ⟨w_quotmsb[0]⟩,
    b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg, c_neg,
    abs_c_alu_event, abs_rem_alu_event, input.is_real, remainder_check_multiplicity⟩
  assertion DivRemCompare.circuit cols
  assertion DivRemCore.circuit cols
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the arithmetic so `isU64 a` (the flag-selected quotient/remainder output, byte-range-checked) discharges
  -- its requirement — breaking the old reader-circularity. Write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, input.is_real⟩
  return cols

set_option maxHeartbeats 8000000 in
@[implicit_reducible] private def derivedElaborated :
    ElaboratedCircuit (ZMod p) Inputs DivRemCols main := by
  elaborate_circuit_with {
    channelsWithGuarantees :=
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  }

-- Seal the large derived record behind theorem constants. Downstream semantic proofs routinely
-- unfold `elaborated`; exposing projections of `derivedElaborated` there makes reducibility unfold
-- the whole chip again during metavariable instantiation.
private theorem derivedLocalLengthEq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (main input).localLength offset = 217 := by
  rw [derivedElaborated.localLength_eq]
  rfl

private theorem derivedSubcircuitsConsistent (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).SubcircuitsConsistent offset :=
  derivedElaborated.subcircuitsConsistent input offset

private theorem derivedChannelsLawful :
    ElaboratedCircuit.ChannelsLawful main
      ([byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] :
        List (RawChannel (ZMod p))) :=
  derivedElaborated.channelsLawful

/-- Clean derives the output layout and structural metadata from the composed chip.  The public record
forwards the compact output while keeping the constant local length visible at the proof boundary. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs DivRemCols main where
  output := derivedElaborated.output
  output_eq := derivedElaborated.output_eq
  -- Keep the constant visible at the proof boundary: exposing the derived length makes
  -- `circuit_proof_start` normalize the entire 246-column circuit whenever it unfolds this record.
  localLength _ := 217
  localLength_eq := derivedLocalLengthEq
  subcircuitsConsistent := derivedSubcircuitsConsistent
  channelsWithGuarantees :=
    [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := derivedChannelsLawful (p := p)

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 217 := rfl

/-- The shared CPU-state block in DivRem's output is an alias of the input block.  Exposing this
small projection prevents whole-machine proofs from normalizing the complete 217-cell output just
to identify the State-bus payload. -/
@[circuit_norm] lemma output_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((elaborated (p := p)).output input offset).state = input.state := rfl

end SP1Clean.DivRemChip
