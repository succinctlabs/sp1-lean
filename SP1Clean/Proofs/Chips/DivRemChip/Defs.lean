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
the chip's own assertZero tail `ownAsserts`, and the 32-pull byte-range tail), followed by the op_a
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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: completeness of the three memory read-prior pulls must exhibit the channel guarantee's
  -- 24-bit prior timestamps.  This is honest-trace data, not a soundness assumption: soundness derives
  -- the same bounds from the balanced Memory channel.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

/-- All-zero `fromElements` placeholder for any column block. -/
@[irreducible] def zc {α : TypeMap} [ProvableType α] : Var α (ZMod p) :=
  ProvableType.fromElements (F := Expression (ZMod p)) (.replicate _ 0)

-- `assertZeros` + its `circuit_norm` normalization lemmas (`*_map_assert`) and `ExplicitCircuits`
-- instance were relocated verbatim to `Native/Operations/DivRemOperation/AssertZeros.lean` (same
-- `SP1Clean.DivRemChip` namespace) so the `DivRemCore` assertion gadget can emit the same
-- own-assert tail without importing this chip skeleton.

set_option maxHeartbeats 4000000 in
/-- The witness-only prefix of `main`, factored as a plain circuit definition so completeness can
reason about the 217-cell populate stream separately from the semantic proof boundaries. This is
not a new subcircuit: inlining it preserves the exact witness order and the resulting flat AIR. -/
def populateRow (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var DivRemCols (ZMod p)) := do
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
  return ⟨input.state, input.adapter, a, b, c,
    quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c,
    max_abs_c_or_1, c_times_quotient, mul_lower, mul_upper, ⟨w_cneg⟩, ⟨w_rneg⟩, lt_out,
    carry, fromElements (F := Expression (ZMod p)) w_is_c_0,
    is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw,
    is_overflow, fromElements (F := Expression (ZMod p)) w_ovb,
    fromElements (F := Expression (ZMod p)) w_ovc,
    ⟨w_bmsb[0]⟩, ⟨w_remmsb[0]⟩, ⟨w_cmsb[0]⟩, ⟨w_quotmsb[0]⟩,
    b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg, c_neg,
    abs_c_alu_event, abs_rem_alu_event, input.is_real, remainder_check_multiplicity⟩

/-- The explicit row layout produced by `populateRow` at a given local-witness offset. Naming this
layout prevents downstream proofs from repeatedly reducing the full 30-bind populate program merely
to discover the same column indices. It is checked against `populateRow` by
`populateRow_output_eq`; it is not an independent witness generator. -/
def populatedRowAt (input : Var Inputs (ZMod p)) (offset : ℕ) : Var DivRemCols (ZMod p) :=
  let flags := varFromOffset (F := ZMod p) (fields 8) offset
  let oQc := offset + 8
  let quotientComp := varFromOffset (F := ZMod p) (fields 4) oQc
  let oA := oQc + 4
  let a := varFromOffset (F := ZMod p) (fields 4) oA
  let oB := oA + 4
  let b := varFromOffset (F := ZMod p) (fields 4) oB
  let oC := oB + 4
  let c := varFromOffset (F := ZMod p) (fields 4) oC
  let oMulLower := oC + 4
  let mulLower := varFromOffset (F := ZMod p) Extracted.MulOperation oMulLower
  let oMulUpper := oMulLower + 45
  let mulUpper := varFromOffset (F := ZMod p) Extracted.MulOperation oMulUpper
  let oScal := oMulUpper + 45
  let scal := varFromOffset (F := ZMod p) (fields 7) oScal
  let oCtq := oScal + 7
  let ctq := varFromOffset (F := ZMod p) (fields 8) oCtq
  let oCarry := oCtq + 8
  let carry := varFromOffset (F := ZMod p) (fields 8) oCarry
  let oOvb := oCarry + 8
  let wOvb := varFromOffset (F := ZMod p) (fields 11) oOvb
  let oOvc := oOvb + 11
  let wOvc := varFromOffset (F := ZMod p) (fields 11) oOvc
  let oIsC0 := oOvc + 11
  let wIsC0 := varFromOffset (F := ZMod p) (fields 11) oIsC0
  let oAbsC := oIsC0 + 11
  let absC := varFromOffset (F := ZMod p) (fields 4) oAbsC
  let oAbsRemainder := oAbsC + 4
  let absRemainder := varFromOffset (F := ZMod p) (fields 4) oAbsRemainder
  let oRemainderComp := oAbsRemainder + 4
  let remainderComp := varFromOffset (F := ZMod p) (fields 4) oRemainderComp
  let oMaxAbsCOr1 := oRemainderComp + 4
  let maxAbsCOr1 := varFromOffset (F := ZMod p) (fields 4) oMaxAbsCOr1
  let oCNeg := oMaxAbsCOr1 + 4
  let cNeg := varFromOffset (F := ZMod p) (fields 4) oCNeg
  let oRemNeg := oCNeg + 4
  let remNeg := varFromOffset (F := ZMod p) (fields 4) oRemNeg
  let oMisc := oRemNeg + 4
  let misc := varFromOffset (F := ZMod p) (fields 3) oMisc
  let oCl := oMisc + 3
  let cl := varFromOffset (F := ZMod p) (fields 2) oCl
  let oLtFlags := oCl + 2
  let ltFlags := varFromOffset (F := ZMod p) (fields 4) oLtFlags
  let oNotEqInv := oLtFlags + 4
  let notEqInv := varFromOffset (F := ZMod p) (fields 1) oNotEqInv
  let oBit := oNotEqInv + 1
  let bit := varFromOffset (F := ZMod p) (fields 1) oBit
  let ltOut : Var Extracted.LtOperationUnsigned (ZMod p) :=
    ⟨⟨bit[0]⟩, ltFlags, notEqInv[0], cl⟩
  let oRemainder := oBit + 1
  let remainder := varFromOffset (F := ZMod p) (fields 4) oRemainder
  let oQuotient := oRemainder + 4
  let quotient := varFromOffset (F := ZMod p) (fields 4) oQuotient
  let oBmsb := oQuotient + 4
  let bmsb := varFromOffset (F := ZMod p) (fields 1) oBmsb
  let oCmsb := oBmsb + 1
  let cmsb := varFromOffset (F := ZMod p) (fields 1) oCmsb
  let oRemmsb := oCmsb + 1
  let remmsb := varFromOffset (F := ZMod p) (fields 1) oRemmsb
  let oQuotmsb := oRemmsb + 1
  let quotmsb := varFromOffset (F := ZMod p) (fields 1) oQuotmsb
  ⟨input.state, input.adapter, a, b, c,
    quotient, quotientComp, remainderComp, remainder, absRemainder, absC,
    maxAbsCOr1, ctq, mulLower, mulUpper, ⟨cNeg⟩, ⟨remNeg⟩, ltOut,
    carry, fromElements (F := Expression (ZMod p)) wIsC0,
    flags[0], flags[1], flags[2], flags[3], flags[4], flags[5], flags[6], flags[7],
    scal[0], fromElements (F := Expression (ZMod p)) wOvb,
    fromElements (F := Expression (ZMod p)) wOvc,
    ⟨bmsb[0]⟩, ⟨remmsb[0]⟩, ⟨cmsb[0]⟩, ⟨quotmsb[0]⟩,
    scal[1], scal[2], scal[3], scal[4], scal[5], scal[6],
    misc[0], misc[1], input.is_real, misc[2]⟩

set_option linter.unusedSectionVars false in
/-- Folded projection of the lower Mul witness block from the explicit row layout. -/
theorem populatedRowAt_mulLower_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_times_quotient_lower =
      ProvableType.varFromOffset (F := ZMod p) Extracted.MulOperation
        (offset + 8 + 4 + 4 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projection of the upper Mul witness block from the explicit row layout. -/
theorem populatedRowAt_mulUpper_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_times_quotient_upper =
      ProvableType.varFromOffset (F := ZMod p) Extracted.MulOperation
        (offset + 8 + 4 + 4 + 4 + 4 + 45) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projection of the quotient-complement witness vector. -/
theorem populatedRowAt_quotientComp_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).quotient_comp =
      varFromOffset (F := ZMod p) (fields 4) (offset + 8) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projection of the normalized divisor witness vector. -/
theorem populatedRowAt_c_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c =
      varFromOffset (F := ZMod p) (fields 4) (offset + 8 + 4 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projection of the eight `c_times_quotient` limbs. -/
theorem populatedRowAt_ctq_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_times_quotient =
      varFromOffset (F := ZMod p) (fields 8)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7) := rfl

/-! The following projection lemmas are intentionally repetitive.  They make the explicit witness
layout an opaque API: completeness proofs rewrite one named field without weak-head-normalizing the
other 245 columns of `populatedRowAt`. -/

set_option linter.unusedSectionVars false in
theorem populatedRowAt_adapter_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).adapter = input.adapter := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).state = input.state := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isDiv_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_div = var { index := offset } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isDivu_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_divu = var { index := offset + 1 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isRem_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_rem = var { index := offset + 2 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isRemu_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_remu = var { index := offset + 3 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isDivw_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_divw = var { index := offset + 4 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isRemw_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_remw = var { index := offset + 5 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isDivuw_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_divuw = var { index := offset + 6 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isRemuw_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_remuw = var { index := offset + 7 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isReal_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_real = input.is_real := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_a_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).a =
      varFromOffset (F := ZMod p) (fields 4) (offset + 8 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_b_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).b =
      varFromOffset (F := ZMod p) (fields 4) (offset + 8 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remainderComp_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder_comp =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_absC_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).abs_c =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_absRemainder_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).abs_remainder =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_maxAbsCOr1_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).max_abs_c_or_1 =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_cNegValue_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_neg_operation.value =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remNegValue_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).rem_neg_operation.value =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projection of the complete divisor-negation operation. -/
theorem populatedRowAt_cNegOperation_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_neg_operation =
      varFromOffset (F := ZMod p) Extracted.AddOperation (offset + 186) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projection of the complete remainder-negation operation. -/
theorem populatedRowAt_remNegOperation_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).rem_neg_operation =
      varFromOffset (F := ZMod p) Extracted.AddOperation (offset + 190) := rfl

set_option linter.unusedSectionVars false in
/-- Folded projections of the reordered unsigned-less-than witness. -/
theorem populatedRowAt_ltComparisonLimbs_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder_lt_operation.comparison_limbs =
      varFromOffset (F := ZMod p) (fields 2) (offset + 197) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_ltU16Flags_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder_lt_operation.u16_flags =
      varFromOffset (F := ZMod p) (fields 4) (offset + 199) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_ltNotEqInv_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder_lt_operation.not_eq_inv =
      var { index := offset + 203 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_carry_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).carry =
      varFromOffset (F := ZMod p) (fields 8)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remainder_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_quotient_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).quotient =
      varFromOffset (F := ZMod p) (fields 4)
        (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isOverflow_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_overflow =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_bNeg_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).b_neg =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 1 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_bNegNotOverflow_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).b_neg_not_overflow =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 2 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_bNotNegNotOverflow_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).b_not_neg_not_overflow =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 3 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isRealNotWord_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_real_not_word =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remNeg_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).rem_neg =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 5 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_cNeg_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_neg =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 6 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_absCEvent_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).abs_c_alu_event =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_absRemEvent_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).abs_rem_alu_event =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 1 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remainderCheckMultiplicity_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder_check_multiplicity =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 2 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isOverflowB_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_overflow_b =
      ProvableType.fromElements (M := Extracted.IsEqualWordOperation)
        (varFromOffset (F := ZMod p) (fields 11)
          (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8)) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isOverflowC_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_overflow_c =
      ProvableType.fromElements (M := Extracted.IsEqualWordOperation)
        (varFromOffset (F := ZMod p) (fields 11)
          (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11)) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_isC0_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).is_c_0 =
      ProvableType.fromElements (M := Extracted.IsZeroWordOperation)
        (varFromOffset (F := ZMod p) (fields 11)
          (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11)) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_bMsb_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).b_msb.msb =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_cMsb_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_msb.msb =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remMsb_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).rem_msb.msb =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1 } := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_quotMsb_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).quot_msb.msb =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1 + 1 } := rfl

set_option linter.unusedSectionVars false in
/-- Folded projections of the four one-cell sign-bit operations. -/
theorem populatedRowAt_bMsbOperation_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).b_msb =
      varFromOffset (F := ZMod p) Extracted.U16MSBOperation (offset + 213) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_cMsbOperation_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).c_msb =
      varFromOffset (F := ZMod p) Extracted.U16MSBOperation (offset + 214) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_remMsbOperation_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).rem_msb =
      varFromOffset (F := ZMod p) Extracted.U16MSBOperation (offset + 215) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_quotMsbOperation_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).quot_msb =
      varFromOffset (F := ZMod p) Extracted.U16MSBOperation (offset + 216) := rfl

set_option linter.unusedSectionVars false in
theorem populatedRowAt_ltBit_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populatedRowAt input offset).remainder_lt_operation.u16_compare_operation.bit =
      var { index := offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
        + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 } := rfl

/-- The value of one generated forty-five-cell Mul witness block.  This stays irreducible because
putting the raw `Eval.eval (varFromOffset MulOperation ...)` term in downstream theorem types makes
the elaborator normalize the entire generated struct during `whnf`. -/
@[irreducible] def evaluatedMulBlock (env : Environment (ZMod p)) (offset : ℕ) :
    Extracted.MulOperation (ZMod p) :=
  Eval.eval env (ProvableType.varFromOffset (F := ZMod p) Extracted.MulOperation offset)

/-- Component-wise evaluation of the committed DivRem row. This is the whole-chip counterpart of
the compact comparison input's evaluator: consumers rewrite it before projecting fields instead
of normalizing the 246-column flattened evaluator. -/
@[circuit_norm] theorem eval_divRemCols {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env.toEnvironment cols.state,
         adapter := Eval.eval env.toEnvironment cols.adapter,
         a := Eval.eval env.toEnvironment cols.a,
         b := Eval.eval env.toEnvironment cols.b,
         c := Eval.eval env.toEnvironment cols.c,
         quotient := Eval.eval env.toEnvironment cols.quotient,
         quotient_comp := Eval.eval env.toEnvironment cols.quotient_comp,
         remainder_comp := Eval.eval env.toEnvironment cols.remainder_comp,
         remainder := Eval.eval env.toEnvironment cols.remainder,
         abs_remainder := Eval.eval env.toEnvironment cols.abs_remainder,
         abs_c := Eval.eval env.toEnvironment cols.abs_c,
         max_abs_c_or_1 := Eval.eval env.toEnvironment cols.max_abs_c_or_1,
         c_times_quotient := Eval.eval env.toEnvironment cols.c_times_quotient,
         c_times_quotient_lower := Eval.eval env.toEnvironment cols.c_times_quotient_lower,
         c_times_quotient_upper := Eval.eval env.toEnvironment cols.c_times_quotient_upper,
         c_neg_operation := Eval.eval env.toEnvironment cols.c_neg_operation,
         rem_neg_operation := Eval.eval env.toEnvironment cols.rem_neg_operation,
         remainder_lt_operation := Eval.eval env.toEnvironment cols.remainder_lt_operation,
         carry := Eval.eval env.toEnvironment cols.carry,
         is_c_0 := Eval.eval env.toEnvironment cols.is_c_0,
         is_div := Eval.eval env.toEnvironment cols.is_div,
         is_divu := Eval.eval env.toEnvironment cols.is_divu,
         is_rem := Eval.eval env.toEnvironment cols.is_rem,
         is_remu := Eval.eval env.toEnvironment cols.is_remu,
         is_divw := Eval.eval env.toEnvironment cols.is_divw,
         is_remw := Eval.eval env.toEnvironment cols.is_remw,
         is_divuw := Eval.eval env.toEnvironment cols.is_divuw,
         is_remuw := Eval.eval env.toEnvironment cols.is_remuw,
         is_overflow := Eval.eval env.toEnvironment cols.is_overflow,
         is_overflow_b := Eval.eval env.toEnvironment cols.is_overflow_b,
         is_overflow_c := Eval.eval env.toEnvironment cols.is_overflow_c,
         b_msb := Eval.eval env.toEnvironment cols.b_msb,
         rem_msb := Eval.eval env.toEnvironment cols.rem_msb,
         c_msb := Eval.eval env.toEnvironment cols.c_msb,
         quot_msb := Eval.eval env.toEnvironment cols.quot_msb,
         b_neg := Eval.eval env.toEnvironment cols.b_neg,
         b_neg_not_overflow := Eval.eval env.toEnvironment cols.b_neg_not_overflow,
         b_not_neg_not_overflow := Eval.eval env.toEnvironment cols.b_not_neg_not_overflow,
         is_real_not_word := Eval.eval env.toEnvironment cols.is_real_not_word,
         rem_neg := Eval.eval env.toEnvironment cols.rem_neg,
         c_neg := Eval.eval env.toEnvironment cols.c_neg,
         abs_c_alu_event := Eval.eval env.toEnvironment cols.abs_c_alu_event,
         abs_rem_alu_event := Eval.eval env.toEnvironment cols.abs_rem_alu_event,
         is_real := Eval.eval env.toEnvironment cols.is_real,
         remainder_check_multiplicity :=
           Eval.eval env.toEnvironment cols.remainder_check_multiplicity } : DivRemCols F) := by
  provable_struct_simp

/-- Verifier-environment form of `eval_divRemCols`.  The row is a `ProvableType`, so its prover
and verifier evaluations coincide; exposing both spellings prevents soundness proofs from
manufacturing a runtime hint merely to use the component-wise evaluator. -/
@[circuit_norm] theorem eval_divRemCols_verifier {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         a := Eval.eval env cols.a,
         b := Eval.eval env cols.b,
         c := Eval.eval env cols.c,
         quotient := Eval.eval env cols.quotient,
         quotient_comp := Eval.eval env cols.quotient_comp,
         remainder_comp := Eval.eval env cols.remainder_comp,
         remainder := Eval.eval env cols.remainder,
         abs_remainder := Eval.eval env cols.abs_remainder,
         abs_c := Eval.eval env cols.abs_c,
         max_abs_c_or_1 := Eval.eval env cols.max_abs_c_or_1,
         c_times_quotient := Eval.eval env cols.c_times_quotient,
         c_times_quotient_lower := Eval.eval env cols.c_times_quotient_lower,
         c_times_quotient_upper := Eval.eval env cols.c_times_quotient_upper,
         c_neg_operation := Eval.eval env cols.c_neg_operation,
         rem_neg_operation := Eval.eval env cols.rem_neg_operation,
         remainder_lt_operation := Eval.eval env cols.remainder_lt_operation,
         carry := Eval.eval env cols.carry,
         is_c_0 := Eval.eval env cols.is_c_0,
         is_div := Eval.eval env cols.is_div,
         is_divu := Eval.eval env cols.is_divu,
         is_rem := Eval.eval env cols.is_rem,
         is_remu := Eval.eval env cols.is_remu,
         is_divw := Eval.eval env cols.is_divw,
         is_remw := Eval.eval env cols.is_remw,
         is_divuw := Eval.eval env cols.is_divuw,
         is_remuw := Eval.eval env cols.is_remuw,
         is_overflow := Eval.eval env cols.is_overflow,
         is_overflow_b := Eval.eval env cols.is_overflow_b,
         is_overflow_c := Eval.eval env cols.is_overflow_c,
         b_msb := Eval.eval env cols.b_msb,
         rem_msb := Eval.eval env cols.rem_msb,
         c_msb := Eval.eval env cols.c_msb,
         quot_msb := Eval.eval env cols.quot_msb,
         b_neg := Eval.eval env cols.b_neg,
         b_neg_not_overflow := Eval.eval env cols.b_neg_not_overflow,
         b_not_neg_not_overflow := Eval.eval env cols.b_not_neg_not_overflow,
         is_real_not_word := Eval.eval env cols.is_real_not_word,
         rem_neg := Eval.eval env cols.rem_neg,
         c_neg := Eval.eval env cols.c_neg,
         abs_c_alu_event := Eval.eval env cols.abs_c_alu_event,
         abs_rem_alu_event := Eval.eval env cols.abs_rem_alu_event,
         is_real := Eval.eval env cols.is_real,
         remainder_check_multiplicity :=
           Eval.eval env cols.remainder_check_multiplicity } : DivRemCols F) := by
  let proverEnv : ProverEnvironment F :=
    { toEnvironment := env, hint := ProverHint.empty F }
  have h := eval_divRemCols proverEnv cols
  simpa only [proverEnv, CircuitType.eval_expression_prover_to_verifier] using h

/-! These verifier projections are deliberately scalar.  Consumers at the completed chip boundary
must not rewrite `eval_divRemCols_verifier` directly: doing so places the complete 246-column
evaluated row in the goal and can make an otherwise structural proof normalize the full DivRem
witness.  Each lemma below pays that cost once, behind an opaque declaration. -/

@[circuit_norm] theorem eval_divRemCols_state_verifier {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).state = Eval.eval env cols.state := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_adapter_verifier {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).adapter = Eval.eval env cols.adapter := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_a_verifier {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).a = Eval.eval env cols.a := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_c_verifier {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c = Eval.eval env cols.c := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_quotientComp_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).quotient_comp = Eval.eval env cols.quotient_comp := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_mulLower_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c_times_quotient_lower =
      Eval.eval env cols.c_times_quotient_lower := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_mulUpper_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c_times_quotient_upper =
      Eval.eval env cols.c_times_quotient_upper := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_ctq_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c_times_quotient =
      Eval.eval env cols.c_times_quotient := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_ctq_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 8) :
    (Eval.eval env cols).c_times_quotient[i] =
      Expression.eval env cols.c_times_quotient[i] := by
  rw [eval_divRemCols_ctq_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.c_times_quotient i hi).symm

@[circuit_norm] theorem eval_divRemCols_carry_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 8) :
    (Eval.eval env cols).carry[i] =
      Expression.eval env cols.carry[i] := by
  rw [eval_divRemCols_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.carry i hi).symm

@[circuit_norm] theorem eval_divRemCols_remainderComp_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).remainder_comp[i] =
      Expression.eval env cols.remainder_comp[i] := by
  rw [eval_divRemCols_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.remainder_comp i hi).symm

@[circuit_norm] theorem eval_divRemCols_remainder_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).remainder[i] =
      Expression.eval env cols.remainder[i] := by
  rw [eval_divRemCols_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.remainder i hi).symm

@[circuit_norm] theorem eval_divRemCols_quotient_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).quotient[i] =
      Expression.eval env cols.quotient[i] := by
  rw [eval_divRemCols_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.quotient i hi).symm

@[circuit_norm] theorem eval_divRemCols_absRemainder_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).abs_remainder[i] =
      Expression.eval env cols.abs_remainder[i] := by
  rw [eval_divRemCols_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.abs_remainder i hi).symm

@[circuit_norm] theorem eval_divRemCols_absC_getElem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).abs_c[i] =
      Expression.eval env cols.abs_c[i] := by
  rw [eval_divRemCols_verifier]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.abs_c i hi).symm

@[circuit_norm] theorem eval_divRemCols_remNeg_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).rem_neg = Eval.eval env cols.rem_neg := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isReal_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_real = Eval.eval env cols.is_real := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isRealNotWord_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_real_not_word =
      Eval.eval env cols.is_real_not_word := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isDiv_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_div = Eval.eval env cols.is_div := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isDivu_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_divu = Eval.eval env cols.is_divu := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isRem_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_rem = Eval.eval env cols.is_rem := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isRemu_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_remu = Eval.eval env cols.is_remu := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isDivw_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_divw = Eval.eval env cols.is_divw := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isRemw_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_remw = Eval.eval env cols.is_remw := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isDivuw_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_divuw = Eval.eval env cols.is_divuw := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_isRemuw_verifier
    {F : Type} [FiniteField F]
    (env : Environment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_remuw = Eval.eval env cols.is_remuw := by
  rw [eval_divRemCols_verifier]

@[circuit_norm] theorem eval_divRemCols_quotientComp {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).quotient_comp = Eval.eval env.toEnvironment cols.quotient_comp := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_c {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c = Eval.eval env.toEnvironment cols.c := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isRealNotWord {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_real_not_word =
      Eval.eval env.toEnvironment cols.is_real_not_word := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isReal {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_real = Eval.eval env.toEnvironment cols.is_real := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_mulLower {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c_times_quotient_lower =
      Eval.eval env.toEnvironment cols.c_times_quotient_lower := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_mulUpper {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c_times_quotient_upper =
      Eval.eval env.toEnvironment cols.c_times_quotient_upper := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_ctq {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).c_times_quotient =
      Eval.eval env.toEnvironment cols.c_times_quotient := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_carry {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).carry = Eval.eval env.toEnvironment cols.carry := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_remainderComp {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).remainder_comp = Eval.eval env.toEnvironment cols.remainder_comp := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_remainder {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).remainder = Eval.eval env.toEnvironment cols.remainder := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_quotient {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).quotient = Eval.eval env.toEnvironment cols.quotient := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_absRemainder {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).abs_remainder = Eval.eval env.toEnvironment cols.abs_remainder := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_absC {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).abs_c = Eval.eval env.toEnvironment cols.abs_c := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_remNeg {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).rem_neg = Eval.eval env.toEnvironment cols.rem_neg := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isDiv {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_div = Eval.eval env.toEnvironment cols.is_div := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isDivu {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_divu = Eval.eval env.toEnvironment cols.is_divu := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isRem {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_rem = Eval.eval env.toEnvironment cols.is_rem := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isRemu {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_remu = Eval.eval env.toEnvironment cols.is_remu := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isDivw {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_divw = Eval.eval env.toEnvironment cols.is_divw := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isRemw {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_remw = Eval.eval env.toEnvironment cols.is_remw := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isDivuw {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_divuw = Eval.eval env.toEnvironment cols.is_divuw := by
  rw [eval_divRemCols]

@[circuit_norm] theorem eval_divRemCols_isRemuw {F : Type} [FiniteField F]
    (env : ProverEnvironment F) (cols : DivRemCols (Expression F)) :
    (Eval.eval env cols).is_remuw = Eval.eval env.toEnvironment cols.is_remuw := by
  rw [eval_divRemCols]

set_option linter.unusedSectionVars false in
/-- Folded evaluator for the lower Mul block of `populatedRowAt`. -/
theorem eval_populatedRowAt_mulLower (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).c_times_quotient_lower =
      evaluatedMulBlock env.toEnvironment (offset + 8 + 4 + 4 + 4 + 4) := by
  rw [eval_divRemCols_mulLower, populatedRowAt_mulLower_eq, evaluatedMulBlock]

set_option linter.unusedSectionVars false in
/-- Folded evaluator for the upper Mul block of `populatedRowAt`. -/
theorem eval_populatedRowAt_mulUpper (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).c_times_quotient_upper =
      evaluatedMulBlock env.toEnvironment (offset + 8 + 4 + 4 + 4 + 4 + 45) := by
  rw [eval_divRemCols_mulUpper, populatedRowAt_mulUpper_eq, evaluatedMulBlock]

set_option linter.unusedSectionVars false in
/-- Evaluated opcode-flag projections of the explicit row layout.  Keeping these exact readback
lemmas avoids reducing `Vector.getElem` proof arguments in large parent goals. -/
theorem eval_populatedRowAt_isDiv (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_div = env.get offset := by
  rw [eval_divRemCols_isDiv]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isDivu (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_divu = env.get (offset + 1) := by
  rw [eval_divRemCols_isDivu]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isRem (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_rem = env.get (offset + 2) := by
  rw [eval_divRemCols_isRem]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isRemu (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_remu = env.get (offset + 3) := by
  rw [eval_divRemCols_isRemu]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isDivw (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_divw = env.get (offset + 4) := by
  rw [eval_divRemCols_isDivw]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isRemw (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_remw = env.get (offset + 5) := by
  rw [eval_divRemCols_isRemw]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isDivuw (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_divuw = env.get (offset + 6) := by
  rw [eval_divRemCols_isDivuw]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isRemuw (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_remuw = env.get (offset + 7) := by
  rw [eval_divRemCols_isRemuw]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isReal (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_real =
      Expression.eval env.toEnvironment input.is_real := by
  rw [eval_divRemCols_isReal]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_isRealNotWord (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).is_real_not_word =
      env.get (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) := by
  rw [eval_divRemCols_isRealNotWord]
  simp +instances only [populatedRowAt, circuit_norm]

set_option linter.unusedSectionVars false in
theorem eval_populatedRowAt_remNeg (env : ProverEnvironment (ZMod p))
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (populatedRowAt input offset)).rem_neg =
      env.get (offset + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 5) := by
  rw [eval_divRemCols_remNeg]
  simp +instances only [populatedRowAt, circuit_norm]

/-- `populatedRowAt` is exactly the output layout of the witness-only prefix. The proof is kept
opaque so consumers rewrite one small theorem constant instead of reducing the populate program. -/
theorem populateRow_output_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populateRow input).output offset = populatedRowAt input offset := by
  simp only [populateRow, populatedRowAt, Circuit.output, Circuit.bind_def, Circuit.pure_def,
    witnessVectorNative, CircuitNormalization.witnessNative_apply_eq, Operations.localLength,
    Nat.add_zero, show size Extracted.MulOperation = 45 from rfl]

/-- The constraint-only suffix of `main`. Its five calls are the public proof boundaries of the
chip: the two readers, the comparison cluster, the arithmetic core, and the destination write. -/
def constrainRow (input : Var Inputs (ZMod p)) (cols : Var DivRemCols (ZMod p)) :
    Circuit (ZMod p) (Var DivRemCols (ZMod p)) := do
  -- Readers (after the witness stream, extracted order — `E382` opcode + result-word write):
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * (65536 : Expression (ZMod p)), input.state.pc,
     cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
       + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
     cols.a[0], cols.a[1], cols.a[2], cols.a[3]⟩
  -- Assert the entire non-reader constraint set through the two whole-row `FormalAssertion`
  -- gadgets (each `localLength = 0`, so the witness prefix is
  -- the complete 217-cell row): `DivRemCompare.circuit` (IsEqualWord ×4 / IsZeroWord / Add ×2 /
  -- LtU / U16MSB ×7) and `DivRemCore.circuit` (MulOperation ×2 + the 8 product-glue asserts +
  -- `assertZeros (ownAsserts cols)` — `E13…E367`, `op_a_0`, incl. the binary gates like
  -- `is_real·(is_real-1)` = E355 — + the 32 gated byte-range pulls).
  assertion DivRemCompare.circuit (DivRemCompare.Inputs.ofCols cols)
  assertion DivRemCore.circuit cols
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the arithmetic so `isU64 a` (the flag-selected quotient/remainder output, byte-range-checked) discharges
  -- its requirement — breaking the old reader-circularity. Write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, cols.a, input.is_real⟩
  return cols

/-- `main` witnesses the Rust-layout row and then checks it through the chip's five auditable
constraint contracts. `populateRow` and `constrainRow` are plain definitional factoring, so this
has exactly the same flat operations, local length, and output as the former one-block definition. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var DivRemCols (ZMod p)) := do
  let cols ← populateRow input
  constrainRow input cols

/-- The constraint-only suffix returns the committed row unchanged.  Keeping this output identity
folded lets soundness reason about one opaque row instead of reducing all five subcircuits. -/
theorem main_output_eq_populateRow (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (main input).output offset = (populateRow input).output offset := by
  simp only [main, constrainRow, Circuit.output, Circuit.bind_def, subcircuitWithAssertion,
    assertion, Circuit.pure_def]

private theorem main_localLength_decompose (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (main input).localLength offset =
      (populateRow input).localLength offset +
        (constrainRow input ((populateRow input).output offset)).localLength
          (offset + (populateRow input).localLength offset) := by
  change (populateRow input >>= constrainRow input).localLength offset = _
  exact Circuit.bind_localLength_eq _ _ _

private theorem constrainRow_localLength_eq (input : Var Inputs (ZMod p))
    (cols : Var DivRemCols (ZMod p)) (offset : ℕ) :
    (constrainRow input cols).localLength offset = 0 := by
  simp only [constrainRow, Circuit.bind_localLength_eq, Circuit.pure_localLength_eq,
    subcircuitWithAssertion, assertion, Circuit.localLength, Operations.localLength,
    GeneralFormalCircuit.toSubcircuit_localLength, FormalAssertion.toSubcircuit_localLength,
    Readers.CPUState.circuit_localLength, Readers.RTypeReader.circuit_localLength,
    Readers.RegisterWrite.circuit_localLength, DivRemCompare.circuit_localLength,
    DivRemCore.circuit_localLength, Nat.add_zero]

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

/-- The folded witness prefix occupies exactly the 217 Rust-layout auxiliary columns.  This is
derived from the already-elaborated whole-chip length and the zero-length constraint suffix, so the
kernel never has to unfold the 217 nested witness binds merely to recover the offset. -/
@[circuit_norm] theorem populateRow_localLength_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (populateRow input).localLength offset = 217 := by
  have wholeLength := derivedLocalLengthEq input offset
  rw [main_localLength_decompose, constrainRow_localLength_eq, Nat.add_zero] at wholeLength
  exact wholeLength

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
