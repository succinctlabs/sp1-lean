import SP1Clean.Specs.Chip
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.IsEqualWordOperation.Formal
import SP1Clean.Operations.IsZeroWordOperation.Formal
import SP1Clean.Operations.AddOperation.Formal
import SP1Clean.Operations.U16MSBOperation.Formal
import SP1Clean.Operations.LtOperationUnsigned.Formal
import SP1Clean.Chips.DivRemChip.OwnAsserts
import SP1Clean.Readers.CPUState
import SP1Clean.Readers.RTypeReader
import SP1Clean.Foundations.Channels
import SP1Clean.Extracted.DivRemChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `DivRem` chip row as a `GeneralFormalCircuit`

`DIV`/`DIVU`/`REM`/`REMU`/`DIVW`/`REMW`/`DIVUW`/`REMUW`: flag-gated `Spec` (RV64 div/rem identities on
`cols.a`) in `Specs/Chip.lean`; output is the extracted `DivRemCols` (246 columns).

`main` composes the full constraint set: two `MulOperation` `c·quotient` products (low/high),
`IsEqualWordOperation`×4 (overflow), `IsZeroWordOperation` (divide-by-zero), `AddOperation`×2 (negation),
`LtOperationUnsigned` (remainder range), `U16MSBOperation`×7 (sign bits), `CPUState`/`RTypeReader`
readers, and the chip's own assertZero tail (`ownAsserts`). Soundness is proved; completeness is a
deferred `sorry`. (`Assumptions`/soundness/completeness/`circuit` in `Formal`.) -/

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

/-- All-zero `fromElements` placeholder for any column block. -/
@[irreducible] def zc {α : TypeMap} [ProvableType α] : Var α (ZMod p) :=
  ProvableType.fromElements (F := Expression (ZMod p)) (.replicate _ 0)

/-- Emit a list of zero-asserts in one circuit bind (`es.map .assert`). Used for `ownAsserts cols`. -/
def assertZeros (es : List (Expression (ZMod p))) : Circuit (ZMod p) Unit :=
  fun _ => ((), es.map (fun e => .assert e))

-- `circuit_norm` lemmas so `ElaboratedCircuit` obligations close on `assertZeros es` without unfolding
-- the opaque `ownAsserts cols`: a list of `.assert` ops contributes 0 length, 0 subcircuit offsets, no channels.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_map_assert (es : List (Expression (ZMod p))) :
    Operations.localLength (es.map fun e => (Operation.assert e)) = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma forAll_map_assert (offset : ℕ) (cond : Condition (ZMod p))
    (es : List (Expression (ZMod p))) :
    Operations.forAll offset cond (es.map fun e => (Operation.assert e))
      ↔ ∀ e ∈ es, cond.assert offset e := by
  induction es with
  | nil => simp [Operations.forAll]
  | cons e es ih =>
    simp only [List.map_cons, Operations.forAll, ih, List.mem_cons, forall_eq_or_imp]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma forAllNoOffset_map_assert (cond : ConditionNoOffset (ZMod p))
    (es : List (Expression (ZMod p))) :
    Operations.forAllNoOffset cond (es.map fun e => (Operation.assert e))
      ↔ ∀ e ∈ es, cond.assert e := by
  induction es with
  | nil => simp [Operations.forAllNoOffset]
  | cons e es ih =>
    simp only [List.map_cons, Operations.forAllNoOffset, ih, List.mem_cons, forall_eq_or_imp]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma shallowChannels_map_assert (es : List (Expression (ZMod p))) :
    Operations.shallowChannels (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.shallowChannels, List.map_cons]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma subChannelsG_map_assert (es : List (Expression (ZMod p))) :
    Operations.subcircuitChannelsWithGuarantees (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.subcircuitChannelsWithGuarantees, List.map_cons]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma subChannelsR_map_assert (es : List (Expression (ZMod p))) :
    Operations.subcircuitChannelsWithRequirements (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.subcircuitChannelsWithRequirements, List.map_cons]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma interactions_map_assert (es : List (Expression (ZMod p))) :
    Operations.interactions (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.interactions, List.map_cons, ih]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma shallowInteractions_map_assert (es : List (Expression (ZMod p))) :
    Operations.shallowInteractions (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Operations.shallowInteractions, List.map_cons, ih]

set_option maxHeartbeats 16000000 in
/-- `main` — composes all sub-gadgets in `Extracted/DivRemChip.lean` `asserts`/`interactions` order:
the two `c_times_quotient` `MulOperation`s (`lower`: low-64, gated `is_mul = is_real`; `upper`:
high-64, gated `is_mulh = is_div + is_rem` signed / `is_mulhu = is_divu + is_remu` unsigned), the four
`IsEqualWordOperation` overflow checks, `IsZeroWordOperation`, two `AddOperation` negations,
`LtOperationUnsigned`, seven `U16MSBOperation` sign-bit gadgets, the `CPUState`/`RTypeReader` readers,
the chip's own `=== 0` asserts (`ownAsserts`), and the byte-range tail. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var DivRemCols (ZMod p)) := do
  let flags ← witnessVector 8 (fun _ => (#v[0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod p) 8))
  let is_div := flags[0]; let is_divu := flags[1]; let is_rem := flags[2]; let is_remu := flags[3]
  let is_divw := flags[4]; let is_remw := flags[5]; let is_divuw := flags[6]; let is_remuw := flags[7]
  let quotient_comp ← witnessVector 4 (fun _ => (#v[0, 0, 0, 0] : Vector (ZMod p) 4))
  let a ← witnessVector 4 (fun _ => (#v[0, 0, 0, 0] : Vector (ZMod p) 4))
  -- (1,2) The two `c_times_quotient` products of `quotient_comp × c`. Witness each `MulOperation`
  -- column struct via `populate`, then compose as a Clean `assertion` gated by `is_real`
  -- (`divrem/mod.rs:721`). `mul_lower` = low product (`is_mul = is_real`); `mul_upper` = high product
  -- (`is_mulh = is_div + is_rem`, `is_mulhu = is_divu + is_remu`). Both have `is_mulw = 0`, so
  -- `is_mulw → is_real` is vacuous; the `isU64 quotient_comp` precondition is vacuous on padding rows.
  let mul_lower ← ProvableType.witness (fun env =>
    MulOperation.populate
      #v[env quotient_comp[0], env quotient_comp[1], env quotient_comp[2], env quotient_comp[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]
      0 0 0)
  let mul_upper ← ProvableType.witness (fun env =>
    MulOperation.populate
      #v[env quotient_comp[0], env quotient_comp[1], env quotient_comp[2], env quotient_comp[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]
      (env is_div + env is_rem) 0 0)
  assertion MulOperation.circuit
    ⟨quotient_comp, input.op_c_val, mul_lower, input.is_real, input.is_real, 0, 0, 0, 0⟩
  assertion MulOperation.circuit
    ⟨quotient_comp, input.op_c_val, mul_upper, input.is_real, 0, is_div + is_rem, is_divu + is_remu, 0, 0⟩
  -- (3-7) The two `IsEqualWordOperation` overflow checks (`is_overflow_b` vs `i64::MIN`,
  -- `is_overflow_c` vs `-1`), each asserted twice — full-word @ `is_real_not_word`, low-half @ `E2`
  -- (word-variant gate) — and `IsZeroWordOperation` on `c`. Nested cols witnessed flat via
  -- `fromElements (F := …)`. `E2` = word-variant flag sum; `irnw` = `is_real_not_word = is_real·(1-E2)`.
  let e2 := is_divw + is_remw + is_divuw + is_remuw
  -- witnessed scalar sign/gate columns + the `c_times_quotient`/`carry` byte vectors (placeholder
  -- values; pinned by the own-asserts `E13/E15/…` and the carry chain `E121…E151`).
  let scal ← witnessVector 7 (fun _ => .replicate 7 0)
  let is_overflow := scal[0]; let b_neg := scal[1]; let b_neg_not_overflow := scal[2]
  let b_not_neg_not_overflow := scal[3]; let is_real_not_word := scal[4]
  let rem_neg := scal[5]; let c_neg := scal[6]
  let c_times_quotient ← witnessVector 8 (fun _ => .replicate 8 0)
  let carry ← witnessVector 8 (fun _ => .replicate 8 0)
  -- Link `c_times_quotient` to the two `MulOperation` gadgets' product bytes: the low 64 (limbs 0..3)
  -- to `mul_lower`'s bytes 0..7, the high 64 (limbs 4..7) to `mul_upper`'s bytes 8..15. SP1 expresses
  -- this by passing `c_times_quotient` as the Mul *result slot*; our native `MulOperation` reconstructs
  -- its `resultWord` internally (it does not take the result as input), so we glue here — without this
  -- the two Mul `Spec`s are dangling and the Euclidean identity `c_times_quotient = quotient_comp · c`
  -- is underivable. (Each glue is an `assertZero`, contributing 0 to `localLength`.) `mul_lower`'s
  -- `resultWord` is unconditionally its bytes 0..7 (its high flags are 0); `mul_upper`'s is bytes 8..15
  -- on the 64-bit variants (`is_mulh`/`is_mulhu` set).
  let c256 : Expression (ZMod p) := 256
  c_times_quotient[0] === mul_lower.product[0] + mul_lower.product[1] * c256
  c_times_quotient[1] === mul_lower.product[2] + mul_lower.product[3] * c256
  c_times_quotient[2] === mul_lower.product[4] + mul_lower.product[5] * c256
  c_times_quotient[3] === mul_lower.product[6] + mul_lower.product[7] * c256
  c_times_quotient[4] === mul_upper.product[8] + mul_upper.product[9] * c256
  c_times_quotient[5] === mul_upper.product[10] + mul_upper.product[11] * c256
  c_times_quotient[6] === mul_upper.product[12] + mul_upper.product[13] * c256
  c_times_quotient[7] === mul_upper.product[14] + mul_upper.product[15] * c256
  let irnw := is_real_not_word
  let bpv := input.adapter.op_b_memory.prev_value
  let cpv := input.adapter.op_c_memory.prev_value
  let w_ovb ← witnessVector 11 (fun _ => .replicate 11 0)
  let w_ovc ← witnessVector 11 (fun _ => .replicate 11 0)
  let w_is_c_0 ← witnessVector 11 (fun _ => .replicate 11 0)
  assertion IsEqualWordOperation.circuit
    ⟨#v[bpv[0], bpv[1], bpv[2], bpv[3]], #v[0, 0, 0, 32768],
     fromElements (F := Expression (ZMod p)) w_ovb, irnw⟩
  assertion IsEqualWordOperation.circuit
    ⟨#v[cpv[0], cpv[1], cpv[2], cpv[3]], #v[65535, 65535, 65535, 65535],
     fromElements (F := Expression (ZMod p)) w_ovc, irnw⟩
  assertion IsEqualWordOperation.circuit
    ⟨#v[bpv[0], bpv[1], 0, 0], #v[0, 32768, 0, 0],
     fromElements (F := Expression (ZMod p)) w_ovb, e2⟩
  assertion IsEqualWordOperation.circuit
    ⟨#v[cpv[0], cpv[1], 0, 0], #v[65535, 65535, 0, 0],
     fromElements (F := Expression (ZMod p)) w_ovc, e2⟩
  assertion IsZeroWordOperation.circuit
    ⟨input.op_c_val, fromElements (F := Expression (ZMod p)) w_is_c_0, input.is_real⟩
  -- (8-10) Two `AddOperation` two's-complement negations (`|c|`, `|remainder|`), and
  -- `LtOperationUnsigned` (`|remainder| < max(|c|,1)`). `LtOperationUnsigned` witnesses its comparison
  -- columns here via `populate_*`, then is composed as a Clean `assertion` gated by
  -- `remainder_check_multiplicity` (`is_real·(1 − is_c_0)`).
  let abs_c ← witnessVector 4 (fun _ => .replicate 4 0)
  let abs_remainder ← witnessVector 4 (fun _ => .replicate 4 0)
  let remainder_comp ← witnessVector 4 (fun _ => .replicate 4 0)
  let max_abs_c_or_1 ← witnessVector 4 (fun _ => .replicate 4 0)
  let w_cneg ← witnessVector 4 (fun _ => .replicate 4 0)
  let w_rneg ← witnessVector 4 (fun _ => .replicate 4 0)
  let misc ← witnessVector 3 (fun _ => .replicate 3 0)
  let abs_c_alu_event := misc[0]; let abs_rem_alu_event := misc[1]
  let remainder_check_multiplicity := misc[2]
  assertion AddOperation.circuit ⟨input.op_c_val, abs_c, ⟨w_cneg⟩, abs_c_alu_event⟩
  assertion AddOperation.circuit ⟨remainder_comp, abs_remainder, ⟨w_rneg⟩, abs_rem_alu_event⟩
  let cl ← witnessVector 2 (fun env =>
    LtOperationUnsigned.comparisonLimbsWitness
      #v[env abs_remainder[0], env abs_remainder[1], env abs_remainder[2], env abs_remainder[3]]
      #v[env max_abs_c_or_1[0], env max_abs_c_or_1[1], env max_abs_c_or_1[2], env max_abs_c_or_1[3]])
  let f ← witnessVector 4 (fun env =>
    LtOperationUnsigned.flagsWitness
      #v[env abs_remainder[0], env abs_remainder[1], env abs_remainder[2], env abs_remainder[3]]
      #v[env max_abs_c_or_1[0], env max_abs_c_or_1[1], env max_abs_c_or_1[2], env max_abs_c_or_1[3]])
  let not_eq_inv ← witnessVector 1 (fun env =>
    LtOperationUnsigned.notEqInvWitness
      #v[env abs_remainder[0], env abs_remainder[1], env abs_remainder[2], env abs_remainder[3]]
      #v[env max_abs_c_or_1[0], env max_abs_c_or_1[1], env max_abs_c_or_1[2], env max_abs_c_or_1[3]])
  let bit ← witnessVector 1 (fun env => #v[U16CompareOperation.populate_bit (env cl[0]) (env cl[1])])
  let lt_out : Var Extracted.LtOperationUnsigned (ZMod p) := ⟨⟨bit[0]⟩, f, not_eq_inv[0], cl⟩
  assertion LtOperationUnsigned.circuit
    ⟨abs_remainder, max_abs_c_or_1, lt_out, remainder_check_multiplicity⟩
  -- (11-17) Seven `U16MSBOperation` sign-bit extractions — b/c/remainder high u16 (@ `irnw`),
  -- b/c/remainder/quotient low-half-high u16 (@ `E2`).
  let remainder ← witnessVector 4 (fun _ => .replicate 4 0)
  let quotient ← witnessVector 4 (fun _ => .replicate 4 0)
  let w_bmsb ← witnessVector 1 (fun _ => .replicate 1 0)
  let w_cmsb ← witnessVector 1 (fun _ => .replicate 1 0)
  let w_remmsb ← witnessVector 1 (fun _ => .replicate 1 0)
  let w_quotmsb ← witnessVector 1 (fun _ => .replicate 1 0)
  assertion U16MSBOperation.circuit ⟨bpv[3], ⟨w_bmsb[0]⟩, irnw⟩
  assertion U16MSBOperation.circuit ⟨cpv[3], ⟨w_cmsb[0]⟩, irnw⟩
  assertion U16MSBOperation.circuit ⟨remainder[3], ⟨w_remmsb[0]⟩, irnw⟩
  assertion U16MSBOperation.circuit ⟨bpv[1], ⟨w_bmsb[0]⟩, e2⟩
  assertion U16MSBOperation.circuit ⟨cpv[1], ⟨w_cmsb[0]⟩, e2⟩
  assertion U16MSBOperation.circuit ⟨remainder[1], ⟨w_remmsb[0]⟩, e2⟩
  assertion U16MSBOperation.circuit ⟨quotient[1], ⟨w_quotmsb[0]⟩, e2⟩
  -- Readers (after the arithmetic gadgets, extracted order — `E382` opcode + result-word write):
  assertion Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  assertion Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * (65536 : Expression (ZMod p)), input.state.pc,
     is_divu * 16 + is_remu * 18 + is_div * 15 + is_rem * 17 + is_divw * 25 + is_remw * 27
       + is_divuw * 26 + is_remuw * 28,
     a[0], a[1], a[2], a[3]⟩
  -- Assemble `DivRemCols`, then emit the chip's own assertZero constraints (`E13…E367`, `op_a_0`, incl.
  -- the binary gates like `is_real·(is_real-1)` = E355) via `ownAsserts`.
  let cols : Var DivRemCols (ZMod p) := ⟨input.state, input.adapter, a, input.op_b_val, input.op_c_val,
    quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c,
    max_abs_c_or_1, c_times_quotient, mul_lower, mul_upper, ⟨w_cneg⟩, ⟨w_rneg⟩, lt_out,
    carry, fromElements (F := Expression (ZMod p)) w_is_c_0,
    is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw,
    is_overflow, fromElements (F := Expression (ZMod p)) w_ovb,
    fromElements (F := Expression (ZMod p)) w_ovc,
    ⟨w_bmsb[0]⟩, ⟨w_remmsb[0]⟩, ⟨w_cmsb[0]⟩, ⟨w_quotmsb[0]⟩,
    b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg, c_neg,
    abs_c_alu_event, abs_rem_alu_event, input.is_real, remainder_check_multiplicity⟩
  assertZeros (ownAsserts cols)
  -- Byte-range tail (opcode `Range` = 6, all gated `is_real`): the 8 carry-chain u16 limbs
  -- (`E123…E151`) and `abs_c`/`abs_remainder`/`quotient`/`remainder`/`c_times_quotient` limbs.
  -- `rn := rem_neg·65535` (`E120`) is the high-limb addend.
  let rn : Expression (ZMod p) := rem_neg * (65535 : Expression (ZMod p))
  let e123 : Expression (ZMod p) := c_times_quotient[0] + remainder_comp[0] - carry[0] * (65536 : Expression (ZMod p))
  let e127 : Expression (ZMod p) := c_times_quotient[1] + remainder_comp[1] - carry[1] * (65536 : Expression (ZMod p)) + carry[0]
  let e131 : Expression (ZMod p) := c_times_quotient[2] + remainder_comp[2] - carry[2] * (65536 : Expression (ZMod p)) + carry[1]
  let e135 : Expression (ZMod p) := c_times_quotient[3] + remainder_comp[3] - carry[3] * (65536 : Expression (ZMod p)) + carry[2]
  let e139 : Expression (ZMod p) := c_times_quotient[4] + rn - carry[4] * (65536 : Expression (ZMod p)) + carry[3]
  let e143 : Expression (ZMod p) := c_times_quotient[5] + rn - carry[5] * (65536 : Expression (ZMod p)) + carry[4]
  let e147 : Expression (ZMod p) := c_times_quotient[6] + rn - carry[6] * (65536 : Expression (ZMod p)) + carry[5]
  let e151 : Expression (ZMod p) := c_times_quotient[7] + rn - carry[7] * (65536 : Expression (ZMod p)) + carry[6]
  let g := input.is_real
  byteChannel.pullIf g (⟨6, e123, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e127, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e131, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e135, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e139, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e143, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e147, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, e151, 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_c[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_c[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_c[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_c[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_remainder[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_remainder[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_remainder[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, abs_remainder[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, quotient[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, quotient[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, quotient[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, quotient[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, remainder[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, remainder[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, remainder[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, remainder[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[0], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[2], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[3], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[4], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[5], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[6], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf g (⟨6, c_times_quotient[7], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  -- Two extra `e2`-gated u16 range checks on `remainder[1]`/`quotient[1]`: the word-variant MSB
  -- gadgets need `< 2^16` even on padding word rows (`is_real = 0`, word flag set), where the main
  -- `is_real`-gated checks are off. SP1's `eval_msb` relies on the operand's own gated range check instead.
  byteChannel.pullIf e2 (⟨6, remainder[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf e2 (⟨6, quotient[1], 16, 0⟩ : ByteRow (Expression (ZMod p)))
  return cols

set_option maxHeartbeats 16000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs DivRemCols main where
  -- MulOperation FormalAssertions witness 45 cols each; total: 209.
  localLength _ := 209
  localLength_eq := by simp +arith [circuit_norm, main, AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit, LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit, U16MSBOperation.circuit, assertZeros]
  subcircuitsConsistent := by simp only [circuit_norm, main, AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit, LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit, U16MSBOperation.circuit, assertZeros]; try omega
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements :=
    [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw]
  -- the ~30 upstream `pullIf` unfold/refolds put this past simp's default step budget post-#398
  channelsLawful := by simp (maxSteps := 1000000) [circuit_norm, main, AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit, LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit, U16MSBOperation.circuit, assertZeros]

end SP1Clean.DivRemChip
