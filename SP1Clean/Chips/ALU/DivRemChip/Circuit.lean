import SP1Clean.Chips.ALU.DivRemChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.IsZeroWordOperation
import SP1Clean.Operations.IsEqualWordOperation
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.U16MSBOperation
import RISCV.Instructions

/-! # `DivRemChip` Clean circuit + `FormalAssertion`

Mirrors `SP1Clean/Chips/ALU/AddChip/Circuit.lean`'s canonical pattern,
but bundles 8 RV64IM division variants
(`div`/`divu`/`rem`/`remu`/`divw`/`remw`/`divuw`/`remuw`) — one-hot
selected by `aux_post.mode_flags[0..7]`. `Assertion.main` composes the
19-subcircuit graph that mirrors the upstream Rust `DivRemChip::eval`
(2× `MulOp.assertion`, 4× `IsEqualWordOp.assertion`, 1×
`IsZeroWordOp.assertion`, 2× `AddOp.assertion`, 1×
`LtUnsignedOp.assertion`, 7× `U16MSBOp.assertion`, plus
`CPUState.Gated.assertion` and `RTypeReader.Gated.assertion` flag-threaded
on `is_real`), followed by 5 chip-level binary gates and `op_a_0 = 0`.

`FormalSpec` lives at `SP1Clean/Chips/Spec.lean:613`; it is semantically
pure — the structural sub-Specs from CPUState/RTypeReader plus the 8
variant-gated `RV64.{div,divu,rem,remu,divw,remw,divuw,remuw}` equations
on `is_real = 1`. The mid-level sub-op Specs and the ~150 inline aux-gates
that wire them together are *not* exposed; they're implementation details
of the div/rem composition reconstructed via the chip's eventual
`iff_sp1`.

## Sorries (breadcrumbs)

Two sorries with explicit rationale, tracking the two architectural
barriers identified in CLEAN_FUTURE.md's "scope-fence" verdict for
DivRem:

- `elaborated.subcircuitsConsistent` — 19-subcircuit composition's
  consistency check exceeds the default heartbeat budget. Same escape
  hatch as `MulChip`/`ShiftLeftChip`/`ShiftRightChip`/`BitwiseChip`.
- `soundness` / `completeness` — chip-level `iff_sp1_full` doesn't
  exist for DivRem (no biconditional between the SP1 row `.allHold` and
  the BitVec-level FormalSpec). Forward direction can be discharged via
  the variant `_root_.<Variant>.correct_*` theorems in
  `SP1Chips/DivRem/{DivRem,DivuRemu,DivwRemw,DivuwRemuw}.lean`, but the
  composition requires `main` to emit all ~150 inline aux-gates that
  `_root_.DivRem.constraints` enforces (currently absent — Aggregate's
  main is incomplete). Backward direction is genuinely unprovable
  without strengthening `MulOperation` with an `iff_sp1_full` (per
  CLEAN_FUTURE.md Phase B6).

The per-variant Sail equivalence is *not* in `FormalSpec`; it's
derived externally via the 8 variant theorems in
`SP1Clean.DivRem.SailBridge`, each invoking the underlying
`_root_.<Variant>.correct_*` directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

-- `MulOp.assertion` requires `[Fact (2 ^ 24 < p)]` (carry-chain limb
-- bound); the section's `2 ^ 17 < p` is not enough.
variable [Fact (2 ^ 24 < p)]

/-- Clean-side chip circuit. Mirrors SP1 Rust's `DivRemChip::eval(builder, cols)`
sub-circuit graph: collapsed `CPUState.Gated` + `RTypeReader.Gated`
readers, plus 17 operation sub-circuits (`MulOp ×2`, `IsEqualWordOp ×4`,
`IsZeroWordOp`, `AddOp ×2`, `LtUnsignedOp`, `U16MSBOp ×7`), plus 5
chip-level binary gates and `op_a_0 = 0`.

The opcode delivered to `RTypeReader.Gated.assertion` is the one-hot
encoding `is_div*15 + is_divu*16 + ... + is_remuw*28`, dispatched from
`aux_post.mode_flags`. -/
@[reducible]
def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, op_a_write_value,
       b, c, quotient, quotient_comp, remainder_comp, remainder,
       abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient,
       c_times_quotient_lower, c_times_quotient_upper,
       aux_post,
       c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity,
       adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  -- Mode-flag aliases mirroring SP1's `E0..E11` aggregates.
  let is_div   : Expression (ZMod p) := aux_post.mode_flags[0]
  let is_divu  : Expression (ZMod p) := aux_post.mode_flags[1]
  let is_rem_f : Expression (ZMod p) := aux_post.mode_flags[2]
  let is_remu  : Expression (ZMod p) := aux_post.mode_flags[3]
  let is_divw  : Expression (ZMod p) := aux_post.mode_flags[4]
  let is_remw  : Expression (ZMod p) := aux_post.mode_flags[5]
  let is_divuw : Expression (ZMod p) := aux_post.mode_flags[6]
  let is_remuw : Expression (ZMod p) := aux_post.mode_flags[7]
  let e92      : Expression (ZMod p) := is_div + is_rem_f                        -- E92
  let e93      : Expression (ZMod p) := is_divu + is_remu                        -- E93
  let opcode_e : Expression (ZMod p) :=
    is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
      + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28
  -- Reader block: eval_cpu_state + eval_r_type (collapsed via Gated).
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
  -- CS0: c_times_quotient_lower = quotient_comp × c (always pure mul gated by is_real).
  SP1Clean.MulOp.assertion
    (⟨#v[c_times_quotient[0], c_times_quotient[1],
         c_times_quotient[2], c_times_quotient[3]],
       quotient_comp, c,
       c_times_quotient_lower.carry, c_times_quotient_lower.product,
       c_times_quotient_lower.b_lower_byte.low_bytes,
       c_times_quotient_lower.c_lower_byte.low_bytes,
       c_times_quotient_lower.b_msb, c_times_quotient_lower.c_msb,
       c_times_quotient_lower.product_msb.msb,
       c_times_quotient_lower.b_sign_extend,
       c_times_quotient_lower.c_sign_extend,
       is_real, 0, 0, 0, 0⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  -- CS1: c_times_quotient_upper = quotient_comp × c (variant-gated MULH/MULHU).
  SP1Clean.MulOp.assertion
    (⟨#v[c_times_quotient[4], c_times_quotient[5],
         c_times_quotient[6], c_times_quotient[7]],
       quotient_comp, c,
       c_times_quotient_upper.carry, c_times_quotient_upper.product,
       c_times_quotient_upper.b_lower_byte.low_bytes,
       c_times_quotient_upper.c_lower_byte.low_bytes,
       c_times_quotient_upper.b_msb, c_times_quotient_upper.c_msb,
       c_times_quotient_upper.product_msb.msb,
       c_times_quotient_upper.b_sign_extend,
       c_times_quotient_upper.c_sign_extend,
       0, e92, e93, 0, 0⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  -- CS2: is_overflow_b — op_b == -2^63 (little-endian: 0, 0, 0, 32768).
  SP1Clean.IsEqualWordOp.assertion
    (⟨adapter.op_b_memory.prev_value, #v[0, 0, 0, 32768],
       #v[aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].inverse],
       #v[aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].result],
       aux_post.is_overflow_b.is_diff_zero.is_zero_first_half,
       aux_post.is_overflow_b.is_diff_zero.is_zero_second_half,
       aux_post.is_overflow_b.is_diff_zero.result⟩ :
      Var SP1Clean.IsEqualWordOp.Inputs (ZMod p))
  -- CS3: is_overflow_c — op_c == -1 (all-ones).
  SP1Clean.IsEqualWordOp.assertion
    (⟨adapter.op_c_memory.prev_value, #v[65535, 65535, 65535, 65535],
       #v[aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].inverse],
       #v[aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].result],
       aux_post.is_overflow_c.is_diff_zero.is_zero_first_half,
       aux_post.is_overflow_c.is_diff_zero.is_zero_second_half,
       aux_post.is_overflow_c.is_diff_zero.result⟩ :
      Var SP1Clean.IsEqualWordOp.Inputs (ZMod p))
  -- CS4: is_overflow_b (32-bit check) — low 2 limbs of op_b == -2^31.
  --      Reuses the same is_overflow_b witness columns as CS2.
  SP1Clean.IsEqualWordOp.assertion
    (⟨#v[adapter.op_b_memory.prev_value[0], adapter.op_b_memory.prev_value[1], 0, 0],
       #v[0, 32768, 0, 0],
       #v[aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].inverse],
       #v[aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].result],
       aux_post.is_overflow_b.is_diff_zero.is_zero_first_half,
       aux_post.is_overflow_b.is_diff_zero.is_zero_second_half,
       aux_post.is_overflow_b.is_diff_zero.result⟩ :
      Var SP1Clean.IsEqualWordOp.Inputs (ZMod p))
  -- CS5: is_overflow_c (32-bit check) — low 2 limbs of op_c == -1 (32-bit).
  --      Reuses the same is_overflow_c witness columns as CS3.
  SP1Clean.IsEqualWordOp.assertion
    (⟨#v[adapter.op_c_memory.prev_value[0], adapter.op_c_memory.prev_value[1], 0, 0],
       #v[65535, 65535, 0, 0],
       #v[aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].inverse],
       #v[aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].result],
       aux_post.is_overflow_c.is_diff_zero.is_zero_first_half,
       aux_post.is_overflow_c.is_diff_zero.is_zero_second_half,
       aux_post.is_overflow_c.is_diff_zero.result⟩ :
      Var SP1Clean.IsEqualWordOp.Inputs (ZMod p))
  -- CS6: is_c_0 — divisor c == 0.
  SP1Clean.IsZeroWordOp.assertion
    (⟨c,
       #v[aux_post.is_c_0.is_zero_limb[0].inverse,
          aux_post.is_c_0.is_zero_limb[1].inverse,
          aux_post.is_c_0.is_zero_limb[2].inverse,
          aux_post.is_c_0.is_zero_limb[3].inverse],
       #v[aux_post.is_c_0.is_zero_limb[0].result,
          aux_post.is_c_0.is_zero_limb[1].result,
          aux_post.is_c_0.is_zero_limb[2].result,
          aux_post.is_c_0.is_zero_limb[3].result],
       aux_post.is_c_0.is_zero_first_half,
       aux_post.is_c_0.is_zero_second_half,
       aux_post.is_c_0.result⟩ :
      Var SP1Clean.IsZeroWordOp.Inputs (ZMod p))
  -- CS7: c_neg_operation — c + abs_c = neg_c (for the absolute-value
  --      computation in signed divrem).
  SP1Clean.AddOp.assertion
    (⟨c, abs_c, aux_post.c_neg_operation.value, abs_c_alu_event⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- CS8: rem_neg_operation — remainder_comp + abs_remainder.
  SP1Clean.AddOp.assertion
    (⟨remainder_comp, abs_remainder, aux_post.rem_neg_operation.value, abs_rem_alu_event⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- CS9: remainder_lt_operation — abs_remainder < max_abs_c_or_1.
  SP1Clean.LtUnsignedOp.assertion
    (⟨abs_remainder, max_abs_c_or_1,
       aux_post.remainder_lt_operation.u16_compare_operation.bit,
       aux_post.remainder_lt_operation.u16_flags,
       aux_post.remainder_lt_operation.not_eq_inv,
       aux_post.remainder_lt_operation.comparison_limbs⟩ :
      Var SP1Clean.LtUnsignedOp.Inputs (ZMod p))
  -- CS10-CS16: 7× U16MSB sign-bit witnesses (b/c/rem at high limb and
  -- second-high limb, plus quotient at second-high). SP1 emits the
  -- selector mults (`Main[239]` for the 64-bit family, `E2 = is_word`
  -- for the 32-bit family); Clean's `U16MSBOp.assertion` is the
  -- unconditional form (no `U16MSBOp.Gated.assertion` ships yet).
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_b_memory.prev_value[3], aux_post.b_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_c_memory.prev_value[3], aux_post.c_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨remainder[3], aux_post.rem_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_b_memory.prev_value[1], aux_post.b_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_c_memory.prev_value[1], aux_post.c_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨remainder[1], aux_post.rem_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨quotient[1], aux_post.quot_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- Chip-level scalar gates: binary flags + op_a_0 zero.
  c_neg             * (c_neg             - 1) === 0
  abs_c_alu_event   * (abs_c_alu_event   - 1) === 0
  abs_rem_alu_event * (abs_rem_alu_event - 1) === 0
  is_real           * (is_real           - 1) === 0
  remainder_check_multiplicity * (remainder_check_multiplicity - 1) === 0
  -- Suppress the unused-binding warning for `b` — its constraints are
  -- emitted by `_root_.DivRem.constraints` but live outside the
  -- sub-circuit graph (the ~150 inline arithmetic wiring gates not yet
  -- mirrored here).
  let _ := b
  adapter.op_a_0 === 0

set_option maxHeartbeats 6400000 in
-- 6.4M heartbeats: 19 sub-circuit calls (2 readers + 2 MulOp + 4
-- IsEqualWord + IsZeroWord + 2 AddOp + LtUnsigned + 7 U16MSB) push
-- `localLength_eq` synthesis well past the default. The
-- `subcircuitsConsistent` field is sorry'd same as `MulChip` /
-- `ShiftLeftChip` / `ShiftRightChip` — the constraint structure is
-- legitimate; lining up Clean's internal consistency check across 19
-- sub-circuits is a tractable but multi-hour proof outside the scope
-- of this AddChip-shape alignment PR.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by sorry

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to
`is_real`. The `is_real = 1` precondition restricts the FormalAssertion
to non-padding rows — matching AddChip's `Assumptions`. -/
def Assumptions (cols : DivRemCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧ cols.is_real = 1

-- The unified chip Spec `SP1Clean.DivRem.Assertion.FormalSpec` is defined
-- in `Spec.lean:613` (already in scope in this `Assertion` namespace via
-- the transitive `SP1Clean.Chips.Spec` import). Unlike AddChip — whose
-- `FormalSpec` lives at the `SP1Clean.Add` level and is re-exported here
-- via an `abbrev` — DivRem's is already inside `Assertion`, so the
-- unqualified `FormalSpec` below resolves directly to it.

/-- Soundness — breadcrumbed. Forward direction requires the variant
`_root_.<Variant>.correct_*` lemmas in
`SP1Chips/DivRem/{DivRem,DivuRemu,DivwRemw,DivuwRemuw}.lean`, which
take the full SP1 row `.allHold` as input. Clean's `circuit_proof_start`
exposes only the 19 sub-circuit Specs + 5 chip-level scalar gates;
reconstructing the SP1 row's `.allHold` from these requires the ~150
inline aux-gates that `_root_.DivRem.constraints` emits to be present
in `main` — they currently aren't. Closing this requires either:
(a) adding ~150 inline gate emissions to `main` (faithful Rust
mirror, ~200 LoC), or (b) shipping a chip-level `iff_sp1_full` per
CLEAN_FUTURE.md Phase B6. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

/-- Completeness — breadcrumbed. Backward direction (`FormalSpec → allHold`)
is structurally unprovable for DivRem without a chip-level `iff_sp1_full`,
since `FormalSpec` carries only the 8 semantic `RV64.{div,…}` equations
and not the 246-column witness layout (carry chains, MulOp byte
decompositions, sign-extend wiring, abs-value witnesses). `MulOperation`
ships only `of_sp1` (forward); `LtOperationUnsigned` lacks `iff_sp1_full`.
Per CLEAN_FUTURE.md, DivRem is a "scope-fence" case — completeness is
not in scope until upstream operations strengthen. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

-- `Fact (2 ^ 24 < p)` is transitive via `MulOp.assertion`'s requirement
-- in `Assertion.elaborated`.
def assertion [Fact (2 ^ 24 < p)] : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRem
