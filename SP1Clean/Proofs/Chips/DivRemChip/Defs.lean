import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.MulOperation
import SP1Clean.Proofs.Operations.IsEqualWordOperation.Formal
import SP1Clean.Proofs.Operations.IsZeroWordOperation.Formal
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal
import SP1Clean.Proofs.Chips.DivRemChip.OwnAsserts
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

/-- Prover-side row well-formedness: the register-read `isU64`s, the `is_real` binary selector, the
honest `"div_rem_flags"` hint (each flag binary, the sum `= 1` **unconditionally** — E367 is ungated,
and SP1's padding rows carry `is_divu = 1`), the **padding pin** (an `is_real = 0` row is exactly
SP1's "0 divided by 1" template: zero `b` read, `c` read `= Word(1)`, the `is_divu` flag — this is
what makes the ungated lower glue and the flag-gated shape asserts dischargeable off-gate),
`op_a_0 = 0`, the CPUState clock bounds, and the three register-access timestamp `Spec`s (mirrors
`MulChip.ProverAssumptions` — R-type, no immediate machinery). Lives in `Defs` (not `Formal`) so the
`Completeness/` split files can import it without a cycle. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
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

-- `interactionsWith` (per-channel filter) of a list of pure `.assert` ops is empty — lets the
-- `exposedChannels_eq` State-bus descent close over `assertZeros (ownAsserts cols)` without unfolding.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma interactionsWith_map_assert (channel : RawChannel (ZMod p))
    (es : List (Expression (ZMod p))) :
    Operations.interactionsWith channel (es.map fun e => (Operation.assert e)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [List.map_cons, Operations.interactionsWith_assert, ih]

set_option maxHeartbeats 16000000 in
/-- `main` — composes all sub-gadgets in `Extracted/DivRemChip.lean` `asserts`/`interactions` order:
the two `c_times_quotient` `MulOperation`s (`lower`: low-64, gated `is_mul = is_real`; `upper`:
high-64, gated `is_mulh = is_div + is_rem` signed / `is_mulhu = is_divu + is_remu` unsigned), the four
`IsEqualWordOperation` overflow checks, `IsZeroWordOperation`, two `AddOperation` negations,
`LtOperationUnsigned`, seven `U16MSBOperation` sign-bit gadgets, the `CPUState`/`RTypeReader` readers,
the chip's own `=== 0` asserts (`ownAsserts`), and the byte-range tail. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var DivRemCols (ZMod p)) := do
  let bpv := input.adapter.op_b_memory.prev_value
  let cpv := input.adapter.op_c_memory.prev_value
  -- The honest variant flags from the `"div_rem_flags"` `ProverHint` (one-hot on real rows;
  -- the key's absence defaults to the `is_divu = 1` padding template — `Populate.hintFlags`).
  let flags ← witnessVector 8 (fun env => hintFlags env.hint)
  let is_div := flags[0]; let is_divu := flags[1]; let is_rem := flags[2]; let is_remu := flags[3]
  let is_divw := flags[4]; let is_remw := flags[5]; let is_divuw := flags[6]; let is_remuw := flags[7]
  let quotient_comp ← witnessVector 4 (fun env =>
    populateQuotComp #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let a ← witnessVector 4 (fun env =>
    populateA #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- The arithmetic **operands** `b`/`c` — committed columns distinct from the raw register reads
  -- (`adapter.op_b/c_memory.prev_value`). The chip's own-asserts E20–E47 tie them to the reads: equal to the
  -- read for the 64-bit variants, the sign/zero-extension of the low 32 bits for the W-variants (`b[i] =
  -- read[i]·(1-isword) + b_neg·isword·0xFFFF`). Witnessed here (before the `MulOperation`s, which multiply by
  -- `c`); populated honestly (`bComp`/`cComp` compute the flag-dependent extension). Soundness does not
  -- depend on the populate value (E20–E47 pin the columns).
  let b ← witnessVector 4 (fun env =>
    bComp #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]] (hintFlags env.hint))
  let c ← witnessVector 4 (fun env =>
    cComp #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- (1,2) The two `c_times_quotient` product structs of `quotient_comp × c`, witnessed via the
  -- gated populates (`mul_lower` on real rows only; `mul_upper` only on the 64-bit variants —
  -- SP1's word rows and padding leave them all-zero). The `assertion`s composing them are emitted
  -- below, after the `scal` block, so the upper gate can reference the witnessed
  -- `is_real_not_word` column (witness ops emit no constraints, so the `h_holds` conjunct order
  -- is unchanged).
  let mul_lower ← ProvableType.witness (fun env =>
    populateMulLower (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let mul_upper ← ProvableType.witness (fun env =>
    populateMulUpper (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- (3-7) The two `IsEqualWordOperation` overflow checks (`is_overflow_b` vs `i64::MIN`,
  -- `is_overflow_c` vs `-1`), each asserted twice — full-word @ `is_real_not_word`, low-half @ `E2`
  -- (word-variant gate) — and `IsZeroWordOperation` on `c`. Nested cols witnessed flat via
  -- `fromElements (F := …)`. `E2` = word-variant flag sum; `irnw` = `is_real_not_word = is_real·(1-E2)`.
  let e2 := is_divw + is_remw + is_divuw + is_remuw
  -- witnessed scalar sign/gate columns + the `c_times_quotient`/`carry` u16-limb vectors, all
  -- honestly populated (`populateScal`/`populateCtq`/`populateCarry`); the own-asserts
  -- `E13/E15/…` and the carry chain `E121…E151` pin them.
  let scal ← witnessVector 7 (fun env =>
    populateScal (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let is_overflow := scal[0]; let b_neg := scal[1]; let b_neg_not_overflow := scal[2]
  let b_not_neg_not_overflow := scal[3]; let is_real_not_word := scal[4]
  let rem_neg := scal[5]; let c_neg := scal[6]
  let c_times_quotient ← witnessVector 8 (fun env =>
    populateCtq #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let carry ← witnessVector 8 (fun env =>
    populateCarry #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  -- (1,2 cont.) The two `MulOperation` `assertion`s (`divrem/mod.rs:721`): `mul_lower` = low
  -- product, gate + `is_mul` = `is_real`; `mul_upper` = high product, gate = the witnessed
  -- `is_real_not_word` (SP1 passes `is_real_not_word` as the upper Mul's multiplicity — on word
  -- rows the struct is all-zero and its product constraints must be off), `is_mulh = is_div +
  -- is_rem`, `is_mulhu = is_divu + is_remu`. Both have `is_mulw = 0`, so `is_mulw → is_real` is
  -- vacuous; the `isU64 quotient_comp` precondition is vacuous on padding rows.
  assertion MulOperation.circuit
    ⟨quotient_comp, c, mul_lower, input.is_real, input.is_real, 0, 0, 0, 0⟩
  assertion MulOperation.circuit
    ⟨quotient_comp, c, mul_upper, is_real_not_word, 0, is_div + is_rem, is_divu + is_remu, 0, 0⟩
  -- Link `c_times_quotient` to the two `MulOperation` gadgets' product bytes: the low 64 (limbs 0..3)
  -- to `mul_lower`'s bytes 0..7, the high 64 (limbs 4..7) to `mul_upper`'s bytes 8..15. SP1 expresses
  -- this by passing `c_times_quotient` as the Mul *result slot*; our native `MulOperation` reconstructs
  -- its `resultWord` internally (it does not take the result as input), so we glue here — without this
  -- the two Mul `Spec`s are dangling and the Euclidean identity `c_times_quotient = quotient_comp · c`
  -- is underivable. (Each glue is an `assertZero`, contributing 0 to `localLength`.) `mul_lower`'s
  -- `resultWord` is unconditionally its bytes 0..7 (its high flags are 0); `mul_upper`'s is bytes 8..15
  -- on the 64-bit variants (`is_mulh`/`is_mulhu` set). The **upper** glue is gated by the 64-bit flag
  -- sum (mirroring SP1's `is_mulh + is_mulhu` result-tie gates): on the signed-word rows
  -- `c_times_quotient[4..7]` carries the sign-extension limbs of the 128-bit product while `mul_upper`
  -- is all-zero, so an unconditional tie would be unsatisfiable by the honest witness.
  let c256 : Expression (ZMod p) := 256
  let g64 := is_div + is_divu + is_rem + is_remu
  c_times_quotient[0] === mul_lower.product[0] + mul_lower.product[1] * c256
  c_times_quotient[1] === mul_lower.product[2] + mul_lower.product[3] * c256
  c_times_quotient[2] === mul_lower.product[4] + mul_lower.product[5] * c256
  c_times_quotient[3] === mul_lower.product[6] + mul_lower.product[7] * c256
  g64 * (c_times_quotient[4] - (mul_upper.product[8] + mul_upper.product[9] * c256)) === 0
  g64 * (c_times_quotient[5] - (mul_upper.product[10] + mul_upper.product[11] * c256)) === 0
  g64 * (c_times_quotient[6] - (mul_upper.product[12] + mul_upper.product[13] * c256)) === 0
  g64 * (c_times_quotient[7] - (mul_upper.product[14] + mul_upper.product[15] * c256)) === 0
  let irnw := is_real_not_word
  let w_ovb ← witnessVector 11 (fun env =>
    ProvableType.toElements (ovbWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]] (hintFlags env.hint)))
  let w_ovc ← witnessVector 11 (fun env =>
    ProvableType.toElements (ovcWitness (env input.is_real)
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)))
  let w_is_c_0 ← witnessVector 11 (fun env =>
    ProvableType.toElements (isC0Witness
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)))
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
    ⟨c, fromElements (F := Expression (ZMod p)) w_is_c_0, input.is_real⟩
  -- (8-10) Two `AddOperation` two's-complement negations (`|c|`, `|remainder|`), and
  -- `LtOperationUnsigned` (`|remainder| < max(|c|,1)`). `LtOperationUnsigned` witnesses its comparison
  -- columns here via `populate_*`, then is composed as a Clean `assertion` gated by
  -- `remainder_check_multiplicity` (`is_real·(1 − is_c_0)`).
  let abs_c ← witnessVector 4 (fun env =>
    populateAbsC #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let abs_remainder ← witnessVector 4 (fun env =>
    populateAbsRem #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let remainder_comp ← witnessVector 4 (fun env =>
    populateRemComp #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let max_abs_c_or_1 ← witnessVector 4 (fun env =>
    populateMaxAbsCOr1 #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let w_cneg ← witnessVector 4 (fun env =>
    wCnegWitness (env input.is_real)
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let w_rneg ← witnessVector 4 (fun env =>
    wRnegWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let misc ← witnessVector 3 (fun env =>
    populateMisc (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let abs_c_alu_event := misc[0]; let abs_rem_alu_event := misc[1]
  let remainder_check_multiplicity := misc[2]
  assertion AddOperation.circuit ⟨c, abs_c, ⟨w_cneg⟩, abs_c_alu_event⟩
  assertion AddOperation.circuit ⟨remainder_comp, abs_remainder, ⟨w_rneg⟩, abs_rem_alu_event⟩
  let cl ← witnessVector 2 (fun env =>
    ltClWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let f ← witnessVector 4 (fun env =>
    ltFlagsWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let not_eq_inv ← witnessVector 1 (fun env =>
    ltNotEqInvWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let bit ← witnessVector 1 (fun env =>
    ltBitWitness (env input.is_real)
      #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let lt_out : Var Extracted.LtOperationUnsigned (ZMod p) := ⟨⟨bit[0]⟩, f, not_eq_inv[0], cl⟩
  assertion LtOperationUnsigned.circuit
    ⟨abs_remainder, max_abs_c_or_1, lt_out, remainder_check_multiplicity⟩
  -- (11-17) Seven `U16MSBOperation` sign-bit extractions — b/c/remainder high u16 (@ `irnw`),
  -- b/c/remainder/quotient low-half-high u16 (@ `E2`).
  let remainder ← witnessVector 4 (fun env =>
    populateRemainder #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let quotient ← witnessVector 4 (fun env =>
    populateQuotient #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint))
  let w_bmsb ← witnessVector 1 (fun env =>
    #v[bMsbCell #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]] (hintFlags env.hint)])
  let w_cmsb ← witnessVector 1 (fun env =>
    #v[cMsbCell #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)])
  let w_remmsb ← witnessVector 1 (fun env =>
    #v[remMsbCell #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)])
  let w_quotmsb ← witnessVector 1 (fun env =>
    #v[quotMsbCell #v[env bpv[0], env bpv[1], env bpv[2], env bpv[3]]
      #v[env cpv[0], env cpv[1], env cpv[2], env cpv[3]] (hintFlags env.hint)])
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
  -- `RTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.RTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * (65536 : Expression (ZMod p)), input.state.pc,
     is_divu * 16 + is_remu * 18 + is_div * 15 + is_rem * 17 + is_divw * 25 + is_remw * 27
       + is_divuw * 26 + is_remuw * 28,
     a[0], a[1], a[2], a[3]⟩
  -- Assemble `DivRemCols`, then emit the chip's own assertZero constraints (`E13…E367`, `op_a_0`, incl.
  -- the binary gates like `is_real·(is_real-1)` = E355) via `ownAsserts`.
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
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- the arithmetic so `isU64 a` (the flag-selected quotient/remainder output, byte-range-checked) discharges
  -- its requirement — breaking the old reader-circularity. Write access clock is the recombined low clock `+ 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, a, input.is_real⟩
  return cols

set_option maxHeartbeats 16000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs DivRemCols main where
  -- MulOperation FormalAssertions witness 45 cols each; + the `b`/`c` operand columns (4 each); total: 217.
  localLength _ := 217
  localLength_eq := by simp +arith [circuit_norm, main, AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit, LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit, Readers.RegisterWrite.circuit, U16MSBOperation.circuit, assertZeros]
  subcircuitsConsistent := by simp only [circuit_norm, main, AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit, LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit, Readers.RegisterWrite.circuit, U16MSBOperation.circuit, assertZeros]; try omega
  -- (W11 flip) `programChannel` joins the guarantees: `RTypeReader` now **pulls** the program fetch
  -- (a guarantee = `ProgramMsg.RowSpec`), so its guarantee propagates up here alongside `byteChannel`;
  -- `memoryChannel` likewise joins from `RTypeReader`'s memory read **pulls** (W11 memory flip). The
  -- `RegisterWrite` op_a write push owes a memory requirement (in `circuit.channelsWithRequirements`).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  -- the ~30 upstream `pullIf` unfold/refolds put this past simp's default step budget post-#398
  channelsLawful := by simp (maxSteps := 1000000) [circuit_norm, main, AddOperation.circuit, IsEqualWordOperation.circuit, IsZeroWordOperation.circuit, LtOperationUnsigned.circuit, MulOperation.circuit, Readers.CPUState.circuit, Readers.RTypeReader.circuit, Readers.RegisterWrite.circuit, U16MSBOperation.circuit, assertZeros]

end SP1Clean.DivRemChip
