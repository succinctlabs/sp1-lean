import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.MulOperation.RawSpec
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Extracted.MulOperation

/-! # Faithfulness anchor — `MulOperation` interactions ↔ native `InteractSpec`

Anchors SP1's generated `MulOperation` **interaction** list (`SP1Clean/Extracted/MulOperation.lean`)
to a native structural `MulOpInteractSpec`. `MulOperation.interactions` is a *composed* list:

  `U16toU8OperationSafe.interactions (b) ++ U16toU8OperationSafe.interactions (c)`
  `  ++ U16MSBOperation.interactions (a[1]) ++ <own 26 byte sends>`

The own tail is: two `MSB` sends pinning `b_msb`/`c_msb` to the high decomposition bytes `E7`/`E15`,
sixteen `Range(16)` carry sends, and eight `U8Range` product-pair sends. `MulOpInteractSpec` defers the
three composed sub-lists (each anchored by its own `Faithful/*` file when this op is composed in a chip)
and states the own tail's meaning verbatim; `mulOp_interactions_faithful` is the parity at `is_real = 1`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The high decomposition byte of `b` (`E7 = U16toU8OperationSafe.value b ...[7]`), the value the
`MSB` send pins `b_msb` against. -/
private def hiByteB (b : Word (ZMod p)) (cols : Extracted.MulOperation (ZMod p)) (is_real : ZMod p) :
    ZMod p :=
  (Extracted.U16toU8OperationSafe.value #v[b[0], b[1], b[2], b[3]]
    { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1],
      cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } is_real)[7]

/-- The high decomposition byte of `c` (`E15`). -/
private def hiByteC (c : Word (ZMod p)) (cols : Extracted.MulOperation (ZMod p)) (is_real : ZMod p) :
    ZMod p :=
  (Extracted.U16toU8OperationSafe.value #v[c[0], c[1], c[2], c[3]]
    { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1],
      cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } is_real)[7]

/-- **Interaction half — structural spec.** The meaning of `MulOperation.interactions` at `is_real = 1`:
the three composed sub-lists' interactions (`Interaction.toProp`, deferred to their own anchors when this
op is composed), plus the own tail — `b_msb`/`c_msb` are the byte-MSBs of the high decomposition bytes
`E7`/`E15`, the sixteen carries are `< 2^16`, and the sixteen product bytes are `< 256` (eight `U8Range`
pairs). Stated to match the `Interaction.toProp`-normalised list field-for-field. -/
def MulOpInteractSpec (a b c : Word (ZMod p)) (cols : Extracted.MulOperation (ZMod p))
    (is_mulw : ZMod p) : Prop :=
  List.Forall Interaction.toProp
      (Extracted.U16toU8OperationSafe.interactions #v[b[0], b[1], b[2], b[3]]
        { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1],
          cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } 1) ∧
  List.Forall Interaction.toProp
      (Extracted.U16toU8OperationSafe.interactions #v[c[0], c[1], c[2], c[3]]
        { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1],
          cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } 1) ∧
  List.Forall Interaction.toProp
      (Extracted.U16MSBOperation.interactions a[1] cols.product_msb is_mulw) ∧
  ((cols.b_msb.val < 256 ∧ (hiByteB b cols 1).val < 256 ∧ (0 : ZMod p).val < 256) ∧
    (cols.b_msb = 0 ∨ cols.b_msb = 1) ∧ (cols.b_msb = 1 ↔ 128 ≤ (hiByteB b cols 1).val)) ∧
  ((cols.c_msb.val < 256 ∧ (hiByteC c cols 1).val < 256 ∧ (0 : ZMod p).val < 256) ∧
    (cols.c_msb = 0 ∨ cols.c_msb = 1) ∧ (cols.c_msb = 1 ↔ 128 ≤ (hiByteC c cols 1).val)) ∧
  cols.carry[0].val < 2 ^ 16 ∧ cols.carry[1].val < 2 ^ 16 ∧ cols.carry[2].val < 2 ^ 16 ∧
    cols.carry[3].val < 2 ^ 16 ∧ cols.carry[4].val < 2 ^ 16 ∧ cols.carry[5].val < 2 ^ 16 ∧
    cols.carry[6].val < 2 ^ 16 ∧ cols.carry[7].val < 2 ^ 16 ∧ cols.carry[8].val < 2 ^ 16 ∧
    cols.carry[9].val < 2 ^ 16 ∧ cols.carry[10].val < 2 ^ 16 ∧ cols.carry[11].val < 2 ^ 16 ∧
    cols.carry[12].val < 2 ^ 16 ∧ cols.carry[13].val < 2 ^ 16 ∧ cols.carry[14].val < 2 ^ 16 ∧
    cols.carry[15].val < 2 ^ 16 ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[0].val < 256 ∧ cols.product[1].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[2].val < 256 ∧ cols.product[3].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[4].val < 256 ∧ cols.product[5].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[6].val < 256 ∧ cols.product[7].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[8].val < 256 ∧ cols.product[9].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[10].val < 256 ∧ cols.product[11].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[12].val < 256 ∧ cols.product[13].val < 256) ∧
  ((0 : ZMod p).val < 256 ∧ cols.product[14].val < 256 ∧ cols.product[15].val < 256)

set_option maxHeartbeats 1600000 in
/-- **Faithfulness anchor — interaction half.** SP1's `MulOperation` interaction list holds (under
`Interaction.toProp`) iff `MulOpInteractSpec` holds, at `is_real = 1`. -/
theorem mulOp_interactions_faithful (a b c : Word (ZMod p))
    (cols : Extracted.MulOperation (ZMod p)) (is_mulw : ZMod p) :
    List.Forall Interaction.toProp
        (Extracted.MulOperation.interactions a b c cols 1 1 1 is_mulw 1 1) ↔
      MulOpInteractSpec a b c cols is_mulw := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.MulOperation.interactions, List.forall_append, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_three, ByteOpcode.ofNat_five, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_U8Range, ByteOpcode.constrain_MSB, ByteOpcode.constrain_Range, val_16_zmod_p,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, MulOpInteractSpec, hiByteB, hiByteC,
    and_assoc]

/-
DEFERRED — the SYNTACTIC interaction anchor for `MulOperation` (emitted = SP1's extracted list, via
`toAccess`, like `add_interactions_faithful_syntactic`). It is COMPLETE and CORRECT (it elaborates and
closes), but it is left commented out because the final 26-element byte-interaction list-equality costs
**~8 min** to compile — the irreducible kernel cost of checking the proof term over that large list (the
descent + sub-anchor composition + reduction is only ~25 s; the list close is the wall). MulOp emits 26
inline byte pulls, vs 2-3 for Add/Sub/Addw where the same shape is cheap. The semantic `toProp` anchor
`mulOp_interactions_faithful` above already covers interaction-faithfulness in the meantime.

To enable it: uncomment this block AND restore these imports at the top of the file —
  import SP1Clean.Model.InteractionRecovery
  import SP1Clean.Faithful.ExtractedInteractionModel
  import SP1Clean.Extracted.Circuit.MulOperation
  import SP1Clean.Faithful.U16toU8OperationSafe
  import SP1Clean.Faithful.U16MSBOperation
Speed notes baked into the proof (do not "simplify"): the op5 high-byte products (`eob_v`/`eoc_v`) go in as
`.val`-wrapped `rw` targets AFTER the simp, and the `-is_real` multiplicity (`eneg_s`) as a `signedVal`-wrapped
simp arg — their bare `Expression.eval` forms as simp args probe every `eval` in the 28-deep list and blow up.

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 2000000 in
/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `MulOperation` emits byte interactions
from four sources, in order: the two composed `U16toU8OperationSafe` subs on `b`/`c`, the composed
`U16MSBOperation` sub on the result limb `a[1] = product[2] + product[3]·256`, then 26 inline pulls
(two `MSB`(5) sends pinning `b_msb`/`c_msb` to the high decomposition bytes `(·[3]-low[3])·256⁻¹`,
sixteen `Range`(6) carry pulls, eight `U8Range`(3) product-pair pulls). The byte image splits
(`congr 1`) into the three sub anchors + the inline leaf pulls; every `=== 0` gate emits nothing. -/
theorem mulOp_interactions_faithful_syntactic [Fact (2 ^ 24 < p)]
    (env : Environment (ZMod p)) (input : Var SP1Clean.MulOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b c : Word (ZMod p)) (cols : Extracted.MulOperation (ZMod p)) (is_real is_mulw : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_mulw : Expression.eval env input.is_mulw = is_mulw)
    (h_b0 : Expression.eval env input.b[0] = b[0])
    (h_b1 : Expression.eval env input.b[1] = b[1])
    (h_b2 : Expression.eval env input.b[2] = b[2])
    (h_b3 : Expression.eval env input.b[3] = b[3])
    (h_c0 : Expression.eval env input.c[0] = c[0])
    (h_c1 : Expression.eval env input.c[1] = c[1])
    (h_c2 : Expression.eval env input.c[2] = c[2])
    (h_c3 : Expression.eval env input.c[3] = c[3])
    (h_a1 : Expression.eval env (input.cols.product[2] + input.cols.product[3] * 256) = a[1])
    (h_blb0 : Expression.eval env input.cols.b_lower_byte.low_bytes[0] = cols.b_lower_byte.low_bytes[0])
    (h_blb1 : Expression.eval env input.cols.b_lower_byte.low_bytes[1] = cols.b_lower_byte.low_bytes[1])
    (h_blb2 : Expression.eval env input.cols.b_lower_byte.low_bytes[2] = cols.b_lower_byte.low_bytes[2])
    (h_blb3 : Expression.eval env input.cols.b_lower_byte.low_bytes[3] = cols.b_lower_byte.low_bytes[3])
    (h_clb0 : Expression.eval env input.cols.c_lower_byte.low_bytes[0] = cols.c_lower_byte.low_bytes[0])
    (h_clb1 : Expression.eval env input.cols.c_lower_byte.low_bytes[1] = cols.c_lower_byte.low_bytes[1])
    (h_clb2 : Expression.eval env input.cols.c_lower_byte.low_bytes[2] = cols.c_lower_byte.low_bytes[2])
    (h_clb3 : Expression.eval env input.cols.c_lower_byte.low_bytes[3] = cols.c_lower_byte.low_bytes[3])
    (h_bmsb : Expression.eval env input.cols.b_msb = cols.b_msb)
    (h_cmsb : Expression.eval env input.cols.c_msb = cols.c_msb)
    (h_pmsb : Expression.eval env input.cols.product_msb.msb = cols.product_msb.msb)
    (h_cy0 : Expression.eval env input.cols.carry[0] = cols.carry[0])
    (h_cy1 : Expression.eval env input.cols.carry[1] = cols.carry[1])
    (h_cy2 : Expression.eval env input.cols.carry[2] = cols.carry[2])
    (h_cy3 : Expression.eval env input.cols.carry[3] = cols.carry[3])
    (h_cy4 : Expression.eval env input.cols.carry[4] = cols.carry[4])
    (h_cy5 : Expression.eval env input.cols.carry[5] = cols.carry[5])
    (h_cy6 : Expression.eval env input.cols.carry[6] = cols.carry[6])
    (h_cy7 : Expression.eval env input.cols.carry[7] = cols.carry[7])
    (h_cy8 : Expression.eval env input.cols.carry[8] = cols.carry[8])
    (h_cy9 : Expression.eval env input.cols.carry[9] = cols.carry[9])
    (h_cy10 : Expression.eval env input.cols.carry[10] = cols.carry[10])
    (h_cy11 : Expression.eval env input.cols.carry[11] = cols.carry[11])
    (h_cy12 : Expression.eval env input.cols.carry[12] = cols.carry[12])
    (h_cy13 : Expression.eval env input.cols.carry[13] = cols.carry[13])
    (h_cy14 : Expression.eval env input.cols.carry[14] = cols.carry[14])
    (h_cy15 : Expression.eval env input.cols.carry[15] = cols.carry[15])
    (h_p0 : Expression.eval env input.cols.product[0] = cols.product[0])
    (h_p1 : Expression.eval env input.cols.product[1] = cols.product[1])
    (h_p2 : Expression.eval env input.cols.product[2] = cols.product[2])
    (h_p3 : Expression.eval env input.cols.product[3] = cols.product[3])
    (h_p4 : Expression.eval env input.cols.product[4] = cols.product[4])
    (h_p5 : Expression.eval env input.cols.product[5] = cols.product[5])
    (h_p6 : Expression.eval env input.cols.product[6] = cols.product[6])
    (h_p7 : Expression.eval env input.cols.product[7] = cols.product[7])
    (h_p8 : Expression.eval env input.cols.product[8] = cols.product[8])
    (h_p9 : Expression.eval env input.cols.product[9] = cols.product[9])
    (h_p10 : Expression.eval env input.cols.product[10] = cols.product[10])
    (h_p11 : Expression.eval env input.cols.product[11] = cols.product[11])
    (h_p12 : Expression.eval env input.cols.product[12] = cols.product[12])
    (h_p13 : Expression.eval env input.cols.product[13] = cols.product[13])
    (h_p14 : Expression.eval env input.cols.product[14] = cols.product[14])
    (h_p15 : Expression.eval env input.cols.product[15] = cols.product[15]) :
    (Extracted.MulOperation.interactions a b c cols is_real is_real is_real is_mulw is_real is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.MulOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 24 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h5 : (5 : ZMod p).val = 5 := by
    have h : (5 : ℕ) < p := by have := Fact.out (p := 2 ^ 24 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 24 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h16 : (16 : ZMod p).val = 16 := by
    have h : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 24 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  -- `value[7]` (the high decomposition byte the op5 `MSB` send pins) is `(·[3]-low[3])·256⁻¹`;
  -- precompute it so the inline simp never unfolds the (irreducible, heavy) `value`.
  have hvb : (Extracted.U16toU8OperationSafe.value #v[b[0], b[1], b[2], b[3]]
      { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1],
        cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } is_real)[7]
      = (b[3] - cols.b_lower_byte.low_bytes[3]) * (256 : ZMod p)⁻¹ := by
    simp [Extracted.U16toU8OperationSafe.value]
  have hvc : (Extracted.U16toU8OperationSafe.value #v[c[0], c[1], c[2], c[3]]
      { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1],
        cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } is_real)[7]
      = (c[3] - cols.c_lower_byte.low_bytes[3]) * (256 : ZMod p)⁻¹ := by
    simp [Extracted.U16toU8OperationSafe.value]
  -- Precompute every non-variable `eval` the inline RHS carries (opcode numerals, the `const 16`
  -- carry bound, the `0` sink, the two op5 high-byte products, the `-is_real` multiplicity) as ground
  -- rewrites — so the inline simp never runs `Expression.eval` over the 26-element list (which would
  -- recurse through the whole `Var` and is pathologically slow). `circuit_norm` is cheap here (tiny
  -- terms). Variable evals stay pinned by the column hypotheses.
  have e3 : Expression.eval env (3 : Expression (ZMod p)) = 3 := by simp only [circuit_norm]
  have e5 : Expression.eval env (5 : Expression (ZMod p)) = 5 := by simp only [circuit_norm]
  have e6 : Expression.eval env (6 : Expression (ZMod p)) = 6 := by simp only [circuit_norm]
  have e16 : Expression.eval env (Expression.const (16 : ZMod p)) = 16 := by
    simp only [circuit_norm]
  have e0 : Expression.eval env (0 : Expression (ZMod p)) = 0 := by simp only [circuit_norm]
  have eob : Expression.eval env ((input.b[3] - input.cols.b_lower_byte.low_bytes[3])
      * Expression.const (256 : ZMod p)⁻¹) = (b[3] - cols.b_lower_byte.low_bytes[3]) * (256 : ZMod p)⁻¹ := by
    simp only [circuit_norm, h_b3, h_blb3, sub_eq_add_neg]
  have eoc : Expression.eval env ((input.c[3] - input.cols.c_lower_byte.low_bytes[3])
      * Expression.const (256 : ZMod p)⁻¹) = (c[3] - cols.c_lower_byte.low_bytes[3]) * (256 : ZMod p)⁻¹ := by
    simp only [circuit_norm, h_c3, h_clb3, sub_eq_add_neg]
  have eneg : Expression.eval env (-input.is_real) = -is_real := by simp only [circuit_norm, h_ir]
  -- LHS: oracle = `U16toU8(b) ++ U16toU8(c) ++ U16MSB(a[1]) ++ [26 inline sends]`.
  simp only [Extracted.MulOperation.interactions, List.map_append]
  -- RHS: descend `main`; the three subs ++ the inline pulls (the `=== 0` gates emit nothing).
  simp only [SP1Clean.MulOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, SP1Clean.U16toU8OperationSafe.circuit,
    SP1Clean.U16MSBOperation.circuit, Gadgets.Equality.main, List.filter_nil, List.append_nil,
    List.map_append]
  congr 1
  · -- U16toU8(b)
    exact u16tou8safe_interactions_faithful_syntactic env
      ⟨input.b, input.cols.b_lower_byte, input.is_real⟩ _ #v[b[0], b[1], b[2], b[3]]
      { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1],
        cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } is_real
      h_ir h_b0 h_b1 h_b2 h_b3 h_blb0 h_blb1 h_blb2 h_blb3
  congr 1
  · -- U16toU8(c)
    exact u16tou8safe_interactions_faithful_syntactic env
      ⟨input.c, input.cols.c_lower_byte, input.is_real⟩ _ #v[c[0], c[1], c[2], c[3]]
      { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1],
        cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } is_real
      h_ir h_c0 h_c1 h_c2 h_c3 h_clb0 h_clb1 h_clb2 h_clb3
  congr 1
  · -- U16MSB(a[1])
    exact u16msb_interactions_faithful_syntactic env
      ⟨input.cols.product[2] + input.cols.product[3] * 256, input.cols.product_msb, input.is_mulw⟩ _
      a[1] cols.product_msb.msb is_mulw h_mulw h_a1 h_pmsb
  · -- the 26 inline byte pulls: reduce both sides' `toAccess` to byte tuples (`toAccess_byte`/`hk`),
    -- then close field-for-field by ground rewrites. Speed is delicate here (a 26-element list of byte
    -- tuples): the `-is_real` multiplicity (26 copies) goes in as the `signedVal`-wrapped `eneg_s` simp
    -- arg, but the two op5 high-byte products go in as `.val`-wrapped *`rw` targets after* the simp
    -- (`eob_v`/`eoc_v`). A bare `eval _ = _` (or `.val`-wrapped) form as a *simp* arg makes simp probe
    -- the big `Expression.eval` pattern against every `.val` in the list (~10min); as one-shot `rw`
    -- targets they hit only the two op5 positions and the lists become syntactically equal (fast rfl).
    have eneg_s : signedVal (Expression.eval env (-input.is_real)) = signedVal (-is_real) := by
      rw [eneg]
    have eob_v : (Expression.eval env ((input.b[3] - input.cols.b_lower_byte.low_bytes[3])
        * Expression.const 256⁻¹)).val = ((b[3] - cols.b_lower_byte.low_bytes[3]) * 256⁻¹).val := by
      rw [eob]
    have eoc_v : (Expression.eval env ((input.c[3] - input.cols.c_lower_byte.low_bytes[3])
        * Expression.const 256⁻¹)).val = ((c[3] - cols.c_lower_byte.low_bytes[3]) * 256⁻¹).val := by
      rw [eoc]
    simp only [Extracted.Interaction.toAccess_byte, hk, ByteOpcode.idx, ByteOpcode.ofNat_three,
      ByteOpcode.ofNat_five, ByteOpcode.ofNat_six, hvb, hvc, e3, e5, e6, e16, e0, eneg_s, h_bmsb,
      h_cmsb, h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6, h_cy7, h_cy8, h_cy9, h_cy10, h_cy11,
      h_cy12, h_cy13, h_cy14, h_cy15, h_p0, h_p1, h_p2, h_p3, h_p4, h_p5, h_p6, h_p7, h_p8, h_p9,
      h_p10, h_p11, h_p12, h_p13, h_p14, h_p15, h3, h5, h6, h16, ZMod.val_zero]
    rw [eob_v, eoc_v]
-/

end SP1Clean.Faithful
