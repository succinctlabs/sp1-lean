module

public import SP1Clean.Semantics.Specs.Bitwise
public import SP1Clean.Circuits.Gadgets.BitwiseBytes
public import SP1Clean.Circuits.Gadgets.U16toU8Safe
import ToClean.Circuit.IteDecide
import Mathlib.Tactic.FinCases

/-! # Bitwise word witnesses

Value-level and Clean witness-IR construction of the same operand decompositions and result
bytes. Honest construction uses bounded input limbs; circuit soundness derives active bounds
from byte lookups.
-/

@[expose] public section

namespace SP1Clean.BitwiseU16Operation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The decomposition + result columns for `populate`: the low bytes are `w[i] % 256`, the result bytes
are the per-byte `byteOp opcode` of the decomposed operand bytes (mirroring SP1's `populate`). -/
def populate (b c : Word (ZMod p)) (opcode : ZMod p) : Columns (ZMod p) :=
  let lb : Circuits.Types.U16toU8Operation (ZMod p) :=
    ⟨#v[((b[0].val % 256 : ℕ) : ZMod p), ((b[1].val % 256 : ℕ) : ZMod p),
        ((b[2].val % 256 : ℕ) : ZMod p), ((b[3].val % 256 : ℕ) : ZMod p)]⟩
  let lc : Circuits.Types.U16toU8Operation (ZMod p) :=
    ⟨#v[((c[0].val % 256 : ℕ) : ZMod p), ((c[1].val % 256 : ℕ) : ZMod p),
        ((c[2].val % 256 : ℕ) : ZMod p), ((c[3].val % 256 : ℕ) : ZMod p)]⟩
  ⟨lb, lc, BitwiseOperation.populate (decompBytes b lb) (decompBytes c lc) opcode⟩

/-! ### Witness IR

The exportable twin of `populate` (the `AddOperation/Populate.lean` pattern, struct-shaped): the
same sixteen columns as a `Columns` struct of `FExpr`s, the composing chip's `witness` payload. The
result-byte operands are computed **in the u64 sort** — even bytes `b[i].val % 256`, odd bytes
`b[i].val / 256` — which agrees with `populate`'s field-side `(w − low)·256⁻¹` high bytes on
16-bit limbs (`decomp_high_eq`); `byteOpF` branches on the *field* opcode exactly as `byteOp`
branches on its `val` (equivalent by `val` injectivity, no opcode bound needed). Deliberately
**not** `@[circuit_norm]` (the opacity doctrine); only `populateFE_eval`/`populateFE_congr` cross
the boundary. The three `toElements_cell_*` navigators are the per-cell `toElements` projections
over an *opaque* struct (the `toElements_result_byte` technique from the chip's `Formal.lean`), so
neither proof ever runs `whnf` through the `combinedSize'` tower on a compound literal. -/

/-- The `FExpr` twin of `Math.byteOp`, branching on the field opcode (AND = 0, OR = 1, XOR = 2). -/
def byteOpF (opcode : Expression (ZMod p)) (a b : Witgen.U64Expr (ZMod p)) :
    Witgen.FExpr (ZMod p) :=
  .ite (opcode =? (0 : ZMod p)) (a &&& b).toField
    (.ite (opcode =? (1 : ZMod p)) (a ||| b).toField (a ^^^ b).toField)

/-- The witness-IR twin of `populate`, over the chip's input expressions. -/
def populateFE (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p)) :
    Columns (Witgen.FExpr (ZMod p)) :=
  ⟨⟨#v[(b[0].val % 256).toField, (b[1].val % 256).toField,
       (b[2].val % 256).toField, (b[3].val % 256).toField]⟩,
   ⟨#v[(c[0].val % 256).toField, (c[1].val % 256).toField,
       (c[2].val % 256).toField, (c[3].val % 256).toField]⟩,
   ⟨#v[byteOpF opcode (b[0].val % 256) (c[0].val % 256),
       byteOpF opcode (b[0].val / 256) (c[0].val / 256),
       byteOpF opcode (b[1].val % 256) (c[1].val % 256),
       byteOpF opcode (b[1].val / 256) (c[1].val / 256),
       byteOpF opcode (b[2].val % 256) (c[2].val % 256),
       byteOpF opcode (b[2].val / 256) (c[2].val / 256),
       byteOpF opcode (b[3].val % 256) (c[3].val % 256),
       byteOpF opcode (b[3].val / 256) (c[3].val / 256)]⟩⟩

/-- `populate`'s field-side high byte is the ℕ high byte: `(x − (v % 256))·256⁻¹ = v / 256` when
`x` casts `v` (the subtraction is exact, and `256` is invertible under `2^17 < p`). -/
private lemma decomp_high_eq {x : ZMod p} {v : ℕ} (hx : x = (v : ZMod p)) :
    (x - ((v % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹ = ((v / 256 : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have h256 : (256 : ZMod p) ≠ 0 := by
    intro h
    have hval : ((256 : ℕ) : ZMod p).val = 256 := ZMod.val_natCast_of_lt (by omega)
    rw [Nat.cast_ofNat, h, ZMod.val_zero] at hval
    omega
  subst hx
  rw [show (v : ZMod p) - ((v % 256 : ℕ) : ZMod p) = ((256 * (v / 256) : ℕ) : ZMod p) by
        rw [← Nat.cast_sub (Nat.mod_le v 256)]; congr 1; omega,
      Nat.cast_mul, Nat.cast_ofNat, mul_comm ((256 : ZMod p)) _, mul_assoc,
      mul_inv_cancel₀ h256, mul_one]

set_option linter.unusedSectionVars false in
/-- Cell `k` (`k < 4`) of a flattened `Columns` struct is the `k`-th `b` low byte. Stated over an
opaque `s`, so instantiating at a compound literal only pattern-matches. -/
private lemma toElements_cell_bLow {F : Type} (s : Columns F) (k : ℕ) (hk : k < 4) :
    (toElements s)[k]'(by have h16 : size Columns = 16 := rfl; omega)
      = s.b_low_bytes.low_bytes[k] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
       ProvableStruct.componentsToElements]
     refine (Vector.getElem_append_left ?_).trans
       ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `4 + k` (`k < 4`) of a flattened `Columns` struct is the `k`-th `c` low byte. -/
private lemma toElements_cell_cLow {F : Type} (s : Columns F) (k : ℕ) (hk : k < 4) :
    (toElements s)[4 + k]'(by have h16 : size Columns = 16 := rfl; omega)
      = s.c_low_bytes.low_bytes[k] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
       ProvableStruct.componentsToElements]
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_left ?_).trans
         ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_))) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `8 + k` (`k < 8`) of a flattened `Columns` struct is the `k`-th result byte (the generic-`F`
form of the chip-side `toElements_result_byte`). -/
private lemma toElements_cell_result {F : Type} (s : Columns F) (k : ℕ) (hk : k < 8) :
    (toElements s)[8 + k]'(by have h16 : size Columns = 16 := rfl; omega)
      = s.bitwise_operation.result[k] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
       ProvableStruct.componentsToElements]
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_left ?_).trans
           ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide)

/-! The per-shape eval/congr helpers, each proved once over *abstract* operand values with a
minimal context (the fold rule: `u64Wrap`'s `omega` takes the whole local context as facts, so
sixteen fat-context simp cases blow the declaration budget where six small-context helpers plus
term-mode assembly stay cheap). -/

omit [Fact (2 ^ 17 < p)] in
private lemma lowByteFE_eval (env : ProverEnvironment (ZMod p))
    (e : Expression (ZMod p)) (v : ZMod p)
    (he : Expression.eval env.toEnvironment e = v) (hv : v.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField) = ((v.val % 256 : ℕ) : ZMod p) := by
  simp only [circuit_norm, he]

private lemma byteOpFE_eval_lo (env : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p)) (v w : ZMod p)
    (he : Expression.eval env.toEnvironment e = v)
    (hf : Expression.eval env.toEnvironment f = w)
    (hv : v.val < 2 ^ 16) (hw : w.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val % 256) (f.val % 256))
      = ((byteOp (Expression.eval env.toEnvironment opcode).val
          (((v.val % 256 : ℕ) : ZMod p)).val (((w.val % 256 : ℕ) : ZMod p)).val : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hval0 : ∀ x : ZMod p, x.val = 0 ↔ x = 0 := fun x => by
    rw [show (0 : ℕ) = ZMod.val (0 : ZMod p) from ZMod.val_zero.symm, FiniteField.val_inj_F]
  have hval1 : ∀ x : ZMod p, x.val = 1 ↔ x = 1 := fun x => by
    rw [show (1 : ℕ) = ZMod.val (1 : ZMod p) by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)],
      FiniteField.val_inj_F]
  simp only [byteOpF, byteOp, circuit_norm, he, hf,
    ZMod.val_natCast_of_lt (show v.val % 256 < p by omega),
    ZMod.val_natCast_of_lt (show w.val % 256 < p by omega),
    hval0, hval1, apply_ite (Nat.cast (R := ZMod p))]

private lemma byteOpFE_eval_hi (env : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p)) (v w : ZMod p)
    (he : Expression.eval env.toEnvironment e = v)
    (hf : Expression.eval env.toEnvironment f = w)
    (hv : v.val < 2 ^ 16) (hw : w.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val / 256) (f.val / 256))
      = ((byteOp (Expression.eval env.toEnvironment opcode).val
          ((v - ((v.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val
          ((w - ((w.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hval0 : ∀ x : ZMod p, x.val = 0 ↔ x = 0 := fun x => by
    rw [show (0 : ℕ) = ZMod.val (0 : ZMod p) from ZMod.val_zero.symm, FiniteField.val_inj_F]
  have hval1 : ∀ x : ZMod p, x.val = 1 ↔ x = 1 := fun x => by
    rw [show (1 : ℕ) = ZMod.val (1 : ZMod p) by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)],
      FiniteField.val_inj_F]
  have hxv : v = ((v.val : ℕ) : ZMod p) := by rw [ZMod.natCast_val, ZMod.cast_id]
  have hxw : w = ((w.val : ℕ) : ZMod p) := by rw [ZMod.natCast_val, ZMod.cast_id]
  rw [decomp_high_eq hxv, decomp_high_eq hxw]
  simp only [byteOpF, byteOp, circuit_norm, he, hf,
    ZMod.val_natCast_of_lt (show v.val / 256 < p by omega),
    ZMod.val_natCast_of_lt (show w.val / 256 < p by omega),
    hval0, hval1, apply_ite (Nat.cast (R := ZMod p))]

omit [Fact (2 ^ 17 < p)] in
private lemma lowByteFE_congr (env env' : ProverEnvironment (ZMod p))
    (e : Expression (ZMod p))
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField)
      = Witgen.FExpr.eval { env := env' } ((e.val % 256).toField) := by
  simp only [circuit_norm, -Witgen.u64Wrap, he]

omit [Fact (2 ^ 17 < p)] in
private lemma byteOpFE_congr_lo (env env' : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p))
    (hop : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode)
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e)
    (hf : Expression.eval env.toEnvironment f = Expression.eval env'.toEnvironment f) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val % 256) (f.val % 256))
      = Witgen.FExpr.eval { env := env' } (byteOpF opcode (e.val % 256) (f.val % 256)) := by
  simp only [byteOpF, circuit_norm, -Witgen.u64Wrap, hop, he, hf]

omit [Fact (2 ^ 17 < p)] in
private lemma byteOpFE_congr_hi (env env' : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p))
    (hop : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode)
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e)
    (hf : Expression.eval env.toEnvironment f = Expression.eval env'.toEnvironment f) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val / 256) (f.val / 256))
      = Witgen.FExpr.eval { env := env' } (byteOpF opcode (e.val / 256) (f.val / 256)) := by
  simp only [byteOpF, circuit_norm, -Witgen.u64Wrap, hop, he, hf]

/-- Evaluating the witness IR is exactly `populate` on the evaluated operands (stated with the
evaluated words abstracted, in the `#v[…]`-of-`Expression.eval` form the chip completeness context
carries). The `isU64` bounds keep the u64-sorted `val`s from wrapping; the opcode needs no bound —
`byteOpF`'s field branches and `byteOp`'s `val` branches agree by `val` injectivity. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p)) (vb vc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvc : #v[Expression.eval env.toEnvironment c[0], Expression.eval env.toEnvironment c[1],
              Expression.eval env.toEnvironment c[2], Expression.eval env.toEnvironment c[3]] = vc)
    (hb : vb.isU64) (hc : vc.isU64) :
    Witgen.eval { env := env } (populateFE b c opcode)
      = populate vb vc (Expression.eval env.toEnvironment opcode) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hc
  have hB0 : Expression.eval env.toEnvironment b[0] = vb[0] := by rw [← hvb]; simp
  have hB1 : Expression.eval env.toEnvironment b[1] = vb[1] := by rw [← hvb]; simp
  have hB2 : Expression.eval env.toEnvironment b[2] = vb[2] := by rw [← hvb]; simp
  have hB3 : Expression.eval env.toEnvironment b[3] = vb[3] := by rw [← hvb]; simp
  have hC0 : Expression.eval env.toEnvironment c[0] = vc[0] := by rw [← hvc]; simp
  have hC1 : Expression.eval env.toEnvironment c[1] = vc[1] := by rw [← hvc]; simp
  have hC2 : Expression.eval env.toEnvironment c[2] = vc[2] := by rw [← hvc]; simp
  have hC3 : Expression.eval env.toEnvironment c[3] = vc[3] := by rw [← hvc]; simp
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi16 : i < 16 := by
    have hsz : size Columns = 16 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements, Vector.getElem_map]
  interval_cases i
  · exact ((congrArg _ (toElements_cell_bLow _ 0 (by omega))).trans
      (lowByteFE_eval env b[0] vb[0] hB0 hb0)).trans (toElements_cell_bLow _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 1 (by omega))).trans
      (lowByteFE_eval env b[1] vb[1] hB1 hb1)).trans (toElements_cell_bLow _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 2 (by omega))).trans
      (lowByteFE_eval env b[2] vb[2] hB2 hb2)).trans (toElements_cell_bLow _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 3 (by omega))).trans
      (lowByteFE_eval env b[3] vb[3] hB3 hb3)).trans (toElements_cell_bLow _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 0 (by omega))).trans
      (lowByteFE_eval env c[0] vc[0] hC0 hc0)).trans (toElements_cell_cLow _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 1 (by omega))).trans
      (lowByteFE_eval env c[1] vc[1] hC1 hc1)).trans (toElements_cell_cLow _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 2 (by omega))).trans
      (lowByteFE_eval env c[2] vc[2] hC2 hc2)).trans (toElements_cell_cLow _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 3 (by omega))).trans
      (lowByteFE_eval env c[3] vc[3] hC3 hc3)).trans (toElements_cell_cLow _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 0 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[0] c[0] vb[0] vc[0] hB0 hC0 hb0 hc0)).trans
      (toElements_cell_result _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 1 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[0] c[0] vb[0] vc[0] hB0 hC0 hb0 hc0)).trans
      (toElements_cell_result _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 2 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[1] c[1] vb[1] vc[1] hB1 hC1 hb1 hc1)).trans
      (toElements_cell_result _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 3 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[1] c[1] vb[1] vc[1] hB1 hC1 hb1 hc1)).trans
      (toElements_cell_result _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 4 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[2] c[2] vb[2] vc[2] hB2 hC2 hb2 hc2)).trans
      (toElements_cell_result _ 4 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 5 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[2] c[2] vb[2] vc[2] hB2 hC2 hb2 hc2)).trans
      (toElements_cell_result _ 5 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 6 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[3] c[3] vb[3] vc[3] hB3 hC3 hb3 hc3)).trans
      (toElements_cell_result _ 6 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 7 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[3] c[3] vb[3] vc[3] hB3 hC3 hb3 hc3)).trans
      (toElements_cell_result _ 7 (by omega)).symm

/-- Elementwise corollary of `populateFE_eval`, in the exact shape the chip completeness seam's
per-cell witness obligations arrive in (`FExpr.eval` of one `toElements` cell of the folded
`populateFE`). -/
theorem populateFE_eval_cell (env : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p)) (vb vc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvc : #v[Expression.eval env.toEnvironment c[0], Expression.eval env.toEnvironment c[1],
              Expression.eval env.toEnvironment c[2], Expression.eval env.toEnvironment c[3]] = vc)
    (hb : vb.isU64) (hc : vc.isU64) (j : ℕ) (hj : j < 16) :
    Witgen.FExpr.eval { env := env }
        ((toElements (populateFE b c opcode))[j]'(by
          have h16 : size Columns = 16 := rfl
          omega))
      = (toElements (populate vb vc (Expression.eval env.toEnvironment opcode)))[j]'(by
          have h16 : size Columns = 16 := rfl
          omega) := by
  have h := congrArg
    (fun s : Columns (ZMod p) => (toElements s)[j]'(by
      have h16 : size Columns = 16 := rfl
      omega))
    (populateFE_eval env b c opcode vb vc hvb hvc hb hc)
  rw [show (Witgen.eval { env := env } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements] at h
  simpa [Vector.getElem_map] using h

omit [Fact (2 ^ 17 < p)] in
/-- `ofFExprs`-of-`toElements` evaluation is the flattened struct evaluation (the raw payload
form the `ComputableWitnesses` obligations quantify over). -/
private lemma ofFExprs_eval_eq (env : ProverEnvironment (ZMod p))
    (xs : Columns (Witgen.FExpr (ZMod p))) :
    (Witgen.WitgenIR.ofFExprs (toElements xs)).eval env
      = toElements (Witgen.eval { env := env } xs) := by
  rw [show (Witgen.eval { env := env } xs : Columns (ZMod p))
        = fromElements ((toElements xs).map (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements]
  apply Vector.ext
  intro i hi
  simp [circuit_norm, Vector.getElem_map]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the witness IR (the `ComputableWitnesses` counterpart of
`populateFE_eval` — a congruence, so it needs no bounds). -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment c[i] = Expression.eval env'.toEnvironment c[i])
    (hOp : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode) :
    Witgen.eval { env := env } (populateFE b c opcode)
      = Witgen.eval { env := env' } (populateFE b c opcode) := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi16 : i < 16 := by
    have hsz : size Columns = 16 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    show (Witgen.eval { env := env' } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env' })) from rfl,
    ProvableType.toElements_fromElements, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_map]
  interval_cases i
  · exact ((congrArg _ (toElements_cell_bLow _ 0 (by omega))).trans
      (lowByteFE_congr env env' b[0] hB0)).trans
      (congrArg _ (toElements_cell_bLow _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 1 (by omega))).trans
      (lowByteFE_congr env env' b[1] hB1)).trans
      (congrArg _ (toElements_cell_bLow _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 2 (by omega))).trans
      (lowByteFE_congr env env' b[2] hB2)).trans
      (congrArg _ (toElements_cell_bLow _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 3 (by omega))).trans
      (lowByteFE_congr env env' b[3] hB3)).trans
      (congrArg _ (toElements_cell_bLow _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 0 (by omega))).trans
      (lowByteFE_congr env env' c[0] hC0)).trans
      (congrArg _ (toElements_cell_cLow _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 1 (by omega))).trans
      (lowByteFE_congr env env' c[1] hC1)).trans
      (congrArg _ (toElements_cell_cLow _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 2 (by omega))).trans
      (lowByteFE_congr env env' c[2] hC2)).trans
      (congrArg _ (toElements_cell_cLow _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 3 (by omega))).trans
      (lowByteFE_congr env env' c[3] hC3)).trans
      (congrArg _ (toElements_cell_cLow _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 0 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[0] c[0] hOp hB0 hC0)).trans
      (congrArg _ (toElements_cell_result _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 1 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[0] c[0] hOp hB0 hC0)).trans
      (congrArg _ (toElements_cell_result _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 2 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[1] c[1] hOp hB1 hC1)).trans
      (congrArg _ (toElements_cell_result _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 3 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[1] c[1] hOp hB1 hC1)).trans
      (congrArg _ (toElements_cell_result _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 4 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[2] c[2] hOp hB2 hC2)).trans
      (congrArg _ (toElements_cell_result _ 4 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 5 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[2] c[2] hOp hB2 hC2)).trans
      (congrArg _ (toElements_cell_result _ 5 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 6 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[3] c[3] hOp hB3 hC3)).trans
      (congrArg _ (toElements_cell_result _ 6 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 7 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[3] c[3] hOp hB3 hC3)).trans
      (congrArg _ (toElements_cell_result _ 7 (by omega))).symm

omit [Fact (2 ^ 17 < p)] in
/-- `populateFE_congr` in the raw `ofFExprs` payload form the `ComputableWitnesses` obligations
quantify over. -/
theorem populateFE_congr_flat (env env' : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment c[i] = Expression.eval env'.toEnvironment c[i])
    (hOp : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode) :
    (Witgen.WitgenIR.ofFExprs (toElements (populateFE b c opcode))).eval env
      = (Witgen.WitgenIR.ofFExprs (toElements (populateFE b c opcode))).eval env' :=
  (ofFExprs_eval_eq env _).trans
    ((congrArg toElements (populateFE_congr env env' b c opcode hB hC hOp)).trans
      (ofFExprs_eval_eq env' _).symm)

/-- The witnessed columns `populate b c opcode` satisfy the gadget `Spec` for any `is_real`, given the
operands are 64-bit and the opcode is AND/OR/XOR: the populated low bytes (`w[i] % 256`) and the derived
high bytes are genuine bytes, so the composed `BitwiseOperation.spec_populate` applies. The composing
`BitwiseChip` uses this to discharge its `assertion BitwiseU16Operation.circuit` prover obligation. -/
theorem spec_populate {b c : Word (ZMod p)} (hb : Word.isU64 b) (hc : Word.isU64 c)
    {opcode : ZMod p} (hop : opcode.val < 3) (is_real : ZMod p) :
    Spec (⟨b, c, populate b c opcode, opcode, is_real⟩ : Inputs (ZMod p)) := by
  have hp256 : (256 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hc
  have low_lt : ∀ u : ZMod p, (((u.val % 256 : ℕ) : ZMod p)).val < 256 := fun u => by
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  have high_lt : ∀ u : ZMod p, u.val < 65536 →
      ((u - ((u.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val < 256 := fun u hu => by
    rw [← e8]; exact U16toU8OperationSafe.high_byte_lt u (by rw [e16]; exact hu)
  have hbytes : ∀ i : Fin 8,
      (decompBytes b (populate b c opcode).b_low_bytes)[(i : ℕ)].val < 256 ∧
        (decompBytes c (populate b c opcode).c_low_bytes)[(i : ℕ)].val < 256 := by
    intro i
    fin_cases i <;>
      refine ⟨?_, ?_⟩ <;>
      · simp only [populate, decompBytes, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        first
          | exact low_lt _
          | (apply high_lt; assumption)
  exact BitwiseOperation.spec_populate hbytes hop is_real

end SP1Clean.BitwiseU16Operation
