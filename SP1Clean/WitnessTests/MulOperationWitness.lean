import SP1Clean.Operations.MulOperation
import SP1Clean.Extracted.WitnessVectors.MulOperation
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `MulOperation`.

`native_decide` that the native Lean `MulOperation.populate` reproduces — on every vector dumped from
SP1's **real** `MulOperation::populate` (`MulOperationWitnessVectors`, the `witness_vectors` binary,
flag combos `(is_mulh, is_mulhsu, is_mulw)`) — the exact column values: the 16 product bytes, the 16
column carries, the two `U16toU8` low-byte decompositions, the three MSB columns, and the two
sign-extend selectors. Checked at SP1's concrete field (KoalaBear); corrupting any vector fails the
build. The `low_bytes` of the `U16toU8` sub-columns are recomputed `limb & 0xFF` in the dumper
(`U16toU8Operation::low_bytes` is private), which is exactly `populate_u16_to_u8_safe`'s output. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- `MulOperation.populate` needs `2 ^ 24 < p`; discharged at KoalaBear (`2^24 = 16777216 < SP1Prime`). -/
instance instFact2pow24SP1Prime : Fact (2 ^ 24 < SP1Prime) := ⟨by norm_num [SP1Prime]⟩

/-- One conformance check: `populate` on the dumped operands + flags reproduces every dumped column. -/
def mulPopulateConforms :
    (Vector ℕ 4 × Vector ℕ 4 × ℕ × ℕ × ℕ × Vector ℕ 16 × Vector ℕ 16 × Vector ℕ 4 × Vector ℕ 4 ×
      ℕ × ℕ × ℕ × ℕ × ℕ) → Bool :=
  fun (bl, cl, imh, imhsu, imw, carry, product, blo, clo, bmsb, cmsb, pmsb, bse, cse) =>
    let cols := MulOperation.populate (toWord bl) (toWord cl) (toField imh) (toField imhsu) (toField imw)
    (cols.carry.toList == (toFieldVec carry).toList) &&
    (cols.product.toList == (toFieldVec product).toList) &&
    (cols.b_lower_byte.low_bytes.toList == (toFieldVec blo).toList) &&
    (cols.c_lower_byte.low_bytes.toList == (toFieldVec clo).toList) &&
    (cols.b_msb == toField bmsb) && (cols.c_msb == toField cmsb) &&
    (cols.product_msb.msb == toField pmsb) &&
    (cols.b_sign_extend == toField bse) && (cols.c_sign_extend == toField cse)

/-- **Conformance anchor.** The native `MulOperation.populate` reproduces SP1's `populate` columns on
every dumped vector. -/
theorem mul_populate_conforms :
    MulOperationWitnessVectors.all mulPopulateConforms = true := by native_decide

end SP1Clean.WitnessTests
