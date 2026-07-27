import SP1Clean.Math.Bitwise
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.BitwiseOperation
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases

/-! # Faithfulness anchor — `BitwiseOperation` byte constraints ↔ native per-byte `byteOp`

Anchors the native gadget's per-byte relation to SP1's `BitwiseOperation` constraint definition
(the eight `send_byte` lookups composed after the `U16toU8` decomposition). The anchor theorem
`bitwise_byte_constraints_faithful` proves those constraint lists hold **exactly** iff the native
per-byte `byteOp` relation.

Scope: the byte-opcode core (`BitwiseOperation`). Anchoring the full `BitwiseU16Operation` (which
additionally composes two `U16toU8OperationUnsafe` decompositions) is future work.

`coe_eq_val` rewrites the dynamic `ByteOpcode.ofNat ↑opcode` to `ByteOpcode.ofNat opcode.val`. -/

namespace SP1Clean.FaithfulBitwise

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Per-byte bridge: a single `send_byte`'s `constrain` (under `is_real = 1`, `opcode < 3`)
is exactly the native `byteOp` relation. -/
lemma constrain_iff_byteOp {x a b : ZMod p} {opcode : ZMod p} (hop : opcode.val < 3) :
    (ByteOpcode.ofNat opcode.val).constrain x a b ↔
      (x.val < 256 ∧ a.val < 256 ∧ b.val < 256) ∧ x.val = byteOp opcode.val a.val b.val := by
  haveI : NeZero p := ⟨(Nat.Prime.pos Fact.out).ne'⟩
  -- `ofNat_zero/one/two` (auto `@[simp]`) reduce `ByteOpcode.ofNat {0,1,2}` to AND/OR/XOR;
  -- passing `ByteOpcode.ofNat` itself would instead unfold it to its `Nat.ble` decision tree.
  interval_cases h : opcode.val <;>
    simp [ByteOpcode.constrain, byteOp]

/-- Raw-opcode form of `constrain_iff_byteOp`. The first conjunct is now an exact statement about
the field element carried by Rust's byte bus, rather than a lossy eager enum decode. -/
lemma constrainField_iff_byteOp {x a b : ZMod p} {opcode : ZMod p}
    (hop : opcode.val < 3) :
    ByteOpcode.constrainField opcode x a b ↔
      (x.val < 256 ∧ a.val < 256 ∧ b.val < 256) ∧
        x.val = byteOp opcode.val a.val b.val := by
  haveI : NeZero p := ⟨(Nat.Prime.pos Fact.out).ne'⟩
  have hdecode := ByteOpcode.constrainField_natCast
    (p := p) (k := opcode.val) (by omega) x a b
  rw [ZMod.natCast_zmod_val] at hdecode
  exact hdecode.trans (constrain_iff_byteOp hop)

set_option linter.unusedSimpArgs false in
/-- **Faithfulness anchor.** SP1's `BitwiseOperation` constraint list (the eight byte-opcode
sends) holds iff the native per-byte `byteOp` relation holds — the relation the witnessed
gadget's soundness/completeness run through. -/
theorem bitwise_byte_constraints_faithful
    (a b result : Vector (ZMod p) 8) (opcode : ZMod p) (hop : opcode.val < 3) :
    (List.Forall (· = 0) (Extracted.BitwiseOperation.asserts a b ⟨result⟩ opcode 1) ∧
      List.Forall Interaction.toProp (Extracted.BitwiseOperation.interactions a b ⟨result⟩ opcode 1)) ↔
      ((result[0].val < 256 ∧ a[0].val < 256 ∧ b[0].val < 256) ∧ result[0].val = byteOp opcode.val a[0].val b[0].val) ∧
      ((result[1].val < 256 ∧ a[1].val < 256 ∧ b[1].val < 256) ∧ result[1].val = byteOp opcode.val a[1].val b[1].val) ∧
      ((result[2].val < 256 ∧ a[2].val < 256 ∧ b[2].val < 256) ∧ result[2].val = byteOp opcode.val a[2].val b[2].val) ∧
      ((result[3].val < 256 ∧ a[3].val < 256 ∧ b[3].val < 256) ∧ result[3].val = byteOp opcode.val a[3].val b[3].val) ∧
      ((result[4].val < 256 ∧ a[4].val < 256 ∧ b[4].val < 256) ∧ result[4].val = byteOp opcode.val a[4].val b[4].val) ∧
      ((result[5].val < 256 ∧ a[5].val < 256 ∧ b[5].val < 256) ∧ result[5].val = byteOp opcode.val a[5].val b[5].val) ∧
      ((result[6].val < 256 ∧ a[6].val < 256 ∧ b[6].val < 256) ∧ result[6].val = byteOp opcode.val a[6].val b[6].val) ∧
      ((result[7].val < 256 ∧ a[7].val < 256 ∧ b[7].val < 256) ∧ result[7].val = byteOp opcode.val a[7].val b[7].val) := by
  haveI : NeZero p := ⟨(Nat.Prime.pos Fact.out).ne'⟩
  simp only [Extracted.BitwiseOperation.asserts, Extracted.BitwiseOperation.interactions, List.Forall,
    Interaction.toProp_send_byte, ne_eq, one_ne_zero, not_false_eq_true, true_implies,
    true_and, and_true, constrainField_iff_byteOp hop]

end SP1Clean.FaithfulBitwise
