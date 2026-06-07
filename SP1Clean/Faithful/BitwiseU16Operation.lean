import SP1Clean.Foundations.Bitwise
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.BitwiseOperation
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases

/-! # Faithfulness anchor for the Bitwise byte operation

Anchors the native gadget's per-byte relation to **SP1's `BitwiseOperation` constraint
definition** — the byte-opcode lookups (`send_byte`) that `BitwiseU16Operation` composes after
the `U16toU8` decomposition (`operations/bitwise.rs`). The SP1 pieces are no longer re-created
inline: the `ByteOpcode` datatype lives in the shared `SP1Clean/Foundations/SP1Constraint.lean`
(its `constrain` carries the real AND/OR/XOR meaning) and the `Interaction` bus vocabulary in
`SP1Clean/Extracted/ExtractionDSL.lean`, and `BitwiseOperation`'s `interactions` (the eight
`send_byte`s) is generated into `SP1Clean/Extracted/BitwiseOperation.lean`. The anchor theorem
`bitwise_byte_constraints_faithful` proves those constraint lists hold **exactly** iff the native
per-byte `byteOp` relation the gadget's soundness/completeness run through.

Scope: the byte-opcode core (`BitwiseOperation`). The full `BitwiseU16Operation` additionally
composes two `U16toU8OperationUnsafe` decompositions; anchoring that layer is future work.

The generated `constraints` is field-generic with a `[CoeHead F ℕ]` hypothesis; applying it at
`ZMod p` uses the scoped `CoeHead (ZMod p) ℕ` instance (`open scoped …ConstraintCoe`), whose
`coe_eq_val` lemma rewrites the dynamic `ByteOpcode.ofNat ↑opcode` to `ByteOpcode.ofNat
opcode.val`. -/

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

omit [Fact (2 ^ 17 < p)] in
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
    true_and, and_true, ConstraintCoe.coe_eq_val, constrain_iff_byteOp hop]

end SP1Clean.FaithfulBitwise
