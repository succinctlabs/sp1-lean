import Mathlib.Tactic
import SP1Clean.Native.Operations.BitwiseOperation.RawSpec
import SP1Clean.Native.Operations.BitwiseOperation.Defs
import SP1Clean.Faithful.BitwiseU16Operation
import SP1Clean.Math.Bitwise
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.BitwiseOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (Bitwise byte op)

Anchors the native `BitwiseOperation` gadget's `RawSpec` to **SP1's `BitwiseOperation` constraint
definition** (`Extracted/BitwiseOperation.lean`: eight per-byte opcode sends). The byte-send ⇔
`byteOp` equivalence is already proved, op-uniformly, by
`FaithfulBitwise.bitwise_byte_constraints_faithful` (in `Faithful/BitwiseU16Operation.lean`); the
gadget's `RawSpec` is defined to be exactly that lemma's right-hand side, so this anchor is a thin
restatement — no constraint re-proof, axiom-clean. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — assertion half.** `BitwiseOperation` emits no algebraic `asserts`, so its
(empty) `asserts` list trivially holds, matching the trivial `AssertSpec`. -/
theorem bitwise_asserts_faithful (a b : Vector (ZMod p) 8) (opcode : ZMod p)
    (cols : Extracted.BitwiseOperation (ZMod p)) :
    List.Forall (· = 0) (Extracted.BitwiseOperation.asserts a b cols opcode 1) ↔
      SP1Clean.BitwiseOperation.AssertSpec a b opcode cols := by
  simp only [Extracted.BitwiseOperation.asserts, List.Forall,
    SP1Clean.BitwiseOperation.AssertSpec]

/-- **Faithfulness anchor — interaction half.** SP1's `BitwiseOperation` `interactions` list (the
eight byte-opcode sends) holds iff the native gadget's `InteractSpec` (the per-byte `byteOp`
relation) holds. -/
theorem bitwise_interactions_faithful (a b : Vector (ZMod p) 8) (opcode : ZMod p)
    (cols : Extracted.BitwiseOperation (ZMod p)) (hop : opcode.val < 3) :
    List.Forall Interaction.toProp (Extracted.BitwiseOperation.interactions a b cols opcode 1) ↔
      SP1Clean.BitwiseOperation.InteractSpec a b opcode cols := by
  have h := FaithfulBitwise.bitwise_byte_constraints_faithful a b cols.result opcode hop
  simp only [Extracted.BitwiseOperation.asserts, List.Forall, true_and] at h
  simpa only [SP1Clean.BitwiseOperation.InteractSpec] using h

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half, SYNTACTIC.** SP1's extracted `BitwiseOperation.interactions`
and the Clean circuit's emitted byte interactions project to the **same** `LookupAccess` list — the eight
per-byte `⟨opcode, result[i], a[i], b[i]⟩` AND/OR/XOR sends. Both sides preserve the raw field-valued
opcode, so this structural equality is unconditional; opcode validity belongs to the byte-table
semantics. Bindings are vector-level (the eight per-limb evals are derived inside). -/
theorem bitwise_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.BitwiseOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b : Vector (ZMod p) 8) (cols : Extracted.BitwiseOperation (ZMod p)) (opcode is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_op : Expression.eval env input.opcode = opcode)
    (h_a : Vector.map (Expression.eval env) input.a = a)
    (h_b : Vector.map (Expression.eval env) input.b = b)
    (h_r : Vector.map (Expression.eval env) input.cols.result = cols.result) :
    (Extracted.BitwiseOperation.interactions a b cols opcode is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.BitwiseOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have ea : ∀ (i : ℕ) (hi : i < 8), Expression.eval env input.a[i] = a[i] :=
    fun i hi => by rw [← h_a, Vector.getElem_map]
  have eb : ∀ (i : ℕ) (hi : i < 8), Expression.eval env input.b[i] = b[i] :=
    fun i hi => by rw [← h_b, Vector.getElem_map]
  have er : ∀ (i : ℕ) (hi : i < 8), Expression.eval env input.cols.result[i] = cols.result[i] :=
    fun i hi => by rw [← h_r, Vector.getElem_map]
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  simp only [SP1Clean.BitwiseOperation.main, circuit_norm, hk,
    Extracted.BitwiseOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, h_ir, h_op, ea, eb, er]

end SP1Clean.Faithful
