import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.U16toU8OperationSafe
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Foundations.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.U16toU8OperationSafe

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (U16toU8 safe)

Anchors the native `U16toU8OperationSafe` gadget's `RawSpec` to **SP1's `U16toU8OperationSafe`
constraint definition** (`Extracted/U16toU8OperationSafe.lean`: four `U8Range` byte sends —
opcode 3 — each bounding a low byte `cols.low_bytes[i]` and its derived high byte
`(u16_values[i] - low_bytes[i]) * 256⁻¹`, with a constant `0` in the first slot). At `is_real = 1`
each send fires and `U8Range`'s `constrain` is exactly `a.val < 256 ∧ b.val < 256 ∧ c.val < 256`;
the `a = 0` conjunct collapses, so the anchor `u16tou8safe_constraints_faithful` proves the constraint
lists hold exactly iff the native gadget's `RawSpec`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor.** SP1's `U16toU8OperationSafe` constraint list (the four `U8Range`
sends) holds iff the native gadget's `RawSpec` (each low/high byte `< 256`) holds. -/
theorem u16tou8safe_constraints_faithful (u16_values : Vector (ZMod p) 4)
    (cols : Extracted.U16toU8Operation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.U16toU8OperationSafe.asserts u16_values cols 1) ∧
      List.Forall Interaction.toProp (Extracted.U16toU8OperationSafe.interactions u16_values cols 1)) ↔
      SP1Clean.U16toU8OperationSafe.RawSpec u16_values cols := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  simp only [Extracted.U16toU8OperationSafe.asserts, Extracted.U16toU8OperationSafe.interactions,
    List.Forall, Interaction.toProp_send_byte, ByteOpcode.ofNat_three, ByteOpcode.constrain_U8Range,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, ZMod.val_zero,
    SP1Clean.U16toU8OperationSafe.RawSpec, true_and,
    show (0 : ℕ) < 256 from by norm_num]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC (WITNESSED case).** SP1's extracted
`U16toU8OperationSafe.interactions` (at `is_real = 1`) and the Clean circuit's emitted byte interactions
project to the **same** `LookupAccess` list — the four `U8Range` pair pulls `⟨3, 0, low_i, high_i⟩`. This
is the first **witnessed-value** anchor: the four low bytes are `witnessVector` outputs, so after descent
they are `Expression.var ⟨offset+k⟩` (not an `input.<field>`); the binding hypotheses
`h_lb*` realise those witnessed columns as the oracle's `cols.low_bytes[k]` (the env-at-offset = the
output struct). The template for every remaining witnessed op/chip anchor (Address/BitwiseU16/LtSigned,
AddChip byte/memory, the whole chip rollout). The gate is the constant `1`, so this is stated at the
oracle's `is_real = 1`. -/
theorem u16tou8safe_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.U16toU8OperationSafe.Inputs (ZMod p))
    (offset : ℕ) (u16_values : Vector (ZMod p) 4) (cols : Extracted.U16toU8Operation (ZMod p))
    (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_u0 : Expression.eval env input.u16_values[0] = u16_values[0])
    (h_u1 : Expression.eval env input.u16_values[1] = u16_values[1])
    (h_u2 : Expression.eval env input.u16_values[2] = u16_values[2])
    (h_u3 : Expression.eval env input.u16_values[3] = u16_values[3])
    (h_lb0 : Expression.eval env input.cols.low_bytes[0] = cols.low_bytes[0])
    (h_lb1 : Expression.eval env input.cols.low_bytes[1] = cols.low_bytes[1])
    (h_lb2 : Expression.eval env input.cols.low_bytes[2] = cols.low_bytes[2])
    (h_lb3 : Expression.eval env input.cols.low_bytes[3] = cols.low_bytes[3]) :
    (Extracted.U16toU8OperationSafe.interactions u16_values cols is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.U16toU8OperationSafe.main input).operations offset).interactionsWith
          byteChannel.toRawGated).map (AbstractInteraction.toAccess env) := by
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env (byteChannel.receivedGated g s) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_receivedGated_byte env g s
  simp only [SP1Clean.U16toU8OperationSafe.main, circuit_norm, hk,
    Extracted.U16toU8OperationSafe.interactions, Extracted.Interaction.toAccess_byte,
    ByteOpcode.ofNat_three, ByteOpcode.idx, ZMod.val_zero,
    h_ir, h_u0, h_u1, h_u2, h_u3, h_lb0, h_lb1, h_lb2, h_lb3, h3, sub_eq_add_neg]

end SP1Clean.Faithful
