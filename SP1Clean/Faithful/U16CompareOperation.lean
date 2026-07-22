import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.U16CompareOperation.RawSpec
import SP1Clean.Native.Operations.U16CompareOperation.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.U16CompareOperation
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (U16Compare)

Anchors the native `U16CompareOperation` gadget's `RawSpec` to **SP1's `U16CompareOperation`
constraint definition** (`Extracted/U16CompareOperation.lean`: the `is_real` gate, `bit` boolean,
and one `ByteOpcode.Range` send on `(a-b)+bit*2^16`). At `is_real = 1` the gate collapses to `True`
and the send fires, so the anchor `u16compare_constraints_faithful` proves the constraint lists hold
exactly iff the native gadget's `RawSpec`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Faithfulness anchor.** SP1's `U16CompareOperation` constraint list holds iff the native
gadget's `RawSpec` holds. -/
theorem u16compare_constraints_faithful (a b : ZMod p)
    (cols : Extracted.U16CompareOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.U16CompareOperation.asserts a b cols 1) ∧
      List.Forall Interaction.toProp (Extracted.U16CompareOperation.interactions a b cols 1)) ↔
      SP1Clean.U16CompareOperation.RawSpec a b cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.U16CompareOperation.asserts, Extracted.U16CompareOperation.interactions,
    List.Forall, Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.U16CompareOperation.RawSpec, sub_self, mul_zero, true_and,
    bool_iff, show (2 : ℕ) ^ 16 = 65536 from by norm_num]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC.** SP1's extracted `U16CompareOperation.interactions`
and the Clean circuit's emitted byte interaction project to the **same** `LookupAccess` — the single
`Range` pull on the computed limb `(a-b)+bit*2^16`. Sibling of `u16msb_interactions_faithful_syntactic`
(another computed-expression leaf). -/
theorem u16compare_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.U16CompareOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b is_real : ZMod p) (cols : Extracted.U16CompareOperation (ZMod p))
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_a : Expression.eval env input.a = a)
    (h_b : Expression.eval env input.b = b)
    (h_bit : Expression.eval env input.cols.bit = cols.bit) :
    (Extracted.U16CompareOperation.interactions a b cols is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.U16CompareOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.U16CompareOperation.main, circuit_norm, hk, heq,
    Extracted.U16CompareOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, ByteOpcode.ofNat_six, ByteOpcode.idx,
    h_ir, h_a, h_b, h_bit, h6]

end SP1Clean.Faithful
