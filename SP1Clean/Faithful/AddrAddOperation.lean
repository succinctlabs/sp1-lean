import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.AddrAddOperation.RawSpec
import SP1Clean.Operations.AddrAddOperation.Extracted
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Foundations.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.AddrAddOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (AddrAdd)

Anchors the native `AddrAddOperation` gadget's `RawSpec` to **SP1's `AddrAddOperation` constraint
definition** (`Extracted/AddrAddOperation.lean`: the `is_real` gate, four inverse-form boolean
carries, and three `ByteOpcode.Range` sends on the result limbs). Mirrors the `AddOperation` anchor
with a 3-limb result and a `sub_zero` on the high carry. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)`. -/
private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

omit [Fact (2 ^ 17 < p)] in
/-- Carry-bool bridge: `x*(x-1)=0 ↔ x∈{0,1}` (field; `→` via `bool_of_mul_pred`). -/
private lemma bool_iff {x : ZMod p} : x * (x - 1) = 0 ↔ (x = 0 ∨ x = 1) := by
  rw [sub_eq_add_neg]
  exact ⟨SP1Clean.bool_of_mul_pred,
    fun h => by rcases h with h | h <;> rw [h] <;> ring⟩

/-- **Faithfulness anchor.** SP1's `AddrAddOperation` constraint list holds iff the native gadget's
`RawSpec` holds. -/
theorem addrAdd_constraints_faithful (a b : Word (ZMod p))
    (cols : Extracted.AddrAddOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.AddrAddOperation.asserts a b cols 1) ∧
      List.Forall Interaction.toProp (Extracted.AddrAddOperation.interactions a b cols 1)) ↔
      SP1Clean.AddrAddOperation.RawSpec a b cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.AddrAddOperation.asserts, Extracted.AddrAddOperation.interactions, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.AddrAddOperation.RawSpec, one_mul, add_zero, sub_zero, sub_self, mul_zero,
    true_and, bool_iff, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC.** SP1's extracted `AddrAddOperation.interactions`
and the Clean circuit's emitted byte interactions project to the **same** `LookupAccess` list (the three
`Range` pulls on the result limbs). Sibling of `add_interactions_faithful_syntactic` with a 3-limb result.
The `a b` operands are ignored by `interactions` (`_a`/`_b`). -/
theorem addrAdd_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.AddrAddOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b : Word (ZMod p)) (cols : Extracted.AddrAddOperation (ZMod p)) (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_v0 : Expression.eval env input.cols.value[0] = cols.value[0])
    (h_v1 : Expression.eval env input.cols.value[1] = cols.value[1])
    (h_v2 : Expression.eval env input.cols.value[2] = cols.value[2]) :
    (Extracted.AddrAddOperation.interactions a b cols is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.AddrAddOperation.main input).operations offset).interactionsWith
          byteChannel.toRawGated).map (AbstractInteraction.toAccess env) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env (byteChannel.receivedGated g s) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_receivedGated_byte env g s
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) byteChannel.toRawGated
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.AddrAddOperation.main, circuit_norm, hk, heq,
    Extracted.AddrAddOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, ByteOpcode.ofNat_six, ByteOpcode.idx,
    h_ir, h_v0, h_v1, h_v2, h6]

end SP1Clean.Faithful
