import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.AddwOperation.RawSpec
import SP1Clean.Operations.AddwOperation.Extracted
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Foundations.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.AddwOperation
import SP1Clean.Faithful.U16MSBOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (ADDW)

The native `AddwOp` gadget's constraints are hand-written; this module anchors them to **SP1's
`AddwOperation` constraint definition** — the operation-level form the `sp1-constraint-compiler`
emits and `update_extracted.py` writes to `SP1Clean/Extracted/AddwOperation.lean`. SP1's
`AddwOperation` **composes** `U16MSBOperation` (its `constraints` is `U16MSB.constraints … ++
[two-limb add carry chain]`), so the anchor splits the list at the `++`: the `U16MSB` fragment is
discharged by `u16msb_constraints_faithful`, and the two-limb add fragment by the same
`ByteOpcode.Range`/`bool_iff` simp as `add_constraints_faithful`. The native gadget's
soundness/completeness run through exactly `U16MSBOperation.RawSpec` and `AddwOperation.RawSpec`,
so the gadget proofs are faithful to SP1's operation constraints. -/

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

set_option linter.unusedSimpArgs false in
/-- **Faithfulness anchor.** SP1's composed `AddwOperation` constraint list holds iff the native
gadget's combined raw spec (`U16MSBOperation.RawSpec` on the sign bit ∧ `AddwOperation.RawSpec` on
the two-limb add chain) holds. -/
theorem addw_constraints_faithful (a b : Word (ZMod p)) (cols : Extracted.AddwOperation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.AddwOperation.asserts a b cols 1) ∧
      List.Forall Interaction.toProp (Extracted.AddwOperation.interactions a b cols 1)) ↔
      U16MSBOperation.RawSpec cols.value[1] cols.msb ∧ AddwOperation.RawSpec a b cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.AddwOperation.asserts, Extracted.AddwOperation.interactions]
  rw [forall_append_pair, u16msb_constraints_faithful]
  refine and_congr Iff.rfl ?_
  simp only [List.Forall, Interaction.toProp_send_byte, ByteOpcode.ofNat_six, ByteOpcode.constrain_Range, val_16,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, AddwOperation.RawSpec, one_mul, add_zero,
    sub_self, mul_zero, true_and, and_true, bool_iff, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC (HYBRID composition + inline).** `AddwOperation`
emits its byte interactions from TWO sources in the same order as the oracle: the composed
`U16MSBOperation` sub on `value[1]` (the sign-bit limb), then two inline `Range` pulls on `value[0]`/`value[1]`.
So the byte image splits (`congr 1`) into the `u16msb` syntactic anchor + the two inline leaf pulls. The
thirteen `=== 0` gates drop. Template for `Subw` (sibling) and the other mixed composed ops. -/
theorem addw_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.AddwOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b : Word (ZMod p)) (cols : Extracted.AddwOperation (ZMod p)) (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_v0 : Expression.eval env input.cols.value[0] = cols.value[0])
    (h_v1 : Expression.eval env input.cols.value[1] = cols.value[1])
    (h_msb : Expression.eval env input.cols.msb.msb = cols.msb.msb) :
    (Extracted.AddwOperation.interactions a b cols is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.AddwOperation.main input).operations offset).interactionsWith
          byteChannel.toRawGated).map (AbstractInteraction.toAccess env) := by
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
  -- LHS: oracle = `U16MSB.interactions value[1] ⟨msb⟩ is_real ++ [v0 byte, v1 byte]`.
  simp only [Extracted.AddwOperation.interactions, List.map_append]
  -- RHS: descend; the U16MSB sub byte ++ the two inline pulls (the `=== 0` gates emit nothing).
  simp only [SP1Clean.AddwOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, SP1Clean.U16MSBOperation.circuit,
    Gadgets.Equality.main, List.filter_nil, List.append_nil, List.map_append]
  congr 1
  · exact u16msb_interactions_faithful_syntactic env
      ⟨input.cols.value[1], input.cols.msb, input.is_real⟩ _
      cols.value[1] cols.msb.msb is_real h_ir h_v1 h_msb
  · simp only [hk, circuit_norm, Extracted.Interaction.toAccess_byte,
      ByteOpcode.ofNat_six, ByteOpcode.idx, h_ir, h_v0, h_v1, h6]

end SP1Clean.Faithful
