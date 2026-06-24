import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.AddwOperation.RawSpec
import SP1Clean.Extracted.Circuit.AddwOperation
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.AddwOperation
import SP1Clean.Faithful.U16MSBOperation
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor — `AddwOperation` constraints ↔ native raw spec

Anchors the native `AddwOperation` gadget's constraints to SP1's generated `AddwOperation`
constraint definition (`Extracted/AddwOperation.lean`). SP1's `AddwOperation` composes
`U16MSBOperation` (`U16MSB.constraints ++ [two-limb add carry chain]`); the anchor splits at the
`++`: the `U16MSB` fragment is discharged by `u16msb_constraints_faithful`, the two-limb add
fragment by `ByteOpcode.Range`/`bool_iff` simp. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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

/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `AddwOperation` emits byte interactions
from two sources: the composed `U16MSBOperation` sub on `value[1]` (sign-bit limb), then two inline
`Range` pulls on `value[0]`/`value[1]`. The byte image splits (`congr 1`) into the `u16msb`
syntactic anchor + the two inline leaf pulls; the thirteen `=== 0` gates drop. -/
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
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pullIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
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
