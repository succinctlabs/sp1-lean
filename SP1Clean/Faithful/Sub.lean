import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.SubOperation.RawSpec
import SP1Clean.Extracted.Circuit.SubOperation
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.SubOperation

/-! # Faithfulness anchor — `SubOperation` constraints ↔ native `RawSpec`

Anchors the native `SubOp` gadget's constraints to SP1's `SubOperation` constraint definition
(`SP1Clean/Extracted/SubOperation.lean`).

SP1 computes `a - b` as `a + (2^64 - b)` (`sp1/crates/core/machine/src/operations/sub.rs`),
using `2^16 - 1 - b[i]` as the added limb with the carry **initialized to 1**; the constant
`65535 = 2^16 - 1` is SP1's `base - one`. The constraint shape is the **borrow-form** `RawSpec`
(carry `c_i = (a[i] + 65535 - b[i] - value[i] + c_{i-1}) * 65536⁻¹`, `c_{-1} = 1`), so the
anchor `sub_constraints_faithful` is a trivial `simp`, just like `add_constraints_faithful`.

The generated `constraints` is field-generic with a `[CoeHead F ℕ]` hypothesis; applying it at
`ZMod p` uses the scoped `CoeHead (ZMod p) ℕ` instance (`open scoped …ConstraintCoe`). -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Faithfulness anchor.** SP1's `SubOperation` constraint list (the generated operation
fragment the Rust extraction composes for subtraction) holds iff the native gadget's `RawSpec`
holds. Since the native `SubOp` gadget's soundness/completeness run through this exact `RawSpec`,
native-gadget proofs are faithful to SP1's operation constraints. -/
theorem sub_constraints_faithful (a b value : Word (ZMod p)) :
    (List.Forall (· = 0) (Extracted.SubOperation.asserts a b ⟨value⟩ 1) ∧
      List.Forall Interaction.toProp (Extracted.SubOperation.interactions a b ⟨value⟩ 1)) ↔
      SP1Clean.SubOperation.RawSpec a b value := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.SubOperation.asserts, Extracted.SubOperation.interactions, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.SubOperation.RawSpec, one_mul, sub_self, mul_zero, true_and,
    bool_iff, Nat.cast_ofNat, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  -- The generated constraints use `a[i] + 65536 - 1` where `RawSpec` uses `a[i] + 65535`;
  -- these are ring-equal, so normalize both sides of each carry equation. The split groups the
  -- carry-bool asserts and the byte-range interactions separately, so `tauto` reassociates.
  ring_nf
  tauto

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC.** SP1's extracted `SubOperation.interactions`
and the Clean circuit's emitted byte interactions project to the same `LookupAccess` list. Channel,
message arg values, signed multiplicity (the byte pull sign `-is_real`). The `a b` operands are
ignored by `interactions`, so passed as `value`. Sub's byte fragment is identical to Add's. -/
theorem sub_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.SubOperation.Inputs (ZMod p)) (offset : ℕ)
    (value : Word (ZMod p)) (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_v0 : Expression.eval env input.cols.value[0] = value[0])
    (h_v1 : Expression.eval env input.cols.value[1] = value[1])
    (h_v2 : Expression.eval env input.cols.value[2] = value[2])
    (h_v3 : Expression.eval env input.cols.value[3] = value[3]) :
    (Extracted.SubOperation.interactions value value ⟨value⟩ is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.SubOperation.main input).operations offset).interactionsWith
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
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) byteChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.SubOperation.main, circuit_norm, hk, heq,
    Extracted.SubOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, ByteOpcode.ofNat_six, ByteOpcode.idx,
    h_ir, h_v0, h_v1, h_v2, h_v3, h6]

end SP1Clean.Faithful
