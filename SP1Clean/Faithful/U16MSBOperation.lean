import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Native.Operations.U16MSBOperation.Defs
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.U16MSBOperation
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Faithful.ChipOracle

/-! # Faithfulness anchor — `U16MSBOperation` constraints ↔ native `RawSpec`

Anchors SP1's `U16MSBOperation` constraint definition (`SP1Clean/Extracted/U16MSBOperation.lean`:
an `is_real` bool, an `msb` bool, and one `ByteOpcode.Range` send on `2*a - msb*2^16`) to the
native gadget's `RawSpec`. The generated `constraints` is field-generic; applying at `ZMod p`
uses `open scoped …ConstraintCoe`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- All four `1 ≠ 0 →` discharge lemmas (`one_ne_zero`/`ne_eq`/`not_false_eq_true`/`true_implies`)
-- are genuinely needed — dropping either pair leaves unsolved goals — but on this short
-- (single-send) constraint list the `unusedSimpArgs` linter false-positives on two of them, so
-- it is disabled for this anchor only.
set_option linter.unusedSimpArgs false in
/-- **Faithfulness anchor.** SP1's `U16MSBOperation` constraint list (the generated operation
fragment) holds iff the native gadget's `RawSpec` holds. Since the native gadget's soundness runs
through this exact `RawSpec` (`msb_of_raw`), native-gadget proofs are faithful to SP1's operation
constraints. -/
theorem u16msb_constraints_faithful (a msb : ZMod p) :
    (List.Forall (· = 0) (Extracted.U16MSBOperation.asserts a ⟨msb⟩ 1) ∧
      List.Forall Interaction.toProp (Extracted.U16MSBOperation.interactions a ⟨msb⟩ 1)) ↔
      SP1Clean.U16MSBOperation.RawSpec a ⟨msb⟩ := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.U16MSBOperation.asserts, Extracted.U16MSBOperation.interactions, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.constrainField_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.U16MSBOperation.RawSpec, one_mul, sub_self, mul_zero, true_and, and_true,
    bool_iff, two_mul]

@[circuit_norm] theorem eval_u16MSBColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } :
        Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- Folded normalization of the native MSB fragment to the exact generated Rust assertion list. -/
theorem u16msb_assertions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.U16MSBOperation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.U16MSBOperation.main input).operations offset) =
      Extracted.U16MSBOperation.asserts
        (Expression.eval env input.a)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  simp [nativeAssertZeros, SP1Clean.U16MSBOperation.main,
    Gadgets.Equality.main, Extracted.U16MSBOperation.asserts,
    circuit_norm]
  have heval (value : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) value)[0] =
        Expression.eval env value := rfl
  simp_rw [heval]
  have hinput : Eval.eval env input =
      ({ a := Eval.eval env input.a, cols := Eval.eval env input.cols,
         is_real := Eval.eval env input.is_real } :
        SP1Clean.U16MSBOperation.Inputs (ZMod p)) := by
    rw [ProvableStruct.eval_eq_eval]
    rfl
  rw [← ProvableStruct.eval_eq_eval, hinput, eval_u16MSBColumns]
  simp only [eval_sub, Expression.eval, sub_zero,
    ProvableType.eval_field]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC.** SP1's extracted `U16MSBOperation.interactions`
and the Clean circuit's emitted byte interaction project to the **same** `LookupAccess` — the single
`Range` pull on the computed limb `2*a - msb*2^16`. Exercises the byte arm on a *computed* expression
(not a bare column): the circuit emits the Expression `2*a - msb*65536`, which `Expression.eval` reduces
(through `circuit_norm` + the `a`/`msb` bindings) to the same `ZMod` value the oracle records. -/
theorem u16msb_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.U16MSBOperation.Inputs (ZMod p)) (offset : ℕ)
    (a msb is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_a : Expression.eval env input.a = a)
    (h_msb : Expression.eval env input.cols.msb = msb) :
    (Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.U16MSBOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have hk := toAccess_pullIf_byte_forall env
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [SP1Clean.U16MSBOperation.main, circuit_norm, hk, heq,
    Extracted.U16MSBOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, h_ir, h_a, h_msb, h6]

end SP1Clean.Faithful
