import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.AddOperation.RawSpec
import SP1Clean.Extracted.Circuit.AddOperation
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.AddOperation

/-! # Faithfulness anchor — `AddOperation` constraints ↔ native `AssertSpec`/`InteractSpec`

Anchors the native `AddOp` gadget's hand-written constraints to SP1's generated
`AddOperation` constraint definition (`Extracted/AddOperation.lean`). The two anchor theorems
`add_asserts_faithful` / `add_interactions_faithful` prove those two constraint lists hold
**exactly** iff the native gadget's `AssertSpec` / `InteractSpec` respectively.

The generated `constraints` is field-generic with a `[CoeHead F ℕ]` hypothesis; applying it at
`ZMod p` uses the scoped `CoeHead (ZMod p) ℕ` instance (`open scoped …ConstraintCoe`). -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — assertion half.** SP1's `AddOperation` `asserts` list (the five gated
carry-bool field constraints) holds iff the native gadget's `AssertSpec` (the four carry-bool
predicates) holds. -/
theorem add_asserts_faithful (a b value : Word (ZMod p)) :
    List.Forall (· = 0) (Extracted.AddOperation.asserts a b ⟨value⟩ 1) ↔
      SP1Clean.AddOperation.AssertSpec a b value := by
  simp only [Extracted.AddOperation.asserts, List.Forall,
    SP1Clean.AddOperation.AssertSpec, one_mul, add_zero, sub_self, mul_zero, true_and,
    bool_iff]

/-- **Faithfulness anchor — interaction half.** SP1's `AddOperation` `interactions` list (the four
`Range` byte sends) holds iff the native gadget's `InteractSpec` (the four limb-range predicates)
holds. Together with `add_asserts_faithful`, native-gadget proofs (which route through `AssertSpec`
and `InteractSpec`) are faithful to SP1's operation constraints. -/
theorem add_interactions_faithful (a b value : Word (ZMod p)) :
    List.Forall Interaction.toProp (Extracted.AddOperation.interactions a b ⟨value⟩ 1) ↔
      SP1Clean.AddOperation.InteractSpec value := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.AddOperation.interactions, List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.AddOperation.InteractSpec, show (2 : ℕ) ^ 16 = 65536 from by norm_num]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

/-- **Faithfulness anchor — interaction half, SYNTACTIC** (the canonical replacement for the `toProp`
`add_interactions_faithful`). Instead of an *interpreter* mapping a byte send to `mult ≠ 0 →
op.constrain …` (and every non-byte interaction to `True`), this compares the **emitted interaction
list itself**: SP1's extracted `AddOperation.interactions` and the Clean circuit's emitted byte
interactions project — through `Extracted.Interaction.toAccess` / `AbstractInteraction.toAccess` — to
the **same** `LookupAccess` list `(kind, table, argvals, signedmult)`. No semantics (`op.constrain`,
`< 65536`), just interaction modeling: channel, message arg values, and the signed multiplicity (the
byte *pull* sink sign `-is_real`). Under an `env` realising the result-limb columns (`h_v*`) and
`is_real` (`h_ir`). The byte tuple `[6, value[i].val, 16, 0]` matches field-for-field; the sole modeling
fact is the byte send/receive (sink) sign, recorded in `Extracted.Interaction.toAccess`'s `.byte` arm.
The `a b` operands are ignored by `interactions` (`_a`/`_b`), so they are passed as `value` here. -/
theorem add_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.AddOperation.Inputs (ZMod p)) (offset : ℕ)
    (value : Word (ZMod p)) (is_real : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_v0 : Expression.eval env input.cols.value[0] = value[0])
    (h_v1 : Expression.eval env input.cols.value[1] = value[1])
    (h_v2 : Expression.eval env input.cols.value[2] = value[2])
    (h_v3 : Expression.eval env input.cols.value[3] = value[3]) :
    (Extracted.AddOperation.interactions value value ⟨value⟩ is_real).map
        Extracted.Interaction.toAccess
      = (((SP1Clean.AddOperation.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  -- the byte kernel maps each recovered `pullIf` pull to its `LookupAccess`
  have hk : ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  -- the five `=== 0` gates are `Gadgets.Equality` `FormalAssertion` subcircuits emitting no byte
  -- interaction, so their `byteChannel` filter is empty (as in `programLookups_eq_emitted`).
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  -- RHS: recover the 4 byte pulls from `main`; LHS: expand the extracted list + projection.
  simp only [SP1Clean.AddOperation.main, circuit_norm, hk, heq,
    Extracted.AddOperation.interactions, List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte, ByteOpcode.ofNat_six, ByteOpcode.idx,
    h_ir, h_v0, h_v1, h_v2, h_v3, h6]

/-- **Faithfulness anchor — combined.** The two-list pair form of `add_asserts_faithful` /
`add_interactions_faithful`, for composing `AddOperation` as a fragment inside a chip-level anchor
via the `faithful_chip` macro. Legacy `toProp` form — retained as the compat bridge for
`AddiChip`/`JalChip`/`JalrChip`/`UTypeChip`; the canonical interaction anchor is
`add_interactions_faithful_syntactic`. -/
theorem add_constraints_faithful (a b value : Word (ZMod p)) :
    (List.Forall (· = 0) (Extracted.AddOperation.asserts a b ⟨value⟩ 1) ∧
        List.Forall Interaction.toProp (Extracted.AddOperation.interactions a b ⟨value⟩ 1)) ↔
      (SP1Clean.AddOperation.AssertSpec a b value ∧
        SP1Clean.AddOperation.InteractSpec value) := by
  rw [add_asserts_faithful, add_interactions_faithful]

end SP1Clean.Faithful
