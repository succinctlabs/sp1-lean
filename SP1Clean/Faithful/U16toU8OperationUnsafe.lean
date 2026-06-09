import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Operations.U16toU8OperationUnsafe
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Foundations.InteractionRecovery
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Extracted.U16toU8OperationUnsafe

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (U16toU8 unsafe)

Anchors the native `U16toU8OperationUnsafe` gadget's `RawSpec` to **SP1's
`U16toU8OperationUnsafe` constraint definition** (`Extracted/U16toU8OperationUnsafe.lean`). That
extracted op emits **empty** `asserts` and `interactions` lists (a separate `value : Vector F 8`
carries the split bytes) — the unsafe split imposes no range checks — so the anchor
`u16tou8unsafe_constraints_faithful` proves those lists hold exactly iff the native gadget's `RawSpec`
(`True`). The byte bounds live in the `U16toU8OperationSafe` sibling. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor.** SP1's `U16toU8OperationUnsafe` constraint lists (both empty) hold iff the
native gadget's `RawSpec` (`True`) holds. -/
theorem u16tou8unsafe_constraints_faithful (u16_values : Vector (ZMod p) 4)
    (cols : Extracted.U16toU8Operation (ZMod p)) :
    (List.Forall (· = 0) (Extracted.U16toU8OperationUnsafe.asserts u16_values cols) ∧
      List.Forall Interaction.toProp (Extracted.U16toU8OperationUnsafe.interactions u16_values cols)) ↔
      SP1Clean.U16toU8OperationUnsafe.RawSpec u16_values cols := by
  simp only [Extracted.U16toU8OperationUnsafe.asserts, Extracted.U16toU8OperationUnsafe.interactions,
    List.Forall, SP1Clean.U16toU8OperationUnsafe.RawSpec, and_self]

open SP1Clean.Channels (byteChannel)
open SP1Clean.InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
/-- **Faithfulness anchor — interaction half, SYNTACTIC.** `U16toU8OperationUnsafe.main` is empty (the
unsafe split asserts nothing and pulls no byte ranges), matching SP1's empty extracted `interactions` —
both `toAccess` images are `[]`. -/
theorem u16tou8unsafe_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var SP1Clean.U16toU8OperationUnsafe.Inputs (ZMod p)) (offset : ℕ)
    (u16_values : Vector (ZMod p) 4) (cols : Extracted.U16toU8Operation (ZMod p)) :
    (Extracted.U16toU8OperationUnsafe.interactions u16_values cols).map Extracted.Interaction.toAccess
      = (((SP1Clean.U16toU8OperationUnsafe.main input).operations offset).interactionsWith
          byteChannel.toRawGated).map (AbstractInteraction.toAccess env) := by
  simp only [SP1Clean.U16toU8OperationUnsafe.main, circuit_norm,
    Extracted.U16toU8OperationUnsafe.interactions, List.map_nil]

end SP1Clean.Faithful
