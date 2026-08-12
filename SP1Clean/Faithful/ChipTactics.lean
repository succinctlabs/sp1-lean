import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Math.Word
import SP1Clean.Extracted.ExtractionDSL
import SP1Clean.Faithful.CPUState

/-! # Shared chip-faithfulness scaffolding

Shared across the per-chip `Faithful/*Chip.lean` anchors:

* `val_16` / `bool_iff` — field-arithmetic helpers every operation-level anchor needs;
* `toAccess_pullIf_byte_forall` — the ∀-form byte-pull `toAccess` kernel the interaction anchors
  `simp` with;
* `faithful_chip` — the legacy chip-level proof macro for the old `<op> ++ CPUState ++ <reader>`
  `*cols_constraints_faithful` layout (`cpustate_constraints_faithful` baked in). Currently it has
  no invocations — the whole-chip oracle anchors superseded it.

This module lives in `Faithful/` (not the foundational `Math/` + `Model/` layer) because the
`faithful_chip` macro hard-references `SP1Clean.Extracted.forall_append_pair` and
`SP1Clean.Faithful.cpustate_constraints_faithful` by definition-site resolution — both `import`s
above are load-bearing. Establish `NeZero p` in the caller before invoking the macro. -/

namespace SP1Clean.Faithful

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(16 : ZMod p).val = 16` — the Faithful-local spelling of `SP1Clean.val_16_zmod_p`
(kept as the established name used across the per-chip anchors' `simp only` lists). -/
lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := val_16_zmod_p

omit [Fact (2 ^ 17 < p)] in
/-- Carry-bool bridge: `x*(x-1)=0 ↔ x∈{0,1}` (field; `→` via the `mul_eq_zero`-free
`bool_of_mul_pred`). -/
lemma bool_iff {x : ZMod p} : x * (x - 1) = 0 ↔ (x = 0 ∨ x = 1) :=
  ⟨SP1Clean.bool_of_mul_pred,
    fun h => by rcases h with h | h <;> rw [h] <;> ring⟩

omit [Fact (2 ^ 17 < p)] in
open SP1Clean.Channels (byteChannel) in
/-- **Byte-pull `toAccess` kernel, ∀-form.** The `∀ g s`-quantified spelling of
`SP1Clean.toAccess_pullIf_byte`: the `toAccess`-image of a gated byte *pull* is the `byteSend`-style
`LookupAccess`. Every interaction anchor over the Byte bus needs it in exactly this shape as a
`simp only` rewrite, and thirteen of them wrote the eta-expanded `have hk : ∀ g s, …` block out by
hand; each becomes `have hk := toAccess_pullIf_byte_forall env`. The two `Faithful/CPUState.lean`
copies are the exception — this module *imports* that one (`faithful_chip` cites
`cpustate_constraints_faithful`), so they cannot cite it back. -/
lemma toAccess_pullIf_byte_forall (env : Environment (ZMod p)) :
    ∀ (g : Expression (ZMod p)) (s : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g s).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env s.opcode).val, (Expression.eval env s.a).val,
           (Expression.eval env s.b).val, (Expression.eval env s.c).val],
          signedVal (Expression.eval env (-g))) :=
  fun g s => toAccess_pullIf_byte env g s

/-- **Chip-level faithfulness anchor skeleton.** Discharges a `*cols_constraints_faithful` goal whose
constraint list is `<op-fragment> ++ CPUState ++ <reader> ++ [binary gate, op_a_0 = 0]`.

Arguments (all identifiers): the generated `asserts` def, the generated `interactions` def, the
`is_real = 1` hypothesis, the operation-fragment anchor, and the register-adapter anchor. Requires a
`NeZero p` instance in context (add `haveI : NeZero p := ⟨…⟩` in the caller). -/
syntax "faithful_chip" ident ppSpace ident ppSpace ident ppSpace ident ppSpace ident : tactic
macro_rules
  | `(tactic| faithful_chip $asserts:ident $inter:ident $hreal:ident $opAnchor:ident $rdrAnchor:ident) =>
    `(tactic| (
      simp only [$asserts:ident, $inter:ident]
      rw [SP1Clean.Extracted.forall_append_pair, SP1Clean.Extracted.forall_append_pair,
        SP1Clean.Extracted.forall_append_pair]
      simp only [$hreal:ident]
      rw [$opAnchor:ident, SP1Clean.Faithful.cpustate_constraints_faithful, $rdrAnchor:ident]
      simp only [List.Forall, sub_self, mul_zero, true_and]
      tauto))

/-- **Chip-level faithfulness anchor skeleton — assertion half.** Discharges a `*cols_asserts_faithful`
goal whose `asserts` list is `<op-fragment> ++ CPUState ++ <reader> ++ [binary gate, op_a_0 = 0]`.
Arguments: the generated `asserts` def, the `is_real = 1` hypothesis, the operation-fragment
*assertion* anchor, and the register-adapter *assertion* anchor. The shared `cpustate_asserts_faithful`
(trivial) is baked in. Requires a `NeZero p` instance in context. -/
syntax "faithful_chip_assert" ident ppSpace ident ppSpace ident ppSpace ident : tactic
macro_rules
  | `(tactic| faithful_chip_assert $asserts:ident $hreal:ident $opAnchor:ident $rdrAnchor:ident) =>
    `(tactic| (
      simp only [$asserts:ident]
      rw [SP1Clean.Extracted.forall_append_single, SP1Clean.Extracted.forall_append_single,
        SP1Clean.Extracted.forall_append_single]
      simp only [$hreal:ident]
      rw [$opAnchor:ident, SP1Clean.Faithful.cpustate_asserts_faithful, $rdrAnchor:ident]
      simp only [List.Forall, sub_self, mul_zero, true_and]
      tauto))

/-- **Chip-level faithfulness anchor skeleton — interaction half.** Discharges a
`*cols_interactions_faithful` goal whose `interactions` list is `<op-fragment> ++ CPUState ++ <reader> ++ []`.
Arguments: the generated `interactions` def, the `is_real = 1` hypothesis, the operation-fragment
*interaction* anchor, and the register-adapter *interaction* anchor. The shared
`cpustate_interactions_faithful` is baked in. Requires a `NeZero p` instance in context. -/
syntax "faithful_chip_interact" ident ppSpace ident ppSpace ident ppSpace ident : tactic
macro_rules
  | `(tactic| faithful_chip_interact $inter:ident $hreal:ident $opAnchor:ident $rdrAnchor:ident) =>
    `(tactic| (
      simp only [$inter:ident]
      rw [SP1Clean.Extracted.forall_append_interactions,
        SP1Clean.Extracted.forall_append_interactions,
        SP1Clean.Extracted.forall_append_interactions]
      simp only [$hreal:ident]
      rw [$opAnchor:ident, SP1Clean.Faithful.cpustate_interactions_faithful, $rdrAnchor:ident]
      simp only [List.Forall]
      tauto))

end SP1Clean.Faithful
