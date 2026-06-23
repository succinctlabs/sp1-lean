import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.LtOperationSigned.RawSpec
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.LtOperationSigned
import SP1Clean.Faithful.LtOperationUnsigned
import SP1Clean.Faithful.ChipTactics

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (LtSigned)

Anchors the native `LtOperationSigned` gadget's `RawSpec` to **SP1's `LtOperationSigned` constraint
definition** (`Extracted/LtOperationSigned.lean`). The most composite anchor: two
`U16MSBOperation` sub-lists gated by the **free** `is_signed` (so their `Range` sends keep the
`is_signed ≠ 0 →` guard), a full `LtOperationUnsigned` sub-list on the sign-adjusted words (gated by
`is_real = 1`, hence discharged), and five top-level `assertZero`s. Fixes `is_real = 1`, leaves
`is_signed` free. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 8000000 in
/-- **Faithfulness anchor.** SP1's `LtOperationSigned` constraint list (at `is_real = 1`, `is_signed`
free) holds iff the native gadget's `RawSpec` holds. -/
theorem ltSigned_constraints_faithful (b cc : Word (ZMod p))
    (cols : Extracted.LtOperationSigned (ZMod p)) (is_signed : ZMod p) :
    (List.Forall (· = 0) (Extracted.LtOperationSigned.asserts b cc cols is_signed 1) ∧
      List.Forall Interaction.toProp (Extracted.LtOperationSigned.interactions b cc cols is_signed 1)) ↔
      SP1Clean.LtOperationSigned.RawSpec b cc cols is_signed := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Split the composed list `U16MSB(b) ++ U16MSB(c) ++ LtUnsigned ++ ⟨tail⟩` at each `++`, then
  -- collapse the `is_real = 1`-gated LtUnsigned sub-list to its `RawSpec` via its own anchor — this
  -- turns the whole `U16Compare` expansion into one opaque atom, so the residual reassociation over
  -- the two (small) MSB clauses + the tail is cheap.
  simp only [Extracted.LtOperationSigned.asserts, Extracted.LtOperationSigned.interactions]
  rw [forall_append_pair, forall_append_pair, forall_append_pair,
    ltUnsigned_constraints_faithful]
  simp only [Extracted.U16MSBOperation.asserts, Extracted.U16MSBOperation.interactions,
    List.Forall,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, ne_eq,
    SP1Clean.LtOperationSigned.RawSpec, Nat.cast_ofNat,
    zero_mul, sub_self, mul_zero, true_and, and_assoc, bool_iff,
    show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  itauto

end SP1Clean.Faithful
