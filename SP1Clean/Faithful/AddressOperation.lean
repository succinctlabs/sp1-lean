import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.AddressOperation

/-! # Faithfulness anchor to the SP1 (Rust-extraction) constraints (Address)

Anchors the native `AddressOperation` gadget's `RawSpec` to **SP1's `AddressOperation` constraint
definition** (`Extracted/AddressOperation.lean`). A value-returning op (it also emits a separate
`value : Vector F 3`, unused here), it composes an `AddrAddOperation` sub-list (three `Range` sends at
`n = 16`) alongside its own offset `Range` send at `n = 13` — hence both `val_16` and `val_13`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)`. -/
private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

/-- `(13 : ZMod p).val = 13` under `Fact (2^17 < p)`. -/
private lemma val_13 [NeZero p] : (13 : ZMod p).val = 13 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (13 : ℕ) < p by omega)

omit [Fact (2 ^ 17 < p)] in
/-- Carry-bool bridge: `x*(x-1)=0 ↔ x∈{0,1}` (field; `→` via `bool_of_mul_pred`). -/
private lemma bool_iff {x : ZMod p} : x * (x - 1) = 0 ↔ (x = 0 ∨ x = 1) := by
  rw [sub_eq_add_neg]
  exact ⟨SP1Clean.bool_of_mul_pred,
    fun h => by rcases h with h | h <;> rw [h] <;> ring⟩

set_option maxHeartbeats 4000000 in
/-- **Faithfulness anchor.** SP1's `AddressOperation` constraint lists (`asserts` + `interactions`)
hold iff the native gadget's `RawSpec` holds. -/
theorem address_constraints_faithful (b cc : Word (ZMod p))
    (offset_bit0 offset_bit1 offset_bit2 : ZMod p) (cols : Extracted.AddressOperation (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2 1 cols) ∧
        List.Forall Interaction.toProp
          (Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2 1 cols)) ↔
      SP1Clean.AddressOperation.RawSpec b cc offset_bit0 offset_bit1 offset_bit2 cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.AddressOperation.asserts, Extracted.AddressOperation.interactions,
    Extracted.AddrAddOperation.asserts, Extracted.AddrAddOperation.interactions,
    List.Forall, List.cons_append, List.nil_append,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Interaction.toProp_send_byte, ByteOpcode.ofNat_six,
    ByteOpcode.constrain_Range, val_16, val_13, one_ne_zero, ne_eq, not_false_eq_true, true_implies,
    SP1Clean.AddressOperation.RawSpec, SP1Clean.AddrAddOperation.RawSpec,
    one_mul, add_zero, sub_zero, sub_self, mul_zero, true_and, and_assoc, bool_iff,
    show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  itauto

end SP1Clean.Faithful
