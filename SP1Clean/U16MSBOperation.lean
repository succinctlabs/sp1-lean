import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Gadgets.Equality
import Clean.Utils.Field
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.U16MSBOperation.Operation
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Clean.ByteOpcodeTable

/-! # Tier 2a pilot: `U16MSBOperation` mirror

SP1's `U16MSBOperation` extracts the most-significant bit of a 16-bit value.
Its constraint list under `is_real = 1`:

- `msb * (msb - 1) = 0`                                  — boolean
- `send (.byte Range (2*a - msb*65536) 16 0) is_real`    — `(2*a - msb*65536).val < 2^16`

This is the smallest fragment that exercises one byte interaction. The Clean
mirror replaces the `send` with a single `lookup ByteOpcodeTable …` call
(see `SP1Clean/ByteOpcodeTable.lean`).

The principled Clean patch (drop the duplicate `Fin.foldl_eq_foldl_finRange`
in `Clean/Utils/Misc.lean`) means the `<==` / `===` operators are now
available — the circuit definition below uses them idiomatically. Promoting
to a full `FormalCircuit` (with soundness + completeness against the table's
`Spec`) is followup; the pilot ships the `iff_sp1` bridge.
-/

namespace SP1Clean.U16MSBOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)] [Fact (p > 65536)]

/-- Clean-side circuit. Witnesses `msb`, asserts boolean via `===`, then
performs the single byte-opcode lookup for `Range(2*a - msb*65536, 16, 0)`. -/
def main (a : Expression (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let msb ← witnessField (fun env =>
    if (a.eval env).val < 32768 then 0 else 1)
  msb * (msb - 1) === 0
  -- Row layout #v[opcode, a, b, c]; here opcode = Range.toNat = 6.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), 2 * a - msb * 65536, 16, 0] : Vector (Expression (ZMod p)) 4)
  return msb

/-- Pilot Spec: `msb` is boolean and `2*a - msb*65536` is a u16
(i.e. `< 65536`). -/
def Spec (a msb : ZMod p) : Prop :=
  msb * (msb - 1) = 0 ∧ (2 * a - msb * 65536).val < 65536

omit [Fact (p > 512)] in
/-- Helper: in `ZMod p` with `p > 65536`, `(16 : ZMod p).val = 16`. -/
lemma val_sixteen : ((16 : ZMod p) : ZMod p).val = 16 := by
  have hp : 65536 < p := (Fact.out : p > 65536)
  rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by norm_num,
      ZMod.val_natCast, Nat.mod_eq_of_lt]
  omega

omit [Fact (p > 512)] in
/-- Helper: `Range.constrain_poly _ 16 _` reduces to `_.val < 65536`. -/
lemma range_at_sixteen (x : ZMod p) :
    ByteOpcode.Range.constrain_poly x (16 : ZMod p) (0 : ZMod p) ↔ x.val < 65536 := by
  rw [ByteOpcode.constrain_poly_Range, val_sixteen]
  norm_num

omit [Fact (p > 512)] in
/-- The bridge to SP1: SP1's `allHold_poly` under `is_real = 1` is exactly
the pilot `Spec`. -/
theorem iff_sp1 (a : ZMod p) (cols : U16MSBOperation (ZMod p)) :
    (U16MSBOperation.constraints (F := ZMod p) a cols 1).allHold_poly ↔
    Spec a cols.msb := by
  simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold_poly, List.Forall,
    SP1Constraint.toProp_poly, Spec]
  simp only [ByteOpcode.ofNat_seven]  -- ByteOpcode.ofNat 6 = Range
  constructor
  · rintro ⟨_h_isreal, h_bool, h_range⟩
    refine ⟨?_, ?_⟩
    · linear_combination h_bool
    · have h1ne : ((1 : ZMod p) ≠ 0) := one_ne_zero
      have hr := h_range h1ne
      rw [range_at_sixteen] at hr
      exact hr
  · rintro ⟨h_bool, h_range⟩
    refine ⟨?_, ?_, ?_⟩
    · ring
    · linear_combination h_bool
    · intro _
      rw [range_at_sixteen]
      exact h_range

end SP1Clean.U16MSBOp
