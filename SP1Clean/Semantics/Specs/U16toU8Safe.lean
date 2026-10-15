module

public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.U16toU8Operation
import SP1Clean.Math.Bitwise

/-! # Safe byte-decomposition contract

Active rows decompose four limbs into bounded low/high bytes. The contract and its range
readout are independent of the byte-channel implementation; padding leaves the bytes free.
-/

@[expose] public section

namespace SP1Clean.U16toU8OperationSafe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The four 16-bit input limbs to split, the already-`populate`d low-byte column struct, and the
`is_real` gate (the `eval` params verbatim, faithful to SP1's `U16toU8OperationSafeInput`). -/
structure Inputs (F : Type) where
  /-- Four operand limbs to decompose. -/
  u16_values : fields 4 F
  /-- Committed low bytes; high bytes are derived from the limbs. -/
  cols : Circuits.Types.U16toU8Operation F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The ungated byte-decomposition content (2-arg, over explicit operand limbs + columns): for each
limb the low and high bytes are genuine bytes and reassemble the limb. Reused by composing operations
(e.g. `MulOperation`) that need the decomposition fact directly. -/
def DecompSpec (u16_values : Word (ZMod p)) (cols : Circuits.Types.U16toU8Operation (ZMod p)) : Prop :=
  ∀ i : Fin 4,
    cols.low_bytes[i].val < 256 ∧
    ((u16_values[i] - cols.low_bytes[i]) * 256⁻¹).val < 256 ∧
    u16_values[i] = cols.low_bytes[i] + (u16_values[i] - cols.low_bytes[i]) * 256⁻¹ * 256

/-- Semantic contract (`is_real`-gated, `FormalAssertion`-style): on a real row, the eight output bytes
are the little-endian decomposition of the four limbs. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 → DecompSpec input.u16_values input.cols

/-- The only composer-supplied fact is that the row gate is binary. The four limb bounds are
conclusions of this gadget's own byte-table pulls, not preconditions supplied by its parent. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 0 ∨ input.is_real = 1

/-- The reassembly identity `low + (u - low) * 256⁻¹ * 256 = u`. -/
lemma reassemble (u low : ZMod p) :
    u = low + (u - low) * (256 : ZMod p)⁻¹ * 256 := by
  have h256 : (256 : ZMod p)⁻¹ * 256 = 1 := inv_mul_cancel₀ val_256_ne_zero
  rw [mul_assoc, h256, mul_one]; ring

private lemma byteComposeVal {x lo hi : ZMod p} (hlo : lo.val < 256) (hhi : hi.val < 256)
    (h : x = lo + hi * 256) : x.val = lo.val + hi.val * 256 := by
  subst x
  have hhi256 : (hi * 256 : ZMod p).val = hi.val * 256 := by
    rw [ZMod.val_mul, val_256_zmod_p, Nat.mod_eq_of_lt]
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  rw [ZMod.val_add_of_lt, hhi256]
  have := Fact.out (p := 2 ^ 17 < p)
  omega

/-- A successful byte decomposition proves that every input limb is genuinely 16-bit. This is the
semantic range fact that composing arithmetic gadgets should consume instead of assuming it. -/
theorem isU64_of_decomp {u16_values : Word (ZMod p)}
    {cols : Circuits.Types.U16toU8Operation (ZMod p)} (h : DecompSpec u16_values cols) :
    Word.isU64 u16_values := by
  intro i
  have hi := h i
  rw [byteComposeVal hi.1 hi.2.1 hi.2.2]
  omega

end SP1Clean.U16toU8OperationSafe
