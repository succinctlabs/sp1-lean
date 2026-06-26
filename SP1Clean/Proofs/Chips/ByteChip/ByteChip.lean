import SP1Clean.Model.Channels
import SP1Clean.Math.Bitwise
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
import Clean.Gadgets.And.And8
import Clean.Gadgets.Or.Or8
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The in-circuit `ByteChip` provider (push side of SP1's byte-op table)

SP1's `ByteChip` (`crates/core/machine/src/bytes/air.rs`) is a **preprocessed** table over all
`(b, c) ∈ [0, 256)²` that `receive_byte`s six rows per `(b, c)` pair — one per `ByteOpcode` in
`byte_table() = [AND, OR, XOR, U8Range, LTU, MSB]` (indices `0..5`). On the Byte bus those receives are
*pushes* of valid byte-table rows, balanced against the consumers' pulls. Clean has no "trusted
preprocessed table" primitive for channels, so a finished-`byteChannel` **provider must re-prove each
pushed row valid in-circuit** (the `ByteRowSpec` membership predicate, `Model/ByteTable.lean`).

This module is the in-circuit provider's push side. For each opcode we build a Clean
`GeneralFormalCircuit` whose `main`:
- range-checks the byte operands in-circuit with Clean's `Gadgets.ToBits.rangeCheck 8` (an `assertion`
  subcircuit — a genuine bit-decomposition, *not* a byte lookup, so the provider owes nothing to the
  byte bus it provides), then
- witnesses a multiplicity `m` (the LogUp lookup count) and `byteChannel.pushIf m`-pushes the row,

and whose soundness discharges the push's `Requirements` (`ByteRowSpec` of the pushed row, since
`byteChannel` is a typed/`Normal` channel whose push owes its `Guarantees`) via the matching
`Model/ByteTable.lean` lemma. Faithful row forms (matching SP1's `bytes/air.rs`, opcodes per
`events/byte.rs`):
- `U8Range(3)` → `⟨3, 0, b, c⟩` (`byteRowSpec_u8range_pair`),
- `AND(0)/OR(1)/XOR(2)` → `⟨op, r, b, c⟩` (`byteRowSpec_byteOp`),
- `MSB(5)` → `⟨5, msb, b, 0⟩` (`byteRowSpec_msb`).

Each opcode lives in its own sub-namespace so its `main`/`Spec`/`circuit` stay independent. The
`RangeChip` (opcode 6, variable width) is a separate, harder chip and is *not* built here. -/

namespace SP1Clean.ByteChip

open Circuit
open SP1Clean (ByteRow ByteRowSpec)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `p > 2` (needed by `Gadgets.ToBits.rangeCheck`'s `Fact (p > 2)`), from `2^17 < p`. -/
-- `local` so this `Fact (p > 2)` (needed by `rangeCheck`) does not leak to importing files, where a
-- global instance would make their `omit [Fact (2^17 < p)]` clauses illegal (cf. `RangeChip`/`ByteTable`).
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- `1 < p` (so `(1 : ZMod p).val = 1`), from `2^17 < p`. -/
instance : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2^8 < p` — the bit-width bound `Gadgets.ToBits.rangeCheck 8` needs. -/
lemma two_pow_eight_lt : (2 : ℕ) ^ 8 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (2 : ℕ) ^ 8 < 2 ^ 17 := by norm_num
  omega

/-! ## op 3 — `U8Range`: push `⟨3, 0, b, c⟩` for two range-checked bytes -/

namespace U8Range

/-- The two checked bytes — the `b`/`c` slots of SP1's `U8Range` send `⟨3, 0, b, c⟩`. -/
structure Inputs (F : Type) where
  b : F
  c : F
deriving ProvableStruct

/-- Range-checks `b` and `c` as bytes (Clean `rangeCheck 8`, in-circuit bit decomposition), witnesses a
multiplicity `m`, and pushes the `U8Range` row `⟨3, 0, b, c⟩` onto `byteChannel` with multiplicity `m`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) input.b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) input.c
  let m ← witnessField (fun _ => 1)
  byteChannel.pushIf m (⟨3, 0, input.b, input.c⟩ : ByteRow (Expression (ZMod p)))

/-- The `U8Range` provider: pushes `⟨3, 0, b, c⟩` for two in-circuit range-checked bytes. `Spec` is the
two byte bounds; soundness derives them from the `rangeCheck` subcircuits and discharges the push's
`ByteRowSpec` requirement via `byteRowSpec_u8range_pair`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  Spec input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact ⟨h_holds, fun _ _ => (byteRowSpec_u8range_pair input_b input_c).mpr h_holds⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact h_assumptions

end U8Range

/-! ## op 5 — `MSB`: push `⟨5, msb, b, 0⟩`, `msb` = high bit of the byte `b`

Mirrors SP1's `operations/msb.rs` trick at byte width: `msb` boolean and `2*b - msb*256` a genuine byte
(`rangeCheck 8`) force `msb` to be `b`'s top bit (`msb = 1 ↔ 128 ≤ b.val`). -/

namespace MSB

/-- The checked byte — the `b` slot of SP1's `MSB` send `⟨5, msb, b, 0⟩` (the `msb` is derived). -/
structure Inputs (F : Type) where
  b : F
deriving ProvableStruct

/-- The 8-bit MSB core (byte analog of `U16MSBOperation.msb_of_raw`): `msb` boolean and `2*b - msb*256`
a genuine byte force `msb = 1 ↔ 128 ≤ b.val`. -/
lemma byte_msb_iff {b msb : ZMod p} (hb : b.val < 2 ^ 8)
    (hbool : msb = 0 ∨ msb = 1) (hr : (2 * b - msb * 256).val < 2 ^ 8) :
    msb = 1 ↔ 128 ≤ b.val := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h256] at hb hr
  have h2 : (2 * b : ZMod p).val = 2 * b.val := by
    rw [two_mul, ZMod.val_add_of_lt (by omega)]; omega
  rcases hbool with h0 | h1
  · subst h0
    simp only [zero_mul, sub_zero] at hr
    rw [h2] at hr
    refine ⟨fun h => absurd h zero_ne_one, fun h => ?_⟩
    exfalso; omega
  · subst h1
    simp only [one_mul] at hr
    have hge : 128 ≤ b.val := by
      have hsum : (2 * b - 256 : ZMod p) + 256 = 2 * b := by ring
      have hbound : (2 * b - 256 : ZMod p).val + (256 : ZMod p).val < p := by
        rw [val_256_zmod_p]; omega
      have hval := ZMod.val_add_of_lt hbound
      rw [hsum, h2, val_256_zmod_p] at hval
      omega
    exact ⟨fun _ => hge, fun _ => rfl⟩

/-- The completeness range fact: for a byte `b`, the value `2*b - msb*256` (with `msb` `b`'s high bit)
is itself a byte. Both branches reduce the field value to a `Nat.cast` of a `< 256` natural. -/
lemma byte_msb_range {b : ZMod p} (hb : b.val < 2 ^ 8) :
    (2 * b - (if 128 ≤ b.val then 1 else 0) * 256).val < 2 ^ 8 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  rw [show (2 : ℕ) ^ 8 = 256 from by norm_num] at hb ⊢
  have hbc : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_zmod_val b
  split
  · rename_i hge
    rw [one_mul]
    have hcast : ((2 * b.val - 256 : ℕ) : ZMod p) = 2 * b - 256 := by
      rw [Nat.cast_sub (by omega : 256 ≤ 2 * b.val)]; push_cast; rw [hbc]
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]; omega
  · rename_i hlt
    rw [zero_mul, sub_zero]
    have hcast : ((2 * b.val : ℕ) : ZMod p) = 2 * b := by push_cast; rw [hbc]
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]; omega

/-- Range-checks `b` as a byte, witnesses its high bit `msb`, asserts `msb` boolean and `2*b - msb*256`
a byte (forcing `msb` to be the top bit), and pushes the `MSB` row `⟨5, msb, b, 0⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) b
  let msb ← witnessField (fun env => if 128 ≤ (env b).val then 1 else 0)
  assertion assertBool msb
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) (2 * b - msb * 256)
  let m ← witnessField (fun _ => 1)
  byteChannel.pushIf m (⟨5, msb, b, 0⟩ : ByteRow (Expression (ZMod p)))

/-- The `MSB` provider: pushes `⟨5, msb, b, 0⟩` where `msb` is the in-circuit-derived top bit of byte `b`.
`Spec` is `b.val < 2^8` (the only verifier-visible input fact); soundness derives the `msb` boolean and
the `msb = 1 ↔ 128 ≤ b.val` relation and discharges the push's `ByteRowSpec` via `byteRowSpec_msb`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  Spec input _ _ := input.b.val < 2 ^ 8
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    obtain ⟨hb, hbool, hr⟩ := h_holds
    refine ⟨hb, fun _ _ => (byteRowSpec_msb _ _).mpr ⟨⟨?_, hb⟩, hbool, byte_msb_iff hb hbool ?_⟩⟩
    · rcases hbool with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
    · rw [sub_eq_add_neg]; exact hr
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    obtain ⟨hmsb, -⟩ := h_env
    refine ⟨h_assumptions, ?_, ?_⟩
    · rw [hmsb]; split <;> simp [IsBool]
    · rw [hmsb, ← sub_eq_add_neg]; exact byte_msb_range h_assumptions

end MSB

/-! ## ops 0/1/2 — byte AND/OR/XOR: push `⟨op, r, b, c⟩`, `r` = the per-byte bitwise result

Each reuses a self-contained Clean byte gadget — `And8`/`Or8` (or the `ByteXorTable` lookup for XOR) —
to derive `r = b op c` in-circuit. Those gadgets are sound by construction via Clean's static
`ByteXorTable` *lookup*, **not** the byte bus the provider provides, so there is no circular dependence.
SP1 emits one row per opcode `⟨op, r, b, c⟩` from `bytes/air.rs`; each is a separate fixed-opcode
provider here. -/

/-- `p > 512`, needed by Clean's `And8`/`Or8`/`ByteXorTable` gadgets. -/
instance : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

namespace AndByte

/-- The two operand bytes — `⟨0, r, b, c⟩`'s `b`/`c` slots (`r = b AND c` is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
deriving ProvableStruct

/-- Range-checks `b`, `c` as bytes, derives `r = b AND c` via Clean's `And8` gadget, and pushes the
`AND` row `⟨0, r, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let c := input.c
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) c
  let r ← Gadgets.And.And8.circuit ⟨b, c⟩
  let m ← witnessField (fun _ => 1)
  byteChannel.pushIf m (⟨0, r, b, c⟩ : ByteRow (Expression (ZMod p)))

/-- The `AND` provider: pushes `⟨0, r, b, c⟩` with `r = b AND c` derived in-circuit; soundness discharges
`ByteRowSpec` via `byteRowSpec_byteOp` (opcode `0`, `byteOp_zero`). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  Spec input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    obtain ⟨hb, hc, hand⟩ := h_holds
    have hr : (Expression.eval env (Gadgets.And.And8.circuit.output
        { x := input_var_b, y := input_var_c } (i₀ + 8 + 8))).val = input_b.val &&& input_c.val :=
      hand ⟨hb, hc⟩
    refine ⟨⟨hb, hc⟩, Or.inl rfl,
      fun _ _ => (byteRowSpec_byteOp _ _ _ (by rw [ZMod.val_zero]; norm_num)).mpr ⟨⟨?_, hb, hc⟩, ?_⟩⟩
    · rw [hr]; exact Nat.and_lt_two_pow (n := 8) input_b.val hc
    · rw [ZMod.val_zero, byteOp_zero]; exact hr
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact ⟨h_assumptions.1, h_assumptions.2, h_assumptions⟩

end AndByte

namespace OrByte

/-- The two operand bytes — `⟨1, r, b, c⟩`'s `b`/`c` slots (`r = b OR c` is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
deriving ProvableStruct

/-- Range-checks `b`, `c` as bytes, derives `r = b OR c` via Clean's `Or8` gadget, and pushes the
`OR` row `⟨1, r, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let c := input.c
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) c
  let r ← Gadgets.Or.Or8.circuit ⟨b, c⟩
  let m ← witnessField (fun _ => 1)
  byteChannel.pushIf m (⟨1, r, b, c⟩ : ByteRow (Expression (ZMod p)))

/-- The `OR` provider: pushes `⟨1, r, b, c⟩` with `r = b OR c` derived in-circuit; soundness discharges
`ByteRowSpec` via `byteRowSpec_byteOp` (opcode `1`, `byteOp_one`). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  Spec input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    obtain ⟨hb, hc, hor⟩ := h_holds
    have hr : (Expression.eval env (Gadgets.Or.Or8.circuit.output
        { x := input_var_b, y := input_var_c } (i₀ + 8 + 8))).val = input_b.val ||| input_c.val ∧
        (Expression.eval env (Gadgets.Or.Or8.circuit.output
        { x := input_var_b, y := input_var_c } (i₀ + 8 + 8))).val < 256 :=
      hor ⟨hb, hc⟩
    refine ⟨⟨hb, hc⟩, Or.inl rfl,
      fun _ _ => (byteRowSpec_byteOp _ _ _ (by rw [ZMod.val_one]; norm_num)).mpr ⟨⟨hr.2, hb, hc⟩, ?_⟩⟩
    rw [ZMod.val_one, byteOp_one]; exact hr.1
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact ⟨h_assumptions.1, h_assumptions.2, h_assumptions⟩

end OrByte

namespace XorByte

/-- The two operand bytes — `⟨2, r, b, c⟩`'s `b`/`c` slots (`r = b XOR c` is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
deriving ProvableStruct

/-- Range-checks `b`, `c` as bytes, derives `r = b XOR c` via Clean's static `ByteXorTable` lookup, and
pushes the `XOR` row `⟨2, r, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let c := input.c
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) c
  let r ← witnessField (fun env => (((env b).val ^^^ (env c).val : ℕ) : ZMod p))
  lookup Gadgets.Xor.ByteXorTable (b, c, r)
  let m ← witnessField (fun _ => 1)
  byteChannel.pushIf m (⟨2, r, b, c⟩ : ByteRow (Expression (ZMod p)))

/-- The `XOR` provider: pushes `⟨2, r, b, c⟩` with `r = b XOR c` from the `ByteXorTable` lookup; soundness
discharges `ByteRowSpec` via `byteRowSpec_byteOp` (opcode `2`, `byteOp_two`). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  Spec input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, Gadgets.Xor.ByteXorTable]
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    obtain ⟨hb, hc, -, -, hxor⟩ := h_holds
    have hval2 : (2 : ZMod p).val = 2 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast]
      exact ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)
    refine ⟨⟨hb, hc⟩,
      fun _ _ => (byteRowSpec_byteOp _ _ _ (by rw [hval2]; norm_num)).mpr ⟨⟨?_, hb, hc⟩, ?_⟩⟩
    · rw [hxor]; exact Nat.xor_lt_two_pow (n := 8) hb hc
    · rw [hval2, byteOp_two]; exact hxor
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, Gadgets.Xor.ByteXorTable]
    obtain ⟨hb, hc⟩ := h_assumptions
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have hxlt : input_b.val ^^^ input_c.val < 256 := Nat.xor_lt_two_pow (n := 8) hb hc
    refine ⟨hb, hc, hb, hc, ?_⟩
    rw [h_env.1, ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]

end XorByte

end SP1Clean.ByteChip
