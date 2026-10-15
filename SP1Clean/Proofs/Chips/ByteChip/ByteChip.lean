import ToClean.Gadgets.LookupProjection
import ToClean.Gadgets.BitwiseByte
import SP1Clean.Model.Channels
import SP1Clean.Math.Bitwise
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
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
- range-checks the byte operands in-circuit with Clean's bundled bit decomposition (directly in the bitwise gadget
  or through `Gadgets.ToBits.rangeCheck 8`), then
- reads the explicit multiplicity column `m` from the row and `byteChannel.pushIf m`-pushes the row,

and whose soundness discharges the push's `Requirements` (`ByteRowSpec` of the pushed row, since
`byteChannel` is a typed/`Normal` channel whose push owes its `Guarantees`) via the matching
`Model/ByteTable.lean` lemma. Faithful row forms (matching SP1's `bytes/air.rs`, opcodes per
`events/byte.rs`):
- `U8Range(3)` → `⟨3, 0, b, c⟩` (`byteRowSpec_u8range_pair`),
- `AND(0)/OR(1)/XOR(2)` → `⟨op, r, b, c⟩` (`byteRowSpec_byteOp`),
- `MSB(5)` → `⟨5, msb, b, 0⟩` (`byteRowSpec_msb`),
- `LTU(4)` → `⟨4, ltu, b, c⟩` (`byteRowSpec_ltu`).

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
  have := Fact.out (p := 2 ^ 17 < p); omega

/-! ## op 3 — `U8Range`: push `⟨3, 0, b, c⟩` for two range-checked bytes -/

namespace U8Range

/-- The two checked bytes — the `b`/`c` slots of SP1's `U8Range` send `⟨3, 0, b, c⟩`. -/
structure Inputs (F : Type) where
  b : F
  c : F
  /-- The LogUp count for this preprocessed byte-table key. Zero is padding; counts greater than
  one aggregate repeated consumer occurrences. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Range-checks `b` and `c` as bytes (Clean `rangeCheck 8`, in-circuit bit decomposition) and
pushes the `U8Range` row `⟨3, 0, b, c⟩` at the explicit input multiplicity. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) input.b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) input.c
  byteChannel.pushIf input.multiplicity
    (⟨3, 0, input.b, input.c⟩ : ByteRow (Expression (ZMod p)))

/-- The `U8Range` provider: pushes `⟨3, 0, b, c⟩` for two in-circuit range-checked bytes. `Spec` is the
two byte bounds; soundness derives them from the `rangeCheck` subcircuits and discharges the push's
`ByteRowSpec` requirement via `byteRowSpec_u8range_pair`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.byte.u8_range"
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

/-- The provider's static lookup keys, independent of the interaction multiplicity. -/
@[circuit_norm] theorem main_lookupNames (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]

end U8Range

/-! ## op 5 — `MSB`: push `⟨5, msb, b, 0⟩`, `msb` = high bit of the byte `b`

Mirrors SP1's `operations/msb.rs` trick at byte width: `msb` boolean and `2*b - msb*256` a genuine byte
(`rangeCheck 8`) force `msb` to be `b`'s top bit (`msb = 1 ↔ 128 ≤ b.val`). -/

namespace MSB

/-- The checked byte — the `b` slot of SP1's `MSB` send `⟨5, msb, b, 0⟩` (the `msb` is derived). -/
structure Inputs (F : Type) where
  b : F
  /-- The LogUp count for this byte-table key. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The 8-bit MSB core (byte analog of `U16MSBOperation.msb_of_raw`): `msb` boolean and `2*b - msb*256`
a genuine byte force `msb = 1 ↔ 128 ≤ b.val`. -/
lemma byte_msb_iff {b msb : ZMod p} (hb : b.val < 2 ^ 8)
    (hbool : msb = 0 ∨ msb = 1) (hr : (2 * b - msb * 256).val < 2 ^ 8) :
    msb = 1 ↔ 128 ≤ b.val := by
  have hp : 2 ^ 17 < p := Fact.out
  rw [show (2 : ℕ) ^ 8 = 256 from by norm_num] at hb hr
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
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let b := input.b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) b
  let msb ← witnessField (.ite (127 <? b.val) 1 0)
  assertion assertBool msb
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) (2 * b - msb * 256)
  byteChannel.pushIf input.multiplicity
    (⟨5, msb, b, 0⟩ : ByteRow (Expression (ZMod p)))
  return msb

/-- The `MSB` provider returns and pushes the in-circuit-derived top bit of byte `b`.  Its semantic
`Spec` exposes that result even when the row multiplicity is zero; soundness also discharges the
push's `ByteRowSpec` requirement via `byteRowSpec_msb`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs field where
  name := "sp1.native.byte.msb"
  main
  Spec input output _ :=
    input.b.val < 2 ^ 8 ∧ output = if 128 ≤ input.b.val then 1 else 0
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    obtain ⟨hb, hbool, hr⟩ := h_holds
    have hiff := byte_msb_iff hb hbool hr
    have hvalue : Expression.eval env
        (var ⟨i₀ + (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt).localLength input_var_b⟩) =
        if 128 ≤ input_b.val then 1 else 0 := by
      split
      · rename_i hge
        exact hiff.mpr hge
      · rename_i hlt
        rcases hbool with hzero | hone
        · exact hzero
        · exact False.elim (hlt (hiff.mp hone))
    refine ⟨⟨hb, hvalue⟩,
      fun _ _ => (byteRowSpec_msb _ _).mpr ⟨⟨?_, hb⟩, hbool, hiff⟩⟩
    · rcases hbool with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    refine ⟨h_assumptions, ?_, ?_⟩
    · rw [h_env]; split <;> simp [IsBool]
    · rw [h_env]; exact byte_msb_range h_assumptions

/-- The provider's static lookup keys, independent of the interaction multiplicity. -/
@[circuit_norm] theorem main_lookupNames (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]

end MSB

/-! ## ops 0/1/2 — byte AND/OR/XOR: push `⟨op, r, b, c⟩`, `r` = the per-byte bitwise result

Each composes the same lookup-free bitwise gadget: two Clean bit decompositions and a packed
bit polynomial derive `r = b op c`. The provider has no legacy static lookup or circular byte-bus
dependency. Its result and operand bounds remain specified when multiplicity is zero.
SP1 emits one row per opcode `⟨op, r, b, c⟩` from `bytes/air.rs`; each is a separate fixed-opcode
provider here. -/

namespace AndByte

/-- The two operand bytes — `⟨0, r, b, c⟩`'s `b`/`c` slots (`r = b AND c` is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
  /-- The LogUp count for this byte-table key. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Range-checks `b`, `c` as bytes, derives `r = b AND c` via the bit-decomposition gadget, and pushes the
`AND` row `⟨0, r, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let b := input.b
  let c := input.c
  let r ← Gadgets.BitwiseByte.circuit .and two_pow_eight_lt (b, c)
  byteChannel.pushIf input.multiplicity
    (⟨0, r, b, c⟩ : ByteRow (Expression (ZMod p)))
  return r

/-- The `AND` provider returns and pushes `r = b AND c`; exposing `r` in `Spec` preserves the
semantic result for zero-multiplicity rows as well. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs field where
  name := "sp1.native.byte.and"
  main
  Spec input output _ :=
    (input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) ∧
      output.val = input.b.val &&& input.c.val
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.BitwiseByte.circuit, Gadgets.BitwiseByte.Op.apply]
    obtain ⟨⟨hb, hc⟩, hr⟩ := h_holds
    refine ⟨⟨⟨hb, hc⟩, hr⟩,
      fun _ _ => (byteRowSpec_byteOp _ _ _ (by rw [ZMod.val_zero]; norm_num)).mpr ⟨⟨?_, hb, hc⟩, ?_⟩⟩
    · rw [hr]; exact Nat.and_lt_two_pow (n := 8) input_b.val hc
    · rw [ZMod.val_zero, byteOp_zero]; exact hr
  completeness := by
    circuit_proof_start [Gadgets.BitwiseByte.circuit]
    exact h_assumptions

/-- The provider's static lookup keys, independent of the interaction multiplicity. -/
@[circuit_norm] theorem main_lookupNames (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, Gadgets.BitwiseByte.circuit, circuit_norm]

end AndByte

namespace OrByte

/-- The two operand bytes — `⟨1, r, b, c⟩`'s `b`/`c` slots (`r = b OR c` is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
  /-- The LogUp count for this byte-table key. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Range-checks `b`, `c` as bytes, derives `r = b OR c` via the bit-decomposition gadget, and pushes the
`OR` row `⟨1, r, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let b := input.b
  let c := input.c
  let r ← Gadgets.BitwiseByte.circuit .or two_pow_eight_lt (b, c)
  byteChannel.pushIf input.multiplicity
    (⟨1, r, b, c⟩ : ByteRow (Expression (ZMod p)))
  return r

/-- The `OR` provider returns and pushes `r = b OR c`; the result remains specified independently
of the interaction multiplicity. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs field where
  name := "sp1.native.byte.or"
  main
  Spec input output _ :=
    (input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) ∧
      output.val = input.b.val ||| input.c.val
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.BitwiseByte.circuit, Gadgets.BitwiseByte.Op.apply]
    obtain ⟨⟨hb, hc⟩, hr⟩ := h_holds
    refine ⟨⟨⟨hb, hc⟩, hr⟩,
      fun _ _ => (byteRowSpec_byteOp _ _ _ (by rw [ZMod.val_one]; norm_num)).mpr ⟨⟨?_, hb, hc⟩, ?_⟩⟩
    · rw [hr]; exact Nat.or_lt_two_pow (n := 8) hb hc
    · rw [ZMod.val_one, byteOp_one]; exact hr
  completeness := by
    circuit_proof_start [Gadgets.BitwiseByte.circuit]
    exact h_assumptions

/-- The provider's static lookup keys, independent of the interaction multiplicity. -/
@[circuit_norm] theorem main_lookupNames (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, Gadgets.BitwiseByte.circuit, circuit_norm]

end OrByte

namespace XorByte

/-- The two operand bytes — `⟨2, r, b, c⟩`'s `b`/`c` slots (`r = b XOR c` is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
  /-- The LogUp count for this byte-table key. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Range-checks `b`, `c` as bytes, derives `r = b XOR c` via the bit-decomposition gadget, and
pushes the `XOR` row `⟨2, r, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let b := input.b
  let c := input.c
  let r ← Gadgets.BitwiseByte.circuit .xor two_pow_eight_lt (b, c)
  byteChannel.pushIf input.multiplicity
    (⟨2, r, b, c⟩ : ByteRow (Expression (ZMod p)))
  return r

/-- The `XOR` provider returns and pushes `r = b XOR c`; the result is part of the semantic `Spec`
even when no lookup demand is assigned to the row. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs field where
  name := "sp1.native.byte.xor"
  main
  Spec input output _ :=
    (input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) ∧
      output.val = input.b.val ^^^ input.c.val
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.BitwiseByte.circuit, Gadgets.BitwiseByte.Op.apply]
    obtain ⟨⟨hb, hc⟩, hr⟩ := h_holds
    refine ⟨⟨⟨hb, hc⟩, hr⟩,
      fun _ _ => (byteRowSpec_byteOp _ _ _ (by rw [val_2_zmod_p]; norm_num)).mpr ⟨⟨?_, hb, hc⟩, ?_⟩⟩
    · rw [hr]; exact Nat.xor_lt_two_pow (n := 8) hb hc
    · rw [val_2_zmod_p, byteOp_two]; exact hr
  completeness := by
    circuit_proof_start [Gadgets.BitwiseByte.circuit]
    exact h_assumptions

/-- The provider's static lookup keys, independent of the interaction multiplicity. -/
@[circuit_norm] theorem main_lookupNames (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, Gadgets.BitwiseByte.circuit, circuit_norm]

end XorByte

/-! ## op 4 — `LTU`: push `⟨4, ltu, b, c⟩`, `ltu` = the boolean unsigned comparison `b <u c`

Mirrors the `MSB` derivation trick at byte width: `ltu` boolean and `b - c + ltu*256` a genuine byte
(`rangeCheck 8`) force `ltu` to be the comparison bit (`ltu = 1 ↔ b.val < c.val`). The machine's
consumer is the AluX0 chip's `opcode < 29` check (its pull `⟨4, 1, opcode, 29⟩`). -/

namespace Ltu

/-- The two operand bytes — `⟨4, ltu, b, c⟩`'s `b`/`c` slots (the `ltu` bit is derived). -/
structure Inputs (F : Type) where
  b : F
  c : F
  /-- The LogUp count for this byte-table key. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The 8-bit unsigned-comparison core (byte analog of `MSB.byte_msb_iff`): `ltu` boolean and
`b - c + ltu * 256` a genuine byte force `ltu = 1 ↔ b.val < c.val`. -/
lemma byte_ltu_iff {b c ltu : ZMod p} (hb : b.val < 2 ^ 8) (hc : c.val < 2 ^ 8)
    (hbool : ltu = 0 ∨ ltu = 1) (hr : (b - c + ltu * 256).val < 2 ^ 8) :
    ltu = 1 ↔ b.val < c.val := by
  have hp : 2 ^ 17 < p := Fact.out
  rw [show (2 : ℕ) ^ 8 = 256 from by norm_num] at hb hc hr
  rcases hbool with h0 | h1
  · subst h0
    simp only [zero_mul, add_zero] at hr
    have hge : c.val ≤ b.val := by
      have hsum : (b - c : ZMod p) + c = b := by ring
      have hval := ZMod.val_add_of_lt (show (b - c : ZMod p).val + c.val < p by omega)
      rw [hsum] at hval
      omega
    exact ⟨fun h => absurd h zero_ne_one, fun h => absurd h (by omega)⟩
  · subst h1
    simp only [one_mul] at hr
    have hlt : b.val < c.val := by
      have hsum : (b - c + 256 : ZMod p) + c = b + 256 := by ring
      have hval := ZMod.val_add_of_lt (show (b - c + 256 : ZMod p).val + c.val < p by omega)
      have hb256 : (b + 256 : ZMod p).val = b.val + 256 := by
        rw [ZMod.val_add_of_lt (by rw [val_256_zmod_p]; omega), val_256_zmod_p]
      rw [hsum, hb256] at hval
      omega
    exact ⟨fun _ => hlt, fun _ => rfl⟩

/-- The completeness range fact: for bytes `b`, `c`, the value `b - c + ltu*256` (with `ltu` the
comparison bit) is itself a byte. Both branches reduce the field value to a `Nat.cast` of a `< 256`
natural (mirror of `MSB.byte_msb_range`). -/
lemma byte_ltu_range {b c : ZMod p} (hb : b.val < 2 ^ 8) (hc : c.val < 2 ^ 8) :
    (b - c + (if b.val < c.val then 1 else 0) * 256).val < 2 ^ 8 := by
  have hp : 2 ^ 17 < p := Fact.out
  rw [show (2 : ℕ) ^ 8 = 256 from by norm_num] at hb hc ⊢
  have hbc : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_zmod_val b
  have hcc : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
  split
  · rename_i hlt
    rw [one_mul]
    have hcast : ((b.val + 256 - c.val : ℕ) : ZMod p) = b - c + 256 := by
      rw [Nat.cast_sub (by omega : c.val ≤ b.val + 256)]; push_cast; rw [hbc, hcc]; ring
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]; omega
  · rename_i hge
    rw [zero_mul, add_zero]
    have hcast : ((b.val - c.val : ℕ) : ZMod p) = b - c := by
      rw [Nat.cast_sub (by omega : c.val ≤ b.val), hbc, hcc]
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]; omega

/-- Range-checks `b` and `c` as bytes, witnesses the comparison bit `ltu`, asserts `ltu` boolean and
`b - c + ltu * 256` a byte (forcing `ltu` to be the unsigned comparison `b <u c`), and pushes the
`LTU` row `⟨4, ltu, b, c⟩`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let b := input.b
  let c := input.c
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) b
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) c
  let ltu ← witnessField (.ite (.flt (.expr b) (.expr c)) 1 0)
  assertion assertBool ltu
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt) (b - c + ltu * 256)
  byteChannel.pushIf input.multiplicity
    (⟨4, ltu, b, c⟩ : ByteRow (Expression (ZMod p)))
  return ltu

/-- The `LTU` provider returns and pushes the in-circuit-derived comparison bit.  The output
equation is part of `Spec`, so downstream faithful transports do not inspect witness internals. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs field where
  name := "sp1.native.byte.ltu"
  main
  Spec input output _ :=
    (input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8) ∧
      output = if input.b.val < input.c.val then 1 else 0
  ProverAssumptions input _ _ := input.b.val < 2 ^ 8 ∧ input.c.val < 2 ^ 8
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    obtain ⟨hb, hc, hbool, hr⟩ := h_holds
    have hiff := byte_ltu_iff hb hc hbool hr
    have hvalue : Expression.eval env
        (var ⟨i₀ + 8 + 8⟩) = if input_b.val < input_c.val then 1 else 0 := by
      split
      · rename_i hlt
        exact hiff.mpr hlt
      · rename_i hge
        rcases hbool with hzero | hone
        · exact hzero
        · exact False.elim (hge (hiff.mp hone))
    refine ⟨⟨⟨hb, hc⟩, hvalue⟩, fun _ _ =>
      (byteRowSpec_ltu _ _ _).mpr ⟨⟨?_, hb, hc⟩, hbool, hiff⟩⟩
    rcases hbool with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    refine ⟨h_assumptions.1, h_assumptions.2, ?_, ?_⟩
    · rw [h_env]; split <;> simp [IsBool]
    · rw [h_env]; exact byte_ltu_range h_assumptions.1 h_assumptions.2

/-- The provider's static lookup keys, independent of the interaction multiplicity. -/
@[circuit_norm] theorem main_lookupNames (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]

end Ltu

end SP1Clean.ByteChip
