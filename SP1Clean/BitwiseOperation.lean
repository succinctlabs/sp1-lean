import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Utils.Field
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.BitwiseOperation.Operation
import SP1Operations.Operation.BitwiseOperation.Constraints
import SP1Clean.ByteOpcodeTable

/-! # Tier 2c pilot: `BitwiseOperation` mirror

SP1's `BitwiseOperation` mirrors a per-byte bitwise op (AND/OR/XOR) for an
8-limb word. Its constraint list is **8 `send (.byte (ByteOpcode.ofNat
opcode) result[i] a[i] b[i]) is_real`** — and nothing else. This makes it the
single best Tier-2 test for the opcode-parametric, multi-payload byte
interaction encoding from `SP1Clean/ByteOpcodeTable.lean`.

The pilot deliverable is the **equivalence iff** between SP1's `allHold`
and the Clean spec — `FormalCircuit` integration is deferred per the
import-collision note in `IsZeroOperation.lean`.
-/

namespace SP1Clean.BitwiseOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- Clean-side circuit. Witnesses the 8-byte `result`, then performs 8
byte-opcode lookups, one per limb. The opcode flows through as a single
parameter; whichever `ByteOpcode` it resolves to (AND/OR/XOR for a typical
chip use) is checked by the `ByteOpcodeSpec` existential. -/
def main (a b : Vector (Expression (ZMod p)) 8) (opcode : Expression (ZMod p)) :
    Circuit (ZMod p) (Vector (Expression (ZMod p)) 8) := do
  let r0 ← witnessField (fun _ => 0)
  let r1 ← witnessField (fun _ => 0)
  let r2 ← witnessField (fun _ => 0)
  let r3 ← witnessField (fun _ => 0)
  let r4 ← witnessField (fun _ => 0)
  let r5 ← witnessField (fun _ => 0)
  let r6 ← witnessField (fun _ => 0)
  let r7 ← witnessField (fun _ => 0)
  -- 8 byte-opcode lookups. Row layout #v[opcode, result_i, a_i, b_i].
  lookup ByteOpcodeTable (#v[opcode, r0, a[0], b[0]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r1, a[1], b[1]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r2, a[2], b[2]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r3, a[3], b[3]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r4, a[4], b[4]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r5, a[5], b[5]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r6, a[6], b[6]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r7, a[7], b[7]] : Vector (Expression (ZMod p)) 4)
  return #v[r0, r1, r2, r3, r4, r5, r6, r7]

/-- Pilot Spec: under SP1's `is_real = 1`, each of the 8 byte-sends asserts
that `(ByteOpcode.ofNat opcode.val).constrain` holds on the per-byte
triple `(result[i], a[i], b[i])`.

This phrasing matches SP1's `toProp` exactly, which makes the iff a
case-split on `i`. The connection to `ByteOpcodeTable.ByteOpcodeSpec` (via
the existential over `ByteOpcode`) goes through `ByteOpcode.ofNat opcode.val`
as the witness — provable only when `opcode.val < 7`, a hypothesis that is
the **chip's** responsibility to supply (typically via an extra constraint
like `opcode * (opcode - 1) * (opcode - 2) = 0`). -/
def Spec (a b : Vector (ZMod p) 8) (opcode : ZMod p) (result : Vector (ZMod p) 8) : Prop :=
  ∀ i : Fin 8, (ByteOpcode.ofNat opcode.val).constrain
    (result[i.val]'i.is_lt) (a[i.val]'i.is_lt) (b[i.val]'i.is_lt)

omit [Fact (p > 512)] in
/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Pure case-split on the `Fin 8` index — no opcode
round-trip needed. -/
theorem iff_sp1
    (a b : Vector (ZMod p) 8) (opcode : ZMod p)
    (cols : BitwiseOperation (ZMod p)) :
    (BitwiseOperation.constraints (F := ZMod p) a b cols opcode 1).allHold ↔
    Spec a b opcode cols.result := by
  have h1ne : ((1 : ZMod p) ≠ 0) := one_ne_zero
  simp only [BitwiseOperation.constraints, SP1ConstraintList.allHold, List.Forall,
    SP1Constraint.toProp, Spec]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ i
    match i with
    | ⟨0, _⟩ => exact h0 h1ne
    | ⟨1, _⟩ => exact h1 h1ne
    | ⟨2, _⟩ => exact h2 h1ne
    | ⟨3, _⟩ => exact h3 h1ne
    | ⟨4, _⟩ => exact h4 h1ne
    | ⟨5, _⟩ => exact h5 h1ne
    | ⟨6, _⟩ => exact h6 h1ne
    | ⟨7, _⟩ => exact h7 h1ne
  · intro hSpec
    refine ⟨fun _ => hSpec ⟨0, by omega⟩, fun _ => hSpec ⟨1, by omega⟩,
            fun _ => hSpec ⟨2, by omega⟩, fun _ => hSpec ⟨3, by omega⟩,
            fun _ => hSpec ⟨4, by omega⟩, fun _ => hSpec ⟨5, by omega⟩,
            fun _ => hSpec ⟨6, by omega⟩, fun _ => hSpec ⟨7, by omega⟩⟩

omit [Fact (p > 512)] in
/-- Connection to `ByteOpcodeTable.ByteOpcodeSpec`. When `opcode.val < 7`
(a discipline the chip enforces — see e.g. `SP1Chips/BitwiseChip.lean`'s
`is_and ∨ is_or ∨ is_xor` decomposition), the existential over `ByteOpcode`
inside the table's `Spec` is witnessed by `ByteOpcode.ofNat opcode.val`. -/
lemma ByteOpcodeSpec_of_Spec_when_lt7
    (a b : Vector (ZMod p) 8) (opcode : ZMod p) (result : Vector (ZMod p) 8)
    (h_opcode : opcode.val < 7) (hSpec : Spec a b opcode result) :
    ∀ i : Fin 8,
      SP1Clean.ByteOpcodeSpec (#v[opcode, result[i.val]'i.is_lt,
        a[i.val]'i.is_lt, b[i.val]'i.is_lt] : Vector (ZMod p) 4) := by
  intro i
  refine ⟨ByteOpcode.ofNat opcode.val, ?_, hSpec i⟩
  -- `((ByteOpcode.ofNat opcode.val).toNat : ZMod p) = opcode.val = opcode`
  -- when `opcode.val < 7`: case-split on `opcode.val ∈ {0,…,6}`.
  have hround : ((opcode.val : ℕ) : ZMod p) = opcode := by
    exact_mod_cast ZMod.natCast_zmod_val opcode
  interval_cases opcode.val <;> push_cast at hround <;> simp [hround]

end SP1Clean.BitwiseOp
