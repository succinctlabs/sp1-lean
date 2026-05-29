import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Operations.Operation.MulOperation.Constraints
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.MulCarryChain

/-! # Witness-generation: the unsigned 16-byte multiply as a `FormalCircuit`

**Status: pilot (genuine semantic completeness via witnessed carry chain).**
Standalone — not imported by the `SP1Clean` lib root; validate with
`lake env lean SP1Clean/Operations/MulOperationWitnessed.lean`.

## Why this exists

Production `SP1Clean.MulOp` (`SP1Clean/Operations/MulOperation.lean`) is a
`FormalAssertion` whose carry/product columns are *free inputs* + a *semantic*
`Spec`, so its completeness is **false as structured** (nothing pins those
inputs; see the project memory `project-mul-witnessed-completeness`). This file
models the carry/product the way the SP1 prover actually fills them —
**internally generated `witnessVector` witnesses** — so the circuit becomes a
`FormalCircuit` (output = the 16-byte product) whose `Spec` is genuinely
*semantic* (`output.toBitVec128 = (b.extend false) * (c.extend false)`, the
unsigned `64×64→128` product) and whose completeness is *actually provable*.

Scope: the **unsigned** core (`sgn = false`, i.e. the `MUL`/`MULHU` path). It
exercises the genuinely-novel content — the witnessed carry chain — without the
chip-integration layer (signed/`msb` sign-extension, the five selectors, the
`a_word` per-variant extraction, the RV64 dispatch). Those are documented as the
next layer in `~/.claude/plans/make-a-plan-to-serialized-starlight.md`.

- **soundness** = forward `core_mul` (`SP1Operations/.../Constraints.lean`).
- **completeness** = the proven `SP1Clean.MulCarryChain` core (recurrence +
  carry/product bounds, instantiated at `cpNat` over the operand bytes).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulOpWitnessed

open Circuit
open SP1Clean (ByteOpcodeTable)
open SP1Clean.MulCarryChain (chainM carry product cpNat)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

/-- Two 8-byte operands (`BWord`s). -/
structure Inputs (F : Type) where
  b : fields 8 F
  c : fields 8 F
deriving ProvableStruct

/-- The `ℕ`-valued byte stream of a witnessed/evaluated `BWord`, zero-padded
past index 7 (the unsigned `setWidth` extension). -/
def byteFn (w : Vector (ZMod p) 8) : ℕ → ℕ :=
  fun k => if h : k < 8 then (w[k]'h).val else 0

/-- The cross-product stream for the operand bytes. -/
def cpOf (b c : Vector (ZMod p) 8) : ℕ → ℕ := cpNat (byteFn b) (byteFn c)

/-- Generated circuit: witness the 16 product bytes and 16 carries from the
schoolbook chain, emit the 16 carry-chain gates, the 16 carry `u16`-range
lookups and the 8 product-pair `u8`-range lookups, then return the product.
The cross-product expressions are written explicitly (zero-extended view:
bytes 8..15 are 0, so those terms drop) — they equal
`cp (b.extend false) (c.extend false) i` after unfolding `cp`. -/
def main (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var (fields 16) (ZMod p)) := do
  let b := input.b
  let cc := input.c
  let product ← witnessVector 16 (fun env =>
    Vector.ofFn (fun i =>
      ((MulCarryChain.product (cpOf (Vector.map (Expression.eval env) input.b)
        (Vector.map (Expression.eval env) input.c)) i.val : ℕ) : ZMod p)))
  let carry ← witnessVector 16 (fun env =>
    Vector.ofFn (fun i =>
      ((MulCarryChain.carry (cpOf (Vector.map (Expression.eval env) input.b)
        (Vector.map (Expression.eval env) input.c)) i.val : ℕ) : ZMod p)))
  let r256 : Expression (ZMod p) := 256
  -- 16 carry-chain gates: product[i] = cpᵢ (+ carry[i-1]) - carry[i] * 256.
  (product[0] - (b[0]*cc[0] - carry[0]*r256)) === 0
  (product[1] - (b[0]*cc[1] + b[1]*cc[0] + carry[0] - carry[1]*r256)) === 0
  (product[2] - (b[0]*cc[2] + b[1]*cc[1] + b[2]*cc[0] + carry[1] - carry[2]*r256)) === 0
  (product[3] - (b[0]*cc[3] + b[1]*cc[2] + b[2]*cc[1] + b[3]*cc[0] + carry[2] - carry[3]*r256)) === 0
  (product[4] - (b[0]*cc[4] + b[1]*cc[3] + b[2]*cc[2] + b[3]*cc[1] + b[4]*cc[0] + carry[3] - carry[4]*r256)) === 0
  (product[5] - (b[0]*cc[5] + b[1]*cc[4] + b[2]*cc[3] + b[3]*cc[2] + b[4]*cc[1] + b[5]*cc[0] + carry[4] - carry[5]*r256)) === 0
  (product[6] - (b[0]*cc[6] + b[1]*cc[5] + b[2]*cc[4] + b[3]*cc[3] + b[4]*cc[2] + b[5]*cc[1] + b[6]*cc[0] + carry[5] - carry[6]*r256)) === 0
  (product[7] - (b[0]*cc[7] + b[1]*cc[6] + b[2]*cc[5] + b[3]*cc[4] + b[4]*cc[3] + b[5]*cc[2] + b[6]*cc[1] + b[7]*cc[0] + carry[6] - carry[7]*r256)) === 0
  (product[8] - (b[1]*cc[7] + b[2]*cc[6] + b[3]*cc[5] + b[4]*cc[4] + b[5]*cc[3] + b[6]*cc[2] + b[7]*cc[1] + carry[7] - carry[8]*r256)) === 0
  (product[9] - (b[2]*cc[7] + b[3]*cc[6] + b[4]*cc[5] + b[5]*cc[4] + b[6]*cc[3] + b[7]*cc[2] + carry[8] - carry[9]*r256)) === 0
  (product[10] - (b[3]*cc[7] + b[4]*cc[6] + b[5]*cc[5] + b[6]*cc[4] + b[7]*cc[3] + carry[9] - carry[10]*r256)) === 0
  (product[11] - (b[4]*cc[7] + b[5]*cc[6] + b[6]*cc[5] + b[7]*cc[4] + carry[10] - carry[11]*r256)) === 0
  (product[12] - (b[5]*cc[7] + b[6]*cc[6] + b[7]*cc[5] + carry[11] - carry[12]*r256)) === 0
  (product[13] - (b[6]*cc[7] + b[7]*cc[6] + carry[12] - carry[13]*r256)) === 0
  (product[14] - (b[7]*cc[7] + carry[13] - carry[14]*r256)) === 0
  (product[15] - (carry[14] - carry[15]*r256)) === 0
  -- 16 carry u16-range lookups (opcode 6, bound 16 = 2^16).
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[0], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[1], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[2], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[3], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[4], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[5], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[6], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[7], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[8], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[9], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[10], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[11], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[12], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[13], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[14], 16, 0])
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), carry[15], 16, 0])
  -- 8 product-pair u8-range lookups (opcode 3).
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[0], product[1]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[2], product[3]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[4], product[5]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[6], product[7]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[8], product[9]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[10], product[11]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[12], product[13]])
  lookup ByteOpcodeTable (#v[(3 : Expression (ZMod p)), 0, product[14], product[15]])
  return product

set_option maxHeartbeats 1600000 in
-- 1.6M heartbeats: the `localLength_eq` / `output_eq` / `subcircuitsConsistent`
-- syntheses run `circuit_norm` over a 32-witness + 40-statement `main`.
instance elaborated : ElaboratedCircuit (ZMod p) Inputs (fields 16) where
  main := main
  localLength _ := 32
  output _ i0 := varFromOffset (fields 16) i0
  localLength_eq input offset := by simp only [main, circuit_norm]
  output_eq input offset := by simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by simp +arith only [main, circuit_norm]

/-- Both operands' bytes fit in a byte. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  BWord.isU64 input.b ∧ BWord.isU64 input.c

/-- Semantic spec: the synthesized 16-byte product equals the unsigned
`128`-bit product of the two operands (`core_mul`'s conclusion at `sgn = false`). -/
def Spec (input : Inputs (ZMod p)) (product : Vector (ZMod p) 16) : Prop :=
  BDWord.toBitVec128 product
    = BDWord.toBitVec128 (BWord.extend input.b false)
      * BDWord.toBitVec128 (BWord.extend input.c false)

-- CLOSURE STEP (soundness — forward `core_mul`). After `circuit_proof_start`:
--   `h_holds` = 16 carry-chain gate equations (`env.get (i₀+i) + -(<bytes> + … ) = 0`)
--     ∧ 16 carry `ByteOpcodeTable.Soundness` ∧ 8 product `ByteOpcodeTable.Soundness`;
--   `h_input` : `Vector.map (eval env) input_var_{b,c} = input_{b,c}`;  goal :
--   `BDWord.toBitVec128 (map eval (mapRange 16 (var i₀+i))) = (b.extend false)·(c.extend false)`.
-- 1. `simp only [Lookup.Soundness, Table.toRaw, ByteOpcodeTable] at h_holds`; destructure into
--    `g0..g15` (gates) + `cr0..cr15` (carry specs) + `pr0..pr7` (product-pair specs).
-- 2. Set `prod := Vector.ofFn (i ↦ env.get (i₀+i))`, `cy := Vector.ofFn (i ↦ env.get (i₀+16+i))`.
-- 3. Carry bounds `cy[i].val < 65536 := byteOpcodeSpec_range16 _ cr_i`;
--    product bounds `prod[k].val < 256` from `(byteOpcodeSpec_u8range_lt _ _ pr_j).1/.2` then the
--    ZMod-`<` → `.val <` conversion (`(256:ZMod p).val = 256`, `ZMod.val_natCast_of_lt`).
-- 4. The 16 `core_mul` gate hypotheses `prod[i] = cp (b.extend false) (c.extend false) i + … - cy[i]·256`:
--    per `i`, `simp only [cp, BWord.extend, Vector.ofFn, Vector.getElem_ofFn]` unfolds `cp` to the
--    explicit byte products, then `linear_combination g_i` (after rewriting `eval input_var_b[j] =
--    input_b[j]` via `h_input` + `Vector.getElem_map`).
-- 5. `core_mul input_b input_c isU64_b isU64_c false false prod cy <gates> <carry-bnds> <prod-bnds>`
--    gives `prod.toBitVec128 = (b.extend false)·(c.extend false)`; finish by rewriting the goal's
--    `map eval (mapRange …)` to `prod` (`Vector.ext` + `Vector.getElem_map`/`getElem_mapRange`).
omit [Fact (2 ^ 24 < p)] in
/-- The product `ByteOpcodeSpec`'s ZMod-`<` byte bound as a `.val` bound. -/
private lemma val_lt_256_of_lt {x : ZMod p} (h : x < 256) : x.val < 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : (256 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h256 : (256 : ZMod p).val = 256 := by
    rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) by push_cast; rfl, ZMod.val_natCast_of_lt hp]
  have hv : x.val < (256 : ZMod p).val := h
  omega

set_option maxHeartbeats 1600000 in
-- 1.6M heartbeats: 16 carry-chain gates each run a full `cp`/`BWord.extend`
-- unfold + `linear_combination`, and the `core_mul` application threads 48 hypotheses.
theorem soundness : Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hb, hc⟩ := h_input
  obtain ⟨isU64_b, isU64_c⟩ := h_assumptions
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw, ByteOpcodeTable] at h_holds
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15,
          cr0, cr1, cr2, cr3, cr4, cr5, cr6, cr7, cr8, cr9, cr10, cr11, cr12, cr13, cr14, cr15,
          pr0, pr1, pr2, pr3, pr4, pr5, pr6, pr7⟩ := h_holds
  set prod : BDWord (ZMod p) := Vector.ofFn (fun i : Fin 16 => env.get (i₀ + i.val)) with hprod
  set cy : BDWord (ZMod p) := Vector.ofFn (fun i : Fin 16 => env.get (i₀ + 16 + i.val)) with hcy
  unfold id at *
  have key := MulOperation.core_mul input_b input_c isU64_b isU64_c false false prod cy
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g0)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g1)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g2)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g3)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g4)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g5)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g6)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g7)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g8)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g9)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g10)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g11)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g12)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g13)
    (by
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      (try rw [← hb, ← hc]); (try simp only [Vector.getElem_map])
      linear_combination g14)
    (by
      -- `cp _ _ 15 = 0` (unsigned: no byte products at limb 15), so no eval bridge needed.
      simp only [hprod, hcy, Vector.getElem_ofFn, Nat.add_zero]
      simp [cp, Vector.ofFn, Vector.get, BWord.extend]
      linear_combination g15)
    (by simp only [hcy, Vector.getElem_ofFn, Nat.add_zero]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr0)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr1)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr2)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr3)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr4)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr5)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr6)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr7)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr8)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr9)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr10)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr11)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr12)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr13)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr14)
    (by simp only [hcy, Vector.getElem_ofFn]; exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ cr15)
    (by simp only [hprod, Vector.getElem_ofFn, Nat.add_zero]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr0).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr0).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr1).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr1).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr2).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr2).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr3).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr3).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr4).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr4).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr5).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr5).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr6).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr6).2)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr7).1)
    (by simp only [hprod, Vector.getElem_ofFn]; exact val_lt_256_of_lt (SP1Clean.MulOp.byteOpcodeSpec_u8range_lt _ _ pr7).2)
  have hpe : Vector.map (Expression.eval env)
      (Vector.mapRange 16 (fun i => var { index := i₀ + i })) = prod := by
    apply Vector.ext; intro k hk
    simp only [hprod, Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_mapRange,
      Expression.eval]
  rw [hpe]
  exact key

-- CLOSURE STEP (completeness — the witnessed-construction heart, via `SP1Clean.MulCarryChain`).
-- After `circuit_proof_start`, `h_env` (`UsesLocalWitnessesCompleteness`) pins each witnessed cell to
-- its `main` compute: `env.get (i₀+i) = (MulCarryChain.product (cpOf b c) i : ZMod p)` and
-- `env.get (i₀+16+i) = (MulCarryChain.carry (cpOf b c) i : ZMod p)`; `h_assumptions` gives
-- `BWord.isU64 b`, `BWord.isU64 c`; goal = the 16 gates ∧ 24 `Lookup.Completeness`.
-- 1. From `isU64`, every byte `< 256`, so `byteFn b`/`byteFn c ≤ 255`, hence
--    `cpOf b c i ≤ cpBound` by `MulCarryChain.cpNat_le_cpBound` (for `i ≤ 15`).
-- 2. Carry-chain gates: rewrite the witnessed cells via `h_env`, then discharge gate `i` with
--    `MulCarryChain.gate_zero`/`gate_succ` (the `ZMod` recurrence) after proving
--    `(cpOf b c i : ZMod p) = <explicit byte products>` (= `cpNat` cast: `push_cast` + `byteFn`
--    unfolding + `(b[j].val : ZMod p) = b[j]` via `ZMod.natCast_zmod_val`).
-- 3. Carry `u16`-range lookups (`Lookup.Completeness` = `ByteOpcodeSpec #v[6, carry i, 16, 0]`):
--    witness `ByteOpcode.Range`; the value bound `< 65536` is `MulCarryChain.carry_lt` +
--    `carry_val` (`.val = carry … < 65536`).
-- 4. Product `u8`-range lookups (`ByteOpcodeSpec #v[3, 0, prod 2k, prod 2k+1]`): witness
--    `ByteOpcode.U8Range`; bounds `< 256` from `MulCarryChain.product_lt` + `product_val`.
-- (Helpers `byteOpcodeSpec_range16_of_lt` / a `u8range`-constructor mirror the soundness extractors.)
theorem completeness : Completeness (ZMod p) elaborated Assumptions := by
  sorry

/-- The witnessed unsigned multiply `FormalCircuit`. -/
def circuit : FormalCircuit (ZMod p) Inputs (fields 16) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SP1Clean.MulOpWitnessed
