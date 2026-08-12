import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Bitwise
import SP1Clean.Native.Operations.BitwiseOperation.RawSpec

/-! # `BitwiseOperation` — `populate` (the witness generator)

The witness assignment `populate` (the eight result bytes — the per-byte `byteOp opcode` of the operand
bytes, threaded in by a composing operation) and `spec_populate` (the witnessed result satisfies the
gadget `Spec`). The elaborated `eval` circuit is hand-maintained in the sibling `Defs.lean`; the
arithmetic core is in `RawSpec`; the `FormalAssertion` contract in `Formal`. -/

namespace SP1Clean.BitwiseOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native port of SP1's `BitwiseOperation` result column: each result byte is `byteOp opcode a b`. -/
def populate (a b : Vector (ZMod p) 8) (opcode : ZMod p) : Columns (ZMod p) :=
  ⟨#v[((byteOp opcode.val a[0].val b[0].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[1].val b[1].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[2].val b[2].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[3].val b[3].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[4].val b[4].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[5].val b[5].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[6].val b[6].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[7].val b[7].val : ℕ) : ZMod p)]⟩

/-- The witnessed result bytes `populate a b opcode` satisfy the gadget `Spec` for any `is_real`, given
the operand bytes are genuine bytes and the opcode is one of AND/OR/XOR. The composing
`BitwiseU16Operation` uses this to discharge its `assertion BitwiseOperation.circuit` prover obligation.

Heartbeat budget: measured 2026-07 by ladder (control run at 1 heartbeat gave a real `isDefEq`
timeout). Passes at 20000 and 10000, fails at 5000 (`simp`-nested `whnf` in the `fin_cases` block),
so the true floor is in (5000, 10000] and the plain default carries ≥20× headroom. The former
2000000 ceiling here was ~200-400× over and was removed. -/
theorem spec_populate {a b : Vector (ZMod p) 8} {opcode : ZMod p}
    (hbytes : ∀ i : Fin 8, a[(i : ℕ)].val < 256 ∧ b[(i : ℕ)].val < 256) (_hopcode : opcode.val < 3)
    (is_real : ZMod p) :
    Spec (⟨a, b, populate a b opcode, opcode, is_real⟩ : Inputs (ZMod p)) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hb256 : (256 : ℕ) < p := by omega
  intro _
  have hres : ∀ i : Fin 8,
      (populate a b opcode).result[(i : ℕ)].val
        = byteOp opcode.val a[(i : ℕ)].val b[(i : ℕ)].val := by
    intro i
    have hi := hbytes i
    fin_cases i <;>
      simp only [populate, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] <;>
      exact ZMod.val_natCast_of_lt (lt_trans (byteOp_lt256 _ _ _ hi.1 hi.2) hb256)
  exact ⟨hbytes, bitwise_of_byteOp (a := a) (b := b) hres⟩

end SP1Clean.BitwiseOperation
