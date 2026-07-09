import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Math.MulCarryChain
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Native.Operations.U16toU8OperationSafe
import SP1Clean.Extracted.MulOperation
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! # `MulOperation` — arithmetic core (`RawSpec` + `mulSemantics_of_raw`).

The byte/schoolbook helpers (`extendedBytes`/`byteAt`/`colSum`/`carryVal`, the `colSum_k`
expansions, reassembly lemmas), the literal `RawSpec`, and the soundness core
`mulSemantics_of_raw : RawSpec → SemanticSpec`. -/

namespace SP1Clean.MulOperation

open Circuit
open SP1Clean.Channels (byteChannel)

-- The multiply column arithmetic needs a wider field than the rest of the project: a product
-- column `colSum k` (≤ 16 byte×byte terms ≈ 2^20) plus the outgoing `carry k * 256` term reaches
-- ≈ 2^24 before the ZMod→ℕ lift is valid, so the gadget requires `Fact (2 ^ 24 < p)`. This
-- subsumes the project-wide `Fact (2 ^ 17 < p)`, which we re-derive as an instance below so the
-- shared `Word`/`Gadgets` lemmas keep firing.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


instance : Fact (p > 2) :=
  ⟨by have h := Fact.out (p := 2 ^ 24 < p); have : (2 : ℕ) < 2 ^ 24 := by norm_num
      omega⟩

instance : Fact (1 < p) :=
  ⟨by have h := Fact.out (p := 2 ^ 24 < p); have : (1 : ℕ) < 2 ^ 24 := by norm_num
      omega⟩

omit [Fact p.Prime] in
/-- `2 ^ 16 < p`, the side condition `Gadgets.ToBits.rangeCheck 16` needs. -/
lemma hn16 : 2 ^ 16 < p := by
  have h := Fact.out (p := 2 ^ 24 < p)
  have : (2 : ℕ) ^ 16 < 2 ^ 24 := by norm_num
  omega

omit [Fact p.Prime] in
/-- `2 ^ 8 < p`, the side condition `Gadgets.ToBits.rangeCheck 8` needs. -/
lemma hn8 : 2 ^ 8 < p := by
  have h := Fact.out (p := 2 ^ 24 < p)
  have : (2 : ℕ) ^ 8 < 2 ^ 24 := by norm_num
  omega

/-- **Low-half schoolbook reassembly** (the MUL keystone). Given the first eight columns of the
schoolbook product/carry chain over the eight operand bytes `b0..b7`, `c0..c7` (each column equation
`p_k + k_k·256 = ∑_{i+j=k} b_i·c_j + (incoming carry)`), the eight low product bytes reassemble — mod
`2^64` — to the full integer product. The high columns (`k ≥ 8`) and the outgoing carry `k₇` only
contribute multiples of `2^64`, so they vanish under the truncation; this is exactly the low 64 bits
that `MUL` returns. Proof: telescope the eight equations into the exact identity
`∑ p_k·256^k + k₇·2^64 = S` (the low convolution `S`, by `omega`), split the full product as
`S + 2^64·(high convolution)` (by `ring`), then read off the congruence (by `omega`). -/
lemma low_half
    (b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7
     p0 p1 p2 p3 p4 p5 p6 p7 k0 k1 k2 k3 k4 k5 k6 k7 : ℕ)
    (e0 : p0 + k0 * 256 = b0*c0)
    (e1 : p1 + k1 * 256 = b0*c1 + b1*c0 + k0)
    (e2 : p2 + k2 * 256 = b0*c2 + b1*c1 + b2*c0 + k1)
    (e3 : p3 + k3 * 256 = b0*c3 + b1*c2 + b2*c1 + b3*c0 + k2)
    (e4 : p4 + k4 * 256 = b0*c4 + b1*c3 + b2*c2 + b3*c1 + b4*c0 + k3)
    (e5 : p5 + k5 * 256 = b0*c5 + b1*c4 + b2*c3 + b3*c2 + b4*c1 + b5*c0 + k4)
    (e6 : p6 + k6 * 256 = b0*c6 + b1*c5 + b2*c4 + b3*c3 + b4*c2 + b5*c1 + b6*c0 + k5)
    (e7 : p7 + k7 * 256 = b0*c7 + b1*c6 + b2*c5 + b3*c4 + b4*c3 + b5*c2 + b6*c1 + b7*c0 + k6) :
    (p0 + p1*256 + p2*256^2 + p3*256^3 + p4*256^4 + p5*256^5 + p6*256^6 + p7*256^7) % 2^64
      = ((b0 + b1*256 + b2*256^2 + b3*256^3 + b4*256^4 + b5*256^5 + b6*256^6 + b7*256^7)
         * (c0 + c1*256 + c2*256^2 + c3*256^3 + c4*256^4 + c5*256^5 + c6*256^6 + c7*256^7)) % 2^64 := by
  set S : ℕ := b0*c0
    + (b0*c1 + b1*c0)*256
    + (b0*c2 + b1*c1 + b2*c0)*256^2
    + (b0*c3 + b1*c2 + b2*c1 + b3*c0)*256^3
    + (b0*c4 + b1*c3 + b2*c2 + b3*c1 + b4*c0)*256^4
    + (b0*c5 + b1*c4 + b2*c3 + b3*c2 + b4*c1 + b5*c0)*256^5
    + (b0*c6 + b1*c5 + b2*c4 + b3*c3 + b4*c2 + b5*c1 + b6*c0)*256^6
    + (b0*c7 + b1*c6 + b2*c5 + b3*c4 + b4*c3 + b5*c2 + b6*c1 + b7*c0)*256^7 with hS
  have hLOW :
      (p0 + p1*256 + p2*256^2 + p3*256^3 + p4*256^4 + p5*256^5 + p6*256^6 + p7*256^7)
        + k7 * 2^64 = S := by rw [hS]; omega
  have hHIGH :
      (b0 + b1*256 + b2*256^2 + b3*256^3 + b4*256^4 + b5*256^5 + b6*256^6 + b7*256^7)
        * (c0 + c1*256 + c2*256^2 + c3*256^3 + c4*256^4 + c5*256^5 + c6*256^6 + c7*256^7)
      = S + 2^64 * (
          (b1*c7 + b2*c6 + b3*c5 + b4*c4 + b5*c3 + b6*c2 + b7*c1)
        + (b2*c7 + b3*c6 + b4*c5 + b5*c4 + b6*c3 + b7*c2)*256
        + (b3*c7 + b4*c6 + b5*c5 + b6*c4 + b7*c3)*256^2
        + (b4*c7 + b5*c6 + b6*c5 + b7*c4)*256^3
        + (b5*c7 + b6*c6 + b7*c5)*256^4
        + (b6*c7 + b7*c6)*256^5
        + (b7*c7)*256^6) := by rw [hS]; ring
  omega

set_option maxHeartbeats 16000000 in
/-- **Full-product schoolbook reassembly** (the high-half keystone). The 16-column
mod-`2^128` analogue of `low_half`: given the sixteen schoolbook column equations over the
sixteen sign/zero-extended operand bytes, the sixteen product bytes reassemble — mod `2^128` —
to the full integer product of the 16-byte operands. The carry `k15` out of the top column
contributes only a multiple of `2^128`, and the operand cross terms with `i+j ≥ 16` are
multiples of `2^128`, so both vanish under the truncation. -/
lemma full_product
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
     p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 : ℕ)
    (e0 : p0 + k0 * 256 = b0*c0)
    (e1 : p1 + k1 * 256 = b0*c1 + b1*c0 + k0)
    (e2 : p2 + k2 * 256 = b0*c2 + b1*c1 + b2*c0 + k1)
    (e3 : p3 + k3 * 256 = b0*c3 + b1*c2 + b2*c1 + b3*c0 + k2)
    (e4 : p4 + k4 * 256 = b0*c4 + b1*c3 + b2*c2 + b3*c1 + b4*c0 + k3)
    (e5 : p5 + k5 * 256 = b0*c5 + b1*c4 + b2*c3 + b3*c2 + b4*c1 + b5*c0 + k4)
    (e6 : p6 + k6 * 256 = b0*c6 + b1*c5 + b2*c4 + b3*c3 + b4*c2 + b5*c1 + b6*c0 + k5)
    (e7 : p7 + k7 * 256 = b0*c7 + b1*c6 + b2*c5 + b3*c4 + b4*c3 + b5*c2 + b6*c1 + b7*c0 + k6)
    (e8 : p8 + k8 * 256 = b0*c8 + b1*c7 + b2*c6 + b3*c5 + b4*c4 + b5*c3 + b6*c2 + b7*c1 + b8*c0 + k7)
    (e9 : p9 + k9 * 256 = b0*c9 + b1*c8 + b2*c7 + b3*c6 + b4*c5 + b5*c4 + b6*c3 + b7*c2 + b8*c1 + b9*c0 + k8)
    (e10 : p10 + k10 * 256 = b0*c10 + b1*c9 + b2*c8 + b3*c7 + b4*c6 + b5*c5 + b6*c4 + b7*c3 + b8*c2 + b9*c1 + b10*c0 + k9)
    (e11 : p11 + k11 * 256 = b0*c11 + b1*c10 + b2*c9 + b3*c8 + b4*c7 + b5*c6 + b6*c5 + b7*c4 + b8*c3 + b9*c2 + b10*c1 + b11*c0 + k10)
    (e12 : p12 + k12 * 256 = b0*c12 + b1*c11 + b2*c10 + b3*c9 + b4*c8 + b5*c7 + b6*c6 + b7*c5 + b8*c4 + b9*c3 + b10*c2 + b11*c1 + b12*c0 + k11)
    (e13 : p13 + k13 * 256 = b0*c13 + b1*c12 + b2*c11 + b3*c10 + b4*c9 + b5*c8 + b6*c7 + b7*c6 + b8*c5 + b9*c4 + b10*c3 + b11*c2 + b12*c1 + b13*c0 + k12)
    (e14 : p14 + k14 * 256 = b0*c14 + b1*c13 + b2*c12 + b3*c11 + b4*c10 + b5*c9 + b6*c8 + b7*c7 + b8*c6 + b9*c5 + b10*c4 + b11*c3 + b12*c2 + b13*c1 + b14*c0 + k13)
    (e15 : p15 + k15 * 256 = b0*c15 + b1*c14 + b2*c13 + b3*c12 + b4*c11 + b5*c10 + b6*c9 + b7*c8 + b8*c7 + b9*c6 + b10*c5 + b11*c4 + b12*c3 + b13*c2 + b14*c1 + b15*c0 + k14) :
    (p0 + p1*256^1 + p2*256^2 + p3*256^3 + p4*256^4 + p5*256^5 + p6*256^6 + p7*256^7 + p8*256^8 + p9*256^9 + p10*256^10 + p11*256^11 + p12*256^12 + p13*256^13 + p14*256^14 + p15*256^15) % 2^128
      = ((b0 + b1*256^1 + b2*256^2 + b3*256^3 + b4*256^4 + b5*256^5 + b6*256^6 + b7*256^7 + b8*256^8 + b9*256^9 + b10*256^10 + b11*256^11 + b12*256^12 + b13*256^13 + b14*256^14 + b15*256^15)
         * (c0 + c1*256^1 + c2*256^2 + c3*256^3 + c4*256^4 + c5*256^5 + c6*256^6 + c7*256^7 + c8*256^8 + c9*256^9 + c10*256^10 + c11*256^11 + c12*256^12 + c13*256^13 + c14*256^14 + c15*256^15)) % 2^128 := by
  set S : ℕ := (b0*c0)
    + (b0*c1 + b1*c0)*256^1
    + (b0*c2 + b1*c1 + b2*c0)*256^2
    + (b0*c3 + b1*c2 + b2*c1 + b3*c0)*256^3
    + (b0*c4 + b1*c3 + b2*c2 + b3*c1 + b4*c0)*256^4
    + (b0*c5 + b1*c4 + b2*c3 + b3*c2 + b4*c1 + b5*c0)*256^5
    + (b0*c6 + b1*c5 + b2*c4 + b3*c3 + b4*c2 + b5*c1 + b6*c0)*256^6
    + (b0*c7 + b1*c6 + b2*c5 + b3*c4 + b4*c3 + b5*c2 + b6*c1 + b7*c0)*256^7
    + (b0*c8 + b1*c7 + b2*c6 + b3*c5 + b4*c4 + b5*c3 + b6*c2 + b7*c1 + b8*c0)*256^8
    + (b0*c9 + b1*c8 + b2*c7 + b3*c6 + b4*c5 + b5*c4 + b6*c3 + b7*c2 + b8*c1 + b9*c0)*256^9
    + (b0*c10 + b1*c9 + b2*c8 + b3*c7 + b4*c6 + b5*c5 + b6*c4 + b7*c3 + b8*c2 + b9*c1 + b10*c0)*256^10
    + (b0*c11 + b1*c10 + b2*c9 + b3*c8 + b4*c7 + b5*c6 + b6*c5 + b7*c4 + b8*c3 + b9*c2 + b10*c1 + b11*c0)*256^11
    + (b0*c12 + b1*c11 + b2*c10 + b3*c9 + b4*c8 + b5*c7 + b6*c6 + b7*c5 + b8*c4 + b9*c3 + b10*c2 + b11*c1 + b12*c0)*256^12
    + (b0*c13 + b1*c12 + b2*c11 + b3*c10 + b4*c9 + b5*c8 + b6*c7 + b7*c6 + b8*c5 + b9*c4 + b10*c3 + b11*c2 + b12*c1 + b13*c0)*256^13
    + (b0*c14 + b1*c13 + b2*c12 + b3*c11 + b4*c10 + b5*c9 + b6*c8 + b7*c7 + b8*c6 + b9*c5 + b10*c4 + b11*c3 + b12*c2 + b13*c1 + b14*c0)*256^14
    + (b0*c15 + b1*c14 + b2*c13 + b3*c12 + b4*c11 + b5*c10 + b6*c9 + b7*c8 + b8*c7 + b9*c6 + b10*c5 + b11*c4 + b12*c3 + b13*c2 + b14*c1 + b15*c0)*256^15
    with hS
  have hLOW :
      (p0 + p1*256^1 + p2*256^2 + p3*256^3 + p4*256^4 + p5*256^5 + p6*256^6 + p7*256^7 + p8*256^8 + p9*256^9 + p10*256^10 + p11*256^11 + p12*256^12 + p13*256^13 + p14*256^14 + p15*256^15)
        + k15 * 2^128 = S := by rw [hS]; omega
  have hHIGH :
      (b0 + b1*256^1 + b2*256^2 + b3*256^3 + b4*256^4 + b5*256^5 + b6*256^6 + b7*256^7 + b8*256^8 + b9*256^9 + b10*256^10 + b11*256^11 + b12*256^12 + b13*256^13 + b14*256^14 + b15*256^15)
        * (c0 + c1*256^1 + c2*256^2 + c3*256^3 + c4*256^4 + c5*256^5 + c6*256^6 + c7*256^7 + c8*256^8 + c9*256^9 + c10*256^10 + c11*256^11 + c12*256^12 + c13*256^13 + c14*256^14 + c15*256^15)
      = S + 2^128 * (
          (b1*c15 + b2*c14 + b3*c13 + b4*c12 + b5*c11 + b6*c10 + b7*c9 + b8*c8 + b9*c7 + b10*c6 + b11*c5 + b12*c4 + b13*c3 + b14*c2 + b15*c1)
        + (b2*c15 + b3*c14 + b4*c13 + b5*c12 + b6*c11 + b7*c10 + b8*c9 + b9*c8 + b10*c7 + b11*c6 + b12*c5 + b13*c4 + b14*c3 + b15*c2)*256^1
        + (b3*c15 + b4*c14 + b5*c13 + b6*c12 + b7*c11 + b8*c10 + b9*c9 + b10*c8 + b11*c7 + b12*c6 + b13*c5 + b14*c4 + b15*c3)*256^2
        + (b4*c15 + b5*c14 + b6*c13 + b7*c12 + b8*c11 + b9*c10 + b10*c9 + b11*c8 + b12*c7 + b13*c6 + b14*c5 + b15*c4)*256^3
        + (b5*c15 + b6*c14 + b7*c13 + b8*c12 + b9*c11 + b10*c10 + b11*c9 + b12*c8 + b13*c7 + b14*c6 + b15*c5)*256^4
        + (b6*c15 + b7*c14 + b8*c13 + b9*c12 + b10*c11 + b11*c10 + b12*c9 + b13*c8 + b14*c7 + b15*c6)*256^5
        + (b7*c15 + b8*c14 + b9*c13 + b10*c12 + b11*c11 + b12*c10 + b13*c9 + b14*c8 + b15*c7)*256^6
        + (b8*c15 + b9*c14 + b10*c13 + b11*c12 + b12*c11 + b13*c10 + b14*c9 + b15*c8)*256^7
        + (b9*c15 + b10*c14 + b11*c13 + b12*c12 + b13*c11 + b14*c10 + b15*c9)*256^8
        + (b10*c15 + b11*c14 + b12*c13 + b13*c12 + b14*c11 + b15*c10)*256^9
        + (b11*c15 + b12*c14 + b13*c13 + b14*c12 + b15*c11)*256^10
        + (b12*c15 + b13*c14 + b14*c13 + b15*c12)*256^11
        + (b13*c15 + b14*c14 + b15*c13)*256^12
        + (b14*c15 + b15*c14)*256^13
        + (b15*c15)*256^14) := by rw [hS]; ring
  omega

/-! ## Byte helpers for the schoolbook product

The schoolbook multiply is over the **16-byte** sign/zero-extended operands: bytes `0..7` are the
operand's own bytes (low byte `low_bytes[i]`, high byte `(w[i] - low_bytes[i]) * 256⁻¹`), and bytes
`8..15` are the sign fill `sign_extend * 255` (`0` for unsigned operands, `0xFF` for negative signed
operands). -/

/-- The 16 little-endian sign/zero-extended bytes of operand word `w`. -/
def extendedBytes (w : Word (ZMod p)) (lower : Extracted.U16toU8Operation (ZMod p))
    (sign_extend : ZMod p) : Fin 16 → ZMod p :=
  ![ lower.low_bytes[0], (w[0] - lower.low_bytes[0]) * 256⁻¹,
     lower.low_bytes[1], (w[1] - lower.low_bytes[1]) * 256⁻¹,
     lower.low_bytes[2], (w[2] - lower.low_bytes[2]) * 256⁻¹,
     lower.low_bytes[3], (w[3] - lower.low_bytes[3]) * 256⁻¹,
     sign_extend * 255, sign_extend * 255, sign_extend * 255, sign_extend * 255,
     sign_extend * 255, sign_extend * 255, sign_extend * 255, sign_extend * 255 ]

/-- Read a byte function at a `ℕ` index, `0` outside `0..15`. -/
def byteAt (f : Fin 16 → ZMod p) (k : ℕ) : ZMod p :=
  if h : k < 16 then f ⟨k, h⟩ else 0

/-- The `k`-th schoolbook product column `∑_{i+j=k} b[i]·c[j]` over the 16-byte operands. -/
def colSum (bb cc : Fin 16 → ZMod p) (k : ℕ) : ZMod p :=
  Finset.sum (Finset.range 16) (fun i => if i ≤ k then byteAt bb i * byteAt cc (k - i) else 0)

/-- Witnessed column carry `k`, `0` outside `0..15`. -/
def carryVal (cols : Extracted.MulOperation (ZMod p)) (k : ℕ) : ZMod p :=
  if h : k < 16 then cols.carry[k]'h else 0

/-! ### Schoolbook column expansions, proven once on tiny abstract goals.

Each `colSum_k` unfolds the 16-term `Finset.range 16` convolution to its `byteAt` form
`∑_{i=0}^k byteAt bb i * byteAt cc (k-i)`. Hoisting this off the multi-million-character chain
goals in `soundness`/`completeness` — where it is applied by `rw [colSum_k]` ahead of the cheap
`byteAt`/`extendedBytes` reduction — keeps the heavy `Finset` expansion out of those proofs. -/

section ColSumExpand

lemma colSum_0 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 0 = byteAt bb 0 * byteAt cc 0 := by
  simp [colSum]

lemma colSum_1 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 1 = byteAt bb 0 * byteAt cc 1 + byteAt bb 1 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_2 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 2 = byteAt bb 0 * byteAt cc 2 + byteAt bb 1 * byteAt cc 1
      + byteAt bb 2 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_3 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 3 = byteAt bb 0 * byteAt cc 3 + byteAt bb 1 * byteAt cc 2
      + byteAt bb 2 * byteAt cc 1 + byteAt bb 3 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_4 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 4 = byteAt bb 0 * byteAt cc 4 + byteAt bb 1 * byteAt cc 3
      + byteAt bb 2 * byteAt cc 2 + byteAt bb 3 * byteAt cc 1 + byteAt bb 4 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_5 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 5 = byteAt bb 0 * byteAt cc 5 + byteAt bb 1 * byteAt cc 4
      + byteAt bb 2 * byteAt cc 3 + byteAt bb 3 * byteAt cc 2 + byteAt bb 4 * byteAt cc 1
      + byteAt bb 5 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_6 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 6 = byteAt bb 0 * byteAt cc 6 + byteAt bb 1 * byteAt cc 5
      + byteAt bb 2 * byteAt cc 4 + byteAt bb 3 * byteAt cc 3 + byteAt bb 4 * byteAt cc 2
      + byteAt bb 5 * byteAt cc 1 + byteAt bb 6 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_7 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 7 = byteAt bb 0 * byteAt cc 7 + byteAt bb 1 * byteAt cc 6
      + byteAt bb 2 * byteAt cc 5 + byteAt bb 3 * byteAt cc 4 + byteAt bb 4 * byteAt cc 3
      + byteAt bb 5 * byteAt cc 2 + byteAt bb 6 * byteAt cc 1 + byteAt bb 7 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_8 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 8 = byteAt bb 0 * byteAt cc 8 + byteAt bb 1 * byteAt cc 7
      + byteAt bb 2 * byteAt cc 6 + byteAt bb 3 * byteAt cc 5 + byteAt bb 4 * byteAt cc 4
      + byteAt bb 5 * byteAt cc 3 + byteAt bb 6 * byteAt cc 2 + byteAt bb 7 * byteAt cc 1
      + byteAt bb 8 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_9 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 9 = byteAt bb 0 * byteAt cc 9 + byteAt bb 1 * byteAt cc 8
      + byteAt bb 2 * byteAt cc 7 + byteAt bb 3 * byteAt cc 6 + byteAt bb 4 * byteAt cc 5
      + byteAt bb 5 * byteAt cc 4 + byteAt bb 6 * byteAt cc 3 + byteAt bb 7 * byteAt cc 2
      + byteAt bb 8 * byteAt cc 1 + byteAt bb 9 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_10 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 10 = byteAt bb 0 * byteAt cc 10 + byteAt bb 1 * byteAt cc 9
      + byteAt bb 2 * byteAt cc 8 + byteAt bb 3 * byteAt cc 7 + byteAt bb 4 * byteAt cc 6
      + byteAt bb 5 * byteAt cc 5 + byteAt bb 6 * byteAt cc 4 + byteAt bb 7 * byteAt cc 3
      + byteAt bb 8 * byteAt cc 2 + byteAt bb 9 * byteAt cc 1 + byteAt bb 10 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_11 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 11 = byteAt bb 0 * byteAt cc 11 + byteAt bb 1 * byteAt cc 10
      + byteAt bb 2 * byteAt cc 9 + byteAt bb 3 * byteAt cc 8 + byteAt bb 4 * byteAt cc 7
      + byteAt bb 5 * byteAt cc 6 + byteAt bb 6 * byteAt cc 5 + byteAt bb 7 * byteAt cc 4
      + byteAt bb 8 * byteAt cc 3 + byteAt bb 9 * byteAt cc 2 + byteAt bb 10 * byteAt cc 1
      + byteAt bb 11 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_12 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 12 = byteAt bb 0 * byteAt cc 12 + byteAt bb 1 * byteAt cc 11
      + byteAt bb 2 * byteAt cc 10 + byteAt bb 3 * byteAt cc 9 + byteAt bb 4 * byteAt cc 8
      + byteAt bb 5 * byteAt cc 7 + byteAt bb 6 * byteAt cc 6 + byteAt bb 7 * byteAt cc 5
      + byteAt bb 8 * byteAt cc 4 + byteAt bb 9 * byteAt cc 3 + byteAt bb 10 * byteAt cc 2
      + byteAt bb 11 * byteAt cc 1 + byteAt bb 12 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_13 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 13 = byteAt bb 0 * byteAt cc 13 + byteAt bb 1 * byteAt cc 12
      + byteAt bb 2 * byteAt cc 11 + byteAt bb 3 * byteAt cc 10 + byteAt bb 4 * byteAt cc 9
      + byteAt bb 5 * byteAt cc 8 + byteAt bb 6 * byteAt cc 7 + byteAt bb 7 * byteAt cc 6
      + byteAt bb 8 * byteAt cc 5 + byteAt bb 9 * byteAt cc 4 + byteAt bb 10 * byteAt cc 3
      + byteAt bb 11 * byteAt cc 2 + byteAt bb 12 * byteAt cc 1 + byteAt bb 13 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_14 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 14 = byteAt bb 0 * byteAt cc 14 + byteAt bb 1 * byteAt cc 13
      + byteAt bb 2 * byteAt cc 12 + byteAt bb 3 * byteAt cc 11 + byteAt bb 4 * byteAt cc 10
      + byteAt bb 5 * byteAt cc 9 + byteAt bb 6 * byteAt cc 8 + byteAt bb 7 * byteAt cc 7
      + byteAt bb 8 * byteAt cc 6 + byteAt bb 9 * byteAt cc 5 + byteAt bb 10 * byteAt cc 4
      + byteAt bb 11 * byteAt cc 3 + byteAt bb 12 * byteAt cc 2 + byteAt bb 13 * byteAt cc 1
      + byteAt bb 14 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]

lemma colSum_15 (bb cc : Fin 16 → ZMod p) :
    colSum bb cc 15 = byteAt bb 0 * byteAt cc 15 + byteAt bb 1 * byteAt cc 14
      + byteAt bb 2 * byteAt cc 13 + byteAt bb 3 * byteAt cc 12 + byteAt bb 4 * byteAt cc 11
      + byteAt bb 5 * byteAt cc 10 + byteAt bb 6 * byteAt cc 9 + byteAt bb 7 * byteAt cc 8
      + byteAt bb 8 * byteAt cc 7 + byteAt bb 9 * byteAt cc 6 + byteAt bb 10 * byteAt cc 5
      + byteAt bb 11 * byteAt cc 4 + byteAt bb 12 * byteAt cc 3 + byteAt bb 13 * byteAt cc 2
      + byteAt bb 14 * byteAt cc 1 + byteAt bb 15 * byteAt cc 0 := by
  simp [colSum, Finset.sum_range_succ]
end ColSumExpand


/-- Per-column `ℕ` lift (the `limb_lift` analogue for the multiply schoolbook). The `ZMod`-level
column equation `prodk + cc · 256 = col + prev` — with `prodk` a byte, `cc` a 16-bit carry, `col`
a `< 2^21` column sum and `prev` a 16-bit incoming carry — lifts to the `ℕ` equation. Every term
stays `< 2^24 < p`: the largest, `prodk + cc·256`, is `≤ 255 + (2^16-1)·256 = 2^24 - 1`. -/
lemma col_lift (prodk cc col prev : ZMod p)
    (hprod : prodk.val < 256) (hcc : cc.val < 2 ^ 16)
    (hcol : col.val < 2 ^ 21) (hprev : prev.val < 2 ^ 16)
    (h : prodk + cc * 256 = col + prev) :
    prodk.val + cc.val * 256 = col.val + prev.val := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp : 2 ^ 24 < p := Fact.out
  apply_fun ZMod.val at h
  have hcc256 : (cc * 256 : ZMod p).val = cc.val * 256 := by
    rw [ZMod.val_mul, val_256_zmod_p, Nat.mod_eq_of_lt (by omega)]
  have hL : (prodk + cc * 256 : ZMod p).val = prodk.val + cc.val * 256 := by
    rw [ZMod.val_add_of_lt (by rw [hcc256]; omega), hcc256]
  have hR : (col + prev : ZMod p).val = col.val + prev.val :=
    ZMod.val_add_of_lt (by omega)
  rw [hL, hR] at h
  exact h

omit [Fact (2 ^ 24 < p)] in
/-- A `byteAt` read of a function whose `Fin 16` values are bytes is itself a byte. -/
lemma byteAt_val_lt (f : Fin 16 → ZMod p) (hf : ∀ i : Fin 16, (f i).val < 256) (i : ℕ) :
    (byteAt f i).val < 256 := by
  unfold byteAt
  split
  · exact hf _
  · simp [ZMod.val_zero]

/-- Push `.val` through a schoolbook column over byte-valued operands: the field column sum's value
is the `ℕ` convolution of the byte values. Every column stays `< 16 · 65535 < 2^24 < p`, so no
wraparound. -/
lemma colSum_val (bb cc : Fin 16 → ZMod p)
    (hbb : ∀ i : Fin 16, (bb i).val < 256) (hcc : ∀ i : Fin 16, (cc i).val < 256) (k : ℕ) :
    (colSum bb cc k).val
      = ∑ i ∈ Finset.range 16, if i ≤ k then (byteAt bb i).val * (byteAt cc (k - i)).val else 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp : 2 ^ 24 < p := Fact.out
  have hbA : ∀ i, (byteAt bb i).val < 256 := byteAt_val_lt bb hbb
  have hcA : ∀ i, (byteAt cc i).val < 256 := byteAt_val_lt cc hcc
  set N : ℕ := ∑ i ∈ Finset.range 16,
      if i ≤ k then (byteAt bb i).val * (byteAt cc (k - i)).val else 0 with hN
  have hcast : colSum bb cc k = (N : ZMod p) := by
    unfold colSum
    rw [hN, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i ≤ k
    · simp only [if_pos h, Nat.cast_mul, ZMod.natCast_zmod_val]
    · simp only [if_neg h, Nat.cast_zero]
  have hNlt : N < p := by
    have hbound : N ≤ 16 * 65535 := by
      rw [hN]
      calc ∑ i ∈ Finset.range 16,
              (if i ≤ k then (byteAt bb i).val * (byteAt cc (k - i)).val else 0)
          ≤ ∑ _i ∈ Finset.range 16, 65535 := by
            apply Finset.sum_le_sum
            intro i _
            split
            · have h1 := hbA i; have h2 := hcA (k - i)
              calc (byteAt bb i).val * (byteAt cc (k - i)).val ≤ 255 * 255 :=
                    Nat.mul_le_mul (by omega) (by omega)
                _ ≤ 65535 := by omega
            · omega
        _ = 16 * 65535 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hNlt]

/-- A `{0,1}` field element has `.val ∈ {0,1}`. -/
lemma bool_val {x : ZMod p} (h : x = 0 ∨ x = 1) : x.val = 0 ∨ x.val = 1 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  rcases h with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]

/-- With exactly one of five booleans set and the first set, the other four are `0`. -/
lemma rest_zero {a b c d e : ZMod p}
    (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1)
    (ha1 : a = 1) (hsum : a + b + c + d + e = 1) : b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp := Fact.out (p := 2 ^ 24 < p)
  have hbv := bool_val hb; have hcv := bool_val hc; have hdv := bool_val hd; have hev := bool_val he
  have hsum0 : b + c + d + e = 0 := by rw [ha1] at hsum; linear_combination hsum
  have hcast : b + c + d + e = ((b.val + c.val + d.val + e.val : ℕ) : ZMod p) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [hcast] at hsum0
  have hlt : b.val + c.val + d.val + e.val < p := by omega
  have hz : b.val + c.val + d.val + e.val = 0 := by
    have := congrArg ZMod.val hsum0
    rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at this
  exact ⟨(ZMod.val_eq_zero b).mp (by omega), (ZMod.val_eq_zero c).mp (by omega),
         (ZMod.val_eq_zero d).mp (by omega), (ZMod.val_eq_zero e).mp (by omega)⟩

/-- With five booleans whose sum is `{0,1}`-bounded and at least one set, the sum is exactly `1`. (The
chip's `is_real = 1` row commits one active variant flag; this turns the sum-bound gate into `sum = 1`,
the hypothesis `aSelector_eq_resultWord`/`rest_zero` need.) -/
lemma sum_eq_one {a b c d e : ZMod p}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1)
    (hsum01 : a + b + c + d + e = 0 ∨ a + b + c + d + e = 1)
    (hone : a = 1 ∨ b = 1 ∨ c = 1 ∨ d = 1 ∨ e = 1) :
    a + b + c + d + e = 1 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp := Fact.out (p := 2 ^ 24 < p)
  rcases hsum01 with h0 | h1
  · exfalso
    have hcast : a + b + c + d + e = ((a.val + b.val + c.val + d.val + e.val : ℕ) : ZMod p) := by
      push_cast [ZMod.natCast_zmod_val]; ring
    rw [hcast] at h0
    have hlt : a.val + b.val + c.val + d.val + e.val < p := by
      have va : a.val ≤ 1 := by rcases ha with h | h <;> simp [h, ZMod.val_one]
      have vb : b.val ≤ 1 := by rcases hb with h | h <;> simp [h, ZMod.val_one]
      have vc : c.val ≤ 1 := by rcases hc with h | h <;> simp [h, ZMod.val_one]
      have vd : d.val ≤ 1 := by rcases hd with h | h <;> simp [h, ZMod.val_one]
      have ve : e.val ≤ 1 := by rcases he with h | h <;> simp [h, ZMod.val_one]
      omega
    have hz : a.val + b.val + c.val + d.val + e.val = 0 := by
      have := congrArg ZMod.val h0
      rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at this
    rcases hone with h | h | h | h | h <;> (rw [h] at hz; simp [ZMod.val_one] at hz)
  · exact h1

/-- Flag-weighted reconstruction of the 64-bit result word from the witnessed `product` columns. The
chip witnesses its register-write word `a` and ties it to this selector; given the five variant flags
are boolean with exactly one set, it collapses to `resultWord` (see `aSelector_eq_resultWord`). `MUL`
takes product bytes `0..7` (low 64), the `MULH*` family bytes `8..15` (high 64), and `MULW` the low 32
(bytes `0..3`) with the product sign bit `msb * 65535` filling the upper two limbs. -/
def aSelector (cols : Extracted.MulOperation (ZMod p))
    (is_mul is_mulh is_mulhu is_mulhsu is_mulw : ZMod p) : Word (ZMod p) :=
  let msb := cols.product_msb.msb
  #v[ is_mul * (productVal cols 0 + productVal cols 1 * 256)
        + (is_mulh + is_mulhu + is_mulhsu) * (productVal cols 8 + productVal cols 9 * 256)
        + is_mulw * (productVal cols 0 + productVal cols 1 * 256),
      is_mul * (productVal cols 2 + productVal cols 3 * 256)
        + (is_mulh + is_mulhu + is_mulhsu) * (productVal cols 10 + productVal cols 11 * 256)
        + is_mulw * (productVal cols 2 + productVal cols 3 * 256),
      is_mul * (productVal cols 4 + productVal cols 5 * 256)
        + (is_mulh + is_mulhu + is_mulhsu) * (productVal cols 12 + productVal cols 13 * 256)
        + is_mulw * (msb * 65535),
      is_mul * (productVal cols 6 + productVal cols 7 * 256)
        + (is_mulh + is_mulhu + is_mulhsu) * (productVal cols 14 + productVal cols 15 * 256)
        + is_mulw * (msb * 65535) ]

set_option linter.unusedSimpArgs false in
/-- With the five variant flags boolean and exactly one set, the flag-weighted `aSelector` collapses to
the variant's `resultWord` slice. (`resultWord` ignores `input.b`/`input.c`, so only the flags matter.) -/
lemma aSelector_eq_resultWord (input : Inputs (ZMod p)) (cols : Extracted.MulOperation (ZMod p))
    (hmul : input.is_mul = 0 ∨ input.is_mul = 1) (hmh : input.is_mulh = 0 ∨ input.is_mulh = 1)
    (hmhu : input.is_mulhu = 0 ∨ input.is_mulhu = 1) (hmhsu : input.is_mulhsu = 0 ∨ input.is_mulhsu = 1)
    (hmw : input.is_mulw = 0 ∨ input.is_mulw = 1)
    (hsum : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1) :
    aSelector cols input.is_mul input.is_mulh input.is_mulhu input.is_mulhsu input.is_mulw
      = resultWord input cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  unfold aSelector resultWord
  rcases hmul with h | h
  · rcases hmh with hh | hh
    · rcases hmhu with hu | hu
      · rcases hmhsu with hs | hs
        · -- is_mulw = 1 (the other four are 0)
          have hw : input.is_mulw = 1 := by linear_combination hsum - h - hh - hu - hs
          rw [h, hh, hu, hs, hw]
          simp only [if_pos, if_neg h01, one_mul, zero_mul, add_zero, zero_add, true_or, or_true,
            or_self, if_true]
        · -- is_mulhsu = 1
          have hw : input.is_mulw = 0 := by linear_combination hsum - h - hh - hu - hs
          rw [h, hh, hu, hs, hw]
          simp only [if_pos, if_neg h01, one_mul, zero_mul, add_zero, zero_add, true_or, or_true,
            or_self, if_true]
      · -- is_mulhu = 1
        obtain ⟨_, _, emhsu, emw⟩ := rest_zero (Or.inl h) (Or.inl hh) hmhsu hmw hu (by linear_combination hsum)
        rw [h, hh, hu, emhsu, emw]
        simp only [if_pos, if_neg h01, one_mul, zero_mul, add_zero, zero_add, true_or, or_true,
          or_self, if_true]
    · -- is_mulh = 1
      obtain ⟨_, emhu, emhsu, emw⟩ := rest_zero (Or.inl h) hmhu hmhsu hmw hh (by linear_combination hsum)
      rw [h, hh, emhu, emhsu, emw]
      simp only [if_pos, if_neg h01, one_mul, zero_mul, add_zero, zero_add, true_or, or_true,
        or_self, if_true]
  · -- is_mul = 1
    obtain ⟨emh, emhu, emhsu, emw⟩ := rest_zero hmh hmhu hmhsu hmw h hsum
    rw [h, emh, emhu, emhsu, emw]
    simp only [if_pos, if_neg h01, one_mul, zero_mul, add_zero, zero_add, true_or, or_true,
      or_self, if_true]

/-- Compose a 16-bit limb from its two bytes at the `ℕ`-value level. -/
lemma byte_compose_val {x lo hi : ZMod p} (hlo : lo.val < 256) (hhi : hi.val < 256)
    (h : x = lo + hi * 256) : x.val = lo.val + hi.val * 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp := Fact.out (p := 2 ^ 24 < p)
  subst h
  have hhi256 : (hi * 256 : ZMod p).val = hi.val * 256 := by
    rw [ZMod.val_mul, val_256_zmod_p, Nat.mod_eq_of_lt (by omega)]
  rw [ZMod.val_add_of_lt (by rw [hhi256]; omega), hhi256]

/-- The operand word reassembles from its eight little-endian bytes (the low byte / high byte of each
of its four limbs, as exposed by the `U16toU8OperationSafe` sub-op): its `toNat` is the byte sum that
the schoolbook product consumes. -/
lemma lower_toNat (w : Word (ZMod p)) (lower : Extracted.U16toU8Operation (ZMod p)) (s : ZMod p)
    (hspec : U16toU8OperationSafe.DecompSpec w lower) :
    w.toNat
      = (byteAt (extendedBytes w lower s) 0).val + (byteAt (extendedBytes w lower s) 1).val * 256
      + (byteAt (extendedBytes w lower s) 2).val * 256 ^ 2 + (byteAt (extendedBytes w lower s) 3).val * 256 ^ 3
      + (byteAt (extendedBytes w lower s) 4).val * 256 ^ 4 + (byteAt (extendedBytes w lower s) 5).val * 256 ^ 5
      + (byteAt (extendedBytes w lower s) 6).val * 256 ^ 6 + (byteAt (extendedBytes w lower s) 7).val * 256 ^ 7 := by
  have hw : ∀ j : Fin 4,
      w[j].val = (lower.low_bytes[j]).val + ((w[j] - lower.low_bytes[j]) * 256⁻¹).val * 256 := by
    intro j
    obtain ⟨hlo, hhi, hre⟩ := hspec j
    exact byte_compose_val hlo hhi hre
  -- Re-type the per-limb facts with `Nat` getElem so `rw` matches `Word.toNat_def` syntactically.
  have h0 : w[0].val = (lower.low_bytes[0]).val + ((w[0] - lower.low_bytes[0]) * 256⁻¹).val * 256 := hw 0
  have h1 : w[1].val = (lower.low_bytes[1]).val + ((w[1] - lower.low_bytes[1]) * 256⁻¹).val * 256 := hw 1
  have h2 : w[2].val = (lower.low_bytes[2]).val + ((w[2] - lower.low_bytes[2]) * 256⁻¹).val * 256 := hw 2
  have h3 : w[3].val = (lower.low_bytes[3]).val + ((w[3] - lower.low_bytes[3]) * 256⁻¹).val * 256 := hw 3
  have e0 : byteAt (extendedBytes w lower s) 0 = lower.low_bytes[0] := rfl
  have e1 : byteAt (extendedBytes w lower s) 1 = (w[0] - lower.low_bytes[0]) * 256⁻¹ := rfl
  have e2 : byteAt (extendedBytes w lower s) 2 = lower.low_bytes[1] := rfl
  have e3 : byteAt (extendedBytes w lower s) 3 = (w[1] - lower.low_bytes[1]) * 256⁻¹ := rfl
  have e4 : byteAt (extendedBytes w lower s) 4 = lower.low_bytes[2] := rfl
  have e5 : byteAt (extendedBytes w lower s) 5 = (w[2] - lower.low_bytes[2]) * 256⁻¹ := rfl
  have e6 : byteAt (extendedBytes w lower s) 6 = lower.low_bytes[3] := rfl
  have e7 : byteAt (extendedBytes w lower s) 7 = (w[3] - lower.low_bytes[3]) * 256⁻¹ := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7, Word.toNat_def, h0, h1, h2, h3]
  ring

/-- Every one of the sixteen sign/zero-extended operand bytes is a genuine byte: bytes `0..7` from the
`U16toU8` decomposition, bytes `8..15` from the `{0,1}` sign-extend selector. -/
lemma extendedBytes_byte_lt (w : Word (ZMod p)) (lower : Extracted.U16toU8Operation (ZMod p))
    (s : ZMod p)
    (hlow : ∀ i : Fin 4, (lower.low_bytes[i]).val < 256)
    (hhigh : ∀ i : Fin 4, ((w[i] - lower.low_bytes[i]) * 256⁻¹).val < 256)
    (hs : s = 0 ∨ s = 1) :
    ∀ i : Fin 16, (extendedBytes w lower s i).val < 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hsv : (s * 255).val < 256 := by
    rcases hs with h | h
    · rw [h, zero_mul, ZMod.val_zero]; norm_num
    · rw [h, one_mul, show (255 : ZMod p) = ((255 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 24 < p); omega)]
      norm_num
  intro i
  fin_cases i <;>
    first
      | exact hlow 0 | exact hlow 1 | exact hlow 2 | exact hlow 3
      | exact hhigh 0 | exact hhigh 1 | exact hhigh 2 | exact hhigh 3
      | exact hsv

/-- A schoolbook column value is `< 2^21` (it is at most `16 · 65535`). -/
lemma colSum_lt (bb cc : Fin 16 → ZMod p)
    (hbb : ∀ i : Fin 16, (bb i).val < 256) (hcc : ∀ i : Fin 16, (cc i).val < 256) (k : ℕ) :
    (colSum bb cc k).val < 2 ^ 21 := by
  rw [colSum_val bb cc hbb hcc k]
  have hbnd : ∀ i ∈ Finset.range 16,
      (if i ≤ k then (byteAt bb i).val * (byteAt cc (k - i)).val else 0) ≤ 65535 := by
    intro i _
    split
    · have h1 := byteAt_val_lt bb hbb i; have h2 := byteAt_val_lt cc hcc (k - i)
      calc (byteAt bb i).val * (byteAt cc (k - i)).val ≤ 255 * 255 :=
            Nat.mul_le_mul (by omega) (by omega)
        _ ≤ 65535 := by omega
    · omega
  calc ∑ i ∈ Finset.range 16, (if i ≤ k then (byteAt bb i).val * (byteAt cc (k - i)).val else 0)
      ≤ ∑ _i ∈ Finset.range 16, 65535 := Finset.sum_le_sum hbnd
    _ = 16 * 65535 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ < 2 ^ 21 := by norm_num

/-- The uniform per-column `ℕ` equation: the raw schoolbook chain at column `k`, lifted to `ℕ`. -/
lemma colEq (cols : Extracted.MulOperation (ZMod p)) (bb cc : Fin 16 → ZMod p)
    (hbb : ∀ i : Fin 16, (bb i).val < 256) (hcc : ∀ i : Fin 16, (cc i).val < 256)
    (h_chain : ∀ k : ℕ, k < 16 →
      productVal cols k = colSum bb cc k
        + (if k = 0 then 0 else carryVal cols (k - 1)) - carryVal cols k * 256)
    (h_pbyte : ∀ k : ℕ, k < 16 → (productVal cols k).val < 256)
    (h_carry : ∀ k : ℕ, k < 16 → (carryVal cols k).val < 2 ^ 16)
    (k : ℕ) (hk : k < 16) :
    (productVal cols k).val + (carryVal cols k).val * 256
      = (colSum bb cc k).val + (if k = 0 then 0 else (carryVal cols (k - 1)).val) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hc' : productVal cols k + carryVal cols k * 256
      = colSum bb cc k + (if k = 0 then 0 else carryVal cols (k - 1)) := by
    rw [h_chain k hk]; ring
  have hprevb : (if k = 0 then (0 : ZMod p) else carryVal cols (k - 1)).val < 2 ^ 16 := by
    split_ifs with h
    · simp [ZMod.val_zero]
    · exact h_carry (k - 1) (by omega)
  have hcl := col_lift (productVal cols k) (carryVal cols k) (colSum bb cc k)
    (if k = 0 then 0 else carryVal cols (k - 1)) (h_pbyte k hk) (h_carry k hk)
    (colSum_lt bb cc hbb hcc k) hprevb hc'
  rw [hcl]
  congr 1
  split_ifs with h <;> simp [ZMod.val_zero]

/-- Apply `full_product` to the sixteen schoolbook column equations recovered from the raw
chain (via `colEq`): the witnessed `product` reassembles — mod `2^128` — to the integer
product of the two 16-byte sign/zero-extended operands. The high-half/`MULW` semantic conjuncts
read their result slices off this. -/
lemma product_reassembly (cols : Extracted.MulOperation (ZMod p)) (bb cc : Fin 16 → ZMod p)
    (hbb : ∀ i : Fin 16, (bb i).val < 256) (hcc : ∀ i : Fin 16, (cc i).val < 256)
    (h_chain : ∀ k : ℕ, k < 16 →
      productVal cols k = colSum bb cc k
        + (if k = 0 then 0 else carryVal cols (k - 1)) - carryVal cols k * 256)
    (h_pbyte : ∀ k : ℕ, k < 16 → (productVal cols k).val < 256)
    (h_carry : ∀ k : ℕ, k < 16 → (carryVal cols k).val < 2 ^ 16) :
    ((productVal cols 0).val + (productVal cols 1).val*256^1 + (productVal cols 2).val*256^2 + (productVal cols 3).val*256^3 + (productVal cols 4).val*256^4 + (productVal cols 5).val*256^5 + (productVal cols 6).val*256^6 + (productVal cols 7).val*256^7 + (productVal cols 8).val*256^8 + (productVal cols 9).val*256^9 + (productVal cols 10).val*256^10 + (productVal cols 11).val*256^11 + (productVal cols 12).val*256^12 + (productVal cols 13).val*256^13 + (productVal cols 14).val*256^14 + (productVal cols 15).val*256^15) % 2^128
      = (((byteAt bb 0).val + (byteAt bb 1).val*256^1 + (byteAt bb 2).val*256^2 + (byteAt bb 3).val*256^3 + (byteAt bb 4).val*256^4 + (byteAt bb 5).val*256^5 + (byteAt bb 6).val*256^6 + (byteAt bb 7).val*256^7 + (byteAt bb 8).val*256^8 + (byteAt bb 9).val*256^9 + (byteAt bb 10).val*256^10 + (byteAt bb 11).val*256^11 + (byteAt bb 12).val*256^12 + (byteAt bb 13).val*256^13 + (byteAt bb 14).val*256^14 + (byteAt bb 15).val*256^15)
         * ((byteAt cc 0).val + (byteAt cc 1).val*256^1 + (byteAt cc 2).val*256^2 + (byteAt cc 3).val*256^3 + (byteAt cc 4).val*256^4 + (byteAt cc 5).val*256^5 + (byteAt cc 6).val*256^6 + (byteAt cc 7).val*256^7 + (byteAt cc 8).val*256^8 + (byteAt cc 9).val*256^9 + (byteAt cc 10).val*256^10 + (byteAt cc 11).val*256^11 + (byteAt cc 12).val*256^12 + (byteAt cc 13).val*256^13 + (byteAt cc 14).val*256^14 + (byteAt cc 15).val*256^15)) % 2^128 := by
  have e0 : (productVal cols 0).val + (carryVal cols 0).val * 256
      = (byteAt bb 0).val * (byteAt cc 0).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 0 (by norm_num)
    rw [colSum_val bb cc hbb hcc 0] at h
    simp at h; omega
  have e1 : (productVal cols 1).val + (carryVal cols 1).val * 256
      = (byteAt bb 0).val * (byteAt cc 1).val + (byteAt bb 1).val * (byteAt cc 0).val + (carryVal cols 0).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 1 (by norm_num)
    rw [colSum_val bb cc hbb hcc 1] at h
    simp [Finset.sum_range_succ] at h; omega
  have e2 : (productVal cols 2).val + (carryVal cols 2).val * 256
      = (byteAt bb 0).val * (byteAt cc 2).val + (byteAt bb 1).val * (byteAt cc 1).val + (byteAt bb 2).val * (byteAt cc 0).val + (carryVal cols 1).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 2 (by norm_num)
    rw [colSum_val bb cc hbb hcc 2] at h
    simp [Finset.sum_range_succ] at h; omega
  have e3 : (productVal cols 3).val + (carryVal cols 3).val * 256
      = (byteAt bb 0).val * (byteAt cc 3).val + (byteAt bb 1).val * (byteAt cc 2).val + (byteAt bb 2).val * (byteAt cc 1).val + (byteAt bb 3).val * (byteAt cc 0).val + (carryVal cols 2).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 3 (by norm_num)
    rw [colSum_val bb cc hbb hcc 3] at h
    simp [Finset.sum_range_succ] at h; omega
  have e4 : (productVal cols 4).val + (carryVal cols 4).val * 256
      = (byteAt bb 0).val * (byteAt cc 4).val + (byteAt bb 1).val * (byteAt cc 3).val + (byteAt bb 2).val * (byteAt cc 2).val + (byteAt bb 3).val * (byteAt cc 1).val + (byteAt bb 4).val * (byteAt cc 0).val + (carryVal cols 3).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 4 (by norm_num)
    rw [colSum_val bb cc hbb hcc 4] at h
    simp [Finset.sum_range_succ] at h; omega
  have e5 : (productVal cols 5).val + (carryVal cols 5).val * 256
      = (byteAt bb 0).val * (byteAt cc 5).val + (byteAt bb 1).val * (byteAt cc 4).val + (byteAt bb 2).val * (byteAt cc 3).val + (byteAt bb 3).val * (byteAt cc 2).val + (byteAt bb 4).val * (byteAt cc 1).val + (byteAt bb 5).val * (byteAt cc 0).val + (carryVal cols 4).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 5 (by norm_num)
    rw [colSum_val bb cc hbb hcc 5] at h
    simp [Finset.sum_range_succ] at h; omega
  have e6 : (productVal cols 6).val + (carryVal cols 6).val * 256
      = (byteAt bb 0).val * (byteAt cc 6).val + (byteAt bb 1).val * (byteAt cc 5).val + (byteAt bb 2).val * (byteAt cc 4).val + (byteAt bb 3).val * (byteAt cc 3).val + (byteAt bb 4).val * (byteAt cc 2).val + (byteAt bb 5).val * (byteAt cc 1).val + (byteAt bb 6).val * (byteAt cc 0).val + (carryVal cols 5).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 6 (by norm_num)
    rw [colSum_val bb cc hbb hcc 6] at h
    simp [Finset.sum_range_succ] at h; omega
  have e7 : (productVal cols 7).val + (carryVal cols 7).val * 256
      = (byteAt bb 0).val * (byteAt cc 7).val + (byteAt bb 1).val * (byteAt cc 6).val + (byteAt bb 2).val * (byteAt cc 5).val + (byteAt bb 3).val * (byteAt cc 4).val + (byteAt bb 4).val * (byteAt cc 3).val + (byteAt bb 5).val * (byteAt cc 2).val + (byteAt bb 6).val * (byteAt cc 1).val + (byteAt bb 7).val * (byteAt cc 0).val + (carryVal cols 6).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 7 (by norm_num)
    rw [colSum_val bb cc hbb hcc 7] at h
    simp [Finset.sum_range_succ] at h; omega
  have e8 : (productVal cols 8).val + (carryVal cols 8).val * 256
      = (byteAt bb 0).val * (byteAt cc 8).val + (byteAt bb 1).val * (byteAt cc 7).val + (byteAt bb 2).val * (byteAt cc 6).val + (byteAt bb 3).val * (byteAt cc 5).val + (byteAt bb 4).val * (byteAt cc 4).val + (byteAt bb 5).val * (byteAt cc 3).val + (byteAt bb 6).val * (byteAt cc 2).val + (byteAt bb 7).val * (byteAt cc 1).val + (byteAt bb 8).val * (byteAt cc 0).val + (carryVal cols 7).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 8 (by norm_num)
    rw [colSum_val bb cc hbb hcc 8] at h
    simp [Finset.sum_range_succ] at h; omega
  have e9 : (productVal cols 9).val + (carryVal cols 9).val * 256
      = (byteAt bb 0).val * (byteAt cc 9).val + (byteAt bb 1).val * (byteAt cc 8).val + (byteAt bb 2).val * (byteAt cc 7).val + (byteAt bb 3).val * (byteAt cc 6).val + (byteAt bb 4).val * (byteAt cc 5).val + (byteAt bb 5).val * (byteAt cc 4).val + (byteAt bb 6).val * (byteAt cc 3).val + (byteAt bb 7).val * (byteAt cc 2).val + (byteAt bb 8).val * (byteAt cc 1).val + (byteAt bb 9).val * (byteAt cc 0).val + (carryVal cols 8).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 9 (by norm_num)
    rw [colSum_val bb cc hbb hcc 9] at h
    simp [Finset.sum_range_succ] at h; omega
  have e10 : (productVal cols 10).val + (carryVal cols 10).val * 256
      = (byteAt bb 0).val * (byteAt cc 10).val + (byteAt bb 1).val * (byteAt cc 9).val + (byteAt bb 2).val * (byteAt cc 8).val + (byteAt bb 3).val * (byteAt cc 7).val + (byteAt bb 4).val * (byteAt cc 6).val + (byteAt bb 5).val * (byteAt cc 5).val + (byteAt bb 6).val * (byteAt cc 4).val + (byteAt bb 7).val * (byteAt cc 3).val + (byteAt bb 8).val * (byteAt cc 2).val + (byteAt bb 9).val * (byteAt cc 1).val + (byteAt bb 10).val * (byteAt cc 0).val + (carryVal cols 9).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 10 (by norm_num)
    rw [colSum_val bb cc hbb hcc 10] at h
    simp [Finset.sum_range_succ] at h; omega
  have e11 : (productVal cols 11).val + (carryVal cols 11).val * 256
      = (byteAt bb 0).val * (byteAt cc 11).val + (byteAt bb 1).val * (byteAt cc 10).val + (byteAt bb 2).val * (byteAt cc 9).val + (byteAt bb 3).val * (byteAt cc 8).val + (byteAt bb 4).val * (byteAt cc 7).val + (byteAt bb 5).val * (byteAt cc 6).val + (byteAt bb 6).val * (byteAt cc 5).val + (byteAt bb 7).val * (byteAt cc 4).val + (byteAt bb 8).val * (byteAt cc 3).val + (byteAt bb 9).val * (byteAt cc 2).val + (byteAt bb 10).val * (byteAt cc 1).val + (byteAt bb 11).val * (byteAt cc 0).val + (carryVal cols 10).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 11 (by norm_num)
    rw [colSum_val bb cc hbb hcc 11] at h
    simp [Finset.sum_range_succ] at h; omega
  have e12 : (productVal cols 12).val + (carryVal cols 12).val * 256
      = (byteAt bb 0).val * (byteAt cc 12).val + (byteAt bb 1).val * (byteAt cc 11).val + (byteAt bb 2).val * (byteAt cc 10).val + (byteAt bb 3).val * (byteAt cc 9).val + (byteAt bb 4).val * (byteAt cc 8).val + (byteAt bb 5).val * (byteAt cc 7).val + (byteAt bb 6).val * (byteAt cc 6).val + (byteAt bb 7).val * (byteAt cc 5).val + (byteAt bb 8).val * (byteAt cc 4).val + (byteAt bb 9).val * (byteAt cc 3).val + (byteAt bb 10).val * (byteAt cc 2).val + (byteAt bb 11).val * (byteAt cc 1).val + (byteAt bb 12).val * (byteAt cc 0).val + (carryVal cols 11).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 12 (by norm_num)
    rw [colSum_val bb cc hbb hcc 12] at h
    simp [Finset.sum_range_succ] at h; omega
  have e13 : (productVal cols 13).val + (carryVal cols 13).val * 256
      = (byteAt bb 0).val * (byteAt cc 13).val + (byteAt bb 1).val * (byteAt cc 12).val + (byteAt bb 2).val * (byteAt cc 11).val + (byteAt bb 3).val * (byteAt cc 10).val + (byteAt bb 4).val * (byteAt cc 9).val + (byteAt bb 5).val * (byteAt cc 8).val + (byteAt bb 6).val * (byteAt cc 7).val + (byteAt bb 7).val * (byteAt cc 6).val + (byteAt bb 8).val * (byteAt cc 5).val + (byteAt bb 9).val * (byteAt cc 4).val + (byteAt bb 10).val * (byteAt cc 3).val + (byteAt bb 11).val * (byteAt cc 2).val + (byteAt bb 12).val * (byteAt cc 1).val + (byteAt bb 13).val * (byteAt cc 0).val + (carryVal cols 12).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 13 (by norm_num)
    rw [colSum_val bb cc hbb hcc 13] at h
    simp [Finset.sum_range_succ] at h; omega
  have e14 : (productVal cols 14).val + (carryVal cols 14).val * 256
      = (byteAt bb 0).val * (byteAt cc 14).val + (byteAt bb 1).val * (byteAt cc 13).val + (byteAt bb 2).val * (byteAt cc 12).val + (byteAt bb 3).val * (byteAt cc 11).val + (byteAt bb 4).val * (byteAt cc 10).val + (byteAt bb 5).val * (byteAt cc 9).val + (byteAt bb 6).val * (byteAt cc 8).val + (byteAt bb 7).val * (byteAt cc 7).val + (byteAt bb 8).val * (byteAt cc 6).val + (byteAt bb 9).val * (byteAt cc 5).val + (byteAt bb 10).val * (byteAt cc 4).val + (byteAt bb 11).val * (byteAt cc 3).val + (byteAt bb 12).val * (byteAt cc 2).val + (byteAt bb 13).val * (byteAt cc 1).val + (byteAt bb 14).val * (byteAt cc 0).val + (carryVal cols 13).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 14 (by norm_num)
    rw [colSum_val bb cc hbb hcc 14] at h
    simp [Finset.sum_range_succ] at h; omega
  have e15 : (productVal cols 15).val + (carryVal cols 15).val * 256
      = (byteAt bb 0).val * (byteAt cc 15).val + (byteAt bb 1).val * (byteAt cc 14).val + (byteAt bb 2).val * (byteAt cc 13).val + (byteAt bb 3).val * (byteAt cc 12).val + (byteAt bb 4).val * (byteAt cc 11).val + (byteAt bb 5).val * (byteAt cc 10).val + (byteAt bb 6).val * (byteAt cc 9).val + (byteAt bb 7).val * (byteAt cc 8).val + (byteAt bb 8).val * (byteAt cc 7).val + (byteAt bb 9).val * (byteAt cc 6).val + (byteAt bb 10).val * (byteAt cc 5).val + (byteAt bb 11).val * (byteAt cc 4).val + (byteAt bb 12).val * (byteAt cc 3).val + (byteAt bb 13).val * (byteAt cc 2).val + (byteAt bb 14).val * (byteAt cc 1).val + (byteAt bb 15).val * (byteAt cc 0).val + (carryVal cols 14).val := by
    have h := colEq cols bb cc hbb hcc h_chain h_pbyte h_carry 15 (by norm_num)
    rw [colSum_val bb cc hbb hcc 15] at h
    simp [Finset.sum_range_succ] at h; omega
  exact full_product (byteAt bb 0).val (byteAt bb 1).val (byteAt bb 2).val (byteAt bb 3).val (byteAt bb 4).val (byteAt bb 5).val (byteAt bb 6).val (byteAt bb 7).val (byteAt bb 8).val (byteAt bb 9).val (byteAt bb 10).val (byteAt bb 11).val (byteAt bb 12).val (byteAt bb 13).val (byteAt bb 14).val (byteAt bb 15).val (byteAt cc 0).val (byteAt cc 1).val (byteAt cc 2).val (byteAt cc 3).val (byteAt cc 4).val (byteAt cc 5).val (byteAt cc 6).val (byteAt cc 7).val (byteAt cc 8).val (byteAt cc 9).val (byteAt cc 10).val (byteAt cc 11).val (byteAt cc 12).val (byteAt cc 13).val (byteAt cc 14).val (byteAt cc 15).val
    (productVal cols 0).val (productVal cols 1).val (productVal cols 2).val (productVal cols 3).val (productVal cols 4).val (productVal cols 5).val (productVal cols 6).val (productVal cols 7).val (productVal cols 8).val (productVal cols 9).val (productVal cols 10).val (productVal cols 11).val (productVal cols 12).val (productVal cols 13).val (productVal cols 14).val (productVal cols 15).val (carryVal cols 0).val (carryVal cols 1).val (carryVal cols 2).val (carryVal cols 3).val (carryVal cols 4).val (carryVal cols 5).val (carryVal cols 6).val (carryVal cols 7).val (carryVal cols 8).val (carryVal cols 9).val (carryVal cols 10).val (carryVal cols 11).val (carryVal cols 12).val (carryVal cols 13).val (carryVal cols 14).val (carryVal cols 15).val
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15

/-- The raw schoolbook constraint form, stated against the witnessed `product`/`carry`/sign-extend
cols: each product byte is the column sum plus incoming carry minus the outgoing carry times 256;
product bytes are genuine bytes and carries are 16-bit-bounded; the sign-extend selectors are the
gated operand MSBs; all booleanity. (The byte-MSB table lookups tying `b_msb`/`c_msb` to the operand
top bytes are deferred to the faithfulness anchor.) -/
def RawSpec (input : Inputs (ZMod p)) (cols : Extracted.MulOperation (ZMod p)) : Prop :=
  let bb := extendedBytes input.b cols.b_lower_byte cols.b_sign_extend
  let cc := extendedBytes input.c cols.c_lower_byte cols.c_sign_extend
  (∀ k : ℕ, k < 16 →
      productVal cols k =
        colSum bb cc k + (if k = 0 then 0 else carryVal cols (k - 1)) - carryVal cols k * 256) ∧
  (∀ k : ℕ, k < 16 → (productVal cols k).val < 256) ∧
  (∀ k : ℕ, k < 16 → (carryVal cols k).val < 2 ^ 16) ∧
  cols.b_sign_extend = (input.is_mulh + input.is_mulhsu) * cols.b_msb ∧
  cols.c_sign_extend = input.is_mulh * cols.c_msb ∧
  (cols.b_msb = 0 ∨ cols.b_msb = 1) ∧ (cols.c_msb = 0 ∨ cols.c_msb = 1) ∧
  (cols.b_sign_extend = 0 ∨ cols.b_sign_extend = 1) ∧
  (cols.c_sign_extend = 0 ∨ cols.c_sign_extend = 1)


/-- The full 16-byte sign/zero-extended operand value: the low eight bytes reassemble to
`w.toNat` (via `lower_toNat`); the high eight bytes are all the sign fill `s * 255`. -/
lemma extendedBytes_toNat (w : Word (ZMod p)) (lower : Extracted.U16toU8Operation (ZMod p))
    (s : ZMod p) (hspec : U16toU8OperationSafe.DecompSpec w lower) :
    (byteAt (extendedBytes w lower s) 0).val + (byteAt (extendedBytes w lower s) 1).val*256^1 + (byteAt (extendedBytes w lower s) 2).val*256^2 + (byteAt (extendedBytes w lower s) 3).val*256^3 + (byteAt (extendedBytes w lower s) 4).val*256^4 + (byteAt (extendedBytes w lower s) 5).val*256^5 + (byteAt (extendedBytes w lower s) 6).val*256^6 + (byteAt (extendedBytes w lower s) 7).val*256^7 + (byteAt (extendedBytes w lower s) 8).val*256^8 + (byteAt (extendedBytes w lower s) 9).val*256^9 + (byteAt (extendedBytes w lower s) 10).val*256^10 + (byteAt (extendedBytes w lower s) 11).val*256^11 + (byteAt (extendedBytes w lower s) 12).val*256^12 + (byteAt (extendedBytes w lower s) 13).val*256^13 + (byteAt (extendedBytes w lower s) 14).val*256^14 + (byteAt (extendedBytes w lower s) 15).val*256^15
      = w.toNat + (s * 255).val * (256^8 + 256^9 + 256^10 + 256^11 + 256^12 + 256^13 + 256^14 + 256^15) := by
  have hlow := lower_toNat w lower s hspec
  have e8 : byteAt (extendedBytes w lower s) 8 = s * 255 := rfl
  have e9 : byteAt (extendedBytes w lower s) 9 = s * 255 := rfl
  have e10 : byteAt (extendedBytes w lower s) 10 = s * 255 := rfl
  have e11 : byteAt (extendedBytes w lower s) 11 = s * 255 := rfl
  have e12 : byteAt (extendedBytes w lower s) 12 = s * 255 := rfl
  have e13 : byteAt (extendedBytes w lower s) 13 = s * 255 := rfl
  have e14 : byteAt (extendedBytes w lower s) 14 = s * 255 := rfl
  have e15 : byteAt (extendedBytes w lower s) 15 = s * 255 := rfl
  rw [e8, e9, e10, e11, e12, e13, e14, e15]
  omega

set_option linter.unusedSectionVars false in
/-- `BitVec.ofNat 128 (w.toNat)` is the 128-bit zero-extension `setWidth 128` of the word. -/
lemma ofNat128_eq_setWidth (w : Word (ZMod p)) (hw : w.isU64) :
    BitVec.ofNat 128 (Word.toNat w) = (Word.toBitVec64 w).setWidth 128 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Word.toBitVec64_toNat hw]

set_option linter.unusedSectionVars false in
/-- A 128-bit value is its own `BitVec.ofNat` round-trip. -/
lemma ofNat128_signExtend (w : Word (ZMod p)) :
    BitVec.ofNat 128 ((Word.toBitVec64 w).signExtend 128).toNat
      = (Word.toBitVec64 w).signExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- The 128-bit sign extension of a 64-bit word, as a `ℕ`: `w.toNat` plus the sign fill
`2^128 - 2^64` when the top bit (`w[3].val ≥ 32768`) is set. -/
lemma signExtend128_toNat (w : Word (ZMod p)) (hw : w.isU64) :
    ((Word.toBitVec64 w).signExtend 128).toNat
      = Word.toNat w + (if w[3].val ≥ 32768 then 2 ^ 128 - 2 ^ 64 else 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  have hmsb_iff : (Word.toBitVec64 w).msb = true ↔ w[3].val ≥ 32768 := by
    rw [BitVec.msb_eq_decide, decide_eq_true_eq, Word.toBitVec64_toNat hw, Word.toNat_def]; omega
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, Word.toBitVec64_toNat hw,
      Nat.mod_eq_of_lt (show Word.toNat w < 2 ^ 128 by rw [Word.toNat_def]; omega)]
  by_cases hm : (Word.toBitVec64 w).msb = true
  · rw [if_pos hm, if_pos (hmsb_iff.mp hm)]
  · rw [if_neg hm, if_neg (fun hc => hm (hmsb_iff.mpr hc))]

set_option maxHeartbeats 8000000 in
/-- The high-64 slice (`MULH*` family) of the witnessed product equals bits 64..127 of the
128-bit product of the two extended operand values `Bext`, `Cext`. -/
lemma high_half_eq (cols : Extracted.MulOperation (ZMod p)) (bb cc : Fin 16 → ZMod p)
    (Bext Cext : ℕ)
    (hbb : ∀ i : Fin 16, (bb i).val < 256) (hcc : ∀ i : Fin 16, (cc i).val < 256)
    (h_chain : ∀ k : ℕ, k < 16 → productVal cols k = colSum bb cc k
        + (if k = 0 then 0 else carryVal cols (k - 1)) - carryVal cols k * 256)
    (h_pbyte : ∀ k : ℕ, k < 16 → (productVal cols k).val < 256)
    (h_carry : ∀ k : ℕ, k < 16 → (carryVal cols k).val < 2 ^ 16)
    (hBlt : Bext < 2 ^ 128) (hClt : Cext < 2 ^ 128)
    (hSbb : (byteAt bb 0).val + (byteAt bb 1).val*256^1 + (byteAt bb 2).val*256^2 + (byteAt bb 3).val*256^3 + (byteAt bb 4).val*256^4 + (byteAt bb 5).val*256^5 + (byteAt bb 6).val*256^6 + (byteAt bb 7).val*256^7 + (byteAt bb 8).val*256^8 + (byteAt bb 9).val*256^9 + (byteAt bb 10).val*256^10 + (byteAt bb 11).val*256^11 + (byteAt bb 12).val*256^12 + (byteAt bb 13).val*256^13 + (byteAt bb 14).val*256^14 + (byteAt bb 15).val*256^15 = Bext)
    (hScc : (byteAt cc 0).val + (byteAt cc 1).val*256^1 + (byteAt cc 2).val*256^2 + (byteAt cc 3).val*256^3 + (byteAt cc 4).val*256^4 + (byteAt cc 5).val*256^5 + (byteAt cc 6).val*256^6 + (byteAt cc 7).val*256^7 + (byteAt cc 8).val*256^8 + (byteAt cc 9).val*256^9 + (byteAt cc 10).val*256^10 + (byteAt cc 11).val*256^11 + (byteAt cc 12).val*256^12 + (byteAt cc 13).val*256^13 + (byteAt cc 14).val*256^14 + (byteAt cc 15).val*256^15 = Cext) :
    Word.toBitVec64 #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256, productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256]
      = ((BitVec.ofNat 128 Bext * BitVec.ofNat 128 Cext) >>> 64).setWidth 64 := by
  have hbpc : ∀ a b : ZMod p, a.val < 256 → b.val < 256 → (a + b * 256).val = a.val + b.val * 256 :=
    fun a b ha hb => byte_compose_val ha hb rfl
  have hUhi : Word.isU64 #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256, productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256] := by
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
        List.getElem_cons_zero]
    · rw [hbpc _ _ (h_pbyte 8 (by norm_num)) (h_pbyte 9 (by norm_num))]
      have h8 := h_pbyte 8 (by norm_num); have h9 := h_pbyte 9 (by norm_num); omega
    · rw [hbpc _ _ (h_pbyte 10 (by norm_num)) (h_pbyte 11 (by norm_num))]
      have h10 := h_pbyte 10 (by norm_num); have h11 := h_pbyte 11 (by norm_num); omega
    · rw [hbpc _ _ (h_pbyte 12 (by norm_num)) (h_pbyte 13 (by norm_num))]
      have h12 := h_pbyte 12 (by norm_num); have h13 := h_pbyte 13 (by norm_num); omega
    · rw [hbpc _ _ (h_pbyte 14 (by norm_num)) (h_pbyte 15 (by norm_num))]
      have h14 := h_pbyte 14 (by norm_num); have h15 := h_pbyte 15 (by norm_num); omega
  have hreasm := product_reassembly cols bb cc hbb hcc h_chain h_pbyte h_carry
  rw [hSbb, hScc] at hreasm
  have hHi : Word.toNat #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256, productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256]
      = (productVal cols 8).val + (productVal cols 9).val*256 + ((productVal cols 10).val + (productVal cols 11).val*256)*2^16 + ((productVal cols 12).val + (productVal cols 13).val*256)*2^32 + ((productVal cols 14).val + (productVal cols 15).val*256)*2^48 := by
    rw [Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero]
    rw [hbpc _ _ (h_pbyte 8 (by norm_num)) (h_pbyte 9 (by norm_num)),
        hbpc _ _ (h_pbyte 10 (by norm_num)) (h_pbyte 11 (by norm_num)),
        hbpc _ _ (h_pbyte 12 (by norm_num)) (h_pbyte 13 (by norm_num)),
        hbpc _ _ (h_pbyte 14 (by norm_num)) (h_pbyte 15 (by norm_num))]
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hUhi, hHi, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_eq_div_pow]
  have q0 := h_pbyte 0 (by norm_num)
  have q1 := h_pbyte 1 (by norm_num)
  have q2 := h_pbyte 2 (by norm_num)
  have q3 := h_pbyte 3 (by norm_num)
  have q4 := h_pbyte 4 (by norm_num)
  have q5 := h_pbyte 5 (by norm_num)
  have q6 := h_pbyte 6 (by norm_num)
  have q7 := h_pbyte 7 (by norm_num)
  have q8 := h_pbyte 8 (by norm_num)
  have q9 := h_pbyte 9 (by norm_num)
  have q10 := h_pbyte 10 (by norm_num)
  have q11 := h_pbyte 11 (by norm_num)
  have q12 := h_pbyte 12 (by norm_num)
  have q13 := h_pbyte 13 (by norm_num)
  have q14 := h_pbyte 14 (by norm_num)
  have q15 := h_pbyte 15 (by norm_num)
  rw [Nat.mod_eq_of_lt hBlt, Nat.mod_eq_of_lt hClt]
  omega

set_option maxHeartbeats 1600000 in
/-- Forward (soundness) core: the raw schoolbook form implies the per-variant semantic result.
The `MUL` (low-64, unsigned) conjunct is proved end-to-end here via the native `low_half` reassembly;
the four high-half / `MULW` conjuncts are scoped sorries (they read further slices off the *full*
128-bit `product_reassembly`, deferred to a later pass). The `U16toU8`/`U16MSB` sub-op `Spec`s are
threaded in (they are discharged by the composed subcircuits in `soundness`). -/
theorem mulSemantics_of_raw {input : Inputs (ZMod p)} {cols : Extracted.MulOperation (ZMod p)}
    (hbU : Word.isU64 input.b) (hcU : Word.isU64 input.c)
    (hmul_b : input.is_mul = 0 ∨ input.is_mul = 1) (hmh_b : input.is_mulh = 0 ∨ input.is_mulh = 1)
    (hmhu_b : input.is_mulhu = 0 ∨ input.is_mulhu = 1) (hmhsu_b : input.is_mulhsu = 0 ∨ input.is_mulhsu = 1)
    (hmw_b : input.is_mulw = 0 ∨ input.is_mulw = 1)
    (hsum : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 0 ∨
      input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1)
    (hb_low : U16toU8OperationSafe.DecompSpec input.b cols.b_lower_byte)
    (hc_low : U16toU8OperationSafe.DecompSpec input.c cols.c_lower_byte)
    (hmsb_bool : cols.product_msb.msb = 0 ∨ cols.product_msb.msb = 1)
    (hmsb : input.is_mulw = 1 → cols.product_msb.msb
      = if (cols.product[2] + cols.product[3] * 256).val ≥ 32768 then 1 else 0)
    (hb_msb : cols.b_msb = if input.b[3].val ≥ 32768 then 1 else 0)
    (hc_msb : cols.c_msb = if input.c[3].val ≥ 32768 then 1 else 0)
    (h_raw : RawSpec input cols) : SemanticSpec input cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  obtain ⟨h_chain, h_pbyte, h_carry, h_bse, h_cse, h_bmsb, h_cmsb, h_bse01, h_cse01⟩ := h_raw
  set bb := extendedBytes input.b cols.b_lower_byte cols.b_sign_extend with hbb_def
  set cc := extendedBytes input.c cols.c_lower_byte cols.c_sign_extend with hcc_def
  have hbb_lt : ∀ i : Fin 16, (bb i).val < 256 :=
    extendedBytes_byte_lt input.b cols.b_lower_byte cols.b_sign_extend
      (fun i => (hb_low i).1) (fun i => (hb_low i).2.1) h_bse01
  have hcc_lt : ∀ i : Fin 16, (cc i).val < 256 :=
    extendedBytes_byte_lt input.c cols.c_lower_byte cols.c_sign_extend
      (fun i => (hc_low i).1) (fun i => (hc_low i).2.1) h_cse01
  -- A byte pair packs to a 16-bit value; the witnessed `msb` is a bit, so `msb * 65535` is 16-bit.
  have hbp : ∀ a b : ZMod p, a.val < 256 → b.val < 256 → (a + b * 256).val < 2 ^ 16 := by
    intro a b ha hb; rw [byte_compose_val ha hb rfl]; omega
  have hmsb01 : cols.product_msb.msb = 0 ∨ cols.product_msb.msb = 1 := hmsb_bool
  have hmsbp : (cols.product_msb.msb * 65535).val < 2 ^ 16 := by
    rcases hmsb01 with h | h
    · rw [h, zero_mul, ZMod.val_zero]; norm_num
    · rw [h, one_mul, show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 24 < p); omega)]; norm_num
  have hisU64 : Word.isU64 (resultWord input cols) := by
    unfold resultWord
    split_ifs with h1 h2 <;> refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
        List.getElem_cons_zero] <;>
      first
        | exact hbp _ _ (h_pbyte _ (by norm_num)) (h_pbyte _ (by norm_num))
        | exact hmsbp
  refine ⟨hisU64, ?_, ?_, ?_, ?_, ?_⟩
  · -- MUL: low 64 bits of the unsigned product
    intro hmul
    have hsum1 : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1 :=
      sum_eq_one hmul_b hmh_b hmhu_b hmhsu_b hmw_b hsum (Or.inl hmul)
    obtain ⟨hmh0, hmhu0, hmhsu0, hmw0⟩ := rest_zero hmh_b hmhu_b hmhsu_b hmw_b hmul hsum1
    have hrw : resultWord input cols
        = #v[productVal cols 0 + productVal cols 1 * 256, productVal cols 2 + productVal cols 3 * 256,
             productVal cols 4 + productVal cols 5 * 256, productVal cols 6 + productVal cols 7 * 256] := by
      unfold resultWord
      rw [if_neg (by rw [hmw0]; exact zero_ne_one), if_neg (by rw [hmh0, hmhu0, hmhsu0]; simp)]
    have hUresult := hrw ▸ hisU64
    -- The eight low column equations, fed to `low_half`.
    have e0 : (productVal cols 0).val + (carryVal cols 0).val * 256
        = (byteAt bb 0).val * (byteAt cc 0).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 0 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 0] at h
      simp at h; omega
    have e1 : (productVal cols 1).val + (carryVal cols 1).val * 256
        = (byteAt bb 0).val * (byteAt cc 1).val + (byteAt bb 1).val * (byteAt cc 0).val
          + (carryVal cols 0).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 1 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 1] at h
      simp [Finset.sum_range_succ] at h; omega
    have e2 : (productVal cols 2).val + (carryVal cols 2).val * 256
        = (byteAt bb 0).val * (byteAt cc 2).val + (byteAt bb 1).val * (byteAt cc 1).val
          + (byteAt bb 2).val * (byteAt cc 0).val + (carryVal cols 1).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 2 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 2] at h
      simp [Finset.sum_range_succ] at h; omega
    have e3 : (productVal cols 3).val + (carryVal cols 3).val * 256
        = (byteAt bb 0).val * (byteAt cc 3).val + (byteAt bb 1).val * (byteAt cc 2).val
          + (byteAt bb 2).val * (byteAt cc 1).val + (byteAt bb 3).val * (byteAt cc 0).val
          + (carryVal cols 2).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 3 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 3] at h
      simp [Finset.sum_range_succ] at h; omega
    have e4 : (productVal cols 4).val + (carryVal cols 4).val * 256
        = (byteAt bb 0).val * (byteAt cc 4).val + (byteAt bb 1).val * (byteAt cc 3).val
          + (byteAt bb 2).val * (byteAt cc 2).val + (byteAt bb 3).val * (byteAt cc 1).val
          + (byteAt bb 4).val * (byteAt cc 0).val + (carryVal cols 3).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 4 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 4] at h
      simp [Finset.sum_range_succ] at h; omega
    have e5 : (productVal cols 5).val + (carryVal cols 5).val * 256
        = (byteAt bb 0).val * (byteAt cc 5).val + (byteAt bb 1).val * (byteAt cc 4).val
          + (byteAt bb 2).val * (byteAt cc 3).val + (byteAt bb 3).val * (byteAt cc 2).val
          + (byteAt bb 4).val * (byteAt cc 1).val + (byteAt bb 5).val * (byteAt cc 0).val
          + (carryVal cols 4).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 5 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 5] at h
      simp [Finset.sum_range_succ] at h; omega
    have e6 : (productVal cols 6).val + (carryVal cols 6).val * 256
        = (byteAt bb 0).val * (byteAt cc 6).val + (byteAt bb 1).val * (byteAt cc 5).val
          + (byteAt bb 2).val * (byteAt cc 4).val + (byteAt bb 3).val * (byteAt cc 3).val
          + (byteAt bb 4).val * (byteAt cc 2).val + (byteAt bb 5).val * (byteAt cc 1).val
          + (byteAt bb 6).val * (byteAt cc 0).val + (carryVal cols 5).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 6 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 6] at h
      simp [Finset.sum_range_succ] at h; omega
    have e7 : (productVal cols 7).val + (carryVal cols 7).val * 256
        = (byteAt bb 0).val * (byteAt cc 7).val + (byteAt bb 1).val * (byteAt cc 6).val
          + (byteAt bb 2).val * (byteAt cc 5).val + (byteAt bb 3).val * (byteAt cc 4).val
          + (byteAt bb 4).val * (byteAt cc 3).val + (byteAt bb 5).val * (byteAt cc 2).val
          + (byteAt bb 6).val * (byteAt cc 1).val + (byteAt bb 7).val * (byteAt cc 0).val
          + (carryVal cols 6).val := by
      have h := colEq cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry 7 (by norm_num)
      rw [colSum_val bb cc hbb_lt hcc_lt 7] at h
      simp [Finset.sum_range_succ] at h; omega
    -- Reassemble `result.toNat`, the operand byte sums, and finish through `low_half`.
    have hresult_toNat : Word.toNat
        #v[productVal cols 0 + productVal cols 1 * 256, productVal cols 2 + productVal cols 3 * 256,
           productVal cols 4 + productVal cols 5 * 256, productVal cols 6 + productVal cols 7 * 256]
        = (productVal cols 0).val + (productVal cols 1).val * 256 + (productVal cols 2).val * 256 ^ 2
          + (productVal cols 3).val * 256 ^ 3 + (productVal cols 4).val * 256 ^ 4
          + (productVal cols 5).val * 256 ^ 5 + (productVal cols 6).val * 256 ^ 6
          + (productVal cols 7).val * 256 ^ 7 := by
      rw [Word.toNat_def]
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
        List.getElem_cons_zero]
      rw [byte_compose_val (h_pbyte 0 (by norm_num)) (h_pbyte 1 (by norm_num)) rfl,
          byte_compose_val (h_pbyte 2 (by norm_num)) (h_pbyte 3 (by norm_num)) rfl,
          byte_compose_val (h_pbyte 4 (by norm_num)) (h_pbyte 5 (by norm_num)) rfl,
          byte_compose_val (h_pbyte 6 (by norm_num)) (h_pbyte 7 (by norm_num)) rfl]
      ring
    have hlt64 : (productVal cols 0).val + (productVal cols 1).val * 256
        + (productVal cols 2).val * 256 ^ 2 + (productVal cols 3).val * 256 ^ 3
        + (productVal cols 4).val * 256 ^ 4 + (productVal cols 5).val * 256 ^ 5
        + (productVal cols 6).val * 256 ^ 6 + (productVal cols 7).val * 256 ^ 7 < 2 ^ 64 := by
      have b0 := h_pbyte 0 (by norm_num); have b1 := h_pbyte 1 (by norm_num)
      have b2 := h_pbyte 2 (by norm_num); have b3 := h_pbyte 3 (by norm_num)
      have b4 := h_pbyte 4 (by norm_num); have b5 := h_pbyte 5 (by norm_num)
      have b6 := h_pbyte 6 (by norm_num); have b7 := h_pbyte 7 (by norm_num)
      omega
    have hbToNat : Word.toNat input.b
        = (byteAt bb 0).val + (byteAt bb 1).val * 256 + (byteAt bb 2).val * 256 ^ 2
          + (byteAt bb 3).val * 256 ^ 3 + (byteAt bb 4).val * 256 ^ 4 + (byteAt bb 5).val * 256 ^ 5
          + (byteAt bb 6).val * 256 ^ 6 + (byteAt bb 7).val * 256 ^ 7 := by
      rw [hbb_def]; exact lower_toNat input.b cols.b_lower_byte cols.b_sign_extend hb_low
    have hcToNat : Word.toNat input.c
        = (byteAt cc 0).val + (byteAt cc 1).val * 256 + (byteAt cc 2).val * 256 ^ 2
          + (byteAt cc 3).val * 256 ^ 3 + (byteAt cc 4).val * 256 ^ 4 + (byteAt cc 5).val * 256 ^ 5
          + (byteAt cc 6).val * 256 ^ 6 + (byteAt cc 7).val * 256 ^ 7 := by
      rw [hcc_def]; exact lower_toNat input.c cols.c_lower_byte cols.c_sign_extend hc_low
    rw [hrw, ← BitVec.toNat_inj, Word.toBitVec64_toNat hUresult, BitVec.toNat_mul,
        Word.toBitVec64_toNat hbU, Word.toBitVec64_toNat hcU, hresult_toNat,
        ← Nat.mod_eq_of_lt hlt64,
        low_half (byteAt bb 0).val (byteAt bb 1).val (byteAt bb 2).val (byteAt bb 3).val
          (byteAt bb 4).val (byteAt bb 5).val (byteAt bb 6).val (byteAt bb 7).val
          (byteAt cc 0).val (byteAt cc 1).val (byteAt cc 2).val (byteAt cc 3).val
          (byteAt cc 4).val (byteAt cc 5).val (byteAt cc 6).val (byteAt cc 7).val
          (productVal cols 0).val (productVal cols 1).val (productVal cols 2).val (productVal cols 3).val
          (productVal cols 4).val (productVal cols 5).val (productVal cols 6).val (productVal cols 7).val
          (carryVal cols 0).val (carryVal cols 1).val (carryVal cols 2).val (carryVal cols 3).val
          (carryVal cols 4).val (carryVal cols 5).val (carryVal cols 6).val (carryVal cols 7).val
          e0 e1 e2 e3 e4 e5 e6 e7,
        ← hbToNat, ← hcToNat]
  · intro hmulhu
    have hsum1 : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1 :=
      sum_eq_one hmul_b hmh_b hmhu_b hmhsu_b hmw_b hsum (Or.inr (Or.inr (Or.inl hmulhu)))
    have hsum' : input.is_mulhu + input.is_mul + input.is_mulh + input.is_mulhsu + input.is_mulw = 1 := by linear_combination hsum1
    obtain ⟨hmul0, hmh0, hmhsu0, hmw0⟩ := rest_zero hmul_b hmh_b hmhsu_b hmw_b hmulhu hsum'
    have hbse0 : cols.b_sign_extend = 0 := by rw [h_bse, hmh0, hmhsu0]; ring
    have hcse0 : cols.c_sign_extend = 0 := by rw [h_cse, hmh0]; ring
    have hrw : resultWord input cols = #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256, productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256] := by
      unfold resultWord
      rw [if_neg (by rw [hmw0]; exact zero_ne_one), if_pos (Or.inr (Or.inl hmulhu))]
    have hSbb : (byteAt bb 0).val + (byteAt bb 1).val*256^1 + (byteAt bb 2).val*256^2 + (byteAt bb 3).val*256^3 + (byteAt bb 4).val*256^4 + (byteAt bb 5).val*256^5 + (byteAt bb 6).val*256^6 + (byteAt bb 7).val*256^7 + (byteAt bb 8).val*256^8 + (byteAt bb 9).val*256^9 + (byteAt bb 10).val*256^10 + (byteAt bb 11).val*256^11 + (byteAt bb 12).val*256^12 + (byteAt bb 13).val*256^13 + (byteAt bb 14).val*256^14 + (byteAt bb 15).val*256^15 = Word.toNat input.b := by
      rw [hbb_def, extendedBytes_toNat input.b cols.b_lower_byte cols.b_sign_extend hb_low, hbse0]; simp
    have hScc : (byteAt cc 0).val + (byteAt cc 1).val*256^1 + (byteAt cc 2).val*256^2 + (byteAt cc 3).val*256^3 + (byteAt cc 4).val*256^4 + (byteAt cc 5).val*256^5 + (byteAt cc 6).val*256^6 + (byteAt cc 7).val*256^7 + (byteAt cc 8).val*256^8 + (byteAt cc 9).val*256^9 + (byteAt cc 10).val*256^10 + (byteAt cc 11).val*256^11 + (byteAt cc 12).val*256^12 + (byteAt cc 13).val*256^13 + (byteAt cc 14).val*256^14 + (byteAt cc 15).val*256^15 = Word.toNat input.c := by
      rw [hcc_def, extendedBytes_toNat input.c cols.c_lower_byte cols.c_sign_extend hc_low, hcse0]; simp
    have hBlt : Word.toNat input.b < 2 ^ 128 := by
      obtain ⟨a,b,c,d⟩ := Word.lt_cases_of_isU64 hbU; rw [Word.toNat_def]; omega
    have hClt : Word.toNat input.c < 2 ^ 128 := by
      obtain ⟨a,b,c,d⟩ := Word.lt_cases_of_isU64 hcU; rw [Word.toNat_def]; omega
    rw [hrw, ← ofNat128_eq_setWidth input.b hbU, ← ofNat128_eq_setWidth input.c hcU]
    exact high_half_eq cols bb cc (Word.toNat input.b) (Word.toNat input.c)
      hbb_lt hcc_lt h_chain h_pbyte h_carry hBlt hClt hSbb hScc
  · intro hmulh
    have hsum1 : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1 :=
      sum_eq_one hmul_b hmh_b hmhu_b hmhsu_b hmw_b hsum (Or.inr (Or.inl hmulh))
    have hsum' : input.is_mulh + input.is_mul + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1 := by linear_combination hsum1
    obtain ⟨hmul0, hmhu0, hmhsu0, hmw0⟩ := rest_zero hmul_b hmhu_b hmhsu_b hmw_b hmulh hsum'
    have hbse_eq : cols.b_sign_extend = cols.b_msb := by rw [h_bse, hmulh, hmhsu0]; simp
    have hcse_eq : cols.c_sign_extend = cols.c_msb := by rw [h_cse, hmulh]; simp
    have hrw : resultWord input cols = #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256, productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256] := by
      unfold resultWord
      rw [if_neg (by rw [hmw0]; exact zero_ne_one), if_pos (Or.inl hmulh)]
    have hSbb : (byteAt bb 0).val + (byteAt bb 1).val*256^1 + (byteAt bb 2).val*256^2 + (byteAt bb 3).val*256^3 + (byteAt bb 4).val*256^4 + (byteAt bb 5).val*256^5 + (byteAt bb 6).val*256^6 + (byteAt bb 7).val*256^7 + (byteAt bb 8).val*256^8 + (byteAt bb 9).val*256^9 + (byteAt bb 10).val*256^10 + (byteAt bb 11).val*256^11 + (byteAt bb 12).val*256^12 + (byteAt bb 13).val*256^13 + (byteAt bb 14).val*256^14 + (byteAt bb 15).val*256^15 = ((Word.toBitVec64 input.b).signExtend 128).toNat := by
      rw [hbb_def, extendedBytes_toNat input.b cols.b_lower_byte cols.b_sign_extend hb_low, signExtend128_toNat input.b hbU]
      congr 1
      rw [hbse_eq, hb_msb]
      split_ifs with hge
      · rw [one_mul, show (255 : ZMod p) = ((255 : ℕ) : ZMod p) from by norm_cast,
            ZMod.val_natCast_of_lt (show (255:ℕ) < p from by have := Fact.out (p := 2 ^ 24 < p); omega)]
        norm_num
      · simp
    have hScc : (byteAt cc 0).val + (byteAt cc 1).val*256^1 + (byteAt cc 2).val*256^2 + (byteAt cc 3).val*256^3 + (byteAt cc 4).val*256^4 + (byteAt cc 5).val*256^5 + (byteAt cc 6).val*256^6 + (byteAt cc 7).val*256^7 + (byteAt cc 8).val*256^8 + (byteAt cc 9).val*256^9 + (byteAt cc 10).val*256^10 + (byteAt cc 11).val*256^11 + (byteAt cc 12).val*256^12 + (byteAt cc 13).val*256^13 + (byteAt cc 14).val*256^14 + (byteAt cc 15).val*256^15 = ((Word.toBitVec64 input.c).signExtend 128).toNat := by
      rw [hcc_def, extendedBytes_toNat input.c cols.c_lower_byte cols.c_sign_extend hc_low, signExtend128_toNat input.c hcU]
      congr 1
      rw [hcse_eq, hc_msb]
      split_ifs with hge
      · rw [one_mul, show (255 : ZMod p) = ((255 : ℕ) : ZMod p) from by norm_cast,
            ZMod.val_natCast_of_lt (show (255:ℕ) < p from by have := Fact.out (p := 2 ^ 24 < p); omega)]
        norm_num
      · simp
    rw [hrw, ← ofNat128_signExtend input.b, ← ofNat128_signExtend input.c]
    exact high_half_eq cols bb cc _ _ hbb_lt hcc_lt h_chain h_pbyte h_carry (BitVec.isLt _) (BitVec.isLt _) hSbb hScc
  · intro hmulhsu
    have hsum1 : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1 :=
      sum_eq_one hmul_b hmh_b hmhu_b hmhsu_b hmw_b hsum (Or.inr (Or.inr (Or.inr (Or.inl hmulhsu))))
    have hsum' : input.is_mulhsu + input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulw = 1 := by linear_combination hsum1
    obtain ⟨hmul0, hmh0, hmhu0, hmw0⟩ := rest_zero hmul_b hmh_b hmhu_b hmw_b hmulhsu hsum'
    have hbse_eq : cols.b_sign_extend = cols.b_msb := by rw [h_bse, hmh0, hmulhsu]; simp
    have hcse0 : cols.c_sign_extend = 0 := by rw [h_cse, hmh0]; ring
    have hrw : resultWord input cols = #v[productVal cols 8 + productVal cols 9 * 256, productVal cols 10 + productVal cols 11 * 256, productVal cols 12 + productVal cols 13 * 256, productVal cols 14 + productVal cols 15 * 256] := by
      unfold resultWord
      rw [if_neg (by rw [hmw0]; exact zero_ne_one), if_pos (Or.inr (Or.inr hmulhsu))]
    have hSbb : (byteAt bb 0).val + (byteAt bb 1).val*256^1 + (byteAt bb 2).val*256^2 + (byteAt bb 3).val*256^3 + (byteAt bb 4).val*256^4 + (byteAt bb 5).val*256^5 + (byteAt bb 6).val*256^6 + (byteAt bb 7).val*256^7 + (byteAt bb 8).val*256^8 + (byteAt bb 9).val*256^9 + (byteAt bb 10).val*256^10 + (byteAt bb 11).val*256^11 + (byteAt bb 12).val*256^12 + (byteAt bb 13).val*256^13 + (byteAt bb 14).val*256^14 + (byteAt bb 15).val*256^15 = ((Word.toBitVec64 input.b).signExtend 128).toNat := by
      rw [hbb_def, extendedBytes_toNat input.b cols.b_lower_byte cols.b_sign_extend hb_low, signExtend128_toNat input.b hbU]
      congr 1
      rw [hbse_eq, hb_msb]
      split_ifs with hge
      · rw [one_mul, show (255 : ZMod p) = ((255 : ℕ) : ZMod p) from by norm_cast,
            ZMod.val_natCast_of_lt (show (255:ℕ) < p from by have := Fact.out (p := 2 ^ 24 < p); omega)]
        norm_num
      · simp
    have hScc : (byteAt cc 0).val + (byteAt cc 1).val*256^1 + (byteAt cc 2).val*256^2 + (byteAt cc 3).val*256^3 + (byteAt cc 4).val*256^4 + (byteAt cc 5).val*256^5 + (byteAt cc 6).val*256^6 + (byteAt cc 7).val*256^7 + (byteAt cc 8).val*256^8 + (byteAt cc 9).val*256^9 + (byteAt cc 10).val*256^10 + (byteAt cc 11).val*256^11 + (byteAt cc 12).val*256^12 + (byteAt cc 13).val*256^13 + (byteAt cc 14).val*256^14 + (byteAt cc 15).val*256^15 = Word.toNat input.c := by
      rw [hcc_def, extendedBytes_toNat input.c cols.c_lower_byte cols.c_sign_extend hc_low, hcse0]; simp
    have hClt : Word.toNat input.c < 2 ^ 128 := by
      obtain ⟨a,b,c,d⟩ := Word.lt_cases_of_isU64 hcU; rw [Word.toNat_def]; omega
    rw [hrw, ← ofNat128_signExtend input.b, ← ofNat128_eq_setWidth input.c hcU]
    exact high_half_eq cols bb cc _ (Word.toNat input.c) hbb_lt hcc_lt h_chain h_pbyte h_carry (BitVec.isLt _) hClt hSbb hScc
  · intro hmulw
    have hsum1 : input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1 :=
      sum_eq_one hmul_b hmh_b hmhu_b hmhsu_b hmw_b hsum (Or.inr (Or.inr (Or.inr (Or.inr hmulw))))
    have hsum' : input.is_mulw + input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu = 1 := by linear_combination hsum1
    obtain ⟨hmul0, hmh0, hmhu0, hmhsu0⟩ := rest_zero hmul_b hmh_b hmhu_b hmhsu_b hmulw hsum'
    have hbse0 : cols.b_sign_extend = 0 := by rw [h_bse, hmh0, hmhsu0]; ring
    have hcse0 : cols.c_sign_extend = 0 := by rw [h_cse, hmh0]; ring
    have hrw : resultWord input cols = #v[productVal cols 0 + productVal cols 1 * 256, productVal cols 2 + productVal cols 3 * 256, cols.product_msb.msb * 65535, cols.product_msb.msb * 65535] := by
      unfold resultWord; rw [if_pos hmulw]
    have hSbb : (byteAt bb 0).val + (byteAt bb 1).val*256^1 + (byteAt bb 2).val*256^2 + (byteAt bb 3).val*256^3 + (byteAt bb 4).val*256^4 + (byteAt bb 5).val*256^5 + (byteAt bb 6).val*256^6 + (byteAt bb 7).val*256^7 + (byteAt bb 8).val*256^8 + (byteAt bb 9).val*256^9 + (byteAt bb 10).val*256^10 + (byteAt bb 11).val*256^11 + (byteAt bb 12).val*256^12 + (byteAt bb 13).val*256^13 + (byteAt bb 14).val*256^14 + (byteAt bb 15).val*256^15 = Word.toNat input.b := by
      rw [hbb_def, extendedBytes_toNat input.b cols.b_lower_byte cols.b_sign_extend hb_low, hbse0]; simp
    have hScc : (byteAt cc 0).val + (byteAt cc 1).val*256^1 + (byteAt cc 2).val*256^2 + (byteAt cc 3).val*256^3 + (byteAt cc 4).val*256^4 + (byteAt cc 5).val*256^5 + (byteAt cc 6).val*256^6 + (byteAt cc 7).val*256^7 + (byteAt cc 8).val*256^8 + (byteAt cc 9).val*256^9 + (byteAt cc 10).val*256^10 + (byteAt cc 11).val*256^11 + (byteAt cc 12).val*256^12 + (byteAt cc 13).val*256^13 + (byteAt cc 14).val*256^14 + (byteAt cc 15).val*256^15 = Word.toNat input.c := by
      rw [hcc_def, extendedBytes_toNat input.c cols.c_lower_byte cols.c_sign_extend hc_low, hcse0]; simp
    have hreasm := product_reassembly cols bb cc hbb_lt hcc_lt h_chain h_pbyte h_carry
    rw [hSbb, hScc] at hreasm
    have pv2 : productVal cols 2 = cols.product[2] := by simp [productVal]
    have pv3 : productVal cols 3 = cols.product[3] := by simp [productVal]
    have hmsb' : cols.product_msb.msb = if (productVal cols 2 + productVal cols 3 * 256).val ≥ 32768 then 1 else 0 := by
      rw [pv2, pv3]; exact hmsb hmulw
    rw [hrw]
    refine toBitVec64_signExtend_word _ ((Word.toBitVec64 input.b * Word.toBitVec64 input.c).setWidth 32) cols.product_msb.msb ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
      exact hbp _ _ (h_pbyte 0 (by norm_num)) (h_pbyte 1 (by norm_num))
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exact hbp _ _ (h_pbyte 2 (by norm_num)) (h_pbyte 3 (by norm_num))
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]; exact hmsb'
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · rw [BitVec.toNat_setWidth, BitVec.toNat_mul, Word.toBitVec64_toNat hbU, Word.toBitVec64_toNat hcU]
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [byte_compose_val (h_pbyte 0 (by norm_num)) (h_pbyte 1 (by norm_num)) rfl,
          byte_compose_val (h_pbyte 2 (by norm_num)) (h_pbyte 3 (by norm_num)) rfl]
      have q0 := h_pbyte 0 (by norm_num)
      have q1 := h_pbyte 1 (by norm_num)
      have q2 := h_pbyte 2 (by norm_num)
      have q3 := h_pbyte 3 (by norm_num)
      have q4 := h_pbyte 4 (by norm_num)
      have q5 := h_pbyte 5 (by norm_num)
      have q6 := h_pbyte 6 (by norm_num)
      have q7 := h_pbyte 7 (by norm_num)
      have q8 := h_pbyte 8 (by norm_num)
      have q9 := h_pbyte 9 (by norm_num)
      have q10 := h_pbyte 10 (by norm_num)
      have q11 := h_pbyte 11 (by norm_num)
      have q12 := h_pbyte 12 (by norm_num)
      have q13 := h_pbyte 13 (by norm_num)
      have q14 := h_pbyte 14 (by norm_num)
      have q15 := h_pbyte 15 (by norm_num)
      omega


end SP1Clean.MulOperation
