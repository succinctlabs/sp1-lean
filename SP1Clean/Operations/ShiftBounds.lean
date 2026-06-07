import SP1Clean.Foundations.Word
import Mathlib.Tactic

/-! # Shared arithmetic bounds for the shift `within_byte` lemmas

Factored-out `.val`-bridge and bound lemmas common to the four `srl_within_byte_shift*`
(`Chips/ShiftRightChip/Core.lean`) and `sll_within_byte_shift*` (`Chips/ShiftLeftChip/Core.lean`)
variants. Proving each fact **once** on a small context — rather than inline by `nlinarith` per
limb, per variant (~100 calls total across both files) — collapses the call sites to
`exact`/one-liners and runs `nlinarith` only a handful of times. This is the compile-time win
documented in `docs/agents/compile-profile.md` thread B.

Every lemma is generic over the byte-decomposition radices `M`, `N` with `M * N = 65536`
(the within-byte split of a 16-bit limb). -/

namespace SP1Clean.ShiftBounds
open SP1Clean

variable {p : ℕ} [Fact (2 ^ 17 < p)]

/-- `M * N = 65536 ⟹ 0 < N` (a zero factor would make the product zero). -/
lemma N_pos {M N : ℕ} (h_MN : M * N = 65536) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h, Nat.mul_zero] at h_MN; omega
  · exact h

/-- `M * N = 65536 ⟹ N < p` (since `N ≤ 65536 < 2^17 < p`). -/
lemma N_lt_p {M N : ℕ} (h_MN : M * N = 65536) : N < p := by
  have hp : 2 ^ 17 < p := Fact.out
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, Nat.zero_mul] at h_MN; omega
    · exact h
  have hN : N ≤ 65536 := by nlinarith [h_MN, hM]
  have h17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
  omega

/-- Product `.val` bridge: `(a * v).val = a.val * M` when `v.val = M` and `a.val < N`. -/
lemma mul_v_val {M N : ℕ} {a v : ZMod p} (h_MN : M * N = 65536)
    (h_v : v.val = M) (h_a : a.val < N) : (a * v).val = a.val * M := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  rw [ZMod.val_mul_of_lt, h_v]
  rw [h_v]; nlinarith [h_a, h_MN]

/-- Product `.val` bridge: `(a * ↑N).val = a.val * N` when `a.val < M`. -/
lemma mul_N_val {M N : ℕ} {a : ZMod p} (h_MN : M * N = 65536)
    (h_a : a.val < M) : (a * ((N : ℕ) : ZMod p)).val = a.val * N := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_NM : N * M = 65536 := by rw [Nat.mul_comm]; exact h_MN
  have h_N_val : ((N : ℕ) : ZMod p).val = N := ZMod.val_natCast_of_lt (N_lt_p h_MN)
  rw [ZMod.val_mul_of_lt, h_N_val]
  rw [h_N_val]; nlinarith [h_a, h_MN, h_NM]

/-- High·low recombination `.val`: `(hl * ↑N + ll).val = hl.val * N + ll.val`. -/
lemma hi_lo_val {M N : ℕ} {hl ll : ZMod p} (h_MN : M * N = 65536)
    (h_hl : hl.val < M) (h_ll : ll.val < N) :
    (hl * ((N : ℕ) : ZMod p) + ll).val = hl.val * N + ll.val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_NM : N * M = 65536 := by rw [Nat.mul_comm]; exact h_MN
  have h_mul := mul_N_val (a := hl) h_MN h_hl
  rw [ZMod.val_add_of_lt]
  · rw [h_mul]
  · rw [h_mul]; nlinarith [h_ll, h_hl, h_MN, h_NM]

/-- Low·high recombination `.val`: `(hl + ll * v).val = hl.val + ll.val * M`. -/
lemma lo_hi_val {M N : ℕ} {hl ll v : ZMod p} (h_MN : M * N = 65536)
    (h_v : v.val = M) (h_hl : hl.val < M) (h_ll : ll.val < N) :
    (hl + ll * v).val = hl.val + ll.val * M := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_mul := mul_v_val h_MN h_v h_ll
  rw [ZMod.val_add_of_lt]
  · rw [h_mul]
  · rw [h_mul]; nlinarith [h_hl, h_ll, h_MN]

/-- Low·high recombination `.val`, product-first: `(ll * v + hl).val = ll.val * M + hl.val`.
The `ShiftLeftCore` limb order (product then carry-in), vs. `lo_hi_val`'s `hl + ll * v`. -/
lemma mul_v_add_val {M N : ℕ} {hl ll v : ZMod p} (h_MN : M * N = 65536)
    (h_v : v.val = M) (h_ll : ll.val < N) (h_hl : hl.val < M) :
    (ll * v + hl).val = ll.val * M + hl.val := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  have h_mul := mul_v_val h_MN h_v h_ll
  rw [ZMod.val_add_of_lt]
  · rw [h_mul]
  · rw [h_mul]; nlinarith [h_hl, h_ll, h_MN]

/-- `a < M → b < N → a * N + b < 65536`. -/
lemma hi_lo_lt {M N a b : ℕ} (h_MN : M * N = 65536) (ha : a < M) (hb : b < N) :
    a * N + b < 65536 := by nlinarith [ha, hb, h_MN]

/-- `a < M → b < N → a + b * M < 65536`. -/
lemma lo_hi_lt {M N a b : ℕ} (h_MN : M * N = 65536) (ha : a < M) (hb : b < N) :
    a + b * M < 65536 := by nlinarith [ha, hb, h_MN]

/-- `a < M → a < 65536` (since `M ≤ M * N = 65536`). -/
lemma lt_65536_of_lt_M {M N a : ℕ} (h_MN : M * N = 65536) (ha : a < M) : a < 65536 := by
  have hN : 0 < N := N_pos (M := M) h_MN
  have hM : M ≤ 65536 := by nlinarith [h_MN, hN]
  omega

end SP1Clean.ShiftBounds
