import SP1Clean.Math.Word
import Mathlib.Tactic

/-! # Shared `.val`-bridge and bound lemmas for the shift within-byte proofs

Common to `srl_within_byte_shift*` (`Proofs/Chips/ShiftRightChip/Core.lean`) and
`sll_within_byte_shift*` (`Proofs/Chips/ShiftLeftChip/Core.lean`). Proving each fact once collapses
the ~100 `nlinarith` call sites to `exact`/one-liners (compile-time win; see
`docs/snapshots/compile-profile.md` thread B).

Every lemma is generic over byte-decomposition radices `M`, `N` with `M * N = 65536`. -/

namespace SP1Clean.ShiftBounds
open SP1Clean

variable {p : ℕ} [Fact (2 ^ 17 < p)]

/-- A factor of `65536` is at most `65536`. -/
private lemma factor_le {M N : ℕ} (h_MN : M * N = 65536) : M ≤ 65536 :=
  Nat.le_of_dvd (by norm_num) ⟨N, h_MN.symm⟩

/-- `M * N = 65536 ⟹ 0 < N` (a zero factor would make the product zero). -/
lemma N_pos {M N : ℕ} (h_MN : M * N = 65536) : 0 < N :=
  Nat.pos_of_ne_zero fun h => by simp [h] at h_MN

/-- `M * N = 65536 ⟹ N < p` (since `N ≤ 65536 < 2^17 < p`). -/
lemma N_lt_p {M N : ℕ} (h_MN : M * N = 65536) : N < p := by
  have hp : 2 ^ 17 < p := Fact.out
  have hN : N ≤ 65536 := factor_le (by rw [Nat.mul_comm]; exact h_MN)
  have h17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
  omega

/-- Product `.val` bridge: `(a * v).val = a.val * M` when `v.val = M` and `a.val < N`. -/
lemma mul_v_val {M N : ℕ} {a v : ZMod p} (h_MN : M * N = 65536)
    (h_v : v.val = M) (h_a : a.val < N) : (a * v).val = a.val * M := by
  have hp : 2 ^ 17 < p := Fact.out
  rw [ZMod.val_mul_of_lt, h_v]
  rw [h_v]; nlinarith [h_a, h_MN]

/-- Product `.val` bridge: `(a * ↑N).val = a.val * N` when `a.val < M`. -/
lemma mul_N_val {M N : ℕ} {a : ZMod p} (h_MN : M * N = 65536)
    (h_a : a.val < M) : (a * ((N : ℕ) : ZMod p)).val = a.val * N :=
  mul_v_val (M := N) (N := M) (by rw [Nat.mul_comm]; exact h_MN)
    (ZMod.val_natCast_of_lt (N_lt_p h_MN)) h_a

/-- Low·high recombination `.val`: `(hl + ll * v).val = hl.val + ll.val * M`. -/
lemma lo_hi_val {M N : ℕ} {hl ll v : ZMod p} (h_MN : M * N = 65536)
    (h_v : v.val = M) (h_hl : hl.val < M) (h_ll : ll.val < N) :
    (hl + ll * v).val = hl.val + ll.val * M := by
  have hp : 2 ^ 17 < p := Fact.out
  have h_mul := mul_v_val h_MN h_v h_ll
  rw [ZMod.val_add_of_lt]
  · rw [h_mul]
  · rw [h_mul]; nlinarith [h_hl, h_ll, h_MN]

/-- Low·high recombination `.val`, product-first: `(ll * v + hl).val = ll.val * M + hl.val`.
`ShiftLeftCore` limb order (product then carry-in), vs. `lo_hi_val`'s `hl + ll * v`. -/
lemma mul_v_add_val {M N : ℕ} {hl ll v : ZMod p} (h_MN : M * N = 65536)
    (h_v : v.val = M) (h_ll : ll.val < N) (h_hl : hl.val < M) :
    (ll * v + hl).val = ll.val * M + hl.val := by
  rw [add_comm (ll * v) hl, lo_hi_val h_MN h_v h_hl h_ll, Nat.add_comm]

/-- High·low recombination `.val`: `(hl * ↑N + ll).val = hl.val * N + ll.val`. -/
lemma hi_lo_val {M N : ℕ} {hl ll : ZMod p} (h_MN : M * N = 65536)
    (h_hl : hl.val < M) (h_ll : ll.val < N) :
    (hl * ((N : ℕ) : ZMod p) + ll).val = hl.val * N + ll.val :=
  mul_v_add_val (M := N) (N := M) (by rw [Nat.mul_comm]; exact h_MN)
    (ZMod.val_natCast_of_lt (N_lt_p h_MN)) h_hl h_ll

/-- `a < M → b < N → a * N + b < 65536`. -/
lemma hi_lo_lt {M N a b : ℕ} (h_MN : M * N = 65536) (ha : a < M) (hb : b < N) :
    a * N + b < 65536 := by nlinarith [ha, hb, h_MN]

/-- `a < M → b < N → a + b * M < 65536`. -/
lemma lo_hi_lt {M N a b : ℕ} (h_MN : M * N = 65536) (ha : a < M) (hb : b < N) :
    a + b * M < 65536 := by nlinarith [ha, hb, h_MN]

/-- `a < M → a < 65536` (since `M ≤ M * N = 65536`). -/
lemma lt_65536_of_lt_M {M N a : ℕ} (h_MN : M * N = 65536) (ha : a < M) : a < 65536 :=
  lt_of_lt_of_le ha (factor_le h_MN)

end SP1Clean.ShiftBounds
