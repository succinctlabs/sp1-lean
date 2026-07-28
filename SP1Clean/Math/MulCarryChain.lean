import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination

/-! # Carry-chain witness construction (`ℕ`-level core)

The genuine-completeness engine for the witnessed `MulOperation` circuit: given the byte-level
cross-products `cp i = Σ_{j+k=i} b_j c_k`, exhibit `product i` / `carry i` byte vectors satisfying
the schoolbook recurrence `product i + 256 * carry i = cp i + carry (i-1)` together with the range
bounds `carry i < 2^16`, `product i < 256`.

This core is proved *abstractly* over `cp : ℕ → ℕ` (the only hypothesis being a uniform per-index
bound `cp i ≤ 1040400 = 16·255·255`, the worst case for a 16-term convolution of bytes). The
witnessed `MulOperation` circuit instantiates `cp` with the concrete byte convolution (`cpNat`);
`main`'s witness generators and the completeness proof both read off `product`/`carry`.

Everything here is `ℕ` arithmetic closed by `omega` after `Nat.div_add_mod` — no field, no `Clean`,
no heavy imports (plus a couple of `ZMod` casts at the end). -/

namespace SP1Clean.MulCarryChain

/-- Accumulated partial sum of the schoolbook multiply: at limb `i` the running value is the
cross-product `cp i` plus the carry out of the previous limb. `carry`/`product` are its
`÷ 256` / `% 256` split. -/
def chainM (cp : ℕ → ℕ) : ℕ → ℕ
  | 0 => cp 0
  | (i + 1) => cp (i + 1) + chainM cp i / 256

/-- The carry out of limb `i`. -/
def carry (cp : ℕ → ℕ) (i : ℕ) : ℕ := chainM cp i / 256

/-- The product byte at limb `i`. -/
def product (cp : ℕ → ℕ) (i : ℕ) : ℕ := chainM cp i % 256

/-- Worst-case convolution bound: a 16-term sum of byte products `≤ 16 · 255 · 255`. -/
abbrev cpBound : ℕ := 1040400

/-- Carry-bound invariant: every carry stays below `2^16` (in fact `≤ 4095`), proved by induction.
The slack (`4095` vs the `< 65536 = 2^16` range check) is what makes the no-overflow cast to
`ZMod p` valid for `p > 2^24`. -/
theorem carry_le (cp : ℕ → ℕ) (hcp : ∀ i, cp i ≤ cpBound) :
    ∀ i, carry cp i ≤ 4095 := by
  intro i
  induction i with
  | zero =>
    have h0 := hcp 0
    simp only [carry, chainM, cpBound] at h0 ⊢
    omega
  | succ n ih =>
    have hn := hcp (n + 1)
    simp only [carry, chainM, cpBound] at hn ih ⊢
    omega

/-- The product byte is always a genuine byte (`< 256`). -/
theorem product_lt (cp : ℕ → ℕ) (i : ℕ) : product cp i < 256 :=
  Nat.mod_lt _ (by omega)

/-- The carry stays below the `2^16` range-check bound. -/
theorem carry_lt (cp : ℕ → ℕ) (hcp : ∀ i, cp i ≤ cpBound) (i : ℕ) :
    carry cp i < 65536 := by
  have := carry_le cp hcp i; omega

/-- Base recurrence: `product 0 + 256 * carry 0 = cp 0`. -/
theorem recurrence_zero (cp : ℕ → ℕ) :
    product cp 0 + 256 * carry cp 0 = cp 0 := by
  simp only [product, carry, chainM]
  omega

/-- Step recurrence: `product (i+1) + 256 * carry (i+1) = cp (i+1) + carry i`. -/
theorem recurrence_succ (cp : ℕ → ℕ) (i : ℕ) :
    product cp (i + 1) + 256 * carry cp (i + 1) = cp (i + 1) + carry cp i := by
  simp only [product, carry, chainM]
  omega

/-! ## `ZMod p` bridges

The witnessed `MulOperation` circuit's carry-chain gates and range-check lookups live over
`ZMod p`. These cast the `ℕ` facts above into the exact shapes those obligations need: the gate
`product i = cp i (+ carry (i-1)) - carry i * 256` (an additive rearrangement of the recurrence) and
the range facts `(carry i).val < 65536` / `(product i).val < 256`. -/

variable {p : ℕ}

/-- Base carry-chain gate over `ZMod p`. -/
theorem gate_zero (cp : ℕ → ℕ) :
    ((product cp 0 : ℕ) : ZMod p)
      = ((cp 0 : ℕ) : ZMod p) - ((carry cp 0 : ℕ) : ZMod p) * 256 := by
  have hc : (((product cp 0 : ℕ) : ZMod p) + 256 * ((carry cp 0 : ℕ) : ZMod p))
      = ((cp 0 : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) (recurrence_zero cp)
  linear_combination hc

/-- Step carry-chain gate over `ZMod p`. -/
theorem gate_succ (cp : ℕ → ℕ) (i : ℕ) :
    ((product cp (i + 1) : ℕ) : ZMod p)
      = ((cp (i + 1) : ℕ) : ZMod p) + ((carry cp i : ℕ) : ZMod p)
        - ((carry cp (i + 1) : ℕ) : ZMod p) * 256 := by
  have hc : (((product cp (i + 1) : ℕ) : ZMod p) + 256 * ((carry cp (i + 1) : ℕ) : ZMod p))
      = ((cp (i + 1) : ℕ) : ZMod p) + ((carry cp i : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) (recurrence_succ cp i)
  linear_combination hc

/-- The carry cast into `ZMod p` round-trips through `.val` (no wrap), giving the `< 65536` range
fact the carry lookups need. -/
theorem carry_val [NeZero p] (cp : ℕ → ℕ) (hcp : ∀ i, cp i ≤ cpBound)
    (hp : 65536 < p) (i : ℕ) :
    (((carry cp i : ℕ) : ZMod p)).val = carry cp i := by
  have := carry_lt cp hcp i
  exact ZMod.val_natCast_of_lt (by omega)

/-- The product byte cast into `ZMod p` round-trips through `.val`, giving the `< 256` range fact
the product lookups need. -/
theorem product_val [NeZero p] (cp : ℕ → ℕ) (hp : 256 < p) (i : ℕ) :
    (((product cp i : ℕ) : ZMod p)).val = product cp i := by
  have := product_lt cp i
  exact ZMod.val_natCast_of_lt (by omega)

/-! ## Concrete byte convolution

`cpNat b c k = Σ_{i ≤ k} b i · c (k-i)` is the schoolbook cross-product at limb `k` over `ℕ`-valued
byte streams `b`, `c`. For byte inputs (`≤ 255`) and `k ≤ 15` it meets the `cpBound` hypothesis of
`carry_lt`, so it is the canonical `cp` to feed the chain. -/

/-- Byte cross-product at limb `k`. -/
def cpNat (b c : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), b i * c (k - i)

/-- A `(k+1)`-term sum of byte products is `≤ (k+1) · 255²`. -/
theorem cpNat_le (b c : ℕ → ℕ) (k : ℕ) (hb : ∀ i, b i ≤ 255) (hc : ∀ i, c i ≤ 255) :
    cpNat b c k ≤ (k + 1) * 65025 := by
  calc cpNat b c k
      ≤ ∑ _i ∈ Finset.range (k + 1), 65025 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (hb i) (hc (k - i)))
    _ = (k + 1) * 65025 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- For limbs `k ≤ 15`, the byte convolution meets `cpBound = 1040400`. -/
theorem cpNat_le_cpBound (b c : ℕ → ℕ) (k : ℕ) (hk : k ≤ 15)
    (hb : ∀ i, b i ≤ 255) (hc : ∀ i, c i ≤ 255) :
    cpNat b c k ≤ cpBound := by
  have h := cpNat_le b c k hb hc
  have : (k + 1) * 65025 ≤ 16 * 65025 := Nat.mul_le_mul_right _ (by omega)
  simp only [cpBound]; omega

/-- When the left stream `b` has support in `[0,15]` (vanishes past index 15), the byte convolution
meets `cpBound` at *every* limb `k` — not only `k ≤ 15`: at most 16 terms are nonzero (those with
`i ≤ 15`), each a product of two bytes (`≤ 255 · 255`). This is the *total* hypothesis the
carry-chain range lemmas (`carry_lt`/`carry_val`) require. -/
theorem cpNat_le_cpBound_total (b c : ℕ → ℕ) (hb : ∀ i, b i ≤ 255) (hc : ∀ i, c i ≤ 255)
    (hb0 : ∀ i, 16 ≤ i → b i = 0) (k : ℕ) :
    cpNat b c k ≤ cpBound := by
  simp only [cpNat, cpBound]
  calc ∑ i ∈ Finset.range (k + 1), b i * c (k - i)
      = ∑ i ∈ (Finset.range (k + 1)).filter (· < 16), b i * c (k - i) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (k + 1)) (· < 16)]
        have hz : ∑ i ∈ (Finset.range (k + 1)).filter (fun i => ¬ i < 16), b i * c (k - i) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          simp only [Finset.mem_filter, not_lt] at hi
          rw [hb0 i hi.2, zero_mul]
        rw [hz, add_zero]
    _ ≤ ∑ _i ∈ (Finset.range (k + 1)).filter (· < 16), 65025 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (hb i) (hc (k - i)))
    _ = ((Finset.range (k + 1)).filter (· < 16)).card * 65025 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 16 * 65025 := by
        apply Nat.mul_le_mul_right
        calc ((Finset.range (k + 1)).filter (· < 16)).card
            ≤ (Finset.range 16).card := by
              apply Finset.card_le_card; intro i hi
              simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; exact hi.2
          _ = 16 := by simp
    _ = 1040400 := by norm_num

end SP1Clean.MulCarryChain
