import SP1Foundations.Field

/-! # Carry-chain witness construction (`ℕ`-level core)

The genuine-completeness blocker for `MulOperation` (and the backward
direction of `MulOperation.iff_sp1_full`) is a *constructive* 16-byte
carry chain: given the byte-level cross-products `cp i = Σ_{j+k=i} b_j c_k`,
exhibit `product i` / `carry i` byte vectors satisfying the schoolbook
recurrence `product i + 256 * carry i = cp i + carry (i-1)` together with
the range bounds `carry i < 2^16`, `product i < 256`.

This file proves that core *abstractly* over `cp : ℕ → ℕ` (the only
hypothesis being a uniform per-index bound `cp i ≤ 1040400 = 16·255·255`,
the worst case for a 16-term convolution of bytes). The witnessed
`MulOperation` circuit instantiates `cp` with the concrete byte
convolution; `core_mul` (`SP1Operations/.../Constraints.lean`) then
consumes the resulting `product`/`carry` to recover the BitVec product.

Everything here is `ℕ` arithmetic closed by `omega` after `Nat.div_add_mod`
— no field, no `Clean`, no heavy imports. -/

namespace SP1Clean.MulCarryChain

/-- Accumulated partial sum `mₐ` of the schoolbook multiply: at limb `i`
the running value is the cross-product `cp i` plus the carry out of the
previous limb. `carry`/`product` are its `÷ 256` / `% 256` split. -/
def chainM (cp : ℕ → ℕ) : ℕ → ℕ
  | 0 => cp 0
  | (i + 1) => cp (i + 1) + chainM cp i / 256

/-- The carry out of limb `i`. -/
def carry (cp : ℕ → ℕ) (i : ℕ) : ℕ := chainM cp i / 256

/-- The product byte at limb `i`. -/
def product (cp : ℕ → ℕ) (i : ℕ) : ℕ := chainM cp i % 256

/-- Worst-case convolution bound: a 16-term sum of byte products
`≤ 16 · 255 · 255`. -/
abbrev cpBound : ℕ := 1040400

/-- Carry-bound invariant: every carry stays below `2^16` (in fact `≤ 4095`),
proved by induction. The slack (`4095` vs the `< 65536 = 2^16` range check)
is what makes the no-overflow cast to `ZMod p` valid for `p > 2^24`. -/
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
theorem product_lt (cp : ℕ → ℕ) (i : ℕ) : product cp i < 256 := by
  simp only [product]
  exact Nat.mod_lt _ (by omega)

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

The witnessed `MulOperation` circuit's carry-chain gates and range-check
lookups live over `ZMod p`. These cast the `ℕ` facts above into the exact
shapes those obligations need: the gate `product i = cp i (+ carry (i-1))
- carry i * 256` (an additive rearrangement of the recurrence) and the
range fact `(carry i).val < 65536` / `(product i).val < 256`. -/

variable {p : ℕ}

/-- Base carry-chain gate over `ZMod p`. -/
theorem gate_zero (cp : ℕ → ℕ) :
    ((product cp 0 : ℕ) : ZMod p)
      = ((cp 0 : ℕ) : ZMod p) - ((carry cp 0 : ℕ) : ZMod p) * 256 := by
  have h := recurrence_zero cp
  have hc : (((product cp 0 : ℕ) : ZMod p) + 256 * ((carry cp 0 : ℕ) : ZMod p))
      = ((cp 0 : ℕ) : ZMod p) := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h
  linear_combination hc

/-- Step carry-chain gate over `ZMod p`. -/
theorem gate_succ (cp : ℕ → ℕ) (i : ℕ) :
    ((product cp (i + 1) : ℕ) : ZMod p)
      = ((cp (i + 1) : ℕ) : ZMod p) + ((carry cp i : ℕ) : ZMod p)
        - ((carry cp (i + 1) : ℕ) : ZMod p) * 256 := by
  have h := recurrence_succ cp i
  have hc : (((product cp (i + 1) : ℕ) : ZMod p) + 256 * ((carry cp (i + 1) : ℕ) : ZMod p))
      = ((cp (i + 1) : ℕ) : ZMod p) + ((carry cp i : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h
  linear_combination hc

/-- The carry cast into `ZMod p` round-trips through `.val` (no wrap),
giving the `< 65536` range fact the carry lookups need. -/
theorem carry_val [NeZero p] (cp : ℕ → ℕ) (hcp : ∀ i, cp i ≤ cpBound)
    (hp : 65536 < p) (i : ℕ) :
    (((carry cp i : ℕ) : ZMod p)).val = carry cp i := by
  have := carry_lt cp hcp i
  exact ZMod.val_natCast_of_lt (by omega)

/-- The product byte cast into `ZMod p` round-trips through `.val`, giving
the `< 256` range fact the product lookups need. -/
theorem product_val [NeZero p] (cp : ℕ → ℕ) (hp : 256 < p) (i : ℕ) :
    (((product cp i : ℕ) : ZMod p)).val = product cp i := by
  have := product_lt cp i
  exact ZMod.val_natCast_of_lt (by omega)

/-! ## Concrete byte convolution

`cpNat b c k = Σ_{i ≤ k} b i · c (k-i)` is the schoolbook cross-product at
limb `k` over `ℕ`-valued byte streams `b`, `c`. For byte inputs (`≤ 255`)
and `k ≤ 15` it meets the `cpBound` hypothesis of `carry_lt`, so it is the
canonical `cp` to feed the chain. -/

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

end SP1Clean.MulCarryChain
