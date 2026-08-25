import SP1Clean.Native.Operations.MulOperation.RawSpec

/-! # `MulOperation.populate` — the witness (trace generation), mirroring SP1's
`MulOperation::populate`. -/

namespace SP1Clean.MulOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

def extStream (l0 l1 l2 l3 sgn : ℕ) : ℕ → ℕ := fun i =>
  [l0 % 256, l0 / 256, l1 % 256, l1 / 256, l2 % 256, l2 / 256, l3 % 256, l3 / 256,
   sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255].getD i 0

/-- Witnessed schoolbook product byte `k` of the sign/zero-extended operands. -/
def schoolProduct (b0 b1 b2 b3 c0 c1 c2 c3 bsgn csgn k : ℕ) : ℕ :=
  MulCarryChain.product (MulCarryChain.cpNat (extStream b0 b1 b2 b3 bsgn) (extStream c0 c1 c2 c3 csgn)) k

/-- Witnessed schoolbook column carry `k`. -/
def schoolCarry (b0 b1 b2 b3 c0 c1 c2 c3 bsgn csgn k : ℕ) : ℕ :=
  MulCarryChain.carry (MulCarryChain.cpNat (extStream b0 b1 b2 b3 bsgn) (extStream c0 c1 c2 c3 csgn)) k

/-- The witness assignment (trace generation), mirroring SP1's `MulOperation::populate`
(`operations/mul.rs:66-162`): the 16 schoolbook product bytes + 16 column carries (with the
sign/zero-extended byte streams), the `U16toU8` low-byte decompositions of `b`/`c`, the three MSB
witnesses, and the two sign-extend selectors. The columns depend on the operands and the signed-variant
flags (`is_mulh`/`is_mulhsu`) only — `is_mul`/`is_mulhu`/`is_mulw` affect result *placement*, not the
product columns. The composing chip calls this to fill `cols`; conformance anchors it to SP1's `populate`. -/
def populate (b c : Word (ZMod p)) (is_mulh is_mulhsu is_mulw : ZMod p) :
    Extracted.MulOperation (ZMod p) :=
  let bsgn := (is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)
  let csgn := is_mulh.val * (c[3].val / 32768 % 2)
  let carry : Vector (ZMod p) 16 := Vector.ofFn (fun k : Fin 16 =>
    ((schoolCarry b[0].val b[1].val b[2].val b[3].val c[0].val c[1].val c[2].val c[3].val
      bsgn csgn k.val : ℕ) : ZMod p))
  let product : Vector (ZMod p) 16 := Vector.ofFn (fun k : Fin 16 =>
    ((schoolProduct b[0].val b[1].val b[2].val b[3].val c[0].val c[1].val c[2].val c[3].val
      bsgn csgn k.val : ℕ) : ZMod p))
  let b_msb := U16MSBOperation.populate_msb b[3]
  let c_msb := U16MSBOperation.populate_msb c[3]
  -- `product_msb` is gated on `is_mulw` (SP1 `mul.rs:80-84`: only the MULW variant fills it, the
  -- low-half high u16 `product[2] + product[3]*256` = `limbs[1]` of the signed low-32 product; else 0).
  { carry := carry, product := product,
    b_lower_byte := U16toU8OperationSafe.populate b, c_lower_byte := U16toU8OperationSafe.populate c,
    b_msb := b_msb, c_msb := c_msb,
    product_msb := ⟨if is_mulw = 1 then U16MSBOperation.populate_msb (product[2] + product[3] * 256)
      else 0⟩,
    b_sign_extend := (is_mulh + is_mulhsu) * b_msb, c_sign_extend := is_mulh * c_msb }

/-! ### Witness IR

The exportable twin of `populate` (the campaign's largest single gadget). The schoolbook
recursion is mirrored **structurally**: `chainU` is the authoring-time Lean recursion producing,
at each concrete limb, a closed first-order `U64Expr` — the `MulCarryChain.chainM` shape
verbatim, so the eval lemma is one induction. The convolution `cpF` mirrors `cpNat`'s
`Finset.range` sum as a list fold over the same index order. Everything stays in the u64 sort
(the whole chain is `≤ cpBound + 4095 < 2^21`, far from the wrap); only the sign selectors and
the gated `product_msb` touch the field sort. Deliberately **not** `@[circuit_norm]`. -/

/-- The 16-entry sign/zero-extended byte stream of a word, as u64-sorted IR (the `extStream`
twin): eight operand bytes (`lᵢ % 256`, `lᵢ / 256`) then eight sign-fill bytes (`sgn · 255`). -/
def streamF (w : Word (Expression (ZMod p))) (sgn : Witgen.U64Expr (ZMod p)) (i : ℕ) :
    Witgen.U64Expr (ZMod p) :=
  [w[0].val % 256, w[0].val / 256, w[1].val % 256, w[1].val / 256,
   w[2].val % 256, w[2].val / 256, w[3].val % 256, w[3].val / 256,
   sgn * 255, sgn * 255, sgn * 255, sgn * 255,
   sgn * 255, sgn * 255, sgn * 255, sgn * 255].getD i 0

/-- The `b`-operand sign selector (`(is_mulh.val + is_mulhsu.val) · msb`), u64-sorted. -/
def bsgnF (is_mulh is_mulhsu b3 : Expression (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (Witgen.U64Expr.val (.expr is_mulh) + Witgen.U64Expr.val (.expr is_mulhsu))
    * (Witgen.U64Expr.val (.expr b3) / 32768 % 2)

/-- The `c`-operand sign selector (`is_mulh.val · msb`), u64-sorted. -/
def csgnF (is_mulh c3 : Expression (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  Witgen.U64Expr.val (.expr is_mulh) * (Witgen.U64Expr.val (.expr c3) / 32768 % 2)

/-- The byte cross-product at limb `k` (the `cpNat` twin), as a fold over the same index order. -/
def cpF (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (k : ℕ) : Witgen.U64Expr (ZMod p) :=
  (List.range (k + 1)).foldr (fun i acc => bS i * cS (k - i) + acc) 0

/-- The accumulated schoolbook chain (the `MulCarryChain.chainM` twin, authoring-time recursion
producing closed terms at each concrete limb). -/
def chainF (bS cS : ℕ → Witgen.U64Expr (ZMod p)) : ℕ → Witgen.U64Expr (ZMod p)
  | 0 => cpF bS cS 0
  | i + 1 => cpF bS cS (i + 1) + chainF bS cS i / 256

/-- The witnessed carry cell at limb `k`, as IR. -/
def carryF (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (k : ℕ) : Witgen.FExpr (ZMod p) :=
  (chainF bS cS k / 256).toField

/-- The witnessed product byte at limb `k`, as IR. -/
def productF (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (k : ℕ) : Witgen.FExpr (ZMod p) :=
  (chainF bS cS k % 256).toField

/-- The witness-IR twin of `populate`, over the chip's input expressions (`is_mulh`/`is_mulhsu`/
`is_mulw` are the chip's witnessed flag cells). -/
def populateFE (b c : Word (Expression (ZMod p))) (is_mulh is_mulhsu is_mulw : Expression (ZMod p)) :
    Extracted.MulOperation (Witgen.FExpr (ZMod p)) :=
  let bS := streamF b (bsgnF is_mulh is_mulhsu b[3])
  let cS := streamF c (csgnF is_mulh c[3])
  { carry := Vector.ofFn fun k : Fin 16 => carryF bS cS k.val,
    product := Vector.ofFn fun k : Fin 16 => productF bS cS k.val,
    b_lower_byte := ⟨#v[(b[0].val % 256).toField, (b[1].val % 256).toField,
                        (b[2].val % 256).toField, (b[3].val % 256).toField]⟩,
    c_lower_byte := ⟨#v[(c[0].val % 256).toField, (c[1].val % 256).toField,
                        (c[2].val % 256).toField, (c[3].val % 256).toField]⟩,
    b_msb := U16MSBOperation.populate_msbF (.expr b[3]),
    c_msb := U16MSBOperation.populate_msbF (.expr c[3]),
    product_msb := ⟨.ite (is_mulw =? (1 : ZMod p))
      (U16MSBOperation.populate_msbF
        (productF bS cS 2 + productF bS cS 3 * (256 : Witgen.FExpr (ZMod p))))
      0⟩,
    b_sign_extend := (.expr is_mulh + .expr is_mulhsu) * U16MSBOperation.populate_msbF (.expr b[3]),
    c_sign_extend := .expr is_mulh * U16MSBOperation.populate_msbF (.expr c[3]) }

section EvalLemmas

omit [Fact (2 ^ 24 < p)]

/-- Evaluating the stream twin is `extStream` at the evaluated limbs (per index; indices past the
sixteen entries default to `0` on both sides). The limb bounds keep the u64-sorted `val`s from
wrapping, and `sgn ≤ 1` keeps the sign-fill bytes at `≤ 255`. -/
private lemma streamF_eval (ctx : Witgen.Ctx (ZMod p))
    (w : Word (Expression (ZMod p))) (sgn : Witgen.U64Expr (ZMod p)) (vw : Word (ZMod p))
    (sgnv : ℕ)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval ctx.env.toEnvironment w[i] = vw[i])
    (hU : ∀ (i : ℕ) (_ : i < 4), vw[i].val < 2 ^ 16)
    (hsgn : ((sgn.eval ctx)).toNat = sgnv) (hs1 : sgnv ≤ 1) :
    ∀ i : ℕ, ((streamF w sgn i).eval ctx).toNat
      = extStream vw[0].val vw[1].val vw[2].val vw[3].val sgnv i := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  have u0 := hU 0 (by omega); have u1 := hU 1 (by omega)
  have u2 := hU 2 (by omega); have u3 := hU 3 (by omega)
  intro i
  rcases Nat.lt_or_ge i 16 with hlt | hge
  · interval_cases i <;>
      simp only [streamF, extStream, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, circuit_norm, h0, h1, h2, h3, hsgn]
  · have hs : streamF w sgn i = 0 := by
      simp only [streamF]
      rw [List.getD_eq_default]
      simp
      omega
    have he : extStream vw[0].val vw[1].val vw[2].val vw[3].val sgnv i = 0 := by
      simp only [extStream]
      rw [List.getD_eq_default]
      simp
      omega
    rw [hs, he]
    simp [circuit_norm]

/-- The bounded fold bridge: evaluating the term-level sum fold is the ℕ sum fold, with the
partial-sum bound threaded so every u64 wrap discharges (each term is a byte product `≤ 65025`,
at most sixteen terms). -/
private lemma foldr_eval (ctx : Witgen.Ctx (ZMod p)) (l : List ℕ)
    (f : ℕ → Witgen.U64Expr (ZMod p)) (g : ℕ → ℕ)
    (hf : ∀ i ∈ l, ((f i).eval ctx).toNat = g i) (hb : ∀ i ∈ l, g i ≤ 65025)
    (hlen : l.length ≤ 16) :
    ((l.foldr (fun i acc => f i + acc) (0 : Witgen.U64Expr (ZMod p))).eval ctx).toNat
        = l.foldr (fun i acc => g i + acc) 0 ∧
      l.foldr (fun i acc => g i + acc) 0 ≤ l.length * 65025 := by
  induction l with
  | nil => simp [circuit_norm]
  | cons hd tl ih =>
    obtain ⟨ihEq, ihLe⟩ := ih (fun i hi => hf i (List.mem_cons_of_mem hd hi))
      (fun i hi => hb i (List.mem_cons_of_mem hd hi))
      (le_trans (by simp) hlen)
    have hhd := hf hd (List.mem_cons_self ..)
    have hhdb := hb hd (List.mem_cons_self ..)
    have hlen' : tl.length ≤ 15 := by
      have := hlen
      simp only [List.length_cons] at this
      omega
    constructor
    · have ihEq' := ihEq
      simp only [Witgen.U64Expr.add_def] at ihEq'
      simp only [List.foldr_cons, Witgen.U64Expr.add_def, Witgen.U64Expr.eval,
        UInt64.toNat_add, hhd, ihEq']
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [List.foldr_cons, List.length_cons]
      omega

/-- Additive fold with a nonzero initial value splits off the initial value. -/
private lemma foldr_add_init (g : ℕ → ℕ) (l : List ℕ) (a : ℕ) :
    l.foldr (fun i acc => g i + acc) a = l.foldr (fun i acc => g i + acc) 0 + a := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp only [List.foldr_cons, ih]; omega

/-- A `Finset.range` sum is the corresponding `List.range` fold (the bridge between `cpNat`'s
spelling and the term-level fold). -/
private lemma sum_range_eq_foldr (g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range n, g i = (List.range n).foldr (fun i acc => g i + acc) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.foldr_append, ih]
    simp only [List.foldr_cons, List.foldr_nil]
    conv_rhs => rw [foldr_add_init]
    omega

/-- Evaluating the convolution twin is `cpNat` at the evaluated streams (for `k < 16`). -/
private lemma cpF_eval (ctx : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (bv cv : ℕ → ℕ)
    (hbS : ∀ i : ℕ, ((bS i).eval ctx).toNat = bv i)
    (hcS : ∀ i : ℕ, ((cS i).eval ctx).toNat = cv i)
    (hbb : ∀ i : ℕ, bv i ≤ 255) (hcb : ∀ i : ℕ, cv i ≤ 255) (k : ℕ) (hk : k < 16) :
    ((cpF bS cS k).eval ctx).toNat = MulCarryChain.cpNat bv cv k := by
  have hfold := foldr_eval ctx (List.range (k + 1)) (fun i => bS i * cS (k - i))
    (fun i => bv i * cv (k - i))
    (fun i _ => by
      have hprod : bv i * cv (k - i) ≤ 65025 := Nat.mul_le_mul (hbb i) (hcb (k - i))
      simp only [Witgen.U64Expr.eval, UInt64.toNat_mul, hbS i, hcS (k - i)]
      exact Nat.mod_eq_of_lt (by omega))
    (fun i _ => Nat.mul_le_mul (hbb i) (hcb (k - i)))
    (by simp; omega)
  rw [MulCarryChain.cpNat, sum_range_eq_foldr]
  exact hfold.1

/-- The accumulated chain is bounded, needing `cp` bounds only at the limbs it touches (the
convolution grows past limb 15, but the chain never looks there): each step is
`cp + previous/256 ≤ cpBound + (cpBound + 4095)/256 ≤ cpBound + 4095`. -/
private lemma chainM_le (cp : ℕ → ℕ) (n : ℕ)
    (hcp : ∀ i, i ≤ n → cp i ≤ MulCarryChain.cpBound) :
    MulCarryChain.chainM cp n ≤ MulCarryChain.cpBound + 4095 := by
  induction n with
  | zero =>
    have := hcp 0 (le_refl 0)
    simp only [MulCarryChain.chainM, MulCarryChain.cpBound] at this ⊢
    omega
  | succ m ih =>
    have h1 := hcp (m + 1) (le_refl _)
    have h2 := ih fun i hi => hcp i (by omega)
    simp only [MulCarryChain.chainM, MulCarryChain.cpBound] at h1 h2 ⊢
    omega

/-- Evaluating the chain twin is `chainM` at the evaluated streams (induction over the limb; the
chain stays below `2^21`, so no u64 wrap fires). -/
private lemma chainF_eval (ctx : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (bv cv : ℕ → ℕ)
    (hbS : ∀ i : ℕ, ((bS i).eval ctx).toNat = bv i)
    (hcS : ∀ i : ℕ, ((cS i).eval ctx).toNat = cv i)
    (hbb : ∀ i : ℕ, bv i ≤ 255) (hcb : ∀ i : ℕ, cv i ≤ 255) :
    ∀ (k : ℕ), k < 16 → ((chainF bS cS k).eval ctx).toNat
      = MulCarryChain.chainM (MulCarryChain.cpNat bv cv) k := by
  have hcp : ∀ i, i ≤ 15 → MulCarryChain.cpNat bv cv i ≤ MulCarryChain.cpBound := fun i hi => by
    have h := MulCarryChain.cpNat_le bv cv i hbb hcb
    have h16 : (i + 1) * 65025 ≤ 16 * 65025 := Nat.mul_le_mul_right _ (by omega)
    simp only [MulCarryChain.cpBound]
    omega
  intro k
  induction k with
  | zero =>
    intro hk
    simp only [chainF, MulCarryChain.chainM]
    exact cpF_eval ctx bS cS bv cv hbS hcS hbb hcb 0 (by omega)
  | succ n ihn =>
    intro hk
    have hcpn := cpF_eval ctx bS cS bv cv hbS hcS hbb hcb (n + 1) hk
    have hprev := ihn (by omega)
    have hchle := chainM_le (MulCarryChain.cpNat bv cv) n fun i hi => hcp i (by omega)
    have hcpb := hcp (n + 1) (by omega)
    simp only [chainF, MulCarryChain.chainM, Witgen.U64Expr.add_def,
      Witgen.U64Expr.div_def, Witgen.U64Expr.eval, UInt64.toNat_add, UInt64.toNat_div,
      UInt64.toNat_ofNat, hcpn, hprev]
    rw [Nat.mod_eq_of_lt (show (256 : ℕ) < 2 ^ 64 by omega)]
    simp only [MulCarryChain.cpBound] at hcpb hchle
    exact Nat.mod_eq_of_lt (by omega)

/-- Evaluating a carry cell is the witnessed `schoolCarry`-shaped cast. -/
private lemma carryF_eval (ctx : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (bv cv : ℕ → ℕ)
    (hbS : ∀ i : ℕ, ((bS i).eval ctx).toNat = bv i)
    (hcS : ∀ i : ℕ, ((cS i).eval ctx).toNat = cv i)
    (hbb : ∀ i : ℕ, bv i ≤ 255) (hcb : ∀ i : ℕ, cv i ≤ 255) (k : ℕ) (hk : k < 16) :
    (carryF bS cS k).eval ctx
      = ((MulCarryChain.carry (MulCarryChain.cpNat bv cv) k : ℕ) : ZMod p) := by
  have hch := chainF_eval ctx bS cS bv cv hbS hcS hbb hcb k hk
  simp only [carryF, MulCarryChain.carry, Witgen.U64Expr.div_def,
    Witgen.U64Expr.toField, Witgen.FExpr.eval, Witgen.U64Expr.eval, UInt64.toNat_div,
    UInt64.toNat_ofNat, hch, FiniteField.fromNat_F]

/-- Evaluating a product cell is the witnessed `schoolProduct`-shaped cast. -/
private lemma productF_eval (ctx : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p)) (bv cv : ℕ → ℕ)
    (hbS : ∀ i : ℕ, ((bS i).eval ctx).toNat = bv i)
    (hcS : ∀ i : ℕ, ((cS i).eval ctx).toNat = cv i)
    (hbb : ∀ i : ℕ, bv i ≤ 255) (hcb : ∀ i : ℕ, cv i ≤ 255) (k : ℕ) (hk : k < 16) :
    (productF bS cS k).eval ctx
      = ((MulCarryChain.product (MulCarryChain.cpNat bv cv) k : ℕ) : ZMod p) := by
  have hch := chainF_eval ctx bS cS bv cv hbS hcS hbb hcb k hk
  simp only [productF, MulCarryChain.product, Witgen.U64Expr.mod_def,
    Witgen.U64Expr.toField, Witgen.FExpr.eval, Witgen.U64Expr.eval, UInt64.toNat_mod,
    UInt64.toNat_ofNat, hch, FiniteField.fromNat_F]

/-- Evaluating the `b` sign selector is `populate`'s `bsgn` (the flag binarities keep the u64
`val`s from wrapping and give `bsgn ≤ 1`; the limb bound feeds the msb split). -/
private lemma bsgnF_eval (ctx : Witgen.Ctx (ZMod p)) (is_mulh is_mulhsu b3 : Expression (ZMod p))
    (vh vhsu v3 : ZMod p)
    (hh : Expression.eval ctx.env.toEnvironment is_mulh = vh)
    (hhsu : Expression.eval ctx.env.toEnvironment is_mulhsu = vhsu)
    (h3 : Expression.eval ctx.env.toEnvironment b3 = v3)
    (hhb : vh = 0 ∨ vh = 1) (hhsub : vhsu = 0 ∨ vhsu = 1) (h3b : v3.val < 65536) :
    ((bsgnF is_mulh is_mulhsu b3).eval ctx).toNat
      = (vh.val + vhsu.val) * (v3.val / 32768 % 2) := by
  have hh1 : vh.val ≤ 1 := by
    rcases hhb with h | h <;> subst h
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
  have hhsu1 : vhsu.val ≤ 1 := by
    rcases hhsub with h | h <;> subst h
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
  simp only [bsgnF, Witgen.U64Expr.add_def, Witgen.U64Expr.mul_def,
    Witgen.U64Expr.div_def, Witgen.U64Expr.mod_def, Witgen.U64Expr.eval,
    Witgen.FExpr.eval, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat, hh, hhsu, h3, FiniteField.val_F]
  have e1 : vh.val % 2 ^ 64 = vh.val := Nat.mod_eq_of_lt (by omega)
  have e2 : vhsu.val % 2 ^ 64 = vhsu.val := Nat.mod_eq_of_lt (by omega)
  have e3 : v3.val % 2 ^ 64 = v3.val := Nat.mod_eq_of_lt (by omega)
  have e4 : (32768 : ℕ) % 2 ^ 64 = 32768 := Nat.mod_eq_of_lt (by norm_num)
  have e5 : (2 : ℕ) % 2 ^ 64 = 2 := Nat.mod_eq_of_lt (by norm_num)
  rw [e1, e2, e3, e4, e5, Nat.mod_eq_of_lt (show vh.val + vhsu.val < 2 ^ 64 by omega)]
  have hm : v3.val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  exact Nat.mod_eq_of_lt (by
    have := Nat.mul_le_mul (show vh.val + vhsu.val ≤ 2 by omega) hm
    omega)

/-- Evaluating the `c` sign selector is `populate`'s `csgn`. -/
private lemma csgnF_eval (ctx : Witgen.Ctx (ZMod p)) (is_mulh c3 : Expression (ZMod p))
    (vh v3 : ZMod p)
    (hh : Expression.eval ctx.env.toEnvironment is_mulh = vh)
    (h3 : Expression.eval ctx.env.toEnvironment c3 = v3)
    (hhb : vh = 0 ∨ vh = 1) (h3b : v3.val < 65536) :
    ((csgnF is_mulh c3).eval ctx).toNat = vh.val * (v3.val / 32768 % 2) := by
  have hh1 : vh.val ≤ 1 := by
    rcases hhb with h | h <;> subst h
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
  simp only [csgnF, Witgen.U64Expr.mul_def,
    Witgen.U64Expr.div_def, Witgen.U64Expr.mod_def, Witgen.U64Expr.eval,
    Witgen.FExpr.eval, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat, hh, h3, FiniteField.val_F]
  have e1 : vh.val % 2 ^ 64 = vh.val := Nat.mod_eq_of_lt (by omega)
  have e3 : v3.val % 2 ^ 64 = v3.val := Nat.mod_eq_of_lt (by omega)
  have e4 : (32768 : ℕ) % 2 ^ 64 = 32768 := Nat.mod_eq_of_lt (by norm_num)
  have e5 : (2 : ℕ) % 2 ^ 64 = 2 := Nat.mod_eq_of_lt (by norm_num)
  rw [e1, e3, e4, e5]
  have hm : v3.val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  exact Nat.mod_eq_of_lt (by
    have := Nat.mul_le_mul hh1 hm
    omega)

/-- Every entry of the sign/zero-extended byte stream is a byte (given 16-bit limbs and a
binary sign). -/
private lemma extStream_le {l0 l1 l2 l3 sgn : ℕ} (h0 : l0 < 65536) (h1 : l1 < 65536)
    (h2 : l2 < 65536) (h3 : l3 < 65536) (hs : sgn ≤ 1) (i : ℕ) :
    extStream l0 l1 l2 l3 sgn i ≤ 255 := by
  rcases Nat.lt_or_ge i 16 with hlt | hge
  · interval_cases i <;>
      (simp only [extStream, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some]
       omega)
  · rw [show extStream l0 l1 l2 l3 sgn i = [l0 % 256, l0 / 256, l1 % 256, l1 / 256, l2 % 256,
        l2 / 256, l3 % 256, l3 / 256, sgn * 255, sgn * 255, sgn * 255, sgn * 255, sgn * 255,
        sgn * 255, sgn * 255, sgn * 255].getD i 0 from rfl, List.getD_eq_default]
    · omega
    · simpa using hge

end EvalLemmas

section Navigators

/-! The per-cell `toElements` projections over an *opaque* struct (the `toElements_result_byte`
technique): destructure, then literal-index `getElem` append/cast chains — never `whnf` through
the `combinedSize'` tower on a compound literal. Cell order: carry 0–15, product 16–31,
`b_lower_byte` 32–35, `c_lower_byte` 36–39, `b_msb` 40, `c_msb` 41, `product_msb` 42,
`b_sign_extend` 43, `c_sign_extend` 44. -/

set_option linter.unusedSectionVars false in
/-- Cell `k` (`k < 16`) of a flattened `MulOperation` struct is the `k`-th carry. -/
private lemma toElements_cell_carry {F : Type} (s : Extracted.MulOperation F)
    (k : ℕ) (hk : k < 16) :
    (toElements s)[k]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.carry[k] := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     exact Vector.getElem_append_left (by decide))

set_option linter.unusedSectionVars false in
/-- Cell `16 + k` (`k < 16`) is the `k`-th product byte. -/
private lemma toElements_cell_product {F : Type} (s : Extracted.MulOperation F)
    (k : ℕ) (hk : k < 16) :
    (toElements s)[16 + k]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.product[k] := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `32 + k` (`k < 4`) is the `k`-th `b` low byte. -/
private lemma toElements_cell_bLower {F : Type} (s : Extracted.MulOperation F)
    (k : ℕ) (hk : k < 4) :
    (toElements s)[32 + k]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.b_lower_byte.low_bytes[k] := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_left ?_).trans
           ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `36 + k` (`k < 4`) is the `k`-th `c` low byte. -/
private lemma toElements_cell_cLower {F : Type} (s : Extracted.MulOperation F)
    (k : ℕ) (hk : k < 4) :
    (toElements s)[36 + k]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.c_lower_byte.low_bytes[k] := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_right ?_ ?_).trans
           ((Vector.getElem_append_left ?_).trans
             ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_))))) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `40` is the `b` MSB. -/
private lemma toElements_cell_bMsb {F : Type} (s : Extracted.MulOperation F) :
    (toElements s)[40]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.b_msb := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          (Vector.getElem_append_left ?_)))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `41` is the `c` MSB. -/
private lemma toElements_cell_cMsb {F : Type} (s : Extracted.MulOperation F) :
    (toElements s)[41]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.c_msb := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          ((Vector.getElem_append_right ?_ ?_).trans
            (Vector.getElem_append_left ?_))))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `42` is the gated product MSB. -/
private lemma toElements_cell_productMsb {F : Type} (s : Extracted.MulOperation F) :
    (toElements s)[42]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.product_msb.msb := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          ((Vector.getElem_append_right ?_ ?_).trans
            ((Vector.getElem_append_right ?_ ?_).trans
              ((Vector.getElem_append_left ?_).trans
                ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))))))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `43` is the `b` sign-extend selector. -/
private lemma toElements_cell_bSignExtend {F : Type} (s : Extracted.MulOperation F) :
    (toElements s)[43]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.b_sign_extend := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          ((Vector.getElem_append_right ?_ ?_).trans
            ((Vector.getElem_append_right ?_ ?_).trans
              ((Vector.getElem_append_right ?_ ?_).trans
                (Vector.getElem_append_left ?_))))))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `44` is the `c` sign-extend selector. -/
private lemma toElements_cell_cSignExtend {F : Type} (s : Extracted.MulOperation F) :
    (toElements s)[44]'(by have h45 : size Extracted.MulOperation = 45 := rfl; omega)
      = s.c_sign_extend := by
  obtain ⟨ca, pr, ⟨bl⟩, ⟨cl⟩, bm, cm, ⟨pm⟩, bs, cs⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          ((Vector.getElem_append_right ?_ ?_).trans
            ((Vector.getElem_append_right ?_ ?_).trans
              ((Vector.getElem_append_right ?_ ?_).trans
                ((Vector.getElem_append_right ?_ ?_).trans
                  (Vector.getElem_append_left ?_)))))))) <;> decide

end Navigators

section StructEval

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating a low-byte cell (`(e.val % 256).toField`) is the witnessed byte cast. -/
private lemma lowByteFE_eval (env : ProverEnvironment (ZMod p))
    (e : Expression (ZMod p)) (v : ZMod p)
    (he : Expression.eval env.toEnvironment e = v) (hv : v.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField) = ((v.val % 256 : ℕ) : ZMod p) := by
  simp only [circuit_norm, he]

/-- Whole-struct evaluation: the witness IR evaluates to `populate` (with the evaluated words and
flags abstracted). The `isU64` bounds keep the u64-sorted byte streams from wrapping; the flag
binarities plus the one-hot sum bound keep the sign selectors binary (SP1's `is_mulh`/`is_mulhsu`
are mutually exclusive opcode flags). -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (is_mulh is_mulhsu is_mulw : Expression (ZMod p))
    (vb vc : Word (ZMod p)) (vh vhsu vw : ZMod p)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvc : #v[Expression.eval env.toEnvironment c[0], Expression.eval env.toEnvironment c[1],
              Expression.eval env.toEnvironment c[2], Expression.eval env.toEnvironment c[3]] = vc)
    (hh : Expression.eval env.toEnvironment is_mulh = vh)
    (hhsu : Expression.eval env.toEnvironment is_mulhsu = vhsu)
    (hw : Expression.eval env.toEnvironment is_mulw = vw)
    (hb : vb.isU64) (hc : vc.isU64)
    (hhb : vh = 0 ∨ vh = 1) (hhsub : vhsu = 0 ∨ vhsu = 1)
    (hsum : vh.val + vhsu.val ≤ 1) :
    Witgen.eval { env := env } (populateFE b c is_mulh is_mulhsu is_mulw)
      = populate vb vc vh vhsu vw := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hc
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  have hC : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment c[i] = vc[i] := by
    intro i h; rw [← hvc]; interval_cases i <;> simp
  have hbU : ∀ (i : ℕ) (_ : i < 4), vb[i].val < 2 ^ 16 := by
    intro i hi; interval_cases i; exacts [hb0, hb1, hb2, hb3]
  have hcU : ∀ (i : ℕ) (_ : i < 4), vc[i].val < 2 ^ 16 := by
    intro i hi; interval_cases i; exacts [hc0, hc1, hc2, hc3]
  -- the two sign-selector values and their binarity
  have hbsgn := bsgnF_eval { env := env } is_mulh is_mulhsu b[3] vh vhsu vb[3]
    hh hhsu (hB 3 (by omega)) hhb hhsub hb3
  have hcsgn := csgnF_eval { env := env } is_mulh c[3] vh vc[3]
    hh (hC 3 (by omega)) hhb hc3
  have hbsgnb : ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) ≤ 1 := by
    have hm : vb[3].val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
    simpa using Nat.mul_le_mul hsum hm
  have hcsgnb : (vh.val * (vc[3].val / 32768 % 2)) ≤ 1 := by
    have hm : vc[3].val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
    have h1 : vh.val ≤ 1 := le_trans (Nat.le_add_right _ _) hsum
    simpa using Nat.mul_le_mul h1 hm
  -- the evaluated byte streams and their byte bounds
  have hbS := streamF_eval { env := env } b (bsgnF is_mulh is_mulhsu b[3]) vb
    ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) hB hbU hbsgn hbsgnb
  have hcS := streamF_eval { env := env } c (csgnF is_mulh c[3]) vc
    (vh.val * (vc[3].val / 32768 % 2)) hC hcU hcsgn hcsgnb
  have hbb := extStream_le hb0 hb1 hb2 hb3 hbsgnb
  have hcb := extStream_le hc0 hc1 hc2 hc3 hcsgnb
  -- the schoolbook cells
  have hcar : ∀ (k : ℕ), k < 16 →
      Witgen.FExpr.eval { env := env } (carryF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) k)
        = ((schoolCarry vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) k : ℕ) : ZMod p) :=
    fun k hk => carryF_eval { env := env } _ _ _ _ hbS hcS hbb hcb k hk
  have hprod : ∀ (k : ℕ), k < 16 →
      Witgen.FExpr.eval { env := env } (productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) k)
        = ((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) k : ℕ) : ZMod p) :=
    fun k hk => productF_eval { env := env } _ _ _ _ hbS hcS hbb hcb k hk
  -- the three MSB / sign-extend cells
  have hexprB3 : Witgen.FExpr.eval { env := env } (Witgen.FExpr.expr b[3]) = vb[3] := by
    simp only [circuit_norm, hB 3 (by omega)]
  have hexprC3 : Witgen.FExpr.eval { env := env } (Witgen.FExpr.expr c[3]) = vc[3] := by
    simp only [circuit_norm, hC 3 (by omega)]
  have hbmsb : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF (.expr b[3]))
      = U16MSBOperation.populate_msb vb[3] := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hexprB3]; exact hb3),
      hexprB3]
  have hcmsb : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF (.expr c[3]))
      = U16MSBOperation.populate_msb vc[3] := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hexprC3]; exact hc3),
      hexprC3]
  have hbse : Witgen.FExpr.eval { env := env }
      ((Witgen.FExpr.expr is_mulh + Witgen.FExpr.expr is_mulhsu)
        * U16MSBOperation.populate_msbF (.expr b[3]))
      = (vh + vhsu) * U16MSBOperation.populate_msb vb[3] := by
    simp only [circuit_norm, hh, hhsu, hbmsb]
  have hcse : Witgen.FExpr.eval { env := env }
      (Witgen.FExpr.expr is_mulh * U16MSBOperation.populate_msbF (.expr c[3]))
      = vh * U16MSBOperation.populate_msb vc[3] := by
    simp only [circuit_norm, hh, hcmsb]
  -- the gated product-MSB cell
  have hsp2b : schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 ≤ 255 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hsp3b : schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 ≤ 255 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hp23 : Witgen.FExpr.eval { env := env }
      (productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) 2 + productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) 3 * (256 : Witgen.FExpr (ZMod p)))
      = ((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 + schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 * 256 : ℕ) : ZMod p) := by
    simp only [circuit_norm, hprod 2 (by omega), hprod 3 (by omega)]
    push_cast
    ring
  have hvalb : (((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 + schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 * 256 : ℕ) : ZMod p)).val < 2 ^ 16 := by
    rw [ZMod.val_natCast_of_lt (by have hp : 2 ^ 24 < p := Fact.out; omega)]
    omega
  have hpm : Witgen.FExpr.eval { env := env }
      (U16MSBOperation.populate_msbF
        (productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) 2 + productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) 3 * (256 : Witgen.FExpr (ZMod p))))
      = U16MSBOperation.populate_msb
          (((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 + schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 * 256 : ℕ) : ZMod p)) := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hp23]; exact hvalb), hp23]
  -- cell-by-cell assembly
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi45 : i < 45 := by
    have hsz : size Extracted.MulOperation = 45 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFE b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements, Vector.getElem_map]
  interval_cases i
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 0 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 0 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 0 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 1 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 1 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 1 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 2 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 2 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 2 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 3 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 3 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 3 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 4 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 4 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 4 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 5 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 5 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 5 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 6 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 6 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 6 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 7 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 7 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 7 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 8 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 8 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 8 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 9 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 9 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 9 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 10 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 10 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 10 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 11 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 11 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 11 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 12 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 12 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 12 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 13 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 13 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 13 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 14 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 14 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 14 (by omega)
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 15 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 15 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hcar 15 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 0 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 0 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 0 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 1 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 1 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 1 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 2 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 2 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 2 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 3 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 3 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 3 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 4 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 4 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 4 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 5 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 5 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 5 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 6 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 6 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 6 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 7 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 7 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 7 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 8 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 8 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 8 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 9 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 9 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 9 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 10 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 10 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 10 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 11 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 11 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 11 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 12 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 12 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 12 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 13 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 13 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 13 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 14 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 14 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 14 (by omega)
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 15 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 15 (by omega)]
    simp only [populateFE, populate, Vector.getElem_ofFn]
    exact hprod 15 (by omega)
  · exact ((congrArg _ (toElements_cell_bLower _ 0 (by omega))).trans
      (lowByteFE_eval env b[0] vb[0] (hB 0 (by omega)) hb0)).trans
      (toElements_cell_bLower _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLower _ 1 (by omega))).trans
      (lowByteFE_eval env b[1] vb[1] (hB 1 (by omega)) hb1)).trans
      (toElements_cell_bLower _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLower _ 2 (by omega))).trans
      (lowByteFE_eval env b[2] vb[2] (hB 2 (by omega)) hb2)).trans
      (toElements_cell_bLower _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLower _ 3 (by omega))).trans
      (lowByteFE_eval env b[3] vb[3] (hB 3 (by omega)) hb3)).trans
      (toElements_cell_bLower _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 0 (by omega))).trans
      (lowByteFE_eval env c[0] vc[0] (hC 0 (by omega)) hc0)).trans
      (toElements_cell_cLower _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 1 (by omega))).trans
      (lowByteFE_eval env c[1] vc[1] (hC 1 (by omega)) hc1)).trans
      (toElements_cell_cLower _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 2 (by omega))).trans
      (lowByteFE_eval env c[2] vc[2] (hC 2 (by omega)) hc2)).trans
      (toElements_cell_cLower _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 3 (by omega))).trans
      (lowByteFE_eval env c[3] vc[3] (hC 3 (by omega)) hc3)).trans
      (toElements_cell_cLower _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bMsb _)).trans hbmsb).trans
      (toElements_cell_bMsb _).symm
  · exact ((congrArg _ (toElements_cell_cMsb _)).trans hcmsb).trans
      (toElements_cell_cMsb _).symm
  · refine ((congrArg _ (toElements_cell_productMsb _)).trans ?_).trans
      (toElements_cell_productMsb _).symm
    by_cases hvw : vw = 1
    · simp [populateFE, populate, circuit_norm, Vector.getElem_ofFn, hw, hvw]
      exact hpm.trans (congrArg U16MSBOperation.populate_msb (by push_cast; ring))
    · simp [populateFE, populate, circuit_norm, hw, hvw]
  · exact ((congrArg _ (toElements_cell_bSignExtend _)).trans hbse).trans
      (toElements_cell_bSignExtend _).symm
  · exact ((congrArg _ (toElements_cell_cSignExtend _)).trans hcse).trans
      (toElements_cell_cSignExtend _).symm

/-- Elementwise corollary of `populateFE_eval`, in the exact shape the chip completeness seam's
per-cell witness obligations arrive in. -/
theorem populateFE_eval_cell (env : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (is_mulh is_mulhsu is_mulw : Expression (ZMod p))
    (vb vc : Word (ZMod p)) (vh vhsu vw : ZMod p)
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvc : #v[Expression.eval env.toEnvironment c[0], Expression.eval env.toEnvironment c[1],
              Expression.eval env.toEnvironment c[2], Expression.eval env.toEnvironment c[3]] = vc)
    (hh : Expression.eval env.toEnvironment is_mulh = vh)
    (hhsu : Expression.eval env.toEnvironment is_mulhsu = vhsu)
    (hw : Expression.eval env.toEnvironment is_mulw = vw)
    (hb : vb.isU64) (hc : vc.isU64)
    (hhb : vh = 0 ∨ vh = 1) (hhsub : vhsu = 0 ∨ vhsu = 1)
    (hsum : vh.val + vhsu.val ≤ 1) (j : ℕ) (hj : j < 45) :
    Witgen.FExpr.eval { env := env }
        ((toElements (populateFE b c is_mulh is_mulhsu is_mulw))[j]'(by
          have h45 : size Extracted.MulOperation = 45 := rfl
          omega))
      = (toElements (populate vb vc vh vhsu vw))[j]'(by
          have h45 : size Extracted.MulOperation = 45 := rfl
          omega) := by
  have h := congrArg
    (fun s : Extracted.MulOperation (ZMod p) => (toElements s)[j]'(by
      have h45 : size Extracted.MulOperation = 45 := rfl
      omega))
    (populateFE_eval env b c is_mulh is_mulhsu is_mulw vb vc vh vhsu vw
      hvb hvc hh hhsu hw hb hc hhb hhsub hsum)
  rw [show (Witgen.eval { env := env } (populateFE b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFE b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements] at h
  simpa [Vector.getElem_map] using h

end StructEval

section CongrLemmas

omit [Fact (2 ^ 24 < p)]

/-! Environment-locality (the `ComputableWitnesses` counterparts — congruences, so they need no
bounds). One twin per shape, mirroring the eval ladder. -/

/-- `ofFExprs`-of-`toElements` evaluation is the flattened struct evaluation (the raw payload
form the `ComputableWitnesses` obligations quantify over). -/
private lemma ofFExprs_eval_eq (env : ProverEnvironment (ZMod p))
    (xs : Extracted.MulOperation (Witgen.FExpr (ZMod p))) :
    (Witgen.WitgenIR.ofFExprs (toElements xs)).eval env
      = toElements (Witgen.eval { env := env } xs) := by
  rw [show (Witgen.eval { env := env } xs : Extracted.MulOperation (ZMod p))
        = fromElements ((toElements xs).map (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements]
  apply Vector.ext
  intro i hi
  simp [circuit_norm, Vector.getElem_map]

/-- Congruence for a low-byte cell. -/
private lemma lowByteFE_congr (env env' : ProverEnvironment (ZMod p))
    (e : Expression (ZMod p))
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField)
      = Witgen.FExpr.eval { env := env' } ((e.val % 256).toField) := by
  simp only [circuit_norm, -Witgen.u64Wrap, he]

/-- Congruence for the additive byte-product fold. -/
private lemma foldr_congr (ctx ctx' : Witgen.Ctx (ZMod p)) (l : List ℕ)
    (f : ℕ → Witgen.U64Expr (ZMod p))
    (hf : ∀ i ∈ l, (f i).eval ctx = (f i).eval ctx') :
    ((l.foldr (fun i acc => f i + acc) 0).eval ctx)
      = ((l.foldr (fun i acc => f i + acc) 0).eval ctx') := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih fun i hi => hf i (List.mem_cons_of_mem _ hi)
    simp only [Witgen.U64Expr.add_def] at ih'
    simp only [List.foldr_cons, Witgen.U64Expr.add_def, Witgen.U64Expr.eval,
      hf a (List.mem_cons_self ..), ih']

/-- Congruence for the byte stream. -/
private lemma streamF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (w : Word (Expression (ZMod p))) (sgn : Witgen.U64Expr (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval ctx.env.toEnvironment w[i]
      = Expression.eval ctx'.env.toEnvironment w[i])
    (hsgn : sgn.eval ctx = sgn.eval ctx') :
    ∀ i : ℕ, (streamF w sgn i).eval ctx = (streamF w sgn i).eval ctx' := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  intro i
  rcases Nat.lt_or_ge i 16 with hlt | hge
  · interval_cases i <;>
      simp only [streamF, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, circuit_norm, -Witgen.u64Wrap, h0, h1, h2, h3, hsgn]
  · have hs : streamF w sgn i = 0 := by
      simp only [streamF]
      rw [List.getD_eq_default]
      simp
      omega
    rw [hs]
    rfl

/-- Congruence for the byte cross-product. -/
private lemma cpF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p))
    (hbS : ∀ i : ℕ, (bS i).eval ctx = (bS i).eval ctx')
    (hcS : ∀ i : ℕ, (cS i).eval ctx = (cS i).eval ctx') (k : ℕ) :
    (cpF bS cS k).eval ctx = (cpF bS cS k).eval ctx' := by
  simp only [cpF]
  exact foldr_congr ctx ctx' _ _ fun i _ => by
    simp only [Witgen.U64Expr.eval, hbS i, hcS (k - i)]

/-- Congruence for the accumulated chain. -/
private lemma chainF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p))
    (hbS : ∀ i : ℕ, (bS i).eval ctx = (bS i).eval ctx')
    (hcS : ∀ i : ℕ, (cS i).eval ctx = (cS i).eval ctx') (k : ℕ) :
    (chainF bS cS k).eval ctx = (chainF bS cS k).eval ctx' := by
  induction k with
  | zero => exact cpF_congr ctx ctx' bS cS hbS hcS 0
  | succ n ih =>
    simp only [chainF, Witgen.U64Expr.add_def, Witgen.U64Expr.div_def, Witgen.U64Expr.eval,
      cpF_congr ctx ctx' bS cS hbS hcS (n + 1), ih]

/-- Congruence for a carry cell. -/
private lemma carryF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p))
    (hbS : ∀ i : ℕ, (bS i).eval ctx = (bS i).eval ctx')
    (hcS : ∀ i : ℕ, (cS i).eval ctx = (cS i).eval ctx') (k : ℕ) :
    (carryF bS cS k).eval ctx = (carryF bS cS k).eval ctx' := by
  simp only [carryF, Witgen.U64Expr.toField, Witgen.FExpr.eval, Witgen.U64Expr.div_def,
    Witgen.U64Expr.eval, chainF_congr ctx ctx' bS cS hbS hcS k]

/-- Congruence for a product cell. -/
private lemma productF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (bS cS : ℕ → Witgen.U64Expr (ZMod p))
    (hbS : ∀ i : ℕ, (bS i).eval ctx = (bS i).eval ctx')
    (hcS : ∀ i : ℕ, (cS i).eval ctx = (cS i).eval ctx') (k : ℕ) :
    (productF bS cS k).eval ctx = (productF bS cS k).eval ctx' := by
  simp only [productF, Witgen.U64Expr.toField, Witgen.FExpr.eval, Witgen.U64Expr.mod_def,
    Witgen.U64Expr.eval, chainF_congr ctx ctx' bS cS hbS hcS k]

/-- Congruence for the `b` sign selector. -/
private lemma bsgnF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (is_mulh is_mulhsu b3 : Expression (ZMod p))
    (hh : Expression.eval ctx.env.toEnvironment is_mulh
      = Expression.eval ctx'.env.toEnvironment is_mulh)
    (hhsu : Expression.eval ctx.env.toEnvironment is_mulhsu
      = Expression.eval ctx'.env.toEnvironment is_mulhsu)
    (h3 : Expression.eval ctx.env.toEnvironment b3
      = Expression.eval ctx'.env.toEnvironment b3) :
    (bsgnF is_mulh is_mulhsu b3).eval ctx = (bsgnF is_mulh is_mulhsu b3).eval ctx' := by
  simp only [bsgnF, circuit_norm, -Witgen.u64Wrap, hh, hhsu, h3]

/-- Congruence for the `c` sign selector. -/
private lemma csgnF_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (is_mulh c3 : Expression (ZMod p))
    (hh : Expression.eval ctx.env.toEnvironment is_mulh
      = Expression.eval ctx'.env.toEnvironment is_mulh)
    (h3 : Expression.eval ctx.env.toEnvironment c3
      = Expression.eval ctx'.env.toEnvironment c3) :
    (csgnF is_mulh c3).eval ctx = (csgnF is_mulh c3).eval ctx' := by
  simp only [csgnF, circuit_norm, -Witgen.u64Wrap, hh, h3]

/-- Environment-locality of the whole witness payload (the `ComputableWitnesses` counterpart of
`populateFE_eval` — a congruence, so it needs no bounds). -/
theorem populateFE_congr_flat (env env' : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (is_mulh is_mulhsu is_mulw : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment c[i] = Expression.eval env'.toEnvironment c[i])
    (hH : Expression.eval env.toEnvironment is_mulh
      = Expression.eval env'.toEnvironment is_mulh)
    (hHSU : Expression.eval env.toEnvironment is_mulhsu
      = Expression.eval env'.toEnvironment is_mulhsu)
    (hW : Expression.eval env.toEnvironment is_mulw
      = Expression.eval env'.toEnvironment is_mulw) :
    (Witgen.WitgenIR.ofFExprs (toElements (populateFE b c is_mulh is_mulhsu is_mulw))).eval env
      = (Witgen.WitgenIR.ofFExprs
          (toElements (populateFE b c is_mulh is_mulhsu is_mulw))).eval env' := by
  have hbsgnC := bsgnF_congr { env := env } { env := env' } is_mulh is_mulhsu b[3]
    hH hHSU (hB 3 (by omega))
  have hcsgnC := csgnF_congr { env := env } { env := env' } is_mulh c[3]
    hH (hC 3 (by omega))
  have hbSC := streamF_congr { env := env } { env := env' } b
    (bsgnF is_mulh is_mulhsu b[3]) hB hbsgnC
  have hcSC := streamF_congr { env := env } { env := env' } c
    (csgnF is_mulh c[3]) hC hcsgnC
  have hcarC : ∀ k : ℕ, Witgen.FExpr.eval { env := env } (carryF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) k)
      = Witgen.FExpr.eval { env := env' } (carryF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) k) :=
    carryF_congr { env := env } { env := env' } _ _ hbSC hcSC
  have hprodC : ∀ k : ℕ, Witgen.FExpr.eval { env := env } (productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) k)
      = Witgen.FExpr.eval { env := env' } (productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) k) :=
    productF_congr { env := env } { env := env' } _ _ hbSC hcSC
  have hmsbBC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (.expr b[3]) (by simpa [circuit_norm] using hB 3 (by omega))
  have hmsbCC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (.expr c[3]) (by simpa [circuit_norm] using hC 3 (by omega))
  have hpmC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) 2 + productF (streamF b (bsgnF is_mulh is_mulhsu b[3])) (streamF c (csgnF is_mulh c[3])) 3 * (256 : Witgen.FExpr (ZMod p)))
    (by simp only [circuit_norm, -Witgen.u64Wrap, hprodC 2, hprodC 3])
  rw [ofFExprs_eval_eq, ofFExprs_eval_eq]
  refine congrArg toElements ?_
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi45 : i < 45 := by
    have hsz : size Extracted.MulOperation = 45 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFE b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    show (Witgen.eval { env := env' } (populateFE b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFE b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env' })) from rfl,
    ProvableType.toElements_fromElements, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_map]
  interval_cases i
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 0
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 1
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 2
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 3
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 4 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 4
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 5 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 5
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 6 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 6
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 7 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 7
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 8 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 8
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 9 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 9
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 10 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 10
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 11 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 11
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 12 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 12
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 13 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 13
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 14 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 14
  · rw [toElements_cell_carry (populateFE b c is_mulh is_mulhsu is_mulw) 15 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hcarC 15
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 0
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 1
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 2
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 3
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 4 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 4
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 5 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 5
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 6 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 6
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 7 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 7
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 8 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 8
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 9 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 9
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 10 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 10
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 11 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 11
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 12 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 12
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 13 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 13
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 14 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 14
  · rw [toElements_cell_product (populateFE b c is_mulh is_mulhsu is_mulw) 15 (by omega)]
    simp only [populateFE, Vector.getElem_ofFn]
    exact hprodC 15
  · rw [toElements_cell_bLower (populateFE b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    exact lowByteFE_congr env env' b[0] (hB 0 (by omega))
  · rw [toElements_cell_bLower (populateFE b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    exact lowByteFE_congr env env' b[1] (hB 1 (by omega))
  · rw [toElements_cell_bLower (populateFE b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    exact lowByteFE_congr env env' b[2] (hB 2 (by omega))
  · rw [toElements_cell_bLower (populateFE b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    exact lowByteFE_congr env env' b[3] (hB 3 (by omega))
  · rw [toElements_cell_cLower (populateFE b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    exact lowByteFE_congr env env' c[0] (hC 0 (by omega))
  · rw [toElements_cell_cLower (populateFE b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    exact lowByteFE_congr env env' c[1] (hC 1 (by omega))
  · rw [toElements_cell_cLower (populateFE b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    exact lowByteFE_congr env env' c[2] (hC 2 (by omega))
  · rw [toElements_cell_cLower (populateFE b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    exact lowByteFE_congr env env' c[3] (hC 3 (by omega))
  · rw [toElements_cell_bMsb (populateFE b c is_mulh is_mulhsu is_mulw)]
    exact hmsbBC
  · rw [toElements_cell_cMsb (populateFE b c is_mulh is_mulhsu is_mulw)]
    exact hmsbCC
  · rw [toElements_cell_productMsb (populateFE b c is_mulh is_mulhsu is_mulw)]
    simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hW]
    split_ifs
    · exact hpmC
    · rfl
  · rw [toElements_cell_bSignExtend (populateFE b c is_mulh is_mulhsu is_mulw)]
    simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hH, hHSU, hmsbBC]
  · rw [toElements_cell_cSignExtend (populateFE b c is_mulh is_mulhsu is_mulw)]
    simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hH, hmsbCC]

end CongrLemmas

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (`DivRemChip`'s `c_times_quotient_upper` on word rows; padding rows).
`spec_zero` (in `Formal`) discharges the composed assertion's obligation at this value. -/
def zeroCols : Extracted.MulOperation (ZMod p) :=
  { carry := .replicate 16 0, product := .replicate 16 0,
    b_lower_byte := ⟨.replicate 4 0⟩, c_lower_byte := ⟨.replicate 4 0⟩,
    b_msb := 0, c_msb := 0, product_msb := ⟨0⟩,
    b_sign_extend := 0, c_sign_extend := 0 }

section StructFW

/-! ### FExpr-word twins (`populateFEW`)

The same witness-IR layer over **computed** operand words — `Vector (FExpr) 4` cells rather than
input `Expression`s — for composing chips whose Mul structs multiply witnessed intermediate words
(`DivRemChip`'s `c_times_quotient` structs of `quotient_comp × c`). Text-parallel to the
`Expression` layer above; the stream/chain/carry lemmas in between are stream-abstract and shared.
-/

/-- The 16-entry sign/zero-extended byte stream of a word, as u64-sorted IR (the `extStream`
twin): eight operand bytes (`lᵢ % 256`, `lᵢ / 256`) then eight sign-fill bytes (`sgn · 255`). -/
def streamFW (w : Vector (Witgen.FExpr (ZMod p)) 4) (sgn : Witgen.U64Expr (ZMod p)) (i : ℕ) :
    Witgen.U64Expr (ZMod p) :=
  [w[0].val % 256, w[0].val / 256, w[1].val % 256, w[1].val / 256,
   w[2].val % 256, w[2].val / 256, w[3].val % 256, w[3].val / 256,
   sgn * 255, sgn * 255, sgn * 255, sgn * 255,
   sgn * 255, sgn * 255, sgn * 255, sgn * 255].getD i 0

/-- The `b`-operand sign selector (`(is_mulh.val + is_mulhsu.val) · msb`), u64-sorted. -/
def bsgnFW (is_mulh is_mulhsu b3 : Witgen.FExpr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (Witgen.U64Expr.val is_mulh + Witgen.U64Expr.val is_mulhsu)
    * (Witgen.U64Expr.val b3 / 32768 % 2)

/-- The `c`-operand sign selector (`is_mulh.val · msb`), u64-sorted. -/
def csgnFW (is_mulh c3 : Witgen.FExpr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  Witgen.U64Expr.val is_mulh * (Witgen.U64Expr.val c3 / 32768 % 2)

/-- The witness-IR twin of `populate`, over the chip's input expressions (`is_mulh`/`is_mulhsu`/
`is_mulw` are the chip's witnessed flag cells). -/
def populateFEW (b c : Vector (Witgen.FExpr (ZMod p)) 4) (is_mulh is_mulhsu is_mulw : Witgen.FExpr (ZMod p)) :
    Extracted.MulOperation (Witgen.FExpr (ZMod p)) :=
  let bS := streamFW b (bsgnFW is_mulh is_mulhsu b[3])
  let cS := streamFW c (csgnFW is_mulh c[3])
  { carry := Vector.ofFn fun k : Fin 16 => carryF bS cS k.val,
    product := Vector.ofFn fun k : Fin 16 => productF bS cS k.val,
    b_lower_byte := ⟨#v[(b[0].val % 256).toField, (b[1].val % 256).toField,
                        (b[2].val % 256).toField, (b[3].val % 256).toField]⟩,
    c_lower_byte := ⟨#v[(c[0].val % 256).toField, (c[1].val % 256).toField,
                        (c[2].val % 256).toField, (c[3].val % 256).toField]⟩,
    b_msb := U16MSBOperation.populate_msbF b[3],
    c_msb := U16MSBOperation.populate_msbF c[3],
    product_msb := ⟨.ite (is_mulw =? (1 : ZMod p))
      (U16MSBOperation.populate_msbF
        (productF bS cS 2 + productF bS cS 3 * (256 : Witgen.FExpr (ZMod p))))
      0⟩,
    b_sign_extend := (is_mulh + is_mulhsu) * U16MSBOperation.populate_msbF b[3],
    c_sign_extend := is_mulh * U16MSBOperation.populate_msbF c[3] }

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the stream twin is `extStream` at the evaluated limbs (per index; indices past the
sixteen entries default to `0` on both sides). The limb bounds keep the u64-sorted `val`s from
wrapping, and `sgn ≤ 1` keeps the sign-fill bytes at `≤ 255`. -/
private lemma streamFW_eval (ctx : Witgen.Ctx (ZMod p))
    (w : Vector (Witgen.FExpr (ZMod p)) 4) (sgn : Witgen.U64Expr (ZMod p)) (vw : Word (ZMod p))
    (sgnv : ℕ)
    (hW : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval ctx w[i] = vw[i])
    (hU : ∀ (i : ℕ) (_ : i < 4), vw[i].val < 2 ^ 16)
    (hsgn : ((sgn.eval ctx)).toNat = sgnv) (hs1 : sgnv ≤ 1) :
    ∀ i : ℕ, ((streamFW w sgn i).eval ctx).toNat
      = extStream vw[0].val vw[1].val vw[2].val vw[3].val sgnv i := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  have u0 := hU 0 (by omega); have u1 := hU 1 (by omega)
  have u2 := hU 2 (by omega); have u3 := hU 3 (by omega)
  intro i
  rcases Nat.lt_or_ge i 16 with hlt | hge
  · interval_cases i <;>
      simp only [streamFW, extStream, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, circuit_norm, h0, h1, h2, h3, hsgn]
  · have hs : streamFW w sgn i = 0 := by
      simp only [streamFW]
      rw [List.getD_eq_default]
      simp
      omega
    have he : extStream vw[0].val vw[1].val vw[2].val vw[3].val sgnv i = 0 := by
      simp only [extStream]
      rw [List.getD_eq_default]
      simp
      omega
    rw [hs, he]
    simp [circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the `b` sign selector is `populate`'s `bsgn` (the flag binarities keep the u64
`val`s from wrapping and give `bsgn ≤ 1`; the limb bound feeds the msb split). -/
private lemma bsgnFW_eval (ctx : Witgen.Ctx (ZMod p)) (is_mulh is_mulhsu b3 : Witgen.FExpr (ZMod p))
    (vh vhsu v3 : ZMod p)
    (hh : Witgen.FExpr.eval ctx is_mulh = vh)
    (hhsu : Witgen.FExpr.eval ctx is_mulhsu = vhsu)
    (h3 : Witgen.FExpr.eval ctx b3 = v3)
    (hhb : vh = 0 ∨ vh = 1) (hhsub : vhsu = 0 ∨ vhsu = 1) (h3b : v3.val < 65536) :
    ((bsgnFW is_mulh is_mulhsu b3).eval ctx).toNat
      = (vh.val + vhsu.val) * (v3.val / 32768 % 2) := by
  have hh1 : vh.val ≤ 1 := by
    rcases hhb with h | h <;> subst h
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
  have hhsu1 : vhsu.val ≤ 1 := by
    rcases hhsub with h | h <;> subst h
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
  simp only [bsgnFW, Witgen.U64Expr.add_def, Witgen.U64Expr.mul_def,
    Witgen.U64Expr.div_def, Witgen.U64Expr.mod_def, Witgen.U64Expr.eval,
    UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat, hh, hhsu, h3, FiniteField.val_F]
  have e1 : vh.val % 2 ^ 64 = vh.val := Nat.mod_eq_of_lt (by omega)
  have e2 : vhsu.val % 2 ^ 64 = vhsu.val := Nat.mod_eq_of_lt (by omega)
  have e3 : v3.val % 2 ^ 64 = v3.val := Nat.mod_eq_of_lt (by omega)
  have e4 : (32768 : ℕ) % 2 ^ 64 = 32768 := Nat.mod_eq_of_lt (by norm_num)
  have e5 : (2 : ℕ) % 2 ^ 64 = 2 := Nat.mod_eq_of_lt (by norm_num)
  rw [e1, e2, e3, e4, e5, Nat.mod_eq_of_lt (show vh.val + vhsu.val < 2 ^ 64 by omega)]
  have hm : v3.val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  exact Nat.mod_eq_of_lt (by
    have := Nat.mul_le_mul (show vh.val + vhsu.val ≤ 2 by omega) hm
    omega)

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the `c` sign selector is `populate`'s `csgn`. -/
private lemma csgnFW_eval (ctx : Witgen.Ctx (ZMod p)) (is_mulh c3 : Witgen.FExpr (ZMod p))
    (vh v3 : ZMod p)
    (hh : Witgen.FExpr.eval ctx is_mulh = vh)
    (h3 : Witgen.FExpr.eval ctx c3 = v3)
    (hhb : vh = 0 ∨ vh = 1) (h3b : v3.val < 65536) :
    ((csgnFW is_mulh c3).eval ctx).toNat = vh.val * (v3.val / 32768 % 2) := by
  have hh1 : vh.val ≤ 1 := by
    rcases hhb with h | h <;> subst h
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
  simp only [csgnFW, Witgen.U64Expr.mul_def,
    Witgen.U64Expr.div_def, Witgen.U64Expr.mod_def, Witgen.U64Expr.eval,
    UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat, hh, h3, FiniteField.val_F]
  have e1 : vh.val % 2 ^ 64 = vh.val := Nat.mod_eq_of_lt (by omega)
  have e3 : v3.val % 2 ^ 64 = v3.val := Nat.mod_eq_of_lt (by omega)
  have e4 : (32768 : ℕ) % 2 ^ 64 = 32768 := Nat.mod_eq_of_lt (by norm_num)
  have e5 : (2 : ℕ) % 2 ^ 64 = 2 := Nat.mod_eq_of_lt (by norm_num)
  rw [e1, e3, e4, e5]
  have hm : v3.val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  exact Nat.mod_eq_of_lt (by
    have := Nat.mul_le_mul hh1 hm
    omega)

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating a low-byte cell (`(e.val % 256).toField`) is the witnessed byte cast. -/
private lemma lowByteFW_eval (env : ProverEnvironment (ZMod p))
    (e : Witgen.FExpr (ZMod p)) (v : ZMod p)
    (he : Witgen.FExpr.eval { env := env } e = v) (hv : v.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField) = ((v.val % 256 : ℕ) : ZMod p) := by
  simp only [circuit_norm, he]

/-- Whole-struct evaluation: the witness IR evaluates to `populate` (with the evaluated words and
flags abstracted). The `isU64` bounds keep the u64-sorted byte streams from wrapping; the flag
binarities plus the one-hot sum bound keep the sign selectors binary (SP1's `is_mulh`/`is_mulhsu`
are mutually exclusive opcode flags). -/
theorem populateFEWW_eval (env : ProverEnvironment (ZMod p))
    (b c : Vector (Witgen.FExpr (ZMod p)) 4) (is_mulh is_mulhsu is_mulw : Witgen.FExpr (ZMod p))
    (vb vc : Word (ZMod p)) (vh vhsu vw : ZMod p)
    (hvb : #v[Witgen.FExpr.eval { env := env } b[0], Witgen.FExpr.eval { env := env } b[1],
              Witgen.FExpr.eval { env := env } b[2], Witgen.FExpr.eval { env := env } b[3]] = vb)
    (hvc : #v[Witgen.FExpr.eval { env := env } c[0], Witgen.FExpr.eval { env := env } c[1],
              Witgen.FExpr.eval { env := env } c[2], Witgen.FExpr.eval { env := env } c[3]] = vc)
    (hh : Witgen.FExpr.eval { env := env } is_mulh = vh)
    (hhsu : Witgen.FExpr.eval { env := env } is_mulhsu = vhsu)
    (hw : Witgen.FExpr.eval { env := env } is_mulw = vw)
    (hb : vb.isU64) (hc : vc.isU64)
    (hhb : vh = 0 ∨ vh = 1) (hhsub : vhsu = 0 ∨ vhsu = 1)
    (hsum : vh.val + vhsu.val ≤ 1) :
    Witgen.eval { env := env } (populateFEW b c is_mulh is_mulhsu is_mulw)
      = populate vb vc vh vhsu vw := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hc
  have hB : ∀ (i : ℕ) (h : i < 4), Witgen.FExpr.eval { env := env } b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  have hC : ∀ (i : ℕ) (h : i < 4), Witgen.FExpr.eval { env := env } c[i] = vc[i] := by
    intro i h; rw [← hvc]; interval_cases i <;> simp
  have hbU : ∀ (i : ℕ) (_ : i < 4), vb[i].val < 2 ^ 16 := by
    intro i hi; interval_cases i; exacts [hb0, hb1, hb2, hb3]
  have hcU : ∀ (i : ℕ) (_ : i < 4), vc[i].val < 2 ^ 16 := by
    intro i hi; interval_cases i; exacts [hc0, hc1, hc2, hc3]
  -- the two sign-selector values and their binarity
  have hbsgn := bsgnFW_eval { env := env } is_mulh is_mulhsu b[3] vh vhsu vb[3]
    hh hhsu (hB 3 (by omega)) hhb hhsub hb3
  have hcsgn := csgnFW_eval { env := env } is_mulh c[3] vh vc[3]
    hh (hC 3 (by omega)) hhb hc3
  have hbsgnb : ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) ≤ 1 := by
    have hm : vb[3].val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
    simpa using Nat.mul_le_mul hsum hm
  have hcsgnb : (vh.val * (vc[3].val / 32768 % 2)) ≤ 1 := by
    have hm : vc[3].val / 32768 % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
    have h1 : vh.val ≤ 1 := le_trans (Nat.le_add_right _ _) hsum
    simpa using Nat.mul_le_mul h1 hm
  -- the evaluated byte streams and their byte bounds
  have hbS := streamFW_eval { env := env } b (bsgnFW is_mulh is_mulhsu b[3]) vb
    ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) hB hbU hbsgn hbsgnb
  have hcS := streamFW_eval { env := env } c (csgnFW is_mulh c[3]) vc
    (vh.val * (vc[3].val / 32768 % 2)) hC hcU hcsgn hcsgnb
  have hbb := extStream_le hb0 hb1 hb2 hb3 hbsgnb
  have hcb := extStream_le hc0 hc1 hc2 hc3 hcsgnb
  -- the schoolbook cells
  have hcar : ∀ (k : ℕ), k < 16 →
      Witgen.FExpr.eval { env := env } (carryF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) k)
        = ((schoolCarry vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) k : ℕ) : ZMod p) :=
    fun k hk => carryF_eval { env := env } _ _ _ _ hbS hcS hbb hcb k hk
  have hprod : ∀ (k : ℕ), k < 16 →
      Witgen.FExpr.eval { env := env } (productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) k)
        = ((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) k : ℕ) : ZMod p) :=
    fun k hk => productF_eval { env := env } _ _ _ _ hbS hcS hbb hcb k hk
  -- the three MSB / sign-extend cells
  have hexprB3 : Witgen.FExpr.eval { env := env } b[3] = vb[3] := by
    simp only [circuit_norm, hB 3 (by omega)]
  have hexprC3 : Witgen.FExpr.eval { env := env } c[3] = vc[3] := by
    simp only [circuit_norm, hC 3 (by omega)]
  have hbmsb : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF b[3])
      = U16MSBOperation.populate_msb vb[3] := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hexprB3]; exact hb3),
      hexprB3]
  have hcmsb : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF c[3])
      = U16MSBOperation.populate_msb vc[3] := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hexprC3]; exact hc3),
      hexprC3]
  have hbse : Witgen.FExpr.eval { env := env }
      ((is_mulh + is_mulhsu)
        * U16MSBOperation.populate_msbF b[3])
      = (vh + vhsu) * U16MSBOperation.populate_msb vb[3] := by
    simp only [circuit_norm, hh, hhsu, hbmsb]
  have hcse : Witgen.FExpr.eval { env := env }
      (is_mulh * U16MSBOperation.populate_msbF c[3])
      = vh * U16MSBOperation.populate_msb vc[3] := by
    simp only [circuit_norm, hh, hcmsb]
  -- the gated product-MSB cell
  have hsp2b : schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 ≤ 255 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hsp3b : schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 ≤ 255 := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hp23 : Witgen.FExpr.eval { env := env }
      (productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) 2 + productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) 3 * (256 : Witgen.FExpr (ZMod p)))
      = ((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 + schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 * 256 : ℕ) : ZMod p) := by
    simp only [circuit_norm, hprod 2 (by omega), hprod 3 (by omega)]
    push_cast
    ring
  have hvalb : (((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 + schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 * 256 : ℕ) : ZMod p)).val < 2 ^ 16 := by
    rw [ZMod.val_natCast_of_lt (by have hp : 2 ^ 24 < p := Fact.out; omega)]
    omega
  have hpm : Witgen.FExpr.eval { env := env }
      (U16MSBOperation.populate_msbF
        (productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) 2 + productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) 3 * (256 : Witgen.FExpr (ZMod p))))
      = U16MSBOperation.populate_msb
          (((schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 2 + schoolProduct vb[0].val vb[1].val vb[2].val vb[3].val vc[0].val vc[1].val vc[2].val vc[3].val ((vh.val + vhsu.val) * (vb[3].val / 32768 % 2)) (vh.val * (vc[3].val / 32768 % 2)) 3 * 256 : ℕ) : ZMod p)) := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hp23]; exact hvalb), hp23]
  -- cell-by-cell assembly
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi45 : i < 45 := by
    have hsz : size Extracted.MulOperation = 45 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFEW b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFEW b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements, Vector.getElem_map]
  interval_cases i
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 0 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 0 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 0 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 1 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 1 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 1 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 2 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 2 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 2 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 3 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 3 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 3 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 4 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 4 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 4 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 5 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 5 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 5 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 6 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 6 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 6 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 7 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 7 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 7 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 8 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 8 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 8 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 9 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 9 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 9 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 10 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 10 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 10 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 11 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 11 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 11 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 12 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 12 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 12 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 13 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 13 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 13 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 14 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 14 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 14 (by omega)
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 15 (by omega),
      toElements_cell_carry (populate vb vc vh vhsu vw) 15 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hcar 15 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 0 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 0 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 0 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 1 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 1 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 1 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 2 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 2 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 2 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 3 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 3 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 3 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 4 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 4 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 4 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 5 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 5 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 5 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 6 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 6 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 6 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 7 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 7 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 7 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 8 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 8 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 8 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 9 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 9 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 9 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 10 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 10 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 10 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 11 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 11 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 11 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 12 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 12 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 12 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 13 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 13 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 13 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 14 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 14 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 14 (by omega)
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 15 (by omega),
      toElements_cell_product (populate vb vc vh vhsu vw) 15 (by omega)]
    simp only [populateFEW, populate, Vector.getElem_ofFn]
    exact hprod 15 (by omega)
  · exact ((congrArg _ (toElements_cell_bLower _ 0 (by omega))).trans
      (lowByteFW_eval env b[0] vb[0] (hB 0 (by omega)) hb0)).trans
      (toElements_cell_bLower _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLower _ 1 (by omega))).trans
      (lowByteFW_eval env b[1] vb[1] (hB 1 (by omega)) hb1)).trans
      (toElements_cell_bLower _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLower _ 2 (by omega))).trans
      (lowByteFW_eval env b[2] vb[2] (hB 2 (by omega)) hb2)).trans
      (toElements_cell_bLower _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLower _ 3 (by omega))).trans
      (lowByteFW_eval env b[3] vb[3] (hB 3 (by omega)) hb3)).trans
      (toElements_cell_bLower _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 0 (by omega))).trans
      (lowByteFW_eval env c[0] vc[0] (hC 0 (by omega)) hc0)).trans
      (toElements_cell_cLower _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 1 (by omega))).trans
      (lowByteFW_eval env c[1] vc[1] (hC 1 (by omega)) hc1)).trans
      (toElements_cell_cLower _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 2 (by omega))).trans
      (lowByteFW_eval env c[2] vc[2] (hC 2 (by omega)) hc2)).trans
      (toElements_cell_cLower _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLower _ 3 (by omega))).trans
      (lowByteFW_eval env c[3] vc[3] (hC 3 (by omega)) hc3)).trans
      (toElements_cell_cLower _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bMsb _)).trans hbmsb).trans
      (toElements_cell_bMsb _).symm
  · exact ((congrArg _ (toElements_cell_cMsb _)).trans hcmsb).trans
      (toElements_cell_cMsb _).symm
  · refine ((congrArg _ (toElements_cell_productMsb _)).trans ?_).trans
      (toElements_cell_productMsb _).symm
    by_cases hvw : vw = 1
    · simp [populateFEW, populate, circuit_norm, Vector.getElem_ofFn, hw, hvw]
      exact hpm.trans (congrArg U16MSBOperation.populate_msb (by push_cast; ring))
    · simp [populateFEW, populate, circuit_norm, hw, hvw]
  · exact ((congrArg _ (toElements_cell_bSignExtend _)).trans hbse).trans
      (toElements_cell_bSignExtend _).symm
  · exact ((congrArg _ (toElements_cell_cSignExtend _)).trans hcse).trans
      (toElements_cell_cSignExtend _).symm

omit [Fact (2 ^ 24 < p)] in
/-- Congruence for a low-byte cell. -/
private lemma lowByteFW_congr (env env' : ProverEnvironment (ZMod p))
    (e : Witgen.FExpr (ZMod p))
    (he : Witgen.FExpr.eval { env := env } e = Witgen.FExpr.eval { env := env' } e) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField)
      = Witgen.FExpr.eval { env := env' } ((e.val % 256).toField) := by
  simp only [circuit_norm, -Witgen.u64Wrap, he]

omit [Fact (2 ^ 24 < p)] in
/-- Congruence for the byte stream. -/
private lemma streamFW_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (w : Vector (Witgen.FExpr (ZMod p)) 4) (sgn : Witgen.U64Expr (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval ctx w[i]
      = Witgen.FExpr.eval ctx' w[i])
    (hsgn : sgn.eval ctx = sgn.eval ctx') :
    ∀ i : ℕ, (streamFW w sgn i).eval ctx = (streamFW w sgn i).eval ctx' := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  intro i
  rcases Nat.lt_or_ge i 16 with hlt | hge
  · interval_cases i <;>
      simp only [streamFW, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, circuit_norm, -Witgen.u64Wrap, h0, h1, h2, h3, hsgn]
  · have hs : streamFW w sgn i = 0 := by
      simp only [streamFW]
      rw [List.getD_eq_default]
      simp
      omega
    rw [hs]
    rfl

omit [Fact (2 ^ 24 < p)] in
/-- Congruence for the `b` sign selector. -/
private lemma bsgnFW_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (is_mulh is_mulhsu b3 : Witgen.FExpr (ZMod p))
    (hh : Witgen.FExpr.eval ctx is_mulh
      = Witgen.FExpr.eval ctx' is_mulh)
    (hhsu : Witgen.FExpr.eval ctx is_mulhsu
      = Witgen.FExpr.eval ctx' is_mulhsu)
    (h3 : Witgen.FExpr.eval ctx b3
      = Witgen.FExpr.eval ctx' b3) :
    (bsgnFW is_mulh is_mulhsu b3).eval ctx = (bsgnFW is_mulh is_mulhsu b3).eval ctx' := by
  simp only [bsgnFW, circuit_norm, -Witgen.u64Wrap, hh, hhsu, h3]

omit [Fact (2 ^ 24 < p)] in
/-- Congruence for the `c` sign selector. -/
private lemma csgnFW_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (is_mulh c3 : Witgen.FExpr (ZMod p))
    (hh : Witgen.FExpr.eval ctx is_mulh
      = Witgen.FExpr.eval ctx' is_mulh)
    (h3 : Witgen.FExpr.eval ctx c3
      = Witgen.FExpr.eval ctx' c3) :
    (csgnFW is_mulh c3).eval ctx = (csgnFW is_mulh c3).eval ctx' := by
  simp only [csgnFW, circuit_norm, -Witgen.u64Wrap, hh, h3]

omit [Fact (2 ^ 24 < p)] in
/-- Environment-locality of the whole witness payload (the `ComputableWitnesses` counterpart of
`populateFEWW_eval` — a congruence, so it needs no bounds). -/
theorem populateFEW_congr_flat (env env' : ProverEnvironment (ZMod p))
    (b c : Vector (Witgen.FExpr (ZMod p)) 4) (is_mulh is_mulhsu is_mulw : Witgen.FExpr (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } b[i] = Witgen.FExpr.eval { env := env' } b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } c[i] = Witgen.FExpr.eval { env := env' } c[i])
    (hH : Witgen.FExpr.eval { env := env } is_mulh
      = Witgen.FExpr.eval { env := env' } is_mulh)
    (hHSU : Witgen.FExpr.eval { env := env } is_mulhsu
      = Witgen.FExpr.eval { env := env' } is_mulhsu)
    (hW : Witgen.FExpr.eval { env := env } is_mulw
      = Witgen.FExpr.eval { env := env' } is_mulw) :
    (Witgen.WitgenIR.ofFExprs (toElements (populateFEW b c is_mulh is_mulhsu is_mulw))).eval env
      = (Witgen.WitgenIR.ofFExprs
          (toElements (populateFEW b c is_mulh is_mulhsu is_mulw))).eval env' := by
  have hbsgnC := bsgnFW_congr { env := env } { env := env' } is_mulh is_mulhsu b[3]
    hH hHSU (hB 3 (by omega))
  have hcsgnC := csgnFW_congr { env := env } { env := env' } is_mulh c[3]
    hH (hC 3 (by omega))
  have hbSC := streamFW_congr { env := env } { env := env' } b
    (bsgnFW is_mulh is_mulhsu b[3]) hB hbsgnC
  have hcSC := streamFW_congr { env := env } { env := env' } c
    (csgnFW is_mulh c[3]) hC hcsgnC
  have hcarC : ∀ k : ℕ, Witgen.FExpr.eval { env := env } (carryF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) k)
      = Witgen.FExpr.eval { env := env' } (carryF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) k) :=
    carryF_congr { env := env } { env := env' } _ _ hbSC hcSC
  have hprodC : ∀ k : ℕ, Witgen.FExpr.eval { env := env } (productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) k)
      = Witgen.FExpr.eval { env := env' } (productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) k) :=
    productF_congr { env := env } { env := env' } _ _ hbSC hcSC
  have hmsbBC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    b[3] (by simpa [circuit_norm] using hB 3 (by omega))
  have hmsbCC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    c[3] (by simpa [circuit_norm] using hC 3 (by omega))
  have hpmC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) 2 + productF (streamFW b (bsgnFW is_mulh is_mulhsu b[3])) (streamFW c (csgnFW is_mulh c[3])) 3 * (256 : Witgen.FExpr (ZMod p)))
    (by simp only [circuit_norm, -Witgen.u64Wrap, hprodC 2, hprodC 3])
  rw [ofFExprs_eval_eq, ofFExprs_eval_eq]
  refine congrArg toElements ?_
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi45 : i < 45 := by
    have hsz : size Extracted.MulOperation = 45 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFEW b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFEW b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    show (Witgen.eval { env := env' } (populateFEW b c is_mulh is_mulhsu is_mulw) :
          Extracted.MulOperation (ZMod p))
        = fromElements ((toElements (populateFEW b c is_mulh is_mulhsu is_mulw)).map
            (Witgen.FExpr.eval { env := env' })) from rfl,
    ProvableType.toElements_fromElements, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_map]
  interval_cases i
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 0
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 1
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 2
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 3
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 4 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 4
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 5 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 5
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 6 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 6
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 7 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 7
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 8 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 8
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 9 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 9
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 10 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 10
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 11 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 11
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 12 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 12
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 13 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 13
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 14 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 14
  · rw [toElements_cell_carry (populateFEW b c is_mulh is_mulhsu is_mulw) 15 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hcarC 15
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 0
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 1
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 2
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 3
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 4 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 4
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 5 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 5
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 6 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 6
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 7 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 7
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 8 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 8
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 9 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 9
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 10 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 10
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 11 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 11
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 12 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 12
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 13 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 13
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 14 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 14
  · rw [toElements_cell_product (populateFEW b c is_mulh is_mulhsu is_mulw) 15 (by omega)]
    simp only [populateFEW, Vector.getElem_ofFn]
    exact hprodC 15
  · rw [toElements_cell_bLower (populateFEW b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    exact lowByteFW_congr env env' b[0] (hB 0 (by omega))
  · rw [toElements_cell_bLower (populateFEW b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    exact lowByteFW_congr env env' b[1] (hB 1 (by omega))
  · rw [toElements_cell_bLower (populateFEW b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    exact lowByteFW_congr env env' b[2] (hB 2 (by omega))
  · rw [toElements_cell_bLower (populateFEW b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    exact lowByteFW_congr env env' b[3] (hB 3 (by omega))
  · rw [toElements_cell_cLower (populateFEW b c is_mulh is_mulhsu is_mulw) 0 (by omega)]
    exact lowByteFW_congr env env' c[0] (hC 0 (by omega))
  · rw [toElements_cell_cLower (populateFEW b c is_mulh is_mulhsu is_mulw) 1 (by omega)]
    exact lowByteFW_congr env env' c[1] (hC 1 (by omega))
  · rw [toElements_cell_cLower (populateFEW b c is_mulh is_mulhsu is_mulw) 2 (by omega)]
    exact lowByteFW_congr env env' c[2] (hC 2 (by omega))
  · rw [toElements_cell_cLower (populateFEW b c is_mulh is_mulhsu is_mulw) 3 (by omega)]
    exact lowByteFW_congr env env' c[3] (hC 3 (by omega))
  · rw [toElements_cell_bMsb (populateFEW b c is_mulh is_mulhsu is_mulw)]
    exact hmsbBC
  · rw [toElements_cell_cMsb (populateFEW b c is_mulh is_mulhsu is_mulw)]
    exact hmsbCC
  · rw [toElements_cell_productMsb (populateFEW b c is_mulh is_mulhsu is_mulw)]
    simp only [populateFEW, circuit_norm, -Witgen.u64Wrap, hW]
    split_ifs
    · exact hpmC
    · rfl
  · rw [toElements_cell_bSignExtend (populateFEW b c is_mulh is_mulhsu is_mulw)]
    simp only [populateFEW, circuit_norm, -Witgen.u64Wrap, hH, hHSU, hmsbBC]
  · rw [toElements_cell_cSignExtend (populateFEW b c is_mulh is_mulhsu is_mulw)]
    simp only [populateFEW, circuit_norm, -Witgen.u64Wrap, hH, hmsbCC]


end StructFW

section ZeroFlatten

omit [Fact (2 ^ 24 < p)] in
/-- Every flattened cell of `zeroCols` is zero (the gated-composition else-branch fact, via the
navigator family above). -/
lemma zc_cell (i : ℕ) (hi : i < size Extracted.MulOperation) :
    (toElements (zeroCols : Extracted.MulOperation (ZMod p)))[i] = 0 := by
  have hi' : i < 45 := hi
  rcases Nat.lt_or_ge i 16 with h16 | h16
  · rw [toElements_cell_carry (zeroCols : Extracted.MulOperation (ZMod p)) i h16]
    simp [zeroCols]
  rcases Nat.lt_or_ge i 32 with h32 | h32
  · obtain ⟨j, rfl⟩ : ∃ j, i = 16 + j := ⟨i - 16, by omega⟩
    rw [toElements_cell_product (zeroCols : Extracted.MulOperation (ZMod p)) j (by omega)]
    simp [zeroCols]
  rcases Nat.lt_or_ge i 36 with h36 | h36
  · obtain ⟨j, rfl⟩ : ∃ j, i = 32 + j := ⟨i - 32, by omega⟩
    rw [toElements_cell_bLower (zeroCols : Extracted.MulOperation (ZMod p)) j (by omega)]
    simp [zeroCols]
  rcases Nat.lt_or_ge i 40 with h40 | h40
  · obtain ⟨j, rfl⟩ : ∃ j, i = 36 + j := ⟨i - 36, by omega⟩
    rw [toElements_cell_cLower (zeroCols : Extracted.MulOperation (ZMod p)) j (by omega)]
    simp [zeroCols]
  interval_cases i
  · rw [toElements_cell_bMsb]; rfl
  · rw [toElements_cell_cMsb]; rfl
  · rw [toElements_cell_productMsb]; rfl
  · rw [toElements_cell_bSignExtend]; rfl
  · rw [toElements_cell_cSignExtend]; rfl

omit [Fact (2 ^ 24 < p)] in
/-- The flattened zero struct, as a `fromElements` of zeros (the shape `Witgen.eval_gateFE`'s
else branch produces). -/
lemma fromElements_zero :
    (fromElements (Vector.replicate (size Extracted.MulOperation) 0)
      : Extracted.MulOperation (ZMod p)) = zeroCols := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.toElements_fromElements, Vector.getElem_replicate]
  exact (zc_cell i hi).symm

end ZeroFlatten


end SP1Clean.MulOperation
