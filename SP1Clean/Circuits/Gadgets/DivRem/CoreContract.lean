module

public import SP1Clean.Semantics.Specs.DivRem
public import SP1Clean.Circuits.Gadgets.Mul.Arithmetic
public import SP1Clean.Circuits.Gadgets.DivRem.Assertions

/-! # DivRem product-cluster evidence

Contracts for the bundled `DivRemCore.circuit`: product placement, selection, ranges and the
intermediate raw assertion evidence used by the case proofs. Raw assertions are implementation
evidence; the independent public contract is `DivRemContract.RowSpec`.
-/

@[expose] public section

namespace SP1Clean.DivRemCore

/-- The DivRem row's own assertZero tail, **as evaluated field equations**: every entry of the
`DivRemChip.ownAsserts` chain (the `[E13…E367, adapter.op_a_0]` list, whose carrier-generic body is
here instantiated at `R = ZMod p`) is zero on the committed row.

This is the `DivRemCore` contract's one **deliberately-raw** component: it is exactly the content
the `assertZeros (ownAsserts cols)` block of the gadget's `main` contributes to `h_holds` (each
constraint expression evaluates to `0`), transported to the evaluated row by
`DivRemCore.ownAsserts_map_eval` (`Proofs/Operations/DivRemOperation/Core.lean`). Per the
semantic-not-structural principle the 121 equations are *not* restated semantically here — their
semantic form IS the chip-level evidence layer (`Proofs/Chips/DivRemChip/{Soundness,Cases}.lean`),
which extracts each needed equation by list membership. The selection facts a consumer most often
needs (`is_real`/flag binariness, the one-hot sum, `SelectionSpec`) are already derived out of this
bundle into `CoreSpec`'s explicit conjuncts. -/
def OwnAssertsHold {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  ∀ x ∈ DivRemChip.ownAsserts cols, x = 0

/-- The two bundled Mul contracts, each carrying the actual committed result word. Product
placement is proved inside MulOperation and is not duplicated in the DivRem contract. This cluster
stays folded at chip boundaries so generated witness blocks remain opaque. -/
def ProductSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  let lo := cols.c_times_quotient_lower
  let up := cols.c_times_quotient_upper
  MulOperation.Spec
    ⟨cols.quotient_comp, cols.c, lo, cols.is_real, cols.is_real, 0, 0, 0, 0,
      #v[cols.c_times_quotient[0], cols.c_times_quotient[1],
        cols.c_times_quotient[2], cols.c_times_quotient[3]]⟩ ∧
  MulOperation.Spec
    ⟨cols.quotient_comp, cols.c, up, cols.is_real_not_word, 0,
     cols.is_div + cols.is_rem, cols.is_divu + cols.is_remu, 0, 0,
     #v[cols.c_times_quotient[4], cols.c_times_quotient[5],
       cols.c_times_quotient[6], cols.c_times_quotient[7]]⟩

/-- Binary gates, the ungated one-hot equation, and the resulting unique committed instruction
selection. -/
def SelectionEvidenceSpec {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  (cols.is_real_not_word = 0 ∨ cols.is_real_not_word = 1) ∧
  (cols.is_div = 0 ∨ cols.is_div = 1) ∧ (cols.is_divu = 0 ∨ cols.is_divu = 1) ∧
  (cols.is_rem = 0 ∨ cols.is_rem = 1) ∧ (cols.is_remu = 0 ∨ cols.is_remu = 1) ∧
  (cols.is_divw = 0 ∨ cols.is_divw = 1) ∧ (cols.is_remw = 0 ∨ cols.is_remw = 1) ∧
  (cols.is_divuw = 0 ∨ cols.is_divuw = 1) ∧ (cols.is_remuw = 0 ∨ cols.is_remuw = 1) ∧
  (cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem
    + cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1) ∧
  DivRemContract.SelectionSpec cols.is_real cols

/-- The core's 32 byte-table range facts exposed semantically as `< 2^16` bounds. -/
def RangeSpec {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  let rn := cols.rem_neg * 65535
  cols.is_real = 1 →
    (cols.c_times_quotient[0] + cols.remainder_comp[0]
      - cols.carry[0] * 65536).val < 2 ^ 16 ∧
    (cols.c_times_quotient[1] + cols.remainder_comp[1]
      - cols.carry[1] * 65536 + cols.carry[0]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[2] + cols.remainder_comp[2]
      - cols.carry[2] * 65536 + cols.carry[1]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[3] + cols.remainder_comp[3]
      - cols.carry[3] * 65536 + cols.carry[2]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[4] + rn - cols.carry[4] * 65536 + cols.carry[3]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[5] + rn - cols.carry[5] * 65536 + cols.carry[4]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[6] + rn - cols.carry[6] * 65536 + cols.carry[5]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[7] + rn - cols.carry[7] * 65536 + cols.carry[6]).val < 2 ^ 16 ∧
    (∀ i (_ : i < 4), cols.abs_c[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.abs_remainder[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.quotient[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.remainder[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 8), cols.c_times_quotient[i].val < 2 ^ 16)

/-- The arithmetic core's auditable contract, split into four independently folded clusters:
products, the exact raw Rust assertion tail, selection, and byte ranges. -/
def CoreSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)] (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  ProductSpec cols ∧ OwnAssertsHold cols ∧ SelectionEvidenceSpec cols ∧ RangeSpec cols

end SP1Clean.DivRemCore
