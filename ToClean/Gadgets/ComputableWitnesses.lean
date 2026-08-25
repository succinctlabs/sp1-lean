import ToClean.Circuit.WitgenBridge
import Clean.Gadgets.Bits
import Clean.Gadgets.And.And8
import Clean.Gadgets.Or.Or8

/-! # `ComputableWitnesses` for the Clean gadgets an AIR provider composes

Clean's gadget library carries exactly one `ComputableWitnesses` instance in tree
(`Gadgets/Addition8/Addition8FullCarry.lean`). Every other gadget states its `completeness` only —
"any environment consistent with my generators satisfies my constraints" — which is enough to
compose a circuit but not to *build* a row: an AIR trace-generation argument needs the environment
Clean's array-backed interpreter actually produces, and `Circuit.witgen_usesLocalWitnesses` is
gated on `ComputableWitnesses`.

This file supplies the missing instances for the three gadgets a byte/range table provider
composes. All three are honest for the same reason — their witness generators are witness-IR terms
over the input expressions alone — so each proof is the input-agreement hypothesis pushed through
one `Witgen` evaluation step:

* `Gadgets.ToBits.toBits` — one `witnessVector n (x.bits n)`, then boolean asserts and one equality
  subcircuit, neither of which declares a cell;
* `Gadgets.ToBits.rangeCheck` — the `FormalAssertion` wrapper around `toBits`, dispatched by
  `forAll_witnessCongr_of_generalSubcircuit`;
* `Gadgets.And.And8` / `Gadgets.Or.Or8` — one witnessed result cell computed from the two operand
  cells, with the correctness constraint carried by a static `ByteXorTable` lookup (a lookup
  declares no cells, so it contributes nothing here).

## Upstream

Destined for the gadget files themselves — `computableWitnesses` beside each gadget's `circuit`,
mirroring `Addition8FullCarry`'s. Declared here in the gadgets' own namespaces so acceptance is a
deletion plus dropping the import. Nothing in this file changes an existing Clean declaration; the
three composition lemmas it cites are in `ToClean/Circuit/WitgenBridge.lean`. -/

namespace Gadgets.ToBits

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- `toBits` has computable witnesses: its one witness operation is the bit decomposition of the
input expression, so an environment agreeing on the input agrees on every declared bit. The two
tails — the per-bit boolean assertions (a `forEach` of zero-witness assertions) and the closing
equality subcircuit — declare no cells at all. -/
theorem toBits_computableWitnesses [Fact (p > 2)] (n : ℕ) (hn : 2 ^ n < p) :
    (toBits n hn (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [toBits, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _ h_in => ?_,
    Operations.forAllFlat_witnessCongr_of_localLength_zero _ _ (by simp [circuit_norm]),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm])⟩
  simp only [Witgen.WitgenIR.eval, Witgen.VExpr.eval, Witgen.FExpr.eval, h_in]

/-- `rangeCheck` has computable witnesses: it is the assertion wrapper around `toBits`, whose own
`ComputableWitnesses` dispatches the single composed subcircuit. -/
theorem rangeCheck_computableWitnesses [Fact (p > 2)] (n : ℕ) (hn : 2 ^ n < p) :
    (rangeCheck n hn (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [rangeCheck, circuit_norm, Operations.forAllFlat, Operations.forAll]
  exact FlatOperation.forAll_witnessCongr_of_generalSubcircuit _ _ _
    (toBits_computableWitnesses n hn) fun h => by simpa [circuit_norm] using h

end Gadgets.ToBits

namespace Gadgets.And.And8

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- `And8` has computable witnesses: its single cell is `x &&& y` over the two input cells, and the
`ByteXorTable` lookup that certifies it declares none. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨fun _ h_in => ?_, trivial, trivial⟩
  have hx : Expression.eval env.toEnvironment input.x
      = Expression.eval env'.toEnvironment input.x := by
    simpa [circuit_norm] using congrArg Inputs.x h_in
  have hy : Expression.eval env.toEnvironment input.y
      = Expression.eval env'.toEnvironment input.y := by
    simpa [circuit_norm] using congrArg Inputs.y h_in
  simp only [Witgen.WitgenIR.eval_ofFExpr, Witgen.FExpr.eval, Witgen.U64Expr.eval, hx, hy]

end Gadgets.And.And8

namespace Gadgets.Or.Or8

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- `Or8` has computable witnesses — the `And8` argument verbatim, at `|||`. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨fun _ h_in => ?_, trivial, trivial⟩
  have hx : Expression.eval env.toEnvironment input.x
      = Expression.eval env'.toEnvironment input.x := by
    simpa [circuit_norm] using congrArg Inputs.x h_in
  have hy : Expression.eval env.toEnvironment input.y
      = Expression.eval env'.toEnvironment input.y := by
    simpa [circuit_norm] using congrArg Inputs.y h_in
  simp only [Witgen.WitgenIR.eval_ofFExpr, Witgen.FExpr.eval, Witgen.U64Expr.eval, hx, hy]

end Gadgets.Or.Or8
