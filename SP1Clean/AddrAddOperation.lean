import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.AddrAddOperation

/-! # `AddrAddOperation` gadget mirror — Spec + iff_sp1 only

SP1's `AddrAddOperation` is the address-computation carry-chain used by
Load and Store chips: a 4-limb add `a + b` whose result fits in the
3-limb `cols.value` (the high 4th limb is constrained to be 0, since
SP1 addresses are 48-bit). Same shape as `AddOperation` (inverse-form
boolean carries + result-limb byte bounds), with the 4th carry forced
to absorb a zero high limb.

This mirror packages SP1's `allHold_constraints_iff` RHS as
`SP1Clean.AddrAddOp.Spec`, with `iff_sp1` a one-line re-export. Lets
the chip-level `SpecForIff` defs in
`LoadByte/LoadHalf/LoadWord/LoadDoubleChip.lean` and
`StoreHalf/StoreWord/StoreDoubleChip.lean` drop their inline
`(AddrAddOperation.constraints …).allHold` clauses for a named
predicate.

No `main` or `Assertion` bundle yet — those depend on Clean's
subcircuit DSL and add ~50 LoC of `ProvableStruct` plumbing.
Deferred to a follow-up iter; this minimal mirror is enough to clean
up the 10 chip SpecForIff defs that consume the operation today.
-/

namespace SP1Clean.AddrAddOp

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Pilot Spec, matching SP1's `AddrAddOperation.allHold_constraints_iff`
RHS verbatim under `is_real = 1`. The carry chain is the same as
`AddOperation.Spec` but the 4th carry uses `0` as the high limb of
the result word (`cols.value` is 3 limbs since SP1 addresses are
48-bit), and there is no 4th result-limb bound. -/
def Spec (a b : Word (ZMod p)) (cols : _root_.AddrAddOperation (ZMod p)) : Prop :=
  let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
  let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  (carry2 = 0 ∨ carry2 = 1) ∧
  (carry3 = 0 ∨ carry3 = 1) ∧
  cols.value[0].val < 65536 ∧
  cols.value[1].val < 65536 ∧
  cols.value[2].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`AddrAddOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : _root_.AddrAddOperation (ZMod p)) :
    (_root_.AddrAddOperation.constraints a b cols 1).allHold ↔
      Spec a b cols :=
  _root_.AddrAddOperation.allHold_constraints_iff a b cols

end SP1Clean.AddrAddOp
