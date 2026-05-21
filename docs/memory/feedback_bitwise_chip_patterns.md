---
name: Bitwise chip _poly patterns (multi-variant single iff)
description: Tactical patterns from migrating BitwiseChip's 6 arms — single big iff_poly + variant-derivation helpers (sum_eq_one_*, single_op_poly), opcode arg-reduction via push_cast/ring, struct projection unfolding via op-constraint simp set
type: feedback
originSessionId: affe1bb4-3286-4726-b861-93dd84582b22
---
Three patterns specific to chips with **multiple variants sharing one big
allHold_constraints_iff_poly** (Bitwise: 6 arms; Branch will be similar
shape with 6 arms + ITypeReaderImmutable; ShiftRight may apply).

**1. Variant derivation: `sum_eq_one_*` + `single_op_poly` instead of per-variant iff_polys.**

**Why:** When the Fin KB chip has a single shared iff (not per-variant
like Lt's 4-arm decomposition), writing 6 hand-written per-variant
iff_polys is ~6× the work of one shared iff_poly. Better: write one
shared iff_poly + small helper lemmas that derive the variant-specific
facts (off-variant zeros, sum=1) from the iff's bool/sum disjunctions
plus the `is_*_poly` hypothesis.

**How to apply:** For an N-way variant chip, write:
- `sum_eq_one_of_eq_one_{left,mid,right}` (or analogous for N>3) —
  given one column `= 1` and the bool/sum disjunctions, conclude
  `sum = 1`. Reuses one core helper via `linear_combination` rotation.
  Discharges `1 = 0` / `2 = 0` / `3 = 0` contradictions via
  `linear_combination` with explicit coefficients + `ZMod.val_*`
  injection (see `Bitwise/Constraints.lean` for the canonical pattern).
- `single_op_poly` — given all bool disjunctions plus `sum = 1`,
  conclude mutual exclusion (one column at 1 forces the others to 0).
  Polymorphic counterpart of the chip-local `single_op` lemma.
  In `Bitwise/Constraints.lean`: 6 cases discharged via
  `linear_combination` with the rotated args, contradiction via
  the sum-injectivity lemma `h_sum_inj` (sum ≠ 2 ∧ sum ≠ 3).

**2. Opcode arg-reduction: `push_cast; ring`, not direct `rw [show ...]`.**

**Why:** When the iff_poly RHS has nested op-constraint calls with
opcode arguments like `Main[48] * 2 + Main[49] * 1 + Main[50] * 0`,
Lean prints the literals as `↑2`, `↑1` (Nat-cast displayed) but
typecheck-equals `2`, `1`. A direct `rw [show Main[48]*2 + Main[49]*1
+ Main[50]*0 = 2 from by ring]` fails because the syntactic form has
casts that `ring` resolves but `rw`'s pattern matcher does not.

**How to apply:** Use the `push_cast; ring` recipe inside the `show`:
```
have h_xor_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 2 := by
  rw [h_M48, h_M49, h_M50]; push_cast; ring
rw [h_xor_args] at h_bop
```
The `push_cast` normalizes the Nat-cast literals; `ring` closes the
arithmetic. Same pattern works for the `is_real` arg.

**3. Struct-projection unfold: simp the operation constraints into h_bop.**

**Why:** After applying `BitwiseU16Operation.spec.xor_poly` to `h_bop`,
the result has shape `Word.toBitVec64_poly (BitwiseU16Operation.constraints
b cc cols 2 1).1 = execute_RTYPE_pure_w_poly b cc .XOR`. The `.1`
projection on the operation's tuple-typed output doesn't auto-reduce —
need to unfold the operation's constraint definition to expose the
explicit byte-combined vector.

**How to apply:** After the `apply spec.X_poly` step, run:
```
simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
  BitwiseOperation.constraints] at h_bop
```
This reduces `(constraints ... 2 1).1` to the explicit
`#v[result[0] + result[1]*256, ..., result[6] + result[7]*256]` form,
matching the `sp1_xor`'s `Word.toBitVec64_poly` argument vector. Then
`rw [← h_bop]` substitutes cleanly.

**Common to all 3 patterns:** the chip-arm proof proceeds in a strict
order — destructure iff → derive variant facts via helpers → apply ALU
reader iff_poly → reduce opcode args → apply op spec_poly → simp h_bop
to unfold projections → state_cstrs simp → bridge SailM monadic forms.
Deviations from this order tend to cause simp-leakage or motive errors.
