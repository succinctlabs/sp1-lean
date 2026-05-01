# Lean / SP1 gotchas

Running collection of non-obvious failure modes that have bitten us in
this repo, with the symptom, the root cause, and the recipe that worked.
Add a new section per gotcha; keep the symptom near the top of each so
`grep` works for someone hitting the failure cold.

## Kernel deep-recursion on `2^N` inside `Int.toNat (... % ...)`

**Symptom**: `(kernel) deep recursion detected` during the kernel's
final type-check pass on an otherwise-elaborated proof. The kernel pass
is independent from elaboration heartbeats, so increasing
`maxHeartbeats` doesn't help — the proof appears to elaborate fine and
then fails *after*.

**MWE** — the canonical 2-line reproducer (the smallest standalone case
isolated from this codebase, suitable for an upstream Lean issue):

```lean
example (b n : ℕ) :                                  -- elaborates fine
    ((b : ℤ) % n).toNat = b % n := by rfl

example (b n : ℕ) :                                  -- (kernel) deep recursion
    ((b * 2 ^ 64 : ℤ) % n).toNat = (b * 2 ^ 64) % n := by rfl
```

**Trigger threshold**: any `2 ^ N` with `N ≥ 15` planted inside an
`Int.toNat (... % ...)` shape blows the kernel's stack during `rfl`
re-check. The kernel tries to fully unfold `2 ^ N` definitionally;
once N crosses ~32k succ applications, it dies.

Production proofs hit this through
`BitVec.ofInt n i = (i % 2 ^ n).toNat`, which is what
`BitVec.signExtend` reduces to. So any proof term whose type or body
mentions `BitVec.signExtend N _` with `N ∈ {64, 128}` is a candidate,
as is any `Sail.BitVec.toNatInt`-derived shape with a literal modulus.

**Historical workaround**: `set_option debug.skipKernelTC true in
<decl>` disables the kernel re-check for that declaration. Does **not**
introduce new axioms (`lean_verify` confirms the standard axiom set
unchanged), but removes a verification layer. As of 2026-05-01 the
build is `skipKernelTC`-free; treat the option as a last resort, not a
production fix.

**Diagnostic**: if you suspect a kernel trip, grep the failing proof
term for `Int.toNat`, `BitVec.signExtend`, or `Sail.BitVec.toNatInt`.
Any one is enough to instantiate the substrate. The repo helper
`lean_profile_proof` (MCP) will localize which sub-call carries the
expensive term once the option is added back temporarily.

### Remediation playbook (try in order)

1. **Helper application** — if the trigger is a literal
   `((↑b : ℤ) % n).toNat = b % n` step in your proof, replace the
   `omega`/`aesop` discharge with
   `Int.toNat_natCast_emod_natCast` (`SP1Foundations/Misc.lean`) or
   `BitVec.toNat_ofInt_natCast` (`SP1Foundations/BitVec.lean`). Both
   route through `Int.toNat_emod` + `Int.toNat_natCast` and never
   expose `2 ^ N` to definitional reduction. Canonical site:
   `SP1Foundations/SailM.lean` `exec_RTYPEW_pure_bv_to_w_poly` (SRAW
   arm).

2. **Bare-`BitVec 64` lift** — when the trigger lives inside an
   `aesop`/`bv_decide` proof term over a polymorphic carrier
   (`Word (ZMod p)`, `BWord (ZMod p)`), factor sub-goals that don't
   depend on the carrier into `private` helpers stated at the bare
   `BitVec 64` level. The polymorphic instance graph never appears in
   the helper's proof term, so the kernel can re-check it. Canonical
   helpers in `SP1Foundations/SailM.lean`:
   `zero_extend_zopz0zI_s_eq`, `zero_extend_zopz0zI_u_eq`,
   `shift_bits_right_arith_setWidth_6_eq`. Bisecting which arm is the
   dominant trigger is worth the few minutes — it's often `.SRA`.

3. **Inline-derivation lift** — for chip-side bodies whose `omega`-built
   proof terms expose `BitVec.signExtend N imm`, lift the relevant
   `have h_*_eq : ... := by ...` block to a top-level lemma. The
   kernel walks the trigger once instead of inline at every call site.
   Canonical lifts: `Branch.branch_addr_eq` in
   `SP1Chips/BranchChip.lean` (replaces a 6×-inlined macro);
   `Jalr.jalr_target_mod4`, `Jalr.jalr_unmasked_eq_masked_plus`,
   `Jalr.jalr_target_eq` in `SP1Chips/JalrChip.lean`.

4. **Simp-set swap** — when the lifted helper *itself* still trips, the
   final lever is a simp set that produces a different proof-term
   shape:
   - `BitVec.add_def` (the bare definition `x + y = ⟨…⟩`) does not
     introduce `% 2 ^ w` syntactically into the proof term.
     `BitVec.toNat_add` does — and that `2 ^ w` then compounds with
     literals like `2 ^ 16/32/48` from `Word.toNat_def` to produce the
     trigger shape during omega-certificate construction.
   - `Word.toNat` (which routes through the opaque `toNat_aux.1`
     handle, unfolded automatically by `@[simp] toNat_aux_def`) is
     kernel-friendlier than `Word.toNat_def`. Both unfold to the same
     limb sum on the goal, but the proof terms differ.
   - The `Branch.branch_addr_eq` body in `SP1Chips/BranchChip.lean` is
     the canonical fix; the simp set is
     `simp [BitVec.add_def, Word.toBitVec64, Word.toNat,
     ← BitVec.toNat_inj]`.

### Cross-references

- Helpers:
  `SP1Foundations/Misc.lean` — `Int.toNat_natCast_emod_natCast`;
  `SP1Foundations/BitVec.lean` — `BitVec.toNat_ofInt_natCast`.
- Bare-`BitVec` lifts:
  `SP1Foundations/SailM.lean` (`exec_RTYPE_pure_bv_to_w_poly`,
  `exec_RTYPE_pure_bv_to_bw`).
- Chip-side lifts:
  `SP1Chips/BranchChip.lean` (`branch_addr_eq`),
  `SP1Chips/JalrChip.lean` (`jalr_target_mod4`,
  `jalr_unmasked_eq_masked_plus`).
- Tactic: `SP1Foundations/Tactics.lean` — `bv_amicus_kerneli` is a
  kernel-friendly normalization pass for `BitVec`s; complements the
  helpers above when you need `Nat`-side reasoning without exploding
  the kernel.

### When to revisit

If a future Lean toolchain bump is suspected to have fixed the kernel's
`2 ^ N` reduction, the cheapest re-test is to delete every
`set_option debug.skipKernelTC true in` line, run `lake build`, and
re-add only the lines whose declarations newly fail. As of writing,
there are zero such lines; this section becomes a regression check
rather than an active workaround index.
