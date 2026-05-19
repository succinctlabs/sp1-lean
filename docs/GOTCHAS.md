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
unchanged), but removes a verification layer. The build was
`skipKernelTC`-free as of 2026-05-01; the `_poly` migration reintroduced
~52 sites at peak. A 2026-05-17 batch removed 26 of them via three
distinct recipes — see steps 5–7 below for the playbook. 26 sites still
remain, 6 of them in-scope (Store* chips ×4, JalChip, JalrChip).
Treat the option as a last resort.

**Diagnostic**: if you suspect a kernel trip, grep the failing proof
term for `Int.toNat`, `BitVec.signExtend`, or `Sail.BitVec.toNatInt`.
Any one is enough to instantiate the substrate. The repo helper
`lean_profile_proof` (MCP) will localize which sub-call carries the
expensive term once the option is added back temporarily.

**CRITICAL test caveat**: `lake env lean <file>` does NOT trigger the
final kernel TC re-check that `lake build` runs. A `skipKernelTC` line
deleted in error will let `lake env lean` report green while `lake
build` reports `(kernel) deep recursion detected`. Always confirm
removal with `lake build <module>` (or full-project `lake build`),
never `lake env lean`. Verified 2026-05-17 on
`AddrAddOperation.spec_of_constraints_poly`.

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

5. **Drop `Nat.zero_mul, Nat.add_zero` from simp_only after the limb
   expansion + extract `omega` into a bare-`ℕ` helper** — this is the
   primary recipe that cleared 21 of 26 sites in the 2026-05-17 batch.
   For `_poly` carry-chain proofs in `Word (ZMod p)` carriers (AddrAdd,
   Branch helpers, Load* chip downstreams), the spec body typically has:
   ```
   rw [← BitVec.toNat_inj, BitVec.toNat_add,
       Word.toBitVec64_poly_toNat_poly _, Word.toNat_poly_def, ...]
   simp only [..., h_zero_val, Nat.zero_mul, Nat.add_zero]  -- <-- drop these
   ...
   omega                                                     -- <-- extract
   ```
   The `Nat.zero_mul + Nat.add_zero` simp rewrites add `Eq.mpr` operations
   that compound with the omega certificate's `% 2 ^ 64` exposure, pushing
   the kernel re-check over its stack limit. Drop them from the simp_only,
   then move `omega` into a `private` helper at the bare-`ℕ` level whose
   conclusion accepts the un-simplified `+ 0 * 2 ^ 48` form. The helper's
   `omega` certificate sees `% 2 ^ 64` *in isolation* (no polymorphic
   `ZMod p` instances surrounding it) and the kernel passes. Canonical
   examples: `AddrAddOperation.close_addr_add_nat` and `Branch.close_branch_addr_nat`
   / `close_pc_plus_4_nat`. Often the spec body's `omega` becomes
   `exact close_*_nat _ _ ... hv0' hv1' hv2' n0 n1 n2 n3` (or its `.symm`).
   For chip-level `correct_*` theorems with no helper-lift available
   (e.g. LoadDoubleChip, LoadX0Chip), the in-place simp_only edit alone
   suffices because the trigger is the simp_only itself, not surrounding
   omega.

6. **Quick "stale comment" check — try just removing the line first.**
   Many `skipKernelTC` lines were added defensively and stayed after the
   underlying issue was fixed elsewhere. Both `MulOperation.core_mul_poly`
   and `core_mulw_poly` cleared in the 2026-05-17 batch this way: just
   delete the `set_option` line and rebuild. Cost: one build cycle per
   site (11min for MulOperation). Cheap to test, often the right answer.

7. **Replace `omega` over `BitVec.toInt` with explicit Int lemmas.** When
   the kernel-tripping `omega` is closing a `BitVec.toInt` inequality
   (the omega certificate brings in `2 ^ 64` via `Int.toNat ((... % 2^64)...)`),
   substitute the explicit lemma directly:
   - `Int.not_lt.mpr : b ≤ a → ¬ a < b`
   - `Int.not_le.mp : ¬ a ≤ b → b < a`
   - `Int.not_le.mpr : b < a → ¬ a ≤ b`

   The function-application proof term is shallow; the kernel passes.
   Canonical fix: `correct_bge_poly` in `SP1Chips/BranchChip.lean`.

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
`set_option debug.skipKernelTC true in` line, run **`lake build`** (not
`lake env lean` — see caveat above), and re-add only the lines whose
declarations newly fail.

As of **2026-05-17 evening sweep** there are **11** such lines (down from
~22 after a fresh per-site verification — see
`docs/memory/feedback_skipkerneltc_per_site_status_2026_05_17.md` if
present). The 11 still load-bearing:

- `SP1Operations/Operation/AddrAddOperation.lean` — already cleared 2026-05-17 morning
- `SP1Operations/Operation/MulOperation/Constraints.lean` — already cleared 2026-05-17 morning
- `SP1Chips/Branch/Constraints.lean` — already cleared 2026-05-17 morning
- `SP1Chips/Load*.lean` — already cleared 2026-05-17 morning
- `SP1Chips/DivRem/DivRem.lean` — `div_rem_poly` core (signed 64-bit DWord 8-limb)
- `SP1Chips/DivRem/DivuRemu.lean` — `divu_remu_poly` core
- `SP1Chips/ShiftLeft/Sll.lean` — `spec.sll_poly` **and** `spec.slli_poly`
- `SP1Chips/ShiftRight/Srl.lean` — `spec.srl_common_poly`
- `SP1Chips/Store{Byte,Half,Word,Double}Chip.lean` — all 4 `correct` theorems
- `SP1Chips/JalChip.lean` — `SP1JAL_correct`
- `SP1Chips/JalrChip.lean` — `JALR_correct`

**Sites where cheap removal WORKED in the 2026-05-17 evening sweep (kept removed):**
- `DivRem.lean` ×3: the redundant section-level + `spec.div_poly` + `spec.rem_poly`
  (only the core `div_rem_poly` needs the option — the wrappers don't)
- `DivuRemu.lean` ×2: `spec.divu_poly` + `spec.remu_poly`
- `DivuwRemuw.lean` ×3 and `DivwRemw.lean` ×3: all cores + wrappers cleared
- `ShiftRight/{Sra,Sraw,Srlw}.lean`: all common-bodies cleared
- `ShiftRight/Srlw.lean` ×2: the local `Word.isU64`-style helper too

**Key empirical finding (2026-05-17 evening):** for the DivRem and DivuRemu
*64-bit cores*, the `*_poly` core lemma trips the kernel but the thinner
`spec.*_poly` wrappers that `specialize` into the core do NOT. The wrapper's
proof term is just a function application referencing the core's already-checked
olean — kernel sees a shallow term. Lesson: don't assume "if the core needs
`skipKernelTC`, the wrappers do too." Test each independently.

**Empirical finding on Store* (2026-05-17 evening):** Lifting `h_addr_eq`
(the `(reg + signExt(imm)).toNat = addr_low_limbs` bridge) into a
`Word.toBitVec64_poly_addr3_toNat_eq` top-level helper in `SP1Foundations/Word.lean`
roughly halves elaboration time (~103s → ~51s on StoreByteChip) but **kernel
still trips** — there are *multiple* compounding triggers (h_offset_eq,
h_in_range, `Word.toBitVec64_poly_lowLimb_add_nat`, default-`simp`-via-write_ram).
A single lift is not enough; recipe 2 (bare-`BitVec` helper covering the *whole*
addr-bridge + width-specific write monadic chain) is the documented path but
costs 2–3h per chip with no single-lift shortcut.

**Empirical finding on Sll/Srl 64-bit shifts:** The `spec.sll_poly`,
`spec.slli_poly`, and `spec.srl_common_poly` proofs are structurally identical
to the passing `spec.sra/sraw/srlw_common_poly` proofs — same prologue, same
4-way byte-shift split, same close-helpers. The differentiator is invisible at
the tactic-source level. The passing Sra has an outer `rcases h_msb_b` that
splits the proof term into two arms; the failing Sll/Srl have no analogous
outer split. Hypothesis: adding an outer split (recipe 3 applied at the byte_shift
level — lift each of the 4 byte_shift branches into a separate helper, dispatcher
just does `rcases b_cb5 ... ; rcases b_cb4 ...`) may break the kernel walk into
shallower chunks. Not yet verified.

**Empirical finding on Jal/Jalr:** The `word_four_eq_bitvec_four` helper
extracted in commit `62b65cf` (recipe 3 inline-derivation lift) is insufficient
on its own. Remaining triggers are likely `hmod4` (15-line block with
`Word.toBitVec64_poly` chains), the `AddOperation.spec_poly` results
(`h_add'` / `h_add_pc'` — whose body contains `BitVec.toNat_add`), and the
multiple default `simp [spec_jal, sp1_jal, execute_JAL, ...]` calls. Each is a
candidate for further recipe-3 lifting.

**JalrChip deep-dive findings (sorry-bisection, 5 build cycles):** The trigger
is the single `simp [spec_jalr, sp1_jalr, run_readReg_of_isInitialized _ _ hs,
EStateM.Result.map, cond, execute_JALR, op_a, op_b, op_c, sp1_op_a, sp1_op_b,
sp1_op_c, read_op_a, read_op_b, ← h_imm_signExtend]` call at
`SP1Chips/JalrChip.lean:258-261`. Verified via sorry-truncation:
- truncating BEFORE this simp passes kernel TC;
- truncating AFTER this simp still trips.

Fixes tried that **don't** work:
- Splitting into chained `simp only` (second simp can't apply its lemmas
  because default simp's implicit monad lemmas are needed).
- Moving `← h_imm_signExtend` to a separate `rw` (trigger shifts but still trips).
- Replacing `simp` with `simp only [explicit list]` (can't reproduce default
  simp's monad-bind normalization with explicit lemma list).
- `--tstack=2000000` (5× current; still trips — **not borderline depth**, this
  is pathologically deep recursion).

**The proof term produced by this `simp [...]` is pathologically deep** — the
combination of unfolding `execute_JALR` (Sail spec, multi-step do-block),
applying monad bind normalizations, and rewriting `← h_imm_signExtend` produces
a term whose kernel re-check unfolds beyond any reasonable stack. Fix path:
write a `JALR_correct`-shaped helper at the `EStateM`/Sail level that produces
the same post-simp goal form WITHOUT relying on the default simp set, or lift
the entire post-simp goal manipulation chain (lines 256–317) into a helper
whose conclusion is the original theorem statement. Both are multi-hour
investments per chip.

Same pattern almost certainly applies to `SP1JAL_correct` in `JalChip.lean`
since it uses the analogous `simp [spec_jal, sp1_jal, execute_JAL, ...]` at
line 124.
