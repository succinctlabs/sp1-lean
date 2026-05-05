---
name: Field-genericization effort current state
description: Status of the additive `_poly` companion strategy; 20 chips with at least one correct_* theorem (ALU + memory-write + control-flow + memory-read + Branch complete), recipe validated across all 4 chip categories
type: project
originSessionId: f9ab5b6f-d305-43ed-a962-8c272d98a1d1
---
The repo is mid-effort lifting proofs off `Fin KB` (KoalaBear) onto an
arbitrary prime field. Strategy: **additive parallel `_poly` companions**
parameterized over `{p : ℕ} [Fact (Nat.Prime p)]` (often plus
`[Fact (2^17 < p)]`), keeping the `Fin KB` versions in place. Zero chip-side
churn so far.

**Canonical state summary** lives in `docs/FIELD_GENERIC.md` under
"Current state — 2026-05-01" (top-level section, just under the title).
Read that for the authoritative status. The chronological sub-phase log
below it (A through B.11) is the historical record of what was tried.

**Done as of 2026-05-01:**

- **Foundation** (`SP1Foundations/`) is **complete**: 736 `_poly`
  occurrences across 7 files. `Constraint.lean`, `ByteOpcode.lean`,
  `Assumptions.lean`, `Word.lean` (~50 lemmas across 6 namespaces),
  `BitVec.lean`, `SailM.lean` (18 execute/exec bridges including
  RTYPE/RTYPEW/ITYPE/SHIFTIOP/SHIFTIWOP/MUL/MULW), and `Field.lean`
  primitives all have `_poly` siblings.
- **Operations** (`SP1Operations/`) **substantially complete**: all 21
  ops in `update_constraints.py`'s `PARAMETRIC_OPS` dict have struct +
  Constraints lifted. Hand-written iff_poly: 5 readers + 6 bridge-coupled
  ops + 5 spec_poly + LtUnsigned/Signed (partial). The post-processor
  preserves the lift across regens.
- `lake build` clean (0 errors, 0 warnings, 8508 jobs) at B.11 boundary
  2026-04-28.

**Track A complete (2026-05-01)**: all 5 outstanding `_poly` lemmas landed.
Foundation + Operations are now fully complete. 0 deferred op `_poly` lemmas.

Closed in Track A (LtUnsigned/LtSigned cluster + BitwiseU16 cluster):
- ✅ `LtOperationUnsigned.spec_poly` (BitVec form): closes via `spec.nat_poly`
  + `execute_RTYPE_pure_w_poly` (already in `SailM.lean`) with explicit
  `ZMod.val_one`/`val_zero` discharge.
- ✅ `LtOperationSigned.spec.signed_poly` (the formerly-failed natural-form
  lemma): structured `.val` arithmetic via `val_sub_cases`+`ZMod.val_add_of_lt`,
  plus algebraic identity `shifted_w.toNat_poly = w.toInt_poly + 32768 * 2^48`.
  Heartbeats 4M.
- ✅ `LtOperationSigned.spec.branch_poly`: two private helpers
  (`branch_helper_eq_iff_unsigned_poly`, `branch_helper_eq_iff_signed_poly`)
  prove the `b = d ↔ all flags 0` iff for `is_signed = 0` (msbs forced 0
  via `h_msb_b_eq.resolve_left`) and `is_signed = 1` (4-way limb-3
  sub-case-split via `val_sub_cases` for cross-msb contradictions). The
  `b ≠ d ↔ flag-sum = 1` iff is contrapositively derived from the eq-iff
  plus the sum constraint. The if-then-else conclusion comes from
  `spec.unsigned_poly`/`spec.signed_poly`. Heartbeats 16M / 32M / 16M.
- ✅ `BitwiseU16Operation.spec.{and,or,xor}_poly` (3 lemmas): added
  helper cascade — `Word.{and,or,xor}_toBWord_poly` (via
  `Word.toBitVec64_poly_toBWord_poly`), `U16toU8OperationSafe.spec.unsafe.return_poly`
  + private `u16_to_u8_decomposition_poly` (via `mul_inv_cancel₀ val_256_ne_zero`
  + `ZMod.val_add_of_lt`/`val_mul_of_lt`). Then mirror the `Fin KB`
  proof structure: byte vector extraction → 8 byte-AND/OR/XOR equations →
  `Nat.mod_eq_of_lt` (no Fin wrapping needed) → byte abbreviations →
  `BitVec.ofNat_{add,mul,and,or,xor}` simps → `bv_decide`. OR/XOR need
  `(1 : ZMod p).val = 1` / `(2 : ZMod p).val = 2` helpers re-derived
  after `simp_all` (which strips Fact instances). Heartbeats 64M each.
- **8 chips migrated (Sub, Add, Subw — 2026-05-01; Addi, Addw+Addiw,
  UType, Lt, Bitwise — 2026-05-02)**: chip-level parametric emission added to
  `update_constraints.py` via `PARAMETRIC_CHIPS` dict (incremental,
  per-chip opt-in per user directive). Each chip's
  `<Chip>/Constraints.lean` is parametric in
  `(F : Type) [Field F] [CoeHead F ℕ]`; `<Chip>Chip.lean` restated over
  `{p : ℕ} [Fact (Nat.Prime p)] [Fact (2^17 < p)]` with
  `Main : Vector (ZMod p) N`. `correct_*` consumes `_poly` lemmas;
  lake build clean (8508 jobs, 0/0); standard axioms only.
  - **Sub** (33 cols, RTypeReader): pilot. Commit `e810b29`.
  - **Add** (33 cols, RTypeReader): `AddOperation.spec_poly` landed
    alongside. Commit `c823323`.
  - **Subw** (32 cols, RTypeReader, HWord+U16MSB sign-extend):
    introduced `HWord.sign_extend_32_to_64_msb_poly` and
    `SubwOperation.spec_poly`. Commit `d9ff089`.
  - **Addi** (30 cols, ITypeReader, opcode 1 → needs local
    `(1 : ZMod p).val = 1` via `ZMod.val_one`; reuses existing
    `AddOperation.spec_poly`). Required reader prereq:
    `ITypeReader.allHold_constraints_iff_is_real_poly` (one-line
    `simp [allHold_constraints_iff_poly, h, and_assoc]` mirror of R-type).
    Proof bridges via `← trusted_instr_prop.2; exec_ITYPE_pure_bv_to_w_poly;
    simp only [execute_ITYPE_pure_w_poly, execute_RTYPE_pure_w_poly, rop_of_iop]`
    (drops the `← is_add` step Addw needs — both sides already match
    via execute_RTYPE_pure_w_poly's definitional sum form).
  - **Addw + Addiw** (36 cols, ALUTypeReader, opcode 19 → custom
    `h19_val` like Subw's h20_val; HWord+U16MSB sign-extend; both
    `correct_addw` (Addw) + `correct_addw` (Addiw) in same file).
    Required prereqs: `ALUTypeReader.allHold_constraints_iff_is_real_poly`
    (uses `aesop (add safe (by simp [allHold_constraints_iff_poly]))`
    rather than the simp+and_assoc one-liner because of the imm_c
    discriminator) and `AddwOperation.spec_poly` (mirror of
    `SubwOperation.spec_poly` with Add-form natural carries; private
    `limb_lift` duplicated; 16M heartbeats; same `linear_combination
    + limb_lift + U16MSBOperation.spec_poly` recipe).
  - **UType** (31 cols, JTypeReader, 2 thms — `correct_lui` +
    `correct_auipc`): Lifted private helper
    `toBitVec64_eq_signExtend_sp1_op_b` → `_poly` companion (BitVec
    arithmetic is field-agnostic; only `Main[i].val` accesses change).
    LUI's op_a=0 path needs explicit
    `h_zero_word : Word.toBitVec64_poly #v[0,0,0,0] = 0#64` for the `if`
    reduction; `decide` on `(1 : ZMod p) ≠ 0` fails (free `p`) — use
    `one_ne_zero`. The `omit [Fact (2^17 < p)] in` syntax doesn't compose
    with a docstring; use `set_option linter.unusedSectionVars false in`
    on a comment-prefixed lemma instead. Heartbeats 1.6M for both
    `correct_*`.
  - **Bitwise** (51 cols, ALUTypeReader, 6 thms — `correct_{xor,xori,or,ori,and,andi}`):
    Single big `allHold_constraints_iff_poly` (Sub-style — 51-let body
    is small enough that the same `simp [and_assoc, constraints,
    BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
    sub_eq_zero]` recipe closes; budget elevated to 800K). Per-arm
    structure mirrors LtChip + AddwChip: rw the iff_poly, destructure
    into `(h_bop, cpu, alu, b_xor, b_or, b_and, one_of, h13)`, derive
    `h_is_real := Main[48] + Main[49] + Main[50] = 1` via 3 helpers
    (`sum_eq_one_of_eq_one_{left,mid,right}`) and the off-variant
    zeros via `single_op_poly`. Reduce the BitwiseU16Operation opcode
    arg to a constant via `push_cast; ring`, apply the matching
    `BitwiseU16Operation.spec.{xor,or,and}_poly`, then bridge the
    `.1` projection to the explicit byte-combined form via
    `simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
    BitwiseOperation.constraints] at h_bop`. I-type arms additionally
    use the AddiwChip-style signExtend immediate bridge.
  - **Lt** (44 cols, ALUTypeReader, 4 thms — `correct_{slt,sltu,slti,sltiu}`):
    Pre-existing groundwork in `Lt/Constraints.lean` provided the 4
    `allHold_constraints_iff_*_poly` lemmas (commit `c133022`). Each chip
    `correct_*` mirrors Sub/AddwChip: rw the iff_poly, destructure into
    `(lt_op_cstrs, cpu_cstrs, alu_cstrs, h_M3X, _h13)`, derive
    `h_is_real := Main[32] + Main[33] = 1` from `Main[3X]=1` plus the
    iff's `Main[3Y]=0` byproduct, then unpack ALU reader iff_poly. Custom
    bridges: (1) opcode val for 9 (slt/slti) / 10 (sltu/sltiu) via
    `ZMod.val_natCast_of_lt`; (2) `(0:ZMod p) + 1 = 1` and `1 + 0 = 1`
    rewrites to normalize the LtOperationSigned `is_real` argument before
    `apply spec.{signed,unsigned}_poly`; (3) the result-bit bridge
    `Word.toBitVec64_poly #v[(if cond then 1 else 0), 0, 0, 0]
       = if cond then 1#64 else 0#64`
    via `split_ifs <;> simp [..., ZMod.val_one, ZMod.val_zero]`. I-type
    arms (slti/sltiu) additionally use the AddiwChip recipe for the
    signExtend immediate bridge: reconstruct
    `h_op_c_imm_isU64` from `c0..c3` bounds + `h25_eq..h28_eq`, derive
    `h_signExt_eq` from `h_imm_c_consts.symm`, then `exec_ITYPE_pure_bv_to_w_poly`
    delegates to RTYPE-form via `rop_of_iop`. Heartbeats 1.6M each. State_cstrs
    simp set must include `LtOperationSigned.constraints, LtOperationUnsigned.constraints,
    U16MSBOperation.constraints, U16CompareOperation.constraints` to fully
    unfold the nested operation constraints down to the state-prop layer.
  - **StoreDouble/StoreWord/StoreHalf/StoreByte** (commits `27c98ac`, `5ff0464`, `fcd840a`, 2026-05-02):
    Memory-write family piloted with StoreDouble; the other 3 are mechanical
    clones differing only in width (8/4/2/1 bytes). Pattern: F-parametric
    Main, AddrAddOp.spec_of_constraints_poly for addr arithmetic, then
    `run_vmem_write_of_width_N` (with prime variants for byte/half).
  - **Jal** (commit `59174db`, 2026-05-02): First control-flow chip migration.
    Validates the recipe extends past ALU/memory. Uses `Word.four_isU64_poly`,
    `val_mod_4_eq_zero_iff_zmod`, `jump_to_of_mod4_eq_zero` Sail axiom. Two
    `AddOperation.spec_poly` chains (PC + 4, PC + imm).
  - **Jalr** (commit `1a22ba9`, 2026-05-03): Second control-flow chip,
    handles the bit-clearing mask pattern (chip stores masked low limb +
    bit-0 mask flag separately). Uses `ITypeReader.allHold_constraints_iff_is_real_poly`
    + manual `Opcode.trusted_instr_poly` unfold for opcode 47 (JALR's
    i_type_constraints), three local mask-arithmetic sub-lemmas (target_mod4,
    unmasked_eq_masked_plus, target_eq), and `val_sub_cases` for the ZMod →
    Nat subtraction bridge under the `< 65536` aligned-low-limb constraint.
    `aesop` calls on `isInitialized` side-goals need `clear *- hs; aesop` to
    avoid context-driven recursion.
  - **LoadDouble** (commit `1b0594f`, 2026-05-03): First memory-read chip
    migration. Iff_poly was already landed (commit `301e4a5`); chip migration
    follows StoreDouble's recipe plus per-byte memory bridges (`haddr_plus`
    family + `byteConcat8_toNat_eq_Word_toNat_poly`). Key insight:
    AddrAdd's `isU64_poly` output gives `Main[25].val < 65536`, which is
    enough for the `+ k` shift bridge under just `Fact (2^17 < p)` —
    `Main[25].val + 7 < 65543 < 2^17 < p`. The `Main[28] * (Main[26] +
    Main[27]) = 1` constraint forces the chip-stored memory receive into
    its non-register-index branch. `simpa` (not `exact`) is needed to
    discharge per-byte side-conditions because the post-write-pc state
    differs from the original `s` by a `regs.insert` wrapper that doesn't
    affect `mem`.
  - **LoadHalf / LoadWord / LoadByte** (commits `3ee152c`, `9bd26da`, `38c7563`,
    2026-05-03): Memory-read family completed. Each follows LoadDouble's
    recipe at the per-width level:
    - 16-bit, 32-bit, 8-bit `signExtend64_*_poly` + `setWidth64_*_poly`
      helpers added to `SP1Foundations/Word.lean` (`_ge_`/`_lt_` variants
      for signed; plain for unsigned). One-for-one ports of the Fin KB
      versions; bodies are pure `BitVec`/`Nat` arithmetic. The `_ge_*`
      variants need `[Fact (2^17 < p)]` for `(65535 : ZMod p).val = 65535`
      / `(65280 : ZMod p).val = 65280` via `Nat.mod_eq_of_lt`.
    - `halfword_msb_poly` (LoadHalf, LoadWord): replaces Fin KB's
      `Fin.intCast_val_sub_eq_sub_add_ite` with `val_sub_cases` — the
      wrap-around branch fires when `b = 1` and `a.val < 32768`, and the
      contradiction `(2*a-65536).val = 2*a.val + p - 65536 ≥ p - 65536 >
      65536` falls out from `Fact (2^17 < p)`.
    - `nat_decomp_of_inv8_decomp_poly` (LoadByte): the 8-bit byte-level
      decomposition uses `ZMod.val_mul`/`ZMod.val_add_of_lt` instead of
      `Fin.val_mul`/`Fin.val_add`; produces `x.val = lo.val + hi.val * 256`.
    - LoadByte's `(128 : ZMod p) ≤ Main[43]` ↔ `Main[43].val ≥ 128` is
      handled by `change` (since `LE (ZMod p)` is `x.val ≤ y.val` per
      `SP1Foundations/Field.lean` instance).
    - The 8-case fan-out (LoadByte) and 4-case (LoadHalf) port directly,
      with `(by decide)` contradictions swapped for `zero_ne_one`/
      `one_ne_zero` based on the rewritten direction. The Fin KB
      `simp_all` "everything works" closer is replaced by manual
      case-by-case `bitVec_ofNat8_eq_of_mod` + `omega`.
    - For `iff_lb_poly` / `iff_lh_poly` / `iff_lhu_poly` / `iff_lw_poly` /
      `iff_lwu_poly`: the negative `by_cases` branch needs `(1 + 1 : ZMod p)
      ≠ 0` (via `val_2_ne_zero`) to discharge contradictory
      `Main[42] + Main[43] = 1 + 1 = 0` (or analogous) cases that
      Fin KB's `decide` handles for free.
  - **LoadX0** (3 commits, 2026-05-03):
    - First: `is_loadX0_poly` umbrella flag def (sum-equals-one over
      `Main[41..47]`).
    - Second (`4b7767d`): `LoadX0Chip.lean` chip-side public surface —
      `sp1_op_a/b/c`, `sp1_loadX0` (PC-only advance, no `write_reg`
      because `op_a = x0` makes `wX_bits 0 _` a no-op per
      `Lean_RV64D/Regs.lean:663`), 7 sub-opcode `spec_loadX0_*`
      functions, plus private `seven_collapse_M47`. The collapse
      helper threads `ZMod.val_add_of_lt` bottom-up through 6 partial
      sums (each ≤ 7 < 131072 < p) to derive `Main[41..46] = 0` from
      each Main[i] ∈ {0,1} + sum ∈ {0,1} + Main[47] = 1.
    - Third (`adad452`): `correct_loadX0_ld` — first sub-opcode
      correctness theorem. Inline destructure of the 29-conjunct simp
      normal form (no per-flag iff lemma) → `seven_collapse_M47` →
      byte-routing E92/E95/E100 forces `Main[38..40] = 0` → mirrors
      `Load.LoadDouble.correct_ld` line-for-line. Uses
      `ITypeReaderImmutable.allHold_constraints_iff_is_real_poly`
      (not the regular `ITypeReader` version). The `Opcode.ofNat 35`
      match collapses via `simp [Opcode.trusted_instr_poly,
      Opcode.ofNat, Nat.ble, h35_val, i_type_constraints_poly]`,
      yielding `h14_lt_zmod : Main[14] < 32` (from `op_b_0 < 32`)
      and `h_imm_se` (the third conjunct of i_type_constraints_poly).
      The `wX_bits 0` no-op step closes by single `simp` after the
      `run_vmem_read_of_width_8'` rewrite. Heartbeats 1.6M +
      `skipKernelTC`.
  Now 19 chips with at least one correctness theorem. LoadX0's other
  6 sub-opcodes (LB/LBU/LH/LHU/LW/LWU) **all landed 2026-05-03**
  (commits `bc45f87`, `b5d96b3`, `59b7c80`, `195019a`) — same recipe
  with permuted collapse + varying byte widths. **MemChecks PMA
  rewrite** also landed 2026-05-03 (`45777af`/`0bb6d5f`/`950841b`):
  rewrote `MemChecks.lean` against the SP1 PMA window (instead of the
  old CLINT bound), threaded `h_in_range` through all 11 load/store
  chips, then made each chip derive `h_in_range` from its
  `AddressOperation` constraints (helpers
  `MemChecks.range_subset_sp1_pma`, `is_aligned_vaddr_iff_mod`,
  `AddressOperation.addr_limbs_bounds`).

  4 chips remain: Mul (5 arms), DivRem (8 arms),
  ShiftLeft (4 arms), ShiftRight (8 arms). Constraints body sizes:
  Mul=67 lets, ShiftLeft=203, ShiftRight=325, DivRem=465.

  **DivRem migration in progress (started 2026-05-05).** Pivoted from
  ShiftRight after discovering shift chips embed a KB-specific `64⁻¹`
  literal (`2097414145`); see `feedback_shift_kb_specific_literal.md`.
  DivRem uses only universal literals (65535/65536) → clean Mul-recipe
  migration. 8 variants at Main[201..208] (div/divu/divw/divuw/rem/
  remu/remw/remuw); `is_real := Main[244] = 1` is a separate column
  (NOT a sum-of-flags like Mul/Bitwise — simpler structure).
  Spec lemmas chip-local (no `Operation/DivRemOperation/` directory);
  4 shared cores (`div_rem`, `divu_remu`, `divw_remw`, `divuw_remuw`)
  delegated to by 8 thin `spec.<variant>` wrappers. Chip-side has
  `correct_prologue_facts` (DivRemChip.lean:31) bundling all per-arm
  prologue work; will need `correct_prologue_facts_poly` analogue.

  **Phase 2 (helpers) COMPLETE 2026-05-05** — 6 commits totaling
  ~270 lines. Chip-side _poly infrastructure ready for spec proofs:

  - `0540f40`: Phase 0 parametric emission (`PARAMETRIC_CHIPS` +
    regen). Reverted 9 unrelated regen-bug files (post-processor
    stripped `F` from `(cols : Op F)` → `(cols : Op)` in 4 ops;
    cosmetic paren-additions in 5 readers also reverted to keep
    diff scoped to DivRem).
  - `8dc3860`: Phase 2a chip-local `_poly` defs — 8
    `is_<variant>_poly`, `is_real_poly`, 3 `sp1_op_{a,b,c}_poly`.
  - `b4a9df4`: Phase 2c `register_bounds_poly` (variant-INDEPENDENT
    bounds — op_a < 32, op_b/op_c/pc[0] < 65536; chip-level
    `correct_*_poly` proofs refine op_b/op_c to < 32 via opcode
    reduction with the variant flag in scope) + `ops_U64_b_c_poly`
    + `op_a_is_0_poly`. All via direct destructure of
    `(constraints Main).allHold_poly`: 18-deep nested left-pair
    pattern peels CS0..CS18 (19 entries), then projects CS18 (the
    RTypeReader sub-list) and applies
    `RTypeReader.allHold_constraints_iff_is_real_poly`.
  - `1900adb`: Phase 2b `single_op_poly` + private
    `eight_mutex_left` helper. **Critical insight**: 8-way mutex
    via `.val` arithmetic + `omega`, NOT via 128-case rcases.
    Recipe: chain of 7 `ZMod.val_add_of_lt` rewrites lifts
    field-level `Σ = 1` to Nat-level `Σ a_k.val = 1`; with
    `Fact (2^17 < p)` ⊢ `8 < p` so no overflow at any partial
    sum; `omega` closes "others = 0" conjunction; final bridge
    via `(ZMod.val_eq_zero _).mp`. The destructure of the chip's
    153-item trailing list: 134 underscores + 8 binders
    (b201..b208) + 10 underscores + sum_disj + _h_M13. Variant
    flag booleans at positions 134-141 (E325, E327, ..., E339);
    sum=1 at position 152 (E367, after `sub_eq_zero` on
    `1 - sum = 0`). Per-variant invocation does
    `linear_combination -sum_disj` to permute the sum so the
    active flag is first.
  - `6f11f25`: trim trailing whitespace in is_<variant>_poly
    defs (drive linter warnings to zero per repo policy).

  **Phase 3b PARTIAL — `div_mod_decomposition_w_poly` aux LANDED
  2026-05-05** (commit `ab6def6`, ~30 lines, clean): the polymorphic
  counterpart of `div_mod_decomposition_w` (line 1114). Statement at
  the `.val` level (since ZMod p lacks native `% / /`). Bound is
  `c.val < 2` (vs Fin KB's `c.val < 2130706433/65536`) since at every
  use site `c` is a carry bit. Wrap-around of `val_sub_cases` ruled
  out via `Fact (2^17 < p)`. **First piece** of Phase 3b
  infrastructure for the `divu` pilot.

  **`divu_remu_poly` core (Phase 3b, the heavy work)** —
  **second attempt 2026-05-05 (mid-session, NOT yet committed)**:
  scaffold + Stage 1 (upfront prep) + Blocker 1 (opening rcases) +
  Blocker 2 (c=0 branch) + c≠0 "have arm" all landed in
  `SP1Chips/DivRem/Constraints.lean` lines ~2455–2793. **Sorry
  placeholder** at line ~2793 for the 8-way `b_cry3` end-game
  (Blocker 3 territory — corresponds to Fin KB lines 2416–2442).
  Detailed status in plan file
  `/home/devontuma/.claude/plans/make-a-plan-to-memoized-mitten.md`.
  See `feedback_divrem_core_port_blockers.md` for the resolved
  Blocker 1+2 patterns (incl. the `Nat→ℤ` cast vs `ZMod.cast`
  insight that closed Blocker 2).

  **Phase 3a `correct_prologue_facts_poly` LANDED 2026-05-05**
  (commit `1e4bad0`): variant-INDEPENDENT bundle in
  `DivRemChip.lean` after the existing Fin KB prologue.
  Composes `register_bounds_poly` (op_a < 32, op_b/c/pc[0] < 65536)
  + `ops_U64_b_c_poly` + `op_a_is_0_poly` + 8 `single_op_poly`
  implications, returning a 14-conjunct ∧. **Does NOT bundle**
  the 4 state reads (read_pc / read_op_a / read_op_b / read_op_c)
  nor refine op_b/c < 32 — both are variant-dependent and stay
  per-arm (Mul precedent). A bundled state simp without h14/h21<32
  in scope leaves op_b/c reads in pre-discharged if-then-else form,
  which would require chip arms to re-simp. Keeping reads per-arm
  is cleaner.

  **Remaining (resume here)**:
  - **Phase 3b — 4 cores** (the gating heavy work). Port
    `divu_remu`, `div_rem`, `divuw_remuw`, `divw_remw` (each
    ~430-1000 lines of Fin KB body) to ZMod p. **Each core is
    multi-hour focused work**; not safe in one auto-mode session
    without checkpointing.
    - Available poly infra (already exists in `SP1Foundations/`):
      `combine_MUL_MULHU_poly` (SailM.lean:1015),
      `Word.{extend_poly, extend_true_is_signExtend_poly,
      extend_false_is_setWidth_poly}`,
      `Word.{toNat_reconstruct_poly, toBitVec64_toNat_poly,
      toNat_poly_lt_of_isU64_poly, lt_cases_of_isU64_poly,
      isU64_of_cases_poly}`,
      `DWord.{isU128_of_cases_poly, toBitVec128_toNat_poly}`.
    - `tdiv_tmod_unique_full_nat` (Constraints.lean:1180) is
      field-agnostic (pure ℕ/ℤ) — usable as-is.
    - **`div_mod_decomposition_w` (Constraints.lean:1114) needs
      a poly port**: statement uses `a = b - c * 65536 ↔
      a = b % 65536 ∧ c = b / 65536` over `Fin KB`. ZMod p
      version needs restating (ZMod p has no native `% / /`),
      likely via `.val % 65536` + `.val / 65536` formulation.
      `2130706433 / 65536` bound becomes `p / 65536`.
    - Key Fin KB → ZMod p substitutions:
      `Fin.val_add` → `ZMod.val_add_of_lt`,
      `Nat.mod_eq_of_lt (b := 2130706433)` → `(b := p)` with
      `Fact (2^31 < p)` likely needed (DRS uses
      `2130706433 = KB`, ZMod p comparison must hold for `p`).
      Each core's 8 `(by omega)` discharges of overflow conds.
  - **Phase 3c — 8 thin spec wrappers**: `spec.<variant>_poly` ×
    8 (~200 lines each). Mostly mechanical after cores done.
  - **Phase 4 — 8 `correct_<variant>_poly`** in DivRemChip.lean
    (~25-40 lines each). Use `correct_prologue_facts_poly` for
    variant-independent prep; derive op_b/c < 32 inline via
    `RTypeReader.allHold_constraints_iff_is_real_poly` + simp on
    variant flag + `Opcode.ofNat`/`Nat.ble` (Mul precedent at
    `MulChip.correct_mul_poly`).
    - Suggested order: divu first (simplest, validates recipe),
      then div, remu, rem, divuw, divw, remuw, remw.
  - **Phase 5**: memory + `MEMORY.md` index update (21 → 22 chips).

  **Available helpers** (all in `SP1Chips/DivRem/Constraints.lean`
  `section poly_helpers` near end of file):
  - `is_real_poly`, `is_<variant>_poly` × 8
  - `sp1_op_{a,b,c}_poly`
  - `register_bounds_poly` (op_a < 32, others < 65536)
  - `ops_U64_b_c_poly` (b, c are U64)
  - `op_a_is_0_poly` (Main[6] = 0 → Main[28..31] = 0)
  - `single_op_poly` (8-way mutual exclusion)
  - private `eight_mutex_left` (the .val-omega 8-way mutex engine)

  Chip-side (`SP1Chips/DivRemChip.lean`):
  - `correct_prologue_facts_poly` (commit `1e4bad0`,
    Phase 3a) — bundles all of the above into a 14-conjunct ∧
    via 4 obtains. Variant-INDEPENDENT only.

  Latest plan file:
  `/home/devontuma/.claude/plans/make-a-plan-to-goofy-feather.md`.

  **Mul chip migration COMPLETE 2026-05-05** (12 commits): all 5
  op-level `MulOperation.spec.<variant>_poly` (Phase 3) AND all 5
  chip-level `correct_<variant>_poly` (Phase 5) landed. Mul joins
  the 20 chips → now 21 chips with at least one `correct_*_poly`
  companion. 3 remain (DivRem, ShiftLeft, ShiftRight).

  Phase 5 commits (2026-05-05):
  - `8e0a74b`: `correct_mul_poly` + 5 `is_real_eq_one_of_<variant>`
    helpers in `Mul/Constraints.lean`. Each helper takes cstrs +
    `h_<variant> = 1` and returns `Σ Main[77..81] = 1` via
    `sum_eq_one_of_eq_one_*`. ~80-line proof in new `Mul.Poly`
    sub-namespace.
  - `fb8c27e`: `correct_mulh_poly` (compiled on first attempt).
  - `0d16ba9`: `correct_mulhu_poly` (had wrong `single_op_poly` arm —
    used `.2.2.2.1` instead of `.2.2.1`. The chip-level `single_op_poly`
    uses Main[77..81] in natural order: `.1`=mul, `.2.1`=mulh,
    `.2.2.1`=mulhu, `.2.2.2.1`=mulhsu, `.2.2.2.2`=mulw — distinct
    from MulOperation.single_op_poly's order which has mulw before
    mulhsu).
  - `75ccb9b`: `correct_mulhsu_poly`.
  - `49cc077`: `correct_mulw_poly` (uses `execute_MULW` with no opcode
    arg, distinct from MUL/MULH/MULHU/MULHSU).

  Tactical wisdom from Phase 5:
  - `RTypeReader.allHold_constraints_iff_is_real_poly`'s
    `trusted_instr_prop` is wrapped in `match Opcode.ofNat _ with
    | ...` that doesn't reduce until variant-zero substitutions are
    applied. Recipe: `simp [h_77, h_78, h_79, h_80, h_81,
    Opcode.ofNat, Nat.ble, h<N>_val] at reader_cstrs` (full simp,
    not `simp only`) — `Nat.ble` case-splits the opcode tree and
    the variant zeros pick the active arm. Need explicit
    `h<N>_val : (<N> : ZMod p).val = <N>` for the opcode literal
    (11 for MUL, 12 for MULH, 13 for MULHU, 14 for MULHSU, 24 for MULW).
  - `MulOperation.spec.<variant>_poly` requires `is_real = 1`
    (literal). The chip's CS0 has `is_real = Σ Main[77..81]`. Bridge
    with `rw [h_is_real_eq_one] at mul_op_cstrs`.
  - The `mop_of_mul_op {result_part := ..., signed_rs1 := ...,
    signed_rs2 := ...}` reduces to the matching `mop.<variant>` by
    `rfl`. Apply this rewrite BEFORE `← aw_eq` (which is in
    `execute_MUL_pure` form, matching the post-mop_of_mul_op-reduction
    goal).
  - `simp_all` collapses `Fact (2^17 < p)` to `Fact True`. Solution:
    derive `h_pc3 : Main[3].val < 65536` BEFORE `simp_all` runs, and
    skip the simp_all in the non-zero op_a branch.
  - `state_cstrs` after simp has shape `pc_read ∧ op_a_read ∧ op_b_read
    ∧ op_c_read` (4-tuple, NOT 5 with leading `_`).
  - For mulw, use `execute_MULW'` (no opcode arg) and skip the
    `mop_of_mul_op` rewrite entirely.

  **Mul Phase 3 op-level _poly commits (2026-05-05)** (7 commits):

  Phase 3 commits:
  - `9a9f17d`: `MulOperation.allHold_constraints_iff_is_real_poly`
    (op-level iff lemma, ~85 lines, mirror of Fin KB).
  - `cdf15ee`: `spec.mul_poly` + 5 `sum_eq_one_of_eq_one_*` op-level
    helpers + `U16toU8OperationSafe.spec.return_poly` (5-line
    wrapper around `spec.unsafe.return_poly`). Heartbeats 32M.
  - `b31aad5`: `spec.mulh_poly` + private `msb_to_isNegative_eq`
    helper (bridges MSB iff to `if isNegative_poly then 1 else 0`
    form, ~25 lines).
  - `79b6b7a`: `spec.mulhu_poly` (no sign-extend; like mul but high).
  - `17e9890`: `spec.mulhsu_poly` (signed × unsigned, mixed; reuses
    `msb_to_isNegative_eq` for b-side, direct h_c_sgn = 0 for c-side).
  - `085f055`: `spec.mulw_poly` + 4 BHWord `_poly` companions in
    `Word.lean` (`extend_poly`, `extend_U32_U64_poly`,
    `extend_true_is_signExtend_poly`, `extend_false_is_setWidth_poly`).
    The `extend_true_is_signExtend_poly` proof is a direct mirror of
    `BWord.extend_true_is_signExtend_poly` at smaller dimension via
    `BitVec.toInt_inj` + `BHWord.toBitVec32_poly_toInt_poly`. The
    spec.mulw_poly proof bridges `aw[2]/aw[3] = product_msb.msb * 65535`
    via `U16MSBOperation.spec_poly` on the post-substituted `aw[1]`,
    plus an `eq_cp` helper for cp_poly agreement between bbwe/cbwe
    (16-vec) and hbw/hcw (4-vec) at indices 0..3.

  Tactical wisdom from Phase 3:
  - The constraint compiler's `BWord.extend_poly w sgn` def has form
    `let ext := (if sgn then ... else 0) * 255 ; #v[..., ext, ext, ...]`.
    For sgn = true, it doesn't reduce to a literal; the proof
    leverages this: `rw [h_b_sgn]` substitutes `cols.b_sign_extend`
    with `if isNegative_poly bbw then 1 else 0`, which matches
    `extend_poly bbw true`'s definitional reduction. Avoid
    `simp only [zero_mul]` since it would break the match.
  - `pp_i'` 16-line ladder converts `cols.product[i] < 256` (ZMod)
    to `cols.product[i].val < 256` (Nat) via `val_256_zmod_p`.
    Required by `core_mul_poly`'s Nat-form premises.
  - `simp only [execute_MUL_pure_bw_poly]` reduces same-constructor
    equality (`mop.X = mop.X`) to `True` via internal lemmas, but
    leaves different-constructor equality opaque. So post-simp form
    has `decide (... ∨ True)` that needs explicit rewrite to `true`.
    The `decide_True` lemma doesn't exist by name; use
    `show (decide (...)) = true from by decide` directly.

  Mulw remaining: needs `BHWord.{extend_poly, extend_U32_U64_poly,
  extend_true_is_signExtend_poly}` in `Word.lean`. The
  `extend_true_is_signExtend_poly` proof should mirror Fin KB's
  recipe via `BitVec.toInt_inj` + `BHWord.toBitVec32_poly_toInt_poly` +
  `BWord.toBitVec64_poly_toInt_poly` (both already exist). Earlier
  attempt via Nat-level bridging failed; toInt route is correct.

  **Phase 5 deferred**: 4 chip-level `correct_<variant>_poly` in
  `MulChip.lean` (skip mulw). Each ~150 lines mirroring AddChip's
  `correct_add` pattern (chip cstrs flatten via simp +
  `obtain ⟨mul_op_cstrs, cpu_cstrs, reader_cstrs, b_77, b_78, b_79,
  b_81, b_80, sum_disj, h_M13⟩`, then `single_op_poly` + matching
  `sum_eq_one_of_eq_one_*` for variant zeros, then `ops_U64_b_c_poly`
  for U64 bounds, then `RTypeReader.allHold_constraints_iff_is_real_poly`
  for register bounds, then `MulOperation.spec.<variant>_poly`,
  bridge to monadic via `exec_MUL_pure_bv_to_bw_poly`). Plan
  `make-a-plan-to-goofy-oasis.md` was the active plan.

  **Mul Phase 0–2 groundwork landed 2026-05-04** (7 commits) and
  **carry-chain Phase landed 2026-05-04** (2 commits, `416ddb6` and
  `be52c86`): both `core_mulw_poly` and `core_mul_poly` are in. The 5
  `MulOperation.spec.<variant>_poly` lemmas + chip-level helpers +
  `correct_<variant>_poly` × 5 are the remaining work.
  - Phase 0 (`9db5462`): parametric emission for `Mul` and `MulOperation`
    — `update_constraints.py` PARAMETRIC_CHIPS/OPS dicts, struct lifted
    to `(F : Type)`, both regenerated. `maxHeartbeats 1M` on
    `allHold_constraints_iff_is_real` (KB) to absorb defEq overhead.
  - Phase 1a (`144c33e`): `cp_poly` cross-product foldl helper in
    `SP1Foundations/Word.lean` (companion to existing `cp`).
  - Phase 1b op-level (`41558f8`): `MulOperation.single_op_poly` (5-arm
    boolean cascade, takes the disjunctions + specialized `sum = 1`
    as inputs) + private `four_bools_sum_zero` helper (16 explicit
    cases via `linear_combination` + `congrArg ZMod.val + omega`).
  - Phase 2a (`c2fa12e`): chip-level `is_real_poly`, 5 `is_<variant>_poly`
    `@[simp]` defs, plus `sum_eq_one_of_eq_one_{left, 2, 3, 4, 5}`
    helpers (one per slot). Mirrors Bitwise's 3-arm extended to 5.
  - Phase 2b (`878332b`): chip-level `single_op_poly` — destructures
    `(constraints Main).allHold_poly` directly via `simp only
    [SP1ConstraintList.allHold_poly, constraints, List.forall_append,
    List.Forall, ..._assertZero, sub_eq_zero, mul_eq_zero]` (no chip
    iff_poly!). Constraint compiler emits boolean assertions in order
    `77, 78, 79, 81, 80` (mulw before mulhsu). Also normalized the
    `sum_eq_one_of_eq_one_*` helpers to match simp normal form
    `Σ = 0 ∨ Σ = 1` (sub_eq_zero rewrites `Σ - 1 = 0`).
  - Phase 2c (`fb6c769`): three trivial `sp1_op_*_poly` defs +
    `ops_U64_b_c_poly` extracting `isU64_poly` for both 64-bit operands
    via `RTypeReader.allHold_constraints_iff_is_real_poly`. The latter
    takes `h_is_real_eq_one : Main[77] + ... + Main[81] = 1` as input
    (chip's correct_*_poly will derive once via `sum_eq_one_of_eq_one_*`
    and thread through).
  - **Phase 1b carry chain landed 2026-05-04** (2 commits):
    - `416ddb6`: `core_mulw_poly` (4-byte) + `Fact (2^24 < KB)`
      instance in `SP1Foundations/Field.lean`. Recipe: per-limb Nat
      lift via `linear_combination` + `set L, R` Nat-cast bridge +
      `ZMod.val_natCast_of_lt`, telescope into single polynomial
      identity via `linear_combination` over ℤ after `zify`, BitVec
      bridge via `Nat.add_mul_mod_self_right`. Compiles in 100s.
    - `be52c86`: `core_mul_poly` (16-byte). Same recipe scaled to
      16 limbs. **Critical perf insight**: `nlinarith` doesn't scale
      past 4 limbs (took 30+ min and never finished); replaced with
      explicit `Nat.mul_le_mul (by omega) (by omega)` byte-product
      bounds + `omega`. Took 341s after that fix. The polynomial
      identity is stated in **factored form** directly (`+ (...) *
      2^128`), avoiding the heavyweight final `ring` rewrite that
      plagued the original draft. The 120 cross-product terms with
      `i + j ≥ 16` are factored under `* 2^128` since each is a
      multiple of `256^16 = 2^128`.
    - Both use `set_option debug.skipKernelTC true` to bypass kernel
      deep-recursion on `% 2^N` (precedent: AddrAddOperation).
    - Both require new `Fact (2^24 < p)` typeclass — byte-level
      carries give `prod[i].val + carry[i].val * 256 ≤ 2^24 - 1`,
      requiring `p > 2^24` for clean Nat lift.
  - **Phase 1c spec_poly remaining**: 5 `MulOperation.spec.<variant>_poly`
    lemmas — `spec.mul_poly`, `spec.mulh_poly`, `spec.mulhu_poly`,
    `spec.mulhsu_poly`, `spec.mulw_poly`. Each mirrors the existing
    Fin KB version line-by-line (~50-70 lines each, total ~250-350
    lines). Heavy `simp_all` calls in the original proofs may need
    targeted alternatives. Bridges needed:
    `U16toU8OperationSafe.spec.unsafe.return_poly` (exists),
    `BWord.toBWord_poly_toU64`, `BWord.toWord_poly_toBitVec64_poly`,
    `BDWord.low_as_extract_poly`, `BDWord.high_as_extract_poly`,
    `BDWord.isU128_poly_low_poly_isU64_poly` (exists),
    `BDWord.isU128_poly_high_poly_isU64_poly` (exists),
    `Word.toBWord_poly_isU64_poly` (likely needed),
    `BHWord.extend_U32_U64_poly`, `BHWord.extend_true_is_signExtend_poly`
    (verify exists). Allocate 8M heartbeats per spec.
  - **Phase 3 chip-level remaining** (deferred): `correct_<variant>_poly`
    × 5 in `MulChip.lean`, plus `register_bounds_poly` and
    `op_a_is_0_poly` bound-extraction helpers (mechanical ports of
    lines 146/162 in `Mul/Constraints.lean`). Plus 5 chip-level
    `spec.<variant>_poly` wrappers (counterparts of lines 222-294
    in `Mul/Constraints.lean`).
  - Plan file:
    `/home/devontuma/.claude/plans/make-a-plan-to-lovely-cascade.md`.
  - See `feedback_mul_iff_poly_complexity.md` for why a literal port
    of the chip-level iff doesn't close (bound-source mismatch).

  **Branch chip migration COMPLETE 2026-05-03** (commits `98a2852` →
  `2c96880`, 7 commits, ~1500 lines). All 6 arms (BEQ, BNE, BLT, BGE,
  BLTU, BGEU) have polymorphic correct_*_poly companions. Required
  infrastructure additions:
  - `pc_plus_4_eq_poly_chip` in `Branch/Constraints.lean`: variant of
    `pc_plus_4_eq_poly` accepting the chip's *natural* post-simp limb
    form `((eq form ∨ 65536 = 0) ∨ (a-b)*65536⁻¹ = 1)` produced by
    default simp's mul_eq_zero + inv_eq_zero + sub_eq_zero. Bridges to
    canonical and delegates to `pc_plus_4_eq_poly`.
  - `lt_65536_of_mul_inv_4_lt_poly` in `Word.lean`: ZMod p companion to
    the Fin KB version; needed for Main[25] bound extraction (chip's
    `Main[25] * 4⁻¹ < 16384` constraint).
  - `limb_lift_branch` made non-private (was private to Constraints.lean).
  - Branch chip's branching arm bridges its 4 limb hyps inline (4×
    `linear_combination + rw + ring`) before calling `branch_addr_eq_poly`,
    since adding a separate `branch_addr_eq_poly_chip` ran into
    paren-counting issues with the long chained-carry signature.

  **Branch chip recipe** (per-arm pattern):
  1. `single_op_poly Main cstrs` for variant-zero facts.
  2. `is_real_poly Main` from sub-opcode flag via `Or.inr × N`.
  3. `eq_signExtend_of_is_real_poly` + `add_signExtend_of_constraints_poly`
     for trusted_instr signExtend + `mul4_means_0_1_are_0` for
     low-PC-bits zero.
  4. Destructure cstrs into `⟨_, reader_cstrs, lt_cstrs, chip_cstrs⟩`
     via `simp [SP1ConstraintList.allHold_poly, Branch.constraints]`.
  5. `simp [ITypeReaderImmutable.constraints, h_is_X, ..., Opcode.ofNat,
     Nat.ble, h<opcode>_val] at reader_cstrs` to get bounds.
  6. Derive ZMod-side bounds `Main[k] < (32/65536 : ZMod p)`, then
     bridge to `Main[k].val < 32/65536` via `h32_val/h65_val`.
  7. Rewrite `is_real` and `is_signed` slots in `lt_cstrs` to literal 1
     and 0/1, then `LtOperationSigned.spec.branch_poly` →
     `spec_lt.1/2 rfl` for unsigned/signed case.
  8. Bridge BV equality/ordering to Word equality/Word.toInt_poly /
     Word.toNat_poly via `Word.toBitVec64_poly_toNat_poly` /
     `_toInt_poly` for isU64-bounded Words. The bridge is built
     INSIDE each by_cases arm to avoid simp-leakage that would
     transitivize iff hypotheses through `simp_all only`-style steps.
  9. `simp [SP1ConstraintList.initialState_poly, ...]` on state_cstrs,
     extract h_pc_read, h_op_a_read, h_op_b_read.
  10. `simp [spec_<op>, sp1_branch_poly, execute_BTYPE]; rw [run_readReg];
     simp [h_pc_read]; simp only [BitVec.ofNatLT_eq_ofNat] at h_op_a/b_read;
     simp [op_a, sp1_op_a_poly, h_op_a_read, ...]`.
  11. `by_cases` on appropriate condition (= for BEQ/BNE, .toInt < for
     BLT/BGE, .toNat < for BLTU/BGEU). The condition-rewriting uses
     `h_lt_ite` from `spec_lt.1/2 rfl`'s 3rd conjunct (the
     `if Word.toInt/Nat_poly < then bit = 1 else bit = 0`).
  12. Per-arm: derive `h_is_branching` (Main[34]) via `simp_all`,
     simp `chip_cstrs` with [h_is_branching, sub_eq_zero, ...flags...,
     ...variant_zeros...], destructure into 5-tuple `⟨h_limb0..3,
     h_bound_checks⟩`, derive Main[25/26/27].val < 65536 (the first
     uses `lt_65536_of_mul_inv_4_lt_poly` + `h14_val` rewrite to
     normalize `2 ^ ZMod.val 14` to 16384).
  13. Branching arm: bridge each h_limb to canonical
     `c = 0 ∨ c = 1` form via 4× rcases + linear_combination, then
     `branch_addr_eq_poly`.
  14. Non-branching arm: pass h_limbs directly to `pc_plus_4_eq_poly_chip`
     (which accepts the natural form and bridges internally).
  15. Use the unfolded form `BitVec.signExtend 64 (BitVec.ofNat 13
     Main[21].val)` (NOT `BitVec.signExtend 64 imm`) when defining
     h_addr_eq, since the goal has the unfolded form after the
     `simp only [show imm = ... from rfl]` step.

  ~250-line per-arm proof with ~40% boilerplate (cast lemmas, bound
  extraction, limb bridges) and ~60% structural reasoning. Could be
  factored into shared helpers if chip count grows (each variant's
  if-condition + Main[34] derivation is the only differentiator).

  **Branch foundation landed 2026-05-03** (commits `3ce2234`,
  `f6023ba`): `branch_addr_eq_poly` + `pc_plus_4_eq_poly` paired
  helpers in `SP1Chips/Branch/Constraints.lean`. Both mirror
  `AddrAddOperation.spec_of_constraints_poly` recipe.

  **Track B post-mortem (kept for context):** initial Track B attempt
  (using `(constraints Main).allHold_poly (p := KB)` ascription with
  Fin KB-bound chip auto-gen) was blocked by `List.forall_append`
  failing to unify `+++` at `Fin KB` with outer `List.Forall` at
  `ZMod KB`. Track C1 (chip auto-gen lifted to parametric F) resolves
  this structurally. Both `SubOperation.spec_poly` and
  `RTypeReader.allHold_constraints_iff_is_real_poly` landed in Track B
  prep and are load-bearing for the C1 chip migration.
- **`Fin KB` deletion sweep** not started.
- **No second concrete prime** instantiated; BabyBear / Mersenne31
  remain forward-guidance.

**Recommended next steps** (Tracks A/B/C in the doc):

- **Track A**: ✅ complete.
- **Track B**: ⚠ piloted 2026-05-01, BLOCKED at destructure step
  (Fin KB vs ZMod KB instance mismatch in `+++`). Pivoted to C1.
- **Track C1**: ✅ pilot + 5 follow-on chips landed 2026-05-01/02.
  `update_constraints.py` extended with `PARAMETRIC_CHIPS` dict
  (currently `{Add, Addi, Addw, Sub, Subw, UType}`). 17 chips remain.

  **Chip difficulty taxonomy** (informed by 2026-05-02 attempts on Jal):
  - **Easy (uses reader iff_poly):** Sub/Add/Addi/Addw/Subw (R/I/ALU
    type) and UType (J-type). Direct mirror of SubChip recipe; ~30-60
    min per chip after readers + ops are `_poly`-ready.
  - **Medium-easy (precomputed iff_poly cluster):** Lt — 4 hand-written
    `allHold_constraints_iff_*_poly` lemmas in `Lt/Constraints.lean`
    (commit `c133022`) plus the LtOperationSigned spec_poly cluster from
    Track A made the chip migration mechanical. ~1 session for all 4
    arms; needs result-bit bridge (toBitVec64_poly of if-then-else)
    not present in Sub/Add but trivial to write.
  - **Hard (was Hard — now landed 2026-05-02/03):**
    - **Jal** ✅: Used `val_mod_4_eq_zero_iff_zmod` bridge (lives in
      `Field.lean` now); `set_option debug.skipKernelTC true` for the
      `% 2^64` recursion. PC arithmetic via two `AddOperation.spec_poly`
      chains.
    - **Jalr** ✅: PC mask logic ported via local sub-lemmas using
      `Word.toBitVec64_poly_mod4` simp + `bv_decide` after `generalize`.
      ZMod sub wrap analysis goes through `val_sub_cases` (Field.lean)
      under the chip's `(M[26]-M[34]).val < 65536` aligned-low-limb
      constraint, which lets the wrap branch be ruled out by contradiction
      with `Fact (2^17 < p)`. The `iff_is_real_poly` for ITypeReader
      surfaces a generic `op_b < 65536`; need to additionally unfold
      `Opcode.trusted_instr_poly` (with opcode-val helper for 47) to
      extract the JALR-specific `op_b < 32` from the i_type_constraints.
  - **Medium (extra hand-written infrastructure):** Lt (4 hand-written
    iff_polys × 4 correct_* arms); Bitwise (similar shape, 6 arms);
    Branch (uses ITypeReaderImmutable which lacks `_is_real_poly`).
  Per-chip opt-in: add chip name to `PARAMETRIC_CHIPS`, regen, restate,
  follow recipe in `docs/FIELD_GENERIC.md` "Track C1 — SubChip
  migration landed 2026-05-01" + tactical patterns in
  `feedback_chip_migration_tactics.md`. ~15–60 min per chip after the
  Subw/Addw HWord/sign-extend foundation; cheaper for chips that reuse
  R/I/ALU-type reader + an existing `_poly` op.
  Reader-coverage state: **all 5 readers** (CPUState, RTypeReader,
  ITypeReader, ALUTypeReader, JTypeReader) now have `_is_real_poly`
  companions (last one — JType — landed 2026-05-02). All 5 readers
  also have `_poly` iff. Operation `_poly` `spec_poly` coverage:
  Add/Sub/Addw/Subw done; missing: AddrAdd, U16toU8Safe, Mul, Mulw,
  shift ops, divrem ops, branch helpers (Lt has spec.signed_poly +
  spec.unsigned_poly + spec.branch_poly already).
- **Track C2**: deletion sweep + BabyBear instantiation — defer until
  more chips are migrated and the recipe is validated across chip
  variants (R-type / I-type / J-type / ALU-type / Branch / Load-Store).

**How to apply:** when picking up this work, start by re-reading
`docs/FIELD_GENERIC.md` "Current state — 2026-05-01" — that's the
authoritative entry point. Don't re-derive status from the chronological
log unless a specific historical question requires it. When adding new
chips/ops, the auto-gen pipeline (`update_constraints.py` post-processor)
handles the `Fin KB` vs `(F : Type)` parametric emission via
`PARAMETRIC_OPS`. Hand-written iff lemmas should mirror the existing
patterns: state at `Fin KB`, prove with mathlib field tactics; add a
`_poly` companion using `SP1Constraint.toProp_poly` and the polymorphic
inverse-bridge primitives in `Field.lean`. Don't add new
`KoalaBear.foo`-style namespace-qualified calls — none currently exist;
reach for root-scope simp lemmas instead.

The `KoalaBear` namespace itself is **kept**: load-bearing concrete
instances (`Field (Fin KB)`, primality fact, 11 high-priority arithmetic
instances perf-critical per `docs/PERF_PATTERNS.md`) and literal-side
bridge lemmas that translate between symbolic `(N : Fin KB)⁻¹` form and
precomputed literals required by some omega proofs.

**Do not pursue the global `Fin KB` → `ZMod KB` rename** (Sub-phase B
Step 3, 2026-04-26, reverted): mathlib's instance graph for `ZMod p`
reaches `Zero`/`MulZeroClass` through `CommRing` while
`inv_mul_eq_one₀` reaches it through `GroupWithZero`; these don't unify
in Lean's discrimination tree. The current `Field (Fin KB) :=
ZMod.instField KB`-via-Fin architecture is well-designed for the
typeclass-graph concerns. See `docs/FIELD_GENERIC.md` "Sub-phase B —
Step 3 attempt" for the full investigation.
