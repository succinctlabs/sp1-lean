# Lean 4.31 + Sail environment notes

These are the current migration notes for the shared Lean/Sail dependency graph.

## Current local migration pins (2026-07-16)

- the root builds the entire dependency graph with `leanprover/lean4:v4.31.0`; root mathlib is `v4.31.0`;
- Clean is local `../clean` at `8e6ce748` (`origin/bump-lean-4.31`);
- `sail-riscv-lean`, `riscv-lean`, and `lean-sail` are local path dependencies while their 4.31
  changes are validated under the root toolchain. Their standalone `lean-toolchain` files still say 4.30
  and are part of the unpublished local migration delta; update and validate those before publishing pins;
- PolyFun is pinned to PR #34 head `502582b4bf51cddac166d3faed9ee2bfa5a2b7cc` and is used only for
  the native semantic-machine/run interface.

Restore immutable git pins before merging the migration PR. Do not run bare `lake update`: it can
rewrite all transitive pins and obscure which dependency introduced a toolchain change.

### Generated Sail 4.31 code-generation panic

Lean 4.31 emits a large LCNF panic cascade for the generated `LeanRV64D/Defs.lean` when that file opens
with `noncomputable section`, even though its declarations are computable. Removing the unnecessary
section marker makes the complete generated file compile and code-generate cleanly; this is the local
one-line Sail delta to upstream or regenerate, not a kernel bypass. Never use `skipKernelTC` as a
workaround.

## Historical reason for the independent tree

`sp1-lean` pins the **succinctlabs Clean fork v6.2.2 on Lean 4.29**, which ships **broken**
`Clean.Table.Inductive`, `Clean.Types.U32`, and `Clean.Gadgets.Addition8.Addition8FullCarry` (the last with a
`sorry`) — transitively breaking the `FemtoCairo` example this project models its chips on. The original
Lean 4.28 setup let us use Clean **main**, where the full feature set compiled: `FormalCircuit`, `GeneralFormalCircuit`
(+ `ProverData`/`ProverHint`), `FormalAssertion`, `subcircuit`/`witnessVector`, `FormalTable`,
`InductiveTable`, `Gadgets.ToBits.rangeCheck`, and `FemtoCairo`. That history no longer constrains the
current 4.31 migration.

## The `lake update` toolchain-bump trap

`lake update` follows dependency manifests and can silently replace the reviewed local/pinned graph.
During this migration, use explicit target builds under the root toolchain and update one dependency pin
at a time.

## The Clean-main ↔ Batteries import collision (RESOLVED upstream 2026-06-26)

**Status: no longer a forcing constraint.** The merged-`main` re-pin (`2c20f7f0`, roadmap W9) includes Clean
commit `d25bba8d` "Avoid Fin fold lemma clash with Batteries", which **deletes** Clean's own
`Fin.foldl_eq_foldl_finRange` from `Clean.Utils.Misc` (Clean now `import`s Batteries' `Fin.Fold` directly in
`Gadgets/Keccak/Permutation.lean`). So the duplicate-declaration clash below can no longer occur, and the
import narrowing is **no longer required for correctness**.

We nonetheless **keep** the narrow imports: they are also the project's deliberate narrow-import compile
strategy (a full `import Mathlib` in foundational `Math/Misc.lean` would propagate the whole of Mathlib
transitively to every downstream module). Re-widening to full `import Mathlib` is therefore a compile
regression, not a cleanup — left as a non-goal. (If a specific narrowed file needs an extra instance such as
`LT (ZMod p)`, widen *that* file's import minimally rather than restoring full Mathlib project-wide.)

**Historical symptom (pre-`d25bba8d`).** Public Clean `main`'s `Clean.Utils.Misc` and Batteries both declared
`Fin.foldl_eq_foldl_finRange`. The wider Clean surface (pulled via `Clean.Gadgets.Bits`) clashed with the Sail
side's full `import Mathlib` (which reaches `Batteries.Data.Fin.Fold` through the `Topology/Subpath` corner).
The fix was to narrow the Sail-side files (`Math/Misc.lean`, `Register.lean`, `SailWrap.lean`, and the
`Faithful/*` anchors) to **only** `import Mathlib.Tactic` + `Mathlib.Data.ZMod.Basic` + `Std.Data.ExtDHashMap`
— none of which reach `Batteries.Data.Fin.Fold`. `Clean.Circuit.Basic` + full Mathlib never clash; only the
wider Clean gadget surface did. With the narrowing, the unified `lake build SP1Clean` is 0/0 with both the
gadget half and the Sail half co-imported.

A practical consequence: the narrowed files don't have `LT (ZMod p)` and similar in scope — e.g. a faithfulness
anchor that only sends `Range` should trim `ByteOpcode.constrain`'s `< 256` cases to `_ => True` rather than
pull a wider Mathlib import back in.

## Sail facts that survive (reusable)

- `SailM` and `SailState` come from `LeanRV64D` (`SailState = PreSail.SequentialState RegisterType
  Sail.trivialChoiceSource`). `Register` / `bitVecToRegidxVal` were ported into `Model/Register.lean`.
- `readReg`/`writeReg` are `PreSail.readReg`/`PreSail.writeReg` (namespace **`PreSail`**, not `Sail`), tagged
  `@[simp_sail]`. `Sail.run_readReg` will **not** fire — unfold `PreSail.readReg, PreSail.writeReg` in `simp`
  instead (the `run_rX_bits`/`run_wX_bits` lemmas do fire).
- For ADD, `execute_RTYPE_pure x y .ADD = x + y` definitionally (no `pure_w`/`bv_to_w` plumbing needed);
  `execute_RTYPE_pure x y rop.AND = x &&& y` (and OR/XOR) by `rfl`. The PC is modeled as `BitVec 64` (no limb
  arithmetic) in the bridges.

## Sail memory model (read + write — `Model/SailMemory.lean`)

The memory chips (`LoadDouble`/`StoreDouble`) need the Sail RAM semantics, not just register/PC. These were
**ported natively** from `../sp1-lean`'s `SP1Foundations/MemChecks.lean` into `Model/SailMemory.lean`
(namespace `SP1Clean.SailMem`), against the **shared** `LeanRV64D` model — the dense Sail-monad `simp`
sets transfer almost verbatim. What's there:

- **Config + PMA** — `SailState.isValidMemConfig` (Machine priv, MPRV off `mstatus[17]=0`, Zicfilp
  landing-pads off `mseccfg[10]=0`, **pointer-masking off `mseccfg[33:32]=0`**, htif tohost unset, the SP1
  PMA region), `SP1_PMA`/`SP1_PMA_Region`, `range_subset_sp1_pma`, `is_aligned_vaddr_iff_mod`, and the
  MMIO-readable/writable lemmas.
  - **Platform trust disclosure (`h_mseccfg_pmm`, added during the 4.30 / sail@`793034f3` update).** The
    newer Sail generation added **pointer masking (PMM)**: `transform_effective_address` now masks the addr
    by `mseccfg[33:32]` (`0b01` *throws*), and `is_pmm_applicable` is unconditional for M-mode data — no
    fork toggle exists. So `isValidMemConfig` gained `h_mseccfg_pmm` (PMM disabled ⇒ transform = identity ⇒
    the existing memory-lemma proofs close). This is a **new platform assumption in the trust base**, faithful
    (SP1 has no pointer masking), consistent with the existing CLINT-off / MPRV-off / `mseccfg[10]=0` / PMP=0
    assumptions; it is a *bridge-level hypothesis on the assumed initial config* (a clause of the boot
    predicate), not a Sail axiom. Threaded through the 10 memory-bridge transfer sites + the
    `SailConfigured`/`toValidMemConfig` construction sites.
- **Read** — `run_vmem_read_of_width_8'` (8-byte aligned read returns the eight `mem[addr+k]` bytes),
  with `run_checked/run_mem_read_eight_bytes_of_isInitialized`.
- **Write** — `run_vmem_write_of_width_8` (8-byte write produces the post-state with eight `mem.insert`s of
  `BitVec.ofNat 8 (data.toNat >>> 8·k)`), with `run_checked/run_mem_write_value_eight_bytes_of_isInitialized`.

Fork adaptations (vs sp1-lean): this `LeanRV64D` reads `htif`/`mstatus` via `s.regs.get?` directly, so the
proofs use `Std.ExtDHashMap.get?_eq_some_get`/`effectivePrivilege` + an `extractLsb … = 0#1` MPRV bridge
instead of sp1-lean's `run_readReg_of_isInitialized`; `run_vmem_write_of_width_8` needs an extra
`rw [show extractLsb data 63 0 = data]` before `conv_lhs => rw [h]` (the fork's `vmem_write_addr`
re-extracts the data argument). The target lakefile does not disable `linter.unusedSimpArgs`, so the ported
simp lists were trimmed.

The bridges (`Proofs/Chips/{LoadDouble,StoreDouble}Chip/Bridge.lean`) take the register reads + the memory bytes + the
alignment/fits/range facts as **hypotheses** (the `AddBridge` philosophy — the bus supplies them), so
`correct_{load,store}_double_native` is `(spec).run s = (sp1).run s`. The `execute_STORE` Sail signature is
`execute_STORE imm rs2 rs1 width` (**rs2 before rs1** — the stored-value register first). Axiom profile = the
base trio + `LeanRV64D` platform constants (`{load,match}_reservation`, `plat_term_write`,
`sys_enable_experimental_extensions`) + bv_decide's `Lean.ofReduceBool`/`Lean.trustCompiler` (a `native_decide`
on `plat_clint_base`); **no `sorryAx`**.

## When the toolchain is next touched

When changing a dependency, re-check the exact manifest revision, build the generated Sail model with
code generation enabled, and confirm that all local siblings use 4.31. Finish with a full
`lake build SP1Clean`; the single-file command can conceal stale oleans or stack-overflow exits.
