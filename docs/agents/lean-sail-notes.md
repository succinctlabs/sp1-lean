# Lean 4.28 + Sail environment notes

The whole reason this project exists as a separate tree is the toolchain. These are notes on the 4.28 + Sail
environment, relevant when touching deps, imports, or the Sail side.

## Toolchain pins (do not bump)

- `lean-toolchain`: `leanprover/lean4:v4.28.0`.
- mathlib: `v4.28.0` (public).
- Clean: `github.com/Verified-zkEVM/clean @ 292b9cc3` (public, **non-fork**) — the head of
  [PR #398](https://github.com/Verified-zkEVM/clean/pull/398) (native gated channels), pinned by SHA
  while the PR is in review (W9, 2026-06-10). **Re-pin to the merge commit once it lands on `main`**;
  that re-pin also picks up `d25bba8d` ("Avoid Fin fold lemma clash with Batteries"), which likely
  retires the import-narrowing workaround below — re-test the collision then.
- Sail: two `github.com/succinctlabs/*` deps pinned to the **`dtumad/clean-native`** branch —
  `sail-riscv-lean` (the generated `LeanRV64D` model) and `riscv-lean` (the `RISCV` ISA fns) — which
  transitively pull the `rems-project/lean-sail @ v4` runtime. Each carries its own 4.28 `lean-toolchain`.
  All are fetched by `lake build`; **none is a local sibling checkout** (an earlier setup used local
  `../lean-sail-428` / `../sail-riscv-lean-428` copies — that is no longer the case).

## Why public Clean `main` + 4.28

`sp1-lean` pins the **succinctlabs Clean fork v6.2.2 on Lean 4.29**, which ships **broken**
`Clean.Table.Inductive`, `Clean.Types.U32`, and `Clean.Gadgets.Addition8.Addition8FullCarry` (the last with a
`sorry`) — transitively breaking the `FemtoCairo` example this project models its chips on. Reverting to Lean
4.28 lets us use Clean **main**, where the full feature set compiles: `FormalCircuit`, `GeneralFormalCircuit`
(+ `ProverData`/`ProverHint`), `FormalAssertion`, `subcircuit`/`witnessVector`, `FormalTable`,
`InductiveTable`, `Gadgets.ToBits.rangeCheck`, and `FemtoCairo`. User directive: public (non-succinctlabs)
Clean + mathlib; Sail pinned on the `succinctlabs/* @ dtumad/clean-native` 4.28 branches.

## The `lake update` toolchain-bump trap

`lake update` bumps the project to the **max** toolchain declared by any dependency. A single 4.29 dep
would silently drag the whole project to 4.29 (and back onto the broken Clean fork). The fix that keeps us on
4.28: the `dtumad/clean-native` Sail branches carry a **4.28** `lean-toolchain`. The Sail RISC-V model +
runtime are mathlib-free and build verbatim on 4.28 — only the toolchain file changed. With all deps
declaring 4.28, `lake update` does not bump, and `lake build SP1Clean LeanRV64D` is 0/0.

Both `LeanRV64D` and `RISCV` (`riscv-lean`) are now required and wired in `lakefile.toml`; the
`dtumad/clean-native` branch of `riscv-lean` carries the 4.28 fixes (3 trivial errors — redundant
`rfl`/`congr` after `simp`) so it builds clean alongside the rest.

## The Clean-main ↔ Batteries import collision (and the fix)

**Symptom.** Public Clean `main`'s `Clean.Utils.Misc` and Batteries both declare
`Fin.foldl_eq_foldl_finRange`. The wider Clean surface (pulled via `Clean.Gadgets.Bits`) clashes with the Sail
side's full `import Mathlib` (which reaches `Batteries.Data.Fin.Fold` through the `Topology/Subpath` corner) —
a genuine upstream Clean-main bug (absent on the succinctlabs/4.29 combo, which instead has the broken
`Table.Inductive`).

**Fix.** Narrow the Sail-side files (`Math/Misc.lean`, `Register.lean`, `SailWrap.lean`, and the
`Faithful/*` anchors) to **only** `import Mathlib.Tactic` + `Mathlib.Data.ZMod.Basic` + `Std.Data.ExtDHashMap`
— none of which reach `Batteries.Data.Fin.Fold`. `Clean.Circuit.Basic` + full Mathlib never clash; only the
wider Clean gadget surface does. With the narrowing, the unified `lake build SP1Clean` is 0/0 with both
the gadget half and the Sail half co-imported.

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

- **Config + PMA** — `SailState.isValidMemConfig` (Machine priv, MPRV off, mseccfg/htif off, the SP1 PMA
  region), `SP1_PMA`/`SP1_PMA_Region`, `range_subset_sp1_pma`, `is_aligned_vaddr_iff_mod`, and the
  MMIO-readable/writable lemmas.
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

If you ever add a dep or bump a version, re-check: (1) does `lake update` try to bump past 4.28? (2) does the
Clean-main `Fin.foldl` collision resurface (did a file widen its imports)? (3) do the `dtumad/clean-native`
Sail branches still carry a 4.28 `lean-toolchain`? Finish with a full `lake build SP1Clean` (the `lake env lean` single-file check
lies on stack overflow — see proof-patterns.md).
