# Porting recipe — adding a new chip

A checklist for porting one SP1 instruction/operation into the four-artifact chain. The two complete templates
are **Add** (carry arithmetic) and **Bitwise** (byte-level via `ByteXorTable`); clone whichever is closer.
Read `../architecture.md` first for what each artifact is, and `proof-patterns.md` for the proof skeleton.

## Reference sources (read-only)

- Rust spec oracle: the `sp1` checkout at the `$SP1_DIR` env var (default `../sp1`) — the operation's
  constraint fragment lives under `crates/.../operations/<op>.rs`; copy it **verbatim** into the `Faithful/`
  anchor.
- sp1-lean (4.29, a read-only porting reference, not imported): the `sp1-lean` checkout,
  `SP1Operations/Operation/<Op>/…` and `SP1Chips/<Op>/…` — the `spec`/`spec_inv`/`allHold_constraints_iff`
  to **re-derive natively** here rather than borrow.

## Steps

### 0. Foundations
If the op needs a helper not yet in `Foundations/` (a reassembly lemma, a byte/limb split, a field literal like
`val_256_*`), add it to `Foundations/Word.lean` or `Foundations/Bitwise.lean` first — it's shared by every
future chip. Keep these files axiom-clean.

### 1. `Operations/<Op>Operation.lean` — witnessed gadget
- Namespace `SP1Clean.<Op>Operation`. Variable block `{p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]`.
- `main`: witness the result limbs/bytes; impose byte/range checks as **`byteChannel` pulls**
  (`byteChannel.pullIf input.is_real ⟨opcode, is_real * value, width, 0⟩`, `Foundations/Channels.lean`)
  — the single shared byte foundation, faithful to SP1's `send_byte`. The legacy local-column
  `Gadgets.ToBits.rangeCheck` / `ByteXorTable` + opcode-selected Lagrange pattern is **superseded** (kept
  only in `BitwiseU16Operation`, which can't compose the byte-level op — FormalCircuit duality). See
  `proof-patterns.md` for the pull recipe and the sub-gadget composition rule below.
- `RawSpec` (carry-bool/range or per-byte form), the `*_of_<raw>` / `<raw>_of_*` cores, the semantic `Spec`,
  `soundness`, `completeness`, and `circuit : FormalCircuit`.
- Verify: `#print axioms <Op>Operation.circuit` is clean.

### 2. `Chips/<Op>Chip/{Defs,Formal}.lean` — `GeneralFormalCircuit`
(`Defs.lean` holds the `Inputs` struct, `main`, and the `ElaboratedCircuit` instance; `Formal.lean` imports
`Defs` and holds `Assumptions`/`ProverAssumptions`/local `Spec`/helper lemmas/soundness/completeness/`circuit`.)
- `Inputs` struct (`deriving ProvableStruct`) — the committed `state` (`Extracted.CPUState`) and `adapter`
  reader blocks as **threaded inputs**, operand words + `is_real` (+ `opcode` if multi-variant).
- `main` composes **three** subcircuits — `Readers.CPUState.circuit`, the `<Op>Operation` gadget, and the
  **register adapter reader** — then `is_real * (is_real - 1) === 0`; `return` the assembled extracted col
  struct. Pick the adapter reader by SP1's faithful adapter type:
  - pure R-type (scalar `op_c`, no immediate; e.g. Add/Sub) → `Readers.RTypeReader.circuit`, `adapter :
    Extracted.RTypeReader`;
  - immediate-capable ALU op (`op_c : Word` + `imm_c`; **Lt, Bitwise, Shifts, Addw**) →
    `Readers.ALUTypeReader.circuit`, `adapter : Extracted.ALUTypeReader`. Its op_c register access is gated
    `is_real - imm_c`.
  - I-type (one source register rs1 + immediate; **JALR**, loads) → `Readers.ITypeReader.circuit`, `adapter :
    Extracted.ITypeReader` (op_a write, op_b = rs1 read, op_c the immediate `op_c_imm`);
  - J-type (rd write + two immediates, no source register; **JAL**, AUIPC) → `Readers.JTypeReader.circuit`,
    `adapter : Extracted.JTypeReader`.
- **Control-flow variant.** A jump/branch chip commits a *data-dependent* `next_pc` instead of `pc + 4`: feed
  `Readers.CPUState.circuit` the computed target (an `AddOperation.value`, not `[pc[0]+4, pc[1], pc[2]]`), and
  add the SP1 alignment send (`Range(next_pc[0]/4, 14)`). JALR also commits an `lsb` witness
  (`witnessField (fun env => ↑((env add_value[0]).val % 2))`, +1 to `localLength`) with a binary gate, and
  feeds CPUState the **LSB-cleared** limb `add_value[0] - lsb` (RISC-V's `& ~1`). The `Spec` adds the gated
  jump/link `toBitVec64` identities (mirror `Chips/JalChip.lean` / `Chips/JalrChip.lean`).
- `elaborated` (`localLength`, channel lists — propagated from the subcircuits), `Assumptions`/`Spec`
  (semantic, `is_real`-gated, via `Specs/Chip.lean`'s `RTypeChipSpec` builder), `ProverAssumptions`/
  `ProverSpec`, `soundness` (`circuit_proof_start [RTypeChipSpec]`), `completeness`, `circuit`.
- Mirror `Chips/AddChip.lean` for a `FormalAssertion` gadget (reader composition + `witnessVector populate`
  + the `RTypeChipSpec` soundness recipe), or `Chips/BitwiseChip.lean` for a witnessing `FormalCircuit`
  gadget (`subcircuit <Op>Operation.circuit` returning the gadget output directly).

### 3. `Chips/<Op>Chip/Bridge.lean` — native Sail bridge
(imports `Chips/<Op>Chip/Formal`.)
- Narrowed imports (see LEAN_SAIL_NOTES — `Mathlib.Tactic` + `Mathlib.Data.ZMod.Basic` + `Std.Data.ExtDHashMap`).
- `spec_<op>` (RISC-V Sail execution via `SailWrap`), `sp1_<op>` (writes
  `toBitVec64 (<Op>Operation.resultWord …)`), and `correct_<op>_native` sourcing the identity from the chip's
  `Spec`. For multi-variant ops, one `<op>_chip_reaches_sail_<variant>` per opcode (extract the right `Spec`
  conjunct, close with `rw […]; rfl`). If `SailWrap` lacks the needed `execute_*`, add the wrapper there.
- **Register the `Soundness.ChipKind kind`** (≈12-line block, template `Chips/AddChip/Bridge.lean:92`) — the
  single value that enters the op's rows into the heterogeneous trace + soundness capstone with **no central
  edit**. Set `name := "<SP1 MachineAir::name>"` (the chip's `name()` in `../sp1`, e.g. `"Add"`); its `view`
  projects the adapter through `cols.adapter.toAdapterView` (so an `ALUTypeReader` row and an `RTypeReader`
  row populate the same reader-agnostic `Trace.AdapterView`); `reaches_sail` is the `<op>_chip_reaches_sail`
  lemma applied verbatim.

### 3b. Wire the chip into the registry + coverage table
- Add the `kind` to `Soundness/ChipRegistry.lean`'s `allChipKinds` and bump `allChipKinds_length` (N→N+1).
- Add a `CoverageEntry` to `Soundness/Coverage.lean`'s `coverage` (the chip, its SP1 opcodes, and the
  `RdGuard`), in `allChipKinds` order — `coverage_kinds_eq_registry`'s `rfl` enforces the orders match. Update
  `wiredNames`/`completeChipNames` (if its `circuit.completeness` is sorry-free) and the routing cascades in
  `routeOf`/`routeName` (mirroring SP1's `tracing.rs` arm); the `by decide` ledger guards re-check the rest.
- A heterogeneous trace mixing the new op with Add/Sub then rides the gated capstone via `allChipsTrace`
  (`Soundness/AllChips.lean`) + `gatedExecution_allChips` (`Soundness/GatedVm/Bridge.lean`).

### 4. `Faithful/<Op>.lean` — constraint anchor
- Import the generated `Extracted/<Op>` and the shared datatype (`Foundations/SP1Constraint.lean`:
  `ByteOpcode`, `Interaction`, `SP1Constraints`); `open scoped SP1Clean.ConstraintCoe`. Do **not**
  re-create the datatype — it is project-wide now. If `<Op>` emits a `ByteOpcode` whose `constrain` is still a
  `True` stub, replace the stub with its real meaning in `Foundations/SP1Constraint.lean`.
- Prove `<op>_constraints_faithful : (<Op>Operation.constraints …).allHold ↔ <Op>Operation.RawSpec …`.
  `allHold` unfolds to `List.Forall (· = 0) c.asserts ∧ List.Forall Interaction.toProp c.interactions`; the
  simp staples are `SP1Constraints.allHold`, `List.Forall`, `Interaction.toProp_send_byte`, the
  `ByteOpcode.ofNat_*`/`constrain_*` lemmas, and `bool_iff`. The split groups asserts and interactions into two
  clauses, so a trailing `tauto` (or `ring_nf; tauto`) reassociates where `RawSpec` interleaves them.
- For a **composed** op, split with `SP1Constraints.allHold_append` and collapse each `is_real = 1`-gated
  sub-list via its own anchor (keeps the residual `tauto` small) — see `Faithful/{Addw,LtOperationSigned,
  IsZeroWordOperation}.lean`.
- `NeZero p` via `⟨(Nat.Prime.pos Fact.out).ne'⟩`; `omit [Fact (2^17 < p)] in` if unused;
  `set_option linter.unusedSimpArgs false in` *before* the doc-comment if needed.

### 5. Wire + verify
- Add all four imports to the root `SP1Clean.lean`.
- `lake build SP1Clean` → **0 errors / 0 warnings** (see build-concurrency rules in AGENTS.md; kill stale
  builds first).
- Axiom-check every headline theorem (`lean_verify` or `#print axioms`): only
  `[propext, Classical.choice, Quot.sound]` (+ `Lean.ofReduceBool`/`trustCompiler` if `bv_decide` was used),
  **no `sorryAx`**.

## Scope notes

- Register/memory reads and the PC next-state are **native readers** now: the chip composes
  `Readers.CPUState.circuit` + the register adapter reader (`RTypeReader`/`ALUTypeReader`) as subcircuits
  (§2). The trace-level bus projections (`Soundness/{State,Program,Memory}Consistency.lean`) read a
  **reader-agnostic `Trace.AdapterView`** that every reader projects into via `<Reader>.toAdapterView`
  (R-type ⇒ `op_c := #v[op_c,0,0,0]`, `imm_c := 0`; the op_c memory pair and Program tuple then degenerate
  to the scalar shape). `ProgramChip.ProgramRow` carries `op_c : Word` + `imm_c` to match. The cross-row
  links (PC chain, offline-memory) stay threaded honest assumptions (`TraceStateLink`/`TraceMemoryLink`).
- **`x0`-destination / result-discarding chips (the `AluX0` variant).** SP1 routes any instruction writing
  `x0` to a dedicated chip (loads → `LoadX0`, ALU ops → `AluX0`); `Coverage.routeOf` keys on
  `(opcode, rd == x0)`. Such a chip has **no arithmetic gadget** (the result is discarded) — it composes only
  `CPUState` + the *immutable* adapter reader (op_a a source **read**: `Readers/ALUTypeReaderImmutable.lean`
  or `ITypeReaderImmutable`, with `op_a_0 * prev_value_i = 0` read-zeroing, no `wv*`) + any range checks +
  the `op_a_0` forcing gates (`is_real*(op_a_0-1) = 0`, `(is_real-1)*op_a_0 = 0`). **The Sail bridge is
  trivial and axiom-clean:** `sp1_<chip> pc` just advances `nextPC`; since `execute_<family> rs2 rs1 0#5 op`
  ends in `wX_bits 0#5 result` and `run_wX_bits` collapses a write to `x0` to a no-op **regardless of the
  result**, one *generic* family-core lemma per Sail instruction family (RTYPE/RTYPEW/ITYPE/MUL/MULW) proves
  `spec_<op> ≡ sp1_<chip>` for *every* opcode — **no `execute_*_pure = RV64.*` result-correctness lemma
  needed** — and `ChipKind.sailEquiv` is the ungated N-way conjunction. The register reads (`h_rs1`/`h_rs2`)
  only make the Sail reads *succeed*; their values are discarded. If SP1's adapter call is a plain method
  (e.g. `eval_op_a_immutable`), not an `SP1Operation`, the reader is **inlined** in the extracted
  `asserts`/`interactions` (no `<Reader>.asserts` sub-call), so the `Faithful/` anchor discharges it directly
  with the `Faithful/ALUTypeReader.lean` simp-set rather than `rw`-ing a fragment anchor. `Chips/AluX0Chip/`
  is the worked example.
- **Sub-gadget composition rule (the Mul `output_eq` / mid-struct offset hazard).** *Prefer* composing a
  shared sub-gadget as a `localLength-0` `FormalAssertion` with the chip witnessing the small output (the
  Lt/Bitwise/Addw idiom — it dodges the hazard entirely). A *witnessing* `FormalCircuit` subcircuit
  (`localLength > 0`) whose output is a **non-last** struct field desyncs offsets (`varFromOffset` strides by
  struct *size*, `subcircuit` consumes full *localLength*), making the default `output_eq` false — place such
  a subcircuit **last** in the return struct, or supply a custom offset-based `output`. This bites Mul/Div
  (compose witnessing `U16toU8`); Lt does **not** (composes `U16Compare` as a `localLength-0` assertion).
- **Shifts (SRL/SRA/SRLW/SRAW), in progress as a *chip skeleton* (no operation gadget).** SP1 inlines the
  limb decomposition of the register read into the chip asserts, so `ShiftRightChip` is a skeleton: `main`
  emits the ~58 inline `=== 0` asserts + 9 byte-range pulls, the semantic flag-gated `Spec` is in
  `Specs/Chip.lean`, and the native arithmetic is ported into `Operations/ShiftRightMath.lean` (all four
  variant `*_close_su16_*_case` lemmas, axiom-clean). The `Spec` shifts the **register reads**
  (`adapter.op_b_memory.prev_value` by `op_c_memory.prev_value`), not a separate `op_b_val`. The **SRL
  soundness conjunct is fully proven** (conversion + Stage A + the 4×16 leaf dispatch into `srl_close_su16_*`),
  and **both faithful anchors** are proven & axiom-clean. The `sra_div_to_bitvec_{false,true}` conversion
  helpers (SRA's `b_msb` case-split) are in place. **Remaining:** the SRA/SRLW/SRAW `Spec` conjuncts (each
  reuses the SRL dispatch skeleton across the msb/sign-fill cases — SRA ~2× SRL), the three `U16MSB`
  subcircuit `Assumptions`, and completeness (a deferred `sorry`; needs a `populate` + `ProverHint` opcode
  threading). See `proof-patterns.md` "Bit-shift chip soundness". **Mul/Div** are a later track (Mul's
  carry-chain witnessing + `output_eq` + completeness are still open).
- **Memory chips (LoadDouble / StoreDouble are the templates).** A memory op composes one extra subcircuit —
  `Readers.MemoryAccess.circuit` (the real-48-bit-address `send prev` / `receive new` pair + the timestamp
  gates) — between the address gadget and the adapter, and the address is the **`AddressOperation` gadget**
  output (`rs1 + signExtend(imm)`, 3 limbs), *not* a register index. Clone `Chips/LoadDoubleChip.lean` (a
  read: `MemoryAccess` `new_value = memory_access.prev_value`, adapter `ITypeReader` with op_a a **write**) or
  `Chips/StoreDoubleChip.lean` (a write: `new_value = adapter.op_a_memory.prev_value` = rs2, adapter
  `ITypeReaderImmutable` with op_a a **read**, and **no** chip-level `op_a_0` gate). Honest preconditions: the
  chip `Assumptions` commit a valid aligned non-reserved address (operand `isU64` + `(rs1+imm)%2^64 < 2^48` +
  `≥ 2^16` + 8-aligned) — `AddressOperation`'s inverse gate + offset range-check need them. The bridge ports
  the Sail RAM model (`Foundations/SailMemory.lean`, read **and** write) and takes the bus reads/bytes as
  hypotheses (`lean-sail-notes.md`). `StoreByte` + the sub-word load/store ops drop onto this exact spine —
  only the byte-select/MSB gadgetry is new; no new bus/Sail/trace infrastructure.
- The faithfulness anchor matches the operation **fragment**; matching `update_constraints.py`'s exact
  chip-level output is a separate tooling step.
- Completeness is only provable because the gadget is **witnessed** with a **semantic** spec. If you find
  yourself wanting a free combinatorial witness with a pure-semantic spec, completeness will be false — witness
  the value and constrain it instead.
