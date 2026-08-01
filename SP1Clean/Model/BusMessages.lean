import SP1Clean.Math.Word
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Bus message types (the low layer below both the channels and the semantic predicates)

The `ProvableStruct` message tuples of SP1's dynamic buses — State, Memory, Program — plus the
**structural** (program-independent, execution-independent) per-row predicates over them
(`Spec`/`isU64`/`RowSpec`). Extracted from `Model/Channels.lean` so this layer sits *below* the
semantic-execution predicates (`Model/Semantics/Truth.lean` — `StateTruth`/`MemTruth`/`ProgTruth`),
which need these message types: with the messages here, `Truth` imports this file (not `Channels`), and
`Channels` can then wire the semantic predicates into the channel `Guarantees` without an import cycle.

Namespace is `SP1Clean.Channels` (unchanged), so every `Channels.StateMsg`/`.MemoryMsg.isU64`/… name
resolves exactly as before — this is a pure relocation. The channel *definitions* stay in
`Model/Channels.lean`; the byte bus's `ByteRow`/`ByteRowSpec` stay in `Model/ByteTable.lean`. -/

namespace SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The State-bus message — `(clk_high, clk_low, pc0, pc1, pc2)`, arity 5, matching SP1's
`AirInteraction.state` (`crates/hypercube/src/lookup/interaction.rs`) and the `.state` interaction in
`Extracted/CPUState.lean`. Each CPU/ALU row receives the current `(clk, pc)` and sends the next. -/
structure StateMsg (F : Type) where
  clk_high : F
  clk_low : F
  pc0 : F
  pc1 : F
  pc2 : F
deriving ProvableStruct

/-- Per-row well-formedness of a State message: **`True`**. SP1's `CPUState::eval`
(`crates/core/machine/src/adapter/state.rs:90-98`) range-checks *only* the clock (`clk_0_16` 13-bit Range
+ `clk_16_24` U8Range) — **it does not range-check `pc`** (the `receive_state`/`send_state` pass `cols.pc`/
`next_pc` un-bounded). So the State *send* proves no local guarantee; the pc-limb bounds are *received*
facts (the previous row's send / the verifier-committed initial pc via the PC chain, and the program ROM),
exactly like the register-index bounds. The cross-row PC chain stays the trace level
(`Soundness/StateConsistency.lean`). -/
def StateMsg.Spec (_ : StateMsg (ZMod p)) : Prop := True

/-- The Memory-bus message — `(clk_high, clk_low, addr0, addr1, addr2, value)`, where `value : Word` is
the 4-limb little-endian word; `ProvableStruct` flattens it to the same arity-9 element tuple, matching
SP1's `AirInteraction.memory` (`crates/hypercube/src/lookup/interaction.rs`) and the `.memory`
interaction in `Extracted/RTypeReader.lean`. Registers use `addr0` = register index, `addr1 = addr2 = 0`.
Each register access sends the prior value at the previous timestamp and receives the new value at the
current timestamp. -/
structure MemoryMsg (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  value : Word F
deriving ProvableStruct

/-- Per-row register-access address shape (`addr1 = addr2 = 0`). Kept as a small structural predicate (e.g.
for trace use); it is **not** the memory channel's `Guarantees` — see `memoryChannel`. -/
def MemoryMsg.Spec (msg : MemoryMsg (ZMod p)) : Prop :=
  msg.addr1 = 0 ∧ msg.addr2 = 0

/-- **The Memory message's value well-formedness** — the 4-limb `value` word is a `U64` (each limb
`< 2^16`), literally `Word.isU64`. This is the per-message `Guarantees` the memory **provider proves on
push** (a writer's range-check) and the chips **pull-and-derive** (W11 polarity flip), exactly analogous
to `ProgramMsg.RowSpec` / the byte bus. Because the message carries the whole `Word`, the pull guarantee
and the chips' operand facts are the *same* proposition — no per-limb bridging. -/
def MemoryMsg.isU64 (msg : MemoryMsg (ZMod p)) : Prop :=
  Word.isU64 msg.value

/-- **The Memory message's access-clock bound** — the low clock limb is a genuine 24-bit timestamp.
This is the second half of the memory channel's `Guarantees` (beside `MemoryMsg.isU64`), and it is
stated on the raw limb rather than on `MicroTime`'s `clkNat`/`timeNat` so this module stays below the
semantic-execution layer (row-local hygiene, exactly like `isU64`).

It is **not** derivable from a row's own constraints: `Readers.RegisterAccessTimestamp.Spec` bounds
only the *difference* `clk_target - prev_low - 1`, so as field elements the prior clock could be the
huge representative `p + clk_target - 1 - diff` and the ℕ-level comparison would fail. SP1 relies on
exactly the same missing piece — `crates/core/machine/src/air/memory.rs`'s
`eval_memory_access_timestamp` comments that the underflow argument is valid "as long as both
`current_comp_val, prev_comp_value` are range-checked to be `< 2^24` and as long as we're working in a
field larger than `2 * 2^24`" — and neither range check is local to the accessing row. Carrying the
bound on the bus is what makes it a genuine received fact: a chip that **pulls** a prior record gets
it for free, which is what discharges `Soundness/TouchChains.lean`'s `TouchOK.pull_lt_push`. -/
def MemoryMsg.ClkBound (msg : MemoryMsg (ZMod p)) : Prop :=
  msg.clk_low.val < 2 ^ 24

section ClkBound

/-- **The pusher's side of `MemoryMsg.ClkBound`**: the two `Readers.CPUState.Spec` clock byte bounds
bound the row's recombined low clock plus any intra-row effect offset (`+1`/`+2`/`+3`/`+4`) by `2^24`.
`clk_0_16` decodes as `8 s + 1` with `s < 2^13` (so `≤ 2^16 - 7`) and `clk_16_24 < 2^8`, giving
`clk_low ≤ 2^24 - 7` and hence `clk_low + δ ≤ 2^24 - 3` for `δ ≤ 4`.

The `p ≤ 2^24` branch is genuine, not a dodge: there every `ZMod p` value is `< 2^24` outright, which
is what keeps this lemma — and therefore every chip's Memory-push obligation — inside the
project-standard `Fact (2 ^ 17 < p)` instead of forcing a repo-wide bump to `Fact (2 ^ 25 < p)`. The
consumer that actually *uses* the bound (`Soundness/TimeExtraction.lean`) supplies the stronger
field assumption itself. -/
theorem MemoryMsg.clkBound_of_cpuState_bounds (clk0 clk1 delta : ZMod p) (k : ℕ)
    (hdelta : delta.val = k) (hk : k ≤ 4)
    (clk0Bound : ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1Bound : clk1.val < 2 ^ 8) :
    (clk0 + clk1 * 65536 + delta).val < 2 ^ 24 := by
  by_cases hp : p ≤ 2 ^ 24
  · exact lt_of_lt_of_le (ZMod.val_lt _) hp
  have hp : 2 ^ 24 < p := by omega
  have h17 := Fact.out (p := 2 ^ 17 < p)
  set scaled := (clk0 - 1) * (8 : ZMod p)⁻¹ with scaledDef
  have reconstruct : scaled * 8 + 1 = clk0 := by
    rw [scaledDef, mul_assoc, inv_mul_cancel₀ val_8_ne_zero, mul_one, sub_add_cancel]
  have scaledMulVal : (scaled * 8).val = scaled.val * 8 := by
    rw [ZMod.val_mul_of_lt (by rw [val_8_zmod_p]; omega), val_8_zmod_p]
  have clk0Val : clk0.val = scaled.val * 8 + 1 := by
    rw [← reconstruct, ZMod.val_add_of_lt (by rw [scaledMulVal, ZMod.val_one]; omega),
      scaledMulVal, ZMod.val_one]
  have highLimbVal : (clk1 * 65536).val = clk1.val * 65536 := by
    rw [ZMod.val_mul_of_lt (by rw [val_65536_zmod_p]; omega), val_65536_zmod_p]
  have lowVal : (clk0 + clk1 * 65536).val = clk0.val + clk1.val * 65536 := by
    rw [ZMod.val_add_of_lt (by rw [highLimbVal]; omega), highLimbVal]
  rw [ZMod.val_add_of_lt (by rw [lowVal, hdelta]; omega), lowVal, hdelta]
  omega

end ClkBound

end SP1Clean.Channels

/-! ## The readers' clock discipline

`MemoryMsg.ClkBound` is a *per-message* requirement, but the obligation a chip actually owes its readers
is uniform: **every** intra-row effect offset applied to the row's low clock stays 24-bit. Naming that
once here — rather than spelling a per-offset numeric conjunct in each of the seven readers'
`Assumptions` and rebuilding it in each of the 25 chips — is what keeps a future change to the discipline
(a new effect slot, a wider clock) local to this declaration and the readers that unfold it.

Namespace is `SP1Clean.Readers` (the readers' own), not `SP1Clean.Channels`: this is the *readers'*
contract, stated over the raw clock limbs. It lives in this module — below `FormalModel/Contracts/
Readers.lean`, where the rest of the reader contract surface sits — because `Native/Readers/
RegisterWrite.lean` and `Native/Readers/MemoryAccess.lean` reach `Model/Channels` but deliberately do
**not** import the contract file (they need none of its `Extracted/` column structs), and every reader
reaches this module through `Model/Channels`. Repo convention is that namespaces are decoupled from
directories, so the `Readers.*` names resolve identically wherever the declaration is filed. -/

namespace SP1Clean.Readers

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The clock discipline at **one already-shifted** access clock: the caller applied the effect offset
before handing the clock over, so only the single 24-bit bound remains. `Readers.RegisterWrite` is the
one reader in this shape — its `Inputs.clk_low` is the composing chip's recombined clock already `+ 4`ed
— and `ClkDiscipline.slot` is how a chip produces it from the unshifted discipline. -/
def ClkDisciplineAt (clk is_real : ZMod p) : Prop :=
  is_real = 1 → clk.val < 2 ^ 24

/-- The clock discipline a reader's composing chip owes: every intra-row effect offset (`≤ 4`) applied
to the row's low clock stays 24-bit. Named once so a future change to the discipline touches this
declaration and the readers that unfold it — not the 25 chips that supply it. -/
def ClkDiscipline (clk_low is_real : ZMod p) : Prop :=
  ∀ (delta : ZMod p) (k : ℕ), delta.val = k → k ≤ 4 → is_real = 1 → (clk_low + delta).val < 2 ^ 24

/-- **The chip's constructor.** The hypothesis is `Readers.CPUState.Spec` spelled over the row's two
committed clock byte limbs (that contract file sits *above* this module, so the shape is written out
rather than named); a chip obtains it in soundness by applying its `CPUState` sub-obligation to the
`is_real` binary gate, and in completeness straight out of `ProverAssumptions`. The arithmetic is
`Channels.MemoryMsg.clkBound_of_cpuState_bounds`, so this stays inside the standard `Fact (2 ^ 17 < p)`. -/
theorem ClkDiscipline.of_cpuState_spec {clk0 clk1 is_real : ZMod p}
    (h : is_real = 1 → ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ clk1.val < 2 ^ 8) :
    ClkDiscipline (clk0 + clk1 * 65536) is_real :=
  fun _ k hk hk4 hr =>
    Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ k hk hk4 (h hr).1 (h hr).2

set_option linter.unusedSectionVars false in
/-- Transport the discipline along a gate identification. A chip that composes its readers at a
*derived* selector (the shift chips' `is_sll + is_sllw` flag sum) while its `CPUState` block runs at the
public `is_real` proves the two equal in-circuit; this re-gates the discipline once instead of at every
offset. -/
theorem ClkDiscipline.of_gate {clk_low is_real gate : ZMod p} (h : ClkDiscipline clk_low is_real)
    (hgate : gate = 1 → is_real = 1) : ClkDiscipline clk_low gate :=
  fun delta k hdelta hk hg => h delta k hdelta hk (hgate hg)

set_option linter.unusedSectionVars false in
/-- Specialize the discipline to one effect slot. -/
theorem ClkDiscipline.slot {clk_low is_real : ZMod p} (h : ClkDiscipline clk_low is_real)
    (delta : ZMod p) (k : ℕ) (hdelta : delta.val = k) (hk : k ≤ 4) :
    ClkDisciplineAt (clk_low + delta) is_real :=
  h delta k hdelta hk

/-- The RAM effect slot (`MemoryAccess`'s current-timestamp push). -/
theorem ClkDiscipline.at_one {clk_low is_real : ZMod p} (h : ClkDiscipline clk_low is_real) :
    ClkDisciplineAt (clk_low + 1) is_real :=
  h.slot 1 1 (ZMod.val_one p) (by norm_num)

/-- The op_c operand slot. -/
theorem ClkDiscipline.at_two {clk_low is_real : ZMod p} (h : ClkDiscipline clk_low is_real) :
    ClkDisciplineAt (clk_low + 2) is_real :=
  h.slot 2 2 (by simp) (by norm_num)

/-- The op_b operand slot. -/
theorem ClkDiscipline.at_three {clk_low is_real : ZMod p} (h : ClkDiscipline clk_low is_real) :
    ClkDisciplineAt (clk_low + 3) is_real :=
  h.slot 3 3 (by simp) (by norm_num)

/-- The op_a operand / `rd` write slot. -/
theorem ClkDiscipline.at_four {clk_low is_real : ZMod p} (h : ClkDiscipline clk_low is_real) :
    ClkDisciplineAt (clk_low + 4) is_real :=
  h.slot 4 4 (by simp) (by norm_num)

end SP1Clean.Readers

namespace SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The Program-bus message — the arity-16 instruction-fetch tuple `(pc0, pc1, pc2, opcode, op_a,
op_b0..3, op_c0..3, op_a_0, imm_b, imm_c)`, matching SP1's `AirInteraction.program`
(`crates/hypercube/src/lookup/interaction.rs`, `InteractionKind::Program => 16`) and the `.send
(.program …)` in `Extracted/RTypeReader.lean`. `op_b`/`op_c` are the two operands as 4-limb **`Word`s**;
`ProvableStruct` flattens each to the same 4 elements, so the emitted arity-16 row is byte-identical to
the older 8-scalar-limb form (the `MemoryMsg.value : Word` precedent). **Field order preserves the row**:
`op_b`/`op_c` are adjacent, `imm_b`/`imm_c` stay last — do NOT interleave `imm_b` between them (that would
reorder the bus tuple). For an R-type row only the register-index limb of each operand is non-zero
(`op_b[1..3] = op_c[1..3] = imm_b = imm_c = 0`). -/
structure ProgramMsg (F : Type) where
  pc0 : F
  pc1 : F
  pc2 : F
  opcode : F
  op_a : F
  op_b : Word F
  op_c : Word F
  op_a_0 : F
  imm_b : F
  imm_c : F
deriving ProvableStruct

/-- Per-row well-formedness of a Program message — the part a CPU row can **send-prove locally** for *any*
adapter type. The only genuinely send-local fact is that `op_a_0` is boolean (from the reader's
unconditional `op_a_0 * (op_a_0 - 1) = 0` gate). Everything else is a **decode** fact that belongs on the
**receive** side (`ProgramChip.ProgramRowSpec`), not the send-side channel `Guarantees`. -/
def ProgramMsg.Spec (msg : ProgramMsg (ZMod p)) : Prop :=
  msg.op_a_0 = 0 ∨ msg.op_a_0 = 1

/-- **The Program message's per-row well-formedness** — the decode facts that hold for a validly-decoded
ROM row of *any* instruction type: the destination register index `op_a < 32`, the pc limbs `< 2^16`, and
`op_a_0` boolean. This is the per-message `Guarantees` the **ROM provider proves on push** and the chips
**pull-and-derive** (W11 polarity flip) — program-INDEPENDENT, exactly analogous to
`byteChannel.Guarantees = ByteRowSpec`. The *program-specific* membership (`inROM` — the fetch is in
*this* committed program) is the finished-channel **balance** fact, not a per-message guarantee (see
`Soundness/ProgramConsistency.lean`). -/
def ProgramMsg.RowSpec (msg : ProgramMsg (ZMod p)) : Prop :=
  msg.op_a.val < 32 ∧
  msg.pc0.val < 2 ^ 16 ∧ msg.pc1.val < 2 ^ 16 ∧ msg.pc2.val < 2 ^ 16 ∧
  (msg.op_a_0 = 0 ∨ msg.op_a_0 = 1)

end SP1Clean.Channels
