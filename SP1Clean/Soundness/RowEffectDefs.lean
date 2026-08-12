import SP1Clean.Soundness.RowView
import SP1Clean.Soundness.StateConsistency
import SP1Clean.Model.Semantics.GuestProgram
import SP1Clean.Model.Semantics.Decode

/-! # The refinement invariant and per-row effect (`RowView`-level, below `ChipRow`)

> **NOTE.** The definitions in this module (`RefinesAt`/`RowEffect`/`ValueOperandsBound`/`replayVal`/
> `rcvPcOf`/`sndPcOf`) are **permanent, live-path interface** — the `ChipKind.advance` field and the
> timed-grounding engine state their obligations against them. Only their legacy `TargetVm.lean`
> walk consumers (`WalkOf`/`TargetObligations`/`chain_to_refines`) are the frozen path; do not add
> new lemmas against *those* — new soundness work targets the timed-grounding engine.

The Sail-refinement layer of the target theorem, factored **out of `Soundness/TargetVm.lean`** so it sits
**below `Soundness/ChipRow.lean`**: `RefinesAt`/`RowEffect`/`replayVal`/`rcvPcOf`/`sndPcOf` are all stated
over the chip-agnostic `Trace.RowView` (never `ChipRow`), so a `ChipKind.advance` field can reference
`RowEffect`/`SailStep` without the `ChipRow → TargetVm → SP1Ensemble → ChipRegistry → ChipRow` import cycle.
`SailStep`/`RomLoaded`/`SailConfigured` already live in `Model/`. The `WalkOf`/`TargetObligations`/
`chain_to_refines` machinery — which *does* reference `ChipRow` — stays in `TargetVm.lean`, which imports
this file. Namespace `SP1Clean.Soundness.Target` is unchanged (decoupled from path), so every
`RefinesAt`/`RowEffect`/`rcvPcOf`/… reference resolves as before. -/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open SP1Clean
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-! ## PC limbs ↔ the Sail 64-bit PC -/

/-- The 64-bit PC a row's state-bus **receive** key carries (its current pc). -/
def rcvPcOf (sa : StateAccess (ZMod p)) : BitVec 64 :=
  pcBitsOfVals sa.pc[0].val sa.pc[1].val sa.pc[2].val

/-- The 64-bit PC a row's state-bus **send** key carries (its committed next pc). -/
def sndPcOf (sa : StateAccess (ZMod p)) : BitVec 64 :=
  pcBitsOfVals sa.next_pc[0].val sa.next_pc[1].val sa.next_pc[2].val

/-! ## The refinement invariant and the per-row effect -/

/-- **The exact-replay value (W2).** The value register `idx` holds after replaying the first `i` walk
rows from `s0`: the committed write (`rdWrite`) of the **most-recent** earlier **register-writing** row
(`commit.writesReg`) whose `op_a` destination is `idx`, or `s0`'s value if none wrote it. The
`commit.writesReg` guard (SC Phase 4) skips non-writers — a Branch/Store row whose `op_a` is a *source*
`rs1`/`rs2` read, not a destination — so their read register is not falsely pinned to `rdWrite`. The
exact-value refinement of the old frame disjunction — `RefinesAt.frame` pins each register to this, so a
row's committed operand columns (read-back register values) tie to the live Sail registers (W2's binding). -/
def replayVal (s0 : SailState) (path : List (Trace.RowView (ZMod p))) (idx : BitVec 5) :
    ℕ → Option (BitVec 64)
  | 0 => s0.get_reg? idx
  | i + 1 =>
    if hi : i < path.length then
      if (path[i]'hi).commit.writesReg = true ∧ (idx.toNat : ZMod p) = (path[i]'hi).adapter.op_a then
        some (Word.toBitVec64 (path[i]'hi).rdWrite)
      else replayVal s0 path idx i
    else replayVal s0 path idx i

/-! ## The memory axis (SC Phase 4 · Phase 3b): byte-address replay + the store `MemWrite` helpers -/

/-- The byte address a store's committed `MemWrite` targets — the three `AddressOperation` limbs
recombined (`a0 + a1·2^16 + a2·2^32`). -/
def _root_.SP1Clean.Trace.MemWrite.addrNat (mw : Trace.MemWrite (ZMod p)) : ℕ :=
  mw.addr[0].val + mw.addr[1].val * 2 ^ 16 + mw.addr[2].val * 2 ^ 32

/-- Byte `a` lies in the store's written range `[addrNat, addrNat + width)`. -/
def _root_.SP1Clean.Trace.MemWrite.covers (mw : Trace.MemWrite (ZMod p)) (a : ℕ) : Prop :=
  mw.addrNat ≤ a ∧ a < mw.addrNat + mw.width

instance (mw : Trace.MemWrite (ZMod p)) (a : ℕ) : Decidable (mw.covers a) := by
  unfold Trace.MemWrite.covers; infer_instance

/-- The little-endian byte the store writes at a covered address — the low `width` bytes of `value`. (The
high `8 - width` bytes of SP1's read-modify-write `store_value` never enter the invariant.) -/
def _root_.SP1Clean.Trace.MemWrite.byteAt (mw : Trace.MemWrite (ZMod p)) (a : ℕ) : BitVec 8 :=
  (Word.toBitVec64 mw.value).extractLsb' (8 * (a - mw.addrNat)) 8

/-- **The byte-address exact-replay value** — the memory twin of `replayVal`, folding the store rows'
committed `memWrite`s. The byte at address `a` after replaying the first `i` walk rows: the byte the
most-recent earlier *store* covering `a` wrote (`byteAt a`), or `s0`'s initial memory byte if none.
Parallel to `RomLoaded` but INDUCTIVE (data memory is written by stores, ROM is not). `RefinesAt.mem` pins
each byte to this; a load sources its committed byte from it. -/
def memReplayVal (s0 : SailState) (path : List (Trace.RowView (ZMod p))) (a : ℕ) :
    ℕ → Option (BitVec 8)
  | 0 => s0.mem.get? a
  | i + 1 =>
    if hi : i < path.length then
      match (path[i]'hi).commit.memWrite with
      | some mw => if mw.covers a then some (mw.byteAt a) else memReplayVal s0 path a i
      | none => memReplayVal s0 path a i
    else memReplayVal s0 path a i

/-- The simulation invariant at walk position `i`: the state's PC is the next row's committed pc, the
program ROM is intact, the platform configuration persists, and every register holds its **exact replay
value** (`replayVal`: the most-recent earlier `op_a` write, or `s0`'s value). The register clause is now
an exact replay, not a frame (W2's operand-binding strengthening). -/
structure RefinesAt (prog : GuestProgram) (s0 : SailState)
    (path : List (Trace.RowView (ZMod p))) (i : ℕ) (s : SailState) : Prop where
  pc : ∀ (h : i < path.length),
    s.regs.get? Register.PC = some (rcvPcOf (stateAccess (path[i]'h)))
  rom : RomLoaded prog s
  init : s.isInitialized
  cfg : SailConfigured s
  frame : ∀ idx : BitVec 5, s.get_reg? idx = replayVal s0 path idx i
  mem : ∀ a : ℕ, s.mem.get? a = memReplayVal s0 path a i

/-- The committed effect of one row, as a relation between the pre- and post-states of its interpreter
step: the PC moves to the row's committed `next_pc`; the **register** file is, **when the row writes a
register** (`commit.writesReg`), exactly `s` except at the `op_a` destination (→ the committed `rdWrite`),
and **when it does not** (Branch / AluX0 / LoadX0, `commit.writesReg = false`) a pure frame — the SC
Phase 4 gate that lets a Branch/Store row, whose `op_a` is a *source read*, not corrupt that register;
initialization and configuration persist. `try_step` may also touch bookkeeping registers (`minstret`,
`hart_state`, …) the trace doesn't commit, but those are outside the `BitVec 5` register file. The **memory**
clause is the orthogonal second axis: `commit.memWrite = none` (all chips but stores) → `s'.mem = s.mem`
frame; `some mw` (a store) → the committed `width`-byte range at `mw.addrNat` becomes `mw.byteAt`, the rest
framed.

ROM preservation is intentionally not a row-local field. SP1's trusted Program table is immutable
and separate from data Memory, whereas unmodified Sail fetches from its mutable byte memory. The
named `SailCodeMemoryCompatible` boundary contract supplies preservation only when the pinned
program is refined all the way to a multi-step unmodified-Sail chain. -/
structure RowEffect (_prog : GuestProgram) (r : Trace.RowView (ZMod p))
    (s s' : SailState) : Prop where
  pc : s'.regs.get? Register.PC = some (sndPcOf (stateAccess r))
  regs : (if r.commit.writesReg then
            (∀ idx : BitVec 5, (idx.toNat : ZMod p) = r.adapter.op_a →
              s'.get_reg? idx = some (Word.toBitVec64 r.rdWrite)) ∧
            (∀ idx : BitVec 5, ¬ (idx.toNat : ZMod p) = r.adapter.op_a →
              s'.get_reg? idx = s.get_reg? idx)
          else (∀ idx : BitVec 5, s'.get_reg? idx = s.get_reg? idx))
  mem : (r.commit.memWrite = none → ∀ a : ℕ, s'.mem.get? a = s.mem.get? a) ∧
        (∀ mw : Trace.MemWrite (ZMod p), r.commit.memWrite = some mw →
          (∀ a : ℕ, mw.covers a → s'.mem.get? a = some (mw.byteAt a)) ∧
          (∀ a : ℕ, ¬ mw.covers a → s'.mem.get? a = s.mem.get? a))
  init : s.isInitialized → s'.isInitialized
  cfg : SailConfigured s → SailConfigured s'

/-- **The value half of `OperandsBound`.** For each register source operand (`imm = 0`), the live Sail
register value equals the row's committed read-value column (`op_b`/`op_c` `prev_value`). This is what
W7's `try_step` reduction consumes: the interpreter's `rs1`/`rs2` reads agree with the chip's columns, so
the executed result matches the committed `rdWrite`. (Relocated here from `Soundness/ValueBound.lean` so the
Phase-4 `advance` composition — and eventually a `ChipKind.advance` field — sits below `ChipRow`; namespace
`SP1Clean.Soundness.Target` unchanged so every reference resolves as before.) -/
def ValueOperandsBound (r : Trace.RowView (ZMod p)) (s : SailState) : Prop :=
  (∀ idx : BitVec 5, r.adapter.imm_b = 0 → (idx.toNat : ZMod p) = r.adapter.op_b[0] →
      s.get_reg? idx = some (Word.toBitVec64 r.adapter.op_b_memory.prev_value)) ∧
  (∀ idx : BitVec 5, r.adapter.imm_c = 0 → (idx.toNat : ZMod p) = r.adapter.op_c[0] →
      s.get_reg? idx = some (Word.toBitVec64 r.adapter.op_c_memory.prev_value))

/-- The live value carried by the adapter's `op_a` prior-record slot.  Most chips use `op_a` as a
destination and ignore this fact.  Branches, stores, and the `rd = x0` chips use the same physical
slot as a genuine source, so their `advanceReady` contract consumes it explicitly.  Keeping this
separate from `ValueOperandsBound` preserves the upstream B/C operand convention while making the
source-A dependency visible at the grounding boundary. -/
def SourceAValueBound (r : Trace.RowView (ZMod p)) (s : SailState) : Prop :=
  ∀ idx : BitVec 5, (idx.toNat : ZMod p) = r.adapter.op_a →
    s.get_reg? idx = some (Word.toBitVec64 r.adapter.op_a_memory.prev_value)

end SP1Clean.Soundness.Target
