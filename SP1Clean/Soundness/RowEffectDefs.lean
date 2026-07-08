import SP1Clean.Soundness.RowView
import SP1Clean.Soundness.StateConsistency
import SP1Clean.Model.Semantics.GuestProgram
import SP1Clean.Model.Semantics.Decode

/-! # The refinement invariant and per-row effect (`RowView`-level, below `ChipRow`)

The Sail-refinement layer of the target theorem, factored **out of `Soundness/TargetVm.lean`** so it sits
**below `Soundness/ChipRow.lean`**: `RefinesAt`/`RowEffect`/`replayVal`/`rcvPcOf`/`sndPcOf` are all stated
over the chip-agnostic `Trace.RowView` (never `ChipRow`), so a `ChipKind.advance` field can reference
`RowEffect`/`SailStep` without the `ChipRow → TargetVm → SP1Ensemble → ChipRegistry → ChipRow` import cycle.
`SailStep`/`RomLoaded`/`SailConfigured` already live in `Model/`. The `WalkOf`/`TargetObligations`/
`chain_to_refines` machinery — which *does* reference `ChipRow` — stays in `TargetVm.lean`, which imports
this file. Namespace `SP1Clean.Soundness.Target` is unchanged (decoupled from path), so every
`RefinesAt`/`RowEffect`/`rcvPcOf`/… reference resolves as before. -/

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

/-- The committed effect of one row, as a relation between the pre- and post-states of its interpreter
step: the PC moves to the row's committed `next_pc`; the **register** file is, **when the row writes a
register** (`commit.writesReg`), exactly `s` except at the `op_a` destination (→ the committed `rdWrite`),
and **when it does not** (Branch / AluX0 / LoadX0, `commit.writesReg = false`) a pure frame — the SC
Phase 4 gate that lets a Branch/Store row, whose `op_a` is a *source read*, not corrupt that register; ROM,
initialization, and configuration persist. `try_step` may also touch bookkeeping registers (`minstret`,
`hart_state`, …) the trace doesn't commit, but those are outside the `BitVec 5` register file. (The memory
axis — `RowEffect.mem` / a store's `commit.memWrite` — is added in Phase 3b.) -/
structure RowEffect (prog : GuestProgram) (r : Trace.RowView (ZMod p))
    (s s' : SailState) : Prop where
  pc : s'.regs.get? Register.PC = some (sndPcOf (stateAccess r))
  regs : (if r.commit.writesReg then
            (∀ idx : BitVec 5, (idx.toNat : ZMod p) = r.adapter.op_a →
              s'.get_reg? idx = some (Word.toBitVec64 r.rdWrite)) ∧
            (∀ idx : BitVec 5, ¬ (idx.toNat : ZMod p) = r.adapter.op_a →
              s'.get_reg? idx = s.get_reg? idx)
          else (∀ idx : BitVec 5, s'.get_reg? idx = s.get_reg? idx))
  rom : RomLoaded prog s → RomLoaded prog s'
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

end SP1Clean.Soundness.Target
