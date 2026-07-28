import SP1Clean.Model.Machine.Execution
import SP1Clean.Model.BusMessages

/-! # Ordinary-window micro-time

This module is the proved register/RAM interpretation used by the current ordinary-row grounding
theorem. New whole-machine statements use `Machine.SP1MachineModel.schedule`; the fixed eight-tick
definitions here remain an explicitly scoped compatibility layer until timed grounding is generalized.

- `clkNat` — the ℕ-decoded bus clock (`clk_high · 2^24 + clk_low`, the split every State/Memory message
  carries); `timeNat` projections for both message types.
- **The ordinary window convention**: execution step `k` occupies `[c0 + 8k, c0 + 8(k+1))`
  (`c0` = the committed genesis clock; every chip advances by `CLK_INC = 8`). Intra-row effect times:
  a RAM write lands at offset `+1` (the `MemoryAccess` push offset), a register write at `+4` (the
  op_a write offset); reads/read-backs at `+2`/`+3` observe pre-effect content.
- `MemLoc` — the register-file/RAM split of the Memory bus's 3-limb address (registers are
  `addr0 < 32 ∧ addr1 = addr2 = 0`, the shape `MemoryMsg.Spec` names; RAM locations are SP1's
  canonical aligned 8-byte cells, not overlapping byte-addressed windows).
- `chainState` — the trajectory as a function: `k` iterations of the official interpreter `try_step`
  (`Option`-valued past a failing step), with the bridge to the relational `SailChain`.
- `microValue` — the location's content at a micro-time `τ`: the pre- or post-state of window `k`'s
  step according to the effect-time convention. -/

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ}

/-! ## Bus time -/

/-- The ℕ-decoded bus clock (no-wraparound is supplied where consumed, from the rows' in-circuit
`clk_low` byte bounds). -/
def clkNat (hi lo : ZMod p) : ℕ := hi.val * 2 ^ 24 + lo.val

/-- A State message's time. -/
def StateMsg.timeNat (m : StateMsg (ZMod p)) : ℕ := clkNat m.clk_high m.clk_low

/-- A Memory message's time (slots 0/1 of the arity-9 tuple). -/
def MemoryMsg.timeNat (m : MemoryMsg (ZMod p)) : ℕ := clkNat m.clk_high m.clk_low

/-- The 3-limb pc recombined as the Sail 64-bit pc. -/
def pcBits (pc0 pc1 pc2 : ZMod p) : BitVec 64 :=
  BitVec.ofNat 64 (pc0.val + pc1.val * 2 ^ 16 + pc2.val * 2 ^ 32)

/-- A State message's pc, using the same recombination as the official-Sail row bridge. -/
def StateMsg.pcBits (m : StateMsg (ZMod p)) : BitVec 64 :=
  _root_.SP1Clean.Semantics.pcBits m.pc0 m.pc1 m.pc2

/-! ## Memory locations -/

/-- An SP1 RAM location is an aligned 8-byte cell.  The 61-bit index is the aligned byte address
divided by eight; representing the quotient directly makes non-overlap structural. -/
abbrev RamCell := BitVec 61

/-- The canonical byte address of an SP1 RAM cell. -/
def RamCell.baseAddr (cell : RamCell) : BitVec 64 :=
  BitVec.ofNat 64 (cell.toNat * 8)

/-- A Memory-bus location: a register (index < 32, the `addr1 = addr2 = 0` shape) or an aligned
8-byte RAM cell.  Rust's `CompressedMemory` keys load/store records by `addr & !7`; using the cell
index here keeps the semantic key at exactly that granularity. -/
inductive MemLoc
  | reg (idx : BitVec 5)
  | ram (cell : RamCell)
deriving DecidableEq

/-- Decode a Memory message's 3-limb address into its location (register ⟺ the register shape).
RAM messages are interpreted at SP1's canonical 8-byte-cell granularity.  Faithful load/store rows
already carry the aligned address; division by eight additionally makes the semantic boundary total
for provider records. -/
def MemoryMsg.locOf (m : MemoryMsg (ZMod p)) : MemLoc :=
  if m.addr0.val < 32 ∧ m.addr1 = 0 ∧ m.addr2 = 0 then
    .reg (BitVec.ofNat 5 m.addr0.val)
  else
    .ram (BitVec.ofNat 61
      ((m.addr0.val + m.addr1.val * 2 ^ 16 + m.addr2.val * 2 ^ 32) / 8))

/-- A Memory-bus record with the canonical register address shape decodes to that register.  The
field equality is the form supplied by the Program/decode layer, while the result is the typed
location consumed by timed grounding. -/
theorem MemoryMsg.locOf_register [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (message : MemoryMsg (ZMod p)) (index : BitVec 5)
    (addr0 : (index.toNat : ZMod p) = message.addr0)
    (addr1 : message.addr1 = 0) (addr2 : message.addr2 = 0) :
    MemoryMsg.locOf message = MemLoc.reg index := by
  unfold MemoryMsg.locOf
  rw [← addr0, addr1, addr2]
  have indexLtP : index.toNat < p := by
    have := index.isLt; have := Fact.out (p := 2 ^ 17 < p); omega
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt indexLtP, index.isLt, true_and, if_true,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The 8-byte little-endian RAM word at `a` (the Memory bus's value granularity). -/
def ramWord64? (s : SailState) (a : BitVec 64) : Option (BitVec 64) := do
  let b0 ← s.mem.get? a.toNat
  let b1 ← s.mem.get? (a.toNat + 1)
  let b2 ← s.mem.get? (a.toNat + 2)
  let b3 ← s.mem.get? (a.toNat + 3)
  let b4 ← s.mem.get? (a.toNat + 4)
  let b5 ← s.mem.get? (a.toNat + 5)
  let b6 ← s.mem.get? (a.toNat + 6)
  let b7 ← s.mem.get? (a.toNat + 7)
  pure (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)

/-- A Sail state's content at a location: the 64-bit register value, or the 8-byte RAM word. -/
def locContent (s : SailState) : MemLoc → Option (BitVec 64)
  | .reg i => s.get_reg? i
  | .ram cell => ramWord64? s cell.baseAddr

/-! ## The trajectory as a function -/

/-- Compatibility name for the canonical Lean-native machine step. -/
noncomputable abbrev stepOnce := SP1Clean.Machine.stepOnce

/-- Compatibility name for the canonical PolyFun machine trajectory. -/
noncomputable abbrev chainState := SP1Clean.Machine.trajectory

/-- The function ↔ relation bridge: a defined `chainState` is a `SailChain`. -/
theorem sailChain_of_chainState {s0 s : SailState} :
    ∀ {k : ℕ}, chainState s0 k = some s → SailChain k s0 s := by
  intro k
  induction k generalizing s with
  | zero => intro h; cases h; exact .refl s0
  | succ k ih =>
    intro h; change (Machine.trajectory s0 k).bind Machine.stepOnce = some s at h
    rcases hbind : Machine.trajectory s0 k with _ | s'
    · rw [hbind] at h; cases h
    · rw [hbind, Option.bind_some] at h; unfold Machine.stepOnce at h
      rcases hrun : (try_step 0 false).run s' with b | e
      · rw [hrun] at h; cases h; exact (ih hbind).snoc ⟨_, hrun⟩
      · rw [hrun] at h; cases h

/-- The front-step unfolding: `chainState` is defined by appending at the tail, but a chain peels at
the head — one determined first step shifts the origin. -/
theorem chainState_succ_front {s0 s1 : SailState} (h : stepOnce s0 = some s1) :
    ∀ k, chainState s0 (k + 1) = chainState s1 k := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact congrArg (·.bind Machine.stepOnce) ih

/-- Determinism, the other direction: a `SailChain` forces the `chainState` value. -/
theorem chainState_of_sailChain {s0 s : SailState} :
    ∀ {k : ℕ}, SailChain k s0 s → chainState s0 k = some s := by
  intro k h
  induction h with
  | refl s => rfl
  | @step n s s' _ hstep _ ih =>
    obtain ⟨b, hrun⟩ := hstep
    have hstep1 : Machine.stepOnce s = some s' := by unfold Machine.stepOnce; rw [hrun]
    rw [chainState_succ_front hstep1 n]; exact ih

/-! ## The location content at a micro-time -/

/-- **The intra-row effect convention, as a function.** `microValue s0 c0 loc τ`: the content of `loc`
at micro-time `τ` on the trajectory from `s0` with genesis clock `c0`. Window `k = (τ − c0) / 8`,
offset `δ = (τ − c0) % 8`; the window's step has taken effect at `loc` iff `τ` is at/after the
location's effect offset (RAM `+1`, register `+4`). Pre-genesis times read the initial state. -/
noncomputable def microValue (s0 : SailState) (c0 : ℕ) (loc : MemLoc) (τ : ℕ) : Option (BitVec 64) :=
  if τ < c0 then
    locContent s0 loc
  else
    let k := (τ - c0) / 8
    let δ := (τ - c0) % 8
    let takePost : Bool := match loc with
      | .reg _ => 4 ≤ δ
      | .ram _ => 1 ≤ δ
    (chainState s0 (if takePost then k + 1 else k)).bind (locContent · loc)

end SP1Clean.Semantics
