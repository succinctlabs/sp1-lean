import SP1Clean.FormalModel.TraceGen.ClockBridge

/-!
# The generator's shadow bookkeeping

SP1's offline-memory argument makes every row hand back the record its access displaces: an ALU row
commits, alongside its operands, the *timestamp of the previous access* to each register it touches.
That is bookkeeping the Sail model does not do — the ISA has no notion of when a register was last
read — so a generator walking an execution has to carry it.

`GenState` is that carrier: last-access time per register and per RAM cell. It is deliberately not a
model of anything. Its whole content is the ordering discipline, and the one theorem that matters is
`stepRType_bounded`: **the invariant survives a row**. Every timestamp recorded before a row is
strictly earlier than that row's first access, and every timestamp the row records is strictly
earlier than the *next* row's first access. That is what discharges the three timestamp conjuncts of
`RTypeEvent.WellFormed` — the only part of an event's well-formedness a generator cannot read
straight off the machine state.

The intra-row order is SP1's and is load-bearing: `op_c` is read at `+2`, `op_b` at `+3`, `op_a`
written at `+4` (`Model/Semantics/MicroTime.lean`, the Rust `MemoryAccessPosition` values, linked to
these literals by `ClockBridge.lean`). Applying them in that order is what makes a row like
`add x1, x1, x1` come out right: the `op_b` read's *previous* access is this same row's `op_c` read,
not whatever preceded the row.

The RAM half is carried but unused by the ALU families, which touch no memory. It is here so the
memory chips slot in without restructuring, and so `Bounded` states the invariant over the whole
location space rather than over a subset that would have to be widened later.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Semantics

/-- Last-access time per location, as the generator has recorded it so far. -/
structure GenState where
  regTs : BitVec 5 → ℕ
  ramTs : RamCell → ℕ

namespace GenState

/-- The state at genesis: nothing has been accessed. SP1's initial register records carry
timestamp `0`, which is what makes `Bounded initial 1` hold at the first row's clock. -/
def initial : GenState := ⟨fun _ => 0, fun _ => 0⟩

/-- Record an access to one register. -/
def touchReg (g : GenState) (i : BitVec 5) (t : ℕ) : GenState :=
  { g with regTs := Function.update g.regTs i t }

/-- Record an access to one RAM cell. -/
def touchRam (g : GenState) (cell : RamCell) (t : ℕ) : GenState :=
  { g with ramTs := Function.update g.ramTs cell t }

/-- **The generator's invariant**: every access recorded so far is strictly before `t`. -/
def Bounded (g : GenState) (t : ℕ) : Prop :=
  (∀ i, g.regTs i < t) ∧ (∀ cell, g.ramTs cell < t)

theorem initial_bounded : initial.Bounded 1 :=
  ⟨fun _ => by simp [initial], fun _ => by simp [initial]⟩

theorem Bounded.mono {g : GenState} {s t : ℕ} (h : g.Bounded s) (hst : s ≤ t) : g.Bounded t :=
  ⟨fun i => lt_of_lt_of_le (h.1 i) hst, fun cell => lt_of_lt_of_le (h.2 cell) hst⟩

theorem touchReg_bounded {g : GenState} {i : BitVec 5} {u t : ℕ}
    (h : g.Bounded t) (hu : u < t) : (g.touchReg i u).Bounded t := by
  refine ⟨fun j => ?_, h.2⟩
  by_cases hij : j = i
  · subst hij; simpa [touchReg] using hu
  · simpa [touchReg, Function.update_of_ne hij] using h.1 j

theorem touchRam_bounded {g : GenState} {cell : RamCell} {u t : ℕ}
    (h : g.Bounded t) (hu : u < t) : (g.touchRam cell u).Bounded t := by
  refine ⟨h.1, fun d => ?_⟩
  by_cases hd : d = cell
  · subst hd; simpa [touchRam] using hu
  · simpa [touchRam, Function.update_of_ne hd] using h.2 d

/-! ## One R-type ALU row -/

/-- The state after `op_c`'s read. -/
def afterC (g : GenState) (clk : ℕ) (c : BitVec 5) : GenState :=
  g.touchReg c (clk + regCOffset)

/-- The state after `op_c`'s and `op_b`'s reads. -/
def afterB (g : GenState) (clk : ℕ) (b c : BitVec 5) : GenState :=
  (g.afterC clk c).touchReg b (clk + regBOffset)

/-- The state after the whole row: both reads and the `op_a` write. -/
def stepRType (g : GenState) (clk : ℕ) (a b c : BitVec 5) : GenState :=
  (g.afterB clk b c).touchReg a (clk + regEffectOffset)

/-- The previous-access timestamp an R-type row commits for `op_c`. -/
def prevTsC (g : GenState) (c : BitVec 5) : ℕ := g.regTs c

/-- The previous-access timestamp an R-type row commits for `op_b` — read *after* `op_c`, so a row
whose two sources are the same register sees its own `op_c` read here. -/
def prevTsB (g : GenState) (clk : ℕ) (b c : BitVec 5) : ℕ := (g.afterC clk c).regTs b

/-- The previous-access timestamp an R-type row commits for `op_a` — written after both reads. -/
def prevTsA (g : GenState) (clk : ℕ) (a b c : BitVec 5) : ℕ := (g.afterB clk b c).regTs a

/-- **The three timestamp conjuncts of `RTypeEvent.WellFormed`.**

Each commits the previous access to a register the row is about to touch, and each is strictly
earlier than the touch — including when the row's registers coincide, which is the case the
sequential order exists for. -/
theorem prevTs_lt {g : GenState} {clk : ℕ} (h : g.Bounded (clk + regCOffset))
    (a b c : BitVec 5) :
    g.prevTsA clk a b c < clk + regEffectOffset ∧
      g.prevTsB clk b c < clk + regBOffset ∧
      g.prevTsC c < clk + regCOffset := by
  have hC : (g.afterC clk c).Bounded (clk + regBOffset) :=
    (touchReg_bounded (h.mono (by norm_num)) (by norm_num)).mono (le_refl _)
  have hB : (g.afterB clk b c).Bounded (clk + regEffectOffset) :=
    touchReg_bounded (hC.mono (by norm_num)) (by norm_num)
  exact ⟨hB.1 a, hC.1 b, h.1 c⟩

/-- **The invariant survives a row.** Everything the row records lands strictly inside its own
window, so the next row — one `CLK_INC` later — starts with every timestamp strictly before *its*
first access. This is the induction step a generator's fold runs. -/
theorem stepRType_bounded {g : GenState} {clk : ℕ} (h : g.Bounded (clk + regCOffset))
    (a b c : BitVec 5) :
    (g.stepRType clk a b c).Bounded (clk + ordinaryClkInc + regCOffset) := by
  have hC : (g.afterC clk c).Bounded (clk + ordinaryClkInc + regCOffset) :=
    touchReg_bounded (h.mono (by norm_num)) (by norm_num)
  have hB : (g.afterB clk b c).Bounded (clk + ordinaryClkInc + regCOffset) :=
    touchReg_bounded hC (by norm_num)
  exact touchReg_bounded hB (by norm_num)

end GenState

end SP1Clean.TraceGen
