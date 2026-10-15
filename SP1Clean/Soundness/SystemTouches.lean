import SP1Clean.Soundness.SyscallGrounding
import SP1Clean.Soundness.TypedTimeContracts

/-! # Shared register-touch alignment for HALT and syscalls

Both system rows use x5/x10/x11 at offsets 4/3/2. The x5 push may write a new word; the other
pushes are read-backs. Timestamp ordering is conditional only on the prior record's low-clock
bound, to be supplied by Memory grounding, and never on the system row's full semantic contract.
-/

namespace SP1Clean.Soundness.SystemTouches

open SP1Clean.Semantics SP1Clean.Channels TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

noncomputable def start (state : Circuits.Types.CPUState (ZMod p)) : ℕ :=
  clkNat state.clk_high (state.clk_0_16 + state.clk_16_24 * 65536)

def prior (state : Circuits.Types.CPUState (ZMod p)) (block : Circuits.Types.RegisterAccessCols (ZMod p))
    (idx : ZMod p) : MemoryMsg (ZMod p) :=
  ⟨state.clk_high, block.access_timestamp.prev_low, idx, 0, 0, block.prev_value⟩

def push (state : Circuits.Types.CPUState (ZMod p)) (idx off : ZMod p) (value : Word (ZMod p)) :
    MemoryMsg (ZMod p) :=
  ⟨state.clk_high, state.clk_0_16 + state.clk_16_24 * 65536 + off, idx, 0, 0, value⟩

/-- The exact three paired touches, with separate pre-write and read-back currency points. -/
noncomputable def touches (state : Circuits.Types.CPUState (ZMod p))
    (a b c : Circuits.Types.RegisterAccessCols (ZMod p)) (value : Word (ZMod p)) : List (Touch p) :=
  [((prior state a 5, start state), push state 5 4 value),
   ((prior state b 10, start state + 3), push state 10 3 b.prev_value),
   ((prior state c 11, start state + 2), push state 11 2 c.prev_value)]

/-- The three byte-checked timestamp differences, independent of Memory truth. -/
def TimestampBounds (state : Circuits.Types.CPUState (ZMod p))
    (a b c : Circuits.Types.RegisterAccessCols (ZMod p)) : Prop :=
  ActiveTimestampBounds a.access_timestamp.prev_low a.access_timestamp.diff_low_limb
      (state.clk_0_16 + state.clk_16_24 * 65536 + 4) ∧
    ActiveTimestampBounds b.access_timestamp.prev_low b.access_timestamp.diff_low_limb
      (state.clk_0_16 + state.clk_16_24 * 65536 + 3) ∧
    ActiveTimestampBounds c.access_timestamp.prev_low c.access_timestamp.diff_low_limb
      (state.clk_0_16 + state.clk_16_24 * 65536 + 2)

private theorem push_time (state : Circuits.Types.CPUState (ZMod p))
    (clock : ((state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ state.clk_16_24.val < 2 ^ 8)
    (idx : ZMod p) (value : Word (ZMod p)) (off : ℕ) (bound : off ≤ 6) :
    MemoryMsg.timeNat (push state idx off value) = start state + off ∧
      MemoryMsg.ClkBound (push state idx off value) := by
  obtain ⟨small, addition⟩ := TimeExtraction.clkVal_small_add_of_cpuState_bounds
    state.clk_0_16 state.clk_16_24 off (by omega) clock.1 clock.2
  constructor
  · simp only [MemoryMsg.timeNat, push, start, clkNat]
    omega
  · change (state.clk_0_16 + state.clk_16_24 * 65536 + (off : ZMod p)).val < 2 ^ 24
    omega

private theorem locations (state : Circuits.Types.CPUState (ZMod p))
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (value : Word (ZMod p)) (idx : BitVec 5) (off : ZMod p) :
    MemoryMsg.locOf (prior state block idx.toNat) = MemLoc.reg idx ∧
      MemoryMsg.locOf (push state idx.toNat off value) = MemLoc.reg idx :=
  ⟨MemoryMsg.locOf_register _ idx rfl rfl rfl, MemoryMsg.locOf_register _ idx rfl rfl rfl⟩

/-- All alignment facts for the shared three-register layout. -/
theorem touches_spec (state : Circuits.Types.CPUState (ZMod p))
    (a b c : Circuits.Types.RegisterAccessCols (ZMod p)) (value : Word (ZMod p))
    (clock : ((state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ state.clk_16_24.val < 2 ^ 8)
    (timestamps : TimestampBounds state a b c) :
    (∀ touch ∈ touches state a b c value, TouchOK (start state) touch.1 touch.2) ∧
    (∀ loc, List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      ((touches state a b c value).filter (fun touch => MemoryMsg.locOf touch.2 = loc))) ∧
    (∀ touch ∈ touches state a b c value, MemoryMsg.ClkBound touch.2) ∧
    (∀ touch ∈ touches state a b c value, MemoryMsg.ClkBound touch.1.1 →
      MemoryMsg.timeNat touch.1.1 < MemoryMsg.timeNat touch.2) := by
  obtain ⟨locA, pushA⟩ := locations state a value 5#5 4
  obtain ⟨locB, pushB⟩ := locations state b b.prev_value 10#5 3
  obtain ⟨locC, pushC⟩ := locations state c c.prev_value 11#5 2
  obtain ⟨timeA, boundA⟩ := push_time state clock 5 value 4 (by decide)
  obtain ⟨timeB, boundB⟩ := push_time state clock 10 b.prev_value 3 (by decide)
  obtain ⟨timeC, boundC⟩ := push_time state clock 11 c.prev_value 2 (by decide)
  norm_num only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.cast_ofNat] at locA pushA locB pushB locC pushC timeA boundA timeB boundB timeC boundC
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro touch member
    simp only [touches, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨pushA.trans locA.symm, le_rfl, Nat.le_add_right _ _,
        Or.inr (by dsimp only; rw [timeA, pushA]; rfl)⟩
    · exact ⟨pushB.trans locB.symm, Nat.le_add_right _ _,
        by dsimp only; rw [locB]; exact le_rfl, Or.inl ⟨rfl, timeB⟩⟩
    · exact ⟨pushC.trans locC.symm, Nat.le_add_right _ _,
        by dsimp only; rw [locC]; change start state + 2 ≤ start state + 3; omega, Or.inl ⟨rfl, timeC⟩⟩
  · intro loc
    rcases eq_or_ne loc (MemLoc.reg 5#5) with rfl | n5
    · simp [touches, pushA, pushB, pushC]
    rcases eq_or_ne loc (MemLoc.reg 10#5) with rfl | n10
    · simp [touches, pushA, pushB, pushC]
    rcases eq_or_ne loc (MemLoc.reg 11#5) with rfl | n11
    · simp [touches, pushA, pushB, pushC]
    · simp [touches, pushA, pushB, pushC, Ne.symm n5, Ne.symm n10, Ne.symm n11]
  · intro touch member
    simp only [touches, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    exacts [boundA, boundB, boundC]
  · intro touch member bound
    simp only [touches, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds _ _ _ _ _ bound timestamps.1 rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds _ _ _ _ _ bound timestamps.2.1 rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds _ _ _ _ _ bound timestamps.2.2 rfl rfl rfl

end SP1Clean.Soundness.SystemTouches
