import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.FormalModel.Contracts.SystemChips

/-! # State-message canonicalization (W3 D2, external report Finding 2)

The numeric re-limbing under which a StateBump row's pull and push become the *same* vertex, so its
edge cancels from the endpoint balance (`GoodnessFilter.endpointBalanced_of_cancel_loops`) and the
strictly-ranked instruction residue feeds the unchanged `RankedGrounding` engine.

`canonState` rebuilds a State message from its two semantic values — the ℕ time
`StateMsg.timeNat` and the ℕ pc `StateMsg.pcVal` — in canonical limbs. It is a plain function of
those values (`canonState_congr`), so proving a bump edge cancels reduces to proving its two sides
carry equal time and pc values. That is `stateBump_canon_eq`, this file's keystone: from the
chip's `Spec` (phase 0) and the pulled side's goodness — `clk_high < 2^24` from the filter's first
pass, `pc1, pc2 < 2^16` from its second — the field-level carry/borrow relations lift to exact ℕ
equalities. The goodness hypotheses are not decoration: without them the field relations admit the
`p − 1` wrap solutions (a pulled `clk_high` of `-1` under a carry, a pulled `pc1` of `-1` under a
borrow) in which the two sides genuinely denote *different* numbers, and killing exactly those
solutions is what the goodness filter is for.

`timeNat_canonState` is the transport the trail needs afterwards: on `clk_high`-good messages the
re-limbing preserves the time, so the instruction rows' strict `+8`/`+264` rank survives
canonicalization unchanged. Everything here is ensemble-independent; wiring it into the typed
State decomposition is the cutover. -/

namespace SP1Clean.Soundness

open SP1Clean.Channels (StateMsg)
open SP1Clean.Semantics (clkNat)

variable {p : ℕ} [Fact p.Prime]

/-- The ℕ-decoded 48-bit pc value of a State message (the pre-truncation form of
`StateMsg.pcBits`). -/
def StateMsg.pcVal (m : StateMsg (ZMod p)) : ℕ :=
  m.pc0.val + m.pc1.val * 2 ^ 16 + m.pc2.val * 2 ^ 32

/-- Canonical re-limbing of a State message from its ℕ time and pc values: the clock split at
`2^24`, the pc split into three 16-bit limbs. -/
def canonState (m : StateMsg (ZMod p)) : StateMsg (ZMod p) :=
  ⟨((Semantics.StateMsg.timeNat m / 2 ^ 24 : ℕ) : ZMod p),
   ((Semantics.StateMsg.timeNat m % 2 ^ 24 : ℕ) : ZMod p),
   ((StateMsg.pcVal m % 2 ^ 16 : ℕ) : ZMod p),
   ((StateMsg.pcVal m / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
   ((StateMsg.pcVal m / 2 ^ 32 : ℕ) : ZMod p)⟩

/-- `canonState` is a function of the two semantic values. -/
theorem canonState_congr {m m' : StateMsg (ZMod p)}
    (ht : Semantics.StateMsg.timeNat m = Semantics.StateMsg.timeNat m')
    (hpc : StateMsg.pcVal m = StateMsg.pcVal m') : canonState m = canonState m' := by
  simp only [canonState, ht, hpc]

/-- On a `clk_high`-good message the re-limbing preserves the time, so the instruction rows'
strict clock rank survives canonicalization. (`2^25 < p` gives the quotient limb room: the time of
a good message is below `2^48 + p ≤ p · 2^24`.) -/
theorem timeNat_canonState [Fact (2 ^ 25 < p)] {m : StateMsg (ZMod p)}
    (h : m.clk_high.val < 2 ^ 24) :
    Semantics.StateMsg.timeNat (canonState m) = Semantics.StateMsg.timeNat m := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have hlo : m.clk_low.val < p := ZMod.val_lt _
  set t := Semantics.StateMsg.timeNat m with ht
  have ht' : t = m.clk_high.val * 2 ^ 24 + m.clk_low.val := rfl
  have hdiv : t / 2 ^ 24 < p := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)
  have hmod : t % 2 ^ 24 < p := lt_trans (Nat.mod_lt _ (by norm_num)) (by omega)
  show ((t / 2 ^ 24 : ℕ) : ZMod p).val * 2 ^ 24 + ((t % 2 ^ 24 : ℕ) : ZMod p).val = t
  rw [ZMod.val_natCast_of_lt hdiv, ZMod.val_natCast_of_lt hmod]
  omega

/-- On a message with genuine 16-bit *upper* pc limbs the re-limbing preserves the 64-bit pc image:
the three canonical limb values recombine to exactly `StateMsg.pcVal m`, and each canonical limb
value stays below `p` — `pc0` needs no bound of its own because the top-limb quotient
`pcVal / 2^32` stays below `p` once `pc1`/`pc2` are 16-bit (`pcVal < p + 2^48 < p · 2^32`).  This
is the pc companion of `timeNat_canonState`, consumed by the capstone's `PcWalk` transport. -/
theorem pcBits_canonState [Fact (2 ^ 25 < p)] {m : StateMsg (ZMod p)}
    (hpc1 : m.pc1.val < 2 ^ 16) (hpc2 : m.pc2.val < 2 ^ 16) :
    Semantics.StateMsg.pcBits (canonState m) = Semantics.StateMsg.pcBits m := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have hpc0 : m.pc0.val < p := ZMod.val_lt _
  have hval : StateMsg.pcVal m = m.pc0.val + m.pc1.val * 2 ^ 16 + m.pc2.val * 2 ^ 32 := rfl
  simp only [Semantics.StateMsg.pcBits, Semantics.pcBits, canonState]
  set v := StateMsg.pcVal m with hv
  have h0 : v % 2 ^ 16 < p := lt_trans (Nat.mod_lt _ (by norm_num)) (by omega)
  have h1 : v / 2 ^ 16 % 2 ^ 16 < p := lt_trans (Nat.mod_lt _ (by norm_num)) (by omega)
  have h2 : v / 2 ^ 32 < p := by omega
  rw [ZMod.val_natCast_of_lt h0, ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2]
  congr 1
  omega

/-- The canonical clock limbs really are canonical: the low limb of any canonicalized message is a
genuine 24-bit value. -/
theorem canonState_clk_low_lt [Fact (2 ^ 25 < p)] (m : StateMsg (ZMod p)) :
    (canonState m).clk_low.val < 2 ^ 24 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  exact lt_of_le_of_lt
    (le_of_eq (ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by omega))))
    (Nat.mod_lt _ (by norm_num))

/-- A State message already in canonical limbs is a fixed point of the re-limbing: on genuine
24-bit clock limbs and 16-bit pc limbs the div/mod recomputation returns exactly the original
field elements.  This is what identifies the (canonical-by-construction) boundary verifier's
endpoints with their canonicalized images.  Only the three *lower*-limb bounds are consumed: each
div/mod identity recovers a limb from the bounds of the limbs below it, and the top limbs
(`clk_high`, `pc2`) round-trip through `ZMod.val` unconditionally. -/
theorem canonState_eq_self {m : StateMsg (ZMod p)}
    (hclkLow : m.clk_low.val < 2 ^ 24)
    (hpc0 : m.pc0.val < 2 ^ 16) (hpc1 : m.pc1.val < 2 ^ 16) :
    canonState m = m := by
  have htime : Semantics.StateMsg.timeNat m = m.clk_high.val * 2 ^ 24 + m.clk_low.val := rfl
  have hpc : StateMsg.pcVal m = m.pc0.val + m.pc1.val * 2 ^ 16 + m.pc2.val * 2 ^ 32 := rfl
  have h1 : ((Semantics.StateMsg.timeNat m / 2 ^ 24 : ℕ) : ZMod p) = m.clk_high := by
    rw [show Semantics.StateMsg.timeNat m / 2 ^ 24 = m.clk_high.val by omega,
      ZMod.natCast_zmod_val]
  have h2 : ((Semantics.StateMsg.timeNat m % 2 ^ 24 : ℕ) : ZMod p) = m.clk_low := by
    rw [show Semantics.StateMsg.timeNat m % 2 ^ 24 = m.clk_low.val by omega,
      ZMod.natCast_zmod_val]
  have h3 : ((StateMsg.pcVal m % 2 ^ 16 : ℕ) : ZMod p) = m.pc0 := by
    rw [show StateMsg.pcVal m % 2 ^ 16 = m.pc0.val by omega, ZMod.natCast_zmod_val]
  have h4 : ((StateMsg.pcVal m / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p) = m.pc1 := by
    rw [show StateMsg.pcVal m / 2 ^ 16 % 2 ^ 16 = m.pc1.val by omega, ZMod.natCast_zmod_val]
  have h5 : ((StateMsg.pcVal m / 2 ^ 32 : ℕ) : ZMod p) = m.pc2 := by
    rw [show StateMsg.pcVal m / 2 ^ 32 = m.pc2.val by omega, ZMod.natCast_zmod_val]
  show (⟨_, _, _, _, _⟩ : StateMsg (ZMod p)) = m
  rw [h1, h2, h3, h4, h5]

section StateBump

open SP1Clean.StateBumpChip

variable [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- A boolean field element's value facts, packaged for the ℕ lifts below. -/
private lemma binary_val {b : ZMod p} (h : b = 0 ∨ b = 1) :
    b.val ≤ 1 ∧ (b.val = 0 ∧ b = 0 ∨ b.val = 1 ∧ b = 1) := by
  haveI : Fact (1 < p) := ⟨(Fact.out (p := p.Prime)).one_lt⟩
  rcases h with h | h
  · exact ⟨by rw [h, ZMod.val_zero]; omega, Or.inl ⟨by rw [h, ZMod.val_zero], h⟩⟩
  · exact ⟨by rw [h, ZMod.val_one], Or.inr ⟨by rw [h, ZMod.val_one], h⟩⟩

omit [Fact (2 ^ 17 < p)] in
/-- Recombination lift: `(x + y * k).val = x.val + y.val * k` once the ℕ result fits below `p`,
for a constant `k` given by its value equation. -/
lemma val_recombine {x y kz : ZMod p} {k : ℕ} (hkz : kz.val = k)
    (hlt : x.val + y.val * k < p) : (x + y * kz).val = x.val + y.val * k := by
  have hmul : (y * kz).val = y.val * k := by
    rw [ZMod.val_mul_of_lt (by rw [hkz]; omega), hkz]
  rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]

/-- The State message a StateBump row pulls — the possibly-non-canonical incoming state
(the ZMod-level mirror of the circuit's `pulledMsg`). -/
def StateBumpChip.pulledMessage (r : Inputs (ZMod p)) : StateMsg (ZMod p) :=
  ⟨r.clk_high, r.clk_low, r.pc0, r.pc1, r.pc2⟩

/-- The State message a StateBump row pushes — the canonically re-limbed state
(the ZMod-level mirror of the circuit's `pushedMsg`). -/
def StateBumpChip.pushedMessage (r : Inputs (ZMod p)) : StateMsg (ZMod p) :=
  ⟨r.next_clk_24_32 + r.next_clk_32_48 * 256, r.next_clk_0_16 + r.next_clk_16_24 * 65536,
    r.next_pc0, r.next_pc1, r.next_pc2⟩

/-- **The bump cancellation keystone.** On a real StateBump row whose pulled side is good — the
filter's two passes: `clk_high < 2^24`, `pc1, pc2 < 2^16` — the pulled and pushed messages
canonicalize identically, so the row's edge is a self-loop of the canonicalized balance and
cancels. The proof lifts the `Spec`'s field-level carry/borrow relations to ℕ; the goodness
hypotheses rule out exactly the `p − 1` wrap solutions. -/
theorem stateBump_canon_eq [Fact (2 ^ 25 < p)] {r : Inputs (ZMod p)}
    (hspec : Spec r) (hreal : r.is_real = 1)
    (hgood_clk : r.clk_high.val < 2 ^ 24)
    (hgood_pc1 : r.pc1.val < 2 ^ 16) (hgood_pc2 : r.pc2.val < 2 ^ 16) :
    canonState (StateBumpChip.pulledMessage r) = canonState (StateBumpChip.pushedMessage r) := by
  have hp25 := Fact.out (p := 2 ^ 25 < p)
  obtain ⟨-, hisclk, ⟨b0, b1, hb0, hb1, e0, e1, e2⟩, hgated⟩ := hspec
  obtain ⟨h13, h1624, h2432, h3248, hpc0, hpc1, hpc2, eqhi, eqlo⟩ := hgated hreal
  obtain ⟨hisclkLe, -⟩ := binary_val hisclk
  obtain ⟨hb0Le, -⟩ := binary_val hb0
  obtain ⟨hb1Le, -⟩ := binary_val hb1
  have v65536 : ((65536 : ZMod p)).val = 65536 := by
    rw [show ((65536 : ZMod p)) = ((65536 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)]
  -- The pushed low clock is a genuine 24-bit value (its limbs are range-checked).
  have hpushLoLt : (r.next_clk_0_16 + r.next_clk_16_24 * 65536).val < 2 ^ 24 := by
    have := Channels.MemoryMsg.clkBound_of_cpuState_bounds r.next_clk_0_16 r.next_clk_16_24
      0 0 ZMod.val_zero (by norm_num) h13 h1624
    rwa [add_zero] at this
  -- Carry lifts: `pushedHigh = clk_high + is_clk` and `clk_low = pushedLow + is_clk · 2^24`
  -- hold as ℕ value equations (atomically in the pushed recombinations).
  have hcarryHi : (r.next_clk_24_32 + r.next_clk_32_48 * 256).val
      = r.clk_high.val + r.is_clk.val := by
    rw [eqhi, ZMod.val_add_of_lt (by omega)]
  have hcarryLo : r.clk_low.val
      = (r.next_clk_0_16 + r.next_clk_16_24 * 65536).val + r.is_clk.val * 2 ^ 24 := by
    have v224 : ((16777216 : ZMod p)).val = 2 ^ 24 := by
      rw [show ((16777216 : ZMod p)) = ((16777216 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt (by omega)]
      norm_num
    have hmul : (r.is_clk * 16777216).val = r.is_clk.val * 2 ^ 24 := by
      rw [ZMod.val_mul_of_lt (by rw [v224]; omega), v224]
    rw [← eqlo, ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]
  have htime : Semantics.StateMsg.timeNat (StateBumpChip.pulledMessage r)
      = Semantics.StateMsg.timeNat (StateBumpChip.pushedMessage r) := by
    show r.clk_high.val * 2 ^ 24 + r.clk_low.val
      = (r.next_clk_24_32 + r.next_clk_32_48 * 256).val * 2 ^ 24
        + (r.next_clk_0_16 + r.next_clk_16_24 * 65536).val
    rw [hcarryHi, hcarryLo]
    ring
  -- Borrow lifts: each pc-limb equation holds as a ℕ value equation; the pulled `pc1`/`pc2`
  -- goodness bounds are what keep the left sides below `p`.
  have hlift0 : r.pc0.val = r.next_pc0.val + b0.val * 65536 := by
    rw [e0, val_recombine v65536 (by omega)]
  have hlift1 : b0.val + r.pc1.val = r.next_pc1.val + b1.val * 65536 := by
    have hlhs : (b0 + r.pc1).val = b0.val + r.pc1.val :=
      ZMod.val_add_of_lt (by omega)
    rw [← hlhs, e1, val_recombine v65536 (by omega)]
  have hlift2 : b1.val + r.pc2.val = r.next_pc2.val := by
    have hlhs : (b1 + r.pc2).val = b1.val + r.pc2.val :=
      ZMod.val_add_of_lt (by omega)
    rw [← hlhs, e2]
  have hpc : StateMsg.pcVal (StateBumpChip.pulledMessage r)
      = StateMsg.pcVal (StateBumpChip.pushedMessage r) := by
    show r.pc0.val + r.pc1.val * 2 ^ 16 + r.pc2.val * 2 ^ 32
      = r.next_pc0.val + r.next_pc1.val * 2 ^ 16 + r.next_pc2.val * 2 ^ 32
    omega
  exact canonState_congr htime hpc

/-- `stateBump_canon_eq` with its goodness hypotheses restated on the *pulled message's* fields.
The two spellings are definitionally equal, but crossing them at a decoded `valueFromOffset` row
would ask the unifier to normalize the row decoder; taking the message-level form here, over an
abstract `r`, performs the crossing once where `r` is opaque
(`docs/agents/perf-findings.md` §1). -/
theorem stateBump_canon_eq_of_pulled_good [Fact (2 ^ 25 < p)] {r : Inputs (ZMod p)}
    (hspec : Spec r) (hreal : r.is_real = 1)
    (hgood_clk : (StateBumpChip.pulledMessage r).clk_high.val < 2 ^ 24)
    (hgood_pc1 : (StateBumpChip.pulledMessage r).pc1.val < 2 ^ 16)
    (hgood_pc2 : (StateBumpChip.pulledMessage r).pc2.val < 2 ^ 16) :
    canonState (StateBumpChip.pulledMessage r) = canonState (StateBumpChip.pushedMessage r) :=
  stateBump_canon_eq hspec hreal hgood_clk hgood_pc1 hgood_pc2

omit [Fact (2 ^ 17 < p)] in
/-- The pushed message of a real StateBump row is good by construction: its re-limbed `clk_high`
is a genuine 24-bit value and its upper pc limbs are 16-bit — the `Spec`'s in-circuit range
checks, hoisted onto the message projections.  These are the goodness filter's consumer-target
facts for the bump edges in both passes. -/
theorem stateBump_pushedMessage_good [Fact (2 ^ 25 < p)] {r : Inputs (ZMod p)}
    (hspec : Spec r) (hreal : r.is_real = 1) :
    (StateBumpChip.pushedMessage r).clk_high.val < 2 ^ 24 ∧
      (StateBumpChip.pushedMessage r).pc1.val < 2 ^ 16 ∧
      (StateBumpChip.pushedMessage r).pc2.val < 2 ^ 16 := by
  have hp25 := Fact.out (p := 2 ^ 25 < p)
  obtain ⟨-, -, -, hgated⟩ := hspec
  obtain ⟨-, -, h2432, h3248, -, hpc1, hpc2, -, -⟩ := hgated hreal
  refine ⟨?_, hpc1, hpc2⟩
  have v256 : ((256 : ZMod p)).val = 256 := by
    rw [show ((256 : ZMod p)) = ((256 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)]
  show (r.next_clk_24_32 + r.next_clk_32_48 * 256).val < 2 ^ 24
  rw [val_recombine v256 (by omega)]
  omega

end StateBump

end SP1Clean.Soundness
