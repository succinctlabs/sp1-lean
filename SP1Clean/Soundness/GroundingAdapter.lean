import SP1Clean.Soundness.RowSoundness
import SP1Clean.Soundness.TypedTimeContracts
import SP1Clean.Proofs.Chips.AddChip.Contracts

/-! # The grounding adapter — `ChipKind.advance` → the timed-engine per-row records

The generic bridge from a migrated chip's `ChipKind.advance` payload to the two per-row inputs the
timed grounding engine (`Soundness/TimedGrounding.lean`) consumes: the row's `LocalStepFact` (pulled
state truth + pull currency ⟹ pushed state truth + pushed Memory truths) and its `FrameFact`
(value persistence across the row's window at every location the row does not change).

The statement-level design (validated by the SP-2 spike): the adapter needs one per-row `RowWiring`
bundle — the message ↔ `RowView` correspondences between the row's semantic bus records
(`Semantics.RowFacts`) and the view its `advance` speaks about.  Most fields are `rfl`/bound
extractions; the one genuinely load-bearing discovery is `write_push` — *the op_a write push must be
present in the row's push multiset* — a completeness-of-emission fact channel balance alone does not
force, consumed by `FrameFact`'s written-register case.

Wiring is per-reader-shape, not per-chip: `rowWiring_rtype` below discharges the whole bundle for
any R-type-adapter row from a handful of in-circuit numeric facts (the CPUState clock byte bounds,
the reader's `op_a < 32` decode bound, the write value's range check, and the chip's exact
consumed/produced Memory lists).  Add is the concrete anchor: its exact Memory emissions are
evaluated from `AddChip.exposedMemoryInteractions`, and `addRow_engineFacts` runs a genuine decoded
Add row end-to-end through the adapter. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Functions
open Air.Flat Circuit
open SP1Clean.Soundness.Target
open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## View-level State message projections -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The pull message denoted by a view recombines to the view's receive-side 64-bit pc. -/
theorem pcBits_statePullOfView (view : Trace.RowView (ZMod p)) :
    StateMsg.pcBits (statePullOfView view) = rcvPcOf (stateAccess view) := by
  simp [StateMsg.pcBits, Semantics.pcBits, statePullOfView, rcvPcOf, pcBitsOfVals, stateAccess]

omit [Fact (2 ^ 17 < p)] in
/-- The push message denoted by a view recombines to the view's send-side 64-bit pc. -/
theorem pcBits_statePushOfView (view : Trace.RowView (ZMod p)) :
    StateMsg.pcBits (statePushOfView view) = sndPcOf (stateAccess view) := by
  simp [StateMsg.pcBits, Semantics.pcBits, statePushOfView, sndPcOf, pcBitsOfVals, stateAccess]

/-! ## The advance payload, named -/

/-- The proposition carried by a migrated `ChipKind.advance` field (definitionally the `PLift`
content).  Naming it lets the adapter theorems take the payload as an ordinary hypothesis. -/
def ChipKind.AdvancePayload (kind : ChipKind p) : Prop :=
  ∀ (inp : kind.Inputs (ZMod p)) (cols : kind.Cols (ZMod p)) (data : ProverData (ZMod p))
      (prog : Target.GuestProgram) (s : SailState),
    (kind.view inp cols).is_real = 1 →
    kind.chipSpec inp cols data →
    Target.SailConfigured s → Target.RomLoaded prog s →
    s.regs.get? Register.PC = some (Target.rcvPcOf (stateAccess (kind.view inp cols))) →
    Target.ValueOperandsBound (kind.view inp cols) s →
    Target.decodedInROM prog (programAccess (kind.view inp cols)).toRow →
    kind.advanceReady inp cols prog s →
    ∃ s', Target.SailStep s s' ∧ Target.RowEffect prog (kind.view inp cols) s s'

/-- Extract the named payload from a migrated registry entry. -/
theorem ChipKind.advancePayload_of_migrated {kind : ChipKind p}
    (migrated : kind.advance.isSome = true) : kind.AdvancePayload := by
  obtain ⟨payload, -⟩ := Option.isSome_iff_exists.mp migrated
  exact payload.down

/-! ## The per-row wiring bundle -/

/-- **The per-row message ↔ view correspondence** consumed by the adapter.  `view` is the row view
the chip's `advance` payload speaks about; `rf` is the row's semantic bus record.  All time facts
are already ℕ-decoded (the field → ℕ step is the wiring producer's obligation, from the CPUState
byte bounds).  `push_classified` sorts every Memory push into a pre-effect read-back of one of the
row's own pulls or the `op_a` register write at the `+ 4` effect slot; `write_push` additionally
asserts the write push is *present* whenever the row commits a register write — the one
completeness-of-emission fact balance does not force. -/
structure RowWiring (view : Trace.RowView (ZMod p)) (rf : Semantics.RowFacts p) : Prop where
  /-- The record's state pull is the view's canonical pull message. -/
  statePull_eq : rf.statePull = statePullOfView view
  /-- The record's state push is the view's canonical push message. -/
  statePush_eq : rf.statePush = statePushOfView view
  /-- The ℕ-decoded eight-tick clock step. -/
  time8 : StateMsg.timeNat rf.statePush = StateMsg.timeNat rf.statePull + 8
  /-- Every pull is read at the row's window start (the ordinary currency point). -/
  readTime : ∀ mp ∈ rf.memPulls, mp.2 = StateMsg.timeNat rf.statePull
  /-- A register `op_b` source operand is carried by one of the row's pulls. -/
  opB_pull : ∀ index : BitVec 5, view.adapter.imm_b = 0 →
    (index.toNat : ZMod p) = view.adapter.op_b[0] →
    ∃ mp ∈ rf.memPulls, MemoryMsg.locOf mp.1 = MemLoc.reg index ∧
      mp.1.value = view.adapter.op_b_memory.prev_value
  /-- A register `op_c` source operand is carried by one of the row's pulls. -/
  opC_pull : ∀ index : BitVec 5, view.adapter.imm_c = 0 →
    (index.toNat : ZMod p) = view.adapter.op_c[0] →
    ∃ mp ∈ rf.memPulls, MemoryMsg.locOf mp.1 = MemLoc.reg index ∧
      mp.1.value = view.adapter.op_c_memory.prev_value
  /-- On a register-writing row, the `op_a` write push is present in the push list. -/
  write_push : view.commit.writesReg = true →
    ∀ index : BitVec 5, (index.toNat : ZMod p) = view.adapter.op_a →
    ∃ m ∈ rf.memPushes, MemoryMsg.locOf m = MemLoc.reg index ∧ m.value = view.rdWrite
  /-- Every push is a pre-effect read-back of one of the row's own pulls, or the committed `op_a`
  register write at the `+ 4` effect slot (with its in-circuit range check). -/
  push_classified : ∀ m ∈ rf.memPushes,
    (∃ mp ∈ rf.memPulls, MemoryMsg.locOf m = MemoryMsg.locOf mp.1 ∧ m.value = mp.1.value ∧
      StateMsg.timeNat rf.statePull ≤ MemoryMsg.timeNat m ∧
      MemoryMsg.timeNat m < StateMsg.timeNat rf.statePull + 4) ∨
    (view.commit.writesReg = true ∧ MemoryMsg.isU64 m ∧
      (∃ index : BitVec 5, MemoryMsg.locOf m = MemLoc.reg index ∧
        (index.toNat : ZMod p) = view.adapter.op_a) ∧
      m.value = view.rdWrite ∧
      MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull + 4)
  /-- The row commits no RAM write (register-axis chips; stores are a later batch). -/
  no_ram_write : view.commit.memWrite = none

/-! ## Firing the payload at the pulled state -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- RAM words are untouched by a pointwise memory frame. -/
theorem locContent_ram_congr {s s' : SailState}
    (frame : ∀ a : ℕ, s'.mem.get? a = s.mem.get? a) (a : BitVec 64) :
    locContent s' (MemLoc.ram a) = locContent s (MemLoc.ram a) := by
  simp only [locContent, ramWord64?, frame]

/-- Fire a chip's advance payload at the exact chain state selected by the row's pulled State
record: the pull truth supplies platform configuration, ROM presence, and the committed pc; pull
currency at the window start supplies `ValueOperandsBound` through `localValueAt_stepStart_iff`. -/
theorem RowWiring.advance_at {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, kind.advanceReady inp cols program s)
    {initial state : SailState} {initialClock n : ℕ}
    (chain : SailChain n initial state)
    (htime : StateMsg.timeNat rf.statePull = initialClock + 8 * n)
    (hpc : state.regs.get? Register.PC = some (StateMsg.pcBits rf.statePull))
    (hrom : RomLoaded program state) (hcfg : SailConfigured state)
    (curr : ∀ mp ∈ rf.memPulls, MemoryMsg.isU64 mp.1 ∧
      LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ s', SailStep state s' ∧ RowEffect program (kind.view inp cols) state s' := by
  have operands : ValueOperandsBound (kind.view inp cols) state := by
    constructor
    · intro index himm hidx
      obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opB_pull index himm hidx
      have hc := (curr mp hmp).2
      rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
      exact (localValueAt_stepStart_iff chain).mp hc
    · intro index himm hidx
      obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opC_pull index himm hidx
      have hc := (curr mp hmp).2
      rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
      exact (localValueAt_stepStart_iff chain).mp hc
  rw [wiring.statePull_eq, pcBits_statePullOfView] at hpc
  exact advance inp cols data program state real spec hcfg hrom hpc operands decode (ready state)

/-! ## The step fact -/

/-- **The generic step fact** (SP-2's `stepFact_of_advance`): a migrated chip's `advance` payload
plus its row wiring and the row's static facts produce the timed engine's `LocalStepFact`.  The
seven register-axis crux steps: the pulled state truth selects the chain state; pull currency at the
window start gives `ValueOperandsBound`; the payload fires one real Sail step with the committed
`RowEffect`; the chain extends; the pushed state truth re-assembles at `n + 1`; read-back pushes
shift inside the pre-effect epoch; and the `op_a` write push lands at the `+ 4` effect slot of the
extended trajectory. -/
theorem stepFact_of_advance {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, kind.advanceReady inp cols program s)
    (initial : SailState) (initialClock : ℕ) :
    LocalStepFact program initial initialClock rf := by
  intro hpull hcurr
  obtain ⟨n, state, chain, htime, hpc, hrom, hcfg⟩ := hpull
  have hpull' : LocalStateTruth program initial initialClock rf.statePull :=
    ⟨n, state, chain, htime, hpc, hrom, hcfg⟩
  obtain ⟨s', hstep, heff⟩ :=
    wiring.advance_at advance real spec decode ready chain htime hpc hrom hcfg hcurr
  have chain' : SailChain (n + 1) initial s' := chain.snoc hstep
  have hcs : chainState initial n = some state := chainState_of_sailChain chain
  have hcs' : chainState initial (n + 1) = some s' :=
    chainState_succ_of hcs (stepOnce_of_sailStep hstep)
  refine ⟨?_, ?_⟩
  · -- the pushed state truth, one window later
    refine localStateTruth_of_sailChain chain' ?_ ?_ (heff.rom hrom) (heff.cfg hcfg)
    · rw [wiring.time8, htime]
      omega
    · rw [wiring.statePush_eq, pcBits_statePushOfView]
      exact heff.pc
  · -- every pushed Memory record is true
    intro m hm
    rcases wiring.push_classified m hm with
      ⟨mp, hmp, hloc, hval, hlo, hhi⟩ | ⟨hw, hu64, ⟨idx, hlocw, hidx⟩, hvalw, htw⟩
    · -- read-back: the pull's currency, shifted inside the pre-effect epoch
      have hc := (hcurr mp hmp).2
      rw [wiring.readTime mp hmp] at hc
      have hu : MemoryMsg.isU64 m := by
        show Word.isU64 m.value
        rw [hval]
        exact (hcurr mp hmp).1
      refine ⟨hu, ?_⟩
      rw [hloc, hval]
      cases hlocmp : MemoryMsg.locOf mp.1 with
      | reg i =>
        rw [hlocmp] at hc
        exact localValueAt_shift hpull' (Or.inl ⟨le_refl _, by omega, hlo, hhi⟩) hc
      | ram a =>
        rw [hlocmp] at hc
        by_cases heq : MemoryMsg.timeNat m = StateMsg.timeNat rf.statePull
        · rw [heq]
          exact hc
        · unfold LocalValueAt at hc ⊢
          rw [microValue_ram] at hc ⊢
          rw [htime] at hc
          rw [ramEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hc
          rw [ramEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
          show locContent s' (MemLoc.ram a) = some (Word.toBitVec64 mp.1.value)
          rw [locContent_ram_congr (heff.mem.1 wiring.no_ram_write) a]
          exact hc
    · -- the op_a write: the new register value at the `+ 4` effect slot
      refine ⟨hu64, ?_⟩
      rw [hlocw, hvalw, htw, htime]
      unfold LocalValueAt
      rw [microValue_reg, regEpoch_eq_succ_of (n := n) (by omega) (by omega), hcs']
      show locContent s' (MemLoc.reg idx) = some (Word.toBitVec64 (kind.view inp cols).rdWrite)
      have hregs := heff.regs
      rw [if_pos hw] at hregs
      exact hregs.1 idx hidx

/-! ## The frame fact -/

/-- **The generic frame fact** (SP-2's `frameFact_of_advance`): under the same hypotheses, the
`RowEffect`'s frame halves advance any untouched location's value across the row's window — both
`writesReg` cases on the register axis, and the pointwise memory frame on the RAM axis. -/
theorem frameFact_of_advance {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, kind.advanceReady inp cols program s)
    (initial : SailState) (initialClock : ℕ) :
    FrameFact program initial initialClock rf := by
  intro hpull hcurr loc v hpush hval
  obtain ⟨n, state, chain, htime, hpc, hrom, hcfg⟩ := hpull
  obtain ⟨s', hstep, heff⟩ :=
    wiring.advance_at advance real spec decode ready chain htime hpc hrom hcfg hcurr
  have chain' : SailChain (n + 1) initial s' := chain.snoc hstep
  rw [htime] at hval
  have hcontent : locContent state loc = some (Word.toBitVec64 v) :=
    (localValueAt_stepStart_iff chain).mp hval
  have hpushTime : StateMsg.timeNat rf.statePush = initialClock + 8 * (n + 1) := by
    rw [wiring.time8, htime]
    omega
  rw [hpushTime]
  apply (localValueAt_stepStart_iff chain').mpr
  cases loc with
  | ram a =>
    rw [locContent_ram_congr (heff.mem.1 wiring.no_ram_write) a]
    exact hcontent
  | reg i =>
    show s'.get_reg? i = some (Word.toBitVec64 v)
    have hregs := heff.regs
    by_cases hw : (kind.view inp cols).commit.writesReg = true
    · rw [if_pos hw] at hregs
      by_cases hop : (i.toNat : ZMod p) = (kind.view inp cols).adapter.op_a
      · -- the written register: the pushed write value is pinned to `v` by `hpush`
        obtain ⟨m, hm, hlocm, hvalm⟩ := wiring.write_push hw i hop
        have hveq : m.value = v := hpush m hm hlocm
        rw [hregs.1 i hop, ← hvalm, hveq]
      · rw [hregs.2 i hop]
        exact hcontent
    · rw [if_neg hw] at hregs
      rw [hregs i]
      exact hcontent

/-! ## The dispatcher over the heterogeneous row -/

/-- **The dispatcher-shaped composite** (SP-2's `engineFacts_of_kind`): any migrated registry row
with its wiring and static facts yields both engine records at once. -/
theorem engineFacts_of_kind {row : ChipRow p} {rf : Semantics.RowFacts p}
    (migrated : row.kind.advance.isSome = true)
    (wiring : RowWiring row.view rf)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : row.is_real = 1)
    (spec : row.chipSpec data)
    (decode : Target.decodedInROM program (programAccess row.view).toRow)
    (ready : ∀ s : SailState, row.kind.advanceReady row.inputs row.cols program s)
    (initial : SailState) (initialClock : ℕ) :
    LocalStepFact program initial initialClock rf ∧
      FrameFact program initial initialClock rf := by
  have advance := ChipKind.advancePayload_of_migrated migrated
  exact ⟨stepFact_of_advance wiring advance real spec decode ready initial initialClock,
    frameFact_of_advance wiring advance real spec decode ready initial initialClock⟩

/-! ## The R-type reader-shape wiring

Everything below is the first reader-shape batch: the field → ℕ decoding of the intra-row effect
slots (`+ 2` / `+ 3` / `+ 4` / `+ 8`, from the CPUState clock byte bounds), the canonical R-type
Memory message shapes, and `rowWiring_rtype` — the whole `RowWiring` bundle from those numeric
facts.  The i-type/load/store shapes are later batches. -/

section RType

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- The two CPUState byte bounds decode any small field clock increment as an exact ℕ increment —
the `+ 2`/`+ 3`/`+ 4` effect-slot generalization of
`TimeExtraction.clkNat_add_eight_of_cpuState_bounds`. -/
theorem clkNat_add_delta_of_cpuState_bounds (clkHigh clk0 clk1 delta : ZMod p) (k : ℕ)
    (hdelta : delta.val = k) (hk : k ≤ 8)
    (clk0Bound : ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1Bound : clk1.val < 2 ^ 8) :
    clkNat clkHigh (clk0 + clk1 * 65536 + delta) =
      clkNat clkHigh (clk0 + clk1 * 65536) + k := by
  let scaled := (clk0 - 1) * (8 : ZMod p)⁻¹
  have eightNe : (8 : ZMod p) ≠ 0 := val_8_ne_zero
  have scaledBound : scaled.val < 2 ^ 13 := clk0Bound
  have reconstruct : scaled * 8 + 1 = clk0 := by
    dsimp only [scaled]
    rw [mul_assoc, inv_mul_cancel₀ eightNe, mul_one]
    ring_nf
  have scaledMulLt : scaled.val * (8 : ZMod p).val < p := by
    rw [val_8_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have scaledMulVal : (scaled * 8).val = scaled.val * 8 := by
    rw [ZMod.val_mul_of_lt scaledMulLt, val_8_zmod_p]
  have clk0AddLt : (scaled * 8).val + (1 : ZMod p).val < p := by
    rw [scaledMulVal, ZMod.val_one]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have clk0Val : clk0.val = scaled.val * 8 + 1 := by
    calc
      clk0.val = (scaled * 8 + 1).val := congrArg ZMod.val reconstruct.symm
      _ = (scaled * 8).val + (1 : ZMod p).val := ZMod.val_add_of_lt clk0AddLt
      _ = scaled.val * 8 + 1 := by rw [scaledMulVal, ZMod.val_one]
  have highLimbMulLt : clk1.val * (65536 : ZMod p).val < p := by
    rw [val_65536_zmod_p]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have highLimbVal : (clk1 * 65536).val = clk1.val * 65536 := by
    rw [ZMod.val_mul_of_lt highLimbMulLt, val_65536_zmod_p]
  have lowAddLt : clk0.val + (clk1 * 65536).val < p := by
    rw [clk0Val, highLimbVal]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have lowVal : (clk0 + clk1 * 65536).val = clk0.val + clk1.val * 65536 := by
    rw [ZMod.val_add_of_lt lowAddLt, highLimbVal]
  have incrementAddLt : (clk0 + clk1 * 65536).val + delta.val < p := by
    rw [lowVal, clk0Val, hdelta]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have incrementedVal : (clk0 + clk1 * 65536 + delta).val =
      (clk0 + clk1 * 65536).val + k := by
    rw [ZMod.val_add_of_lt incrementAddLt, hdelta]
  simp only [clkNat, incrementedVal]
  omega

/-- The two CPUState clock byte bounds, bound to a row view's committed state block. -/
structure ViewClockBounds (view : Trace.RowView (ZMod p)) : Prop where
  clk0 : ((view.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
  clk1 : view.state.clk_16_24.val < 2 ^ 8

/-- A retained `CPUState` reader plus the finished Byte guarantees bound the completed chip's view
clock limbs — the raw-bounds companion of `circuitStateTimeStep_of_cpuStateContract`, feeding the
`+ 2`/`+ 3`/`+ 4` effect-slot decodes that the eight-tick theorem does not expose. -/
theorem viewClockBounds_of_cpuStateContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitCPUStateTimeContract circuit view)
    (data : ProverData (ZMod p)) (physical : Array (ZMod p))
    (guarantees : (⟨circuit⟩ : Component (ZMod p)).operations.ChannelGuarantees
      Channels.byteChannel.toRaw (Environment.fromArray physical data))
    (real : (view ((⟨circuit⟩ : Component (ZMod p)).rowInput (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput (Environment.fromArray physical data))).is_real
        = 1) :
    ViewClockBounds (view
      ((⟨circuit⟩ : Component (ZMod p)).rowInput (Environment.fromArray physical data))
      ((⟨circuit⟩ : Component (ZMod p)).rowOutput (Environment.fromArray physical data))) := by
  unfold CircuitCPUStateTimeContract at contract
  dsimp only at contract
  obtain ⟨cpuOffset, cpuInput, cpuMem, binding⟩ := contract
  set component : Component (ZMod p) := ⟨circuit⟩ with hcomponent
  set env := Environment.fromArray physical data with henv
  have rowGuarantees : component.rowOperations.ChannelGuarantees Channels.byteChannel.toRaw env :=
    (Component.channelGuarantees_iff env Channels.byteChannel.toRaw).mp guarantees
  have cpuGuarantees := channelGuarantees_subcircuit_of_mem Channels.byteChannel.toRaw env
    component.rowOperations
    ((Readers.CPUState.circuit (p := p)).toSubcircuit cpuOffset cpuInput) cpuMem rowGuarantees
  have inputEq : Eval.eval env (varFromOffset Input 0) = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output (varFromOffset Input 0) (size Input)) =
      component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
  have bound := binding env
  rw [inputEq, outputEq] at bound
  have cpuReal : Expression.eval env cpuInput.is_real = 1 := bound.real_eq.trans real
  obtain ⟨clk0Bound, clk1Bound⟩ :=
    Readers.CPUState.bounds_of_byteGuarantees cpuInput cpuOffset env cpuGuarantees cpuReal
  constructor
  · rw [← bound.clk0_eq]
    exact clk0Bound
  · rw [← bound.clk1_eq]
    exact clk1Bound

/-! ### The canonical R-type Memory message shapes -/

omit [Fact (2 ^ 17 < p)] in
/-- `(3 : ZMod p)` decodes as the natural number 3 (the op_b read-back effect slot). -/
lemma val_3_zmod_p : (3 : ZMod p).val = 3 := by
  have : (2 ^ 25 : ℕ) < p := Fact.out
  exact ZMod.val_natCast_of_lt (show (3 : ℕ) < p by omega)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The read-prior pull message an R-type register slot consumes. -/
def rtypePriorMessage (view : Trace.RowView (ZMod p)) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high, access.access_timestamp.prev_low, index, 0, 0, access.prev_value⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The read-back push message an R-type register slot produces at effect offset `delta`. -/
def rtypeReadBackMessage (view : Trace.RowView (ZMod p)) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) (delta : ZMod p) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high, view.state.clk_0_16 + view.state.clk_16_24 * 65536 + delta,
   index, 0, 0, access.prev_value⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The committed `op_a` register-write push message at the `+ 4` effect slot. -/
def rtypeWriteMessage (view : Trace.RowView (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨view.state.clk_high, view.state.clk_0_16 + view.state.clk_16_24 * 65536 + 4,
   view.adapter.op_a, 0, 0, view.rdWrite⟩

omit [Fact (2 ^ 17 < p)] in
/-- A read-back push's decoded time is the window start plus its effect offset. -/
theorem timeNat_rtypeReadBackMessage {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) (index : ZMod p)
    (access : Extracted.RegisterAccessCols (ZMod p)) {delta : ZMod p} {k : ℕ}
    (hdelta : delta.val = k) (hk : k ≤ 8) :
    MemoryMsg.timeNat (rtypeReadBackMessage view index access delta) =
      StateMsg.timeNat (statePullOfView view) + k :=
  clkNat_add_delta_of_cpuState_bounds _ _ _ _ k hdelta hk bounds.clk0 bounds.clk1

omit [Fact (2 ^ 17 < p)] in
/-- The `op_a` write push's decoded time is the window start plus four. -/
theorem timeNat_rtypeWriteMessage {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) :
    MemoryMsg.timeNat (rtypeWriteMessage view) =
      StateMsg.timeNat (statePullOfView view) + 4 :=
  clkNat_add_delta_of_cpuState_bounds _ _ _ _ 4 val_4_zmod_p (by omega) bounds.clk0 bounds.clk1

omit [Fact (2 ^ 17 < p)] in
/-- The view's state push decodes exactly eight ticks after its state pull. -/
theorem timeNat_statePushOfView_eight {view : Trace.RowView (ZMod p)}
    (bounds : ViewClockBounds view) :
    StateMsg.timeNat (statePushOfView view) = StateMsg.timeNat (statePullOfView view) + 8 :=
  clkNat_add_delta_of_cpuState_bounds _ _ _ _ 8 val_8_zmod_p (le_refl 8) bounds.clk0 bounds.clk1

/-! ### The R-type wiring bundle -/

/-- **The R-type reader-shape wiring** (SP-2's `rowWiring_rtype`): for any row whose semantic bus
record has the canonical R-type shape — three read-prior pulls at the window start, two read-backs
at `+ 3`/`+ 2`, and the `op_a` write at `+ 4` — the whole `RowWiring` bundle follows from the
CPUState clock byte bounds, the reader's `op_a < 32` decode bound, and the write value's range
check.  No `op_b`/`op_c` register-index bound is needed: a read-back push re-asserts its own pull's
location and value, and the adapter's step fact handles both location kinds. -/
theorem rowWiring_rtype {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (bounds : ViewClockBounds view)
    (commit_eq : view.commit = Trace.CommitEffect.regWrite)
    (opa_lt : view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 view.rdWrite)
    (statePull_eq : rf.statePull = statePullOfView view)
    (statePush_eq : rf.statePush = statePushOfView view)
    (pulls_eq : rf.memPulls =
      [(rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
          StateMsg.timeNat rf.statePull),
       (rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
          StateMsg.timeNat rf.statePull)])
    (pushes_eq : rf.memPushes =
      [rtypeReadBackMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory 3,
       rtypeReadBackMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory 2,
       rtypeWriteMessage view]) :
    RowWiring view rf where
  statePull_eq := statePull_eq
  statePush_eq := statePush_eq
  time8 := by
    rw [statePull_eq, statePush_eq]
    exact timeNat_statePushOfView_eight bounds
  readTime := by
    intro mp hmp
    rw [pulls_eq] at hmp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmp
    rcases hmp with rfl | rfl | rfl <;> rfl
  opB_pull := by
    intro index himm hidx
    refine ⟨(rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  opC_pull := by
    intro index himm hidx
    refine ⟨(rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
      StateMsg.timeNat rf.statePull), ?_, ?_, rfl⟩
    · rw [pulls_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  write_push := by
    intro _ index hidx
    refine ⟨rtypeWriteMessage view, ?_, ?_, rfl⟩
    · rw [pushes_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact MemoryMsg.locOf_register _ index hidx rfl rfl
  push_classified := by
    intro m hm
    rw [pushes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · -- the op_b read-back at `+ 3`
      left
      refine ⟨(rtypePriorMessage view (view.adapter.op_b[0]) view.adapter.op_b_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega), ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_3_zmod_p (by omega), ← statePull_eq]
        omega
    · -- the op_c read-back at `+ 2`
      left
      refine ⟨(rtypePriorMessage view (view.adapter.op_c[0]) view.adapter.op_c_memory,
        StateMsg.timeNat rf.statePull), ?_, rfl, rfl, ?_, ?_⟩
      · rw [pulls_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega), ← statePull_eq]
        omega
      · rw [timeNat_rtypeReadBackMessage bounds _ _ val_2_zmod_p (by omega), ← statePull_eq]
        omega
    · -- the op_a write at `+ 4`
      right
      have hidx : ((BitVec.ofNat 5 view.adapter.op_a.val).toNat : ZMod p) =
          view.adapter.op_a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show view.adapter.op_a.val < 2 ^ 5 by omega)]
        exact ZMod.natCast_zmod_val _
      refine ⟨by rw [commit_eq]; rfl, write_isU64, ?_, rfl, ?_⟩
      · exact ⟨BitVec.ofNat 5 view.adapter.op_a.val,
          MemoryMsg.locOf_register _ _ hidx rfl rfl, hidx⟩
      · rw [timeNat_rtypeWriteMessage bounds, ← statePull_eq]
  no_ram_write := by
    rw [commit_eq]
    rfl

end RType

/-! ## The Add anchor

Add validates the whole pipeline: its exact Memory emissions are evaluated once from the circuit's
public exposed list (`AddChip.exposedMemoryInteractions`), the numeric wiring inputs are extracted
from the finished Byte channel, the chip `Spec`, and the row's own push `Requirements`, and
`addRow_engineFacts` produces both engine records for a genuine decoded Add row. -/

section AddAnchor

variable [Fact (2 ^ 25 < p)]

open SP1Clean.Channels (memoryChannel byteChannel)

omit [Fact (2 ^ 25 < p)] in
/-- The Add instruction descriptor (entry 0 of `supportedChips`). -/
def addChipDescriptor : SupportedChip p :=
  ⟨AddChip.kind, AddChip.circuit, rfl, [.ADD], .nonX0⟩

omit [Fact (2 ^ 25 < p)] in
/-- The Add row view denoted by one physical environment. -/
noncomputable def addViewOf (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  AddChip.rowView ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)

/-- The typed decoder's Add view is `addViewOf` at the row's physical environment — the descriptor's
retained circuit and its flat component agree by structure-literal projection. -/
theorem addViewOf_decodeRow (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    ((addChipDescriptor (p := p)).decodeRow data physical).view =
      addViewOf (Environment.fromArray physical data) := rfl

/-- The descriptor's flat table is the bare Add component — again structure-literal projection. -/
theorem addChipDescriptor_table :
    (addChipDescriptor (p := p)).table = (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)) := rfl

set_option maxHeartbeats 4000000 in
omit [Fact (2 ^ 25 < p)] in
/-- **Add's evaluated Memory interaction list**, in the canonical R-type message shapes over the
row view: the three read-prior pulls and the two read-backs + `op_a` write pushes, all gated by the
view's selector.  Evaluated once from the circuit's public exposed list. -/
theorem addChip_memoryInteractionValues_eq (env : Environment (ZMod p)) :
    (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).operations.interactionValuesWith
        (memoryChannel (p := p)).toRaw env =
      [memoryChannel.pulledIfValue (addViewOf env).is_real
         (rtypePriorMessage (addViewOf env) (addViewOf env).adapter.op_a
           (addViewOf env).adapter.op_a_memory),
       memoryChannel.pulledIfValue (addViewOf env).is_real
         (rtypePriorMessage (addViewOf env) ((addViewOf env).adapter.op_b[0])
           (addViewOf env).adapter.op_b_memory),
       memoryChannel.pushedIfValue (addViewOf env).is_real
         (rtypeReadBackMessage (addViewOf env) ((addViewOf env).adapter.op_b[0])
           (addViewOf env).adapter.op_b_memory 3),
       memoryChannel.pulledIfValue (addViewOf env).is_real
         (rtypePriorMessage (addViewOf env) ((addViewOf env).adapter.op_c[0])
           (addViewOf env).adapter.op_c_memory),
       memoryChannel.pushedIfValue (addViewOf env).is_real
         (rtypeReadBackMessage (addViewOf env) ((addViewOf env).adapter.op_c[0])
           (addViewOf env).adapter.op_c_memory 2),
       memoryChannel.pushedIfValue (addViewOf env).is_real
         (rtypeWriteMessage (addViewOf env))] := by
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((AddChip.main (varFromOffset AddChip.Inputs 0)).operations
        (size AddChip.Inputs)).interactionsWith (memoryChannel (p := p)).toRaw) = _
  rw [AddChip.interactionsWith_memory_eq]
  have inputEq : Eval.eval env (varFromOffset AddChip.Inputs 0) =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddChip.circuit (p := p)).output (varFromOffset AddChip.Inputs 0)
        (size AddChip.Inputs)) =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, circuit_norm]
  simp only [AddChip.exposedMemoryInteractions, List.map_cons, List.map_nil,
    Channel.eval_pulledIf, Channel.eval_pushedIf, eval_registerMemoryMessage]
  simp only [addViewOf, ← inputEq, ← outputEq, rtypePriorMessage, rtypeReadBackMessage,
    rtypeWriteMessage, AddChip.rowView, Extracted.RTypeReader.toAdapterView]
  simp [AddChip.circuit, circuit_norm]

/-- Lift the raw evaluation to the proof-carrying typed decoder for any retained Add row. -/
theorem addChip_typedMemoryInteractions_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p)) :
    decoded.interactionsWith data (memoryChannel (p := p)) =
      [TypedInteraction.pulledIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypePriorMessage (decoded.toChipRow data).view
           (decoded.toChipRow data).view.adapter.op_a
           (decoded.toChipRow data).view.adapter.op_a_memory),
       TypedInteraction.pulledIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypePriorMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_b[0])
           (decoded.toChipRow data).view.adapter.op_b_memory),
       TypedInteraction.pushedIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypeReadBackMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_b[0])
           (decoded.toChipRow data).view.adapter.op_b_memory 3),
       TypedInteraction.pulledIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypePriorMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_c[0])
           (decoded.toChipRow data).view.adapter.op_c_memory),
       TypedInteraction.pushedIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypeReadBackMessage (decoded.toChipRow data).view
           ((decoded.toChipRow data).view.adapter.op_c[0])
           (decoded.toChipRow data).view.adapter.op_c_memory 2),
       TypedInteraction.pushedIfValue memoryChannel (decoded.toChipRow data).view.is_real
         (rtypeWriteMessage (decoded.toChipRow data).view)] := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addChipDescriptor (p := p) := hchip
  subst hchip'
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw, DecodedInstructionRow.environment,
    DecodedInstructionRow.toChipRow, addViewOf_decodeRow, addChipDescriptor_table] using
    addChip_memoryInteractionValues_eq (Environment.fromArray physical data)

/-! ### Consumed/produced lists at an active selector -/

omit [Fact (2 ^ 25 < p)] in
private theorem memPull_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 msg).mult = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (-(1 : ZMod p)) := rfl
    _ = -((1 : ZMod p).val : ℤ) := signedVal_neg_is_real hp (Or.inr rfl)
    _ = -1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
private theorem memPush_one_signed (msg : MemoryMsg (ZMod p)) :
    signedVal (TypedInteraction.pushedIfValue (memoryChannel (p := p)) 1 msg).mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  calc
    _ = signedVal (1 : ZMod p) := rfl
    _ = ((1 : ZMod p).val : ℤ) := signedVal_is_real hp (Or.inr rfl)
    _ = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num

omit [Fact (2 ^ 25 < p)] in
/-- An active R-type six-pack consumes exactly its three read-prior messages. -/
private theorem consumedMessages_rtypeSix (m1 m2 b1 m3 b2 w : MemoryMsg (ZMod p)) :
    consumedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [m1, m2, m3] := by
  have filtered : List.filter (fun i => signedVal i.mult = -1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] =
      [TypedInteraction.pulledIfValue memoryChannel 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pulledIfValue memoryChannel 1 m3] := by
    simp only [List.filter_cons, List.filter_nil, memPull_one_signed, memPush_one_signed]
    norm_num
  rw [consumedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]

omit [Fact (2 ^ 25 < p)] in
/-- An active R-type six-pack produces exactly its two read-backs and its write. -/
private theorem producedMessages_rtypeSix (m1 m2 b1 m3 b2 w : MemoryMsg (ZMod p)) :
    producedMessages
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] = [b1, b2, w] := by
  have filtered : List.filter (fun i => signedVal i.mult = 1)
      [TypedInteraction.pulledIfValue (memoryChannel (p := p)) 1 m1,
       TypedInteraction.pulledIfValue memoryChannel 1 m2,
       TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pulledIfValue memoryChannel 1 m3,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] =
      [TypedInteraction.pushedIfValue memoryChannel 1 b1,
       TypedInteraction.pushedIfValue memoryChannel 1 b2,
       TypedInteraction.pushedIfValue memoryChannel 1 w] := by
    simp only [List.filter_cons, List.filter_nil, memPull_one_signed, memPush_one_signed]
    norm_num
  rw [producedMessages, filtered]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]

/-- An active decoded Add row's consumed Memory messages, in view form. -/
theorem addChip_consumedMemoryMessages_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_a
         (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory] := by
  unfold DecodedInstructionRow.consumedMemoryMessages
  rw [addChip_typedMemoryInteractions_eq decoded data hchip, real]
  exact consumedMessages_rtypeSix _ _ _ _ _ _

/-- An active decoded Add row's produced Memory messages, in view form. -/
theorem addChip_producedMemoryMessages_eq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory 2,
       rtypeWriteMessage (decoded.toChipRow data).view] := by
  unfold DecodedInstructionRow.producedMemoryMessages
  rw [addChip_typedMemoryInteractions_eq decoded data hchip, real]
  exact producedMessages_rtypeSix _ _ _ _ _ _

/-! ### The remaining wiring inputs from the audited surfaces -/

/-- The clock byte bounds of an Add row's view, from the finished Byte channel and the retained
CPU-reader contract. -/
theorem addChip_viewClockBounds (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (hchip : decoded.chip = addChipDescriptor (p := p))
    (guarantees : decoded.chip.table.operations.ChannelGuarantees byteChannel.toRaw
      (decoded.environment data))
    (real : (decoded.toChipRow data).view.is_real = 1) :
    ViewClockBounds (decoded.toChipRow data).view := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = addChipDescriptor (p := p) := hchip
  subst hchip'
  exact viewClockBounds_of_cpuStateContract (AddChip.circuit (p := p)) AddChip.rowView
    AddChip.cpuStateTimeContract data physical guarantees real

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
/-- The reader's decode bound `op_a < 32`, read off the chip `Spec`'s composed R-type contract. -/
theorem addChip_opa_lt (inp : AddChip.Inputs (ZMod p)) (cols : AddChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) (real : inp.is_real = 1)
    (spec : AddChip.Spec inp cols data) :
    (AddChip.rowView inp cols).adapter.op_a.val < 32 := by
  obtain ⟨-, hrspec, -, -⟩ := spec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  exact (hbounds real).1

/-- The row's own push `Requirements`, from the same open-inputs seam that yields `chipSpec`: the
finished Byte/Program channels, the vacuous State channel, and the grounded Memory guarantees make
`Component.weakSoundness` fire, and its second half is exactly the interaction requirements. -/
theorem fullRequirements_of_openSoundnessInputs
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (openInputs : DecodedRowOpenSoundnessInputs decoded witness.data) :
    decoded.chip.table.operations.FullRequirements (decoded.environment witness.data) := by
  have finished := witness_decodedRow_finishedChannelGuarantees witness constraints balanced
    decoded decodedMem
  have guarantees := (DecodedRowChannelGuarantees.mk
    (decodedRow_stateChannelGuarantees decoded witness.data)
    finished.1 finished.2 openInputs.memory).full
    (decoded.usesSupportedBusChannels_of_mem witness.tables decodedMem)
  exact (Component.weakSoundness openInputs.assumptions
    (decodedInstructionRow_constraints witness constraints decoded decodedMem) guarantees).2

/-- Every produced Memory message of a row with proved push requirements is a well-formed `U64` —
in particular the `op_a` write value's range check reaches the wiring. -/
theorem producedMemoryMessages_isU64_of_fullRequirements (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (requirements : decoded.chip.table.operations.FullRequirements
      (decoded.environment data)) :
    ∀ m ∈ decoded.producedMemoryMessages data, MemoryMsg.isU64 m := by
  intro m hm
  unfold DecodedInstructionRow.producedMemoryMessages producedMessages at hm
  obtain ⟨interaction, hfilter, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hmem, hpos⟩ := List.mem_filter.mp hfilter
  simp only [decide_eq_true_eq] at hpos
  have rawReq : interaction.raw.Requirements (decoded.environment data).data := by
    unfold DecodedInstructionRow.interactionsWith typedInteractionValuesWith at hmem
    obtain ⟨⟨abstract, amem⟩, -, rfl⟩ := List.mem_map.mp hmem
    exact requirements abstract (List.mem_of_mem_filter amem)
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact interaction.guarantee_of_requirements (decoded.environment data).data hp rawReq hpos

/-! ### The wiring corollary and the end-to-end demo -/

/-- Assemble a decoded row's `RowWiring` from the R-type shape lemma and its exact Memory lists. -/
theorem rowWiring_rtype_of_decoded (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (bounds : ViewClockBounds (decoded.toChipRow data).view)
    (commit_eq : (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite)
    (opa_lt : (decoded.toChipRow data).view.adapter.op_a.val < 32)
    (write_isU64 : Word.isU64 (decoded.toChipRow data).view.rdWrite)
    (consumed_eq : decoded.consumedMemoryMessages data =
      [rtypePriorMessage (decoded.toChipRow data).view
         (decoded.toChipRow data).view.adapter.op_a
         (decoded.toChipRow data).view.adapter.op_a_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory,
       rtypePriorMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory])
    (produced_eq : decoded.producedMemoryMessages data =
      [rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_b[0])
         (decoded.toChipRow data).view.adapter.op_b_memory 3,
       rtypeReadBackMessage (decoded.toChipRow data).view
         ((decoded.toChipRow data).view.adapter.op_c[0])
         (decoded.toChipRow data).view.adapter.op_c_memory 2,
       rtypeWriteMessage (decoded.toChipRow data).view]) :
    RowWiring (decoded.toChipRow data).view (decoded.ordinaryRowFacts data) := by
  refine rowWiring_rtype bounds commit_eq opa_lt write_isU64 rfl rfl ?_ ?_
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed_eq]
    rfl
  · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
    exact produced_eq

set_option maxHeartbeats 1000000 in
/-- **The Add validation instance** (SP-2's `addRow_engineFacts`): a genuine decoded Add row of a
constrained, balanced witness produces both timed-engine records through the generic adapter — no
Add-specific Sail reasoning beyond the registered `advance` payload.  `decode` and `ready` are the
static-layer/readiness residuals supplied by the surrounding grounding argument. -/
theorem addRow_engineFacts
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = addChipDescriptor (p := p))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (openInputs : DecodedRowOpenSoundnessInputs decoded witness.data)
    (program : GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow witness.data).view).toRow)
    (ready : ∀ s : SailState, (decoded.toChipRow witness.data).kind.advanceReady
      (decoded.toChipRow witness.data).inputs (decoded.toChipRow witness.data).cols program s)
    (initial : SailState) (initialClock : ℕ) :
    LocalStepFact program initial initialClock (decoded.ordinaryRowFacts witness.data) ∧
      FrameFact program initial initialClock (decoded.ordinaryRowFacts witness.data) := by
  have realView : (decoded.toChipRow witness.data).view.is_real = 1 := real
  have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
    decodedMem
  have bounds := addChip_viewClockBounds decoded witness.data hchip byteG realView
  have spec : (decoded.toChipRow witness.data).chipSpec witness.data :=
    decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem openInputs
  have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
    decoded decodedMem openInputs
  have consumed_eq := addChip_consumedMemoryMessages_eq decoded witness.data hchip realView
  have produced_eq := addChip_producedMemoryMessages_eq decoded witness.data hchip realView
  have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite := by
    have hmem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
        decoded.producedMemoryMessages witness.data := by
      rw [produced_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    exact producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements
      _ hmem
  have commit_eq : (decoded.toChipRow witness.data).view.commit =
      Trace.CommitEffect.regWrite := by
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  have opa_lt : (decoded.toChipRow witness.data).view.adapter.op_a.val < 32 := by
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    -- Hypothesis-directed, metavariable-free: extract the circuit `Spec` through the decoder's
    -- registered iff and destructure in place.  Applying the abstract `addChip_opa_lt` here would
    -- hand the unifier metavariables whose resolution forces a full eval-struct normalization.
    obtain ⟨-, hrspec, -, -⟩ :=
      (SupportedChip.decodeRow_chipSpec_iff (addChipDescriptor (p := p))
        witness.data physical).mp spec
    obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
    exact (hbounds realView).1
  have wiring := rowWiring_rtype_of_decoded decoded witness.data bounds commit_eq opa_lt
    writeU64 consumed_eq produced_eq
  have migrated : (decoded.toChipRow witness.data).kind.advance.isSome = true := by
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  exact engineFacts_of_kind migrated wiring real spec decode ready initial initialClock

end AddAnchor

end SP1Clean.Soundness
