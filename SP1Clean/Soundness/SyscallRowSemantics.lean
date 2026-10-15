import SP1Clean.Faithful.SyscallInstrsChip
import SP1Clean.Faithful.SyscallRowDecode
import SP1Clean.Model.Machine.Shard

/-! # What a syscall row means

The bridge from one `SyscallInstrsChip` row to one `Machine.CoreSyscallEvent`, and from the row's
constraints to that event's semantic laws. This is the layer at which "the chip is faithful to SP1's
AIR" becomes "the shard executed a syscall".

**The decoder is reused, not rewritten.** `decodeSyscallRow` (`Faithful/SyscallRowDecode.lean`)
already maps an *extracted* row to a `CoreSyscallEvent`, and `syscallInstrsReconfigure` maps a
native row to an extracted one index-for-index with both round-trips proved. Composing them is what
makes this bridge land on the same events `CoreAIRRefinementObligations` quantifies over; a fresh
decoder would silently fail to connect to the commit obligations.

**What the row gives, and what it does not.** Three of the four `RowLaw` conjuncts are the arm
`Spec`s almost verbatim — `WriteArm ↔ ResultLaw`, `PcArm ↔ PcLaw`, `DispatchArm ↔
HandlerAddressesFit`. What the row does **not** give, and must be supplied by the ensemble:

* the register indices `5`/`10`/`11` — SP1 does not pin them in the AIR either; the preprocessed
  Program table does, because the decoder always emits `Instruction::new(ECALL, X5, X10, X11)`;
* canonicity of the syscall code — see `IsInlineCanonical` below.

The Program bus's low-limb bound suffices to prove `nextPc = pc + 4`, even when the raw next
low limb exceeds `65535`. StateBump normalizes that representation separately. The released
`SyscallRowContext.pcCarry` premise remains for source compatibility; the component-local
`rowLaw_of_spec_and_pulledFacts` theorem needs no such premise.

**The canonical-code profile premise.** SP1's AIR selects from bytes 0 and 1 of `x5`. The executor
dispatches on `x5 as u32` through `SyscallCode::from_u32`, rejecting unrecognized low-32-bit codes.
The native bridge requires the stronger full-word predicate `IsInlineCanonical`; it is not derived
from the row or from successful Rust dispatch. In particular, the cast ignores the upper 32 bits:
`0x100000003` dispatches as `ENTER_UNCONSTRAINED` but is outside this profile. All thirteen inline
codes are below 256, so canonicality requires membership in that list and zero higher bytes. This
restriction preserves the current `IsCanonicalCode`/`SP1Halted` meaning without adding assertions
absent from the Rust row. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.CoreAIR.Current (decodeSyscallRow)
open SP1Clean.Faithful (syscallInstrsReconfigure)
open SP1Clean.Soundness.Target (GuestProgram)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The row's event -/

/-- The event a native syscall row denotes, through the extracted decoder. -/
noncomputable def syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p)) : CoreSyscallEvent :=
  decodeSyscallRow (syscallInstrsReconfigure r)

/-- Lifting one byte split from the field to `ℕ`. The two bytes are each below `256`, so their
recombination is below `2 ^ 16` and cannot wrap the modulus — which is what `Fact (2 ^ 17 < p)` is
for. -/
private theorem byteSplit_val {a low high : ZMod p}
    (hlow : low.val < 256) (hhigh : high.val < 256) (h : a = low + high * 256) :
    a.val = low.val + high.val * 256 := by
  have hp : 2 ^ 17 < p := Fact.out
  have h256 : (256 : ZMod p).val = 256 := by
    have h : ((256 : ℕ) : ZMod p).val = 256 :=
      ZMod.val_natCast_of_lt (by omega)
    exact_mod_cast h
  have hmul : (high * 256 : ZMod p).val = high.val * 256 := by
    rw [ZMod.val_mul, h256]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h, ZMod.val_add, hmul]
  exact Nat.mod_eq_of_lt (by omega)

/-- The event's syscall id is the chip's byte-0 selector input. This is the hinge of the whole
bridge: every arm `Spec` speaks of the selectors, every semantic law speaks of `syscallId`, and
`SelectorsValid`'s `U16toU8` decomposition is what ties them together. -/
theorem syscallId_syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) :
    (syscallEventOfRow r).syscallId = (SyscallInstrsChip.syscallId r).val := by
  obtain ⟨hlow, hhigh, heq⟩ := sel.1 real 0
  -- the decomposition spec speaks at the operation's record projection; the row's own spelling is
  -- defeq to it, and `rw` needs the row's.
  have hlift : (r.op_a_memory.prev_value[0]).val
      = (SyscallInstrsChip.syscallId r).val
        + ((r.op_a_memory.prev_value[0] - r.syscall_id_bytes.low_bytes[0]) * 256⁻¹).val * 256 :=
    byteSplit_val hlow hhigh heq
  have hlow' : (SyscallInstrsChip.syscallId r).val < 256 := hlow
  show (SP1Clean.CoreAIR.Current.word64 (syscallInstrsReconfigure r).values 7 8 9 10).toNat % 256
    = _
  rw [SP1Clean.CoreAIR.Current.word64, BitVec.toNat_ofNat]
  -- `256 ∣ 2 ^ 64`, so the outer truncation does not disturb the low byte; the three high limbs are
  -- multiples of `2 ^ 16` and drop out.
  rw [Nat.mod_mod_of_dvd _ (by norm_num : (256 : ℕ) ∣ 2 ^ 64)]
  show (((syscallInstrsReconfigure r).values[(7 : Fin 65)]).val
    + ((syscallInstrsReconfigure r).values[(8 : Fin 65)]).val * 2 ^ 16
    + ((syscallInstrsReconfigure r).values[(9 : Fin 65)]).val * 2 ^ 32
    + ((syscallInstrsReconfigure r).values[(10 : Fin 65)]).val * 2 ^ 48) % 256 = _
  have hidx : (syscallInstrsReconfigure r).values[(7 : Fin 65)]
      = r.op_a_memory.prev_value[0] := rfl
  rw [hidx, hlift]
  omega

/-- The event's table byte is the chip's `tableByteVar` — the very multiplicity of the syscall-bus
send, which is why an unprovisioned bus forces it to zero. -/
theorem tableByte_syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) :
    (syscallEventOfRow r).tableByte = (SyscallInstrsChip.tableByte r).val := by
  obtain ⟨hlow, hhigh, heq⟩ := sel.1 real 0
  have hlift : (r.op_a_memory.prev_value[0]).val
      = (SyscallInstrsChip.syscallId r).val + (SyscallInstrsChip.tableByte r).val * 256 :=
    byteSplit_val hlow hhigh heq
  have hlow' : (SyscallInstrsChip.syscallId r).val < 256 := hlow
  have hhigh' : (SyscallInstrsChip.tableByte r).val < 256 := hhigh
  show (SP1Clean.CoreAIR.Current.word64 (syscallInstrsReconfigure r).values 7 8 9 10).toNat
    / 256 % 256 = _
  rw [SP1Clean.CoreAIR.Current.word64, BitVec.toNat_ofNat]
  show ((((syscallInstrsReconfigure r).values[(7 : Fin 65)]).val
    + ((syscallInstrsReconfigure r).values[(8 : Fin 65)]).val * 2 ^ 16
    + ((syscallInstrsReconfigure r).values[(9 : Fin 65)]).val * 2 ^ 32
    + ((syscallInstrsReconfigure r).values[(10 : Fin 65)]).val * 2 ^ 48) % 2 ^ 64)
    / 256 % 256 = _
  have hidx : (syscallInstrsReconfigure r).values[(7 : Fin 65)]
      = r.op_a_memory.prev_value[0] := rfl
  rw [hidx, hlift]
  omega

/-! ## The row's bus messages

The State edge and the committed fetch, at the ZMod level the ledger reads. These mirror
`HaltChip`'s, with two differences that are the whole point of the generalization: the pushed pc is
the row's own `next_pc` witness rather than the constant `haltPc`, and the fetch's operands are the
row's own cells rather than the literals `5`/`10`/`11`. -/

/-- The State message a syscall row pulls — the pre-syscall `(clk, pc)`. -/
def SyscallInstrsChip.statePulledMessage (r : SyscallInstrsChip.Inputs (ZMod p)) :
    Channels.StateMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536,
    r.state.pc[0], r.state.pc[1], r.state.pc[2]⟩

/-- The State message a syscall row pushes — `(clk + 264, next_pc)`. -/
def SyscallInstrsChip.statePushedMessage (r : SyscallInstrsChip.Inputs (ZMod p)) :
    Channels.StateMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536 + 264,
    r.next_pc[0], r.next_pc[1], r.next_pc[2]⟩

/-- The Program message a syscall row pulls — the committed `ECALL op_a, op_b, op_c` at its pc. -/
def SyscallInstrsChip.programMessage (r : SyscallInstrsChip.Inputs (ZMod p)) :
    Channels.ProgramMsg (ZMod p) :=
  ⟨r.state.pc[0], r.state.pc[1], r.state.pc[2], 50,
   r.op_a, #v[r.op_b, 0, 0, 0], #v[r.op_c, 0, 0, 0], r.op_a_0, 0, 0⟩

/-- **The selector bridge.** The event's id matches a code exactly when the chip's field-level id
does. Every arm theorem goes through this: the arm `Spec`s are phrased over the `IsZero` selectors,
`SelectorsValid` phrases those over the *field* id, and the semantic laws phrase everything over the
event's *natural* id. Both directions are needed — the default arm's hypotheses are negations. -/
theorem syscallId_field_iff (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) {code : ℕ}
    (hcode : code < 256) :
    (syscallEventOfRow r).syscallId = code ↔ SyscallInstrsChip.syscallId r = (code : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hlt : (SyscallInstrsChip.syscallId r).val < 256 := (sel.1 real 0).1
  rw [syscallId_syscallEventOfRow r sel real]
  constructor
  · intro h
    have := congrArg (fun n : ℕ => (n : ZMod p)) h
    simpa [ZMod.natCast_val, ZMod.cast_id] using this
  · intro h
    rw [h, ZMod.val_natCast_of_lt (by omega : code < p)]

/-! ## The handler

Thirteen arms, dispatching on the id when the table byte is zero. The division of labour matters:
the handler supplies the **effect**, while `RowLaw` — which the row proves — says what the effect
must be. So the handler writes `event.result` to `t0` without itself deciding what `result` is;
`ResultLaw` is what pins it to `0` on ENTER_UNCONSTRAINED, to the oracle on HINT_LEN, and to the
unchanged code everywhere else. -/

/-- **The thirteen-arm handler.** HALT parks at `haltPc`; every other inline code advances one
instruction and writes `t0`. A non-zero table byte routes to a precompile and is not ours. -/
noncomputable def ExecutableSyscallHandler.full : ExecutableSyscallHandler where
  run := fun _program event source =>
    if event.tableByte ≠ 0 then none
    else if event.syscallId = Machine.haltSyscallId then
      some { source with regs := source.regs.insert Register.PC Machine.haltPc }
    else if event.syscallId ∈ inlineSyscallIds then
      some { source with
        regs := (source.regs.insert Register.PC (event.pc + 4)).insert Register.x5 event.result }
    else none

/-- `full` extends `haltOnly`: on a canonical HALT the two produce the same state, so every proof
that consumes the halt path keeps working when the binding is switched. -/
theorem full_run_eq_haltOnly_of_canonicalHalt (program : GuestProgram) (event : CoreSyscallEvent)
    (source : SailState) (h : event.IsCanonicalHalt) :
    ExecutableSyscallHandler.full.run program event source =
      ExecutableSyscallHandler.haltOnly.run program event source := by
  have hraw : event.rawCode = 0 := by
    simpa [CoreSyscallEvent.IsCanonicalHalt, CoreSyscallEvent.IsCanonicalCode] using h
  have hnat : event.rawCode.toNat = 0 := by rw [hraw]; rfl
  have htable : event.tableByte = 0 := by
    rw [CoreSyscallEvent.tableByte, hnat]
  have hid : event.syscallId = haltSyscallId := by
    rw [CoreSyscallEvent.syscallId, hnat]; rfl
  simp only [ExecutableSyscallHandler.full, ExecutableSyscallHandler.haltOnly, htable, hid,
    ne_eq, not_true_eq_false, if_false, if_true, if_pos hraw]

/-- **The goodness obligation a mid-shard syscall row owes.** The halt row is excused from bounding
its pushed pc because that pc is the literal `(1, 0, 0)`. A syscall row's push is a real `pc + 4`, so
both endpoints need limb bounds or `canonState` fails to preserve `pcBits`. -/
theorem syscallEdge_pcBounds (r : SyscallInstrsChip.Inputs (ZMod p))
    (spec : SyscallInstrsChip.Spec r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1) (carry : (r.state.pc[0]).val + 4 < 2 ^ 16) :
    (∀ i : Fin 3, (r.state.pc[i]).val < 2 ^ 16) ∧
      (∀ i : Fin 3, (r.next_pc[i]).val < 2 ^ 16) := by
  have hp : 2 ^ 17 < p := Fact.out
  have : Fact (1 < p) := ⟨by omega⟩
  have hpull := pulled real
  have hpc0 : (r.state.pc[0]).val < 2 ^ 16 := hpull.2.1
  have hpc1 : (r.state.pc[1]).val < 2 ^ 16 := hpull.2.2.1
  have hpc2 : (r.state.pc[2]).val < 2 ^ 16 := hpull.2.2.2.1
  have hnext : (r.next_pc[0]).val < 2 ^ 16 ∧ (r.next_pc[1]).val < 2 ^ 16 ∧
      (r.next_pc[2]).val < 2 ^ 16 := by
    rcases spec.1.2.2.2.1 with hh | hh
    · -- the ordinary arm: `pc + 4`, bounded by the bump chip's carry fact
      have hpc : r.next_pc[0] = r.state.pc[0] + 4 ∧ r.next_pc[1] = r.state.pc[1] ∧
          r.next_pc[2] = r.state.pc[2] := spec.2.2.2.2.2.2.1.2 real hh
      have h4 : ((4 : ZMod p)).val = 4 := by
        rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num,
          ZMod.val_natCast_of_lt (by omega : (4 : ℕ) < p)]
      have hval : ((r.state.pc[0] + 4 : ZMod p)).val = (r.state.pc[0]).val + 4 := by
        rw [ZMod.val_add_of_lt (by rw [h4]; omega), h4]
      refine ⟨?_, ?_, ?_⟩
      · rw [hpc.1, hval]; omega
      · rw [hpc.2.1]; exact hpc1
      · rw [hpc.2.2]; exact hpc2
    · -- the halt arm: the literal `(1, 0, 0)`
      have hpc : r.next_pc[0] = 1 ∧ r.next_pc[1] = 0 ∧ r.next_pc[2] = 0 :=
        spec.2.2.2.2.2.2.1.1 hh
      refine ⟨?_, ?_, ?_⟩
      · rw [hpc.1, ZMod.val_one]; norm_num
      · rw [hpc.2.1, ZMod.val_zero]; norm_num
      · rw [hpc.2.2, ZMod.val_zero]; norm_num
  refine ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact hpc0
    · exact hpc1
    · exact hpc2
  · fin_cases i
    · exact hnext.1
    · exact hnext.2.1
    · exact hnext.2.2

/-! ## The per-arm case theorems

One per inline arm, so that a missing arm is a missing theorem rather than a silent gap. Each says:
*this row's constraints, plus the named ensemble facts, give this arm's semantic transition.* The
exhaustiveness lemma at the end is what turns thirteen separate results into a total dispatch. -/

/-- The ensemble-supplied facts a syscall row needs beyond its own `Spec`. Naming them in one place
keeps the per-arm theorems honest about what is *not* row-local. -/
structure SyscallRowContext (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram)
    (source : SailState) : Prop where
  /-- The register operands are `x5`/`x10`/`x11`, from the Program bus's committed ECALL row. -/
  operands : r.op_a = 5 ∧ r.op_b = 10 ∧ r.op_c = 11
  /-- Legacy no-carry restriction, retained for source compatibility. The row-law proof only
  needs the Program bus's input bound, as `arm_pcAdvance_of_pcBound` shows. -/
  pcCarry : (r.state.pc[0]).val + 4 < 2 ^ 16
  /-- The row sits at an `ECALL` word of the committed program. -/
  ecall : Machine.AboutToExecuteEcall program source
  /-- The three pulled registers hold the row's prior words at this state. -/
  operandValues :
    source.get_reg? 5#5 = some (syscallEventOfRow r).rawCode ∧
    source.get_reg? 10#5 = some (syscallEventOfRow r).arg1 ∧
    source.get_reg? 11#5 = some (syscallEventOfRow r).arg2
  /-- The pc observation at the row's State pull. -/
  pcValue : source.regs.get? Register.PC = some (syscallEventOfRow r).pc

section Arms

variable (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram) (source : SailState)

/-! ### The event's fields, at the row's spelling

Each holds by `rfl` — `syscallInstrsReconfigure` is a field permutation, so the decoder's numeric
indices *are* the row's columns. Stating them once is what keeps every arm proof from re-deriving
the layout. -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem pc_syscallEventOfRow : (syscallEventOfRow r).pc = BitVec.ofNat 64
    ((r.state.pc[0]).val + (r.state.pc[1]).val * 2 ^ 16 + (r.state.pc[2]).val * 2 ^ 32) := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem nextPc_syscallEventOfRow : (syscallEventOfRow r).nextPc = BitVec.ofNat 64
    ((r.next_pc[0]).val + (r.next_pc[1]).val * 2 ^ 16 + (r.next_pc[2]).val * 2 ^ 32) := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem rawCode_syscallEventOfRow : (syscallEventOfRow r).rawCode = BitVec.ofNat 64
    ((r.op_a_memory.prev_value[0]).val + (r.op_a_memory.prev_value[1]).val * 2 ^ 16 +
      (r.op_a_memory.prev_value[2]).val * 2 ^ 32 +
      (r.op_a_memory.prev_value[3]).val * 2 ^ 48) := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem result_syscallEventOfRow : (syscallEventOfRow r).result = BitVec.ofNat 64
    ((r.op_a_value[0]).val + (r.op_a_value[1]).val * 2 ^ 16 +
      (r.op_a_value[2]).val * 2 ^ 32 + (r.op_a_value[3]).val * 2 ^ 48) := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem arg1_syscallEventOfRow : (syscallEventOfRow r).arg1 = BitVec.ofNat 64
    ((r.op_b_memory.prev_value[0]).val + (r.op_b_memory.prev_value[1]).val * 2 ^ 16 +
      (r.op_b_memory.prev_value[2]).val * 2 ^ 32 +
      (r.op_b_memory.prev_value[3]).val * 2 ^ 48) := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem arg2_syscallEventOfRow : (syscallEventOfRow r).arg2 = BitVec.ofNat 64
    ((r.op_c_memory.prev_value[0]).val + (r.op_c_memory.prev_value[1]).val * 2 ^ 16 +
      (r.op_c_memory.prev_value[2]).val * 2 ^ 32 +
      (r.op_c_memory.prev_value[3]).val * 2 ^ 48) := rfl

/-! ### The arms -/

/-- **HALT.** The row parks the machine at `haltPc`. `PcArm`'s halt branch pins the three pc limbs
to `(1, 0, 0)`, which recombines to `BitVec.ofNat 64 1` — SP1's `HALT_PC` exactly. -/
theorem arm_halt (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId = Machine.haltSyscallId) :
    (syscallEventOfRow r).nextPc = Machine.haltPc := by
  have hp : 2 ^ 17 < p := Fact.out
  have : Fact (1 < p) := ⟨by omega⟩
  have hfield : SyscallInstrsChip.syscallId r = ((SyscallInstrsChip.haltCode : ℕ) : ZMod p) :=
    (syscallId_field_iff r sel real (by decide : Machine.haltSyscallId < 256)).1 hid
  have hzero : r.is_halt_zero.result = 1 := by
    rw [(sel.2.1 real).1, if_pos hfield]
  have hhalt : r.is_halt = 1 := by rw [sel.2.2.2.1, hzero, real, one_mul]
  have hpc : r.next_pc[0] = 1 ∧ r.next_pc[1] = 0 ∧ r.next_pc[2] = 0 :=
    spec.2.2.2.2.2.2.1.1 hhalt
  rw [nextPc_syscallEventOfRow, hpc.1, hpc.2.1, hpc.2.2, ZMod.val_one, ZMod.val_zero]
  rfl

/-- Program bounds suffice for the syscall PC increment. The low limb may carry into the
next 16-bit limb; only wrap in the ambient field must be excluded. -/
theorem arm_pcAdvance_of_pcBound (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId ≠ Machine.haltSyscallId)
    (pcBound : (r.state.pc[0]).val < 2 ^ 16) :
    (syscallEventOfRow r).nextPc = (syscallEventOfRow r).pc + 4 := by
  have hp : 2 ^ 17 < p := Fact.out
  have hfield : SyscallInstrsChip.syscallId r ≠ ((SyscallInstrsChip.haltCode : ℕ) : ZMod p) :=
    fun h => hid ((syscallId_field_iff r sel real (by decide : Machine.haltSyscallId < 256)).2 h)
  have hzero : r.is_halt_zero.result = 0 := by
    rw [(sel.2.1 real).1, if_neg hfield]
  have hhalt : r.is_halt = 0 := by rw [sel.2.2.2.1, hzero, zero_mul]
  have hpc : r.next_pc[0] = r.state.pc[0] + 4 ∧ r.next_pc[1] = r.state.pc[1] ∧
      r.next_pc[2] = r.state.pc[2] := spec.2.2.2.2.2.2.1.2 real hhalt
  have hval : ((r.state.pc[0] + 4 : ZMod p)).val = (r.state.pc[0]).val + 4 := by
    have h4 : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    have : ((4 : ZMod p)).val = 4 := by rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num, h4]
    rw [ZMod.val_add_of_lt (by rw [this]; omega), this]
  have harith : (r.state.pc[0]).val + 4 + (r.state.pc[1]).val * 2 ^ 16
        + (r.state.pc[2]).val * 2 ^ 32
      = ((r.state.pc[0]).val + (r.state.pc[1]).val * 2 ^ 16
        + (r.state.pc[2]).val * 2 ^ 32) + 4 := by ring
  rw [nextPc_syscallEventOfRow, pc_syscallEventOfRow, hpc.1, hpc.2.1, hpc.2.2, hval, harith]
  simp [BitVec.ofNat_add]

/-- The released no-carry interface specializes the weaker Program-bound theorem. -/
theorem arm_pcAdvance (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId ≠ Machine.haltSyscallId)
    (carry : (r.state.pc[0]).val + 4 < 2 ^ 16) :
    (syscallEventOfRow r).nextPc = (syscallEventOfRow r).pc + 4 :=
  arm_pcAdvance_of_pcBound r spec sel real hid (by omega)

/-- **ENTER_UNCONSTRAINED.** `t0 := 0`. The tracing VM returns `0` here (the minimal executor's `1`
is never traced), which is what the AIR's zero-word arm records. The `op_a_0` booleanity the write
arm is reported under comes from the Program fetch, hence from `PulledFacts`. -/
theorem arm_enterUnconstrained (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId = Machine.enterUnconstrainedSyscallId) :
    (syscallEventOfRow r).result = 0 := by
  have hfield :
      SyscallInstrsChip.syscallId r = ((SyscallInstrsChip.enterUnconstrainedCode : ℕ) : ZMod p) :=
    (syscallId_field_iff r sel real
      (by decide : Machine.enterUnconstrainedSyscallId < 256)).1 hid
  have henter : r.is_enter_unconstrained.result = 1 := by
    rw [(sel.2.1 real).2.1, if_pos hfield]
  have hw : ∀ i : Fin 4, r.op_a_value[i] = 0 :=
    (spec.2.2.2.2.2.1 (pulled real).2.2.2.2.1).2.2.1 real henter
  have h0 : r.op_a_value[0] = 0 := hw 0
  have h1 : r.op_a_value[1] = 0 := hw 1
  have h2 : r.op_a_value[2] = 0 := hw 2
  have h3 : r.op_a_value[3] = 0 := hw 3
  rw [result_syscallEventOfRow, h0, h1, h2, h3, ZMod.val_zero]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- **HINT_LEN.** The one arm whose result is oracled: `ResultLaw` imposes nothing there, and all
the row does is range-check the word so the read-back is pushable. Saying exactly that — and no
more — is what keeps the hint's value grounded by the host semantics rather than guessed here. -/
theorem arm_hintLen (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1) :
    Word.isU64 r.op_a_value := (pulled real).2.2.2.2.2.2.2.2.2.2.2

/-- **The eight remaining inline codes**, plus HALT, COMMIT and COMMIT_DEFERRED: `t0` is unchanged.
Upstream this is `Ok(None)`, which writes `code as u64` — the same word, *given canonicity*. The
write arm states it limb for limb, which is a genuine 64-bit equality. -/
theorem arm_default (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId ≠ Machine.enterUnconstrainedSyscallId)
    (hid' : (syscallEventOfRow r).syscallId ≠ Machine.hintLenSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode := by
  have hfe : SyscallInstrsChip.syscallId r
      ≠ ((SyscallInstrsChip.enterUnconstrainedCode : ℕ) : ZMod p) :=
    fun h => hid ((syscallId_field_iff r sel real
      (by decide : Machine.enterUnconstrainedSyscallId < 256)).2 h)
  have hfh : SyscallInstrsChip.syscallId r ≠ ((SyscallInstrsChip.hintLenCode : ℕ) : ZMod p) :=
    fun h => hid' ((syscallId_field_iff r sel real
      (by decide : Machine.hintLenSyscallId < 256)).2 h)
  have henter : r.is_enter_unconstrained.result = 0 := by
    rw [(sel.2.1 real).2.1, if_neg hfe]
  have hhint : r.is_hint_len.result = 0 := by
    rw [(sel.2.1 real).2.2.1, if_neg hfh]
  have hsum : r.is_enter_unconstrained.result + r.is_hint_len.result = 0 := by
    rw [henter, hhint, add_zero]
  have hw : ∀ i : Fin 4, r.op_a_value[i] = r.op_a_memory.prev_value[i] :=
    (spec.2.2.2.2.2.1 (pulled real).2.2.2.2.1).2.2.2 real hsum
  have h0 : r.op_a_value[0] = r.op_a_memory.prev_value[0] := hw 0
  have h1 : r.op_a_value[1] = r.op_a_memory.prev_value[1] := hw 1
  have h2 : r.op_a_value[2] = r.op_a_memory.prev_value[2] := hw 2
  have h3 : r.op_a_value[3] = r.op_a_memory.prev_value[3] := hw 3
  rw [result_syscallEventOfRow, rawCode_syscallEventOfRow, h0, h1, h2, h3]

omit [Fact (2 ^ 17 < p)] in
/-- Three bounded limbs summing to zero in the field are each zero. The bound must be the concrete
KoalaBear one rather than the ambient `2 ^ 17 < p`: three `u16` limbs reach `3 · 2 ^ 16`, which
*exceeds* `2 ^ 17`, so the ambient hypothesis genuinely does not suffice. This is the third of the
three facts the plan named as not row-local. -/
private theorem three_limbs_zero {a b c : ZMod p} (koala : 2 ^ 18 < p)
    (ha : a.val < 2 ^ 16) (hb : b.val < 2 ^ 16) (hc : c.val < 2 ^ 16)
    (h : a + b + c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have : NeZero p := ⟨by omega⟩
  have hcast : a + b + c = ((a.val + b.val + c.val : ℕ) : ZMod p) := by
    push_cast [ZMod.natCast_zmod_val]
    ring
  rw [hcast] at h
  have hz : a.val + b.val + c.val = 0 := by
    have h' := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at h'
  exact ⟨(ZMod.val_eq_zero a).mp (by omega), (ZMod.val_eq_zero b).mp (by omega),
    (ZMod.val_eq_zero c).mp (by omega)⟩

/-- **COMMIT.** No guest state changes — `t0` is unchanged, as on every `Ok(None)` arm — and the row's
own content is that `a0` names a digest index below eight. The digest *binding* itself is not here:
it is a public-value hand-off, and `SailState` carries no public values, so COMMIT stays semantically
inert until a `PublicValues` provider exists. -/
theorem arm_commit (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1) (koala : 2 ^ 18 < p)
    (hid : (syscallEventOfRow r).syscallId = Machine.commitSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode ∧
      (syscallEventOfRow r).arg1.toNat < 8 := by
  refine ⟨arm_default r spec sel pulled real (by rw [hid]; decide) (by rw [hid]; decide), ?_⟩
  have hfield : SyscallInstrsChip.syscallId r = ((SyscallInstrsChip.commitCode : ℕ) : ZMod p) :=
    (syscallId_field_iff r sel real (by decide : Machine.commitSyscallId < 256)).1 hid
  have hne : SyscallInstrsChip.syscallId r
      ≠ ((SyscallInstrsChip.commitDeferredCode : ℕ) : ZMod p) := by
    intro h
    have hev := (syscallId_field_iff r sel real
      (by decide : Machine.commitDeferredSyscallId < 256)).2 h
    rw [hid] at hev
    exact absurd hev (by decide)
  have hsum : r.is_commit.result + r.is_commit_deferred.result = 1 := by
    rw [(sel.2.1 real).2.2.2.1, if_pos hfield, (sel.2.1 real).2.2.2.2, if_neg hne, add_zero]
  have cspec : SyscallInstrsChip.CommitArm.Spec (SyscallInstrsChip.toCommitArm r) :=
    spec.2.2.2.2.2.2.2.2.2.2.1
  -- One index bit is set, or the bitmap could not sum to one.
  have hbits : ∀ i : Fin 8, r.digest_index_bits[i] = 0 ∨ r.digest_index_bits[i] = 1 :=
    fun i => cspec.1 i real
  have hbitSum : SyscallInstrsChip.CommitArm.bitSum (SyscallInstrsChip.toCommitArm r) = 1 :=
    cspec.2.2.1 real hsum
  have hexists : ∃ i : Fin 8, r.digest_index_bits[i] = 1 := by
    by_contra hcon
    have hall : ∀ i : Fin 8, r.digest_index_bits[i] = 0 :=
      fun i => (hbits i).resolve_right (fun h => hcon ⟨i, h⟩)
    have e0 : r.digest_index_bits[0] = 0 := hall 0
    have e1 : r.digest_index_bits[1] = 0 := hall 1
    have e2 : r.digest_index_bits[2] = 0 := hall 2
    have e3 : r.digest_index_bits[3] = 0 := hall 3
    have e4 : r.digest_index_bits[4] = 0 := hall 4
    have e5 : r.digest_index_bits[5] = 0 := hall 5
    have e6 : r.digest_index_bits[6] = 0 := hall 6
    have e7 : r.digest_index_bits[7] = 0 := hall 7
    rw [SyscallInstrsChip.CommitArm.bitSum, SyscallInstrsChip.toCommitArm] at hbitSum
    simp only [e0, e1, e2, e3, e4, e5, e6, e7, add_zero] at hbitSum
    exact zero_ne_one hbitSum
  obtain ⟨i, hi⟩ := hexists
  have hlow : r.op_b_memory.prev_value[0] = ((i.val : ℕ) : ZMod p) := cspec.2.1 real i hi
  have hp : 2 ^ 17 < p := Fact.out
  have hlowVal : (r.op_b_memory.prev_value[0]).val < 8 := by
    rw [hlow, ZMod.val_natCast_of_lt (by omega : i.val < p)]
    exact i.isLt
  -- The other three limbs vanish, so `a0` is the index itself.
  have hb : Word.isU64 r.op_b_memory.prev_value := (pulled real).2.2.2.2.2.2.2.1
  have hb1 : (r.op_b_memory.prev_value[1]).val < 2 ^ 16 := hb 1
  have hb2 : (r.op_b_memory.prev_value[2]).val < 2 ^ 16 := hb 2
  have hb3 : (r.op_b_memory.prev_value[3]).val < 2 ^ 16 := hb 3
  have hrest : r.op_b_memory.prev_value[1] + r.op_b_memory.prev_value[2]
      + r.op_b_memory.prev_value[3] = 0 := cspec.2.2.2.2.1 real hsum
  obtain ⟨z1, z2, z3⟩ := three_limbs_zero koala hb1 hb2 hb3 hrest
  rw [arg1_syscallEventOfRow, z1, z2, z3, ZMod.val_zero]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **COMMIT_DEFERRED_PROOFS.** As COMMIT, with `a1` additionally a canonical field element — the
`32512` compare — because the deferred digest is stored as field elements rather than as bytes. -/
theorem arm_commitDeferred (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId = Machine.commitDeferredSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode ∧
      SyscallInstrsChip.ExitCodeValid r.op_c_memory.prev_value := by
  refine ⟨arm_default r spec sel pulled real (by rw [hid]; decide) (by rw [hid]; decide), ?_⟩
  have hfield : SyscallInstrsChip.syscallId r
      = ((SyscallInstrsChip.commitDeferredCode : ℕ) : ZMod p) :=
    (syscallId_field_iff r sel real (by decide : Machine.commitDeferredSyscallId < 256)).1 hid
  have hcd : r.is_commit_deferred.result = 1 := by
    rw [(sel.2.1 real).2.2.2.2, if_pos hfield]
  have hev : SyscallInstrsChip.ExitCodeValid r.op_c_memory.prev_value :=
    (spec.2.2.2.2.2.2.2.2.2.1.2 hcd).2
  exact hev

/-- **RowLaw.** The row's own constraints give all four architecture-level laws. This is where
`SelectorsValid` earns its place: `ResultLaw` and `PcLaw` are `if`-then-`else` on the *event's* id,
while every arm `Spec` speaks of a selector column, and the selector bridge is the only thing that
connects them. Assembling the law from the arms — rather than proving it directly — is what makes a
missing arm a missing theorem. -/
theorem rowLaw_of_spec_and_pulledFacts (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1) :
    (syscallEventOfRow r).RowLaw := by
  have hp : 2 ^ 17 < p := Fact.out
  have : Fact (1 < p) := ⟨by omega⟩
  have htb : (syscallEventOfRow r).tableByte = (SyscallInstrsChip.tableByte r).val :=
    tableByte_syscallEventOfRow r sel real
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `WellRouted`: the routing byte is boolean, which the row asserts ungated.
    rcases spec.1.2.2.2.2 with h | h
    · exact Or.inl (by rw [htb, h, ZMod.val_zero])
    · exact Or.inr (by rw [htb, h, ZMod.val_one])
  · -- `ResultLaw`: the three write arms, dispatched on the event's id.
    unfold CoreSyscallEvent.ResultLaw
    by_cases h3 : (syscallEventOfRow r).syscallId = Machine.enterUnconstrainedSyscallId
    · rw [if_pos h3]; exact arm_enterUnconstrained r spec sel pulled real h3
    · rw [if_neg h3]
      by_cases h240 : (syscallEventOfRow r).syscallId = Machine.hintLenSyscallId
      · rw [if_pos h240]; trivial
      · rw [if_neg h240]; exact arm_default r spec sel pulled real h3 h240
  · -- `PcLaw`: park at `haltPc`, or advance one instruction using the Program bus's low-limb bound.
    unfold CoreSyscallEvent.PcLaw
    by_cases h0 : (syscallEventOfRow r).syscallId = Machine.haltSyscallId
    · rw [if_pos h0]; exact arm_halt r spec sel real h0
    · rw [if_neg h0]; exact arm_pcAdvance_of_pcBound r spec sel real h0 (pulled real).2.1
  · -- `HandlerAddressesFit`: a dispatched row drops its fourth operand limb, leaving 48 bits.
    intro htable
    have hfield : SyscallInstrsChip.tableByte r = 1 := by
      rcases spec.1.2.2.2.2 with h | h
      · rw [CoreSyscallEvent.hasTable, htb, h, ZMod.val_zero] at htable
        exact absurd htable (by decide)
      · exact h
    have hdisp : r.op_b_memory.prev_value[3] = 0 ∧ r.op_c_memory.prev_value[3] = 0 :=
      spec.2.2.2.2.2.2.2.1 hfield
    have hb : Word.isU64 r.op_b_memory.prev_value := (pulled real).2.2.2.2.2.2.2.1
    have hc : Word.isU64 r.op_c_memory.prev_value := (pulled real).2.2.2.2.2.2.2.2.2.1
    have hb0 : (r.op_b_memory.prev_value[0]).val < 2 ^ 16 := hb 0
    have hb1 : (r.op_b_memory.prev_value[1]).val < 2 ^ 16 := hb 1
    have hb2 : (r.op_b_memory.prev_value[2]).val < 2 ^ 16 := hb 2
    have hc0 : (r.op_c_memory.prev_value[0]).val < 2 ^ 16 := hc 0
    have hc1 : (r.op_c_memory.prev_value[1]).val < 2 ^ 16 := hc 1
    have hc2 : (r.op_c_memory.prev_value[2]).val < 2 ^ 16 := hc 2
    constructor
    · rw [arg1_syscallEventOfRow, hdisp.1, ZMod.val_zero]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [arg2_syscallEventOfRow, hdisp.2, ZMod.val_zero]
      simp only [BitVec.toNat_ofNat]
      omega


/-- The released context-bearing interface follows from the row and its pulled bounds alone. -/
theorem rowLaw_of_spec (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1) (ctx : SyscallRowContext r program source) :
    (syscallEventOfRow r).RowLaw := by
  cases ctx
  exact rowLaw_of_spec_and_pulledFacts r spec sel pulled real

end Arms

/-- **Coverage.** Under the canonicity premise and a zero table byte, the row's id is one of the
thirteen — so the arms above are a total dispatch and no case is silently unhandled. -/
theorem inlineSyscallIds_exhaustive (event : CoreSyscallEvent) (hc : event.IsInlineCanonical) :
    event.syscallId ∈ inlineSyscallIds := by
  rw [CoreSyscallEvent.syscallId_of_inlineCanonical hc]; exact hc

/-! ## The assembled transition -/

/-! ### The handler's two reachable arms

`full.run` has four branches, but a canonical row reaches only two: the table byte is zero and the
id is inline, so the two `none` arms are unreachable. Naming the reachable pair keeps the assembled
transition from re-deriving the dispatch each time. -/

theorem full_run_halt (program : GuestProgram) (event : CoreSyscallEvent) (source : SailState)
    (htable : event.tableByte = 0) (h0 : event.syscallId = Machine.haltSyscallId) :
    ExecutableSyscallHandler.full.run program event source
      = some { source with regs := source.regs.insert Register.PC Machine.haltPc } := by
  simp [ExecutableSyscallHandler.full, htable, h0]

theorem full_run_inline (program : GuestProgram) (event : CoreSyscallEvent) (source : SailState)
    (htable : event.tableByte = 0) (h0 : event.syscallId ≠ Machine.haltSyscallId)
    (hmem : event.syscallId ∈ inlineSyscallIds) :
    ExecutableSyscallHandler.full.run program event source
      = some { source with regs :=
          (source.regs.insert Register.PC (event.pc + 4)).insert Register.x5 event.result } := by
  simp [ExecutableSyscallHandler.full, htable, h0, hmem]

/-- **A syscall row executes a syscall.** The row's constraints, the ensemble's operand and carry
facts, and canonicity together give the full `SyscallTransition` against the thirteen-arm handler —
which is exactly what a walked syscall row must supply to the grounding engine.

Note where each conjunct comes from, because the division is the whole design: `RowLaw` is the
*row's*, `MatchesStates`' source half is the *bus's* (it is what the pulls observed), its target half
is the *handler's*, and the handler clause is the handler's own definition. Nothing is assumed twice
and nothing is left to a frame rule. -/
theorem syscallTransition_of_row (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram)
    (source : SailState)
    (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1)
    (canonical : (syscallEventOfRow r).IsInlineCanonical)
    (ctx : SyscallRowContext r program source) :
    ∃ target : SailState,
      ExecutableSyscallHandler.full.run program (syscallEventOfRow r) source = some target ∧
      Machine.SyscallTransition ExecutableSyscallHandler.full.relation program
        (syscallEventOfRow r) source target := by
  have hlaw := rowLaw_of_spec r program source spec sel pulled real ctx
  have htable : (syscallEventOfRow r).tableByte = 0 :=
    CoreSyscallEvent.tableByte_of_inlineCanonical canonical
  obtain ⟨hpc, hx5, hx10, hx11⟩ :
      source.regs.get? Register.PC = some (syscallEventOfRow r).pc ∧
      source.get_reg? 5#5 = some (syscallEventOfRow r).rawCode ∧
      source.get_reg? 10#5 = some (syscallEventOfRow r).arg1 ∧
      source.get_reg? 11#5 = some (syscallEventOfRow r).arg2 :=
    ⟨ctx.pcValue, ctx.operandValues.1, ctx.operandValues.2.1, ctx.operandValues.2.2⟩
  by_cases h0 : (syscallEventOfRow r).syscallId = Machine.haltSyscallId
  · -- HALT parks at `haltPc` and leaves `x5` alone; `ResultLaw` is what makes that agree with
    -- `MatchesStates`, since on this arm the result *is* the unchanged code.
    refine ⟨_, full_run_halt program _ source htable h0, hlaw, ⟨hpc, hx5, hx10, hx11, ?_, ?_⟩,
      full_run_halt program _ source htable h0⟩
    · rw [arm_halt r spec sel real h0]
      simp
    · rw [arm_default r spec sel pulled real (by rw [h0]; decide) (by rw [h0]; decide),
        SailState.get_reg?_insert_PC]
      exact hx5
  · -- Every other inline arm advances the pc and writes `t0`, which is exactly what the two
    -- inserts do; canonicity is what rules out the handler's `none` tail.
    have hmem : (syscallEventOfRow r).syscallId ∈ inlineSyscallIds :=
      inlineSyscallIds_exhaustive _ canonical
    refine ⟨_, full_run_inline program _ source htable h0 hmem, hlaw,
      ⟨hpc, hx5, hx10, hx11, ?_, ?_⟩, full_run_inline program _ source htable h0 hmem⟩
    · rw [arm_pcAdvance r spec sel real h0 ctx.pcCarry]
      simp [Std.ExtDHashMap.get?_insert]
    · simp [SailState.get_reg?]

end SP1Clean.Soundness
