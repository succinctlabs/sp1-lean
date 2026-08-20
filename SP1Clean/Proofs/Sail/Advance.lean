import SP1Clean.Proofs.Sail.TryStepReduction
import SP1Clean.Soundness.RowEffectDefs
import SP1Clean.Soundness.ProgramConsistency
import RISCV.Instructions
import RISCV.SailToRV64

/-! # Phase 4 — the uniform per-chip `advance` (Sail-step obligation)

The generic composition wiring the Phase-3 `try_step` reduction ladder (`Proofs/Sail/TryStepReduction.lean`)
into each chip's Sail-step obligation (`ChipKind.advance`, `Soundness/ChipRow.lean`):
`RefinesAt → OperandsBound → ∃ s', SailStep s s' ∧ RowEffect prog row s s'`.

The load-bearing goal is **uniformity**: one `sp1Effect` (a function of the committed `RowView`), one
generic `advance_write_core` proof, and thin per-chip adapters — replacing the 25 bespoke per-chip
Sail-step predicates so the audit surface is a single statement. -/

open LeanRV64D.Defs
namespace SP1Clean.Advance

open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace
open SP1Clean.TryStepReduction
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The row's committed next-pc as a 64-bit value — data-dependent (straight-line `pc+4` or the control-flow
target), read uniformly off the RowView's `next_pc` limbs via `sndPcOf (stateAccess v)`. -/
def sndPcBV (v : Trace.RowView (ZMod p)) : BitVec 64 := sndPcOf (stateAccess v)

/-- The row's `rd` register index, inverting the committed `op_a = (rd.toNat : ZMod p)` (canonical for a
real row where `rd.toNat < 32 < p`). -/
def rdOf (v : Trace.RowView (ZMod p)) : regidx := .Regidx (BitVec.ofNat 5 v.adapter.op_a.val)

/-- **The single uniform SP1 chip effect** (a function of the committed `RowView`): commit the next-pc, then
write `rd = op_a` with the committed `rdWrite`. Every register-writing family's `sp1_<op>` equals
`sp1Effect (view inp cols)` (x0-destination is a definitional no-op via `wX_bits x0 = pure ()`). -/
def sp1Effect (v : Trace.RowView (ZMod p)) : SailM Unit := do
  set_next_pc (sndPcBV v)
  wX_bits (rdOf v) (Word.toBitVec64 v.rdWrite)

/-- The control-flow effect (branches): commit the next-pc only, no register write. -/
def sp1Effect_ctrl (v : Trace.RowView (ZMod p)) : SailM Unit := set_next_pc (sndPcBV v)

/-! ## Pilot algebra (fetch + operand leaves) -/

/-- **L1 — little-endian byte reassembly.** The four `RomLoaded` bytes of a fetched word `w`
(`data₀..₃ = w.extractLsb' (8·i) 8`), concatenated high-to-low, reassemble `w`. The `: BitVec 32`
ascription normalizes the `8+8+8+8` append width to `32` so `bv_decide` sees a well-typed goal. -/
theorem word_reassemble (w : BitVec 32) :
    (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 : BitVec 32) = w := by
  bv_decide

/-- **L2 — 4-alignment clears the low two pc bits.** A `pc` with `pc.toNat % 4 = 0` has bit 0 and bit 1
zero — the `access0`/`access1` fields the fetch reduction needs. -/
theorem pc_align_bits (pc : BitVec 64) (h : pc.toNat % 4 = 0) :
    BitVec.ofBool pc[0] = 0#1 ∧ BitVec.ofBool pc[1] = 0#1 := by
  have hb : pc[0] = false ∧ pc[1] = false := by
    simp only [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not]
    omega
  rw [hb.1, hb.2]; exact ⟨rfl, rfl⟩

/-- **L4 — the ADD execute identity.** The RV64 `ADD` semantics (`RV64.add rs2 rs1 = rs1 + rs2`) equal the
pure R-type execute value (`execute_RTYPE_pure op1 op2 ADD = op1 + op2`); the bridge tying a chip's `Spec`
result to the value `rtype_execute_reaches` writes. -/
theorem rv64add_eq_execute_RTYPE_pure (a b : BitVec 64) :
    RV64.add b a = execute_RTYPE_pure a b rop.ADD := by
  simp [RV64.add, execute_RTYPE_pure]

/-- **L5 — `rdOf` inverts the committed `op_a`.** When the committed destination column `op_a = (rd.toNat)`
for a genuine `rd : BitVec 5`, the `BitVec.ofNat 5 op_a.val` in `rdOf` recovers `rd` exactly (the register
index is canonical because `rd.toNat < 32 < p`). -/
theorem ofNat_val_eq_of_cast {rd : BitVec 5} {op_a : ZMod p} (hrd : (rd.toNat : ZMod p) = op_a) :
    BitVec.ofNat 5 op_a.val = rd := by
  rw [← hrd]
  have hp : (2:ℕ) ^ 17 < p := Fact.out
  rw [ZMod.val_natCast_of_lt (by have := rd.isLt; omega)]
  simp [BitVec.ofNat_toNat]

/-- **L3 — the straight-line pc bridge.** For a row whose committed `next_pc` is the low-limb `+4`
(`#v[pc[0]+4, pc[1], pc[2]]`), the row's committed send pc is the receive pc plus four: `sndPcOf = rcvPcOf +
4`. Needs the low pc limb `< 2^16` (from the reader `Spec`, via `DecodeBounds`) so `pc[0]+4` does not wrap
the field, and `BitVec.ofNat`'s additivity carries the `+4` out. This is the `RowEffect.pc` content for the
whole straight-line (`pc+4`) family. -/
theorem sndPc_straightline (r : Trace.RowView (ZMod p))
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h0 : (r.state.pc[0]).val < 2 ^ 16) :
    sndPcOf (stateAccess r) = rcvPcOf (stateAccess r) + 4#64 := by
  have hp : (2:ℕ) ^ 17 < p := Fact.out
  have hv4 : (4 : ZMod p).val = 4 := val_4_zmod_p
  have e0 : (r.state.pc[0] + 4 : ZMod p).val = (r.state.pc[0]).val + 4 := by
    rw [ZMod.val_add, hv4, Nat.mod_eq_of_lt (by omega)]
  simp only [sndPcOf, rcvPcOf, stateAccess, pcBitsOfVals, hstraight,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, e0]
  rw [show (r.state.pc[0]).val + 4 + (r.state.pc[1]).val * 2 ^ 16 + (r.state.pc[2]).val * 2 ^ 32
        = ((r.state.pc[0]).val + (r.state.pc[1]).val * 2 ^ 16 + (r.state.pc[2]).val * 2 ^ 32) + 4 from by ring,
     BitVec.ofNat_add]

/-! ## The execute-stage bridge (per family) -/

/-- **The RTYPE execute stage reaches `Retire_Success`.** `execute (.RTYPE …)` on a state whose `rs1`/`rs2`
register reads are known runs to `Retire_Success` and writes only `rd` (via `wX_bits`, x0-uniform). This is
the `hexec` the ladder needs, for the whole R-type family (Add/Sub/Bitwise/Lt/Shift/… — one `op`). The
committed write value is `execute_RTYPE_pure op_b op_c op`; a chip's semantic `Spec` ties that to `rdWrite`. -/
theorem rtype_execute_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : rop)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b)
    (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.RTYPE (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_RTYPE_pure op_b op_c op)))}) := by
  simp only [execute, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **The RTYPEW execute stage reaches `Retire_Success`**, generic over the 32-bit W-op. `execute (.RTYPEW …)`
on a state whose `rs1`/`rs2` reads are known runs to `Retire_Success` writing only `rd` with
`execute_RTYPEW_pure op_b op_c op` (the low-32 result sign-extended to 64). The `hexec` the shared core needs
for the W-op family (Addw/Subw + SLLW/SRLW/SRAW); structurally the RTYPE twin (`execute_RTYPEW'` = two reads +
one write), so the proof is identical modulo `RTYPEW`. -/
theorem rtypew_execute_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : ropw)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b)
    (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.RTYPEW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_RTYPEW_pure op_b op_c op)))}) := by
  simp only [execute, execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **`execute_ITYPE` pure part** — the I-type twin of `execute_RTYPE_pure` (op1 = the `rs1` read, `immext`
= the sign-extended immediate). Covers the ALU immediate ops ADDI/SLTI/SLTIU/ANDI/ORI/XORI, so one
`itype_execute_reaches` serves the whole immediate-ALU family (Addi + the immediate forms of Bitwise/Lt).
(Placed here beside the execute-reaches lemmas; a natural cleanup is to hoist it into `Model/SailWrap.lean`
next to `execute_RTYPE_pure`.) -/
def execute_ITYPE_pure (op1 immext : BitVec 64) (op : iop) : BitVec 64 :=
  match op with
  | .ADDI => op1 + immext
  | .SLTI => zero_extend (m := 64) (bool_to_bit (zopz0zI_s op1 immext))
  | .SLTIU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u op1 immext))
  | .ANDI => op1 &&& immext
  | .ORI => op1 ||| immext
  | .XORI => op1 ^^^ immext

/-- `execute_ITYPE` with the isolated pure part (the I-type twin of `execute_RTYPE'`). -/
def execute_ITYPE' (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : SailM ExecutionResult := do
  let rs1_bits ← rX_bits rs1
  wX_bits rd (execute_ITYPE_pure rs1_bits (sign_extend (m := 64) imm) op)
  pure RETIRE_SUCCESS

@[simp] theorem execute_ITYPE_eq_execute_ITYPE' (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    execute_ITYPE imm rs1 rd op = execute_ITYPE' imm rs1 rd op := by
  cases op <;> simp_all [execute_ITYPE', execute_ITYPE, execute_ITYPE_pure]

/-- **The ITYPE execute stage reaches `Retire_Success`**, generic over the ALU immediate op. `execute
(.ITYPE …)` on a state whose `rs1` read is known runs to `Retire_Success` writing only `rd` with
`execute_ITYPE_pure op_b (signExtend imm) op` — the I-type `hexec` the shared core needs (one read + the
immediate, no `rs2`). Serves the whole immediate-ALU family via `op`. -/
theorem itype_execute_reaches (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (op : iop)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.ITYPE (imm, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_ITYPE_pure op_b (sign_extend (m := 64) imm) op)))}) := by
  simp only [execute, execute_ITYPE_eq_execute_ITYPE', execute_ITYPE']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The pure value written by a 64-bit shift-immediate instruction.  The shift amount is genuinely
six bits in RV64; keeping that width here covers shifts 32--63 rather than routing through the older
five-bit convenience lemmas in `RISCV.SailToRV64`. -/
def execute_SHIFTIOP_pure (op_b : BitVec 64) (shamt : BitVec 6) (op : sop) : BitVec 64 :=
  match op with
  | .SLLI => shift_bits_left op_b shamt
  | .SRLI => shift_bits_right op_b shamt
  | .SRAI => shift_bits_right_arith op_b shamt

/-- `execute_SHIFTIOP` with its register read separated from the pure shift. -/
def execute_SHIFTIOP' (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : SailM ExecutionResult := do
  let op_b ← rX_bits rs1
  wX_bits rd (execute_SHIFTIOP_pure op_b shamt op)
  pure RETIRE_SUCCESS

@[simp] theorem execute_SHIFTIOP_eq_execute_SHIFTIOP'
    (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) :
    execute_SHIFTIOP shamt rs1 rd op = execute_SHIFTIOP' shamt rs1 rd op := by
  have hshamt : Sail.BitVec.extractLsb shamt 5 0 = shamt := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt]
    exact shamt.isLt
  cases op <;>
    simp [execute_SHIFTIOP, execute_SHIFTIOP', execute_SHIFTIOP_pure,
      LeanRV64D.Functions.log2_xlen, hshamt]

/-- The 64-bit shift-immediate execute stage reaches `Retire_Success`, reading only `rs1` and
writing the result of the official six-bit shift operation to `rd`. -/
theorem shiftitype_execute_reaches (shamt : BitVec 6) (rs1_idx rd_idx : BitVec 5) (op : sop)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.SHIFTIOP (shamt, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_SHIFTIOP_pure op_b shamt op)))}) := by
  simp only [execute, execute_SHIFTIOP_eq_execute_SHIFTIOP', execute_SHIFTIOP']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The pure value written by a word shift-immediate instruction. -/
def execute_SHIFTIWOP_pure (op_b : BitVec 64) (shamt : BitVec 5) (op : sopw) : BitVec 64 :=
  let op_b32 := Sail.BitVec.extractLsb op_b 31 0
  let result : BitVec 32 :=
    match op with
    | .SLLIW => shift_bits_left op_b32 shamt
    | .SRLIW => shift_bits_right op_b32 shamt
    | .SRAIW => shift_bits_right_arith op_b32 shamt
  sign_extend (m := 64) result

/-- `execute_SHIFTIWOP` with its register read separated from the pure word shift. -/
def execute_SHIFTIWOP' (shamt : BitVec 5) (rs1 rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let op_b ← rX_bits rs1
  wX_bits rd (execute_SHIFTIWOP_pure op_b shamt op)
  pure RETIRE_SUCCESS

@[simp] theorem execute_SHIFTIWOP_eq_execute_SHIFTIWOP'
    (shamt : BitVec 5) (rs1 rd : regidx) (op : sopw) :
    execute_SHIFTIWOP shamt rs1 rd op = execute_SHIFTIWOP' shamt rs1 rd op := by
  cases op <;> rfl

/-- The word shift-immediate execute stage reaches `Retire_Success`, reading only `rs1`. -/
theorem shiftiwtype_execute_reaches (shamt : BitVec 5) (rs1_idx rd_idx : BitVec 5) (op : sopw)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.SHIFTIWOP (shamt, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_SHIFTIWOP_pure op_b shamt op)))}) := by
  simp only [execute, execute_SHIFTIWOP_eq_execute_SHIFTIWOP', execute_SHIFTIWOP']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **`execute_ADDIW` pure part** — `signExtend 64 (extractLsb (op_b + immext) 31 0)` (the low-32 sum
sign-extended). ADDIW is its own Sail AST arm (`execute_ADDIW`), not `execute_ITYPE .ADDI`, so it gets its
own pure part / reaches (the `execute_RTYPEW_pure`-analogue for the immediate-W form). -/
def execute_ADDIW_pure (op_b immext : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (op_b + immext) 31 0)

/-- **The ADDIW execute stage reaches `Retire_Success`.** `execute (.ADDIW …)` on a state whose `rs1` read is
known runs to `Retire_Success` writing only `rd` with `execute_ADDIW_pure op_b (signExtend imm)`. The
immediate-W `hexec` the shared core needs (one read + the immediate; the `let y ← pure …` intermediate folds
via `pure_bind`). -/
theorem execute_ADDIW_reaches (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.ADDIW (imm, .Regidx rs1_idx, .Regidx rd_idx))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_ADDIW_pure op_b (sign_extend (m := 64) imm))))}) := by
  simp only [execute, execute_ADDIW, execute_ADDIW_pure, pure_bind]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **`execute_UTYPE` pure part** — LUI writes `signExtend (imm ++ 0¹²)` (the immediate `<< 12`); AUIPC writes
`pc + signExtend (imm ++ 0¹²)` (pc-relative). The only `execute` value in the straight-line family that
*depends on the pc* — hence the pc-frame in `advance_write_core`'s `hexec`. -/
def execute_UTYPE_pure (op : uop) (pc : BitVec 64) (imm : BitVec 20) : BitVec 64 :=
  match op with
  | .LUI => sign_extend (m := 64) (imm +++ 0#12)
  | .AUIPC => pc + sign_extend (m := 64) (imm +++ 0#12)

/-- **The UTYPE execute stage reaches `Retire_Success`.** `execute (.UTYPE …)` on a state `t` whose pc is
`pc` runs to `Retire_Success` writing only `rd` with `execute_UTYPE_pure op pc imm` — no register reads, but
AUIPC reads the pc (`get_arch_pc = readReg PC`), threaded via `hpct`. -/
theorem execute_UTYPE_reaches (imm : BitVec 20) (rd_idx : BitVec 5) (op : uop) (pc : BitVec 64)
    (t : SailState) (hpct : t.regs.get? Register.PC = some pc) :
    (execute (.UTYPE (imm, .Regidx rd_idx, op))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then t
           else {t with regs := (t.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_UTYPE_pure op pc imm)))}) := by
  have harchpc : (get_arch_pc ()).run t = .ok pc t := by
    simp [get_arch_pc, PreSail.readReg, hpct]
  cases op
  · simp only [execute, execute_UTYPE, execute_UTYPE_pure, pure_bind]
    rw [run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]; rfl
  · simp only [execute, execute_UTYPE, execute_UTYPE_pure]
    rw [run_bind_of_run t _ pc harchpc, pure_bind,
      run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]; rfl

/-! ## The `StraightLineReady` producer (the `toStraightLineReady` body) -/

/-- **`StraightLineReady` on the post-`minstret_increment`-write state.** From the quiescent machine-mode
config facts on `s` — initialized, machine privilege, active hart, `mstatus.MIE = 0`, `mideleg = 0`, no
landing-pad expectation, valid memory config, PC 4-aligned, and the ROM word present in memory — the
`try_step` post-write state `{s with regs.insert minstret_increment b}` is `StraightLineReady` for the
fetched word `data₃ ++ … ++ data₀`. Pure assembly: the two deep fields come from the `_writeMinstret`
frame lemmas (`run_dispatchInterrupt_machine_none_writeMinstret` / `run_fetch_eq_F_Base_writeMinstret`);
the three register-read fields frame through the disjoint `minstret_increment` insert. This is the body of
the eventual `SailConfigured.toStraightLineReady` (its hypotheses are the strengthened config's fields). -/
theorem straightLineReady_writeMinstret
    (s : SailState) (b : Bool) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (hinit : s.isInitialized)
    (hconfig : SailMem.SailState.isValidMemConfig s hinit)
    (hmie : _get_Mstatus_MIE (s.regs.get Register.mstatus (hinit _)) = 0#1)
    (hmideleg : s.regs.get Register.mideleg (hinit _) = zeros)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_active : s.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (h_elp : s.regs.get? Register.elp
      ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED))
    (h_pc : s.regs.get Register.PC (hinit _) = pc)
    (h_access0 : BitVec.ofBool pc[0] = 0#1) (h_access1 : BitVec.ofBool pc[1] = 0#1)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (pc + 0) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_align : Int.tmod (↑(zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64).toNat) 4 = 0)
    (h_not_rvc : isRVC (Sail.BitVec.extractLsb (data₃ ++ data₂ ++ data₁ ++ data₀) 15 0) = false)
    (hmem₀ : s.mem[(pc + 0).toNat]? = some data₀) (hmem₁ : s.mem[(pc + 0).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(pc + 0).toNat + 2]? = some data₂) (hmem₃ : s.mem[(pc + 0).toNat + 3]? = some data₃) :
    StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) where
  init := SailState.isInitialized_insert s hinit _ _
  priv := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_priv
  active := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_active
  no_interrupt := run_dispatchInterrupt_machine_none_writeMinstret s hinit b hmie hmideleg
  fetched := run_fetch_eq_F_Base_writeMinstret pc data₀ data₁ data₂ data₃ s hinit b hconfig h_pc
    h_access0 h_access1 h_aligned h_in_range h_align h_not_rvc hmem₀ hmem₁ hmem₂ hmem₃
  no_landing_pad := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_elp

/-- **The PC-dependent local fetch predicate** — the *local* half of the `try_step` precondition (the
persist-able global half is `SailConfigured`). At `s`'s current pc, the pc is 4-aligned and the 4 ROM
bytes are present in memory, so the base-instruction fetch yields the little-endian word
`data₃ ++ … ++ data₀`. Kept separate from `SailConfigured` (not persist-able) because it is about *this*
pc — in the walk it is derived at each row from `RomLoaded` + the guest program's `rom_aligned` + the row's
pc-match, not carried as a state invariant. -/
structure FetchReady (s : SailState) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8) : Prop where
  /-- The current pc. -/
  pc_eq : s.regs.get? Register.PC = some pc
  access0 : BitVec.ofBool pc[0] = 0#1
  access1 : BitVec.ofBool pc[1] = 0#1
  aligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true
  in_range : range_subset (zero_extend (BitVec.addInt (pc + 0) 0))
    (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true
  align : Int.tmod (↑(zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64).toNat) 4 = 0
  not_rvc : isRVC (Sail.BitVec.extractLsb (data₃ ++ data₂ ++ data₁ ++ data₀) 15 0) = false
  mem0 : s.mem[(pc + 0).toNat]? = some data₀
  mem1 : s.mem[(pc + 0).toNat + 1]? = some data₁
  mem2 : s.mem[(pc + 0).toNat + 2]? = some data₂
  mem3 : s.mem[(pc + 0).toNat + 3]? = some data₃

/-- **`SailConfigured` + the local fetch facts assemble `StraightLineReady`** — the uniform bridge from the
audit-surface config (`RefinesAt.cfg`) to the ladder's readiness predicate on the post-`minstret`-write
state. The global `SailConfigured` supplies the seven persist-able fields; `FetchReady` supplies the
PC-dependent fetch facts. This is the packaged form of `straightLineReady_writeMinstret`. -/
theorem SailConfigured.toStraightLineReady {s : SailState} (cfg : SailConfigured s) (b : Bool)
    (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃) :
    StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
  straightLineReady_writeMinstret s b pc data₀ data₁ data₂ data₃
    cfg.init cfg.toValidMemConfig cfg.mie cfg.mideleg cfg.priv cfg.active cfg.no_landing_pad
    (by have h := hfetch.pc_eq; rwa [Std.ExtDHashMap.get?_eq_some_get (cfg.init _), Option.some_inj] at h)
    hfetch.access0 hfetch.access1 hfetch.aligned hfetch.in_range hfetch.align hfetch.not_rvc
    hfetch.mem0 hfetch.mem1 hfetch.mem2 hfetch.mem3

/-- **L7 — the `FetchReady` producer.** At a state whose PC is a ROM address `pc` (`fetchWord pc = some w`)
with the ROM bytes present (`RomLoaded`), the PC-dependent local fetch facts hold: alignment (from the
program's `rom_aligned`), `in_range` (from `rom_in_window` via `range_subset_sp1_pma`), `not_rvc` (from
`rom_full_width` + the byte reassembly `word_reassemble`), and the four ROM bytes (from `RomLoaded`). This
is the derivation the split promised — `FetchReady` reconstructed at each row from the committed program +
the pc match, so it need not be a persist-able state invariant. -/
theorem fetchReady_of_romLoaded
    (prog : GuestProgram) (s : SailState) (pc : BitVec 64) (w : BitVec 32)
    (hrom : RomLoaded prog s) (hfetch : prog.fetchWord pc = some w)
    (hpc : s.regs.get? Register.PC = some pc) :
    FetchReady s pc (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8)
      (w.extractLsb' 24 8) := by
  have hfacts : pc.toNat % 4 = 0 ∧ (2 ^ 16 ≤ pc.toNat ∧ pc.toNat + 4 ≤ 2 ^ 48)
      ∧ w.extractLsb' 0 2 = 0b11#2 := by
    have hf := hfetch
    rw [GuestProgram.fetchWord, Option.map_eq_some_iff] at hf
    obtain ⟨e, hfind, hew⟩ := hf
    have hmem := List.mem_of_find?_eq_some hfind
    have hpc' : e.1 = pc := by have := List.find?_some hfind; simpa using this
    refine ⟨?_, ?_, ?_⟩
    · rw [← hpc']; exact prog.rom_aligned e.1 (List.mem_map_of_mem hmem)
    · rw [← hpc']; exact prog.rom_in_window e hmem
    · rw [← hew]; exact prog.rom_full_width e hmem
  obtain ⟨hmod4, ⟨hlo, hhi⟩, h_fw⟩ := hfacts
  have hz : (zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64) = pc := by
    simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend, BitVec.ofInt]
  exact
    { pc_eq := hpc
      access0 := (pc_align_bits pc hmod4).1
      access1 := (pc_align_bits pc hmod4).2
      aligned := (SailMem.is_aligned_vaddr_iff_mod pc 4).mpr hmod4
      in_range := by
        rw [show (pc + 0 : BitVec 64) = pc from by bv_decide]
        exact SailMem.range_subset_sp1_pma pc 4 (by norm_num) hlo hhi
      align := by rw [hz, show (4:ℤ) = ((4:ℕ):ℤ) from rfl, ← Int.ofNat_tmod, hmod4]; rfl
      not_rvc := by
        rw [word_reassemble w]
        simp only [isRVC, Sail.BitVec.extractLsb, BitVec.extractLsb]
        rw [show BitVec.extractLsb' 0 (1 - 0 + 1) (BitVec.extractLsb' 0 (15 - 0 + 1) w)
              = w.extractLsb' 0 2 from by
          apply BitVec.eq_of_getLsbD_eq; intro i; simp [BitVec.getLsbD_extractLsb']]
        rw [h_fw]; decide
      mem0 := by have h := hrom pc w hfetch 0; simpa using h
      mem1 := by have h := hrom pc w hfetch 1; simpa using h
      mem2 := by have h := hrom pc w hfetch 2; simpa using h
      mem3 := by have h := hrom pc w hfetch 3; simpa using h }

/-! ## The generic composition -/

/-- **`run_hart_active` reaches the `Retire_Success` step**, given the execute stage lands there: from the
Phase-3 ladder (`run_hart_active_eq_of_ready`) + a `hstage` fact that `writeReg nextPC (PC+4); execute I`
runs to `Retire_Success` at `s''`, `run_hart_active` yields `Step_Execute (Retire_Success, …)` at `s''`.
The `ExecuteAs` redirect is dead (`execute I` returned `Retire_Success`, not `ExecuteAs`). -/
theorem run_hart_active_reaches (s' s_a s'' : SailState) (w : BitVec 32) (I : instruction) (step_no : Nat)
    (hslr : StraightLineReady s' w)
    (hdec : (ext_decode w).run s' = .ok I s')
    (hsa : (LeanRV64D.writeReg Register.nextPC
        (BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4)).run s' = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'') :
    (run_hart_active step_no).run s'
      = .ok (Step.Step_Execute (ExecutionResult.Retire_Success (), zero_extend (m := 32) w)) s'' := by
  rw [run_hart_active_eq_of_ready s' w I step_no hslr hdec]
  rw [run_bind_of_run s' _ _ (Sail.run_readReg_of_isInitialized s' Register.PC hslr.init),
    run_bind_of_run' s' s_a _ () hsa,
    run_bind_of_run' s_a s'' (execute I) (ExecutionResult.Retire_Success ()) hexec]
  rfl

/-- **`try_step` reaches the row's execute effect** — the full outer-frame composition. On the
post-minstret-write state `s' = {s with regs.insert minstret_increment b}` (with `StraightLineReady s'`),
`try_step 0 false` reduces to its `tick_pc` + minstret tail on `s''` (= the post-`execute I` state), via
`run_hart_active_reaches` (into `h_ha`) + `tryStep_eq_of_hart_active`. -/
theorem tryStep_reaches (s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (hb : (should_inc_minstret Privilege.Machine).run s = .ok b s)
    (hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())) :
    (try_step 0 false).run s
      = (do
          tick_pc ()
          let mi ← LeanRV64D.readReg Register.minstret_increment
          if (true && mi) = true then do
              let m ← LeanRV64D.readReg Register.minstret
              LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
              (pure false : SailM Bool)
            else (pure false : SailM Bool)).run s'' :=
  tryStep_eq_of_hart_active s 0 b (zero_extend (m := 32) w) s'' hactive hb hcp
    (run_hart_active_reaches _ s_a s'' w I 0 hslr hdec hsa hexec) h_active''

/-- **The minstret-bump tail is a register-file frame**: run on any initialized state `t`, the
`minstret_increment`-gated `minstret ← minstret+1` bump yields `.ok false t'` with `t'` agreeing with `t`
on `PC` and on the whole `BitVec 5` register file — the bump touches only the `minstret` CSR. -/
theorem minstret_tail_frame (t : SailState) (hinit : t.isInitialized) :
    ∃ t' : SailState,
      (do
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run t = .ok false t'
      ∧ t'.regs.get? Register.PC = t.regs.get? Register.PC
      ∧ (∀ idx : BitVec 5, t'.get_reg? idx = t.get_reg? idx)
      ∧ t'.mem = t.mem
      ∧ (∀ R : Register, R ≠ Register.minstret → t'.regs.get? R = t.regs.get? R)
      ∧ t'.isInitialized := by
  rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret_increment hinit)]
  split
  · rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret hinit),
      run_writeReg_bind]
    refine ⟨_, rfl, ?_, (fun idx => ?_), rfl, (fun R hR => ?_), SailState.isInitialized_insert t hinit _ _⟩
    · rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
    · exact SailState.get_reg?_insert_of_ne (by unfold reg_idx_to_Register; split <;> decide)
    · rw [Std.ExtDHashMap.get?_insert, dif_neg (fun hc => hR (beq_iff_eq.mp hc).symm)]
  · exact ⟨_, rfl, rfl, fun _ => rfl, rfl, (fun _ _ => rfl), hinit⟩

/-- **The `tick_pc` + minstret tail's effect** on the observables: it commits `PC ← nextPC` and leaves every
`BitVec 5` register file entry fixed (the minstret bump touches only the `minstret` CSR, `tick_pc` only
`PC` — both outside the register file). -/
theorem tail_effect (s'' : SailState) (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState,
      (do
        tick_pc ()
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            (pure false : SailM Bool)
          else (pure false : SailM Bool)).run s'' = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized := by
  simp only [tick_pc_eq, bind_assoc]
  rw [run_bind_of_run s'' _ _ (Sail.run_readReg_of_isInitialized s'' Register.nextPC hinit''),
    run_writeReg_bind]
  obtain ⟨t', hrun, hPC', hxreg', hmem', hframe', hinit'⟩ := minstret_tail_frame
    {s'' with regs := s''.regs.insert Register.PC (s''.regs.get Register.nextPC (hinit'' _))}
    (SailState.isInitialized_insert s'' hinit'' _ _)
  refine ⟨t', hrun, ?_, (fun idx => ?_), hmem', (fun R hRpc hRm => ?_), hinit'⟩
  · rw [hPC', Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_eq_some_get (hinit'' _)]
  · rw [hxreg' idx]; exact SailState.get_reg?_insert_PC
  · rw [hframe' R hRm, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => hRpc (beq_iff_eq.mp hc).symm)]

/-- **The core `SailStep` composition** — joins the landed ladder (`tryStep_reaches`) with the tail's
observable effect (`tail_effect`). Given the ladder inputs on the post-minstret-write state, `try_step`
takes one real step to some `s_final` whose `PC` is the post-execute `nextPC` and whose `BitVec 5`
register file agrees with the post-execute state `s''`. This is the whole `try_step`-side content of a
register-writing chip's `advance`; per-chip work is only characterizing `s''` (via the execute bridge)
and building the ladder inputs from `RefinesAt`/`OperandsBound`. -/
theorem sailStep_of_ladder (s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (hb : (should_inc_minstret Privilege.Machine).run s = .ok b s)
    (hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState, (try_step 0 false).run s = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized := by
  obtain ⟨s_final, hrun, hPC, hxreg, hmem, hframe, hinitf⟩ := tail_effect s'' hinit''
  refine ⟨s_final, ?_, hPC, hxreg, hmem, hframe, hinitf⟩
  rw [tryStep_reaches s s_a s'' w I b hb hcp hactive hslr hdec hsa hexec h_active'']
  exact hrun

/-! ## Per-chip `advance` composition helpers -/

/-- **`SailConfigured` survives the `minstret_increment` write.** Every config field re-derives on
`{s with regs.insert minstret_increment b}` (the register is disjoint from every config CSR) — the fact the
ladder needs to apply the (∀-configured-state) decode and `toStraightLineReady` at the post-write state. -/
theorem SailConfigured.writeMinstret {s : SailState} (cfg : SailConfigured s) (b : Bool) :
    SailConfigured ({s with regs := s.regs.insert Register.minstret_increment b}) where
  init := SailState.isInitialized_insert s cfg.init _ _
  priv := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.priv
  active := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  mie := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mie
  mideleg := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mideleg
  no_landing_pad := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.no_landing_pad
  mprv_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mprv_disabled
  mseccfg_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mseccfg_disabled
  mseccfg_pmm := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mseccfg_pmm
  htif_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.htif_disabled
  pmp_off := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.pmp_off
  pma_regions := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.pma_regions

/-- **Register read-back.** The value `wX_bits`/`execute` writes to a non-`x0` register `rd` reads back
through `get_reg?` — the `bitVecToRegidxVal`/`reg_idx_must_64` casts cancel. This is the `RowEffect.regs`
rd-write clause.

The two `▸` casts are cancelled **explicitly** (`eqRec_eq_cast` → `cast_eq_iff_heq` →
`cast_heq`) rather than by `grind`: `grind` has to whnf through `reg_idx_must_64`'s 31-arm
`match` on `Register`, and that single call was the sole owner of this file's former file-scope
heartbeat ceiling — the same dependent-cast hazard `Model/SailWrap.lean` documents at its
`acLt` fix. -/
theorem get_reg?_writeBack (s : SailState) (rd : BitVec 5) (rd_ne : rd ≠ 0#5) (v : BitVec 64) :
    SailState.get_reg? ({s with regs := s.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd v)}) rd
      = some v := by
  simp only [SailState.get_reg?, Std.ExtDHashMap.get?_insert_self, if_neg (show ¬(rd = 0) from rd_ne),
    bitVecToRegidxVal]
  simp only [eqRec_eq_cast]
  apply cast_eq_iff_heq.mpr
  congr 1
  · exact reg_idx_must_64 rd
  · exact cast_heq _ v

/-- `reg_idx_to_Register` is injective on **nonzero** indices — it collides only at `0#5`/`31#5` (both map
to `x31`, the default arm), and `x0` is hardwired-`some 0` in `get_reg?` so that collision is inert. -/
theorem reg_idx_to_Register_ne (idx rd : BitVec 5) (hi : idx ≠ 0#5) (hr : rd ≠ 0#5) (hne : idx ≠ rd) :
    reg_idx_to_Register rd ≠ reg_idx_to_Register idx := by
  revert idx rd; decide

/-- **`SailConfigured` transfers along a config-register frame.** A state `sf` that is initialized and agrees
with `s` on the nine config registers is itself `SailConfigured` — the `RowEffect.cfg` persistence clause. -/
theorem SailConfigured.congr {sf s : SailState} (cfg : SailConfigured s) (hinit : sf.isInitialized)
    (hf : ∀ R : Register, R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus
      ∨ R = Register.mideleg ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
      ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n → sf.regs.get? R = s.regs.get? R) :
    SailConfigured sf := by
  have hget : ∀ (R : Register) (hsf : R ∈ sf.regs), sf.regs.get? R = s.regs.get? R →
      sf.regs.get R hsf = s.regs.get R (cfg.init R) := by
    intro R hsf heq
    rw [Std.ExtDHashMap.get?_eq_some_get hsf, Std.ExtDHashMap.get?_eq_some_get (cfg.init R)] at heq
    exact Option.some.injEq _ _ |>.mp heq
  exact
    { init := hinit
      priv := by rw [hf _ (by tauto)]; exact cfg.priv
      active := by rw [hf _ (by tauto)]; exact cfg.active
      mie := by rw [hget Register.mstatus (hinit _) (hf _ (by tauto))]; exact cfg.mie
      mideleg := by rw [hget Register.mideleg (hinit _) (hf _ (by tauto))]; exact cfg.mideleg
      no_landing_pad := by rw [hf _ (by tauto)]; exact cfg.no_landing_pad
      mprv_disabled := by rw [hget Register.mstatus (hinit _) (hf _ (by tauto))]; exact cfg.mprv_disabled
      mseccfg_disabled := by rw [hget Register.mseccfg (hinit _) (hf _ (by tauto))]; exact cfg.mseccfg_disabled
      mseccfg_pmm := by rw [hget Register.mseccfg (hinit _) (hf _ (by tauto))]; exact cfg.mseccfg_pmm
      htif_disabled := by rw [hget Register.htif_tohost_base (hinit _) (hf _ (by tauto))]; exact cfg.htif_disabled
      pmp_off := by rw [hget Register.pmpcfg_n (hinit _) (hf _ (by tauto))]; exact cfg.pmp_off
      pma_regions := by rw [hget Register.pma_regions (hinit _) (hf _ (by tauto))]; exact cfg.pma_regions }

/-- **The shared straight-line register-writing core.** Instruction-agnostic: the execute stage writes
*only* `rd` (leaving `nextPC = pc+4`), so this covers the whole straight-line register-writing family
(R-type, I-type, U-type, AluX0, loads-into-registers). From the audit-surface facts (config `cfg`, ROM via
`hfetch`, the committed pc, the fetched-word decode to `I`, `rd ≠ x0`, the `Spec`-derived write `value`),
one real `try_step` realizes the row's `RowEffect`. The **execute** enters as a hypothesis `hexec` (over any
state agreeing with `s` on the register file), so each family plugs in its own execute-reaches lemma
(`rtype_execute_reaches`/`itype_execute_reaches`/…) — the ladder + the five-clause `RowEffect` readoff are
shared. The only per-chip inputs to a wrapper are `I`, `value`/`hexec`, and `hval`. -/
theorem advance_write_core {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (rd : BitVec 5) (value : BitVec 64) (pc : BitVec 64)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc) (hrcv : pc = rcvPcOf (stateAccess r))
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.isInitialized →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ())
        {t with regs := t.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value)})
    (hrd_ne : rd ≠ 0#5) (hrd_a : (rd.toNat : ZMod p) = r.adapter.op_a)
    (hval : Word.toBitVec64 r.rdWrite = value)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hwrites : r.commit.writesReg = true)
    (hnomem : r.commit.memWrite = none) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hrdreg : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → R ≠ reg_idx_to_Register rd := by
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (unfold reg_idx_to_Register; split <;> decide)
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  -- the ladder state `s_a` agrees with `s` on the whole register file (only nextPC/minstret were inserted),
  -- so the family's `hexec` applies.
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  -- `s_a`'s PC is `s`'s PC (the `nextPC`/`minstret` inserts leave `Register.PC` untouched), so a
  -- pc-dependent execute (`AUIPC`, the jump links) reads the committed pc through `hexec`'s pc-frame.
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hinit_sa
  set s'' := ({s_a with regs := s_a.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value)})
    with hs''_def
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  -- the s'' → s register frame off the touched set
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      R ≠ reg_idx_to_Register rd → s''.regs.get? R = s.regs.get? R := fun R h1 h2 h3 => by
    rw [hs''_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h3 (beq_iff_eq.mp hc).symm),
      hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)
      (hrdreg Register.hart_state (by tauto))]; exact cfg.active
  have hinit'' : SailState.isInitialized s'' := by
    rw [hs''_def]; exact SailState.isInitialized_insert s_a hinit_sa _ _
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s'' (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active'' hinit''
  -- the s_final → s config-register frame
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (hrdreg R hR)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hs''_def, hsa_def, hs'_def]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun _ a => by rw [hmem_fin],
        fun mw hmw => absurd (hnomem.symm.trans hmw) (by simp)⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · -- pc
    rw [hPCf]
    have hnp : s''.regs.get? Register.nextPC = some npv := by
      rw [hs''_def, Std.ExtDHashMap.get?_insert,
        dif_neg (by unfold reg_idx_to_Register; split <;> decide), hsa_def,
        Std.ExtDHashMap.get?_insert_self]
    have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
      have h1 : s'.regs.get? Register.PC = some pc := by
        rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
      rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
      exact (Option.some.injEq _ _).mp h1
    rw [hnp]; congr 1
    rw [hnpv_def, hgetPC, sndPc_straightline r hstraight hpc0, ← hrcv]
    simp [BitVec.addInt]
  · -- regs (this is a register-writing chip, `hwrites : commit.writesReg = true` → the write + frame pair)
    rw [if_pos hwrites]
    refine ⟨?_, ?_⟩
    · -- the op_a write
      intro idx hidx
      obtain rfl : idx = rd := (ofNat_val_eq_of_cast hidx).symm.trans (ofNat_val_eq_of_cast hrd_a)
      rw [hxf idx, hs''_def, get_reg?_writeBack s_a idx hrd_ne _, ← hval]
    · -- the frame off op_a
      intro idx hidx
      rw [hxf idx]
      by_cases h0 : idx = 0#5
      · subst h0; simp [SailState.get_reg?]
      · have hidxrd : idx ≠ rd := fun heq => hidx (by rw [heq]; exact hrd_a)
        rw [hs''_def, SailState.get_reg?_insert_of_ne (reg_idx_to_Register_ne idx rd h0 hrd_ne hidxrd),
          hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
          SailState.get_reg?_insert_of_ne (hmne idx)]
  · -- cfg
    exact SailConfigured.congr cfg hinitf hcfg_frame

/-- **The R-type chip `advance` — RowView-generic, one call per chip.** For any straight-line R-type row
`r` refined by `s` (config + ROM + the committed pc), the Memory-bus value bound (`ValueOperandsBound`),
the Program-bus fetch truth (`decodedInROM`), the opcode/imm column shape, the routing fact `op_a ≠ 0`,
the low-pc-limb bound, and the `Spec`-derived write value `hval`, one real `try_step` produces the row's
committed `RowEffect`. Absorbs the whole per-chip plumbing — the ∀-state decode (`decodesRType`), the fetch
(`fetchReady_of_romLoaded`), and the two register reads — over `advance_write_core`, so each chip's adapter
only unpacks its own `Spec` for `hval`/`hpc0` and supplies the column-shape facts by `rfl`. **The only
per-chip-varying inputs are `op` and `hval`.** -/
theorem advance_of_rtype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : rop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((ropToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) op)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesRType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) rd
    (execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_c_memory.prev_value) op) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := rtype_execute_reaches rs2 rs1 rd op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- **The W-op chip `advance` — RowView-generic, one call per chip and 32-bit W-op** (`AddwChip`/`SubwChip`,
and the `*W` variants of Shift). The `execute_RTYPEW` twin of `advance_of_rtype`: identical straight-line,
two-read composition, only the decode (`decodesRTypew`) / execute (`rtypew_execute_reaches`) / write value
(`execute_RTYPEW_pure`) are the W forms. The only per-chip inputs are `op` and the `Spec`-derived `hval`
(`rdWrite = execute_RTYPEW_pure op_b op_c op` — the low-32 op sign-extended). -/
theorem advance_of_rtypew {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : ropw)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((ropwToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPEW_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) op)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesRTypew op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.RTYPEW (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) rd
    (execute_RTYPEW_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_c_memory.prev_value) op) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := rtypew_execute_reaches rs2 rs1 rd op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- **The I-type chip `advance` — RowView-generic, one call per chip and immediate ALU op** (`AddiChip`,
and the immediate forms of Bitwise/Lt). The I-type twin of `advance_of_rtype`: straight-line, one register
read (`rs1` → `op_b`), and the `op_c` column is the sign-extended immediate (`imm_c = 1`), whose 64-bit
value the round-trip `toBitVec64_bitVecToWord` recovers. Feeds the shared `advance_write_core` with
`itype_execute_reaches op`; the only per-chip inputs are `op` and the `Spec`-derived write identity `hval`
(`rdWrite = execute_ITYPE_pure op_b op_c op`). -/
theorem advance_of_itype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : iop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((iopToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = execute_ITYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c) op)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesIType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have himmbind : Word.toBitVec64 r.adapter.op_c = imm.signExtend 64 := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have hval' : Word.toBitVec64 r.rdWrite
      = execute_ITYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) (imm.signExtend 64) op := by
    rw [hval, himmbind]
  exact advance_write_core (instruction.ITYPE (imm, .Regidx rs1, .Regidx rd, op)) rd
    (execute_ITYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) (imm.signExtend 64) op)
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := itype_execute_reaches imm rs1 rd op (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval' hstraight hpc0 hwrites hnomem

/-- The 64-bit shift-immediate `advance`.  Unlike ordinary I-type ALU instructions, Sail represents
these with `.SHIFTIOP` and a six-bit immediate.  The committed Program operand is still a 64-bit word;
decode and the `bitVecToWord` round trip recover its low six bits exactly. -/
theorem advance_of_shiftitype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (op : sop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((sopToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = execute_SHIFTIOP_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          ((Word.toBitVec64 r.adapter.op_c).setWidth 6) op)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, shamt, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesShiftIType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]
    rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by
    intro h0
    apply hnonX0
    rw [hopa', h0]
    simp
  have himmbind : (Word.toBitVec64 r.adapter.op_c).setWidth 6 = shamt := by
    rw [show r.adapter.op_c = bitVecToWord (shamt.setWidth 64) from hopc,
      toBitVec64_bitVecToWord]
    bv_decide
  have hval' : Word.toBitVec64 r.rdWrite
      = execute_SHIFTIOP_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) shamt op := by
    rw [hval, himmbind]
  exact advance_write_core (instruction.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, op)) rd
    (execute_SHIFTIOP_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) shamt op)
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := shiftitype_execute_reaches shamt rs1 rd op
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t ((hframe rs1).trans hrs1)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval' hstraight hpc0 hwrites hnomem

/-- The word shift-immediate `advance`, using Sail's distinct `.SHIFTIWOP` instruction and five-bit
shift amount. -/
theorem advance_of_shiftiwtype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (op : sopw)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((sopwToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = execute_SHIFTIWOP_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          ((Word.toBitVec64 r.adapter.op_c).setWidth 5) op)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, shamt, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesShiftIWType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]
    rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by
    intro h0
    apply hnonX0
    rw [hopa', h0]
    simp
  have himmbind : (Word.toBitVec64 r.adapter.op_c).setWidth 5 = shamt := by
    rw [show r.adapter.op_c = bitVecToWord (shamt.setWidth 64) from hopc,
      toBitVec64_bitVecToWord]
    bv_decide
  have hval' : Word.toBitVec64 r.rdWrite
      = execute_SHIFTIWOP_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) shamt op := by
    rw [hval, himmbind]
  exact advance_write_core (instruction.SHIFTIWOP (shamt, .Regidx rs1, .Regidx rd, op)) rd
    (execute_SHIFTIWOP_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) shamt op)
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := shiftiwtype_execute_reaches shamt rs1 rd op
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t ((hframe rs1).trans hrs1)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval' hstraight hpc0 hwrites hnomem

/-- **The ADDIW chip `advance` — RowView-generic** (the immediate branch of `AddwChip`). The `.ADDIW` twin of
`advance_of_itype`: straight-line, one register read (`rs1` → `op_b`), the `op_c` column the sign-extended
immediate (`imm_c = 1`); feeds `advance_write_core` with `execute_ADDIW_reaches`. The per-chip inputs are the
fixed opcode `ADDW` (= 19, ADDIW shares it) and the `Spec`-derived write identity `hval`
(`rdWrite = execute_ADDIW_pure op_b op_c`). -/
theorem advance_of_addiw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.ADDW).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = execute_ADDIW_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesADDIW hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have himmbind : Word.toBitVec64 r.adapter.op_c = imm.signExtend 64 := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have hval' : Word.toBitVec64 r.rdWrite
      = execute_ADDIW_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) (imm.signExtend 64) := by
    rw [hval, himmbind]
  exact advance_write_core (instruction.ADDIW (imm, .Regidx rs1, .Regidx rd)) rd
    (execute_ADDIW_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value) (imm.signExtend 64))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_ADDIW_reaches imm rs1 rd (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval' hstraight hpc0 hwrites hnomem

/-- **The U-type chip `advance` — RowView-generic** (`UTypeChip`, LUI/AUIPC). No register reads (`imm_b =
imm_c = 1`); the write value is the immediate (LUI) or pc-relative (AUIPC), the latter reading the pc through
the shared core's **pc-frame** `hexec`. The chip supplies `hval` as a function of *the immediate its `op_b`
column encodes* — the decode (`decodesUType`) hands back that immediate (`op_b = bitVecToWord
((imm.signExtend 64) <<< 12)`), and the chip's `immOf`/`RV64.lui`/`RV64.auipc` facts discharge it. -/
theorem advance_of_utype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : uop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((uopToOpcode op).toNat : ZMod p))
    (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : ∀ imm : BitVec 20, r.adapter.op_b = bitVecToWord ((imm.signExtend 64) <<< 12) →
      Word.toBitVec64 r.rdWrite = execute_UTYPE_pure op (rcvPcOf (stateAccess r)) imm)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rd, hfetch, hdecw, hopa, hopb⟩ := decodesUType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have hval' := hval imm hopb
  exact advance_write_core (instruction.UTYPE (imm, .Regidx rd, op)) rd
    (execute_UTYPE_pure op (rcvPcOf (stateAccess r)) imm) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe hpcf _ => by
      have := execute_UTYPE_reaches imm rd op (rcvPcOf (stateAccess r)) t (hpcf.trans hpcread)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval' hstraight hpc0 hwrites hnomem

/-! ## Jumps (computed `next_pc`) — the `execute` sets `nextPC` itself -/

/-- **The JAL execute stage reaches `Retire_Success`.** `execute (.JAL …)` reads the staged `nextPC` (the
link `pc+4`), then `jump_to (pc + signExtend imm)` **overwrites** `nextPC` with the (4-aligned) target, then
writes the link `pc+4` to `rd`. Unlike the straight-line family, the execute *changes* `nextPC` — hence the
jump core below. -/
theorem execute_JAL_reaches (imm : BitVec 21) (rd_idx : BitVec 5) (pc : BitVec 64) (t : SailState)
    (hs : t.isInitialized)
    (hpc : t.regs.get? Register.PC = some pc)
    (hnpc : t.regs.get? Register.nextPC = some (pc + 4#64))
    (halign : (pc + sign_extend (m := 64) imm) % 4#64 = 0) :
    (execute (.JAL (imm, .Regidx rd_idx))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then
            {t with regs := t.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)}
          else
            {t with regs := ((t.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)).insert
              (reg_idx_to_Register rd_idx) (bitVecToRegidxVal rd_idx (pc + 4#64)))}) := by
  have hget_npc : t.regs.get Register.nextPC (hs _) = pc + 4#64 := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hnpc; exact hnpc
  have hget_pc : t.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hpc; exact hpc
  simp only [execute, execute_JAL, get_next_pc]
  rw [run_readReg_bind_of_isInitialized t Register.nextPC hs, hget_npc]
  rw [run_readReg_bind_of_isInitialized t Register.PC hs, hget_pc]
  rw [run_bind_of_run' t _ (jump_to (pc + sign_extend (m := 64) imm))
    (ExecutionResult.Retire_Success ()) (jump_to_of_mod4_eq_zero _ t hs halign)]
  simp only [run_bind_of_run' _ _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  split <;> simp_all

/-- **The jump ladder core** (analog of `advance_write_core`, for computed `next_pc`): the `execute` writes
`rd := link` **and** `nextPC := target`, so the row's committed send-pc is the target (`htgt : sndPcOf = target`)
rather than `pc+4`. Everything else — the minstret/fetch/decode/`try_step` ladder, and the register/ROM/config
frames off `{minstret, nextPC, rd}` — is the same as the straight-line core (an extra `nextPC` peel in the
`s''` frame). Serves the jump family (`JAL`; `JALR` reuses it). -/
theorem advance_jump_core {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (rd : BitVec 5) (target link pc : BitVec 64)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc)
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.regs.get? Register.nextPC = some (pc + 4#64) →
      t.isInitialized → SailConfigured t →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ())
        {t with regs := ((t.regs.insert Register.nextPC target).insert
          (reg_idx_to_Register rd) (bitVecToRegidxVal rd link))})
    (hrd_ne : rd ≠ 0#5) (hrd_a : (rd.toNat : ZMod p) = r.adapter.op_a)
    (hval : Word.toBitVec64 r.rdWrite = link)
    (htgt : sndPcOf (stateAccess r) = target)
    (hwrites : r.commit.writesReg = true)
    (hnomem : r.commit.memWrite = none) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hrdreg : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → R ≠ reg_idx_to_Register rd := by
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (unfold reg_idx_to_Register; split <;> decide)
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
    have h1 : s'.regs.get? Register.PC = some pc := by
      rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
    rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
    exact (Option.some.injEq _ _).mp h1
  have hnpc_sa : s_a.regs.get? Register.nextPC = some (pc + 4#64) := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert_self, hnpv_def, hgetPC]
    simp [BitVec.addInt]
  have hcfg_sa : SailConfigured s_a :=
    SailConfigured.congr (SailConfigured.writeMinstret cfg b) hinit_sa (fun R hR => by
      rw [hsa_def, Std.ExtDHashMap.get?_insert,
          dif_neg (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)])
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hnpc_sa hinit_sa hcfg_sa
  set s'' := ({s_a with regs := ((s_a.regs.insert Register.nextPC target).insert
    (reg_idx_to_Register rd) (bitVecToRegidxVal rd link))}) with hs''_def
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      R ≠ reg_idx_to_Register rd → s''.regs.get? R = s.regs.get? R := fun R h1 h2 h3 => by
    rw [hs''_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h3 (beq_iff_eq.mp hc).symm),
      Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)
      (hrdreg Register.hart_state (by tauto))]; exact cfg.active
  have hinit'' : SailState.isInitialized s'' := by
    rw [hs''_def]
    exact SailState.isInitialized_insert _ (SailState.isInitialized_insert s_a hinit_sa _ _) _ _
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s'' (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active'' hinit''
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (hrdreg R hR)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hs''_def, hsa_def, hs'_def]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun _ a => by rw [hmem_fin],
        fun mw hmw => absurd (hnomem.symm.trans hmw) (by simp)⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · rw [hPCf]
    have hnp : s''.regs.get? Register.nextPC = some target := by
      rw [hs''_def, Std.ExtDHashMap.get?_insert,
        dif_neg (by unfold reg_idx_to_Register; split <;> decide),
        Std.ExtDHashMap.get?_insert_self]
    rw [hnp, htgt]
  · -- regs (register-writing jump: `hwrites` → the link write + frame pair)
    rw [if_pos hwrites]
    refine ⟨?_, ?_⟩
    · intro idx hidx
      obtain rfl : idx = rd := (ofNat_val_eq_of_cast hidx).symm.trans (ofNat_val_eq_of_cast hrd_a)
      rw [hxf idx, hs''_def,
        get_reg?_writeBack {s_a with regs := s_a.regs.insert Register.nextPC target} idx hrd_ne _, ← hval]
    · intro idx hidx
      rw [hxf idx]
      by_cases h0 : idx = 0#5
      · subst h0; simp [SailState.get_reg?]
      · have hidxrd : idx ≠ rd := fun heq => hidx (by rw [heq]; exact hrd_a)
        have hframe_idx : s''.regs.get? (reg_idx_to_Register idx)
            = s.regs.get? (reg_idx_to_Register idx) :=
          hframe_s (reg_idx_to_Register idx) (Ne.symm (hmne idx)) (Ne.symm (hxne idx))
            (Ne.symm (reg_idx_to_Register_ne idx rd h0 hrd_ne hidxrd))
        simp only [SailState.get_reg?]
        rw [hframe_idx]
  · exact SailConfigured.congr cfg hinitf hcfg_frame

/-- **The JAL chip `advance` — RowView-generic.** Over `advance_jump_core`: `rd := pc+4` (the link, via the
pc-frame) and `nextPC := pc + signExtend imm` (the target, the row's committed `next_pc`). The per-chip inputs
are the target relation `hsnd` (the committed send-pc = pc + the decoded offset), the link `hlink`
(`rdWrite = pc+4`), and the 4-alignment `halign` — all from the chip `Spec`. -/
theorem advance_of_jal {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.JAL).toNat : ZMod p))
    (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (halign : (sndPcOf (stateAccess r)).toNat % 4 = 0)
    (hsnd : ∀ imm : BitVec 21, r.adapter.op_b = bitVecToWord (imm.signExtend 64) →
       sndPcOf (stateAccess r) = rcvPcOf (stateAccess r) + sign_extend (m := 64) imm)
    (hlink : Word.toBitVec64 r.rdWrite = rcvPcOf (stateAccess r) + 4#64)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rd, hfetch, hdecw, hopa, hopb, _⟩ := decodesJal hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have htgt : sndPcOf (stateAccess r) = rcvPcOf (stateAccess r) + sign_extend (m := 64) imm := hsnd imm hopb
  have halign' : (rcvPcOf (stateAccess r) + sign_extend (m := 64) imm) % 4#64 = 0 := by
    rw [← htgt]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using halign
  exact advance_jump_core (instruction.JAL (imm, .Regidx rd)) rd
    (rcvPcOf (stateAccess r) + sign_extend (m := 64) imm) (rcvPcOf (stateAccess r) + 4#64)
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t _hframe hpcf hnpc hinit _hcfg => by
      have reached := execute_JAL_reaches imm rd (rcvPcOf (stateAccess r)) t hinit
        (hpcf.trans hpcread) hnpc halign'
      rwa [if_neg hrd_ne] at reached)
    hrd_ne hopa'.symm hlink htgt hwrites hnomem

/-- **The JALR execute stage reaches `Retire_Success`.** Like `execute_JAL_reaches` but JALR (a) has an
`update_elp_state rs1` prefix (a no-op under `isValidMemConfig`), (b) reads `rs1` (not the pc), and (c)
jumps to the **LSB-cleared** target `(rs1_val + signExtend imm) &&& ~~~1` (`BitVec.update … 0 0#1`). -/
theorem execute_JALR_reaches (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (pc rs1_val : BitVec 64)
    (t : SailState) (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (hnpc : t.regs.get? Register.nextPC = some (pc + 4#64))
    (h_rs1 : SailState.get_reg? t rs1_idx = some rs1_val)
    (halign : (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1) % 4#64 = 0) :
    (execute (.JALR (imm, .Regidx rs1_idx, .Regidx rd_idx))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then
            {t with regs := (t.regs.insert Register.nextPC
              (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1))}
          else
            {t with regs := ((t.regs.insert Register.nextPC
              (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1)).insert
              (reg_idx_to_Register rd_idx) (bitVecToRegidxVal rd_idx (pc + 4#64)))}) := by
  have hget_npc : t.regs.get Register.nextPC (hs _) = pc + 4#64 := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hnpc; exact hnpc
  have hupd : (update_elp_state (.Regidx rs1_idx)).run t = .ok () t :=
    update_elp_state_of_isInitialized _ t hs hconfig
  simp only [execute, execute_JALR, get_next_pc_eq]
  rw [run_bind_of_run' t _ _ () hupd]
  rw [run_readReg_bind_of_isInitialized t Register.nextPC hs, hget_npc]
  rw [run_bind_of_run t _ rs1_val (by rw [run_rX_bits, h_rs1])]
  simp only [pure_bind]
  rw [run_bind_of_run' t _ _ (ExecutionResult.Retire_Success ())
    (jump_to_of_mod4_eq_zero _ t hs halign)]
  simp only [run_bind_of_run' _ _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  split <;> simp_all

/-- **The JALR chip `advance` — RowView-generic.** Over `advance_jump_core` (the config-threaded jump core),
reading `rs1` (→ `op_b`) via `ValueOperandsBound`: the target is the LSB-cleared `(rs1_val + signExtend imm)`
(the row's committed `next_pc`), the link `pc+4` written to `rd`. The per-chip inputs are `hsnd` (the LSB-clear
target relation), `hlink` (`rdWrite = pc+4`), and `halign`. -/
theorem advance_of_jalr {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.JALR).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (halign : (sndPcOf (stateAccess r)).toNat % 4 = 0)
    (hsnd : ∀ imm : BitVec 12, r.adapter.op_c = bitVecToWord (imm.signExtend 64) →
       sndPcOf (stateAccess r)
         = BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
             + sign_extend (m := 64) imm) 0 0#1)
    (hlink : Word.toBitVec64 r.rdWrite = rcvPcOf (stateAccess r) + 4#64)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesJalr hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have htgt : sndPcOf (stateAccess r)
      = BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
          + sign_extend (m := 64) imm) 0 0#1 := hsnd imm hopc
  have halign' : (BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + sign_extend (m := 64) imm) 0 0#1) % 4#64 = 0 := by
    rw [← htgt]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using halign
  exact advance_jump_core (instruction.JALR (imm, .Regidx rs1, .Regidx rd)) rd
    (BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value + sign_extend (m := 64) imm) 0 0#1)
    (rcvPcOf (stateAccess r) + 4#64) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hnpc hinit hcfgt => by
      have reached := execute_JALR_reaches imm rs1 rd (rcvPcOf (stateAccess r))
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t hinit
        hcfgt.toValidMemConfig hnpc ((hframe rs1).trans hrs1) halign'
      rwa [if_neg hrd_ne] at reached)
    hrd_ne hopa'.symm hlink htgt hwrites hnomem


/-! ## DivRem (DIV/REM/DIVW/REMW × signed/unsigned) execute-reaches + advance_of_* (SC Phase 4) -/

/-- The DIV/DIVU execute stage reaches `Retire_Success` (write value `SailRV64.div op_c op_b isU`).
The div-by-zero/overflow special cases are fully inside `SailRV64.div`; `div_eq` reduces
`execute_DIV` to `skeleton_binary` by `rfl`, so this mirrors `rtype_execute_reaches` exactly. -/
theorem execute_DIV_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.DIV (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.div op_c op_b isU)))}) := by
  simp only [execute, _root_.div_eq, skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The REM/REMU execute stage reaches `Retire_Success` (write value `SailRV64.rem isU op_c op_b`).
`execute_REM` has only bool-specialized named lemmas, so the reduction to `skeleton_binary` is an
inline `show … from rfl` (holds for a variable `isU` — the body threads `is_unsigned` as a value). -/
theorem execute_REM_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.REM (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.rem isU op_c op_b)))}) := by
  simp only [execute, show execute_REM (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) isU
    = skeleton_binary (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)
        (fun val1 val2 => SailRV64.rem isU val2 val1) from rfl, skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The DIVW/DIVUW execute stage reaches `Retire_Success` (write value `SailRV64.divw op_c op_b isU`). -/
theorem execute_DIVW_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.DIVW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.divw op_c op_b isU)))}) := by
  simp only [execute, _root_.divw_eq, skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The REMW/REMUW execute stage reaches `Retire_Success` (write value `SailRV64.remw isU op_c op_b`). -/
theorem execute_REMW_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.REMW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.remw isU op_c op_b)))}) := by
  simp only [execute, show execute_REMW (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) isU
    = skeleton_binary (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)
        (fun val1 val2 => SailRV64.remw isU val2 val1) from rfl, skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The MUL/MULH/MULHU/MULHSU execute stage reaches `Retire_Success` (write value
`SailRV64.mul op_c op_b op`).  Generic in `op : mul_op`; mirrors `execute_DIV_reaches`
via `_root_.mul_eq`/`skeleton_binary`. -/
theorem execute_MUL_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : mul_op)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.MUL (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.mul op_c op_b op)))}) := by
  simp only [execute, _root_.mul_eq, skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The MULW execute stage reaches `Retire_Success` (write value `SailRV64.mulw op_c op_b`).
Mirrors `execute_DIVW_reaches` via `_root_.mulw_eq`/`skeleton_binary`. -/
theorem execute_MULW_reaches (rs2_idx rs1_idx rd_idx : BitVec 5)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.MULW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.mulw op_c op_b)))}) := by
  simp only [execute, _root_.mulw_eq, skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The **register-writing** MUL-family chip `advance` (RowView-generic; mirrors `advance_of_div`).
**Move-2:** the `mul_op` is pinned by the canonicity guard `hcanon` (via `decodesMul`/`inv_mul'`), so this
covers all four canonical MUL ops — MUL/MULH/MULHU/MULHSU — writing `rd` the low/high product.  The
register-writing twin of the discarded-write `advance_of_alu_x0_mul`. -/
theorem advance_of_mul {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (op : mul_op) (hcanon : mulOpCanonical op = true)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((mulOpToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0) (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = SailRV64.mul (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_b_memory.prev_value) op)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesMul op hcanon hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) rd
    (SailRV64.mul (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_b_memory.prev_value) op) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_MUL_reaches rs2 rs1 rd op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- The **register-writing** MULW chip `advance` (RowView-generic; mirrors `advance_of_divw`).  No
`mul_op` — MULW is fixed by its own opcode; writes `rd` the 32→64 sign-extended low product. -/
theorem advance_of_mulw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.MULW).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0) (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = SailRV64.mulw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_b_memory.prev_value))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesMulw hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.MULW (.Regidx rs2, .Regidx rs1, .Regidx rd)) rd
    (SailRV64.mulw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_b_memory.prev_value)) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_MULW_reaches rs2 rs1 rd (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- The DIV/DIVU chip `advance` (RowView-generic; mirrors `advance_of_rtype`). -/
theorem advance_of_div {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0) (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = SailRV64.div (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_b_memory.prev_value) isU)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesDiv isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) rd
    (SailRV64.div (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_b_memory.prev_value) isU) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_DIV_reaches rs2 rs1 rd isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- The REM/REMU chip `advance` (RowView-generic; note the bool-first `SailRV64.rem isU op_c op_b`). -/
theorem advance_of_rem {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.REMU else Opcode.REM)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0) (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = SailRV64.rem isU (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_b_memory.prev_value))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesRem isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.REM (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) rd
    (SailRV64.rem isU (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_b_memory.prev_value)) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_REM_reaches rs2 rs1 rd isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- The DIVW/DIVUW chip `advance` (RowView-generic). -/
theorem advance_of_divw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0) (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = SailRV64.divw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_b_memory.prev_value) isU)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesDivw isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.DIVW (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) rd
    (SailRV64.divw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_b_memory.prev_value) isU) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_DIVW_reaches rs2 rs1 rd isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- The REMW/REMUW chip `advance` (RowView-generic; bool-first `SailRV64.remw isU op_c op_b`). -/
theorem advance_of_remw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0) (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hval : Word.toBitVec64 r.rdWrite
      = SailRV64.remw isU (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_b_memory.prev_value))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesRemw isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  exact advance_write_core (instruction.REMW (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) rd
    (SailRV64.remw isU (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
      (Word.toBitVec64 r.adapter.op_b_memory.prev_value)) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ => by
      have := execute_REMW_reaches rs2 rs1 rd isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-! ## Control-flow (branches): computed next_pc, NO register write (SC Phase 4 · Phase 3a) -/

/-- The Sail-computed branch-taken predicate for a `bop`, keyed exactly on `execute_BTYPE`'s inner
`match op` (BEQ/BNE via `==`/`!=`, the four ordering forms via the Sail `zopz0z*` comparison fns).
Self-contained (no `BranchSail.branchCond` dependency) so `execute_BTYPE_reaches` sits in `Advance.lean`,
below the BranchChip bridge. The BranchChip adapter bridges `btypeTaken ↔ branchCond` via the
`zopz0z*_eq_slt/ult` lemmas. -/
def btypeTaken (op : bop) (x y : BitVec 64) : Bool :=
  match op with
  | .BEQ => x == y
  | .BNE => x != y
  | .BLT => zopz0zI_s x y
  | .BGE => zopz0zKzJ_s x y
  | .BLTU => zopz0zI_u x y
  | .BGEU => zopz0zKzJ_u x y

/-- **The BTYPE execute stage reaches `Retire_Success`.** On a state `t` whose `rs1`/`rs2` reads and
staged `nextPC = pc + 4` are known, `execute (.BTYPE …)` runs to `Retire_Success` committing
`nextPC := target` (only): the **taken** arm's `jump_to` overwrites `nextPC ← target = pc + signExtend imm`
(4-aligned via `jump_to_of_mod4_eq_zero`); the **not-taken** arm leaves the staged `pc+4` untouched, so the
result equals `{t with regs.insert nextPC target}` (target = pc+4) by the idempotent re-insert of the already
staged `nextPC`. The `hexec` the control-flow core (`advance_of_ctrl`) needs — the branch twin of the
straight-line `*_execute_reaches`, but the execute *changes* `nextPC` (no `rd` write). -/
theorem execute_BTYPE_reaches (imm : BitVec 13) (rs1_idx rs2_idx : BitVec 5) (op : bop)
    (pc target rs1_val rs2_val : BitVec 64) (t : SailState) (hs : t.isInitialized)
    (hpc : t.regs.get? Register.PC = some pc)
    (hnpc : t.regs.get? Register.nextPC = some (pc + 4#64))
    (h_rs1 : SailState.get_reg? t rs1_idx = some rs1_val)
    (h_rs2 : SailState.get_reg? t rs2_idx = some rs2_val)
    (h_taken : btypeTaken op rs1_val rs2_val = true → target = pc + sign_extend (m := 64) imm)
    (h_not_taken : btypeTaken op rs1_val rs2_val = false → target = pc + 4#64)
    (h_align : target.toNat % 4 = 0) :
    (execute (.BTYPE (imm, .Regidx rs2_idx, .Regidx rs1_idx, op))).run t
      = .ok (ExecutionResult.Retire_Success ())
          {t with regs := t.regs.insert Register.nextPC target} := by
  have hpc_get : t.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hpc; exact hpc
  by_cases hc : btypeTaken op rs1_val rs2_val = true
  · have hnpc_t := h_taken hc
    have htgt4 : (pc + sign_extend (m := 64) imm) % 4#64 = 0 := by
      rw [← hnpc_t]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using h_align
    have hjump := jump_to_of_mod4_eq_zero (pc + sign_extend (m := 64) imm) t hs htgt4
    cases op <;> simp only [btypeTaken, beq_iff_eq, bne_iff_ne] at hc <;>
      simp [execute, execute_BTYPE, run_rX_bits, h_rs1, h_rs2,
        Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get, RETIRE_SUCCESS, hjump, hnpc_t, hc]
  · simp only [Bool.not_eq_true] at hc
    have hnt := h_not_taken hc
    have hgtnpc : t.regs.get? Register.nextPC = some target := by rw [hnpc, hnt]
    have hidem : t.regs.insert Register.nextPC target = t.regs := by
      apply Std.ExtDHashMap.ext_get?; intro k; rw [Std.ExtDHashMap.get?_insert]
      split
      · rename_i hk; simp only [beq_iff_eq] at hk; subst hk; rw [hgtnpc]; rfl
      · rfl
    cases op <;> simp only [btypeTaken, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hc <;>
      simp [execute, execute_BTYPE, run_rX_bits, h_rs1, h_rs2, RETIRE_SUCCESS, hc, hidem]

/-- **The control-flow (branch) ladder core** — the twin of `advance_jump_core` for a **computed
`next_pc` with NO register write**. The `execute` commits `nextPC := target` only (no `rd` insert), the row
takes `commit.writesReg = false`, and `RowEffect.regs` discharges via the `if_neg` (frame-only) branch — a
uniform register frame over ALL indices (no `op_a` split). Everything else — the minstret/fetch/decode/
`try_step` ladder and the register/ROM/config frames off `{minstret, nextPC}` — mirrors the straight-line/
jump cores. Serves the branch family (`BTYPE`); the per-chip `hexec` is `execute_BTYPE_reaches`, the target
is the committed `next_pc` (`htgt : sndPcOf = target`). -/
theorem advance_of_ctrl {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (target pc : BitVec 64)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc)
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.regs.get? Register.nextPC = some (pc + 4#64) →
      t.isInitialized → SailConfigured t →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ())
        {t with regs := t.regs.insert Register.nextPC target})
    (htgt : sndPcOf (stateAccess r) = target)
    (hnowrite : r.commit.writesReg = false)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
    have h1 : s'.regs.get? Register.PC = some pc := by
      rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
    rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
    exact (Option.some.injEq _ _).mp h1
  have hnpc_sa : s_a.regs.get? Register.nextPC = some (pc + 4#64) := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert_self, hnpv_def, hgetPC]; simp [BitVec.addInt]
  have hcfg_sa : SailConfigured s_a :=
    SailConfigured.congr (SailConfigured.writeMinstret cfg b) hinit_sa (fun R hR => by
      rw [hsa_def, Std.ExtDHashMap.get?_insert,
          dif_neg (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)])
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hnpc_sa hinit_sa hcfg_sa
  set s'' := ({s_a with regs := s_a.regs.insert Register.nextPC target}) with hs''_def
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      s''.regs.get? R = s.regs.get? R := fun R h1 h2 => by
    rw [hs''_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)]; exact cfg.active
  have hinit'' : SailState.isInitialized s'' := by
    rw [hs''_def]; exact SailState.isInitialized_insert s_a hinit_sa _ _
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s'' (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active'' hinit''
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hs''_def, hsa_def, hs'_def]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun _ a => by rw [hmem_fin],
        fun mw hmw => absurd (hnomem.symm.trans hmw) (by simp)⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · rw [hPCf]
    have hnp : s''.regs.get? Register.nextPC = some target := by
      rw [hs''_def, Std.ExtDHashMap.get?_insert_self]
    rw [hnp, htgt]
  · rw [if_neg (by rw [hnowrite]; decide)]
    intro idx
    rw [hxf idx, hs''_def, SailState.get_reg?_insert_of_ne (hxne idx)]
    exact hframe_sa idx
  · exact SailConfigured.congr cfg hinitf hcfg_frame

/-! ### Jump-to-x0 adapters

JAL and JALR share their Rust tables between ordinary destination writes and `rd = x0`.
The latter still computes and commits the target PC, but Sail discards the link write.  These two
adapters reuse the branch ladder's computed-PC/no-register-write core rather than duplicating it. -/

/-- **JAL into x0.** The decoded destination is forced to `x0` by `op_a = 0`; only the computed
`nextPC` is architecturally committed. -/
theorem advance_of_jal_x0 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.JAL).toNat : ZMod p))
    (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (halign : (sndPcOf (stateAccess r)).toNat % 4 = 0)
    (hsnd : ∀ imm : BitVec 21, r.adapter.op_b = bitVecToWord (imm.signExtend 64) →
      sndPcOf (stateAccess r) = rcvPcOf (stateAccess r) + sign_extend (m := 64) imm)
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rd, hfetch, hdecw, hopa, hopb, _hopc⟩ := decodesJal hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by
      rw [← hopa', hopa0]
      simp
    exact regidx_bv_inj hh
  subst hrd0
  have htgt : sndPcOf (stateAccess r) =
      rcvPcOf (stateAccess r) + sign_extend (m := 64) imm := hsnd imm hopb
  have halign' : (rcvPcOf (stateAccess r) + sign_extend (m := 64) imm) % 4#64 = 0 := by
    rw [← htgt]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod]
    simpa using halign
  exact advance_of_ctrl (instruction.JAL (imm, .Regidx 0#5))
    (rcvPcOf (stateAccess r) + sign_extend (m := 64) imm) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t _hframe hpcf hnpc hinit _hcfg => by
      have reached := execute_JAL_reaches imm 0#5 (rcvPcOf (stateAccess r)) t hinit
        (hpcf.trans hpcread) hnpc halign'
      rwa [if_pos rfl] at reached)
    htgt hnowrite hnomem

/-- **JALR into x0.** The source register still comes from the grounded `op_b` pull; the link is
discarded and only the LSB-cleared target PC is committed. -/
theorem advance_of_jalr_x0 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.JALR).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (halign : (sndPcOf (stateAccess r)).toNat % 4 = 0)
    (hsnd : ∀ imm : BitVec 12, r.adapter.op_c = bitVecToWord (imm.signExtend 64) →
      sndPcOf (stateAccess r) =
        BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
          + sign_extend (m := 64) imm) 0 0#1)
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesJalr hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]
    rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by
      rw [← hopa', hopa0]
      simp
    exact regidx_bv_inj hh
  subst hrd0
  have htgt : sndPcOf (stateAccess r) =
      BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + sign_extend (m := 64) imm) 0 0#1 := hsnd imm hopc
  have halign' : (BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + sign_extend (m := 64) imm) 0 0#1) % 4#64 = 0 := by
    rw [← htgt]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod]
    simpa using halign
  exact advance_of_ctrl (instruction.JALR (imm, .Regidx rs1, .Regidx 0#5))
    (BitVec.update (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + sign_extend (m := 64) imm) 0 0#1)
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hnpc hinit hcfgt => by
      have reached := execute_JALR_reaches imm rs1 0#5 (rcvPcOf (stateAccess r))
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t hinit
        hcfgt.toValidMemConfig hnpc ((hframe rs1).trans hrs1) halign'
      rwa [if_pos rfl] at reached)
    htgt hnowrite hnomem

/-! ## Loads: `execute_LOAD` reads memory; the register write is sourced from `RefinesAt.mem` (Phase 3b.2) -/

/-- **The width-1 `execute_LOAD` reaches `Retire_Success`.** From the quiescent memory config, the `rs1`
read (`reg_val`), the address bounds, and the single memory byte `data₀` at `reg_val + signExtend imm`,
`execute (.LOAD …)` (width 1) runs to `Retire_Success` writing only `rd` with `extend_value is_unsigned
data₀`. The load twin of `itype_execute_reaches`, built from `SailMem.run_vmem_read_of_width_1'`. The one
lemma that consumes the row's memory-read binding (`RefinesAt.mem` downstream). -/
theorem execute_LOAD_reaches_width1 (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (is_unsigned : Bool)
    (reg_val : BitVec 64) (data₀ : BitVec 8) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some reg_val)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀) :
    (execute (.LOAD (imm, .Regidx rs1_idx, .Regidx rd_idx, is_unsigned, 1))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then t
           else {t with regs := (t.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (extend_value is_unsigned data₀)))}) := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 1 = true := by
    rw [is_aligned_vaddr_iff_mod]; omega
  have h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 1 (by omega) h_lo h_hi
  have hread := run_vmem_read_of_width_1' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ t hs h_rs1 h_align' hconfig h_in_range hmem₀
  simp only at hread
  simp only [execute, execute_LOAD, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert]
  simp only [Int.toNat_one, Nat.reduceLeDiff, decide_true, if_true, pure_bind]
  rw [run_bind_of_run t _ _ hread]
  rw [run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **The load register-writing core.** The `advance_write_core` twin whose `hexec` additionally receives
the **memory frame** `t.mem = s.mem` and `SailConfigured t` — so a load's `execute_LOAD` (which reads
`t.mem`) can be discharged. Straight-line (`nextPC = pc+4`), writes only `rd`; identical ladder + five-clause
`RowEffect` read-off to `advance_write_core`. The two changes vs. `advance_write_core`: `hexec`'s antecedents
(`t.mem = s.mem`, `SailConfigured t`) and the `hmem_sa`/`hcfg_sa` haves feeding `hexec s_a …`. -/
theorem advance_load_core {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (rd : BitVec 5) (value : BitVec 64) (pc : BitVec 64)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc) (hrcv : pc = rcvPcOf (stateAccess r))
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.mem = s.mem →
      t.isInitialized → SailConfigured t →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ())
        {t with regs := t.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value)})
    (hrd_ne : rd ≠ 0#5) (hrd_a : (rd.toNat : ZMod p) = r.adapter.op_a)
    (hval : Word.toBitVec64 r.rdWrite = value)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hwrites : r.commit.writesReg = true)
    (hnomem : r.commit.memWrite = none) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hrdreg : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → R ≠ reg_idx_to_Register rd := by
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (unfold reg_idx_to_Register; split <;> decide)
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hmem_sa : s_a.mem = s.mem := by rw [hsa_def, hs'_def]
  have hcfg_sa : SailConfigured s_a :=
    SailConfigured.congr (SailConfigured.writeMinstret cfg b) hinit_sa (fun R hR => by
      rw [hsa_def, Std.ExtDHashMap.get?_insert,
          dif_neg (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)])
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hmem_sa hinit_sa hcfg_sa
  set s'' := ({s_a with regs := s_a.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value)})
    with hs''_def
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      R ≠ reg_idx_to_Register rd → s''.regs.get? R = s.regs.get? R := fun R h1 h2 h3 => by
    rw [hs''_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h3 (beq_iff_eq.mp hc).symm),
      hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)
      (hrdreg Register.hart_state (by tauto))]; exact cfg.active
  have hinit'' : SailState.isInitialized s'' := by
    rw [hs''_def]; exact SailState.isInitialized_insert s_a hinit_sa _ _
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s'' (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active'' hinit''
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (hrdreg R hR)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hs''_def, hsa_def, hs'_def]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun _ a => by rw [hmem_fin],
        fun mw hmw => absurd (hnomem.symm.trans hmw) (by simp)⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · rw [hPCf]
    have hnp : s''.regs.get? Register.nextPC = some npv := by
      rw [hs''_def, Std.ExtDHashMap.get?_insert,
        dif_neg (by unfold reg_idx_to_Register; split <;> decide), hsa_def,
        Std.ExtDHashMap.get?_insert_self]
    have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
      have h1 : s'.regs.get? Register.PC = some pc := by
        rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
      rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
      exact (Option.some.injEq _ _).mp h1
    rw [hnp]; congr 1
    rw [hnpv_def, hgetPC, sndPc_straightline r hstraight hpc0, ← hrcv]
    simp [BitVec.addInt]
  · rw [if_pos hwrites]
    refine ⟨?_, ?_⟩
    · intro idx hidx
      obtain rfl : idx = rd := (ofNat_val_eq_of_cast hidx).symm.trans (ofNat_val_eq_of_cast hrd_a)
      rw [hxf idx, hs''_def, get_reg?_writeBack s_a idx hrd_ne _, ← hval]
    · intro idx hidx
      rw [hxf idx]
      by_cases h0 : idx = 0#5
      · subst h0; simp [SailState.get_reg?]
      · have hidxrd : idx ≠ rd := fun heq => hidx (by rw [heq]; exact hrd_a)
        rw [hs''_def, SailState.get_reg?_insert_of_ne (reg_idx_to_Register_ne idx rd h0 hrd_ne hidxrd),
          hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
          SailState.get_reg?_insert_of_ne (hmne idx)]
  · exact SailConfigured.congr cfg hinitf hcfg_frame

/-- **The width-1 load chip `advance`** (RowView-generic, one call per width-1 load variant). Over
`advance_load_core` + `execute_LOAD_reaches_width1`: straight-line, one `rs1` register read (→ `op_b` via
`ValueOperandsBound`), `op_c` the sign-extended offset. The load's non-standard precondition — the memory
byte at `reg_val + signExtend imm` — enters as `hmem` (in RowView-column form). The per-variant inputs are
`isU`, the read `byte`, the memory binding, and the extend identity `hval`. -/
theorem advance_of_load_width1 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (isU : Bool) (byte : BitVec 8)
    (hpin : ∀ (w' : word_width) (u' : Bool),
      (loadOpcode w' u').toNat = (loadOpcode 1 isU).toNat → w' = 1 ∧ u' = isU)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 1 isU).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte)
    (hval : Word.toBitVec64 r.rdWrite = extend_value isU byte)
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesLoad 1 isU hpin hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte := by rw [← himmbind]; exact hmem
  exact advance_load_core (instruction.LOAD (imm, .Regidx rs1, .Regidx rd, isU, 1)) rd
    (extend_value isU byte) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width1 imm rs1 rd isU
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_hi' h_lo' (by rw [hmemf]; exact hmem')
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-! ## Stores: `execute_STORE` writes memory (the first `commit.memWrite = some` chip) (Phase 3b.3) -/

/-- **The STORE execute stage reaches `Retire_Success`** (width 1). `execute (.STORE …)` on a
state `t` whose `rs1` (base) / `rs2` (value source) reads are known, and whose store address is
1-aligned / fits / in the SP1 PMA window, runs to `Retire_Success` writing ONLY memory: the low
byte of `rs2` (`extractLsb rs2_val 7 0`) at the byte address `(rs1_val + signExtend imm).toNat`,
leaving every register (incl. the staged `nextPC = pc+4`) untouched. The store `hexec` the ladder
needs — the memory twin of the register-writing `*_execute_reaches`. Reduces via
`SailMem.run_vmem_write_of_width_1` (the width-1 fold already collapses `writeBytes` to a single
`mem.insert`, so no general fold lemma is needed for width 1). -/
theorem execute_STORE_reaches (imm : BitVec 12) (rs1_idx rs2_idx : BitVec 5)
    (rs1_val rs2_val : BitVec 64) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some rs1_val) (h_rs2 : t.get_reg? rs2_idx = some rs2_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + sign_extend (m := 64) imm)) 1 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (rs1_val + sign_extend (m := 64) imm) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (execute (.STORE (imm, .Regidx rs2_idx, .Regidx rs1_idx, 1))).run t
      = .ok (ExecutionResult.Retire_Success ())
          { t with mem := t.mem.insert (rs1_val + sign_extend (m := 64) imm).toNat (Sail.BitVec.extractLsb rs2_val 7 0) } := by
  have hwrite := run_vmem_write_of_width_1 rs1_idx rs1_val (sign_extend (m := 64) imm)
    (Sail.BitVec.extractLsb rs2_val 7 0) t hs h_rs1 h_aligned hconfig h_in_range
  simp only [execute]
  simp [execute_STORE, LeanRV64D.Functions.xlen_bytes, PreSail.assert, h_rs2, hwrite,
    RETIRE_SUCCESS]

/-- **The width-2 `execute_STORE` reaches `Retire_Success`** (SH). The `execute_STORE_reaches` (width 1)
twin: additionally requires 2-byte ALIGNMENT, and writes the low half `rs2[15:0]` as two little-endian
bytes at `[addr, addr+1]`, leaving every register (incl. the staged `nextPC = pc+4`) untouched. Reduces
via `SailMem.run_vmem_write_of_width_2` (whose 2-deep `mem.insert` fold this exposes verbatim). -/
theorem execute_STORE_reaches_width2 (imm : BitVec 12) (rs1_idx rs2_idx : BitVec 5)
    (rs1_val rs2_val : BitVec 64) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some rs1_val) (h_rs2 : t.get_reg? rs2_idx = some rs2_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + sign_extend (m := 64) imm)) 2 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (rs1_val + sign_extend (m := 64) imm) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (execute (.STORE (imm, .Regidx rs2_idx, .Regidx rs1_idx, 2))).run t
      = .ok (ExecutionResult.Retire_Success ())
          { t with mem := ((t.mem.insert (rs1_val + sign_extend (m := 64) imm).toNat
              (BitVec.ofNat 8 (Sail.BitVec.extractLsb rs2_val 15 0).toNat)).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 1)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb rs2_val 15 0).toNat >>> 8))) } := by
  have hwrite := run_vmem_write_of_width_2 rs1_idx rs1_val (sign_extend (m := 64) imm)
    (Sail.BitVec.extractLsb rs2_val 15 0) t hs h_rs1 h_aligned hconfig h_in_range
  simp only [execute]
  simp [execute_STORE, LeanRV64D.Functions.xlen_bytes, PreSail.assert, h_rs2, hwrite,
    RETIRE_SUCCESS]

/-- **The width-4 `execute_STORE` reaches `Retire_Success`** (SW). The 4-byte (word) twin: requires
4-byte ALIGNMENT, writes `rs2[31:0]` as four little-endian bytes at `[addr … addr+3]`, leaving every
register untouched. Reduces via `SailMem.run_vmem_write_of_width_4` (4-deep `mem.insert` fold). -/
theorem execute_STORE_reaches_width4 (imm : BitVec 12) (rs1_idx rs2_idx : BitVec 5)
    (rs1_val rs2_val : BitVec 64) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some rs1_val) (h_rs2 : t.get_reg? rs2_idx = some rs2_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + sign_extend (m := 64) imm)) 4 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (rs1_val + sign_extend (m := 64) imm) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (execute (.STORE (imm, .Regidx rs2_idx, .Regidx rs1_idx, 4))).run t
      = .ok (ExecutionResult.Retire_Success ())
          { t with mem := ((((t.mem.insert (rs1_val + sign_extend (m := 64) imm).toNat
              (BitVec.ofNat 8 (Sail.BitVec.extractLsb rs2_val 31 0).toNat)).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 1)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb rs2_val 31 0).toNat >>> 8))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 2)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb rs2_val 31 0).toNat >>> 16))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 3)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb rs2_val 31 0).toNat >>> 24))) } := by
  have hwrite := run_vmem_write_of_width_4 rs1_idx rs1_val (sign_extend (m := 64) imm)
    (Sail.BitVec.extractLsb rs2_val 31 0) t hs h_rs1 h_aligned hconfig h_in_range
  simp only [execute]
  simp [execute_STORE, LeanRV64D.Functions.xlen_bytes, PreSail.assert, h_rs2, hwrite,
    RETIRE_SUCCESS]

/-- **The width-8 `execute_STORE` reaches `Retire_Success`** (SD). The 8-byte (double-word) twin:
requires 8-byte ALIGNMENT, writes the full 64-bit `rs2` as eight little-endian bytes at
`[addr … addr+7]`, leaving every register untouched. Reduces via `SailMem.run_vmem_write_of_width_8`
(8-deep `mem.insert` fold); the `extractLsb rs2 63 0` collapses to `rs2` (`hext`). -/
theorem execute_STORE_reaches_width8 (imm : BitVec 12) (rs1_idx rs2_idx : BitVec 5)
    (rs1_val rs2_val : BitVec 64) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some rs1_val) (h_rs2 : t.get_reg? rs2_idx = some rs2_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + sign_extend (m := 64) imm)) 8 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (rs1_val + sign_extend (m := 64) imm) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (execute (.STORE (imm, .Regidx rs2_idx, .Regidx rs1_idx, 8))).run t
      = .ok (ExecutionResult.Retire_Success ())
          { t with mem := ((((((((t.mem.insert (rs1_val + sign_extend (m := 64) imm).toNat
              (BitVec.ofNat 8 rs2_val.toNat)).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 1)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 8))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 2)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 16))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 3)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 24))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 4)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 32))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 5)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 40))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 6)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 48))).insert
              ((rs1_val + sign_extend (m := 64) imm).toNat + 7)
              (BitVec.ofNat 8 (rs2_val.toNat >>> 56))) } := by
  have hwrite := run_vmem_write_of_width_8 rs1_idx rs1_val (sign_extend (m := 64) imm)
    rs2_val t hs h_rs1 h_aligned hconfig h_in_range
  have hext : Sail.BitVec.extractLsb rs2_val 63 0 = rs2_val := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  simp only [execute]
  simp [execute_STORE, LeanRV64D.Functions.xlen_bytes, PreSail.assert, h_rs2, hext, hwrite,
    RETIRE_SUCCESS]

/-- **The store ladder core** — straight-line PC (`pc+4`), NO register write, ONE contiguous memory
write (SC Phase 4 · Phase 3b.3; the FIRST chip with `commit.memWrite = some`). A hybrid of
`advance_write_core` (straight-line pc via `sndPc_straightline`, since the store leaves the staged
`nextPC = pc+4`) and `advance_of_ctrl` (`commit.writesReg = false`, so `RowEffect.regs` is a pure
frame via the `if_neg` branch), plus the new `RowEffect.mem` `some mw` branch. The execute writes
only memory (`{t with mem := writeMem t.mem}`); the byte-range readoff is supplied by `hcov`/`hncov`
(so this is WIDTH-AGNOSTIC — instantiate `writeMem`/`hcov`/`hncov` per width). Reuses the landed
`sailStep_of_ladder` + `tail_effect` unchanged (already mem-aware: `s_final.mem = s''.mem`).

SP1's immutable Program-table fetch is not identified here with Sail's mutable instruction bytes:
ROM preservation is composed once at the execution boundary through `SailCodeMemoryCompatible`,
rather than repeated as a store-chip precondition. (This theorem now elaborates at the default
heartbeat budget; the file-scope 4000000-heartbeat ceiling it used to inherit was retired once its
sole owner, `get_reg?_writeBack`, was driven to closure.) -/
theorem advance_of_store {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (pc : BitVec 64) (mw : Trace.MemWrite (ZMod p))
    (writeMem : Std.ExtHashMap Nat (BitVec 8) → Std.ExtHashMap Nat (BitVec 8))
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc) (hrcv : pc = rcvPcOf (stateAccess r))
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.isInitialized → SailConfigured t →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ())
        {t with mem := writeMem t.mem})
    (hcov : ∀ a : ℕ, mw.covers a → (writeMem s.mem).get? a = some (mw.byteAt a))
    (hncov : ∀ a : ℕ, ¬ mw.covers a → (writeMem s.mem).get? a = s.mem.get? a)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hnowrite : r.commit.writesReg = false)
    (hmw : r.commit.memWrite = some mw) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
    have h1 : s'.regs.get? Register.PC = some pc := by
      rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
    rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
    exact (Option.some.injEq _ _).mp h1
  have hnpc_sa : s_a.regs.get? Register.nextPC = some (pc + 4#64) := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert_self, hnpv_def, hgetPC]; simp [BitVec.addInt]
  have hcfg_sa : SailConfigured s_a :=
    SailConfigured.congr (SailConfigured.writeMinstret cfg b) hinit_sa (fun R hR => by
      rw [hsa_def, Std.ExtDHashMap.get?_insert,
          dif_neg (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)])
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hinit_sa hcfg_sa
  set s'' := ({s_a with mem := writeMem s_a.mem}) with hs''_def
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      s''.regs.get? R = s.regs.get? R := fun R h1 h2 => by
    rw [hs''_def]
    show s_a.regs.get? R = s.regs.get? R
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)]; exact cfg.active
  have hinit'' : SailState.isInitialized s'' := by
    rw [hs''_def]; exact hinit_sa
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s'' (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active'' hinit''
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
  have hmem_fin : s_final.mem = writeMem s.mem := by rw [hmemf, hs''_def]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun hnone _ => absurd (hmw.symm.trans hnone) (by simp),
              fun mw' hmw' => ?_⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · rw [hPCf]
    have hnp : s''.regs.get? Register.nextPC = some (pc + 4#64) := hnpc_sa
    rw [hnp]; congr 1
    rw [sndPc_straightline r hstraight hpc0, ← hrcv]
  · rw [if_neg (by rw [hnowrite]; decide)]
    intro idx
    rw [hxf idx, hs''_def]
    show SailState.get_reg? s_a idx = SailState.get_reg? s idx
    exact hframe_sa idx
  · obtain rfl : mw' = mw := by rw [hmw] at hmw'; exact (Option.some.injEq _ _).mp hmw'.symm
    refine ⟨fun a hcova => ?_, fun a hncova => ?_⟩
    · rw [hmem_fin]; exact hcov a hcova
    · rw [hmem_fin]; exact hncov a hncova
  · exact SailConfigured.congr cfg hinitf hcfg_frame

/-! ## Loads width 2/4 (LoadHalf/LoadWord) — Phase 3b.2 -/

/-- **The width-2 `execute_LOAD` reaches `Retire_Success`.** The `execute_LOAD_reaches_width1`
twin for a 2-byte (half-word) read: additionally requires 2-byte ALIGNMENT
(`(reg_val + signExtend imm) % 2 = 0`), and the loaded value is the little-endian half
`data₁ ++ data₀`. Built from `SailMem.run_vmem_read_of_width_2'`. -/
theorem execute_LOAD_reaches_width2 (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (is_unsigned : Bool)
    (reg_val : BitVec 64) (data₀ data₁ : BitVec 8) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 2 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁) :
    (execute (.LOAD (imm, .Regidx rs1_idx, .Regidx rd_idx, is_unsigned, 2))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then t
           else {t with regs := (t.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (extend_value is_unsigned (data₁ ++ data₀))))}) := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 2 = true := by
    rw [is_aligned_vaddr_iff_mod]; exact h_aligned
  have h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 2 (by omega) h_lo h_hi
  have hread := run_vmem_read_of_width_2' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ t hs h_rs1 h_align' hconfig h_in_range hmem₀ hmem₁
  simp only at hread
  simp only [execute, execute_LOAD, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert]
  rw [show Int.toNat 2 = 2 from rfl]
  simp only [Nat.reduceLeDiff, decide_true, if_true, pure_bind]
  rw [run_bind_of_run t _ _ hread]
  rw [run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **The width-2 load chip `advance`** (RowView-generic, one call per width-2 load variant).
The `advance_of_load_width1` twin over `advance_load_core` + `execute_LOAD_reaches_width2`.
Differs from width 1 by the 2-byte ALIGNMENT precondition `h_aligned` and the second read
byte `byte₁` (so the read value is the half `byte₁ ++ byte₀`). -/
theorem advance_of_load_width2 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (isU : Bool) (byte₀ byte₁ : BitVec 8)
    (hpin : ∀ (w' : word_width) (u' : Bool),
      (loadOpcode w' u').toNat = (loadOpcode 2 isU).toNat → w' = 2 ∧ u' = isU)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 2 isU).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_aligned : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat % 2 = 0)
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem₀ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte₀)
    (hmem₁ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1]? = some byte₁)
    (hval : Word.toBitVec64 r.rdWrite = extend_value isU (byte₁ ++ byte₀))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesLoad 2 isU hpin hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_aligned' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat % 2 = 0 := by rw [← himmbind]; exact h_aligned
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem₀' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte₀ := by rw [← himmbind]; exact hmem₀
  have hmem₁' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1]? = some byte₁ := by rw [← himmbind]; exact hmem₁
  exact advance_load_core (instruction.LOAD (imm, .Regidx rs1, .Regidx rd, isU, 2)) rd
    (extend_value isU (byte₁ ++ byte₀)) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width2 imm rs1 rd isU
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte₀ byte₁ t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_aligned' h_hi' h_lo'
        (by rw [hmemf]; exact hmem₀') (by rw [hmemf]; exact hmem₁')
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- **The width-4 `execute_LOAD` reaches `Retire_Success`.** The 4-byte (word) read twin:
requires 4-byte ALIGNMENT, loads the little-endian word `data₃ ++ data₂ ++ data₁ ++ data₀`.
Built from `SailMem.run_vmem_read_of_width_4'`. -/
theorem execute_LOAD_reaches_width4 (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (is_unsigned : Bool)
    (reg_val : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 4 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃) :
    (execute (.LOAD (imm, .Regidx rs1_idx, .Regidx rd_idx, is_unsigned, 4))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then t
           else {t with regs := (t.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (extend_value is_unsigned (data₃ ++ data₂ ++ data₁ ++ data₀))))}) := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 4 = true := by
    rw [is_aligned_vaddr_iff_mod]; exact h_aligned
  have h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 4 (by omega) h_lo h_hi
  have hread := run_vmem_read_of_width_4' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ data₂ data₃ t hs h_rs1 h_align' hconfig h_in_range hmem₀ hmem₁ hmem₂ hmem₃
  simp only at hread
  simp only [execute, execute_LOAD, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert]
  rw [show Int.toNat 4 = 4 from rfl]
  simp only [Nat.reduceLeDiff, decide_true, if_true, pure_bind]
  rw [run_bind_of_run t _ _ hread]
  rw [run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **The width-8 `execute_LOAD` reaches `Retire_Success`.** The 8-byte (double-word) read twin:
requires 8-byte ALIGNMENT, loads the little-endian word `data₇ ++ … ++ data₀`.
Built from `SailMem.run_vmem_read_of_width_8'`. -/
theorem execute_LOAD_reaches_width8 (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (is_unsigned : Bool)
    (reg_val : BitVec 64) (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8) (t : SailState)
    (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (h_rs1 : t.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 8 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃)
    (hmem₄ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 4]? = some data₄)
    (hmem₅ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 5]? = some data₅)
    (hmem₆ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 6]? = some data₆)
    (hmem₇ : t.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 7]? = some data₇) :
    (execute (.LOAD (imm, .Regidx rs1_idx, .Regidx rd_idx, is_unsigned, 8))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then t
           else {t with regs := (t.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (extend_value is_unsigned
               (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀))))}) := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 8 = true := by
    rw [is_aligned_vaddr_iff_mod]; exact h_aligned
  have h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 8 (by omega) h_lo h_hi
  have hread := run_vmem_read_of_width_8' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ t hs h_rs1 h_align' hconfig h_in_range
    hmem₀ hmem₁ hmem₂ hmem₃ hmem₄ hmem₅ hmem₆ hmem₇
  simp only at hread
  simp only [execute, execute_LOAD, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert]
  rw [show Int.toNat 8 = 8 from rfl]
  simp only [Nat.reduceLeDiff, decide_true, if_true, pure_bind]
  rw [run_bind_of_run t _ _ hread]
  rw [run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **The width-4 load chip `advance`.** The `advance_of_load_width2` twin: 4-byte alignment
+ four read bytes → the word `byte₃ ++ byte₂ ++ byte₁ ++ byte₀`. -/
theorem advance_of_load_width4 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (isU : Bool) (byte₀ byte₁ byte₂ byte₃ : BitVec 8)
    (hpin : ∀ (w' : word_width) (u' : Bool),
      (loadOpcode w' u').toNat = (loadOpcode 4 isU).toNat → w' = 4 ∧ u' = isU)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 4 isU).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_aligned : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat % 4 = 0)
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem₀ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte₀)
    (hmem₁ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1]? = some byte₁)
    (hmem₂ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 2]? = some byte₂)
    (hmem₃ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 3]? = some byte₃)
    (hval : Word.toBitVec64 r.rdWrite = extend_value isU (byte₃ ++ byte₂ ++ byte₁ ++ byte₀))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesLoad 4 isU hpin hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_aligned' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat % 4 = 0 := by rw [← himmbind]; exact h_aligned
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem₀' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte₀ := by rw [← himmbind]; exact hmem₀
  have hmem₁' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1]? = some byte₁ := by rw [← himmbind]; exact hmem₁
  have hmem₂' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 2]? = some byte₂ := by rw [← himmbind]; exact hmem₂
  have hmem₃' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 3]? = some byte₃ := by rw [← himmbind]; exact hmem₃
  exact advance_load_core (instruction.LOAD (imm, .Regidx rs1, .Regidx rd, isU, 4)) rd
    (extend_value isU (byte₃ ++ byte₂ ++ byte₁ ++ byte₀)) (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width4 imm rs1 rd isU
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte₀ byte₁ byte₂ byte₃ t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_aligned' h_hi' h_lo'
        (by rw [hmemf]; exact hmem₀') (by rw [hmemf]; exact hmem₁')
        (by rw [hmemf]; exact hmem₂') (by rw [hmemf]; exact hmem₃')
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-- **The width-8 load chip `advance`** (LD). The `advance_of_load_width4` twin, but WITHOUT `hpin`:
the width-8 `LD` opcode is the non-injective `else`→LD image of `loadOpcode`, so the decode is pinned
by the width-validity guard via `decodesLoad' 8 false (by decide)`. Signed (`isU = false`, though for a
full 64-bit read the extension is the identity), 8-byte alignment + eight read bytes → the word
`byte₇ ++ … ++ byte₀`. -/
theorem advance_of_load_width8 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (byte₀ byte₁ byte₂ byte₃ byte₄ byte₅ byte₆ byte₇ : BitVec 8)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 8 false).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hnonX0 : r.adapter.op_a ≠ 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_aligned : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat % 8 = 0)
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem₀ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte₀)
    (hmem₁ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1]? = some byte₁)
    (hmem₂ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 2]? = some byte₂)
    (hmem₃ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 3]? = some byte₃)
    (hmem₄ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 4]? = some byte₄)
    (hmem₅ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 5]? = some byte₅)
    (hmem₆ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 6]? = some byte₆)
    (hmem₇ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 7]? = some byte₇)
    (hval : Word.toBitVec64 r.rdWrite
      = extend_value false (byte₇ ++ byte₆ ++ byte₅ ++ byte₄ ++ byte₃ ++ byte₂ ++ byte₁ ++ byte₀))
    (hwrites : r.commit.writesReg = true := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesLoad' 8 false (by decide) hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd_ne : rd ≠ 0#5 := by intro h0; apply hnonX0; rw [hopa', h0]; simp
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_aligned' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat % 8 = 0 := by rw [← himmbind]; exact h_aligned
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem₀' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte₀ := by rw [← himmbind]; exact hmem₀
  have hmem₁' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1]? = some byte₁ := by rw [← himmbind]; exact hmem₁
  have hmem₂' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 2]? = some byte₂ := by rw [← himmbind]; exact hmem₂
  have hmem₃' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 3]? = some byte₃ := by rw [← himmbind]; exact hmem₃
  have hmem₄' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 4]? = some byte₄ := by rw [← himmbind]; exact hmem₄
  have hmem₅' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 5]? = some byte₅ := by rw [← himmbind]; exact hmem₅
  have hmem₆' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 6]? = some byte₆ := by rw [← himmbind]; exact hmem₆
  have hmem₇' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 7]? = some byte₇ := by rw [← himmbind]; exact hmem₇
  exact advance_load_core (instruction.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) rd
    (extend_value false (byte₇ ++ byte₆ ++ byte₅ ++ byte₄ ++ byte₃ ++ byte₂ ++ byte₁ ++ byte₀))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width8 imm rs1 rd false
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte₀ byte₁ byte₂ byte₃ byte₄ byte₅ byte₆ byte₇
        t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_aligned' h_hi' h_lo'
        (by rw [hmemf]; exact hmem₀') (by rw [hmemf]; exact hmem₁')
        (by rw [hmemf]; exact hmem₂') (by rw [hmemf]; exact hmem₃')
        (by rw [hmemf]; exact hmem₄') (by rw [hmemf]; exact hmem₅')
        (by rw [hmemf]; exact hmem₆') (by rw [hmemf]; exact hmem₇')
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0 hwrites hnomem

/-! ## LoadX0 (load-into-x0, result discarded): the no-write LOAD core + per-width adapters -/

/-- **The no-write straight-line LOAD core** (SC Phase 4 · LoadX0). The intersection of
`advance_load_core` (a LOAD execute, so `hexec` receives the memory frame `t.mem = s.mem` and the
`execute_LOAD` read discharges) and `advance_alu_x0_core` (the write is into `x0`, so `execute I`
returns the state UNCHANGED — the `if_pos rfl` no-op branch of `execute_LOAD_reaches_widthN` — and the
row is straight-line no-write: `next_pc = pc+4`, `commit.writesReg = false`, `commit.memWrite = none`).
Identical to `advance_alu_x0_core` except `hexec` additionally receives `t.mem = s.mem` (fed the internal
`hmem_sa`), so a discarded LOAD's memory read still reduces even though its result is thrown away. -/
theorem advance_load_x0_core {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc) (hrcv : pc = rcvPcOf (stateAccess r))
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.mem = s.mem →
      t.isInitialized → SailConfigured t →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ()) t)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hnowrite : r.commit.writesReg = false)
    (hnomem : r.commit.memWrite = none) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hmem_sa : s_a.mem = s.mem := by rw [hsa_def, hs'_def]
  have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
    have h1 : s'.regs.get? Register.PC = some pc := by
      rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
    rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
    exact (Option.some.injEq _ _).mp h1
  have hnpc_sa : s_a.regs.get? Register.nextPC = some (pc + 4#64) := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert_self, hnpv_def, hgetPC]; simp [BitVec.addInt]
  have hcfg_sa : SailConfigured s_a :=
    SailConfigured.congr (SailConfigured.writeMinstret cfg b) hinit_sa (fun R hR => by
      rw [hsa_def, Std.ExtDHashMap.get?_insert,
          dif_neg (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)])
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hmem_sa hinit_sa hcfg_sa
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      s_a.regs.get? R = s.regs.get? R := fun R h1 h2 => by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active_sa : s_a.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)]; exact cfg.active
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s_a (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active_sa hinit_sa
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hmem_sa]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun _ a => by rw [hmem_fin],
        fun mw hmw => absurd (hnomem.symm.trans hmw) (by simp)⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · rw [hPCf, hnpc_sa]; congr 1
    rw [sndPc_straightline r hstraight hpc0, ← hrcv]
  · rw [if_neg (by rw [hnowrite]; decide)]
    intro idx
    rw [hxf idx]; exact hframe_sa idx
  · exact SailConfigured.congr cfg hinitf hcfg_frame

/-- **The width-1 no-write load chip `advance`** (LoadX0 · LB/LBU). The `advance_of_load_width1` twin
with the `x0` ending: `op_a = 0` forces `rd = 0#5` (`regidx_bv_inj`), the read value is discarded
(`if_pos rfl`), `commit.writesReg = false`, `commit.memWrite = none` — no `hval` (the value is thrown
away). Uses `decodesLoad'` (no `hpin` needed). -/
theorem advance_of_load_x0_width1 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (isU : Bool) (byte : BitVec 8)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 1 isU).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte)
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesLoad' 1 isU (by cases isU <;> decide) hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte := by rw [← himmbind]; exact hmem
  exact advance_load_x0_core (instruction.LOAD (imm, .Regidx rs1, .Regidx 0#5, isU, 1))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width1 imm rs1 0#5 isU
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_hi' h_lo' (by rw [hmemf]; exact hmem')
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **The width-2 no-write load chip `advance`** (LoadX0 · LH/LHU). The `advance_of_load_x0_width1` twin
with the 2-byte alignment precondition + a second read byte. -/
theorem advance_of_load_x0_width2 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (isU : Bool) (byte₀ byte₁ : BitVec 8)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 2 isU).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_aligned : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat % 2 = 0)
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem₀ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte₀)
    (hmem₁ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1]? = some byte₁)
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesLoad' 2 isU (by cases isU <;> decide) hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_aligned' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat % 2 = 0 := by rw [← himmbind]; exact h_aligned
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem₀' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte₀ := by rw [← himmbind]; exact hmem₀
  have hmem₁' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1]? = some byte₁ := by rw [← himmbind]; exact hmem₁
  exact advance_load_x0_core (instruction.LOAD (imm, .Regidx rs1, .Regidx 0#5, isU, 2))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width2 imm rs1 0#5 isU
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte₀ byte₁ t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_aligned' h_hi' h_lo'
        (by rw [hmemf]; exact hmem₀') (by rw [hmemf]; exact hmem₁')
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **The width-4 no-write load chip `advance`** (LoadX0 · LW/LWU). The `advance_of_load_x0_width2` twin
with 4-byte alignment + four read bytes. -/
theorem advance_of_load_x0_width4 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (isU : Bool) (byte₀ byte₁ byte₂ byte₃ : BitVec 8)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 4 isU).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_aligned : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat % 4 = 0)
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem₀ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte₀)
    (hmem₁ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1]? = some byte₁)
    (hmem₂ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 2]? = some byte₂)
    (hmem₃ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 3]? = some byte₃)
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesLoad' 4 isU (by cases isU <;> decide) hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_aligned' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat % 4 = 0 := by rw [← himmbind]; exact h_aligned
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem₀' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte₀ := by rw [← himmbind]; exact hmem₀
  have hmem₁' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1]? = some byte₁ := by rw [← himmbind]; exact hmem₁
  have hmem₂' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 2]? = some byte₂ := by rw [← himmbind]; exact hmem₂
  have hmem₃' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 3]? = some byte₃ := by rw [← himmbind]; exact hmem₃
  exact advance_load_x0_core (instruction.LOAD (imm, .Regidx rs1, .Regidx 0#5, isU, 4))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width4 imm rs1 0#5 isU
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) byte₀ byte₁ byte₂ byte₃ t hinit
        hcfgt.toValidMemConfig ((hframe rs1).trans hrs1) h_aligned' h_hi' h_lo'
        (by rw [hmemf]; exact hmem₀') (by rw [hmemf]; exact hmem₁')
        (by rw [hmemf]; exact hmem₂') (by rw [hmemf]; exact hmem₃')
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **The width-8 no-write load chip `advance`** (LoadX0 · LD). The `advance_of_load_width8` twin
(signed `isU = false`, `decodesLoad' 8 false`) with the `x0` no-write ending: 8-byte alignment +
eight read bytes, all discarded. -/
theorem advance_of_load_x0_width8 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (byte₀ byte₁ byte₂ byte₃ byte₄ byte₅ byte₆ byte₇ : BitVec 8)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((loadOpcode 8 false).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (h_aligned : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat % 8 = 0)
    (h_hi : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat)
    (hmem₀ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat]? = some byte₀)
    (hmem₁ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 1]? = some byte₁)
    (hmem₂ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 2]? = some byte₂)
    (hmem₃ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 3]? = some byte₃)
    (hmem₄ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 4]? = some byte₄)
    (hmem₅ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 5]? = some byte₅)
    (hmem₆ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 6]? = some byte₆)
    (hmem₇ : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
        + Word.toBitVec64 r.adapter.op_c).toNat + 7]? = some byte₇)
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesLoad' 8 false (by decide) hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  have himmbind : Word.toBitVec64 r.adapter.op_c = BitVec.signExtend 64 imm := by
    rw [show r.adapter.op_c = bitVecToWord (imm.signExtend 64) from hopc]
    exact toBitVec64_bitVecToWord _
  have h_aligned' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat % 8 = 0 := by rw [← himmbind]; exact h_aligned
  have h_hi' : (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48 := by rw [← himmbind]; exact h_hi
  have h_lo' : 2 ^ 16 ≤ (Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat := by rw [← himmbind]; exact h_lo
  have hmem₀' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat]? = some byte₀ := by rw [← himmbind]; exact hmem₀
  have hmem₁' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 1]? = some byte₁ := by rw [← himmbind]; exact hmem₁
  have hmem₂' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 2]? = some byte₂ := by rw [← himmbind]; exact hmem₂
  have hmem₃' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 3]? = some byte₃ := by rw [← himmbind]; exact hmem₃
  have hmem₄' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 4]? = some byte₄ := by rw [← himmbind]; exact hmem₄
  have hmem₅' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 5]? = some byte₅ := by rw [← himmbind]; exact hmem₅
  have hmem₆' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 6]? = some byte₆ := by rw [← himmbind]; exact hmem₆
  have hmem₇' : s.mem[(Word.toBitVec64 r.adapter.op_b_memory.prev_value
      + BitVec.signExtend 64 imm).toNat + 7]? = some byte₇ := by rw [← himmbind]; exact hmem₇
  exact advance_load_x0_core (instruction.LOAD (imm, .Regidx rs1, .Regidx 0#5, false, 8))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _hpcf hmemf hinit hcfgt => by
      have := execute_LOAD_reaches_width8 imm rs1 0#5 false
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        byte₀ byte₁ byte₂ byte₃ byte₄ byte₅ byte₆ byte₇ t hinit hcfgt.toValidMemConfig
        ((hframe rs1).trans hrs1) h_aligned' h_hi' h_lo'
        (by rw [hmemf]; exact hmem₀') (by rw [hmemf]; exact hmem₁')
        (by rw [hmemf]; exact hmem₂') (by rw [hmemf]; exact hmem₃')
        (by rw [hmemf]; exact hmem₄') (by rw [hmemf]; exact hmem₅')
        (by rw [hmemf]; exact hmem₆') (by rw [hmemf]; exact hmem₇')
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-! ## AluX0 (ALU-into-x0, result discarded): the no-write straight-line core + family adapters -/

/-- **The no-write straight-line ALU core** (SC Phase 4).  The AluX0 (write-into-x0, result
discarded) twin of `advance_write_core` / the no-write branch of `advance_of_ctrl`: the execute
stage returns the state UNCHANGED (the `wX_bits 0#5` no-op leaves the register file fixed),
`next_pc = pc+4`, `commit.writesReg = false`, `commit.memWrite = none`.  Purpose-built for ALU
ops — the `hexec` needs NO memory frame (ALU never touches memory), just the register-file frame
+ pc frame + init + config.  Every AluX0 family adapter plugs in its own `execute_*_reaches`
lemma at `rd = 0#5` (the `if_pos rfl` no-write branch).  The `RowEffect.regs` uses the `if_neg`
all-index frame read-off (writesReg=false), exactly as `advance_of_ctrl`. -/
theorem advance_alu_x0_core {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (I : instruction) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (cfg : SailConfigured s)
    (hpc : s.regs.get? Register.PC = some pc) (hrcv : pc = rcvPcOf (stateAccess r))
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃)
    (hdecgen : ∀ sc : SailState, SailConfigured sc →
      (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run sc = .ok I sc)
    (hexec : ∀ t : SailState, (∀ idx : BitVec 5, SailState.get_reg? t idx = SailState.get_reg? s idx) →
      t.regs.get? Register.PC = s.regs.get? Register.PC →
      t.isInitialized → SailConfigured t →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ()) t)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hnowrite : r.commit.writesReg = false)
    (hnomem : r.commit.memWrite = none) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (LeanRV64D.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hpcf_sa : s_a.regs.get? Register.PC = s.regs.get? Register.PC := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  have hmem_sa : s_a.mem = s.mem := by rw [hsa_def, hs'_def]
  have hgetPC : s'.regs.get Register.PC (hslr.init Register.PC) = pc := by
    have h1 : s'.regs.get? Register.PC = some pc := by
      rw [hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact hpc
    rw [Std.ExtDHashMap.get?_eq_some_get (hslr.init Register.PC)] at h1
    exact (Option.some.injEq _ _).mp h1
  have hnpc_sa : s_a.regs.get? Register.nextPC = some (pc + 4#64) := by
    rw [hsa_def, Std.ExtDHashMap.get?_insert_self, hnpv_def, hgetPC]; simp [BitVec.addInt]
  have hcfg_sa : SailConfigured s_a :=
    SailConfigured.congr (SailConfigured.writeMinstret cfg b) hinit_sa (fun R hR => by
      rw [hsa_def, Std.ExtDHashMap.get?_insert,
          dif_neg (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)])
  have hexec_sa := hexec s_a hframe_sa hpcf_sa hinit_sa hcfg_sa
  have hcp : (LeanRV64D.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
    rw [Sail.run_readReg, cfg.priv]
  have hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  have hdec : (ext_decode (data₃ ++ data₂ ++ data₁ ++ data₀)).run s' = .ok I s' :=
    hdecgen s' (SailConfigured.writeMinstret cfg b)
  have hframe_s : ∀ R : Register, R ≠ Register.minstret_increment → R ≠ Register.nextPC →
      s_a.regs.get? R = s.regs.get? R := fun R h1 h2 => by
    rw [hsa_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      hs'_def, Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  have h_active_sa : s_a.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe_s Register.hart_state (by decide) (by decide)]; exact cfg.active
  obtain ⟨s_final, hrun, hPCf, hxf, hmemf, hframef, hinitf⟩ :=
    sailStep_of_ladder s s_a s_a (data₃ ++ data₂ ++ data₁ ++ data₀) I b
      hb hcp hactive hslr hdec hsa hexec_sa h_active_sa hinit_sa
  have hcfg_frame : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
        ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hmem_sa]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ?_,
      mem := ⟨fun _ a => by rw [hmem_fin],
        fun mw hmw => absurd (hnomem.symm.trans hmw) (by simp)⟩,
      init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
  · rw [hPCf, hnpc_sa]; congr 1
    rw [sndPc_straightline r hstraight hpc0, ← hrcv]
  · rw [if_neg (by rw [hnowrite]; decide)]
    intro idx
    rw [hxf idx]; exact hframe_sa idx
  · exact SailConfigured.congr cfg hinitf hcfg_frame

/-- **U-type into x0.** The decoded destination is forced to `x0` by `op_a = 0`; Sail therefore
discards the LUI/AUIPC result.  The row is a straight-line architectural no-write even though the
physical register-access adapter still emits its zero-valued `op_a` read-back at the `+4` slot. -/
theorem advance_of_utype_x0 {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (op : uop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((uopToOpcode op).toNat : ZMod p))
    (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0)
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rd, hfetch, hdecw, hopa, _hopb⟩ := decodesUType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by
      rw [← hopa', hopa0]
      simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.UTYPE (imm, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t _hframe hpcf _hinit _hcfg => by
      have reached := execute_UTYPE_reaches imm 0#5 op (rcvPcOf (stateAccess r)) t
        (hpcf.trans hpcread)
      rwa [if_pos rfl] at reached)
    hstraight hpc0 hnowrite hnomem

/-- **R-type into x0** (ADD/SUB/XOR/OR/AND/SLL/SRL/SRA/SLT/SLTU, `imm_c = 0`).  Generic over `op`.
`rd` is forced to `0#5` from the committed `op_a = 0` (via `regidx_bv_inj`, the LoadX0 move), so the
`rtype_execute_reaches` value drops out (`if_pos rfl`) and the whole row is straight-line no-write. -/
theorem advance_of_alu_x0_rtype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : rop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((ropToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesRType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := rtype_execute_reaches rs2 rs1 0#5 op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **RTYPEW into x0** (ADDW/SUBW/SLLW/SRLW/SRAW, `imm_c = 0`).  The `execute_RTYPEW` twin of
`advance_of_alu_x0_rtype`. -/
theorem advance_of_alu_x0_rtypew {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : ropw)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((ropwToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesRTypew op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.RTYPEW (.Regidx rs2, .Regidx rs1, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := rtypew_execute_reaches rs2 rs1 0#5 op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **ITYPE into x0** (ADDI, `imm_c = 1`).  One register read (`rs1` → `op_b`), the immediate in `op_c`. -/
theorem advance_of_alu_x0_itype {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (op : iop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((iopToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesIType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.ITYPE (imm, .Regidx rs1, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := itype_execute_reaches imm rs1 0#5 op (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **Shift-immediate into x0** (`SLLI`/`SRLI`/`SRAI`, `imm_c = 1`).  SP1 uses the same
internal opcode as the corresponding register shift and distinguishes the form through `imm_c`;
the discarded destination makes the row an architectural no-write. -/
theorem advance_of_alu_x0_shiftitype {prog : GuestProgram}
    {r : Trace.RowView (ZMod p)} {s : SailState} (op : sop)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((sopToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, shamt, rs1, rd, hfetch, hdecw, hopa, hopb, _hopc⟩ :=
    decodesShiftIType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady :=
    fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]
    rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by
      rw [← hopa', hopa0]
      simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core
    (instruction.SHIFTIOP (shamt, .Regidx rs1, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have reached := shiftitype_execute_reaches shamt rs1 0#5 op
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_pos rfl] at reached)
    hstraight hpc0 hnowrite hnomem

/-- **Word shift-immediate into x0** (`SLLIW`/`SRLIW`/`SRAIW`, `imm_c = 1`). -/
theorem advance_of_alu_x0_shiftiwtype {prog : GuestProgram}
    {r : Trace.RowView (ZMod p)} {s : SailState} (op : sopw)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((sopwToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, shamt, rs1, rd, hfetch, hdecw, hopa, hopb, _hopc⟩ :=
    decodesShiftIWType op hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady :=
    fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]
    rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by
      rw [← hopa', hopa0]
      simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core
    (instruction.SHIFTIWOP (shamt, .Regidx rs1, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have reached := shiftiwtype_execute_reaches shamt rs1 0#5 op
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_pos rfl] at reached)
    hstraight hpc0 hnowrite hnomem

/-- **ADDIW into x0** (`opcode = ADDW`, `imm_c = 1`). -/
theorem advance_of_alu_x0_addiw {prog : GuestProgram}
    {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (Opcode.ADDW.toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 1)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, _hopc⟩ :=
    decodesADDIW hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady :=
    fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]
    rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by
      rw [← hopa', hopa0]
      simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.ADDIW (imm, .Regidx rs1, .Regidx 0#5))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have reached := execute_ADDIW_reaches imm rs1 0#5
        (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_pos rfl] at reached)
    hstraight hpc0 hnowrite hnomem

/-- **DIV/DIVU into x0** (`imm_c = 0`). -/
theorem advance_of_alu_x0_div {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesDiv isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.DIV (.Regidx rs2, .Regidx rs1, .Regidx 0#5, isU))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := execute_DIV_reaches rs2 rs1 0#5 isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **REM/REMU into x0** (`imm_c = 0`; note the bool-first `SailRV64.rem isU`). -/
theorem advance_of_alu_x0_rem {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.REMU else Opcode.REM)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesRem isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.REM (.Regidx rs2, .Regidx rs1, .Regidx 0#5, isU))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := execute_REM_reaches rs2 rs1 0#5 isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **DIVW/DIVUW into x0** (`imm_c = 0`). -/
theorem advance_of_alu_x0_divw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesDivw isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.DIVW (.Regidx rs2, .Regidx rs1, .Regidx 0#5, isU))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := execute_DIVW_reaches rs2 rs1 0#5 isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **REMW/REMUW into x0** (`imm_c = 0`; bool-first `SailRV64.remw isU`). -/
theorem advance_of_alu_x0_remw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState} (isU : Bool)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = (((if isU then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesRemw isU hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.REMW (.Regidx rs2, .Regidx rs1, .Regidx 0#5, isU))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := execute_REMW_reaches rs2 rs1 0#5 isU (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **MUL-family into x0** (MUL/MULH/MULHU/MULHSU, `imm_c = 0`).  Generic over `op : mul_op`
with the canonicity guard `hcanon` (so the guarded decode fixes the instruction).  `rd` is forced to `0#5`
from the committed `op_a = 0` (`regidx_bv_inj`), the `execute_MUL_reaches op` value drops out
(`if_pos rfl`), the whole row is straight-line no-write.  The `.MUL` twin of `advance_of_alu_x0_div`.
**Move-2:** now covers **all four** canonical MUL ops incl. the previously-seam MUL/MULHSU — `hcanon`
replaces the impossible global-injectivity `hpin`, discharged `by decide` at every concrete op. -/
theorem advance_of_alu_x0_mul {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (op : mul_op) (hcanon : mulOpCanonical op = true)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((mulOpToOpcode op).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesMul op hcanon hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.MUL (.Regidx rs2, .Regidx rs1, .Regidx 0#5, op))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := execute_MUL_reaches rs2 rs1 0#5 op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **MULW into x0** (`imm_c = 0`).  No `mul_op`, so the instruction is fully fixed by the
opcode — the `execute_MULW` twin of `advance_of_alu_x0_divw`. -/
theorem advance_of_alu_x0_mulw {prog : GuestProgram} {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s) (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hop : r.opcode = ((Opcode.MULW).toNat : ZMod p))
    (himmb : r.adapter.imm_b = 0) (himmc : r.adapter.imm_c = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl) (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesMulw hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc; rw [h]; rfl
  have hrs1 := hvalb.1 rs1 himmb hidxb
  have hrs2 := hvalb.2 rs2 himmc hidxc
  have hopa' : r.adapter.op_a = (rd.toNat : ZMod p) := hopa
  have hrd0 : rd = 0#5 := by
    have hh : (rd.toNat : ZMod p) = ((0#5 : BitVec 5).toNat : ZMod p) := by rw [← hopa', hopa0]; simp
    exact regidx_bv_inj hh
  subst hrd0
  exact advance_alu_x0_core (instruction.MULW (.Regidx rs2, .Regidx rs1, .Regidx 0#5))
    (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ _ _ => by
      have := execute_MULW_reaches rs2 rs1 0#5 (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_pos rfl] at this)
    hstraight hpc0 hnowrite hnomem

/-- **Complete v6.4.0 AluX0 dispatch.**  The Byte-table range fact identifies SP1's dynamic
opcode as an ALU opcode, while the verification-key-bound Program row identifies the actual Sail
instruction constructor.  Dispatching on that constructor covers both register and immediate
forms without a second, manually synchronized `(opcode, imm_c)` enumeration. -/
theorem advance_of_alu_x0_program {prog : GuestProgram}
    {r : Trace.RowView (ZMod p)} {s : SailState}
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess r)))
    (hvalb : ValueOperandsBound r s)
    (hdecrom : decodedInROM prog (programAccess r).toRow)
    (hopcode : r.opcode.val < 29)
    (himmb : r.adapter.imm_b = 0)
    (hopa0 : r.adapter.op_a = 0) (hpc0 : (r.state.pc[0]).val < 2 ^ 16)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hnowrite : r.commit.writesReg = false := by rfl)
    (hnomem : r.commit.memWrite = none := by rfl) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hdecrom' := hdecrom
  obtain ⟨_word, instruction, _fetch, _decoded, projected⟩ := hdecrom
  have projected' := instrToProgramRow'_some projected
  have isAlu := instrToProgramRow_isCoreAlu_of_opcode_lt projected' (by
    simpa only [programAccess, ProgramAccess.toRow] using hopcode)
  cases instruction <;> simp only [IsCoreAluInstruction] at isAlu
  case ITYPE args =>
    rcases args with ⟨imm, rs1, rd, op⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = ((iopToOpcode op).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have immediate : r.adapter.imm_c = 1 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_itype op hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb immediate hopa0 hpc0 hstraight hnowrite hnomem
  case SHIFTIOP args =>
    rcases args with ⟨shamt, rs1, rd, op⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = ((sopToOpcode op).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have immediate : r.adapter.imm_c = 1 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_shiftitype op hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb immediate hopa0 hpc0 hstraight hnowrite hnomem
  case RTYPE args =>
    rcases args with ⟨rs2, rs1, rd, op⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = ((ropToOpcode op).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_rtype op hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case ADDIW args =>
    rcases args with ⟨imm, rs1, rd⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = (Opcode.ADDW.toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have immediate : r.adapter.imm_c = 1 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_addiw hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb immediate hopa0 hpc0 hstraight hnowrite hnomem
  case RTYPEW args =>
    rcases args with ⟨rs2, rs1, rd, op⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = ((ropwToOpcode op).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_rtypew op hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case SHIFTIWOP args =>
    rcases args with ⟨shamt, rs1, rd, op⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = ((sopwToOpcode op).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have immediate : r.adapter.imm_c = 1 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_shiftiwtype op hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb immediate hopa0 hpc0 hstraight hnowrite hnomem
  case MUL args =>
    rcases args with ⟨rs2, rs1, rd, op⟩
    have canonical := instrToProgramRow'_mul_canonical projected
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = ((mulOpToOpcode op).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_mul op canonical hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case DIV args =>
    rcases args with ⟨rs2, rs1, rd, isU⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq :
        r.opcode = ((if isU then Opcode.DIVU else Opcode.DIV).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_div isU hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case REM args =>
    rcases args with ⟨rs2, rs1, rd, isU⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq :
        r.opcode = ((if isU then Opcode.REMU else Opcode.REM).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_rem isU hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case MULW args =>
    rcases args with ⟨rs2, rs1, rd⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq : r.opcode = (Opcode.MULW.toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_mulw hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case DIVW args =>
    rcases args with ⟨rs2, rs1, rd, isU⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq :
        r.opcode = ((if isU then Opcode.DIVUW else Opcode.DIVW).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_divw isU hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem
  case REMW args =>
    rcases args with ⟨rs2, rs1, rd, isU⟩
    simp only [instrToProgramRow, Option.some.injEq] at projected'
    have opcodeEq :
        r.opcode = ((if isU then Opcode.REMUW else Opcode.REMW).toNat : ZMod p) := by
      have fields := congrArg (fun row => row.opcode) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    have register : r.adapter.imm_c = 0 := by
      have fields := congrArg (fun row => row.imm_c) projected'
      simpa only [programAccess, ProgramAccess.toRow] using fields.symm
    exact advance_of_alu_x0_remw isU hcfg hrom hpcread hvalb hdecrom'
      opcodeEq himmb register hopa0 hpc0 hstraight hnowrite hnomem


end SP1Clean.Advance
