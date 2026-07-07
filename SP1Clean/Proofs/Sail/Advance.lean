import SP1Clean.Proofs.Sail.TryStepReduction
import SP1Clean.Soundness.RowEffectDefs
import SP1Clean.Soundness.ProgramConsistency
import RISCV.Instructions

/-! # Phase 4 — the uniform per-chip `advance` (Sail-step obligation)

The generic composition wiring the Phase-3 `try_step` reduction ladder (`Proofs/Sail/TryStepReduction.lean`)
into each chip's Sail-step obligation (`TargetObligations.lift`, `Soundness/TargetVm.lean`):
`RefinesAt → OperandsBound → ∃ s', SailStep s s' ∧ RowEffect prog row s s'`.

The load-bearing goal is **uniformity**: one `sp1Effect` (a function of the committed `RowView`), one
generic `advance_of_regWrite` proof, and thin per-chip adapters — replacing the 25 bespoke per-chip
`ChipKind.sailEquiv` predicates so the audit surface is a single statement. -/

namespace SP1Clean.Advance

open SP1Clean Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace
open SP1Clean.TryStepReduction

set_option maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

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
  have hp : (2:ℕ) ^ 24 < p := Fact.out
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
  have hp : (2:ℕ) ^ 24 < p := Fact.out
  have hv4 : (4 : ZMod p).val = 4 := by
    simp only [ZMod.val_ofNat, Nat.mod_eq_of_lt (show 4 < p by omega)]
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
    (hsa : (Sail.writeReg Register.nextPC
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
    (hcp : (Sail.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (Sail.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)).run
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (execute I).run s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())) :
    (try_step 0 false).run s
      = (do
          tick_pc ()
          let mi ← Sail.readReg Register.minstret_increment
          if (true && mi) = true then do
              let m ← Sail.readReg Register.minstret
              Sail.writeReg Register.minstret (BitVec.addInt m 1)
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
        let mi ← Sail.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← Sail.readReg Register.minstret
            Sail.writeReg Register.minstret (BitVec.addInt m 1)
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
        let mi ← Sail.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← Sail.readReg Register.minstret
            Sail.writeReg Register.minstret (BitVec.addInt m 1)
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
    (hcp : (Sail.readReg Register.cur_privilege).run s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (ext_decode w).run ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (Sail.writeReg Register.nextPC (BitVec.addInt
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
  htif_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.htif_disabled
  pma_regions := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.pma_regions

/-- **Register read-back.** The value `wX_bits`/`execute` writes to a non-`x0` register `rd` reads back
through `get_reg?` — the `bitVecToRegidxVal`/`reg_idx_must_64` casts cancel. This is the `RowEffect.regs`
rd-write clause. -/
theorem get_reg?_writeBack (s : SailState) (rd : BitVec 5) (rd_ne : rd ≠ 0#5) (v : BitVec 64) :
    SailState.get_reg? ({s with regs := s.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd v)}) rd
      = some v := by
  simp only [SailState.get_reg?, Std.ExtDHashMap.get?_insert_self, if_neg (show ¬(rd = 0) from rd_ne),
    bitVecToRegidxVal]
  grind

/-- `reg_idx_to_Register` is injective on **nonzero** indices — it collides only at `0#5`/`31#5` (both map
to `x31`, the default arm), and `x0` is hardwired-`some 0` in `get_reg?` so that collision is inert. -/
theorem reg_idx_to_Register_ne (idx rd : BitVec 5) (hi : idx ≠ 0#5) (hr : rd ≠ 0#5) (hne : idx ≠ rd) :
    reg_idx_to_Register rd ≠ reg_idx_to_Register idx := by
  revert idx rd; decide

/-- **`SailConfigured` transfers along a config-register frame.** A state `sf` that is initialized and agrees
with `s` on the eight config registers is itself `SailConfigured` — the `RowEffect.cfg` persistence clause. -/
theorem SailConfigured.congr {sf s : SailState} (cfg : SailConfigured s) (hinit : sf.isInitialized)
    (hf : ∀ R : Register, R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus
      ∨ R = Register.mideleg ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
      ∨ R = Register.pma_regions → sf.regs.get? R = s.regs.get? R) :
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
      htif_disabled := by rw [hget Register.htif_tohost_base (hinit _) (hf _ (by tauto))]; exact cfg.htif_disabled
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
      t.isInitialized →
      (execute I).run t = .ok (ExecutionResult.Retire_Success ())
        {t with regs := t.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value)})
    (hrd_ne : rd ≠ 0#5) (hrd_a : (rd.toNat : ZMod p) = r.adapter.op_a)
    (hval : Word.toBitVec64 r.rdWrite = value)
    (hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]])
    (hpc0 : (r.state.pc[0]).val < 2 ^ 16) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  have hxne : ∀ idx : BitVec 5, Register.nextPC ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hmne : ∀ idx : BitVec 5, Register.minstret_increment ≠ reg_idx_to_Register idx := fun idx => by
    unfold reg_idx_to_Register; split <;> decide
  have hrdreg : ∀ R : Register,
      (R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus ∨ R = Register.mideleg
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base ∨ R = Register.pma_regions)
      → R ≠ reg_idx_to_Register rd := by
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (unfold reg_idx_to_Register; split <;> decide)
  obtain ⟨b, hb⟩ : ∃ b, (should_inc_minstret Privilege.Machine).run s = .ok b s :=
    ⟨_, run_should_inc_minstret s cfg.init _⟩
  have hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
    SailConfigured.toStraightLineReady cfg b pc data₀ data₁ data₂ data₃ hfetch
  set s' := ({s with regs := s.regs.insert Register.minstret_increment b}) with hs'_def
  set npv := BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4 with hnpv_def
  set s_a := ({s' with regs := s'.regs.insert Register.nextPC npv}) with hsa_def
  have hsa : (Sail.writeReg Register.nextPC npv).run s' = .ok () s_a := by rw [Sail.run_writeReg]
  have hinit_s' : SailState.isInitialized s' := by
    rw [hs'_def]; exact SailState.isInitialized_insert s cfg.init _ _
  have hinit_sa : SailState.isInitialized s_a := by
    rw [hsa_def]; exact SailState.isInitialized_insert s' hinit_s' _ _
  -- the ladder state `s_a` agrees with `s` on the whole register file (only nextPC/minstret were inserted),
  -- so the family's `hexec` applies.
  have hframe_sa : ∀ idx : BitVec 5, SailState.get_reg? s_a idx = SailState.get_reg? s idx := fun idx => by
    rw [hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
      SailState.get_reg?_insert_of_ne (hmne idx)]
  have hexec_sa := hexec s_a hframe_sa hinit_sa
  set s'' := ({s_a with regs := s_a.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value)})
    with hs''_def
  have hcp : (Sail.readReg Register.cur_privilege).run s = .ok Privilege.Machine s := by
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
        ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base ∨ R = Register.pma_regions)
      → s_final.regs.get? R = s.regs.get? R := fun R hR => by
    rw [hframef R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      hframe_s R (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hR with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (hrdreg R hR)]
  have hmem_fin : s_final.mem = s.mem := by rw [hmemf, hs''_def, hsa_def, hs'_def]
  refine ⟨s_final, ⟨false, hrun⟩,
    { pc := ?_, regs := ⟨?_, ?_⟩, rom := ?_, init := fun _ => hinitf, cfg := fun _ => ?_ }⟩
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
  · -- regs.1
    intro idx hidx
    obtain rfl : idx = rd := (ofNat_val_eq_of_cast hidx).symm.trans (ofNat_val_eq_of_cast hrd_a)
    rw [hxf idx, hs''_def, get_reg?_writeBack s_a idx hrd_ne _, ← hval]
  · -- regs.2
    intro idx hidx
    rw [hxf idx]
    by_cases h0 : idx = 0#5
    · subst h0; simp [SailState.get_reg?]
    · have hidxrd : idx ≠ rd := fun heq => hidx (by rw [heq]; exact hrd_a)
      rw [hs''_def, SailState.get_reg?_insert_of_ne (reg_idx_to_Register_ne idx rd h0 hrd_ne hidxrd),
        hsa_def, SailState.get_reg?_insert_of_ne (hxne idx), hs'_def,
        SailState.get_reg?_insert_of_ne (hmne idx)]
  · -- rom
    intro hr a w hf i; rw [hmem_fin]; exact hr a w hf i
  · -- cfg
    exact SailConfigured.congr cfg hinitf hcfg_frame

/-- **The R-type chip `advance` — RowView-generic, one call per chip.** For any straight-line R-type row
`r` refined by `s` (config + ROM + the committed pc), the Memory-bus value bound (`ValueOperandsBound`),
the Program-bus fetch truth (`decodedInROM`), the opcode/imm column shape, the routing fact `op_a ≠ 0`,
the low-pc-limb bound, and the `Spec`-derived write value `hval`, one real `try_step` produces the row's
committed `RowEffect`. Absorbs the whole per-chip plumbing — the ∀-state decode (`decodesRType`), the fetch
(`fetchReady_of_romLoaded`), and the two register reads — over `advance_of_regWrite`, so each chip's adapter
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
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) op) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesRType op hdecrom hop himmc hcfg
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
    (fun t hframe _ => by
      have := rtype_execute_reaches rs2 rs1 rd op (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
        (Word.toBitVec64 r.adapter.op_c_memory.prev_value) t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval hstraight hpc0

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
          (Word.toBitVec64 r.adapter.op_c) op) :
    ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
  obtain ⟨w, imm, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesIType op hdecrom hop himmc hcfg
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
    (fun t hframe _ => by
      have := itype_execute_reaches imm rs1 rd op (Word.toBitVec64 r.adapter.op_b_memory.prev_value) t
        ((hframe rs1).trans hrs1)
      rwa [if_neg hrd_ne] at this)
    hrd_ne hopa'.symm hval' hstraight hpc0

end SP1Clean.Advance
