import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Chips.StoreDoubleChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for StoreDouble (SD)

`correct_store_double_native` proves that Sail's `execute_STORE` (width = 8) agrees with the
SP1 chip emulation (`sp1_sd`: write `nextPC = pc + 4` and the eight little-endian bytes of
`rs2` into `mem[addr … addr+7]`), via `SailMem.run_vmem_write_of_width_8`. Caller supplies
register/PC reads and alignment / fits / non-reserved-address facts. -/

namespace SP1Clean.StoreSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SD`
(full 64-bit word store). Note the LeanRV64D `execute_STORE` argument order is
`imm`, `rs2` (stored-value register), `rs1` (base-address register), `width`. -/
noncomputable def spec_sd (imm : BitVec 12) (rs1 rs2 : BitVec 5) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_STORE imm (.Regidx rs2) (.Regidx rs1) (width := 8)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the eight little-endian bytes of the
stored word into `mem[addr … addr+7]`, then retire. The byte shape matches
`run_vmem_write_of_width_8`'s RHS (`BitVec.ofNat 8 (data.toNat >>> 8·k)` with
`data = Word.toBitVec64 stored`). -/
def sp1_sd (pc : BitVec 64) (addr : BitVec 64) (stored : Word (ZMod p)) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  let data := Word.toBitVec64 stored
  modify fun st => { st with mem :=
    ((((((((st.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
      (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
      (addr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
      (addr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
      (addr.toNat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
      (addr.toNat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
      (addr.toNat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
      (addr.toNat + 7) (BitVec.ofNat 8 (data.toNat >>> 56))) }
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
omit [Fact (2 ^ 17 < p)] in
theorem correct_store_double_native
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (stored : Word (ZMod p)) (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 stored))
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 8 = 0)
    (_h_does_fit : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (_hstored : Word.isU64 stored) :
    (spec_sd imm rs1_idx rs2_idx).run s
      = (sp1_sd pc (reg_val + BitVec.signExtend 64 imm) stored).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  -- The post-nextPC-write state: only `regs` changes, so `mem`/config registers persist.
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  have hmem_eq : sp.mem = s.mem := rfl
  have hsp_config : SailState.isValidMemConfig sp hsp_init := by
    obtain ⟨hcp, hmprv, hmsec, hhtif, hpma⟩ := hconfig
    have key : ∀ (reg : Register) (h : reg ∈ s.regs) (h' : reg ∈ sp.regs),
        reg ≠ Register.nextPC → sp.regs.get reg h' = s.regs.get reg h := by
      intro reg h h' hne
      show (s.regs.insert Register.nextPC (pc + 4#64)).get reg _ = _
      rw [Std.ExtDHashMap.get_insert]; simp [Ne.symm hne]
    exact
      { h_cur_privilege := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hcp
        h_mprv_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmprv
        h_mseccfg_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmsec
        h_htif_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hhtif
        h_pma_regions := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hpma }
  -- Register reads of `rs1` (base) and `rs2` (stored value) survive the `nextPC` write.
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs1
  have hsp_rs2 : sp.get_reg? rs2_idx = some (Word.toBitVec64 stored) := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs2
  -- The alignment fact in Sail form, and the range-subset PMA fact.
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 8 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_does_fit' : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64 := _h_does_fit
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 8 (by omega) h_lo (by rw [hadd]; exact h_hi)
  -- The write result on `sp` (same memory as `s`).
  have hwrite := run_vmem_write_of_width_8 rs1_idx reg_val (BitVec.signExtend 64 imm)
    (Word.toBitVec64 stored) sp hsp_init hsp_rs1 h_align' hsp_config h_does_fit' h_in_range
  simp only [hmem_eq] at hwrite
  -- Resolve `rX_bits rs2` (the stored-value register) on `sp`, and collapse the `extractLsb`.
  have hrx2 : rX_bits (regidx.Regidx rs2_idx) sp = .ok (Word.toBitVec64 stored) sp := by
    have h := @run_rX_bits rs2_idx sp
    simp only [EStateM.run] at h
    rw [h, hsp_rs2]
  have hext : Sail.BitVec.extractLsb (Word.toBitVec64 stored) 63 0 = Word.toBitVec64 stored := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  -- Reduce the SP1 side: thread the `nextPC` write, then run the `modify` of memory.
  have hsp1 : (sp1_sd pc (reg_val + BitVec.signExtend 64 imm) stored).run s
      = .ok RETIRE_SUCCESS { sp with mem :=
          ((((((((s.mem.insert
            (reg_val + BitVec.signExtend 64 imm).toNat
              (BitVec.ofNat 8 (Word.toBitVec64 stored).toNat)).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 1)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 8))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 2)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 16))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 3)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 24))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 4)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 32))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 5)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 40))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 6)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 48))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 7)
              (BitVec.ofNat 8 ((Word.toBitVec64 stored).toNat >>> 56))) } := by
    rw [sp1_sd]
    rw [EStateM.run_bind, run_writeReg]
    rfl
  rw [hsp1]
  simp only [spec_sd]
  rw [EStateM.run_bind, run_readReg_of_isInitialized _ _ hs, hpc_get]
  simp only [EStateM.run_bind, run_writeReg]
  rw [show ({ s with regs := s.regs.insert Register.nextPC (pc + 4#64) } : SailState) = sp from rfl]
  simp [execute_STORE, hse, LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert,
    hsp_rs2, hext, hwrite]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from chip `Assumptions` + decode + register/PC reads, Sail's `SD` agrees with
the SP1 chip emulation. -/
theorem sd_chip_reaches_sail
    (input : StoreDoubleChip.Inputs (ZMod p)) (_cols : Extracted.StoreDoubleColumns (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : StoreDoubleChip.Assumptions input data)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (h_hi : Word.toNat input.op_b_val + Word.toNat input.op_c_imm + 8 ≤ 2 ^ 48)
    (hstored : Word.isU64 input.adapter.op_a_memory.prev_value)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_a_memory.prev_value)) :
    (spec_sd imm rs1_idx rs2_idx).run s
      = (sp1_sd pc (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm)
          input.adapter.op_a_memory.prev_value).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  obtain ⟨h_b, h_c, _h_fits48, h_nonres, h_align48⟩ := h_assum
  have hreg : (Word.toBitVec64 input.op_b_val).toNat = Word.toNat input.op_b_val :=
    Word.toBitVec64_toNat h_b
  have hoff : (BitVec.signExtend 64 imm).toNat = Word.toNat input.op_c_imm := by
    rw [← h_imm]; exact Word.toBitVec64_toNat h_c
  refine correct_store_double_native rs1_idx rs2_idx imm (Word.toBitVec64 input.op_b_val)
    input.adapter.op_a_memory.prev_value pc s hs hconfig h_pc h_rs1 h_rs2 ?_ ?_ ?_ ?_ hstored
  · -- alignment: `sum % 8 = 0` from the chip's `sum % 2^48 % 8 = 0`
    rw [hreg, hoff, ← Nat.mod_mod_of_dvd _ (by norm_num : (8 : ℕ) ∣ 2 ^ 48)]; exact h_align48
  · -- fits in 64 bits (from the store-fits bound)
    rw [hreg, hoff]; omega
  · -- store fits in the 48-bit physical window
    rw [hreg, hoff]; exact h_hi
  · -- non-reserved: `2^16 ≤ (reg_val + offset).toNat`, no wrap since `sum < 2^48`
    rw [BitVec.toNat_add, hreg, hoff, Nat.mod_eq_of_lt (by omega)]; omega

end SP1Clean.StoreSail

namespace SP1Clean.StoreDoubleChip

open SP1Clean.StoreSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `ChipKind` registration for StoreDouble (SD, opcode 39). -/
def kind : Soundness.ChipKind p where
  name := "StoreDouble"
  Inputs := StoreDoubleChip.Inputs
  Cols := Extracted.StoreDoubleColumns
  view := fun inp _cols => ⟨inp.state,
    #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.adapter.op_a_memory.prev_value, 39⟩
  chipSpec := fun inp cols data => StoreDoubleChip.Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (data : ProverData (ZMod p)) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
      (pc : BitVec 64),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    StoreDoubleChip.Assumptions inp data →
    Word.toBitVec64 inp.op_c_imm = BitVec.signExtend 64 imm →
    Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm + 8 ≤ 2 ^ 48 →
    Word.isU64 inp.adapter.op_a_memory.prev_value →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value) →
    (spec_sd imm rs1 rs2).run s
      = (sp1_sd pc (Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm)
          inp.adapter.op_a_memory.prev_value).run s
  reaches_sail := fun inp cols _data s _h_real _h_chip data rs1 rs2 imm pc hs hconfig h_assum h_imm h_hi
      hstored h_pc h_rs1 h_rs2 =>
    sd_chip_reaches_sail inp cols data rs1 rs2 imm pc s hs hconfig h_assum h_imm h_hi hstored h_pc h_rs1
      h_rs2

end SP1Clean.StoreDoubleChip
