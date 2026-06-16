import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Chips.StoreByteChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for StoreByte (SB)

`correct_store_byte_native` proves Sail's `execute_STORE` (width = 1) agrees with the SP1 chip
emulation: write `nextPC = pc + 4` and the low byte of `rs2` into `mem[addr]`, via
`SailMem.run_vmem_write_of_width_1`. Bytes have no alignment; the 8-byte read-modify-write
`store_value` bus representation is a separate trace-level concern. -/

namespace SP1Clean.StoreByteSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-1 Sail `STORE`. -/
noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : BitVec 5) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_STORE imm (.Regidx rs2) (.Regidx rs1) (width := 1)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the low byte of `data` (`= rs2[7:0]`) into
`mem[addr]`, then retire. -/
def sp1_sb (pc : BitVec 64) (addr : BitVec 64) (data : BitVec 8) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  modify fun st => { st with mem := (st.mem.insert addr.toNat data) }
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
/-- Core correctness. Purely about `BitVec`s / the `SailState`, independent of `p`. -/
theorem correct_store_byte_native
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (stored : BitVec 64) (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_rs2 : s.get_reg? rs2_idx = some stored)
    (h_does_fit : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat) :
    (spec_sb imm rs1_idx rs2_idx).run s
      = (sp1_sb pc (reg_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb stored 7 0)).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
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
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs1
  have hsp_rs2 : sp.get_reg? rs2_idx = some stored := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs2
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 1 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; omega
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 1 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hwrite := run_vmem_write_of_width_1 rs1_idx reg_val (BitVec.signExtend 64 imm)
    (Sail.BitVec.extractLsb stored 7 0) sp hsp_init hsp_rs1 h_align' hsp_config h_does_fit h_in_range
  simp only [hmem_eq] at hwrite
  have hrx2 : rX_bits (regidx.Regidx rs2_idx) sp = .ok stored sp := by
    have h := @run_rX_bits rs2_idx sp
    simp only [EStateM.run] at h
    rw [h, hsp_rs2]
  have hsp1 : (sp1_sb pc (reg_val + BitVec.signExtend 64 imm)
        (Sail.BitVec.extractLsb stored 7 0)).run s
      = .ok RETIRE_SUCCESS { sp with mem :=
          (s.mem.insert (reg_val + BitVec.signExtend 64 imm).toNat
            (Sail.BitVec.extractLsb stored 7 0)) } := by
    rw [sp1_sb, EStateM.run_bind, run_writeReg]; rfl
  rw [hsp1]
  simp only [spec_sb]
  rw [EStateM.run_bind, run_readReg_of_isInitialized _ _ hs, hpc_get]
  simp only [EStateM.run_bind, run_writeReg]
  rw [show ({ s with regs := s.regs.insert Register.nextPC (pc + 4#64) } : SailState) = sp from rfl]
  simp [execute_STORE, hse, LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert,
    hsp_rs2, hwrite]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from chip `Assumptions` + decode + register/PC reads, Sail's `SB` agrees with
the SP1 chip emulation. -/
theorem sb_chip_reaches_sail
    (input : StoreByteChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : StoreByteChip.Assumptions input data)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (h_hi : Word.toNat input.op_b_val + Word.toNat input.op_c_imm + 1 ≤ 2 ^ 48)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_a_memory.prev_value)) :
    (spec_sb imm rs1_idx rs2_idx).run s
      = (sp1_sb pc (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb (Word.toBitVec64 input.adapter.op_a_memory.prev_value) 7 0)).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  obtain ⟨h_b, h_c, _h_fits48, h_nonres, _h_off, _hob0, _hob1, _hob2⟩ := h_assum
  have hreg : (Word.toBitVec64 input.op_b_val).toNat = Word.toNat input.op_b_val :=
    Word.toBitVec64_toNat h_b
  have hoff : (BitVec.signExtend 64 imm).toNat = Word.toNat input.op_c_imm := by
    rw [← h_imm]; exact Word.toBitVec64_toNat h_c
  refine correct_store_byte_native rs1_idx rs2_idx imm (Word.toBitVec64 input.op_b_val)
    (Word.toBitVec64 input.adapter.op_a_memory.prev_value) pc s hs hconfig h_pc h_rs1 h_rs2 ?_ ?_ ?_
  · rw [hreg, hoff]; omega
  · rw [hreg, hoff]; exact h_hi
  · rw [BitVec.toNat_add, hreg, hoff, Nat.mod_eq_of_lt (by omega)]; omega

end SP1Clean.StoreByteSail

namespace SP1Clean.StoreByteChip

open SP1Clean.StoreByteSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `ChipKind` registration for StoreByte (SB, opcode 36). -/
def kind : Soundness.ChipKind p where
  name := "StoreByte"
  Inputs := StoreByteChip.Inputs
  Cols := Extracted.StoreByteColumns
  view := fun inp _cols => ⟨inp.state,
    #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.store_value, 36⟩
  chipSpec := fun inp cols data => StoreByteChip.Spec inp cols data
  sailEquiv := fun inp _cols s => ∀ (data : ProverData (ZMod p)) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
      (pc : BitVec 64),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    StoreByteChip.Assumptions inp data →
    Word.toBitVec64 inp.op_c_imm = BitVec.signExtend 64 imm →
    Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm + 1 ≤ 2 ^ 48 →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value) →
    (spec_sb imm rs1 rs2).run s
      = (sp1_sb pc (Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb (Word.toBitVec64 inp.adapter.op_a_memory.prev_value) 7 0)).run s
  reaches_sail := fun inp _cols _data s _h_real _h_chip data rs1 rs2 imm pc hs hconfig h_assum h_imm h_hi
      h_pc h_rs1 h_rs2 =>
    sb_chip_reaches_sail inp data rs1 rs2 imm pc s hs hconfig h_assum h_imm h_hi h_pc h_rs1 h_rs2

end SP1Clean.StoreByteChip
