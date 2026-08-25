import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for StoreDouble (SD)

`correct_store_double_native` proves that Sail's `execute_STORE` (width = 8) agrees with the
SP1 chip emulation (`sp1_sd`: write `nextPC = pc + 4` and the eight little-endian bytes of
`rs2` into `mem[addr … addr+7]`), via `SailMem.run_vmem_write_of_width_8`. Caller supplies
register/PC reads and alignment / fits / non-reserved-address facts. -/

open LeanRV64D.Defs
namespace SP1Clean.StoreSail

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SD`
(full 64-bit word store). Note the LeanRV64D `execute_STORE` argument order is
`imm`, `rs2` (stored-value register), `rs1` (base-address register), `width`. -/
noncomputable def spec_sd (imm : BitVec 12) (rs1 rs2 : BitVec 5) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  execute_STORE imm (.Regidx rs2) (.Regidx rs1) (width := 8)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the eight little-endian bytes of the
stored word into `mem[addr … addr+7]`, then retire. The byte shape matches
`run_vmem_write_of_width_8`'s RHS (`BitVec.ofNat 8 (data.toNat >>> 8·k)` with
`data = Word.toBitVec64 stored`). -/
def sp1_sd (pc : BitVec 64) (addr : BitVec 64) (stored : Word (ZMod p)) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
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

omit [Fact (2 ^ 17 < p)] in
theorem correct_store_double_native
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (stored : Word (ZMod p)) (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 stored))
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 8 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (_hstored : Word.isU64 stored) :
    (spec_sd imm rs1_idx rs2_idx).run s
      = (sp1_sd pc (reg_val + BitVec.signExtend 64 imm) stored).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rwa [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc
  -- The post-nextPC-write state: only `regs` changes, so `mem`/config registers persist.
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  have hmem_eq : sp.mem = s.mem := rfl
  have hsp_config : SailState.isValidMemConfig sp hsp_init := by
    obtain ⟨hcp, hmprv, hmsec, hmsecpmm, hhtif, hpma, hpmp⟩ := hconfig
    have key : ∀ (reg : Register) (h : reg ∈ s.regs) (h' : reg ∈ sp.regs),
        reg ≠ Register.nextPC → sp.regs.get reg h' = s.regs.get reg h := by
      intro reg h h' hne
      show (s.regs.insert Register.nextPC (pc + 4#64)).get reg _ = _
      rw [Std.ExtDHashMap.get_insert]; simp [Ne.symm hne]
    exact
      { h_cur_privilege := by rwa [key _ (hs _) (hsp_init _) (by decide)]
        h_mprv_disabled := by rwa [key _ (hs _) (hsp_init _) (by decide)]
        h_mseccfg_disabled := by rwa [key _ (hs _) (hsp_init _) (by decide)]
        h_mseccfg_pmm := by rwa [key _ (hs _) (hsp_init _) (by decide)]
        h_htif_disabled := by rwa [key _ (hs _) (hsp_init _) (by decide)]
        h_pma_regions := by rwa [key _ (hs _) (hsp_init _) (by decide)]
        h_pmp_off := by rwa [key _ (hs _) (hsp_init _) (by decide)] }
  -- Register reads of `rs1` (base) and `rs2` (stored value) survive the `nextPC` write.
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hsp_rs2 : sp.get_reg? rs2_idx = some (Word.toBitVec64 stored) := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  -- The alignment fact in Sail form, and the range-subset PMA fact.
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 8 = true := by
    rw [is_aligned_vaddr_iff_mod]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 8 (by omega) h_lo h_hi
  -- The write result on `sp` (same memory as `s`).
  have hwrite := run_vmem_write_of_width_8 rs1_idx reg_val (BitVec.signExtend 64 imm)
    (Word.toBitVec64 stored) sp hsp_init hsp_rs1 h_align' hsp_config h_in_range
  simp only [hmem_eq] at hwrite
  -- Collapse the `extractLsb` on the stored value.
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
    rw [sp1_sd, EStateM.run_bind, run_writeReg]; rfl
  rw [hsp1]
  simp only [spec_sd]
  rw [EStateM.run_bind, run_readReg_of_isInitialized _ _ hs, hpc_get]
  simp only [EStateM.run_bind, run_writeReg]
  rw [show ({ s with regs := s.regs.insert Register.nextPC (pc + 4#64) } : SailState) = sp from rfl]
  simp [execute_STORE, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert,
    hsp_rs2, hext, hwrite]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from chip `Assumptions` + decode + register/PC reads, Sail's `SD` agrees with
the SP1 chip emulation. -/
theorem sd_chip_reaches_sail
    (input : StoreDoubleChip.Inputs (ZMod p)) (_cols : StoreDoubleChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : StoreDoubleChip.Assumptions input data)
    (h_address : AddressOperation.ValidAddress
      ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (hstored : Word.isU64 input.adapter.op_a_memory.prev_value)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_a_memory.prev_value)) :
    (spec_sd imm rs1_idx rs2_idx).run s
      = (sp1_sd pc (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm)
          input.adapter.op_a_memory.prev_value).run s := by
  obtain ⟨h_b, h_c⟩ := h_assum
  have hfacts := AddressOperation.effectiveAddress_facts h_b h_c h_address
  unfold AddressOperation.effectiveAddress at hfacts
  rw [h_imm] at hfacts
  have h_align48 :
      (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat % 8 = 0 := by
    simpa only [ZMod.val_zero, zero_add, zero_mul, add_zero] using hfacts.2.2.symm
  have hhi :
      (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat < 2 ^ 48 := by
    simpa using hfacts.1
  refine correct_store_double_native rs1_idx rs2_idx imm (Word.toBitVec64 input.op_b_val)
    input.adapter.op_a_memory.prev_value pc s hs hconfig h_pc h_rs1 h_rs2
    h_align48 (by omega) (by simpa using hfacts.2.1) hstored

end SP1Clean.StoreSail

namespace SP1Clean.StoreDoubleChip

open SP1Clean.StoreSail
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Kernel-depth helper lemmas (SC Phase 4 · Phase 3b.4) — the width-8 twins of StoreWord.
Each little-endian byte `k` of the full 64-bit stored value `v` is `v.extractLsb' (8·k) 8`. -/

private theorem sd_byte0_64 (v : BitVec 64) :
    BitVec.ofNat 8 v.toNat = v.extractLsb' 0 8 := by
  simp only [BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte1_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 8) = v.extractLsb' 8 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte2_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 16) = v.extractLsb' 16 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte3_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 24) = v.extractLsb' 24 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte4_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 32) = v.extractLsb' 32 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte5_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 40) = v.extractLsb' 40 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte6_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 48) = v.extractLsb' 48 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide
private theorem sd_byte7_64 (v : BitVec 64) :
    BitVec.ofNat 8 (v.toNat >>> 56) = v.extractLsb' 56 8 := by
  simp only [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]; bv_decide

private theorem extHashMap_get?_insert_self_sd (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (m.insert k v).get? k = some v := by simp [Std.ExtHashMap.get?_eq_getElem?]
private theorem extHashMap_get?_insert_ne_sd (m : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8)
    (h : k ≠ a) : (m.insert k v).get? a = m.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
    if_neg (by simpa using h)]

/-- **StoreDouble's committed bus view** — opcode `39 = SD`, straight-line, `commit = .store ⟨addr, rs2, 8⟩`
(8-byte write of the full 64-bit `rs2`). -/
def rowView (inp : Inputs (ZMod p)) (cols : StoreDoubleChip.Columns (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ⟨inp.state, #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.adapter.op_a_memory.prev_value, 39,
    .store ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 8⟩⟩

/-- StoreDouble's exact aligned RAM-access projection. -/
def ramAccessView (inp : Inputs (ZMod p)) (cols : StoreDoubleChip.Columns (ZMod p)) :
    Trace.RamAccessView (ZMod p) :=
  { compareLow := inp.memory_access.access_timestamp.compare_low
    prevHigh := inp.memory_access.access_timestamp.prev_high
    prevLow := inp.memory_access.access_timestamp.prev_low
    diffLow := inp.memory_access.access_timestamp.diff_low_limb
    diffHigh := inp.memory_access.access_timestamp.diff_high_limb
    address := AddressOperation.alignedValue
      ⟨inp.op_b_val, inp.op_c_imm, 0, 0, 0, inp.is_real⟩ cols.address_operation
    priorValue := inp.memory_access.prev_value
    newValue := inp.adapter.op_a_memory.prev_value }

def storeAddrNat (cols : StoreDoubleChip.Columns (ZMod p)) : ℕ :=
  cols.address_operation.addr_operation.value[0].val
    + cols.address_operation.addr_operation.value[1].val * 2 ^ 16
    + cols.address_operation.addr_operation.value[2].val * 2 ^ 32

/-- **StoreDouble's `advanceReady` bundle** (8-byte twin of StoreWord's): the op_a read-back, the two
operand-word bounds supplied by the grounded Memory bus, and the low-pc bound. Wrapped address range
and 8-byte alignment facts come from the chip's `AddressOperation.Spec`. Program-ROM preservation
is composed once through `SailCodeMemoryCompatible`. -/
def AdvanceReady (inp : Inputs (ZMod p)) (_cols : StoreDoubleChip.Columns (ZMod p))
    (_prog : GuestProgram) (s : SailState) : Prop :=
  (∀ idx : BitVec 5, (idx.toNat : ZMod p) = inp.adapter.op_a →
     s.get_reg? idx = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value)) ∧
  Word.isU64 inp.op_b_val ∧ Word.isU64 inp.op_c_imm ∧
  inp.state.pc[0].val < 2 ^ 16

/-- **`StoreDoubleChip.advance`** — the per-SD-row `try_step` lift. Over `advance_of_store` +
`execute_STORE_reaches_width8` (via `decodesStore' 8`): an 8-byte write, no register write; the eight
bytes are `byteAt` at `addr .. addr+7` = the little-endian bytes of `op_a_memory.prev_value` (full rs2). -/
theorem advance (inp : Inputs (ZMod p)) (cols : StoreDoubleChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : AdvanceReady inp cols prog s) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hopa_bind, hb64, hc64, hpc0⟩ := hready
  obtain ⟨h_addr_row, _, _, _⟩ := hspec
  have hreal' : inp.is_real = 1 := by simpa [rowView] using hreal
  have h_addr_spec := h_addr_row.2.2.2 hreal'
  set r := rowView inp cols with hr
  have h39 : (storeOpcode (8 : word_width)).toNat = 39 := storeOpcode_eight_toNat
  have hop : r.opcode = ((storeOpcode (8 : word_width)).toNat : ZMod p) := by rw [h39]; simp [hr, rowView]
  have himmc : r.adapter.imm_c = (1 : ZMod p) := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  obtain ⟨w, imm, rs2, rs1, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesStore' 8 (by decide) hdecrom hop himmc
  have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
  have hrs1 : s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) := hvalb.1 rs1 himmb hidxb
  have hrs2 : s.get_reg? rs2 = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value) :=
    hopa_bind rs2 hopa.symm
  have hse : (sign_extend (m := 64) imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have h_imm : Word.toBitVec64 inp.op_c_imm = sign_extend (m := 64) imm := by
    have hoc : (inp.op_c_imm : Word (ZMod p)) = bitVecToWord (imm.signExtend 64) := hopc
    rw [hoc, toBitVec64_bitVecToWord, hse]
  set obv := Word.toBitVec64 inp.op_b_val with hobv
  set opv := Word.toBitVec64 inp.adapter.op_a_memory.prev_value with hopvdef
  set addressInput : AddressOperation.Inputs (ZMod p) :=
    ⟨inp.op_b_val, inp.op_c_imm, 0, 0, 0, inp.is_real⟩
  have hvalid : AddressOperation.ValidAddress addressInput := by
    simpa [addressInput] using AddressOperation.validAddress_of_spec h_addr_spec
  have haddressFacts := AddressOperation.effectiveAddress_facts hb64 hc64 hvalid
  have heffective :
      AddressOperation.effectiveAddress addressInput = obv + sign_extend (m := 64) imm := by
    simp [AddressOperation.effectiveAddress, addressInput, obv, h_imm]
  rw [heffective] at haddressFacts
  have hsum : cols.address_operation.addr_operation.value[0].val
      + 65536 * cols.address_operation.addr_operation.value[1].val
      + 65536 ^ 2 * cols.address_operation.addr_operation.value[2].val
      = (Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm) % 2 ^ 48 := h_addr_spec.1
  have haddr : storeAddrNat cols = (obv + sign_extend (m := 64) imm).toNat := by
    unfold storeAddrNat
    rw [show cols.address_operation.addr_operation.value[0].val
          + cols.address_operation.addr_operation.value[1].val * 2 ^ 16
          + cols.address_operation.addr_operation.value[2].val * 2 ^ 32
        = cols.address_operation.addr_operation.value[0].val
          + 65536 * cols.address_operation.addr_operation.value[1].val
          + 65536 ^ 2 * cols.address_operation.addr_operation.value[2].val from by ring,
       hsum, AddressOperation.addressMod48_eq_effectiveAddress_toNat hb64 hc64 hvalid,
       heffective]
  set mw : Trace.MemWrite (ZMod p) :=
    ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 8⟩ with hmwdef
  have hmw : r.commit.memWrite = some mw := rfl
  have hmwaddr : mw.addrNat = (obv + sign_extend (m := 64) imm).toNat := haddr
  have hcov_iff : ∀ a : ℕ, mw.covers a ↔
      (a = (obv + sign_extend (m := 64) imm).toNat ∨ a = (obv + sign_extend (m := 64) imm).toNat + 1
       ∨ a = (obv + sign_extend (m := 64) imm).toNat + 2 ∨ a = (obv + sign_extend (m := 64) imm).toNat + 3
       ∨ a = (obv + sign_extend (m := 64) imm).toNat + 4 ∨ a = (obv + sign_extend (m := 64) imm).toNat + 5
       ∨ a = (obv + sign_extend (m := 64) imm).toNat + 6 ∨ a = (obv + sign_extend (m := 64) imm).toNat + 7)
      := by
    intro a; have hw8 : mw.width = 8 := rfl
    unfold Trace.MemWrite.covers; rw [hmwaddr, hw8]; omega
  have hbyteAt0 : mw.byteAt mw.addrNat = BitVec.ofNat 8 opv.toNat := by
    simp only [Trace.MemWrite.byteAt, Nat.sub_self, Nat.mul_zero, hmwdef]
    rw [hopvdef]; exact (sd_byte0_64 _).symm
  have hbyteAt1 : mw.byteAt (mw.addrNat + 1) = BitVec.ofNat 8 (opv.toNat >>> 8) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte1_64 _).symm
  have hbyteAt2 : mw.byteAt (mw.addrNat + 2) = BitVec.ofNat 8 (opv.toNat >>> 16) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte2_64 _).symm
  have hbyteAt3 : mw.byteAt (mw.addrNat + 3) = BitVec.ofNat 8 (opv.toNat >>> 24) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte3_64 _).symm
  have hbyteAt4 : mw.byteAt (mw.addrNat + 4) = BitVec.ofNat 8 (opv.toNat >>> 32) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte4_64 _).symm
  have hbyteAt5 : mw.byteAt (mw.addrNat + 5) = BitVec.ofNat 8 (opv.toNat >>> 40) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte5_64 _).symm
  have hbyteAt6 : mw.byteAt (mw.addrNat + 6) = BitVec.ofNat 8 (opv.toNat >>> 48) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte6_64 _).symm
  have hbyteAt7 : mw.byteAt (mw.addrNat + 7) = BitVec.ofNat 8 (opv.toNat >>> 56) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (sd_byte7_64 _).symm
  have hbA0 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat)
      = BitVec.ofNat 8 opv.toNat := by rw [← hmwaddr]; exact hbyteAt0
  have hbA1 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 1)
      = BitVec.ofNat 8 (opv.toNat >>> 8) := by rw [← hmwaddr]; exact hbyteAt1
  have hbA2 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 2)
      = BitVec.ofNat 8 (opv.toNat >>> 16) := by rw [← hmwaddr]; exact hbyteAt2
  have hbA3 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 3)
      = BitVec.ofNat 8 (opv.toNat >>> 24) := by rw [← hmwaddr]; exact hbyteAt3
  have hbA4 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 4)
      = BitVec.ofNat 8 (opv.toNat >>> 32) := by rw [← hmwaddr]; exact hbyteAt4
  have hbA5 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 5)
      = BitVec.ofNat 8 (opv.toNat >>> 40) := by rw [← hmwaddr]; exact hbyteAt5
  have hbA6 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 6)
      = BitVec.ofNat 8 (opv.toNat >>> 48) := by rw [← hmwaddr]; exact hbyteAt6
  have hbA7 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 7)
      = BitVec.ofNat 8 (opv.toNat >>> 56) := by rw [← hmwaddr]; exact hbyteAt7
  have halignNat : (obv + sign_extend (m := 64) imm).toNat % 8 = 0 := by
    rw [← haddressFacts.2.2]
    simp [addressInput]
  have haligned8 : is_aligned_vaddr (virtaddr.Virtaddr (obv + sign_extend (m := 64) imm)) 8 = true := by
    rwa [is_aligned_vaddr_iff_mod]
  have hinr : range_subset (zero_extend (BitVec.addInt (obv + sign_extend (m := 64) imm) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma (obv + sign_extend (m := 64) imm) 8 (by norm_num)
      haddressFacts.2.1 (by omega)
  have hcov : ∀ a : ℕ, mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        (((((((m.insert ((obv + sign_extend (m := 64) imm).toNat)
            (BitVec.ofNat 8 opv.toNat)).insert
          ((obv + sign_extend (m := 64) imm).toNat + 1)
            (BitVec.ofNat 8 (opv.toNat >>> 8))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 2)
            (BitVec.ofNat 8 (opv.toNat >>> 16))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 3)
            (BitVec.ofNat 8 (opv.toNat >>> 24))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 4)
            (BitVec.ofNat 8 (opv.toNat >>> 32))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 5)
            (BitVec.ofNat 8 (opv.toNat >>> 40))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 6)
            (BitVec.ofNat 8 (opv.toNat >>> 48))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 7)
            (BitVec.ofNat 8 (opv.toNat >>> 56))) s.mem).get? a
        = some (mw.byteAt a) := by
    intro a hcova
    rcases (hcov_iff a).mp hcova with he | he | he | he | he | he | he | he
    · rw [he, hbA0]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 5) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 4) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 3) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 2) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 1) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA1]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 5) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 4) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 3) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 2) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA2]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 5) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 4) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 3) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA3]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 5) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 4) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA4]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 5) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA5]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA6]
      rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) _ _ (by omega),
          extHashMap_get?_insert_self_sd]
    · rw [he, hbA7, extHashMap_get?_insert_self_sd]
  have hncov : ∀ a : ℕ, ¬ mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        (((((((m.insert ((obv + sign_extend (m := 64) imm).toNat)
            (BitVec.ofNat 8 opv.toNat)).insert
          ((obv + sign_extend (m := 64) imm).toNat + 1)
            (BitVec.ofNat 8 (opv.toNat >>> 8))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 2)
            (BitVec.ofNat 8 (opv.toNat >>> 16))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 3)
            (BitVec.ofNat 8 (opv.toNat >>> 24))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 4)
            (BitVec.ofNat 8 (opv.toNat >>> 32))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 5)
            (BitVec.ofNat 8 (opv.toNat >>> 40))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 6)
            (BitVec.ofNat 8 (opv.toNat >>> 48))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 7)
            (BitVec.ofNat 8 (opv.toNat >>> 56))) s.mem).get? a
        = s.mem.get? a := by
    intro a hncova
    have h0 : a ≠ (obv + sign_extend (m := 64) imm).toNat :=
      fun he => hncova ((hcov_iff a).mpr (Or.inl he))
    have h1 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 1 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inl he)))
    have h2 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 2 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inl he))))
    have h3 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 3 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
    have h4 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 4 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
    have h5 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 5 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
    have h6 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 6 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))))
    have h7 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 7 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he))))))))
    rw [extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 7) a _ (fun hc => h7 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 6) a _ (fun hc => h6 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 5) a _ (fun hc => h5 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 4) a _ (fun hc => h4 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 3) a _ (fun hc => h3 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 2) a _ (fun hc => h2 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat + 1) a _ (fun hc => h1 hc.symm),
      extHashMap_get?_insert_ne_sd _ ((obv + sign_extend (m := 64) imm).toNat) a _ (fun hc => h0 hc.symm)]
  refine advance_of_store (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) (rcvPcOf (stateAccess r)) mw
    (fun m => (((((((m.insert ((obv + sign_extend (m := 64) imm).toNat)
        (BitVec.ofNat 8 opv.toNat)).insert
      ((obv + sign_extend (m := 64) imm).toNat + 1)
        (BitVec.ofNat 8 (opv.toNat >>> 8))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 2)
        (BitVec.ofNat 8 (opv.toNat >>> 16))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 3)
        (BitVec.ofNat 8 (opv.toNat >>> 24))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 4)
        (BitVec.ofNat 8 (opv.toNat >>> 32))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 5)
        (BitVec.ofNat 8 (opv.toNat >>> 40))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 6)
        (BitVec.ofNat 8 (opv.toNat >>> 48))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 7)
        (BitVec.ofNat 8 (opv.toNat >>> 56)))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ hinit hcfgt => ?_)
    hcov hncov rfl hpc0 rfl hmw
  exact execute_STORE_reaches_width8 imm rs1 rs2 obv opv t hinit hcfgt.toValidMemConfig
    ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2) haligned8 hinr

/-- `ChipKind` registration for StoreDouble (SD, opcode 39). -/
def kind : Soundness.ChipKind p where
  name := "StoreDouble"
  Inputs := StoreDoubleChip.Inputs
  Cols := StoreDoubleChip.Columns
  view := rowView
  ramAccess := fun inp cols => some (ramAccessView inp cols)
  chipSpec := fun inp cols data => StoreDoubleChip.Spec inp cols data
  advanceReady := AdvanceReady
  advance := some (PLift.up advance)

end SP1Clean.StoreDoubleChip
