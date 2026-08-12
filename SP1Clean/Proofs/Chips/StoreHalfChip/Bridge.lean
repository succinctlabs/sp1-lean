import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.StoreHalfChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for StoreHalf (SH)

`correct_store_half_native` proves Sail's `execute_STORE` (width = 2) agrees with the SP1 chip
emulation: write `nextPC = pc + 4` and the two little-endian bytes of `rs2[15:0]` into
`mem[addr … addr+1]`, via `SailMem.run_vmem_write_of_width_2`. The chip's 8-byte read-modify-write
`store_value` bus representation is a separate trace-level concern. -/

open LeanRV64D.Defs
namespace SP1Clean.StoreHalfSail

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-2 Sail `STORE`. -/
noncomputable def spec_sh (imm : BitVec 12) (rs1 rs2 : BitVec 5) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  execute_STORE imm (.Regidx rs2) (.Regidx rs1) (width := 2)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the two little-endian bytes of `data`
(`= rs2[15:0]`) into `mem[addr … addr+1]`, then retire. -/
def sp1_sh (pc : BitVec 64) (addr : BitVec 64) (data : BitVec 16) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  modify fun st => { st with mem :=
    ((st.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
      (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))) }
  pure RETIRE_SUCCESS

/-- Core correctness. This statement is purely about `BitVec`s / the `SailState`, independent of `p`. -/
theorem correct_store_half_native
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (stored : BitVec 64) (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_rs2 : s.get_reg? rs2_idx = some stored)
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 2 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat) :
    (spec_sh imm rs1_idx rs2_idx).run s
      = (sp1_sh pc (reg_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb stored 15 0)).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rwa [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  have hmem_eq : sp.mem = s.mem := rfl
  have hsp_config : SailState.isValidMemConfig sp hsp_init := by
    obtain ⟨hcp, hmprv, hmsec, hmsecpmm, hhtif, hpma⟩ := hconfig
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
        h_pma_regions := by rwa [key _ (hs _) (hsp_init _) (by decide)] }
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hsp_rs2 : sp.get_reg? rs2_idx = some stored := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 2 = true := by
    rw [is_aligned_vaddr_iff_mod]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 2 (by omega) h_lo h_hi
  have hwrite := run_vmem_write_of_width_2 rs1_idx reg_val (BitVec.signExtend 64 imm)
    (Sail.BitVec.extractLsb stored 15 0) sp hsp_init hsp_rs1 h_align' hsp_config h_in_range
  simp only [hmem_eq] at hwrite
  have hsp1 : (sp1_sh pc (reg_val + BitVec.signExtend 64 imm)
        (Sail.BitVec.extractLsb stored 15 0)).run s
      = .ok RETIRE_SUCCESS { sp with mem :=
          ((s.mem.insert
            (reg_val + BitVec.signExtend 64 imm).toNat
              (BitVec.ofNat 8 (Sail.BitVec.extractLsb stored 15 0).toNat)).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 1)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb stored 15 0).toNat >>> 8))) } := by
    rw [sp1_sh, EStateM.run_bind, run_writeReg]; rfl
  rw [hsp1]
  simp only [spec_sh]
  rw [EStateM.run_bind, run_readReg_of_isInitialized _ _ hs, hpc_get]
  simp only [EStateM.run_bind, run_writeReg]
  rw [show ({ s with regs := s.regs.insert Register.nextPC (pc + 4#64) } : SailState) = sp from rfl]
  simp [execute_STORE, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert,
    hsp_rs2, hwrite]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from chip `Assumptions` + decode + register/PC reads, Sail's `SH` agrees with
the SP1 chip emulation. -/
theorem sh_chip_reaches_sail
    (input : StoreHalfChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : StoreHalfChip.Assumptions input data)
    (h_address : AddressOperation.ValidAddress
      ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1],
        input.is_real⟩)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_a_memory.prev_value)) :
    (spec_sh imm rs1_idx rs2_idx).run s
      = (sp1_sh pc (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb (Word.toBitVec64 input.adapter.op_a_memory.prev_value) 15 0)).run s := by
  obtain ⟨h_b, h_c, _h_sv⟩ := h_assum
  have hfacts := AddressOperation.effectiveAddress_facts h_b h_c h_address
  unfold AddressOperation.effectiveAddress at hfacts
  rw [h_imm] at hfacts
  have h_align2 :
      (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (by norm_num : (2 : ℕ) ∣ 8), ← hfacts.2.2]
    simp [Nat.add_mod, Nat.mul_mod]
  have hhi :
      (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat < 2 ^ 48 := by
    simpa using hfacts.1
  refine correct_store_half_native rs1_idx rs2_idx imm (Word.toBitVec64 input.op_b_val)
    (Word.toBitVec64 input.adapter.op_a_memory.prev_value) pc s hs hconfig h_pc h_rs1 h_rs2
    h_align2 (by omega) (by simpa using hfacts.2.1)

end SP1Clean.StoreHalfSail

namespace SP1Clean.StoreHalfChip

open SP1Clean.StoreHalfSail
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Kernel-depth helper lemmas (SC Phase 4 · Phase 3b.3)

Each is a shallow, separately-checked `bv_decide`/`simp` leaf, so the composed `advance` term stays under
the kernel's C-stack recursion limit (see the analogous note in `StoreByteChip/Bridge.lean`; `--tstack`
is the elaborator stack, not the kernel's). `advance` only *applies* these. -/

/-- SH low byte: `ofNat 8 (rs2[15:0]).toNat` = `rs2.extractLsb' 0 8`. -/
private theorem store_lo_byte16 (v : BitVec 64) :
    BitVec.ofNat 8 (Sail.BitVec.extractLsb v 15 0).toNat = v.extractLsb' 0 8 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.ofNat_toNat]; bv_decide

/-- SH high byte: `ofNat 8 ((rs2[15:0]).toNat >>> 8)` = `rs2.extractLsb' 8 8`. -/
private theorem store_hi_byte16 (v : BitVec 64) :
    BitVec.ofNat 8 ((Sail.BitVec.extractLsb v 15 0).toNat >>> 8) = v.extractLsb' 8 8 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]
  bv_decide

private theorem extHashMap_get?_insert_self (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (m.insert k v).get? k = some v := by simp [Std.ExtHashMap.get?_eq_getElem?]

private theorem extHashMap_get?_insert_ne (m : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8)
    (h : k ≠ a) : (m.insert k v).get? a = m.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
    if_neg (by simpa using h)]

/-- **StoreHalf's committed bus view** — opcode `37 = SH`, straight-line `next_pc = pc+4`, I-type adapter,
`commit = .store ⟨addr, value, 2⟩`: a real 2-byte memory write (`value = rs2` = `op_a_memory.prev_value`;
`MemWrite.byteAt` takes its two low bytes, matching Sail's `extractLsb rs2 15 0`). `rdWrite = store_value`
is a don't-care for a `writesReg = false` store row. -/
def rowView (inp : Inputs (ZMod p)) (cols : StoreHalfChip.Columns (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ⟨inp.state, #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.store_value, 37,
    .store ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 2⟩⟩

/-- StoreHalf's exact aligned RAM-access projection. -/
def ramAccessView (inp : Inputs (ZMod p)) (cols : StoreHalfChip.Columns (ZMod p)) :
    Trace.RamAccessView (ZMod p) :=
  { compareLow := inp.memory_access.access_timestamp.compare_low
    prevHigh := inp.memory_access.access_timestamp.prev_high
    prevLow := inp.memory_access.access_timestamp.prev_low
    diffLow := inp.memory_access.access_timestamp.diff_low_limb
    diffHigh := inp.memory_access.access_timestamp.diff_high_limb
    address := AddressOperation.alignedValue
      ⟨inp.op_b_val, inp.op_c_imm, 0, inp.offset_bit[0], inp.offset_bit[1],
        inp.is_real⟩
      cols.address_operation
    priorValue := inp.memory_access.prev_value
    newValue := inp.store_value }

/-- The reconciled store address as a `ℕ` (the three committed `AddressOperation` limbs). -/
def storeAddrNat (cols : StoreHalfChip.Columns (ZMod p)) : ℕ :=
  cols.address_operation.addr_operation.value[0].val
    + cols.address_operation.addr_operation.value[1].val * 2 ^ 16
    + cols.address_operation.addr_operation.value[2].val * 2 ^ 32

/-- **StoreHalf's `advanceReady` bundle**: the `op_a` source-read binding (rs2's value), the two
operand-word bounds supplied by the grounded Memory bus, and the low-pc-limb bound. Wrapped address
range and 2-byte alignment facts come from the chip's `AddressOperation.Spec`. Program-ROM
preservation is composed once through `SailCodeMemoryCompatible`. -/
def AdvanceReady (inp : Inputs (ZMod p)) (_cols : StoreHalfChip.Columns (ZMod p))
    (_prog : GuestProgram) (s : SailState) : Prop :=
  (∀ idx : BitVec 5, (idx.toNat : ZMod p) = inp.adapter.op_a →
     s.get_reg? idx = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value)) ∧
  Word.isU64 inp.op_b_val ∧ Word.isU64 inp.op_c_imm ∧
  inp.state.pc[0].val < 2 ^ 16

/-- **`StoreHalfChip.advance`** — the per-SH-row `try_step` lift (SC Phase 4 · Phase 3b.3). Over
`advance_of_store` (the width-general memory-write ladder core), whose `execute_STORE_reaches_width2` (via
`decodesStore 2`) commits the 2-byte write and no register write. The write value is the low half of
`op_a_memory.prev_value` (`byteAt` at `addr`/`addr+1`); the address reconciles to `(op_b + signExtend
imm).toNat` via the chip `Spec`'s `AddressOperation.Spec` conjunct. The `hcov`/`hncov` obligations are
discharged through the shallow kernel-depth helpers. -/
theorem advance (inp : Inputs (ZMod p)) (cols : StoreHalfChip.Columns (ZMod p))
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
  have h37 : (storeOpcode (2 : word_width)).toNat = 37 := storeOpcode_two_toNat
  have hop : r.opcode = ((storeOpcode (2 : word_width)).toNat : ZMod p) := by rw [h37]; simp [hr, rowView]
  have himmc : r.adapter.imm_c = (1 : ZMod p) := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  obtain ⟨w, imm, rs2, rs1, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesStore 2 hdecrom hop himmc storeOpcode_pin_two
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
    ⟨inp.op_b_val, inp.op_c_imm, 0, inp.offset_bit[0], inp.offset_bit[1],
      inp.is_real⟩
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
    ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 2⟩ with hmwdef
  have hmw : r.commit.memWrite = some mw := rfl
  have hmwaddr : mw.addrNat = (obv + sign_extend (m := 64) imm).toNat := haddr
  have hcov_iff : ∀ a : ℕ, mw.covers a ↔
      (a = (obv + sign_extend (m := 64) imm).toNat ∨ a = (obv + sign_extend (m := 64) imm).toNat + 1) := by
    intro a; have hw2 : mw.width = 2 := rfl
    unfold Trace.MemWrite.covers; rw [hmwaddr, hw2]; omega
  have hbyteAt0 : mw.byteAt mw.addrNat
      = BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 15 0).toNat := by
    simp only [Trace.MemWrite.byteAt, Nat.sub_self, Nat.mul_zero, hmwdef]
    rw [hopvdef]; exact (store_lo_byte16 _).symm
  have hbyteAt1 : mw.byteAt (mw.addrNat + 1)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 15 0).toNat >>> 8) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left, Nat.mul_one]
    rw [hopvdef]; exact (store_hi_byte16 _).symm
  have hbA0 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat)
      = BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 15 0).toNat := by
    rw [← hmwaddr]; exact hbyteAt0
  have hbA1 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 1)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 15 0).toNat >>> 8) := by
    rw [← hmwaddr]; exact hbyteAt1
  have halignNat : (obv + sign_extend (m := 64) imm).toNat % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _
      (by norm_num : (2 : ℕ) ∣ 8), ← haddressFacts.2.2]
    simp [addressInput, Nat.add_mod, Nat.mul_mod]
  have haligned2 : is_aligned_vaddr (virtaddr.Virtaddr (obv + sign_extend (m := 64) imm)) 2 = true := by
    rwa [is_aligned_vaddr_iff_mod]
  have hinr : range_subset (zero_extend (BitVec.addInt (obv + sign_extend (m := 64) imm) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma (obv + sign_extend (m := 64) imm) 2 (by norm_num)
      haddressFacts.2.1 (by omega)
  have hcov : ∀ a : ℕ, mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        (m.insert ((obv + sign_extend (m := 64) imm).toNat)
            (BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 15 0).toNat)).insert
          ((obv + sign_extend (m := 64) imm).toNat + 1)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 15 0).toNat >>> 8))) s.mem).get? a
        = some (mw.byteAt a) := by
    intro a hcova
    rcases (hcov_iff a).mp hcova with he | he
    · rw [he, hbA0]
      rw [extHashMap_get?_insert_ne _ ((obv + sign_extend (m := 64) imm).toNat + 1)
          ((obv + sign_extend (m := 64) imm).toNat) _ (by omega), extHashMap_get?_insert_self]
    · rw [he, hbA1, extHashMap_get?_insert_self]
  have hncov : ∀ a : ℕ, ¬ mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        (m.insert ((obv + sign_extend (m := 64) imm).toNat)
            (BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 15 0).toNat)).insert
          ((obv + sign_extend (m := 64) imm).toNat + 1)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 15 0).toNat >>> 8))) s.mem).get? a
        = s.mem.get? a := by
    intro a hncova
    have h0 : a ≠ (obv + sign_extend (m := 64) imm).toNat :=
      fun he => hncova ((hcov_iff a).mpr (Or.inl he))
    have h1 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 1 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr he))
    rw [extHashMap_get?_insert_ne _ ((obv + sign_extend (m := 64) imm).toNat + 1) a _
        (fun hc => h1 hc.symm),
      extHashMap_get?_insert_ne _ ((obv + sign_extend (m := 64) imm).toNat) a _ (fun hc => h0 hc.symm)]
  refine advance_of_store (.STORE (imm, .Regidx rs2, .Regidx rs1, 2)) (rcvPcOf (stateAccess r)) mw
    (fun m => (m.insert ((obv + sign_extend (m := 64) imm).toNat)
        (BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 15 0).toNat)).insert
      ((obv + sign_extend (m := 64) imm).toNat + 1)
        (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 15 0).toNat >>> 8)))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ hinit hcfgt => ?_)
    hcov hncov rfl hpc0 rfl hmw
  exact execute_STORE_reaches_width2 imm rs1 rs2 obv opv t hinit hcfgt.toValidMemConfig
    ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2) haligned2 hinr

/-- `ChipKind` registration for StoreHalf (SH, opcode 37). -/
def kind : Soundness.ChipKind p where
  name := "StoreHalf"
  Inputs := StoreHalfChip.Inputs
  Cols := StoreHalfChip.Columns
  view := rowView
  ramAccess := fun inp cols => some (ramAccessView inp cols)
  chipSpec := fun inp cols data => StoreHalfChip.Spec inp cols data
  advanceReady := AdvanceReady
  advance := some (PLift.up advance)

end SP1Clean.StoreHalfChip
