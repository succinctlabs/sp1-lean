import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.StoreWordChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for StoreWord (SW)

`correct_store_word_native` proves Sail's `execute_STORE` (width = 4) agrees with the SP1 chip
emulation: write `nextPC = pc + 4` and the four little-endian bytes of `rs2[31:0]` into
`mem[addr … addr+3]`, via `SailMem.run_vmem_write_of_width_4`. The chip's 8-byte read-modify-write
`store_value` bus representation is a separate trace-level concern. -/

open LeanRV64D.Defs
namespace SP1Clean.StoreWordSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-4 Sail `STORE`. -/
noncomputable def spec_sw (imm : BitVec 12) (rs1 rs2 : BitVec 5) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  execute_STORE imm (.Regidx rs2) (.Regidx rs1) (width := 4)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the four little-endian bytes of `data`
(`= rs2[31:0]`) into `mem[addr … addr+3]`, then retire. -/
def sp1_sw (pc : BitVec 64) (addr : BitVec 64) (data : BitVec 32) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  modify fun st => { st with mem :=
    ((((st.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
      (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
      (addr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
      (addr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))) }
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
/-- Core correctness. This statement is purely about `BitVec`s / the `SailState`, independent of `p`. -/
theorem correct_store_word_native
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (stored : BitVec 64) (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_rs2 : s.get_reg? rs2_idx = some stored)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0)
    (h_does_fit : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat) :
    (spec_sw imm rs1_idx rs2_idx).run s
      = (sp1_sw pc (reg_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb stored 31 0)).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
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
      { h_cur_privilege := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hcp
        h_mprv_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmprv
        h_mseccfg_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmsec
        h_mseccfg_pmm := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmsecpmm
        h_htif_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hhtif
        h_pma_regions := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hpma }
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hsp_rs2 : sp.get_reg? rs2_idx = some stored := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 4 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 4 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hwrite := run_vmem_write_of_width_4 rs1_idx reg_val (BitVec.signExtend 64 imm)
    (Sail.BitVec.extractLsb stored 31 0) sp hsp_init hsp_rs1 h_align' hsp_config h_does_fit h_in_range
  simp only [hmem_eq] at hwrite
  have hsp1 : (sp1_sw pc (reg_val + BitVec.signExtend 64 imm)
        (Sail.BitVec.extractLsb stored 31 0)).run s
      = .ok RETIRE_SUCCESS { sp with mem :=
          ((((s.mem.insert
            (reg_val + BitVec.signExtend 64 imm).toNat
              (BitVec.ofNat 8 (Sail.BitVec.extractLsb stored 31 0).toNat)).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 1)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb stored 31 0).toNat >>> 8))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 2)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb stored 31 0).toNat >>> 16))).insert
            ((reg_val + BitVec.signExtend 64 imm).toNat + 3)
              (BitVec.ofNat 8 ((Sail.BitVec.extractLsb stored 31 0).toNat >>> 24))) } := by
    rw [sp1_sw, EStateM.run_bind, run_writeReg]; rfl
  rw [hsp1]
  simp only [spec_sw]
  rw [EStateM.run_bind, run_readReg_of_isInitialized _ _ hs, hpc_get]
  simp only [EStateM.run_bind, run_writeReg]
  rw [show ({ s with regs := s.regs.insert Register.nextPC (pc + 4#64) } : SailState) = sp from rfl]
  simp [execute_STORE, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert,
    hsp_rs2, hwrite]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from chip `Assumptions` + decode + register/PC reads, Sail's `SW` agrees with
the SP1 chip emulation. -/
theorem sw_chip_reaches_sail
    (input : StoreWordChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : StoreWordChip.Assumptions input data)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (h_hi : Word.toNat input.op_b_val + Word.toNat input.op_c_imm + 4 ≤ 2 ^ 48)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_a_memory.prev_value)) :
    (spec_sw imm rs1_idx rs2_idx).run s
      = (sp1_sw pc (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb (Word.toBitVec64 input.adapter.op_a_memory.prev_value) 31 0)).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  obtain ⟨h_b, h_c, _h_fits48, _h_nonres, h_align4, _h_off, _h_sv⟩ := h_assum
  have hreg : (Word.toBitVec64 input.op_b_val).toNat = Word.toNat input.op_b_val :=
    Word.toBitVec64_toNat h_b
  have hoff : (BitVec.signExtend 64 imm).toNat = Word.toNat input.op_c_imm := by
    rw [← h_imm]; exact Word.toBitVec64_toNat h_c
  refine correct_store_word_native rs1_idx rs2_idx imm (Word.toBitVec64 input.op_b_val)
    (Word.toBitVec64 input.adapter.op_a_memory.prev_value) pc s hs hconfig h_pc h_rs1 h_rs2 ?_ ?_ ?_ ?_
  · -- alignment: `sum % 4 = 0` from the chip's `sum % 2^48 % 4 = 0`
    rw [hreg, hoff, ← Nat.mod_mod_of_dvd _ (by norm_num : (4 : ℕ) ∣ 2 ^ 48)]; exact h_align4
  · -- fits in 64 bits (from the store-fits bound)
    rw [hreg, hoff]; omega
  · -- store fits in the 48-bit physical window
    rw [hreg, hoff]; exact h_hi
  · -- non-reserved: `2^16 ≤ (reg_val + offset).toNat`, no wrap since `sum < 2^48`
    rw [BitVec.toNat_add, hreg, hoff, Nat.mod_eq_of_lt (by omega)]; omega

end SP1Clean.StoreWordSail

namespace SP1Clean.StoreWordChip

open SP1Clean.StoreWordSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Kernel-depth helper lemmas (SC Phase 4 · Phase 3b.3) — the width-4 twins of StoreByte/StoreHalf. -/

private theorem store_byte0_32 (v : BitVec 64) :
    BitVec.ofNat 8 (Sail.BitVec.extractLsb v 31 0).toNat = v.extractLsb' 0 8 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.ofNat_toNat]; bv_decide
private theorem store_byte1_32 (v : BitVec 64) :
    BitVec.ofNat 8 ((Sail.BitVec.extractLsb v 31 0).toNat >>> 8) = v.extractLsb' 8 8 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]
  bv_decide
private theorem store_byte2_32 (v : BitVec 64) :
    BitVec.ofNat 8 ((Sail.BitVec.extractLsb v 31 0).toNat >>> 16) = v.extractLsb' 16 8 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]
  bv_decide
private theorem store_byte3_32 (v : BitVec 64) :
    BitVec.ofNat 8 ((Sail.BitVec.extractLsb v 31 0).toNat >>> 24) = v.extractLsb' 24 8 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]
  bv_decide

private theorem extHashMap_get?_insert_self_sw (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (m.insert k v).get? k = some v := by simp [Std.ExtHashMap.get?_eq_getElem?]
private theorem extHashMap_get?_insert_ne_sw (m : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8)
    (h : k ≠ a) : (m.insert k v).get? a = m.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
    if_neg (by simpa using h)]

/-- **StoreWord's committed bus view** — opcode `38 = SW`, straight-line, `commit = .store ⟨addr, rs2, 4⟩`
(4-byte write of `rs2[31:0]`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.StoreWordColumns (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ⟨inp.state, #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.store_value, 38,
    .store ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 4⟩⟩

def storeAddrNat (cols : Extracted.StoreWordColumns (ZMod p)) : ℕ :=
  cols.address_operation.addr_operation.value[0].val
    + cols.address_operation.addr_operation.value[1].val * 2 ^ 16
    + cols.address_operation.addr_operation.value[2].val * 2 ^ 32

/-- **StoreWord's `advanceReady` bundle** (4-byte twin of StoreHalf's): the op_a read-back, the range
facts, the **4-byte alignment** (`sum % 4 = 0`), the low-pc bound, and the 4-way ROM-disjointness. -/
def AdvanceReady (inp : Inputs (ZMod p)) (cols : Extracted.StoreWordColumns (ZMod p))
    (prog : GuestProgram) (s : SailState) : Prop :=
  (∀ idx : BitVec 5, (idx.toNat : ZMod p) = inp.adapter.op_a →
     s.get_reg? idx = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value)) ∧
  Word.isU64 inp.op_b_val ∧ Word.isU64 inp.op_c_imm ∧
  (Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm + 4 ≤ 2 ^ 48) ∧
  (2 ^ 16 ≤ (Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm) % 2 ^ 48) ∧
  ((Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm) % 4 = 0) ∧
  (inp.state.pc[0].val < 2 ^ 16) ∧
  (∀ a w, prog.fetchWord a = some w → ∀ i : Fin 4,
      a.toNat + (i : ℕ) ≠ storeAddrNat cols ∧ a.toNat + (i : ℕ) ≠ storeAddrNat cols + 1
      ∧ a.toNat + (i : ℕ) ≠ storeAddrNat cols + 2 ∧ a.toNat + (i : ℕ) ≠ storeAddrNat cols + 3)

set_option maxHeartbeats 2000000 in
/-- **`StoreWordChip.advance`** — the per-SW-row `try_step` lift. Over `advance_of_store` +
`execute_STORE_reaches_width4` (via `decodesStore 4`): a 4-byte write, no register write; the four bytes
are `byteAt` at `addr .. addr+3` = the low 4 bytes of `op_a_memory.prev_value`. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.StoreWordColumns (ZMod p))
    (data : ProverData (ZMod p)) (prog : GuestProgram) (s : SailState)
    (_hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : AdvanceReady inp cols prog s) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hopa_bind, hb64, hc64, hfit, hlo, halign, hpc0, hdisj⟩ := hready
  obtain ⟨h_addr_spec, _, _, _⟩ := hspec
  set r := rowView inp cols with hr
  have h38 : (storeOpcode (4 : word_width)).toNat = 38 := storeOpcode_four_toNat
  have hop : r.opcode = ((storeOpcode (4 : word_width)).toNat : ZMod p) := by rw [h38]; simp [hr, rowView]
  have himmc : r.adapter.imm_c = (1 : ZMod p) := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  obtain ⟨w, imm, rs2, rs1, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesStore 4 hdecrom hop himmc storeOpcode_pin_four
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
  have hobn : obv.toNat = Word.toNat inp.op_b_val := Word.toBitVec64_toNat hb64
  have hsimmn : (sign_extend (m := 64) imm : BitVec 64).toNat = Word.toNat inp.op_c_imm := by
    rw [← h_imm]; exact Word.toBitVec64_toNat hc64
  have haddN : (obv + sign_extend (m := 64) imm).toNat
      = Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm := by
    rw [BitVec.toNat_add, hobn, hsimmn, Nat.mod_eq_of_lt (by omega)]
  have hsum : cols.address_operation.addr_operation.value[0].val
      + 65536 * cols.address_operation.addr_operation.value[1].val
      + 65536 ^ 2 * cols.address_operation.addr_operation.value[2].val
      = (Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm) % 2 ^ 48 := h_addr_spec.1
  have haddr : storeAddrNat cols = (obv + sign_extend (m := 64) imm).toNat := by
    rw [haddN]; unfold storeAddrNat
    rw [show cols.address_operation.addr_operation.value[0].val
          + cols.address_operation.addr_operation.value[1].val * 2 ^ 16
          + cols.address_operation.addr_operation.value[2].val * 2 ^ 32
        = cols.address_operation.addr_operation.value[0].val
          + 65536 * cols.address_operation.addr_operation.value[1].val
          + 65536 ^ 2 * cols.address_operation.addr_operation.value[2].val from by ring,
       hsum, Nat.mod_eq_of_lt (by omega)]
  set mw : Trace.MemWrite (ZMod p) :=
    ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 4⟩ with hmwdef
  have hmw : r.commit.memWrite = some mw := rfl
  have hmwaddr : mw.addrNat = (obv + sign_extend (m := 64) imm).toNat := haddr
  have hcov_iff : ∀ a : ℕ, mw.covers a ↔
      (a = (obv + sign_extend (m := 64) imm).toNat ∨ a = (obv + sign_extend (m := 64) imm).toNat + 1
       ∨ a = (obv + sign_extend (m := 64) imm).toNat + 2 ∨ a = (obv + sign_extend (m := 64) imm).toNat + 3) := by
    intro a; have hw4 : mw.width = 4 := rfl
    unfold Trace.MemWrite.covers; rw [hmwaddr, hw4]; omega
  have hbyteAt0 : mw.byteAt mw.addrNat = BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 31 0).toNat := by
    simp only [Trace.MemWrite.byteAt, Nat.sub_self, Nat.mul_zero, hmwdef]
    rw [hopvdef]; exact (store_byte0_32 _).symm
  have hbyteAt1 : mw.byteAt (mw.addrNat + 1)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 8) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (store_byte1_32 _).symm
  have hbyteAt2 : mw.byteAt (mw.addrNat + 2)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 16) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (store_byte2_32 _).symm
  have hbyteAt3 : mw.byteAt (mw.addrNat + 3)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 24) := by
    simp only [Trace.MemWrite.byteAt, hmwdef, Nat.add_sub_cancel_left]
    rw [hopvdef]; exact (store_byte3_32 _).symm
  have hbA0 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat)
      = BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 31 0).toNat := by rw [← hmwaddr]; exact hbyteAt0
  have hbA1 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 1)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 8) := by rw [← hmwaddr]; exact hbyteAt1
  have hbA2 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 2)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 16) := by rw [← hmwaddr]; exact hbyteAt2
  have hbA3 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat + 3)
      = BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 24) := by rw [← hmwaddr]; exact hbyteAt3
  have haligned4 : is_aligned_vaddr (virtaddr.Virtaddr (obv + sign_extend (m := 64) imm)) 4 = true := by
    rw [is_aligned_vaddr_iff_mod, haddN]; exact halign
  have hfit64 : obv.toNat + (sign_extend (m := 64) imm : BitVec 64).toNat + 4 < 2 ^ 64 := by
    rw [hobn, hsimmn]; omega
  have hinr : range_subset (zero_extend (BitVec.addInt (obv + sign_extend (m := 64) imm) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma (obv + sign_extend (m := 64) imm) 4 (by norm_num)
      (by rw [haddN]; omega) (by rw [haddN]; omega)
  have hcov : ∀ a : ℕ, mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        (((m.insert ((obv + sign_extend (m := 64) imm).toNat)
            (BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 31 0).toNat)).insert
          ((obv + sign_extend (m := 64) imm).toNat + 1)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 8))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 2)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 16))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 3)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 24))) s.mem).get? a
        = some (mw.byteAt a) := by
    intro a hcova
    rcases (hcov_iff a).mp hcova with he | he | he | he
    · rw [he, hbA0]
      rw [extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 3) _ _ (by omega),
          extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 2) _ _ (by omega),
          extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 1) _ _ (by omega),
          extHashMap_get?_insert_self_sw]
    · rw [he, hbA1]
      rw [extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 3) _ _ (by omega),
          extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 2) _ _ (by omega),
          extHashMap_get?_insert_self_sw]
    · rw [he, hbA2]
      rw [extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 3) _ _ (by omega),
          extHashMap_get?_insert_self_sw]
    · rw [he, hbA3, extHashMap_get?_insert_self_sw]
  have hncov : ∀ a : ℕ, ¬ mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        (((m.insert ((obv + sign_extend (m := 64) imm).toNat)
            (BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 31 0).toNat)).insert
          ((obv + sign_extend (m := 64) imm).toNat + 1)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 8))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 2)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 16))).insert
          ((obv + sign_extend (m := 64) imm).toNat + 3)
            (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 24))) s.mem).get? a
        = s.mem.get? a := by
    intro a hncova
    have h0 : a ≠ (obv + sign_extend (m := 64) imm).toNat :=
      fun he => hncova ((hcov_iff a).mpr (Or.inl he))
    have h1 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 1 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inl he)))
    have h2 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 2 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inl he))))
    have h3 : a ≠ (obv + sign_extend (m := 64) imm).toNat + 3 :=
      fun he => hncova ((hcov_iff a).mpr (Or.inr (Or.inr (Or.inr he))))
    rw [extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 3) a _ (fun hc => h3 hc.symm),
      extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 2) a _ (fun hc => h2 hc.symm),
      extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat + 1) a _ (fun hc => h1 hc.symm),
      extHashMap_get?_insert_ne_sw _ ((obv + sign_extend (m := 64) imm).toNat) a _ (fun hc => h0 hc.symm)]
  have hdisj' : ∀ a w2, prog.fetchWord a = some w2 → ∀ i : Fin 4, ¬ mw.covers (a.toNat + (i : ℕ)) := by
    intro a w2 hf i hcov'
    rcases (hcov_iff (a.toNat + (i : ℕ))).mp hcov' with he | he | he | he
    · exact (hdisj a w2 hf i).1 (he.trans haddr.symm)
    · exact (hdisj a w2 hf i).2.1 (he.trans (by rw [haddr]))
    · exact (hdisj a w2 hf i).2.2.1 (he.trans (by rw [haddr]))
    · exact (hdisj a w2 hf i).2.2.2 (he.trans (by rw [haddr]))
  refine advance_of_store (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) (rcvPcOf (stateAccess r)) mw
    (fun m => (((m.insert ((obv + sign_extend (m := 64) imm).toNat)
        (BitVec.ofNat 8 (Sail.BitVec.extractLsb opv 31 0).toNat)).insert
      ((obv + sign_extend (m := 64) imm).toNat + 1)
        (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 8))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 2)
        (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 16))).insert
      ((obv + sign_extend (m := 64) imm).toNat + 3)
        (BitVec.ofNat 8 ((Sail.BitVec.extractLsb opv 31 0).toNat >>> 24)))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ hinit hcfgt => ?_)
    hcov hncov hdisj' rfl hpc0 rfl hmw
  exact execute_STORE_reaches_width4 imm rs1 rs2 obv opv t hinit hcfgt.toValidMemConfig
    ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2) haligned4 hfit64 hinr

/-- `ChipKind` registration for StoreWord (SW, opcode 38). -/
def kind : Soundness.ChipKind p where
  name := "StoreWord"
  Inputs := StoreWordChip.Inputs
  Cols := Extracted.StoreWordColumns
  view := rowView
  chipSpec := fun inp cols data => StoreWordChip.Spec inp cols data
  sailEquiv := fun inp _cols s => ∀ (data : ProverData (ZMod p)) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
      (pc : BitVec 64),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    StoreWordChip.Assumptions inp data →
    Word.toBitVec64 inp.op_c_imm = BitVec.signExtend 64 imm →
    Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm + 4 ≤ 2 ^ 48 →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value) →
    (spec_sw imm rs1 rs2).run s
      = (sp1_sw pc (Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb (Word.toBitVec64 inp.adapter.op_a_memory.prev_value) 31 0)).run s
  reaches_sail := fun inp _cols _data s _h_real _h_chip data rs1 rs2 imm pc hs hconfig h_assum h_imm h_hi
      h_pc h_rs1 h_rs2 =>
    sw_chip_reaches_sail inp data rs1 rs2 imm pc s hs hconfig h_assum h_imm h_hi h_pc h_rs1 h_rs2
  advanceReady := AdvanceReady
  advance := some (PLift.up advance)

end SP1Clean.StoreWordChip
