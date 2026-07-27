import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.StoreByteChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for StoreByte (SB)

`correct_store_byte_native` proves Sail's `execute_STORE` (width = 1) agrees with the SP1 chip
emulation: write `nextPC = pc + 4` and the low byte of `rs2` into `mem[addr]`, via
`SailMem.run_vmem_write_of_width_1`. Bytes have no alignment; the 8-byte read-modify-write
`store_value` bus representation is a separate trace-level concern. -/

open LeanRV64D.Defs
namespace SP1Clean.StoreByteSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-1 Sail `STORE`. -/
noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : BitVec 5) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  execute_STORE imm (.Regidx rs2) (.Regidx rs1) (width := 1)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the low byte of `data` (`= rs2[7:0]`) into
`mem[addr]`, then retire. -/
def sp1_sb (pc : BitVec 64) (addr : BitVec 64) (data : BitVec 8) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
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
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat) :
    (spec_sb imm rs1_idx rs2_idx).run s
      = (sp1_sb pc (reg_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb stored 7 0)).run s := by
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
      { h_cur_privilege := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hcp
        h_mprv_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmprv
        h_mseccfg_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmsec
        h_mseccfg_pmm := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmsecpmm
        h_htif_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hhtif
        h_pma_regions := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hpma }
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs1
  have hsp_rs2 : sp.get_reg? rs2_idx = some stored := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs2
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 1 = true := by
    rw [is_aligned_vaddr_iff_mod]; omega
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 1 (by omega) h_lo h_hi
  have hwrite := run_vmem_write_of_width_1 rs1_idx reg_val (BitVec.signExtend 64 imm)
    (Sail.BitVec.extractLsb stored 7 0) sp hsp_init hsp_rs1 h_align' hsp_config h_in_range
  simp only [hmem_eq] at hwrite
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
  simp [execute_STORE, hse, LeanRV64D.Functions.xlen_bytes, PreSail.assert,
    hsp_rs2, hwrite]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from chip `Assumptions` + decode + register/PC reads, Sail's `SB` agrees with
the SP1 chip emulation. -/
theorem sb_chip_reaches_sail
    (input : StoreByteChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : StoreByteChip.Assumptions input data)
    (h_address : AddressOperation.ValidAddress
      ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
        input.offset_bit[2], input.is_real⟩)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_a_memory.prev_value)) :
    (spec_sb imm rs1_idx rs2_idx).run s
      = (sp1_sb pc (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm)
          (Sail.BitVec.extractLsb (Word.toBitVec64 input.adapter.op_a_memory.prev_value) 7 0)).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  obtain ⟨h_b, h_c, _h_sv⟩ := h_assum
  have hfacts := AddressOperation.effectiveAddress_facts h_b h_c h_address
  unfold AddressOperation.effectiveAddress at hfacts
  rw [h_imm] at hfacts
  have hhi :
      (Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat < 2 ^ 48 := by
    simpa using hfacts.1
  refine correct_store_byte_native rs1_idx rs2_idx imm (Word.toBitVec64 input.op_b_val)
    (Word.toBitVec64 input.adapter.op_a_memory.prev_value) pc s hs hconfig h_pc h_rs1 h_rs2
    (by omega) (by simpa using hfacts.2.1)

end SP1Clean.StoreByteSail

namespace SP1Clean.StoreByteChip

open SP1Clean.StoreByteSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Kernel-depth helper lemmas (SC Phase 4 · Phase 3b.3)

The `advance` adapter below assembles `advance_of_store`'s `hcov`/`hncov`/`hbyteAt` obligations. Proving
them with the natural inline `simp [Sail.BitVec.extractLsb, …]` / `simp [Std.ExtHashMap.get?_eq_getElem?]`
grows the proof *term* deep enough that the whole-`advance` kernel type-check hits `(kernel) deep recursion
detected` (a C-stack overflow — `--tstack` is the elaborator stack, not the kernel's). Factoring the three
leaf reductions into these tiny, separately-checked lemmas keeps each `have` a shallow constant application,
so the composed `advance` term stays under the kernel's recursion limit. Each is proven once here; the
`StoreByte` `advance` only *applies* them. (Store{Half,Word,Double} will reuse the same three helpers.) -/

private theorem extractLsb'_0_8_eq (v : BitVec 64) :
    v.extractLsb' 0 8 = Sail.BitVec.extractLsb v 7 0 := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb]

private theorem extHashMap_get?_insert_self (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (m.insert k v).get? k = some v := by simp [Std.ExtHashMap.get?_eq_getElem?]

private theorem extHashMap_get?_insert_ne (m : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8)
    (h : k ≠ a) : (m.insert k v).get? a = m.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
    if_neg (by simpa using h)]

/-- **STORE's committed bus view** — opcode `36 = SB`, straight-line `next_pc = pc+4`, I-type adapter.
`commit = .store ⟨addr, value, 1⟩`: a real 1-byte memory write — `addr` = the 3-limb `AddressOperation`
subcircuit output recovered from the committed columns, `value = inp.adapter.op_a_memory.prev_value`
(rs2's register value word; `MemWrite.byteAt` takes its low byte, matching Sail's
`extractLsb rs2_val 7 0`). `rdWrite` is `inp.store_value` (a don't-care for a `writesReg = false` row). -/
def rowView (inp : Inputs (ZMod p)) (cols : StoreByteChip.Columns (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ⟨inp.state, #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.store_value, 36,
    .store ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 1⟩⟩

/-- StoreByte's exact aligned RAM-access projection. -/
def ramAccessView (inp : Inputs (ZMod p)) (cols : StoreByteChip.Columns (ZMod p)) :
    Trace.RamAccessView (ZMod p) :=
  { compareLow := inp.memory_access.access_timestamp.compare_low
    prevHigh := inp.memory_access.access_timestamp.prev_high
    prevLow := inp.memory_access.access_timestamp.prev_low
    diffLow := inp.memory_access.access_timestamp.diff_low_limb
    diffHigh := inp.memory_access.access_timestamp.diff_high_limb
    address := AddressOperation.alignedValue
      ⟨inp.op_b_val, inp.op_c_imm, inp.offset_bit[0], inp.offset_bit[1],
        inp.offset_bit[2], inp.is_real⟩
      cols.address_operation
    priorValue := inp.memory_access.prev_value
    newValue := inp.store_value }

/-- The reconciled store byte-address as a `ℕ` (the three committed `AddressOperation` limbs). Used in
`AdvanceReady`'s ROM-disjointness clause. -/
def storeAddrNat (cols : StoreByteChip.Columns (ZMod p)) : ℕ :=
  cols.address_operation.addr_operation.value[0].val
    + cols.address_operation.addr_operation.value[1].val * 2 ^ 16
    + cols.address_operation.addr_operation.value[2].val * 2 ^ 32

/-- **StoreByte's `advanceReady` bundle**: the `op_a` source-read binding (rs2's value —
`ValueOperandsBound` supplies only op_b/op_c, so op_a = rs2 is a read-back), the two operand-word
bounds supplied by the grounded Memory bus, and the low-pc-limb bound. Wrapped address range facts
come from the chip's `AddressOperation.Spec`, rather than being repeated as readiness hypotheses.
Program-ROM preservation is a
single execution-boundary `SailCodeMemoryCompatible` contract, not a store AIR precondition. -/
def AdvanceReady (inp : Inputs (ZMod p)) (_cols : StoreByteChip.Columns (ZMod p))
    (_prog : GuestProgram) (s : SailState) : Prop :=
  (∀ idx : BitVec 5, (idx.toNat : ZMod p) = inp.adapter.op_a →
     s.get_reg? idx = some (Word.toBitVec64 inp.adapter.op_a_memory.prev_value)) ∧
  Word.isU64 inp.op_b_val ∧ Word.isU64 inp.op_c_imm ∧
  inp.state.pc[0].val < 2 ^ 16

set_option maxHeartbeats 2000000 in
/-- **`StoreByteChip.advance`** — the per-STORE-row `try_step` lift (SC Phase 4 · Phase 3b.3, the FIRST chip
with a real memory write, `commit = .store …`). Over `advance_of_store` (the memory-write ladder core), whose
`execute_STORE_reaches` (via `decodesStore 1`) commits the 1-byte write and no register write. The write value
is `extractLsb (op_a_memory.prev_value) 7 0` = `byteAt`; the address (`storeAddrNat cols`) reconciles to
`(op_b_val + signExtend imm).toNat` via the chip `Spec`'s `AddressOperation.Spec` conjunct + the range facts
(from `AdvanceReady`). The `hcov`/`hncov`/`hbyteAt` obligations are discharged through the three shallow
kernel-depth helpers above (see their doc-comment). -/
theorem advance (inp : Inputs (ZMod p)) (cols : StoreByteChip.Columns (ZMod p))
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
  have h36 : (storeOpcode (1 : word_width)).toNat = 36 := storeOpcode_one_toNat
  have hop : r.opcode = ((storeOpcode (1 : word_width)).toNat : ZMod p) := by rw [h36]; simp [hr, rowView]
  have himmc : r.adapter.imm_c = (1 : ZMod p) := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  obtain ⟨w, imm, rs2, rs1, hfetch, hdecw, hopa, hopb, hopc⟩ :=
    decodesStore 1 hdecrom hop himmc storeOpcode_pin_one
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
    ⟨inp.op_b_val, inp.op_c_imm, inp.offset_bit[0], inp.offset_bit[1],
      inp.offset_bit[2], inp.is_real⟩
  have hvalid : AddressOperation.ValidAddress addressInput :=
    AddressOperation.validAddress_of_spec h_addr_spec
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
    ⟨cols.address_operation.addr_operation.value, inp.adapter.op_a_memory.prev_value, 1⟩ with hmwdef
  have hmw : r.commit.memWrite = some mw := rfl
  have hmwaddr : mw.addrNat = (obv + sign_extend (m := 64) imm).toNat := haddr
  have hcov_iff : ∀ a : ℕ, mw.covers a ↔ a = (obv + sign_extend (m := 64) imm).toNat := by
    intro a; have hw1 : mw.width = 1 := rfl
    unfold Trace.MemWrite.covers; rw [hmwaddr, hw1]; omega
  have hbyteAt : mw.byteAt mw.addrNat = Sail.BitVec.extractLsb opv 7 0 := by
    simp only [Trace.MemWrite.byteAt, Nat.sub_self, Nat.mul_zero, hmwdef]
    rw [hopvdef]; exact extractLsb'_0_8_eq _
  have hb2 : mw.byteAt ((obv + sign_extend (m := 64) imm).toNat) = Sail.BitVec.extractLsb opv 7 0 := by
    rw [← hmwaddr]; exact hbyteAt
  have haligned : is_aligned_vaddr (virtaddr.Virtaddr (obv + sign_extend (m := 64) imm)) 1 = true := by
    rw [is_aligned_vaddr_iff_mod]; omega
  have hinr : range_subset (zero_extend (BitVec.addInt (obv + sign_extend (m := 64) imm) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma (obv + sign_extend (m := 64) imm) 1 (by norm_num)
      haddressFacts.2.1 (by omega)
  have hcov : ∀ a : ℕ, mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        m.insert ((obv + sign_extend (m := 64) imm).toNat) (Sail.BitVec.extractLsb opv 7 0)) s.mem).get? a
        = some (mw.byteAt a) := by
    intro a hcova
    rw [(hcov_iff a).mp hcova, hb2]; exact extHashMap_get?_insert_self s.mem _ _
  have hncov : ∀ a : ℕ, ¬ mw.covers a →
      ((fun m : Std.ExtHashMap Nat (BitVec 8) =>
        m.insert ((obv + sign_extend (m := 64) imm).toNat) (Sail.BitVec.extractLsb opv 7 0)) s.mem).get? a
        = s.mem.get? a := by
    intro a hncova
    exact extHashMap_get?_insert_ne s.mem _ a _ (fun he => hncova ((hcov_iff a).mpr he.symm))
  refine advance_of_store (.STORE (imm, .Regidx rs2, .Regidx rs1, 1)) (rcvPcOf (stateAccess r)) mw
    (fun m => m.insert ((obv + sign_extend (m := 64) imm).toNat) (Sail.BitVec.extractLsb opv 7 0))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    (fun t hframe _ hinit hcfgt => ?_)
    hcov hncov rfl hpc0 rfl hmw
  exact execute_STORE_reaches imm rs1 rs2 obv opv t hinit hcfgt.toValidMemConfig
    ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2) haligned hinr

/-- `ChipKind` registration for StoreByte (SB, opcode 36). -/
def kind : Soundness.ChipKind p where
  name := "StoreByte"
  Inputs := StoreByteChip.Inputs
  Cols := StoreByteChip.Columns
  view := rowView
  ramAccess := fun inp cols => some (ramAccessView inp cols)
  chipSpec := fun inp cols data => StoreByteChip.Spec inp cols data
  advanceReady := AdvanceReady
  advance := some (PLift.up advance)

end SP1Clean.StoreByteChip
