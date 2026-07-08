import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.LoadByteChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for LoadByte (LB / LBU)

`correct_load_byte_native` proves Sail's `execute_LOAD` (width = 1) agrees with the SP1 chip
emulation (write `nextPC = pc + 4` and the extended byte into `rd`), via
`SailMem.run_vmem_read_of_width_1'`. Bytes have no alignment.

`lb_chip_reaches_sail` discharges the `extend_value` equation: `selected_byte` and sign bit `msb`
extend to `#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` — the sign fills bits
8–63, so the low limb already carries `65280·msb`. -/

namespace SP1Clean.LoadByteSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## 8-bit extension lemmas (single byte; the sign fills within limb 0) -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Zero-extension (LBU) of an 8-bit value is the word `#v[b, 0, 0, 0]`. -/
private lemma zeroExtend64_ofNat8 [NeZero p] (b : ZMod p) (hb : b.val < 256) :
    Sail.BitVec.zeroExtend (BitVec.ofNat 8 b.val) 64 =
      Word.toBitVec64 #v[b, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Sign-extension (LB), low half: when `b < 2^7` the sign bit is `0`, giving `#v[b, 0, 0, 0]`. -/
private lemma signExtend64_ofNat8_of_lt_128 [NeZero p] (b : ZMod p) (hb : b.val < 256)
    (hmsb : b.val < 128) :
    BitVec.signExtend 64 (BitVec.ofNat 8 b.val) =
      Word.toBitVec64 #v[b, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb (BitVec.ofNat 8 b.val) = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
    simp only [decide_eq_false_iff_not, not_le]
    rw [Nat.mod_eq_of_lt (by omega)]; change _ < 2 ^ 7; omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  omega

/-- Sign-extension (LB), high half: when `b ≥ 2^7` the sign bit is `1`, giving
`#v[b + 65280, 65535, 65535, 65535]` (the low limb carries the `0xFF00` fill). -/
private lemma signExtend64_ofNat8_of_ge_128 [NeZero p] (b : ZMod p) (hb : b.val < 256)
    (hmsb : 128 ≤ b.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 b.val) =
      Word.toBitVec64 #v[b + 65280, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb (BitVec.ofNat 8 b.val) = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
    simp only [decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; change 2 ^ 7 ≤ _; omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h65535 : (65535 : ZMod p).val = 65535 := by
    rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  have hsum : (b + 65280 : ZMod p).val = b.val + 65280 := by
    rw [show (65280 : ZMod p) = ((65280 : ℕ) : ZMod p) from by norm_cast,
      ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (show (65280 : ℕ) < p by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hsum, h65535]
  omega

/-! ## The Sail bridge -/

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-1 Sail `LOAD`. -/
noncomputable def spec_lb (imm : BitVec 12) (rs1 rd : BitVec 5) (is_unsigned : Bool) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned (width := 1)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the extended byte into `rd`. -/
def sp1_lb (rd : BitVec 5) (pc : BitVec 64) (val64 : BitVec 64) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits (.Regidx rd) val64
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
/-- Core correctness: a width-1 Sail `LOAD` reading the byte `data₀` at the address agrees with writing
`extend_value is_unsigned data₀` to `rd`. Purely about `BitVec`s / the `SailState`, independent of `p`. -/
theorem correct_load_byte_native
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (is_unsigned : Bool) (data₀ : BitVec 8) (val64 : BitVec 64)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hext : extend_value is_unsigned data₀ = val64)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀) :
    (spec_lb imm rs1_idx rd_idx is_unsigned).run s = (sp1_lb rd_idx pc val64).run s := by
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
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]?
      = some data₀ := by rw [hmem_eq, ← hadd]; exact hmem₀
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 1 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; omega
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 1 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_1' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range hm₀
  simp only at hread
  rw [hsp] at hread
  simp [spec_lb, sp1_lb, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread, hext]

/-- End-to-end: from chip + decode + register/PC reads + selected memory byte, Sail's `LB`/`LBU`
agrees with the SP1 chip emulation. -/
theorem lb_chip_reaches_sail
    (input : LoadByteChip.Inputs (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (is_unsigned : Bool)
    (hsel : input.selected_byte.val < 256)
    (hmsb : input.msb = if input.selected_byte.val ≥ 128 then 1 else 0)
    (h_unsigned_msb : is_unsigned = true → input.msb = 0)
    (reg_val : BitVec 64)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 input.selected_byte.val)) :
    (spec_lb imm rs1_idx rd_idx is_unsigned).run s
      = (sp1_lb rd_idx pc (Word.toBitVec64
          #v[input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb,
            65535 * input.msb])).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hext : extend_value is_unsigned (BitVec.ofNat 8 input.selected_byte.val)
      = Word.toBitVec64 #v[input.selected_byte + 65280 * input.msb, 65535 * input.msb,
          65535 * input.msb, 65535 * input.msb] := by
    cases hu : is_unsigned with
    | true =>
      have hmsb0 : input.msb = 0 := h_unsigned_msb (by rw [hu])
      simp only [extend_value, if_true, zero_extend, hmsb0, mul_zero, add_zero]
      exact zeroExtend64_ofNat8 _ hsel
    | false =>
      simp only [extend_value, Bool.false_eq_true, if_false, sign_extend, Sail.BitVec.signExtend]
      by_cases hge : input.selected_byte.val ≥ 128
      · rw [hmsb, if_pos hge]; simp only [mul_one]
        exact signExtend64_ofNat8_of_ge_128 _ hsel hge
      · rw [hmsb, if_neg hge]; simp only [mul_zero, add_zero]
        exact signExtend64_ofNat8_of_lt_128 _ hsel (by omega)
  exact correct_load_byte_native rs1_idx rd_idx imm reg_val is_unsigned
    (BitVec.ofNat 8 input.selected_byte.val) _ pc s hs hconfig h_pc h_rs1 h_fits h_hi h_lo hext hmem₀

end SP1Clean.LoadByteSail

namespace SP1Clean.LoadByteChip

open SP1Clean.LoadByteSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **The LoadByte `rdWrite ≡ extend_value` identity**, 2-way over LB (sign) / LBU (zero). The `hval`
`advance_of_load_width1` consumes: for a real row, `Word.toBitVec64 (loaded word) = extend_value isU (the
selected byte)`. Reuses the same-file `LoadByteSail` extend lemmas. -/
lemma loadByte_hval (input : Inputs (ZMod p)) (isU : Bool)
    (hsel : input.selected_byte.val < 256)
    (h_lb_msb : input.is_lb = 1 → (input.msb = 0 ∨ input.msb = 1)
        ∧ (input.msb = 1 ↔ 128 ≤ input.selected_byte.val))
    (h_lbu_msb : input.is_lbu = 1 → input.msb = 0)
    (hcase : (input.is_lb = 1 ∧ input.is_lbu = 0 ∧ isU = false)
        ∨ (input.is_lbu = 1 ∧ input.is_lb = 0 ∧ isU = true)) :
    Word.toBitVec64 (#v[input.selected_byte + 65280 * input.msb, 65535 * input.msb,
        65535 * input.msb, 65535 * input.msb] : Word (ZMod p))
      = extend_value isU (BitVec.ofNat 8 input.selected_byte.val) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  rcases hcase with ⟨hlb, _, rfl⟩ | ⟨hlbu, _, rfl⟩
  · -- LB (signed)
    obtain ⟨hmsbbin, hmsbiff⟩ := h_lb_msb hlb
    simp only [extend_value, Bool.false_eq_true, if_false, sign_extend, Sail.BitVec.signExtend]
    by_cases hge : 128 ≤ input.selected_byte.val
    · rw [hmsbiff.mpr hge]; simp only [mul_one]
      exact (LoadByteSail.signExtend64_ofNat8_of_ge_128 _ hsel hge).symm
    · have hmsb0 : input.msb = 0 := by
        rcases hmsbbin with h | h
        · exact h
        · exact absurd (hmsbiff.mp h) hge
      rw [hmsb0]; simp only [mul_zero, add_zero]
      exact (LoadByteSail.signExtend64_ofNat8_of_lt_128 _ hsel (by omega)).symm
  · -- LBU (unsigned)
    rw [h_lbu_msb hlbu]
    simp only [extend_value, if_true, zero_extend, mul_zero, add_zero]
    exact (LoadByteSail.zeroExtend64_ofNat8 _ hsel).symm

/-- **LoadByte's committed bus view** — standalone (identical to the former inline `kind.view`) so
`LoadByteChip.advance` can be supplied *as* `kind.advance`. Straight-line `next_pc = pc+4`, ITypeReader
adapter, `rdWrite = #v[sb+65280·msb, 65535·msb, …]`, opcode `is_lb·29 + is_lbu·32`, `commit = .regWrite`. -/
def rowView (inp : Inputs (ZMod p)) (_cols : Extracted.LoadByteColumns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨inp.state, #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, LoadByteChip.isReal inp,
    #v[inp.selected_byte + 65280 * inp.msb, 65535 * inp.msb, 65535 * inp.msb, 65535 * inp.msb],
    inp.is_lb * 29 + inp.is_lbu * 32, .regWrite⟩

/-- **LoadByte's `advanceReady` bundle**: the routing (`op_a ≠ 0` — x0 destinations route to LoadX0), the
low-pc-limb bound, the LB/LBU one-hot, the address bounds, and the **memory byte-read binding** (the load's
non-standard precondition, phrased in the ITypeReader columns `op_b_memory.prev_value`/`op_c_imm`). -/
def AdvanceReady (inp : Inputs (ZMod p)) (_cols : Extracted.LoadByteColumns (ZMod p))
    (_prog : GuestProgram) (s : SailState) : Prop :=
  inp.adapter.op_a ≠ 0 ∧
  (inp.state.pc[0]).val < 2 ^ 16 ∧
  ((inp.is_lb = 1 ∧ inp.is_lbu = 0) ∨ (inp.is_lbu = 1 ∧ inp.is_lb = 0)) ∧
  (Word.toBitVec64 inp.adapter.op_b_memory.prev_value).toNat
      + (Word.toBitVec64 inp.adapter.op_c_imm).toNat + 1 < 2 ^ 64 ∧
  (Word.toBitVec64 inp.adapter.op_b_memory.prev_value).toNat
      + (Word.toBitVec64 inp.adapter.op_c_imm).toNat + 1 ≤ 2 ^ 48 ∧
  2 ^ 16 ≤ (Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat ∧
  s.mem[(Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat]? = some (BitVec.ofNat 8 inp.selected_byte.val)

set_option maxHeartbeats 4000000 in
/-- **`LoadByteChip.advance`** — the per-LoadByte-row `try_step` lift (SC Phase 4, the **first chip to
consume the memory axis**). 2-way LB/LBU flag dispatch fixing `isU`; each branch derives the opcode
(29/32 = LB/LBU) and the `rdWrite ≡ extend_value` identity (`loadByte_hval`) from the chip `Spec`, then feeds
`advance_of_load_width1` with the memory binding / bounds / routing carried in `advanceReady`. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.LoadByteColumns (ZMod p))
    (data : ProverData (ZMod p)) (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : AdvanceReady inp cols prog s) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hnonX0, hpc0, hflag, h_fits, h_hi, h_lo, hmem⟩ := hready
  obtain ⟨_h_addr, _h_mem, _h_it, h_bounds, h_msb_fact, _h_limbsel, _hmux, _h_op_a_0,
    h_lbu_msb, _h_lb_bin, _h_lbu_bin, _h_real_bin⟩ := hspec
  have hreal' : LoadByteChip.isReal inp = 1 := hreal
  have hsel : inp.selected_byte.val < 256 := (h_bounds hreal').2.2
  set r := rowView inp cols with hr
  rcases hflag with ⟨hlb, hlbu⟩ | ⟨hlbu, hlb⟩
  · -- LB : isU = false, opcode 29
    refine advance_of_load_width1 false (BitVec.ofNat 8 inp.selected_byte.val)
      (by intro w' u' h; simp only [loadOpcode] at h
          cases u' <;> split_ifs at h with h1 h2 h4 <;>
            simp_all [SP1Clean.Soundness.Opcode.toNat, beq_iff_eq])
      hcfg hrom hpcread hvalb hdecrom
      (by show inp.is_lb * 29 + inp.is_lbu * 32 = _
          rw [hlb, hlbu]; simp only [one_mul, zero_mul, add_zero]
          show (29 : ZMod p) = ((loadOpcode 1 false).toNat : ZMod p)
          rw [show (loadOpcode 1 false).toNat = 29 from by decide]; norm_num)
      rfl rfl hnonX0 hpc0 rfl h_fits h_hi h_lo hmem ?_ rfl rfl
    exact loadByte_hval inp false hsel h_msb_fact
      (fun hu => by rw [hu, one_mul] at h_lbu_msb; exact h_lbu_msb)
      (Or.inl ⟨hlb, hlbu, rfl⟩)
  · -- LBU : isU = true, opcode 32
    refine advance_of_load_width1 true (BitVec.ofNat 8 inp.selected_byte.val)
      (by intro w' u' h; simp only [loadOpcode] at h
          cases u' <;> split_ifs at h with h1 h2 h4 <;>
            simp_all [SP1Clean.Soundness.Opcode.toNat, beq_iff_eq])
      hcfg hrom hpcread hvalb hdecrom
      (by show inp.is_lb * 29 + inp.is_lbu * 32 = _
          rw [hlb, hlbu]; simp only [one_mul, zero_mul, zero_add]
          show (32 : ZMod p) = ((loadOpcode 1 true).toNat : ZMod p)
          rw [show (loadOpcode 1 true).toNat = 32 from by decide]; norm_num)
      rfl rfl hnonX0 hpc0 rfl h_fits h_hi h_lo hmem ?_ rfl rfl
    exact loadByte_hval inp true hsel h_msb_fact
      (fun hu => by rw [hu, one_mul] at h_lbu_msb; exact h_lbu_msb)
      (Or.inr ⟨hlbu, hlb, rfl⟩)

/-- `ChipKind` registration for LoadByte (LB / LBU, opcodes 29 / 32). Bytes are unaligned, so
`sailEquiv` has no alignment hypothesis. `view := rowView` (`commit = .regWrite` — loads write rd);
`advance := some BranchChip-style `advance` over `advance_of_load_width1`, the memory-read binding /
bounds / routing carried in `advanceReady`. -/
def kind : Soundness.ChipKind p where
  name := "LoadByte"
  Inputs := LoadByteChip.Inputs
  Cols := Extracted.LoadByteColumns
  view := rowView
  chipSpec := fun inp cols data => LoadByteChip.Spec inp cols data
  sailEquiv := fun inp _cols s => ∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc reg_val : BitVec 64)
      (is_unsigned : Bool),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    inp.selected_byte.val < 256 →
    inp.msb = (if inp.selected_byte.val ≥ 128 then 1 else 0) →
    (is_unsigned = true → inp.msb = 0) →
    reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64 →
    reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 →
    2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some reg_val →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some (BitVec.ofNat 8 inp.selected_byte.val) →
    (spec_lb imm rs1 rd is_unsigned).run s
      = (sp1_lb rd pc (Word.toBitVec64
          #v[inp.selected_byte + 65280 * inp.msb, 65535 * inp.msb, 65535 * inp.msb,
            65535 * inp.msb])).run s
  reaches_sail := fun inp _cols _data s _h_real _h_chip rs1 rd imm pc reg_val is_unsigned hs hconfig
      hsel hmsb h_unsigned_msb h_fits h_hi h_lo h_pc h_rs1 hm0 =>
    lb_chip_reaches_sail inp rs1 rd imm pc s hs hconfig is_unsigned hsel hmsb h_unsigned_msb
      reg_val h_fits h_hi h_lo h_pc h_rs1 hm0
  advanceReady := AdvanceReady
  advance := some (PLift.up advance)

end SP1Clean.LoadByteChip
