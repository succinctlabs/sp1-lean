import SP1Clean.Foundations.SailMemory
import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.LoadHalfChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for LoadHalf (LH / LHU)

`correct_load_half_native` proves Sail's `execute_LOAD` (width = 2) agrees with the SP1 chip
emulation (write `nextPC = pc + 4` and the extended half into `rd`), via
`SailMem.run_vmem_read_of_width_2'`.

`lh_chip_reaches_sail` discharges the `extend_value` equation: `selected_half` and its high bit
`msb` extend (sign for `LH`, zero for `LHU`) to `#v[selected_half, 65535·msb, 65535·msb,
65535·msb]`. -/

namespace SP1Clean.LoadHalfSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Byte-concatenation + extension lemmas (16-bit, the half-word analogues of the word lemmas) -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The little-endian concatenation of the two bytes of a 16-bit limb equals `h`. -/
private lemma toNat_concat_half_bytes [NeZero p] (h : ZMod p) (hh : h.val < 65536) :
    (BitVec.ofNat 8 (h.val >>> 8) ++ BitVec.ofNat 8 h.val).toNat = h.val := by
  have h_hi : h.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have h_decomp : h.val % 256 + (h.val >>> 8) * 256 = h.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (2 ^ 8 : ℕ) = 256 from rfl]
  rw [Nat.mod_eq_of_lt h_hi]
  rw [show h.val >>> 8 <<< 8 ||| h.val % 256 = h.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Zero-extension (LHU) of the 16-bit concatenation is the word `#v[h, 0, 0, 0]`. -/
private lemma zeroExtend64_ofNat16_concat [NeZero p] (h : ZMod p) (hh : h.val < 65536) :
    Sail.BitVec.zeroExtend (BitVec.ofNat 8 (h.val >>> 8) ++ BitVec.ofNat 8 h.val) 64 =
      Word.toBitVec64 #v[h, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, toNat_concat_half_bytes h hh]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Sign-extension (LH), low half: when `h < 2^15` the sign bit is `0`, giving `#v[h, 0, 0, 0]`. -/
private lemma signExtend64_ofNat16_concat_of_lt_32768 [NeZero p]
    (h : ZMod p) (hh : h.val < 65536) (hmsb : h.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (h.val >>> 8) ++ BitVec.ofNat 8 h.val) =
      Word.toBitVec64 #v[h, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb
      (BitVec.ofNat 8 (h.val >>> 8) ++ BitVec.ofNat 8 h.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_half_bytes h hh]
    simp only [decide_eq_false_iff_not, not_le]; change _ < 2 ^ 15; omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_half_bytes h hh]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  omega

/-- Sign-extension (LH), high half: when `h ≥ 2^15` the sign bit is `1`, giving `#v[h, 65535, 65535, 65535]`. -/
private lemma signExtend64_ofNat16_concat_of_ge_32768 [NeZero p]
    (h : ZMod p) (hh : h.val < 65536) (hmsb : 32768 ≤ h.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (h.val >>> 8) ++ BitVec.ofNat 8 h.val) =
      Word.toBitVec64 #v[h, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb
      (BitVec.ofNat 8 (h.val >>> 8) ++ BitVec.ofNat 8 h.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_half_bytes h hh]
    simp only [decide_eq_true_eq]; change 2 ^ 15 ≤ _; omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_half_bytes h hh]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h65535 : (65535 : ZMod p).val = 65535 := by
    rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  rw [h65535]
  omega

/-! ## The Sail bridge -/

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-2 Sail `LOAD`. -/
noncomputable def spec_lh (imm : BitVec 12) (rs1 rd : BitVec 5) (is_unsigned : Bool) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned (width := 2)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the extended loaded word into `rd`. -/
def sp1_lh (rd : BitVec 5) (pc : BitVec 64) (val64 : BitVec 64) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits (.Regidx rd) val64
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
/-- Core correctness: a width-2 Sail `LOAD` reading the two bytes `data₀ data₁` at the (2-aligned)
address agrees with writing `extend_value is_unsigned <read>` to `rd`. Purely about `BitVec`s /
the `SailState`, so independent of the field `p`. -/
theorem correct_load_half_native
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (is_unsigned : Bool) (data₀ data₁ : BitVec 8) (val64 : BitVec 64)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hext : extend_value is_unsigned (data₁ ++ data₀) = val64)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁) :
    (spec_lh imm rs1_idx rd_idx is_unsigned).run s = (sp1_lh rd_idx pc val64).run s := by
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
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]?
      = some data₀ := by rw [hmem_eq, ← hadd]; exact hmem₀
  have hm₁ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1]?
      = some data₁ := by rw [hmem_eq, ← hadd]; exact hmem₁
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 2 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 2 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_2' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range hm₀ hm₁
  simp only at hread
  rw [hsp] at hread
  simp [spec_lh, sp1_lh, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread, hext]

/-- End-to-end: from chip + decode + register/PC reads + selected memory bytes, Sail's `LH`/`LHU`
agrees with the SP1 chip emulation. -/
theorem lh_chip_reaches_sail
    (input : LoadHalfChip.Inputs (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (is_unsigned : Bool)
    (hsel : input.selected_half.val < 65536)
    (hmsb : input.msb = if input.selected_half.val ≥ 32768 then 1 else 0)
    (h_unsigned_msb : is_unsigned = true → input.msb = 0)
    (reg_val : BitVec 64)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 input.selected_half.val))
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (input.selected_half.val >>> 8))) :
    (spec_lh imm rs1_idx rd_idx is_unsigned).run s
      = (sp1_lh rd_idx pc (Word.toBitVec64
          #v[input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb])).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hext : extend_value is_unsigned
      (BitVec.ofNat 8 (input.selected_half.val >>> 8) ++ BitVec.ofNat 8 input.selected_half.val)
      = Word.toBitVec64 #v[input.selected_half, 65535 * input.msb, 65535 * input.msb,
          65535 * input.msb] := by
    cases hu : is_unsigned with
    | true =>
      have hmsb0 : input.msb = 0 := h_unsigned_msb (by rw [hu])
      simp only [extend_value, if_true, zero_extend, hmsb0, mul_zero]
      exact zeroExtend64_ofNat16_concat _ hsel
    | false =>
      simp only [extend_value, Bool.false_eq_true, if_false, sign_extend, Sail.BitVec.signExtend]
      by_cases hge : input.selected_half.val ≥ 32768
      · rw [hmsb, if_pos hge, mul_one]
        exact signExtend64_ofNat16_concat_of_ge_32768 _ hsel hge
      · rw [hmsb, if_neg hge, mul_zero]
        exact signExtend64_ofNat16_concat_of_lt_32768 _ hsel (by omega)
  exact correct_load_half_native rs1_idx rd_idx imm reg_val is_unsigned
    (BitVec.ofNat 8 input.selected_half.val) (BitVec.ofNat 8 (input.selected_half.val >>> 8))
    _ pc s hs hconfig h_pc h_rs1 h_aligned h_fits h_hi h_lo hext hmem₀ hmem₁

end SP1Clean.LoadHalfSail

namespace SP1Clean.LoadHalfChip

open SP1Clean.LoadHalfSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `ChipKind` registration for LoadHalf (LH / LHU, opcodes 30 / 33). `sailEquiv` carries the
2-byte alignment hypothesis. -/
def kind : Soundness.ChipKind p where
  name := "LoadHalf"
  Inputs := LoadHalfChip.Inputs
  Cols := Extracted.LoadHalfColumns
  view := fun inp _cols => ⟨inp.state,
    #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, LoadHalfChip.isReal inp,
    #v[inp.selected_half, 65535 * inp.msb, 65535 * inp.msb, 65535 * inp.msb],
    inp.is_lh * 30 + inp.is_lhu * 33⟩
  chipSpec := fun inp cols data => LoadHalfChip.Spec inp cols data
  sailEquiv := fun inp _cols s => ∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc reg_val : BitVec 64)
      (is_unsigned : Bool),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    inp.selected_half.val < 65536 →
    inp.msb = (if inp.selected_half.val ≥ 32768 then 1 else 0) →
    (is_unsigned = true → inp.msb = 0) →
    (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0 →
    reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64 →
    reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 →
    2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some reg_val →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some (BitVec.ofNat 8 inp.selected_half.val) →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (inp.selected_half.val >>> 8)) →
    (spec_lh imm rs1 rd is_unsigned).run s
      = (sp1_lh rd pc (Word.toBitVec64
          #v[inp.selected_half, 65535 * inp.msb, 65535 * inp.msb, 65535 * inp.msb])).run s
  reaches_sail := fun inp _cols _data s _h_real _h_chip rs1 rd imm pc reg_val is_unsigned hs hconfig
      hsel hmsb h_unsigned_msb h_al h_fits h_hi h_lo h_pc h_rs1 hm0 hm1 =>
    lh_chip_reaches_sail inp rs1 rd imm pc s hs hconfig is_unsigned hsel hmsb h_unsigned_msb
      reg_val h_al h_fits h_hi h_lo h_pc h_rs1 hm0 hm1

end SP1Clean.LoadHalfChip
