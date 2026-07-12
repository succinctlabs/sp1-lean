import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.LoadDoubleChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for LoadDouble (LD)

`correct_load_double_native` proves that the RISC-V Sail execution of `LD`
(`spec_ld`, calling LeanRV64D's `execute_LOAD` with `width = 8`, `is_unsigned = true`)
agrees with the SP1 chip's emulation (`sp1_ld`: write `nextPC = pc + 4` and the loaded
word into the result register `rd`), given:

* the register read of the base address `rs1` (`h_rs1`),
* the PC read (`h_pc`),
* the eight memory bytes that constitute the loaded `Word` (`hmem₀ … hmem₇`),
* alignment / fits / non-reserved-address facts (`h_aligned` / `h_fits` / `h_lo`),

mirroring `SailMem.run_vmem_read_of_width_8'`. This is the memory analogue of
`AddBridge.correct_add_native`: the caller supplies the register/PC reads and the
memory bytes as direct hypotheses (in the full system these come from the reader bus
+ offline-memory consistency), and the byte concatenation of the read equals the
`Word.toBitVec64` of the loaded word (`byteConcat8_toNat_eq_Word_toNat`), so the
`extend_value` (zero-extend, width 8 → 64 with no extension) leaves it and the
`wX_bits` writes on both sides match. -/

open LeanRV64D.Defs
namespace SP1Clean.LoadSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The little-endian concatenation of the eight bytes of a four-limb word equals the word's `toNat`. -/
private lemma byteConcat8_toNat_eq_Word_toNat [NeZero p]
    (a b c d : ZMod p) (ha : a.val < 65536) (hb : b.val < 65536)
    (hc : c.val < 65536) (hd : d.val < 65536) :
    (BitVec.ofNat 8 (d.val >>> 8) ++ BitVec.ofNat 8 d.val ++
      BitVec.ofNat 8 (c.val >>> 8) ++ BitVec.ofNat 8 c.val ++
      BitVec.ofNat 8 (b.val >>> 8) ++ BitVec.ofNat 8 b.val ++
      BitVec.ofNat 8 (a.val >>> 8) ++ BitVec.ofNat 8 a.val).toNat =
      Word.toNat #v[a, b, c, d] := by
  have ha_hi : a.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hb_hi : b.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_hi : c.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hd_hi : d.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have ha_decomp : a.val % 256 + (a.val >>> 8) * 256 = a.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hb_decomp : b.val % 256 + (b.val >>> 8) * 256 = b.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hc_decomp : c.val % 256 + (c.val >>> 8) * 256 = c.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hd_decomp : d.val % 256 + (d.val >>> 8) * 256 = d.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  rw [Word.toNat_def]
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.reducePow,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    show (2 ^ 8 : ℕ) = 256 from rfl]
  have ha_hi_mod : a.val >>> 8 % 256 = a.val >>> 8 := Nat.mod_eq_of_lt ha_hi
  have hb_hi_mod : b.val >>> 8 % 256 = b.val >>> 8 := Nat.mod_eq_of_lt hb_hi
  have hc_hi_mod : c.val >>> 8 % 256 = c.val >>> 8 := Nat.mod_eq_of_lt hc_hi
  have hd_hi_mod : d.val >>> 8 % 256 = d.val >>> 8 := Nat.mod_eq_of_lt hd_hi
  rw [ha_hi_mod, hb_hi_mod, hc_hi_mod, hd_hi_mod]
  rw [show d.val >>> 8 <<< 8 ||| d.val % 256 = d.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  rw [show d.val <<< 8 ||| c.val >>> 8 = d.val * 256 + c.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hc_hi, Nat.shiftLeft_eq]]
  rw [show (d.val * 256 + c.val >>> 8) <<< 8 ||| c.val % 256 =
      (d.val * 256 + c.val >>> 8) * 256 + c.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  rw [show (d.val * 256 + c.val >>> 8) * 256 + c.val % 256 =
      d.val * 65536 + c.val by
    have := hc_decomp; change _ = _; omega]
  rw [show (d.val * 65536 + c.val) <<< 8 ||| b.val >>> 8 =
      (d.val * 65536 + c.val) * 256 + b.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb_hi, Nat.shiftLeft_eq]]
  rw [show ((d.val * 65536 + c.val) * 256 + b.val >>> 8) <<< 8 ||| b.val % 256 =
      ((d.val * 65536 + c.val) * 256 + b.val >>> 8) * 256 + b.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  rw [show ((d.val * 65536 + c.val) * 256 + b.val >>> 8) * 256 + b.val % 256 =
      d.val * 2 ^ 32 + c.val * 65536 + b.val by
    have := hb_decomp; change _ = _; omega]
  rw [show (d.val * 2 ^ 32 + c.val * 65536 + b.val) <<< 8 ||| a.val >>> 8 =
      (d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) ha_hi, Nat.shiftLeft_eq]]
  rw [show ((d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8) <<< 8 ||| a.val % 256 =
      ((d.val * 2 ^ 32 + c.val * 65536 + b.val) * 256 + a.val >>> 8) * 256 + a.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := ha_decomp
  change _ = _
  have : 2 ^ 32 = 4294967296 := by norm_num
  have : 2 ^ 48 = 281474976710656 := by norm_num
  omega

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `LD`
(unsigned, full 64-bit word). -/
noncomputable def spec_ld (imm : BitVec 12) (rs1 rd : BitVec 5) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  execute_LOAD imm (.Regidx rs1) (.Regidx rd) (is_unsigned := true) (width := 8)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the loaded word into the result
register `rd` (x0-uniform via `wX_bits`, exactly as `execute_LOAD` writes its result). -/
def sp1_ld (rd : BitVec 5) (pc : BitVec 64) (loaded : Word (ZMod p)) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits (.Regidx rd) (Word.toBitVec64 loaded)
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
omit [Fact (2 ^ 17 < p)] in
theorem correct_load_double_native
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (loaded : Word (ZMod p)) (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 8 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hloaded : Word.isU64 loaded)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 loaded[0].val))
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (loaded[0].val >>> 8)))
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]?
      = some (BitVec.ofNat 8 loaded[1].val))
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]?
      = some (BitVec.ofNat 8 (loaded[1].val >>> 8)))
    (hmem₄ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 4]?
      = some (BitVec.ofNat 8 loaded[2].val))
    (hmem₅ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 5]?
      = some (BitVec.ofNat 8 (loaded[2].val >>> 8)))
    (hmem₆ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 6]?
      = some (BitVec.ofNat 8 loaded[3].val))
    (hmem₇ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 7]?
      = some (BitVec.ofNat 8 (loaded[3].val >>> 8))) :
    (spec_ld imm rs1_idx rd_idx).run s = (sp1_ld rd_idx pc loaded).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hloaded
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  -- The post-nextPC-write state: only `regs` changes, so `mem`/config registers persist.
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  -- `isInitialized` / `isValidMemConfig` transfer to `sp` (the inserted `nextPC` ≠ config regs).
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  have hmem_eq : sp.mem = s.mem := rfl
  have hsp_config : SailState.isValidMemConfig sp hsp_init := by
    obtain ⟨hcp, hmprv, hmsec, hmsecpmm, hhtif, hpma⟩ := hconfig
    -- Every config register survives the `nextPC` insert (it is none of them).
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
  -- Register read of `rs1` survives the `nextPC` write.
  have hsp_rs1 : sp.get_reg? rs1_idx = some reg_val := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  -- The eight memory bytes on `sp` (same memory as `s`), in the `reg_val.toNat + offset.toNat` form.
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 loaded[0].val) := by rwa [hmem_eq, ← hadd]
  have hm₁ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (loaded[0].val >>> 8)) := by rwa [hmem_eq, ← hadd]
  have hm₂ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2]?
      = some (BitVec.ofNat 8 loaded[1].val) := by rwa [hmem_eq, ← hadd]
  have hm₃ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 3]?
      = some (BitVec.ofNat 8 (loaded[1].val >>> 8)) := by rwa [hmem_eq, ← hadd]
  have hm₄ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4]?
      = some (BitVec.ofNat 8 loaded[2].val) := by rwa [hmem_eq, ← hadd]
  have hm₅ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 5]?
      = some (BitVec.ofNat 8 (loaded[2].val >>> 8)) := by rwa [hmem_eq, ← hadd]
  have hm₆ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 6]?
      = some (BitVec.ofNat 8 loaded[3].val) := by rwa [hmem_eq, ← hadd]
  have hm₇ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 7]?
      = some (BitVec.ofNat 8 (loaded[3].val >>> 8)) := by rwa [hmem_eq, ← hadd]
  -- The alignment fact in Sail form, and the range-subset PMA fact.
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 8 = true := by
    rwa [is_aligned_vaddr_iff_mod, hadd]
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 8 (by omega) h_lo (by rwa [hadd])
  -- The read result on `sp`.
  have hread := run_vmem_read_of_width_8' rs1_idx reg_val (BitVec.signExtend 64 imm)
    (BitVec.ofNat 8 loaded[0].val) (BitVec.ofNat 8 (loaded[0].val >>> 8))
    (BitVec.ofNat 8 loaded[1].val) (BitVec.ofNat 8 (loaded[1].val >>> 8))
    (BitVec.ofNat 8 loaded[2].val) (BitVec.ofNat 8 (loaded[2].val >>> 8))
    (BitVec.ofNat 8 loaded[3].val) (BitVec.ofNat 8 (loaded[3].val >>> 8))
    sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range
    hm₀ hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇
  simp only at hread
  -- The `.toNat` of the concatenated read equals `Word.toNat loaded`.
  have hconcat_toNat :
      (BitVec.ofNat 8 (loaded[3].val >>> 8) ++ BitVec.ofNat 8 loaded[3].val ++
        BitVec.ofNat 8 (loaded[2].val >>> 8) ++ BitVec.ofNat 8 loaded[2].val ++
        BitVec.ofNat 8 (loaded[1].val >>> 8) ++ BitVec.ofNat 8 loaded[1].val ++
        BitVec.ofNat 8 (loaded[0].val >>> 8) ++ BitVec.ofNat 8 loaded[0].val).toNat
        = Word.toNat loaded := by
    rw [byteConcat8_toNat_eq_Word_toNat loaded[0] loaded[1] loaded[2] loaded[3] h0 h1 h2 h3,
      Word.toNat_def, Word.toNat_def]
    simp
  -- The `extend_value` (unsigned, 8→64 with no extension) of the read equals `Word.toBitVec64 loaded`.
  have hextend : extend_value true
        (BitVec.ofNat 8 (loaded[3].val >>> 8) ++ BitVec.ofNat 8 loaded[3].val ++
          BitVec.ofNat 8 (loaded[2].val >>> 8) ++ BitVec.ofNat 8 loaded[2].val ++
          BitVec.ofNat 8 (loaded[1].val >>> 8) ++ BitVec.ofNat 8 loaded[1].val ++
          BitVec.ofNat 8 (loaded[0].val >>> 8) ++ BitVec.ofNat 8 loaded[0].val)
        = Word.toBitVec64 loaded := by
    apply BitVec.toNat_inj.mp
    rw [Word.toBitVec64_toNat hloaded, ← hconcat_toNat]
    simp only [extend_value, if_true, zero_extend, Sail.BitVec.zeroExtend]
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    have := (BitVec.ofNat 8 (loaded[3].val >>> 8) ++ BitVec.ofNat 8 loaded[3].val ++
          BitVec.ofNat 8 (loaded[2].val >>> 8) ++ BitVec.ofNat 8 loaded[2].val ++
          BitVec.ofNat 8 (loaded[1].val >>> 8) ++ BitVec.ofNat 8 loaded[1].val ++
          BitVec.ofNat 8 (loaded[0].val >>> 8) ++ BitVec.ofNat 8 loaded[0].val).isLt
    omega
  -- Unfold `sp` in the read result so its state matches the post-`nextPC`-write record below.
  rw [hsp] at hread
  -- Final simplification: thread the PC read + `nextPC` write, discharge the `width ≤ xlen_bytes`
  -- assert, resolve the read via `hread`, and match the `extend_value` write against
  -- `wX_bits rd (Word.toBitVec64 loaded)` via `hextend`.
  simp [spec_ld, sp1_ld, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, PreSail.assert, hread, hextend]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- **End-to-end composition.** From the `LoadDouble` chip's prover assumptions (the operand `isU64`s
and the valid/aligned/non-reserved 48-bit address) plus the decode + register/PC reads + the eight
memory bytes (the read returns the loaded word — offline-memory consistency) plus the read-fits-in-
physical-memory bound, the RISC-V Sail `LD` execution agrees with the SP1 chip emulation. The loaded
word is the chip's `memory_access.prev_value` column. The memory analogue of
`AddBridge.add_chip_reaches_sail`. -/
theorem ld_chip_reaches_sail
    (input : LoadDoubleChip.Inputs (ZMod p)) (cols : Extracted.LoadDoubleColumns (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_assum : LoadDoubleChip.Assumptions input data)
    (h_imm : Word.toBitVec64 input.op_c_imm = BitVec.signExtend 64 imm)
    (h_hi : Word.toNat input.op_b_val + Word.toNat input.op_c_imm + 8 ≤ 2 ^ 48)
    (hloaded : Word.isU64 cols.memory_access.prev_value)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (hmem₀ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[0].val))
    (hmem₁ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[0].val >>> 8)))
    (hmem₂ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 2]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[1].val))
    (hmem₃ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 3]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[1].val >>> 8)))
    (hmem₄ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 4]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[2].val))
    (hmem₅ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 5]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[2].val >>> 8)))
    (hmem₆ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 6]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[3].val))
    (hmem₇ : s.mem[(Word.toBitVec64 input.op_b_val + BitVec.signExtend 64 imm).toNat + 7]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[3].val >>> 8))) :
    (spec_ld imm rs1_idx rd_idx).run s
      = (sp1_ld rd_idx pc cols.memory_access.prev_value).run s := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  obtain ⟨h_b, h_c, _h_fits48, h_nonres, h_align48, _h_pv_isu64⟩ := h_assum
  have hreg : (Word.toBitVec64 input.op_b_val).toNat = Word.toNat input.op_b_val :=
    Word.toBitVec64_toNat h_b
  have hoff : (BitVec.signExtend 64 imm).toNat = Word.toNat input.op_c_imm := by
    rw [← h_imm]; exact Word.toBitVec64_toNat h_c
  refine correct_load_double_native rs1_idx rd_idx imm (Word.toBitVec64 input.op_b_val)
    cols.memory_access.prev_value pc s hs hconfig h_pc h_rs1 ?_ ?_ ?_ ?_ hloaded
    hmem₀ hmem₁ hmem₂ hmem₃ hmem₄ hmem₅ hmem₆ hmem₇
  · -- alignment: `sum % 8 = 0` from the chip's `sum % 2^48 % 8 = 0`
    rwa [hreg, hoff, ← Nat.mod_mod_of_dvd _ (by norm_num : (8 : ℕ) ∣ 2 ^ 48)]
  · -- fits in 64 bits (from the read-fits bound)
    rw [hreg, hoff]; omega
  · -- read fits in the 48-bit physical window
    rwa [hreg, hoff]
  · -- non-reserved: `2^16 ≤ (reg_val + offset).toNat`, no wrap since `sum < 2^48`
    rw [BitVec.toNat_add, hreg, hoff, Nat.mod_eq_of_lt (by omega)]; omega

end SP1Clean.LoadSail

namespace SP1Clean.LoadDoubleChip

open SP1Clean.LoadSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **LoadDouble's `ChipKind` registration** (LD). Straight-line `view`, I-type adapter, gating selector
`is_real`, rd write-back the loaded 8-byte word `memory_access.prev_value`, opcode 35. `sailEquiv`
quantifies the prover `data` and the chip `Assumptions inp data` internally (keeping the field `data`-free),
together with the decode/fits/`isU64` facts, the rs1/PC reads, and the eight loaded bytes; `reaches_sail`
is `ld_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "LoadDouble"
  Inputs := LoadDoubleChip.Inputs
  Cols := Extracted.LoadDoubleColumns
  view := fun inp _cols => ⟨inp.state,
    #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, inp.is_real, inp.memory_access.prev_value, 35, .regWrite⟩
  chipSpec := fun inp cols data => LoadDoubleChip.Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (data : ProverData (ZMod p)) (rs1 rd : BitVec 5) (imm : BitVec 12)
      (pc : BitVec 64),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    LoadDoubleChip.Assumptions inp data →
    Word.toBitVec64 inp.op_c_imm = BitVec.signExtend 64 imm →
    Word.toNat inp.op_b_val + Word.toNat inp.op_c_imm + 8 ≤ 2 ^ 48 →
    Word.isU64 cols.memory_access.prev_value →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[0].val) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[0].val >>> 8)) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 2]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[1].val) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 3]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[1].val >>> 8)) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 4]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[2].val) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 5]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[2].val >>> 8)) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 6]?
      = some (BitVec.ofNat 8 cols.memory_access.prev_value[3].val) →
    s.mem[(Word.toBitVec64 inp.op_b_val + BitVec.signExtend 64 imm).toNat + 7]?
      = some (BitVec.ofNat 8 (cols.memory_access.prev_value[3].val >>> 8)) →
    (spec_ld imm rs1 rd).run s = (sp1_ld rd pc cols.memory_access.prev_value).run s
  reaches_sail := fun inp cols _data s _h_real _h_chip data rs1 rd imm pc hs hconfig h_assum h_imm h_hi
      hloaded h_pc h_rs1 hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 =>
    ld_chip_reaches_sail inp cols data rs1 rd imm pc s hs hconfig h_assum h_imm h_hi hloaded h_pc h_rs1
      hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7

end SP1Clean.LoadDoubleChip
