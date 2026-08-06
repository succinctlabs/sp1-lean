import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.LoadWordChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for LoadWord (LW / LWU)

`correct_load_word_native` proves the RISC-V Sail execution of a width-4 `LOAD`
(`execute_LOAD` with `width = 4`, `is_unsigned` = false for `LW` / true for `LWU`) agrees with the SP1
chip's emulation (write `nextPC = pc + 4` and the extended loaded word into `rd`), given the register/PC
reads, the four selected memory bytes, alignment/fits/range facts, and the `extend_value` equation tying
the read to the written word. The width-4 analogue of `correct_load_double_native`, threading
`SailMem.run_vmem_read_of_width_4'`.

`lw_chip_reaches_sail` then discharges the `extend_value` equation from the `LoadWordChip` columns: the
selected 32-bit half `selected_word` and its high bit `msb` extend (sign for `LW`, zero for `LWU`) to the
written word `#v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]`. -/

open LeanRV64D.Defs
namespace SP1Clean.LoadWordSail

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Byte-concatenation + extension lemmas -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The little-endian concatenation of the four bytes of two 16-bit limbs equals `x + y·2^16`. -/
private lemma toNat_concat_word_bytes [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) :
    (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat =
      x.val + y.val * 65536 := by
  have hx_hi : x.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_hi : y.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hx_decomp : x.val % 256 + (x.val >>> 8) * 256 = x.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_decomp : y.val % 256 + (y.val >>> 8) * 256 = y.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (2 ^ 8 : ℕ) = 256 from rfl]
  have hx_hi_mod : x.val >>> 8 % 256 = x.val >>> 8 := Nat.mod_eq_of_lt hx_hi
  have hy_hi_mod : y.val >>> 8 % 256 = y.val >>> 8 := Nat.mod_eq_of_lt hy_hi
  rw [hx_hi_mod, hy_hi_mod]
  rw [show y.val >>> 8 <<< 8 ||| y.val % 256 = y.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  rw [show y.val <<< 8 ||| x.val >>> 8 = y.val * 256 + x.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hx_hi, Nat.shiftLeft_eq]]
  rw [show (y.val * 256 + x.val >>> 8) <<< 8 ||| x.val % 256 =
      (y.val * 256 + x.val >>> 8) * 256 + x.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := hx_decomp
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Zero-extension (LWU) of the 32-bit concatenation is the word `#v[x, y, 0, 0]`. -/
private lemma zeroExtend64_ofNat32_concat [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) :
    Sail.BitVec.zeroExtend (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) 64 =
      Word.toBitVec64 #v[x, y, (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; ring

omit [Fact (2 ^ 17 < p)] in
/-- Sign-extension (LW), low half: when `y < 2^15` the sign bit is `0`, giving `#v[x, y, 0, 0]`. -/
private lemma signExtend64_ofNat32_concat_of_lt_32768 [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : y.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes x y hx hy]
    simp only [decide_eq_false_iff_not, not_le]; change _ < 2 ^ 31; omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; ring

/-- Sign-extension (LW), high half: when `y ≥ 2^15` the sign bit is `1`, giving `#v[x, y, 65535, 65535]`. -/
private lemma signExtend64_ofNat32_concat_of_ge_32768 [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : 32768 ≤ y.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes x y hx hy]
    simp only [decide_eq_true_eq]; change 2 ^ 31 ≤ _; omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h65535 : (65535 : ZMod p).val = 65535 := val_65535_zmod_p
  rw [h65535, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change x.val + y.val * 2 ^ 16 + (2 ^ 64 - 2 ^ (8 + 8 + 8 + 8)) =
    x.val + y.val * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

/-! ## The Sail bridge -/

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-4 Sail `LOAD`. -/
noncomputable def spec_lw (imm : BitVec 12) (rs1 rd : BitVec 5) (is_unsigned : Bool) :
    SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned (width := 4)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the extended loaded word into `rd`. -/
def sp1_lw (rd : BitVec 5) (pc : BitVec 64) (val64 : BitVec 64) : SailM ExecutionResult := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits (.Regidx rd) val64
  pure RETIRE_SUCCESS

/-- Core correctness: a width-4 Sail `LOAD` reading the four bytes `data₀..₃` at the (4-aligned)
address agrees with writing `extend_value is_unsigned <read>` to `rd`. This statement is purely about
`BitVec`s / the `SailState`, so it is independent of the field `p`. -/
theorem correct_load_word_native
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (is_unsigned : Bool) (data₀ data₁ data₂ data₃ : BitVec 8) (val64 : BitVec 64)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 4 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hext : extend_value is_unsigned (data₃ ++ data₂ ++ data₁ ++ data₀) = val64)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃) :
    (spec_lw imm rs1_idx rd_idx is_unsigned).run s = (sp1_lw rd_idx pc val64).run s := by
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
  have hm₀ : sp.mem[(reg_val + BitVec.signExtend 64 imm).toNat]?
      = some data₀ := by rwa [hmem_eq]
  have hm₁ : sp.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some data₁ := by rwa [hmem_eq]
  have hm₂ : sp.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]?
      = some data₂ := by rwa [hmem_eq]
  have hm₃ : sp.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]?
      = some data₃ := by rwa [hmem_eq]
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 4 = true := by
    rwa [is_aligned_vaddr_iff_mod]
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 4 (by omega) h_lo h_hi
  have hread := run_vmem_read_of_width_4' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ data₂ data₃ sp hsp_init hsp_rs1 h_align' hsp_config h_in_range
    hm₀ hm₁ hm₂ hm₃
  simp only at hread
  rw [hsp] at hread
  simp [spec_lw, sp1_lw, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, PreSail.assert, hread, hext]
  rfl

/-- **End-to-end composition.** From the `LoadWord` chip prover assumptions + decode + register/PC reads
+ the four selected memory bytes, a width-4 Sail `LOAD` (sign-extended for `LW`, zero-extended for `LWU`)
agrees with the SP1 chip emulation writing `#v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]`
to `rd`. -/
theorem lw_chip_reaches_sail
    (input : LoadWordChip.Inputs (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (is_unsigned : Bool)
    (hsel0 : input.selected_word[0].val < 65536) (hsel1 : input.selected_word[1].val < 65536)
    (hmsb : input.msb = if input.selected_word[1].val ≥ 32768 then 1 else 0)
    (h_unsigned_msb : is_unsigned = true → input.msb = 0)
    (reg_val : BitVec 64)
    (h_aligned : (reg_val + BitVec.signExtend 64 imm).toNat % 4 = 0)
    (h_hi : (reg_val + BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]?
      = some (BitVec.ofNat 8 input.selected_word[0].val))
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (input.selected_word[0].val >>> 8)))
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]?
      = some (BitVec.ofNat 8 input.selected_word[1].val))
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]?
      = some (BitVec.ofNat 8 (input.selected_word[1].val >>> 8))) :
    (spec_lw imm rs1_idx rd_idx is_unsigned).run s
      = (sp1_lw rd_idx pc (Word.toBitVec64
          #v[input.selected_word[0], input.selected_word[1], 65535 * input.msb, 65535 * input.msb])).run s := by
  -- the `extend_value` equation: sign-extend (LW) or zero-extend (LWU) the read = the written word.
  have hext : extend_value is_unsigned
      (BitVec.ofNat 8 (input.selected_word[1].val >>> 8) ++ BitVec.ofNat 8 input.selected_word[1].val ++
        BitVec.ofNat 8 (input.selected_word[0].val >>> 8) ++ BitVec.ofNat 8 input.selected_word[0].val)
      = Word.toBitVec64 #v[input.selected_word[0], input.selected_word[1],
          65535 * input.msb, 65535 * input.msb] := by
    cases hu : is_unsigned with
    | true =>
      have hmsb0 : input.msb = 0 := h_unsigned_msb (by rw [hu])
      simp only [extend_value, if_true, zero_extend, hmsb0, mul_zero]
      exact zeroExtend64_ofNat32_concat _ _ hsel0 hsel1
    | false =>
      simp only [extend_value, Bool.false_eq_true, if_false, sign_extend, Sail.BitVec.signExtend]
      by_cases hge : input.selected_word[1].val ≥ 32768
      · rw [hmsb, if_pos hge, mul_one]
        exact signExtend64_ofNat32_concat_of_ge_32768 _ _ hsel0 hsel1 hge
      · rw [hmsb, if_neg hge, mul_zero]
        exact signExtend64_ofNat32_concat_of_lt_32768 _ _ hsel0 hsel1 (by omega)
  exact correct_load_word_native rs1_idx rd_idx imm reg_val is_unsigned
    (BitVec.ofNat 8 input.selected_word[0].val) (BitVec.ofNat 8 (input.selected_word[0].val >>> 8))
    (BitVec.ofNat 8 input.selected_word[1].val) (BitVec.ofNat 8 (input.selected_word[1].val >>> 8))
    _ pc s hs hconfig h_pc h_rs1 h_aligned h_hi h_lo hext hmem₀ hmem₁ hmem₂ hmem₃

end SP1Clean.LoadWordSail

namespace SP1Clean.LoadWordChip

open SP1Clean.LoadWordSail
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **The LoadWord `rdWrite ≡ extend_value` identity**, 2-way over LW (sign) / LWU (zero).
The sign bit `msb` is the high bit of the TOP limb `selected_word[1]`; the read is the 4-byte
little-endian word. Reuses the same-file `LoadWordSail` 32-bit extend lemmas. The LWU-zero
condition is keyed on `is_lw = 0` (SP1's gate is `msb·(is_lw−1) = 0`). -/
lemma loadWord_hval (input : Inputs (ZMod p)) (isU : Bool)
    (hsel0 : input.selected_word[0].val < 65536) (hsel1 : input.selected_word[1].val < 65536)
    (h_lw_msb : input.is_lw = 1 → input.msb = if input.selected_word[1].val ≥ 32768 then 1 else 0)
    (h_lwu_msb : input.is_lw = 0 → input.msb = 0)
    (hcase : (input.is_lw = 1 ∧ input.is_lwu = 0 ∧ isU = false)
        ∨ (input.is_lwu = 1 ∧ input.is_lw = 0 ∧ isU = true)) :
    Word.toBitVec64 (#v[input.selected_word[0], input.selected_word[1],
        65535 * input.msb, 65535 * input.msb] : Word (ZMod p))
      = extend_value isU (BitVec.ofNat 8 (input.selected_word[1].val >>> 8)
          ++ BitVec.ofNat 8 input.selected_word[1].val
          ++ BitVec.ofNat 8 (input.selected_word[0].val >>> 8)
          ++ BitVec.ofNat 8 input.selected_word[0].val) := by
  rcases hcase with ⟨hlw, _, rfl⟩ | ⟨hlwu, hlw, rfl⟩
  · -- LW (signed)
    have hmsbeq := h_lw_msb hlw
    simp only [extend_value, Bool.false_eq_true, if_false, sign_extend, Sail.BitVec.signExtend]
    by_cases hge : input.selected_word[1].val ≥ 32768
    · rw [hmsbeq, if_pos hge]; simp only [mul_one]
      exact (LoadWordSail.signExtend64_ofNat32_concat_of_ge_32768 _ _ hsel0 hsel1 hge).symm
    · rw [hmsbeq, if_neg hge]; simp only [mul_zero]
      exact (LoadWordSail.signExtend64_ofNat32_concat_of_lt_32768 _ _ hsel0 hsel1 (by omega)).symm
  · -- LWU (unsigned): is_lw = 0
    rw [h_lwu_msb hlw]
    simp only [extend_value, if_true, zero_extend, mul_zero]
    exact (LoadWordSail.zeroExtend64_ofNat32_concat _ _ hsel0 hsel1).symm

/-- **LoadWord's committed bus view** — standalone (identical to the former inline `kind.view`).
Straight-line `next_pc = pc+4`, ITypeReader adapter,
`rdWrite = #v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]`, opcode
`is_lw·31 + is_lwu·34`, `commit = .regWrite`. -/
def rowView (inp : Inputs (ZMod p)) (_cols : LoadWordChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨inp.state, #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, LoadWordChip.isReal inp,
    #v[inp.selected_word[0], inp.selected_word[1], 65535 * inp.msb, 65535 * inp.msb],
    inp.is_lw * 31 + inp.is_lwu * 34, .regWrite⟩

/-- LoadWord's exact aligned RAM-access projection. -/
def ramAccessView (inp : Inputs (ZMod p)) (cols : LoadWordChip.Columns (ZMod p)) :
    Trace.RamAccessView (ZMod p) :=
  { compareLow := inp.memory_access.access_timestamp.compare_low
    prevHigh := inp.memory_access.access_timestamp.prev_high
    prevLow := inp.memory_access.access_timestamp.prev_low
    diffLow := inp.memory_access.access_timestamp.diff_low_limb
    diffHigh := inp.memory_access.access_timestamp.diff_high_limb
    address := AddressOperation.alignedValue
      ⟨inp.op_b_val, inp.op_c_imm, 0, 0, inp.offset_bit, LoadWordChip.isReal inp⟩
      cols.address_operation
    priorValue := inp.memory_access.prev_value
    newValue := inp.memory_access.prev_value }

/-- **LoadWord's `advanceReady` bundle**: routing (`op_a ≠ 0`), the low-pc-limb bound, the LW/LWU
one-hot, the two loaded-limb bounds (`selected_word[i] < 2^16`), the **4-byte alignment**, the
address bounds, and the **four-byte memory-read binding**. -/
def AdvanceReady (inp : Inputs (ZMod p)) (_cols : LoadWordChip.Columns (ZMod p))
    (_prog : GuestProgram) (s : SailState) : Prop :=
  inp.adapter.op_a ≠ 0 ∧
  (inp.state.pc[0]).val < 2 ^ 16 ∧
  ((inp.is_lw = 1 ∧ inp.is_lwu = 0) ∨ (inp.is_lwu = 1 ∧ inp.is_lw = 0)) ∧
  inp.selected_word[0].val < 65536 ∧ inp.selected_word[1].val < 65536 ∧
  (Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat % 4 = 0 ∧
  (Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat + 4 ≤ 2 ^ 48 ∧
  2 ^ 16 ≤ (Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat ∧
  s.mem[(Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat]? = some (BitVec.ofNat 8 inp.selected_word[0].val) ∧
  s.mem[(Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat + 1]?
      = some (BitVec.ofNat 8 (inp.selected_word[0].val >>> 8)) ∧
  s.mem[(Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat + 2]? = some (BitVec.ofNat 8 inp.selected_word[1].val) ∧
  s.mem[(Word.toBitVec64 inp.adapter.op_b_memory.prev_value
      + Word.toBitVec64 inp.adapter.op_c_imm).toNat + 3]?
      = some (BitVec.ofNat 8 (inp.selected_word[1].val >>> 8))

/-- **The width/sign pin for the width-4 loads** (LW · LWU) — `advance_of_load_width4`'s `hpin`.
Stated over loose `isU` so both flag branches of `advance` below cite it instead of re-running the
`loadOpcode` case split against the whole `advance` context (that inline `simp_all` was the file's
entire elaboration budget). The `Model/Semantics/Decode.lean` `storeOpcode_pin_one` analogue. -/
private lemma loadOpcode_pin_four (isU : Bool) (w' : word_width) (u' : Bool)
    (h : (loadOpcode w' u').toNat = (loadOpcode 4 isU).toNat) : w' = 4 ∧ u' = isU := by
  simp only [loadOpcode] at h
  cases isU <;> cases u' <;> split_ifs at h with h1 h2 h4 <;>
    simp_all [SP1Clean.Soundness.Opcode.toNat, beq_iff_eq]

/-- **`LoadWordChip.advance`** — the per-LoadWord-row `try_step` lift (SC Phase 4). 2-way LW/LWU
flag dispatch fixing `isU`; each branch derives the opcode (31/34 = LW/LWU) and the
`rdWrite ≡ extend_value` identity (`loadWord_hval`) from the chip `Spec`, then feeds
`advance_of_load_width4` with the memory binding / bounds / alignment / routing carried in
`advanceReady`. The LWU-zero fact is derived from the `Spec`'s `msb·(is_lw−1) = 0` gate at
`is_lw = 0`. `hreal` unused. -/
theorem advance (inp : Inputs (ZMod p)) (cols : LoadWordChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) (prog : GuestProgram) (s : SailState)
    (_hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : AdvanceReady inp cols prog s) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hnonX0, hpc0, hflag, hsel0, hsel1, h_aligned, h_hi, h_lo,
    hmem₀, hmem₁, hmem₂, hmem₃⟩ := hready
  obtain ⟨_h_addr, _h_mem, h_msb_spec, _h_it, _h_limbsel, _h_op_a_0,
    h_lw_gate, _h_lw_bin, _h_lwu_bin, _h_real_bin⟩ := hspec
  obtain ⟨_hmsbbin, hmsbeq⟩ := h_msb_spec
  set r := rowView inp cols with hr
  rcases hflag with ⟨hlw, hlwu⟩ | ⟨hlwu, hlw⟩
  · -- LW : isU = false, opcode 31
    refine advance_of_load_width4 false (BitVec.ofNat 8 inp.selected_word[0].val)
      (BitVec.ofNat 8 (inp.selected_word[0].val >>> 8)) (BitVec.ofNat 8 inp.selected_word[1].val)
      (BitVec.ofNat 8 (inp.selected_word[1].val >>> 8))
      (loadOpcode_pin_four false) hcfg hrom hpcread hvalb hdecrom
      (by show inp.is_lw * 31 + inp.is_lwu * 34 = _
          rw [hlw, hlwu]; simp only [one_mul, zero_mul, add_zero]
          show (31 : ZMod p) = ((loadOpcode 4 false).toNat : ZMod p)
          rw [show (loadOpcode 4 false).toNat = 31 from by decide]; norm_num)
      rfl rfl hnonX0 hpc0 rfl h_aligned h_hi h_lo hmem₀ hmem₁ hmem₂ hmem₃ ?_ rfl rfl
    exact loadWord_hval inp false hsel0 hsel1 (fun h1 => hmsbeq h1)
      (fun h => by rw [h, zero_sub, mul_neg_one, neg_eq_zero] at h_lw_gate; exact h_lw_gate)
      (Or.inl ⟨hlw, hlwu, rfl⟩)
  · -- LWU : isU = true, opcode 34
    refine advance_of_load_width4 true (BitVec.ofNat 8 inp.selected_word[0].val)
      (BitVec.ofNat 8 (inp.selected_word[0].val >>> 8)) (BitVec.ofNat 8 inp.selected_word[1].val)
      (BitVec.ofNat 8 (inp.selected_word[1].val >>> 8))
      (loadOpcode_pin_four true) hcfg hrom hpcread hvalb hdecrom
      (by show inp.is_lw * 31 + inp.is_lwu * 34 = _
          rw [hlw, hlwu]; simp only [one_mul, zero_mul, zero_add]
          show (34 : ZMod p) = ((loadOpcode 4 true).toNat : ZMod p)
          rw [show (loadOpcode 4 true).toNat = 34 from by decide]; norm_num)
      rfl rfl hnonX0 hpc0 rfl h_aligned h_hi h_lo hmem₀ hmem₁ hmem₂ hmem₃ ?_ rfl rfl
    exact loadWord_hval inp true hsel0 hsel1 (fun h1 => hmsbeq h1)
      (fun h => by rw [h, zero_sub, mul_neg_one, neg_eq_zero] at h_lw_gate; exact h_lw_gate)
      (Or.inr ⟨hlwu, hlw, rfl⟩)

def kind : Soundness.ChipKind p where
  name := "LoadWord"
  Inputs := LoadWordChip.Inputs
  Cols := LoadWordChip.Columns
  view := rowView
  ramAccess := fun inp cols => some (ramAccessView inp cols)
  chipSpec := fun inp cols data => LoadWordChip.Spec inp cols data
  advanceReady := AdvanceReady
  advance := some (PLift.up advance)

end SP1Clean.LoadWordChip
