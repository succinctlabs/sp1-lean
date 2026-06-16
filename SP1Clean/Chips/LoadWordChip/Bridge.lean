import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Chips.LoadWordChip.Formal
import SP1Clean.Soundness.ChipRow

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

namespace SP1Clean.LoadWordSail

open Sail LeanRV64D LeanRV64D.Functions
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

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
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

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
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
  have h65535 : (65535 : ZMod p).val = 65535 := by
    rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  rw [h65535, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change x.val + y.val * 2 ^ 16 + (2 ^ 64 - 2 ^ (8 + 8 + 8 + 8)) =
    x.val + y.val * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

/-! ## The Sail bridge -/

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the width-4 Sail `LOAD`. -/
noncomputable def spec_lw (imm : BitVec 12) (rs1 rd : BitVec 5) (is_unsigned : Bool) :
    SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned (width := 4)

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the extended loaded word into `rd`. -/
def sp1_lw (rd : BitVec 5) (pc : BitVec 64) (val64 : BitVec 64) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits (.Regidx rd) val64
  pure RETIRE_SUCCESS

set_option maxHeartbeats 10000000 in
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
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hext : extend_value is_unsigned (data₃ ++ data₂ ++ data₁ ++ data₀) = val64)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃) :
    (spec_lw imm rs1_idx rd_idx is_unsigned).run s = (sp1_lw rd_idx pc val64).run s := by
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
  have hm₂ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2]?
      = some data₂ := by rw [hmem_eq, ← hadd]; exact hmem₂
  have hm₃ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 3]?
      = some data₃ := by rw [hmem_eq, ← hadd]; exact hmem₃
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 4 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 4 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_4' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ data₂ data₃ sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range
    hm₀ hm₁ hm₂ hm₃
  simp only at hread
  rw [hsp] at hread
  simp [spec_lw, sp1_lw, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread, hext]

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
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
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
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
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
    _ pc s hs hconfig h_pc h_rs1 h_aligned h_fits h_hi h_lo hext hmem₀ hmem₁ hmem₂ hmem₃

end SP1Clean.LoadWordSail

namespace SP1Clean.LoadWordChip

open SP1Clean.LoadWordSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **LoadWord's `ChipKind` registration** — enters LW / LWU rows into the heterogeneous trace and the
soundness capstone. `view` is the straight-line shape (`next_pc = pc + 4`), the I-type adapter
(`ITypeReader.toAdapterView`: `op_b` the rs1 base read, `op_c = op_c_imm` the immediate, `imm_c = 1`),
the gating selector `is_real = is_lw + is_lwu`, the **extended loaded word**
`#v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]` as the rd write-back, and opcode
`31·is_lw + 34·is_lwu`. `sailEquiv` quantifies the row's PC/rs1 reads, the Sail-state init/mem-config,
the alignment/fits/range facts, the limb/`msb` decode facts, and the four selected memory bytes
internally; `reaches_sail` is `lw_chip_reaches_sail` (the load value is committed in the columns, so the
`is_real`/`Spec` hypotheses are unused). -/
def kind : Soundness.ChipKind p where
  name := "LoadWord"
  Inputs := LoadWordChip.Inputs
  Cols := Extracted.LoadWordColumns
  view := fun inp _cols => ⟨inp.state,
    #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, LoadWordChip.isReal inp,
    #v[inp.selected_word[0], inp.selected_word[1], 65535 * inp.msb, 65535 * inp.msb],
    inp.is_lw * 31 + inp.is_lwu * 34⟩
  chipSpec := fun inp cols data => LoadWordChip.Spec inp cols data
  sailEquiv := fun inp _cols s => ∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc reg_val : BitVec 64)
      (is_unsigned : Bool),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    inp.selected_word[0].val < 65536 → inp.selected_word[1].val < 65536 →
    inp.msb = (if inp.selected_word[1].val ≥ 32768 then 1 else 0) →
    (is_unsigned = true → inp.msb = 0) →
    (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0 →
    reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64 →
    reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 →
    2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some reg_val →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some (BitVec.ofNat 8 inp.selected_word[0].val) →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]?
      = some (BitVec.ofNat 8 (inp.selected_word[0].val >>> 8)) →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some (BitVec.ofNat 8 inp.selected_word[1].val) →
    s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]?
      = some (BitVec.ofNat 8 (inp.selected_word[1].val >>> 8)) →
    (spec_lw imm rs1 rd is_unsigned).run s
      = (sp1_lw rd pc (Word.toBitVec64
          #v[inp.selected_word[0], inp.selected_word[1], 65535 * inp.msb, 65535 * inp.msb])).run s
  reaches_sail := fun inp _cols _data s _h_real _h_chip rs1 rd imm pc reg_val is_unsigned hs hconfig
      hsel0 hsel1 hmsb h_unsigned_msb h_al h_fits h_hi h_lo h_pc h_rs1 hm0 hm1 hm2 hm3 =>
    lw_chip_reaches_sail inp rs1 rd imm pc s hs hconfig is_unsigned hsel0 hsel1 hmsb h_unsigned_msb
      reg_val h_al h_fits h_hi h_lo h_pc h_rs1 hm0 hm1 hm2 hm3

end SP1Clean.LoadWordChip
