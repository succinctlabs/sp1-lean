module

public import SP1Clean.Circuits.Types.Mul
public import SP1Clean.FormalModel.Contracts.Readers
public import SP1Clean.Semantics.ISA.RV64

/-! # Multiplication row semantics

The row contract composes register-reader obligations with RV64 multiplication and unique
instruction selection. Its five ISA identities connect the public meaning to the arithmetic
forms used by the circuit proof. No witness generator or circuit implementation is imported.
-/

@[expose] public section

namespace SP1Clean.MulChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Exactly one multiplication variant is selected. The circuit derives this on active rows
from selector booleanity and their sum. -/
def SelectorOneHot (s : SelectorValues (ZMod p)) : Prop :=
  (s.is_mul = 1 ∧ s.is_mulh = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulhsu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulh = 1 ∧ s.is_mul = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulhsu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulhu = 1 ∧ s.is_mul = 0 ∧ s.is_mulh = 0 ∧ s.is_mulhsu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulhsu = 1 ∧ s.is_mul = 0 ∧ s.is_mulh = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulw = 1 ∧ s.is_mul = 0 ∧ s.is_mulh = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulhsu = 0)

/-- High-half kernel: extracting bits `64..127` of the *wide* (129-bit) product of two extensions
equals `setWidth 64` of the *narrow* (128-bit) product shifted right by 64. The two products agree on
their low 128 bits (`setWidth 128` of the wide product is the narrow product), so they agree on bits
`64..127`. The `MULH`/`MULHSU` bridges instantiate this; `MULHU`'s product is already 128-bit. -/
private lemma high64_mul (b' c' : BitVec 129) (b'' c'' : BitVec 128)
    (hb : b'' = BitVec.setWidth 128 b') (hc : c'' = BitVec.setWidth 128 c') :
    BitVec.extractLsb 127 64 (b' * c') = ((b'' * c'') >>> 64).setWidth 64 := by
  have hmul : b'' * c'' = BitVec.setWidth 128 (b' * c') := by
    rw [hb, hc]; exact (BitVec.setWidth_mul b' c' (by omega)).symm
  rw [hmul, BitVec.setWidth_ushiftRight_eq_extractLsb,
    BitVec.extractLsb'_setWidth_of_le (by decide)]
  rfl

/-- `RV64.mul rs2 rs1 = rs1 * rs2` (commuted into the gadget's `b * c` form). -/
lemma rv64_mul_eq (x y : BitVec 64) : RV64.mul x y = y * x := by
  rw [RV64.mul, BitVec.mul_comm]

/-- `RV64.mulh`'s high-64-bit signed×signed product equals the gadget's `>>>64 |>.setWidth 64` form. -/
lemma rv64_mulh_eq (x y : BitVec 64) :
    RV64.mulh x y = ((y.signExtend 128 * x.signExtend 128) >>> 64).setWidth 64 := by
  simp only [RV64.mulh]
  apply high64_mul
  all_goals
    ext i hi
    simp [BitVec.getElem_signExtend, show i < 129 by omega]

/-- `RV64.mulhu`'s high-64-bit unsigned×unsigned product (its inner `extractLsb' 0 128` is the
identity on the 128-bit product) equals the gadget's `setWidth 128`-product `>>>64 |>.setWidth 64` form. -/
lemma rv64_mulhu_eq (x y : BitVec 64) :
    RV64.mulhu x y = ((y.setWidth 128 * x.setWidth 128) >>> 64).setWidth 64 := by
  simp only [RV64.mulhu, BitVec.extractLsb'_eq_self,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  rfl

/-- `RV64.mulhsu`'s high-64-bit signed(rs1)×unsigned(rs2) product equals the gadget's
`signExtend 128 (rs1) * setWidth 128 (rs2)` `>>>64 |>.setWidth 64` form. -/
lemma rv64_mulhsu_eq (x y : BitVec 64) :
    RV64.mulhsu x y = ((y.signExtend 128 * x.setWidth 128) >>> 64).setWidth 64 := by
  simp only [RV64.mulhsu]
  apply high64_mul
  · ext i hi
    simp [BitVec.getElem_signExtend, show i < 129 by omega]
  · exact (BitVec.setWidth_setWidth_of_le x (by decide)).symm

/-- `RV64.mulw`'s low-32 product sign-extended to 64 equals the gadget's
`((rs1 * rs2).setWidth 32).signExtend 64` form. -/
lemma rv64_mulw_eq (x y : BitVec 64) :
    RV64.mulw x y = ((y * x).setWidth 32).signExtend 64 := by
  simp only [RV64.mulw]
  congr 1
  exact (BitVec.setWidth_mul y x (by omega)).symm

/-- Reader obligations, binary activity and the selected RV64 multiplication result.
Every active row selects exactly one variant. Arithmetic and selection are unrestricted on
padding; the reader contract retains its own gated and ungated obligations. Operands follow
RV64's argument order: the second register value comes first. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13 + cols.is_mulhsu * 14
        + cols.is_mulw * 24,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_mul = 1 →
      Word.toBitVec64 cols.a = RV64.mul (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulh = 1 →
      Word.toBitVec64 cols.a = RV64.mulh (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulhu = 1 →
      Word.toBitVec64 cols.a = RV64.mulhu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulhsu = 1 →
      Word.toBitVec64 cols.a = RV64.mulhsu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulw = 1 →
      Word.toBitVec64 cols.a = RV64.mulw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))) ∧
  (input.is_real = 1 → SelectorOneHot (selectors cols))

end SP1Clean.MulChip
