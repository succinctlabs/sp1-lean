import SP1Clean.Soundness.StateConsistency

/-! # Surfacing `is_real ∈ {0, 1}` per chip row

Every SP1Clean chip's `Spec` carries a clause of the form
`is_real * (is_real - 1) = 0` (sometimes written on the sub-opcode
sum for chips without an explicit `is_real` column — Branch, Mul,
Lt, ShiftLeft, ShiftRight, LoadX0, LoadByte, LoadHalf, LoadWord).

This file provides:

- A generic field-level `binary_of_assertZero` lemma deriving
  `x ∈ {0, 1}` from `x * (x - 1) = 0`.
- A trace-level predicate `TraceIsRealBinary` asserting that the
  `is_real` projection of every chip row's `stateAccess` is in
  `{0, 1}`.

The discharge of `TraceIsRealBinary` from each chip's `Spec` is a
deferred per-chip case analysis (20 chips × one-conjunct
projection), structurally analogous to the `TraceClkValid` and
`TraceStateValid` bundled hypotheses in
`MemoryConsistencyClock.lean` and `StateConsistency.lean`.

`TraceIsRealBinary` is the hook by which Phase C's multiplicity-
gating lemmas (`SP1Clean.Multiplicity`) fire at the trace level — any
per-row `send`/`receive` with `mult = (stateAccess row).is_real` can
be turned into a stateless-table membership claim. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime]

/-- Generic field-level binarity: in a `ZMod p` for prime `p`,
`x * (x - 1) = 0` gives `x = 0 ∨ x = 1`. -/
theorem binary_of_assertZero (x : ZMod p) (h : x * (x - 1) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with hx | hxm1
  · exact Or.inl hx
  · exact Or.inr (by linear_combination hxm1)

/-- Variant of `binary_of_assertZero` for the disjunction form
`x = 0 ∨ x - 1 = 0` (used by Bitwise's `Spec` for the
`is_xor + is_or + is_and` sum). -/
theorem binary_of_disjunction (x : ZMod p) (h : x = 0 ∨ x - 1 = 0) :
    x = 0 ∨ x = 1 := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

variable [Fact (2 ^ 17 < p)]

/-- Trace-level `is_real` binarity: every row's `stateAccess.is_real`
projection is in `{0, 1}`.

Deferred discharge: this is implied by `∀ row ∈ rows, row.Spec`
(every chip's `Spec` contains the corresponding `is_real * (is_real -
1) = 0` clause), via per-chip case analysis that selects the right
conjunct. Pending that case analysis, `TraceIsRealBinary` is supplied
by the verifier as part of the trace-shape bundle. -/
def TraceIsRealBinary (rows : List (ChipRow p)) : Prop :=
  ∀ row ∈ rows, (ChipRow.stateAccess row).is_real = 0 ∨
                (ChipRow.stateAccess row).is_real = 1

/-! ## Per-chip discharge lemmas

Each lemma takes the chip-row's `Spec` and projects the `is_real *
(is_real - 1) = 0` conjunct (or the `is_real = 0 ∨ is_real - 1 = 0`
disjunction for Bitwise), then applies `binary_of_assertZero` /
`binary_of_disjunction`. Conjuncts are extracted via `tauto`, which is
robust to variation in conjunct ordering across chips. -/

theorem is_real_binary_add (cols : SP1Clean.Add.AddCols (ZMod p))
    (h : SP1Clean.Add.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  change SP1Clean.Add.Assertion.FormalSpec cols at h
  -- New Gated FormalSpec (RawSpec conjunct dropped): is_real binarity
  -- lives in `CPUState.Gated.Spec`'s first conjunct (the binary-gate
  -- sub-circuit emission). Path: h.1 = CPUState.Gated.Spec; h.1.1 =
  -- `cols.is_real * (cols.is_real - 1) = 0`.
  exact binary_of_assertZero _ h.1.1

theorem is_real_binary_addi (cols : SP1Clean.Addi.AddiCols (ZMod p))
    (h : SP1Clean.Addi.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  change SP1Clean.Addi.FormalSpec cols at h
  -- New Gated FormalSpec: is_real binarity lives in `CPUState.Gated.Spec`'s
  -- first conjunct (mirror of Add).
  exact binary_of_assertZero _ h.2.1.1

theorem is_real_binary_addw (cols : SP1Clean.Addw.AddwCols (ZMod p))
    (h : SP1Clean.Addw.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  change SP1Clean.Addw.FormalSpec cols at h
  -- New Gated FormalSpec: is_real binarity lives in `CPUState.Gated.Spec`'s
  -- first conjunct (mirror of Add/Addi).
  exact binary_of_assertZero _ h.2.1.1

theorem is_real_binary_bitwise (cols : SP1Clean.Bitwise.BitwiseCols (ZMod p))
    (h : SP1Clean.Bitwise.assertion.Spec cols) :
    cols.is_xor + cols.is_or + cols.is_and = 0 ∨
    cols.is_xor + cols.is_or + cols.is_and = 1 := by
  apply binary_of_assertZero
  change SP1Clean.Bitwise.Assertion.FormalSpec cols at h
  unfold SP1Clean.Bitwise.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_branch (cols : SP1Clean.Branch.BranchCols (ZMod p))
    (h : SP1Clean.Branch.assertion.Spec cols) :
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu = 0 ∨
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu = 1 := by
  apply binary_of_assertZero
  change SP1Clean.Branch.Assertion.FormalSpec cols at h
  unfold SP1Clean.Branch.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_divRem (cols : SP1Clean.DivRem.DivRemCols (ZMod p))
    (h : SP1Clean.DivRem.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.DivRem.Assertion.FormalSpec cols at h
  unfold SP1Clean.DivRem.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_jal (cols : SP1Clean.Jal.JalCols (ZMod p))
    (h : SP1Clean.Jal.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.Jal.Assertion.FormalSpec cols at h
  unfold SP1Clean.Jal.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_jalr (cols : SP1Clean.Jalr.JalrCols (ZMod p))
    (h : SP1Clean.Jalr.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.Jalr.Assertion.FormalSpec cols at h
  unfold SP1Clean.Jalr.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_loadByte (cols : SP1Clean.LoadByte.LoadByteCols (ZMod p))
    (h : SP1Clean.LoadByte.assertion.Spec cols) :
    cols.is_lb + cols.is_lbu = 0 ∨ cols.is_lb + cols.is_lbu = 1 := by
  apply binary_of_assertZero
  change SP1Clean.LoadByte.Assertion.FormalSpec cols at h
  unfold SP1Clean.LoadByte.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_loadDouble
    (cols : SP1Clean.LoadDouble.LoadDoubleCols (ZMod p))
    (h : SP1Clean.LoadDouble.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.LoadDouble.Assertion.FormalSpec cols at h
  unfold SP1Clean.LoadDouble.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_loadHalf
    (cols : SP1Clean.LoadHalf.LoadHalfCols (ZMod p))
    (h : SP1Clean.LoadHalf.assertion.Spec cols) :
    cols.is_lh + cols.is_lhu = 0 ∨ cols.is_lh + cols.is_lhu = 1 := by
  apply binary_of_assertZero
  change SP1Clean.LoadHalf.Assertion.FormalSpec cols at h
  unfold SP1Clean.LoadHalf.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_loadWord
    (cols : SP1Clean.LoadWord.LoadWordCols (ZMod p))
    (h : SP1Clean.LoadWord.assertion.Spec cols) :
    cols.is_lw + cols.is_lwu = 0 ∨ cols.is_lw + cols.is_lwu = 1 := by
  apply binary_of_assertZero
  change SP1Clean.LoadWord.Assertion.FormalSpec cols at h
  unfold SP1Clean.LoadWord.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_loadX0
    (cols : SP1Clean.LoadX0.LoadX0Cols (ZMod p))
    (h : SP1Clean.LoadX0.assertion.Spec cols) :
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld = 0 ∨
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld = 1 := by
  apply binary_of_assertZero
  change SP1Clean.LoadX0.Assertion.FormalSpec cols at h
  unfold SP1Clean.LoadX0.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_lt (cols : SP1Clean.Lt.LtCols (ZMod p))
    (h : SP1Clean.Lt.assertion.Spec cols) :
    cols.is_slt + cols.is_sltu = 0 ∨ cols.is_slt + cols.is_sltu = 1 := by
  apply binary_of_assertZero
  change SP1Clean.Lt.Assertion.FormalSpec cols at h
  unfold SP1Clean.Lt.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_mul (cols : SP1Clean.Mul.MulCols (ZMod p))
    (h : SP1Clean.Mul.assertion.Spec cols) :
    cols.is_mul + cols.is_mulh + cols.is_mulw +
      cols.is_mulhsu + cols.is_mulhu = 0 ∨
    cols.is_mul + cols.is_mulh + cols.is_mulw +
      cols.is_mulhsu + cols.is_mulhu = 1 := by
  apply binary_of_assertZero
  change SP1Clean.Mul.Assertion.FormalSpec cols at h
  unfold SP1Clean.Mul.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_shiftLeft
    (cols : SP1Clean.ShiftLeft.ShiftLeftCols (ZMod p))
    (h : SP1Clean.ShiftLeft.assertion.Spec cols) :
    cols.is_sll + cols.is_sllw = 0 ∨ cols.is_sll + cols.is_sllw = 1 := by
  apply binary_of_assertZero
  change SP1Clean.ShiftLeft.Assertion.FormalSpec cols at h
  unfold SP1Clean.ShiftLeft.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_shiftRight
    (cols : SP1Clean.ShiftRight.ShiftRightCols (ZMod p))
    (h : SP1Clean.ShiftRight.assertion.Spec cols) :
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 0 ∨
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1 := by
  apply binary_of_assertZero
  change SP1Clean.ShiftRight.Assertion.FormalSpec cols at h
  unfold SP1Clean.ShiftRight.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_storeByte
    (cols : SP1Clean.StoreByte.StoreByteCols (ZMod p))
    (h : SP1Clean.StoreByte.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.StoreByte.Assertion.FormalSpec cols at h
  unfold SP1Clean.StoreByte.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_storeDouble
    (cols : SP1Clean.StoreDouble.StoreDoubleCols (ZMod p))
    (h : SP1Clean.StoreDouble.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.StoreDouble.Assertion.FormalSpec cols at h
  unfold SP1Clean.StoreDouble.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_storeHalf
    (cols : SP1Clean.StoreHalf.StoreHalfCols (ZMod p))
    (h : SP1Clean.StoreHalf.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.StoreHalf.Assertion.FormalSpec cols at h
  unfold SP1Clean.StoreHalf.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_storeWord
    (cols : SP1Clean.StoreWord.StoreWordCols (ZMod p))
    (h : SP1Clean.StoreWord.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.StoreWord.Assertion.FormalSpec cols at h
  unfold SP1Clean.StoreWord.Assertion.FormalSpec at h
  tauto

theorem is_real_binary_sub (cols : SP1Clean.Sub.SubCols (ZMod p))
    (h : SP1Clean.Sub.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  change SP1Clean.Sub.Assertion.FormalSpec cols at h
  -- New Gated FormalSpec: is_real binarity lives in `CPUState.Gated.Spec`'s
  -- first conjunct (mirror of Add).
  exact binary_of_assertZero _ h.2.1.1

theorem is_real_binary_subw (cols : SP1Clean.Subw.SubwCols (ZMod p))
    (h : SP1Clean.Subw.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  change SP1Clean.Subw.Assertion.FormalSpec cols at h
  -- New Gated FormalSpec: is_real binarity lives in `CPUState.Gated.Spec`'s
  -- first conjunct (mirror of Add).
  exact binary_of_assertZero _ h.2.1.1

theorem is_real_binary_uType (cols : SP1Clean.UType.UTypeCols (ZMod p))
    (h : SP1Clean.UType.assertion.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 := by
  apply binary_of_assertZero
  change SP1Clean.UType.Assertion.FormalSpec cols at h
  unfold SP1Clean.UType.Assertion.FormalSpec at h
  tauto

omit [Fact (2 ^ 17 < p)] in
/-- Boundary chip discharge: the `is_real * (is_real - 1) = 0` clause is
the only conjunct in `MemoryGlobal.Spec` (Phase 4 minimal placeholder),
so it projects via `binary_of_assertZero` directly. -/
theorem is_real_binary_memInitFinalize
    (cols : SP1Clean.MemoryGlobal.MemoryGlobalCols (ZMod p))
    (h : SP1Clean.MemoryGlobal.Spec cols) :
    cols.is_real = 0 ∨ cols.is_real = 1 :=
  binary_of_assertZero _ h

/-- The full discharge: every chip-row `Spec` implies `is_real ∈ {0, 1}`
on the row's `stateAccess`. Replaces the previously-bundled
`TraceIsRealBinary` hypothesis with a constructive proof. -/
theorem traceIsRealBinary_of_chip_specs (rows : List (ChipRow p))
    (h_specs : ∀ row ∈ rows, ChipRow.Spec row) :
    TraceIsRealBinary rows := by
  intro row h_mem
  have hs := h_specs row h_mem
  cases row with
  | add cols => exact is_real_binary_add cols hs
  | addi cols => exact is_real_binary_addi cols hs
  | addw cols => exact is_real_binary_addw cols hs
  | bitwise cols => exact is_real_binary_bitwise cols hs
  | branch cols => exact is_real_binary_branch cols hs
  | divRem cols => exact is_real_binary_divRem cols hs
  | jal cols => exact is_real_binary_jal cols hs
  | jalr cols => exact is_real_binary_jalr cols hs
  | loadByte cols => exact is_real_binary_loadByte cols hs
  | loadDouble cols => exact is_real_binary_loadDouble cols hs
  | loadHalf cols => exact is_real_binary_loadHalf cols hs
  | loadWord cols => exact is_real_binary_loadWord cols hs
  | loadX0 cols => exact is_real_binary_loadX0 cols hs
  | lt cols => exact is_real_binary_lt cols hs
  | mul cols => exact is_real_binary_mul cols hs
  | shiftLeft cols => exact is_real_binary_shiftLeft cols hs
  | shiftRight cols => exact is_real_binary_shiftRight cols hs
  | storeByte cols => exact is_real_binary_storeByte cols hs
  | storeDouble cols => exact is_real_binary_storeDouble cols hs
  | storeHalf cols => exact is_real_binary_storeHalf cols hs
  | storeWord cols => exact is_real_binary_storeWord cols hs
  | sub cols => exact is_real_binary_sub cols hs
  | subw cols => exact is_real_binary_subw cols hs
  | uType cols => exact is_real_binary_uType cols hs
  | memInit cols => exact is_real_binary_memInitFinalize cols hs
  | memFinalize cols => exact is_real_binary_memInitFinalize cols hs

end SP1Clean.Soundness
