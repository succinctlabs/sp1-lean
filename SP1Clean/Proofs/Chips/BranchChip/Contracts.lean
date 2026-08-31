import SP1Clean.Native.Chips.BranchChip.Defs
import SP1Clean.Soundness.RowView
import Clean.Circuit.Extensions

/-! # Branch chip proof assumptions

The verifier-side operand assumptions and honest-prover witness contract for the exact SP1 Branch
row. These live separately from the circuit proof so `Formal.lean` remains a small packaging and
channel-exposure surface.
-/

namespace SP1Clean.BranchChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands `isU64`; `is_real` and the flag/branch bits are proven from AIR gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64
    (#v[input.adapter.op_a_memory.prev_value[0],
      input.adapter.op_a_memory.prev_value[1],
      input.adapter.op_a_memory.prev_value[2],
      input.adapter.op_a_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64
    (#v[input.adapter.op_b_memory.prev_value[0],
      input.adapter.op_b_memory.prev_value[1],
      input.adapter.op_b_memory.prev_value[2],
      input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64
    (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] :
      Word (ZMod p))

/-- Honest witness-generation assumptions for the exact Rust-shaped Branch row.

The two pure `AddOperation.populate` targets are proof-level witness calculations, not AIR
subcircuits. Their high-limb-zero hypotheses justify the three-limb PC representation used by SP1's
inline carry equations. Complete output ranges are supplied for the three real-row byte pulls.
-/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  let br := hintBranching hint
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (rs1WordInput input) ∧
  Word.isU64 (rs2WordInput input) ∧
  Word.isU64
    (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] :
      Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8,
      is_real := input.is_real } ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 0⟩ ∧
  (branchTargetWord input)[3] = 0 ∧
  (fallThroughWord input)[3] = 0 ∧
  (f[0] = 0 ∨ f[0] = 1) ∧
  (f[1] = 0 ∨ f[1] = 1) ∧
  (f[2] = 0 ∨ f[2] = 1) ∧
  (f[3] = 0 ∨ f[3] = 1) ∧
  (f[4] = 0 ∨ f[4] = 1) ∧
  (f[5] = 0 ∨ f[5] = 1) ∧
  (input.is_real = f[0] + f[1] + f[2] + f[3] + f[4] + f[5]) ∧
  (br = 0 ∨ br = 1) ∧
  (input.is_real = 0 → br = 0) ∧
  (input.is_real = 1 →
    (f[0] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) =
        Word.toBitVec64 (rs2WordInput input))) ∧
    (f[1] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) ≠
        Word.toBitVec64 (rs2WordInput input))) ∧
    (f[2] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt
        (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[3] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt
        (Word.toBitVec64 (rs2WordInput input)) = false)) ∧
    (f[4] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult
        (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[5] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult
        (Word.toBitVec64 (rs2WordInput input)) = false))) ∧
  (input.is_real = 1 →
    ((committedNextPc input br)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
    (committedNextPc input br)[1].val < 2 ^ 16 ∧
    (committedNextPc input br)[2].val < 2 ^ 16)

end SP1Clean.BranchChip

/-! ## Physical opcode discriminant (committed-fragment strengthening)

Unlike the other chips' `Contracts.lean` files, this file sits BELOW the chip's `Formal.lean`
(`Core.lean` imports it — the documented proof-decomposition exception), so neither the bundled
`BranchChip.circuit` nor `Bridge.lean`'s `BranchChip.rowView` is importable here. The physical
view and the opcode fact are therefore stated over the folded `main` assertion system and the
`elaborated.output` row: `physicalCols` is definitionally the component `rowOutput` of
`BranchChip.circuit`, `physicalView` is the inline `rowView` literal at the component `rowInput`,
and `Component.constraintsHold_iff` converts the component-level constraints hypothesis into the
`main`-level one consumed here. -/

namespace SP1Clean.Soundness

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- The completed Branch columns at one physical component row (the folded `elaborated.output`;
definitionally the component `rowOutput` of `BranchChip.circuit`). -/
noncomputable def BranchChip.physicalCols (env : Environment (ZMod p)) :
    BranchChip.Columns (ZMod p) :=
  Eval.eval env
    ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
      (size BranchChip.Inputs))

/-- The completed Branch row view at one physical component row (the inline `BranchChip.rowView`
literal at the component `rowInput`). -/
noncomputable def BranchChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  ⟨(BranchChip.physicalCols env).state,
    #v[(BranchChip.physicalCols env).next_pc[0], (BranchChip.physicalCols env).next_pc[1],
      (BranchChip.physicalCols env).next_pc[2]],
    (BranchChip.physicalCols env).adapter.toAdapterView,
    (valueFromOffset BranchChip.Inputs 0 env).is_real,
    #v[0, 0, 0, 0], BranchChip.branchOpcode (BranchChip.physicalCols env), .noWrite⟩

private theorem BranchChip.isBeqBinaryConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset } * (var { index := offset } - 1) - 0 ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp only [BranchChip.main, circuit_norm]
  iterate 1 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (var { index := offset } * (var { index := offset } - 1)) 0 _

private theorem BranchChip.isBneBinaryConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 1 } * (var { index := offset + 1 } - 1) - 0 ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp only [BranchChip.main, circuit_norm]
  iterate 2 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      (var { index := offset + 1 } * (var { index := offset + 1 } - 1)) 0 _

private theorem BranchChip.isBltBinaryConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 2 } * (var { index := offset + 2 } - 1) - 0 ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp only [BranchChip.main, circuit_norm]
  iterate 3 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      (var { index := offset + 2 } * (var { index := offset + 2 } - 1)) 0 _

private theorem BranchChip.isBgeBinaryConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 3 } * (var { index := offset + 3 } - 1) - 0 ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp only [BranchChip.main, circuit_norm]
  iterate 4 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      (var { index := offset + 3 } * (var { index := offset + 3 } - 1)) 0 _

private theorem BranchChip.isBltuBinaryConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 4 } * (var { index := offset + 4 } - 1) - 0 ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp only [BranchChip.main, circuit_norm]
  iterate 5 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      (var { index := offset + 4 } * (var { index := offset + 4 } - 1)) 0 _

private theorem BranchChip.isBgeuBinaryConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    var { index := offset + 5 } * (var { index := offset + 5 } - 1) - 0 ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp only [BranchChip.main, circuit_norm]
  iterate 6 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      (var { index := offset + 5 } * (var { index := offset + 5 } - 1)) 0 _

private theorem BranchChip.isRealLinkConstraint_mem
    (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_real - (var { index := offset } + var { index := offset + 1 } +
      var { index := offset + 2 } + var { index := offset + 3 } +
      var { index := offset + 4 } + var { index := offset + 5 }) ∈
      ((BranchChip.main input).operations offset).constraints := by
  simp [BranchChip.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- Lift a binary field flag to its `ℕ` value. -/
private theorem flagNatValue {x : ZMod p} (hx : x = 0 ∨ x = 1) :
    ∃ b : ℕ, b ≤ 1 ∧ x = (b : ZMod p) := by
  rcases hx with rfl | rfl
  · exact ⟨0, Nat.zero_le 1, by norm_num⟩
  · exact ⟨1, le_rfl, by norm_num⟩

/-- `Nat.cast` into `ZMod p` is injective below `2 ^ 17 < p`. -/
private theorem natCastSmall_inj {a b : ℕ} (ha : a < 2 ^ 17) (hb : b < 2 ^ 17)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hp : (2 : ℕ) ^ 17 < p := Fact.out
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

/-- A real physical Branch row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). Stated over the folded `main`
assertion system — the component-level hypothesis converts to this one through
`Component.constraintsHold_iff` (see the section comment above). -/
theorem BranchChip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      ((BranchChip.main (varFromOffset BranchChip.Inputs 0)).operations
        (size BranchChip.Inputs)).ConstraintsHold env)
    (real : (BranchChip.physicalView env).is_real = 1) :
    (BranchChip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var BranchChip.Inputs (ZMod p) := varFromOffset BranchChip.Inputs 0
  have g0 := constraints.1 _
    (BranchChip.isBeqBinaryConstraint_mem input (size BranchChip.Inputs))
  have g1 := constraints.1 _
    (BranchChip.isBneBinaryConstraint_mem input (size BranchChip.Inputs))
  have g2 := constraints.1 _
    (BranchChip.isBltBinaryConstraint_mem input (size BranchChip.Inputs))
  have g3 := constraints.1 _
    (BranchChip.isBgeBinaryConstraint_mem input (size BranchChip.Inputs))
  have g4 := constraints.1 _
    (BranchChip.isBltuBinaryConstraint_mem input (size BranchChip.Inputs))
  have g5 := constraints.1 _
    (BranchChip.isBgeuBinaryConstraint_mem input (size BranchChip.Inputs))
  have glink := constraints.1 _
    (BranchChip.isRealLinkConstraint_mem input (size BranchChip.Inputs))
  simp only [eval_sub, Expression.eval, sub_zero] at g0 g1 g2 g3 g4 g5 glink
  obtain ⟨a, ha, hea⟩ := flagNatValue (bool_of_mul_pred g0)
  obtain ⟨b, hb, heb⟩ := flagNatValue (bool_of_mul_pred g1)
  obtain ⟨c, hc, hec⟩ := flagNatValue (bool_of_mul_pred g2)
  obtain ⟨d, hd, hed⟩ := flagNatValue (bool_of_mul_pred g3)
  obtain ⟨e, he, hee⟩ := flagNatValue (bool_of_mul_pred g4)
  obtain ⟨f, hf, hef⟩ := flagNatValue (bool_of_mul_pred g5)
  have inputEq : Eval.eval env input = valueFromOffset BranchChip.Inputs 0 env :=
    eval_varFromOffset_valueFromOffset BranchChip.Inputs 0 env
  have viewIsReal : (BranchChip.physicalView env).is_real =
      Expression.eval env input.is_real := by
    simp only [BranchChip.physicalView]
    rw [← inputEq, BranchChip.eval_inputIsReal]
  have hreal : Expression.eval env input.is_real = 1 := viewIsReal.symm.trans real
  have hsum : env.get (size BranchChip.Inputs) + env.get (size BranchChip.Inputs + 1) +
      env.get (size BranchChip.Inputs + 2) + env.get (size BranchChip.Inputs + 3) +
      env.get (size BranchChip.Inputs + 4) + env.get (size BranchChip.Inputs + 5) = 1 :=
    (sub_eq_zero.mp glink).symm.trans hreal
  have projBeq : (BranchChip.physicalCols env).is_beq = env.get (size BranchChip.Inputs) := by
    simpa only [BranchChip.physicalCols, BranchChip.directOutput_eq, CircuitType.eval_expr,
      Expression.eval] using
      congrArg (fun v : BranchChip.Columns (ZMod p) => v.is_beq)
        (BranchChip.eval_columns env
          ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
            (size BranchChip.Inputs)))
  have projBne : (BranchChip.physicalCols env).is_bne =
      env.get (size BranchChip.Inputs + 1) := by
    simpa only [BranchChip.physicalCols, BranchChip.directOutput_eq, CircuitType.eval_expr,
      Expression.eval] using
      congrArg (fun v : BranchChip.Columns (ZMod p) => v.is_bne)
        (BranchChip.eval_columns env
          ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
            (size BranchChip.Inputs)))
  have projBlt : (BranchChip.physicalCols env).is_blt =
      env.get (size BranchChip.Inputs + 2) := by
    simpa only [BranchChip.physicalCols, BranchChip.directOutput_eq, CircuitType.eval_expr,
      Expression.eval] using
      congrArg (fun v : BranchChip.Columns (ZMod p) => v.is_blt)
        (BranchChip.eval_columns env
          ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
            (size BranchChip.Inputs)))
  have projBge : (BranchChip.physicalCols env).is_bge =
      env.get (size BranchChip.Inputs + 3) := by
    simpa only [BranchChip.physicalCols, BranchChip.directOutput_eq, CircuitType.eval_expr,
      Expression.eval] using
      congrArg (fun v : BranchChip.Columns (ZMod p) => v.is_bge)
        (BranchChip.eval_columns env
          ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
            (size BranchChip.Inputs)))
  have projBltu : (BranchChip.physicalCols env).is_bltu =
      env.get (size BranchChip.Inputs + 4) := by
    simpa only [BranchChip.physicalCols, BranchChip.directOutput_eq, CircuitType.eval_expr,
      Expression.eval] using
      congrArg (fun v : BranchChip.Columns (ZMod p) => v.is_bltu)
        (BranchChip.eval_columns env
          ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
            (size BranchChip.Inputs)))
  have projBgeu : (BranchChip.physicalCols env).is_bgeu =
      env.get (size BranchChip.Inputs + 5) := by
    simpa only [BranchChip.physicalCols, BranchChip.directOutput_eq, CircuitType.eval_expr,
      Expression.eval] using
      congrArg (fun v : BranchChip.Columns (ZMod p) => v.is_bgeu)
        (BranchChip.eval_columns env
          ((BranchChip.elaborated (p := p)).output (varFromOffset BranchChip.Inputs 0)
            (size BranchChip.Inputs)))
  have opcodeEq : (BranchChip.physicalView env).opcode =
      env.get (size BranchChip.Inputs) * 40 + env.get (size BranchChip.Inputs + 1) * 41 +
      env.get (size BranchChip.Inputs + 2) * 42 + env.get (size BranchChip.Inputs + 3) * 43 +
      env.get (size BranchChip.Inputs + 4) * 44 + env.get (size BranchChip.Inputs + 5) * 45 := by
    simp only [BranchChip.physicalView, BranchChip.branchOpcode]
    rw [projBeq, projBne, projBlt, projBge, projBltu, projBgeu]
  rw [hea, heb, hec, hed, hee, hef] at hsum
  have habSum : a + b + c + d + e + f = 1 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast hsum)
  intro hEq
  rw [opcodeEq, hea, heb, hec, hed, hee, hef] at hEq
  have hcontra : a * 40 + b * 41 + c * 42 + d * 43 + e * 44 + f * 45 = 50 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast hEq)
  omega

end SP1Clean.Soundness
