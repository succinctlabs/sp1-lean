import SP1Clean.Semantics.Specs.Chips.Branch
import SP1Clean.Native.Operations.AddOperation.Populate
import SP1Clean.Circuits.Gadgets.LtSigned
import ToClean.Circuit.WitnessCombinator
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The BRANCH chip row as a `GeneralFormalCircuit`

Conditional control flow (opcodes 40–45: BEQ/BNE/BLT/BGE/BLTU/BGEU): `next_pc` is data-dependent
(`pc + sign_extend(imm)` taken, `pc + 4` fall-through, chosen by the compare). The row composes
`LtOperationSigned` (mode `is_blt + is_bge`), `CPUState`, and `ITypeReaderImmutable`, then states
SP1's eight inline gated carry equations for the two possible PC additions exactly. `AddOperation`
is used only as proof-oriented witness-generation mathematics; it is not a Branch AIR subcircuit and
does not contribute interactions. The six opcode flags sum to `is_real` (one-hot); the branch opcode
is threaded via `ProverHint`. Implements pinned SP1 v6.4.0's `Branch` `air.rs::eval`. -/

namespace SP1Clean.BranchChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] in
/-- `14 < p`, so the alignment `Range` byte-row width column `14` round-trips through `byteRowSpec_range`. -/
lemma h14p : (14 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The `next_pc` witness as exportable IR: the `is_branching`-selected blend of the two
`AddOperation`-style carry chains (branch target `pc + imm`, fall-through `pc + 4`), limbs 0–2.
Deliberately **not** `@[circuit_norm]`; `nextPcIR_eval` is the boundary. -/
def nextPcIR (pc : Vector (Expression (ZMod p)) 3) (imm : Word (Expression (ZMod p)))
    (is_branching is_real : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 3 :=
  let bs0 : Witgen.U64Expr (ZMod p) := pc[0].val + imm[0].val
  let bs1 : Witgen.U64Expr (ZMod p) := pc[1].val + imm[1].val + bs0 / 65536
  let bs2 : Witgen.U64Expr (ZMod p) := pc[2].val + imm[2].val + bs1 / 65536
  let fs0 : Witgen.U64Expr (ZMod p) := pc[0].val + (4 : Witgen.U64Expr (ZMod p))
  let fs1 : Witgen.U64Expr (ZMod p) := pc[1].val + fs0 / 65536
  let fs2 : Witgen.U64Expr (ZMod p) := pc[2].val + fs1 / 65536
  let br : Witgen.FExpr (ZMod p) := .expr is_branching
  let rl : Witgen.FExpr (ZMod p) := .expr is_real
  .ofFExprs #v[br * (bs0 % 65536).toField + (rl - br) * (fs0 % 65536).toField,
               br * (bs1 % 65536).toField + (rl - br) * (fs1 % 65536).toField,
               br * (bs2 % 65536).toField + (rl - br) * (fs2 % 65536).toField]

omit [Fact (2 ^ 17 < p)] in
private lemma word4_isU64 {v : Word (ZMod p)} (h : Word.isU64 v) :
    v[0].val < 2 ^ 16 ∧ v[1].val < 2 ^ 16 ∧ v[2].val < 2 ^ 16 ∧ v[3].val < 2 ^ 16 :=
  Word.lt_cases_of_isU64 h

/-- Evaluating the `next_pc` IR is exactly the value-level blend of the two `AddOperation.populate`
words, elementwise — the per-cell shape the completeness seam's witness obligations arrive in. The
`isU64` bounds keep the u64-sorted carry chains from wrapping. -/
theorem nextPcIR_eval (env : ProverEnvironment (ZMod p))
    (pc : Vector (Expression (ZMod p)) 3) (imm : Word (Expression (ZMod p)))
    (is_branching is_real : Expression (ZMod p))
    (vpc : Vector (ZMod p) 3) (vimm : Word (ZMod p))
    (hpc : #v[Expression.eval env.toEnvironment pc[0], Expression.eval env.toEnvironment pc[1],
              Expression.eval env.toEnvironment pc[2]] = vpc)
    (himm : #v[Expression.eval env.toEnvironment imm[0], Expression.eval env.toEnvironment imm[1],
               Expression.eval env.toEnvironment imm[2],
               Expression.eval env.toEnvironment imm[3]] = vimm)
    (hpcU : Word.isU64 (#v[vpc[0], vpc[1], vpc[2], 0] : Word (ZMod p)))
    (himmU : vimm.isU64) (k : ℕ) (hk : k < 3) :
    ((nextPcIR pc imm is_branching is_real).eval env)[k]
      = Expression.eval env.toEnvironment is_branching
          * (AddOperation.populate #v[vpc[0], vpc[1], vpc[2], 0] vimm)[k]
        + (Expression.eval env.toEnvironment is_real
            - Expression.eval env.toEnvironment is_branching)
          * (AddOperation.populate #v[vpc[0], vpc[1], vpc[2], 0]
              (#v[4, 0, 0, 0] : Word (ZMod p)))[k] := by
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨hu0, hu1, hu2, -⟩ := word4_isU64 hpcU
  obtain ⟨hi0, hi1, hi2, hi3⟩ := word4_isU64 himmU
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hu0 hu1 hu2
  have hP0 : Expression.eval env.toEnvironment pc[0] = vpc[0] := by rw [← hpc]; simp
  have hP1 : Expression.eval env.toEnvironment pc[1] = vpc[1] := by rw [← hpc]; simp
  have hP2 : Expression.eval env.toEnvironment pc[2] = vpc[2] := by rw [← hpc]; simp
  have hI0 : Expression.eval env.toEnvironment imm[0] = vimm[0] := by rw [← himm]; simp
  have hI1 : Expression.eval env.toEnvironment imm[1] = vimm[1] := by rw [← himm]; simp
  have hI2 : Expression.eval env.toEnvironment imm[2] = vimm[2] := by rw [← himm]; simp
  have h4 : ((4 : ZMod p)).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by push_cast; ring,
      ZMod.val_natCast_of_lt (by omega)]
  interval_cases k <;>
    simp only [nextPcIR, AddOperation.populate, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm,
      hP0, hP1, hP2, hI0, hI1, hI2, h4, ZMod.val_zero]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the `next_pc` IR (no bounds — a congruence). -/
theorem nextPcIR_congr (env env' : ProverEnvironment (ZMod p))
    (pc : Vector (Expression (ZMod p)) 3) (imm : Word (Expression (ZMod p)))
    (is_branching is_real : Expression (ZMod p))
    (hP : ∀ (i : ℕ) (_ : i < 3),
      Expression.eval env.toEnvironment pc[i] = Expression.eval env'.toEnvironment pc[i])
    (hI : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment imm[i] = Expression.eval env'.toEnvironment imm[i])
    (hBr : Expression.eval env.toEnvironment is_branching
      = Expression.eval env'.toEnvironment is_branching)
    (hRl : Expression.eval env.toEnvironment is_real
      = Expression.eval env'.toEnvironment is_real) :
    (nextPcIR pc imm is_branching is_real).eval env
      = (nextPcIR pc imm is_branching is_real).eval env' := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [nextPcIR, circuit_norm, -Witgen.u64Wrap,
      hP 0 (by omega), hP 1 (by omega), hP 2 (by omega),
      hI 0 (by omega), hI 1 (by omega), hI 2 (by omega), hBr, hRl]

/-- The rs1 register value (the `op_a` source read's prior value) as a 4-limb word, from the inputs. -/
def rs1WordInput (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
     input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]

/-- The rs2 register value (the `op_b` source read's prior value) as a 4-limb word, from the inputs. -/
def rs2WordInput (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
     input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]

/-- Compose the branch comparison certificate, decision and selected next PC.

Selectors are ordinary inputs. Clean witnesses the comparison first, then computes
the decision from those cells and feeds it to the existing next-PC witness IR. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let rs1WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
       input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]
  let rs2WordV : Word (Expression (ZMod p)) :=
    #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
       input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
  let is_beq := input.isBeq; let is_bne := input.isBne; let is_blt := input.isBlt
  let is_bge := input.isBge; let is_bltu := input.isBltu; let is_bgeu := input.isBgeu
  let lt_cols ← witness (var := Var Circuits.Types.LtOperationSigned)
    (LtOperationSigned.populateFE rs1WordV rs2WordV (is_blt + is_bge) input.is_real)
  let cmp := lt_cols
  let decision := branchDecision is_beq is_bne is_blt is_bge is_bltu is_bgeu
    cmp.result.u16_compare_operation.bit
    (cmp.result.u16_flags[0] + cmp.result.u16_flags[1]
      + cmp.result.u16_flags[2] + cmp.result.u16_flags[3])
  let is_branching ← witnessField (.expr decision)
  let next_pc ← witnessVectorIR 3
    (nextPcIR #v[input.state.pc[0], input.state.pc[1], input.state.pc[2]]
      input.adapter.op_c_imm is_branching input.is_real)
  assertion LtOperationSigned.circuit ⟨rs1WordV, rs2WordV, lt_cols, is_blt + is_bge, input.is_real⟩
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  -- Activity must be visible to the shallow byte-channel obligations.
  assertZero (sum * (sum - 1))
  is_branching * (is_branching - 1) === 0
  sum * (is_branching - decision) === 0
  let baseInv : Expression (ZMod p) :=
    Expression.const ((65536 : ZMod p)⁻¹)
  let taken0 :=
    (input.state.pc[0] + input.adapter.op_c_imm[0] - next_pc[0]) *
      baseInv
  let taken1 :=
    (input.state.pc[1] + input.adapter.op_c_imm[1] - next_pc[1] +
      taken0) * baseInv
  let taken2 :=
    (input.state.pc[2] + input.adapter.op_c_imm[2] - next_pc[2] +
      taken1) * baseInv
  let taken3 := (input.adapter.op_c_imm[3] + taken2) * baseInv
  assertZero (is_branching * (taken0 * (taken0 - 1)))
  assertZero (is_branching * (taken1 * (taken1 - 1)))
  assertZero (is_branching * (taken2 * (taken2 - 1)))
  assertZero (is_branching * (taken3 * (taken3 - 1)))
  let fall0 :=
    (input.state.pc[0] + (4 : Expression (ZMod p)) - next_pc[0]) *
      baseInv
  let fall1 := (input.state.pc[1] - next_pc[1] + fall0) * baseInv
  let fall2 := (input.state.pc[2] - next_pc[2] + fall1) * baseInv
  let fall3 := fall2 * baseInv
  let fallGate := sum - is_branching
  assertZero (fallGate * (fall0 * (fall0 - 1)))
  assertZero (fallGate * (fall1 * (fall1 - 1)))
  assertZero (fallGate * (fall2 * (fall2 - 1)))
  assertZero (fallGate * (fall3 * (fall3 - 1)))
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[next_pc[0], next_pc[1], next_pc[2]], 8, input.is_real⟩
  let opcode := is_beq * 40 + is_bne * 41 + is_blt * 42 + is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  -- `ITypeReaderImmutable` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, opcode⟩
  byteChannel.pullIf input.is_real
    (⟨6, (next_pc[0] * (4 : ZMod p)⁻¹), Expression.const ((14 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, next_pc[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, next_pc[2], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  return ⟨input.state, input.adapter, next_pc,
    is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_branching, cmp⟩

/-- Derive the 14 Rust-owned witness cells and complete four-channel interface from `main`. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit

/-- Completed row: ten comparison cells, the decision and three next-PC limbs. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        Vector.mapRange 3 fun i => var { index := offset + 11 + i },
        input.isBeq, input.isBne, input.isBlt, input.isBge, input.isBltu, input.isBgeu,
        var { index := offset + 10 },
        varFromOffset Circuits.Types.LtOperationSigned offset⟩ :
        Var Columns (ZMod p)) := rfl

set_option linter.unusedSectionVars false in

@[circuit_norm] lemma localLength_eq (input : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength input = 14 := rfl

/-! ### Operand projections, in `circuit_norm`'s own orientation — stated at the **component**
level (the lift simprocs move projections inside `eval` before an input-level lemma could match;
the `ComputableWitnesses` proof projects the struct-level agreement onto these). Not
`@[circuit_norm]`: on Clean `main` the indexing lift (`Expression.eval env cols.pc[i] ~~>
(ProvableStruct.eval env cols).pc[i]`) undoes `Vector.getElem_map` on their right-hand sides, and
the pair loops. -/

theorem eval_statePc {F : Type} [FiniteField F]
    (env : Environment F) (cols : Circuits.Types.CPUState (Expression F)) :
    (ProvableStruct.eval env cols).pc = Vector.map (Expression.eval env) cols.pc := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Readers.CPUState.eval_cols]
  exact ProvableType.eval_fields env _

theorem eval_opCImm {F : Type} [FiniteField F]
    (env : Environment F) (cols : Circuits.Types.ITypeReader (Expression F)) :
    (ProvableStruct.eval env cols).op_c_imm = Vector.map (Expression.eval env) cols.op_c_imm := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Readers.ITypeReader.eval_cols]
  exact ProvableType.eval_fields env _

theorem eval_prevValue {F : Type} [FiniteField F]
    (env : Environment F) (cols : Circuits.Types.RegisterAccessCols (Expression F)) :
    (ProvableStruct.eval env cols).prev_value
      = Vector.map (Expression.eval env) cols.prev_value := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

/-! Input-level operand projections (plain lemmas, applied by `rw` in the `ComputableWitnesses`
proof — deliberately NOT `@[circuit_norm]`, so no simp set ever renormalizes the struct evals). -/

theorem eval_statePcIn {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).state.pc
      = Vector.map (Expression.eval env) input.state.pc := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, Readers.CPUState.eval_cols]
  exact ProvableType.eval_fields env _

theorem eval_opCImmIn {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).adapter.op_c_imm
      = Vector.map (Expression.eval env) input.adapter.op_c_imm := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, Readers.ITypeReader.eval_cols]
  exact ProvableType.eval_fields env _

theorem eval_rs1In {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).adapter.op_a_memory.prev_value
      = Vector.map (Expression.eval env) input.adapter.op_a_memory.prev_value := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, Readers.ITypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

theorem eval_rs2In {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).adapter.op_b_memory.prev_value
      = Vector.map (Expression.eval env) input.adapter.op_b_memory.prev_value := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, Readers.ITypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

/-- Value interpretation of the comparison witness used to compute the branch decision. -/
def populateComparison (input : Inputs (ZMod p)) : Circuits.Types.LtOperationSigned (ZMod p) :=
  LtOperationSigned.populate (rs1WordInput input) (rs2WordInput input)
    (input.isBlt + input.isBge) input.is_real

/-- Value interpretation of the generated taken-branch bit. -/
def populateBranching (input : Inputs (ZMod p)) : ZMod p :=
  let cmp := populateComparison input
  branchDecision input.isBeq input.isBne input.isBlt input.isBge input.isBltu input.isBgeu
    cmp.result.u16_compare_operation.bit
    (cmp.result.u16_flags[0] + cmp.result.u16_flags[1]
      + cmp.result.u16_flags[2] + cmp.result.u16_flags[3])

/-- The taken target word the chip witnesses for `branch_value` (`pc + op_c_imm`, base-2^16). -/
def branchTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] input.adapter.op_c_imm

/-- The fall-through word the chip witnesses for `fall_value` (`pc + 4`, base-2^16). -/
def fallThroughWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] #v[4, 0, 0, 0]

/-- The committed `next_pc` limbs the chip selects: the `is_branching`-mux of the taken/​fall targets,
as a pure function of the inputs and the prover's `is_branching` value (matches the `main` witness). -/
def committedNextPc (input : Inputs (ZMod p)) (br : ZMod p) : Vector (ZMod p) 3 :=
  let b := branchTargetWord input
  let f := fallThroughWord input
  #v[br * b[0] + (input.is_real - br) * f[0],
     br * b[1] + (input.is_real - br) * f[1],
     br * b[2] + (input.is_real - br) * f[2]]

end SP1Clean.BranchChip
