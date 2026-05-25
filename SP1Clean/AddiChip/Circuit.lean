import SP1Clean.AddiChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `AddiChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract:
- `AddOperation` arithmetic `Spec` (carry chain).
- CPU-state byte bounds (`cpuStateSpec`).
- Full I-type reader spec (`itypeReaderSpec` — program + memory + bounds).
- Two trailing scalar gates (`is_real` binary, `op_a_0 = 0`).
- Pure BitVec `RV64.add` semantic (conditional on `is_real = 1`).

`Assertion.main` composes three subcircuits — `AddOp.assertion`,
`CPUState.assertion`, `ITypeReader.assertion` (the last itself wrapping
`ProgramTable.assertion` + 2 `OperandAccess.assertion` calls) — mirroring
`SP1Chips/Addi/Constraints.lean`'s single `ITypeReader.constraints` call
and the upstream Rust `AddiChip::eval`'s `ITypeReader::eval` invocation 1:1.

The per-row Sail-monadic equivalence to `_root_.Addi.spec_addi` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.AddiChip.SailBridge.sail_correct_of_formalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `AddiChip::eval(builder, cols)`
1:1: one `AddOp.assertion` + one `CPUState.assertion` + one
`ITypeReader.assertion` + two scalar gates. -/
@[reducible]
def main (cols : Var AddiCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, _adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_imm, op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ITypeReader.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 1, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.ITypeReader.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddiCols unit where
  name := "SP1Clean.Addi"
  main := main
  -- Computed from main; ITypeReader contributes 48 (2 assertionGated × 24).
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[29]` in the constraint compiler's emission). This is a
type-level / TrustMode-marker fact that the circuit doesn't enforce; it's
needed by `fromMain_toMain` (`Lemmas.lean`) for the cols→Main→cols
round-trip. -/
def Assumptions (cols : AddiCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.Addi.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.Addi.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop_sub, h_cpu_sub, h_itr_sub, h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  have h_addop := h_addop_sub trivial
  have h_cpu := h_cpu_sub trivial
  have h_itr := h_itr_sub trivial
  refine ⟨h_addop, h_cpu, h_itr, by linear_combination h_isreal, h_op_a_0, ?_⟩
  -- BitVec `RV64.addi` conjunct: combine AddOp.spec (carry chain →
  -- `+` equation) with i_type_constraints' sign-extension identity
  -- (`op_c_imm_bv = signExtend 64 imm12`) to recover the addi form.
  intro _h_is_real_eq
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Unpack itypeReaderSpec to get (a) the trusted_instr clause for the
  -- sign-extension fact, and (b) isU64 of op_b plus the 4 op_c_imm
  -- limb bounds.
  obtain ⟨h_ti, _, _, h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _, _, _,
          _h_diff_a, _h_diff_b, _h_ts_b, _h_ts_a, _h_isU64_a_idx, h_isU64_b_idx, _⟩ := h_itr
  -- Sign-extension fact from i_type_constraints' third conjunct:
  -- `Word.toBitVec64 op_c_imm = signExtend 64 (BitVec.ofNat 12 op_c_imm[0].val)`.
  -- The trusted_instr predicate unfolds via @[simp] to
  -- (imm_consts) ∧ (op_b_consts) ∧ (sign_ext_eq); `.2.2` projects the sign_ext_eq.
  have h_signExt : Word.toBitVec64
        #v[input_adapter_op_c_imm[0], input_adapter_op_c_imm[1],
           input_adapter_op_c_imm[2], input_adapter_op_c_imm[3]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 input_adapter_op_c_imm[0].val) := by
    have := h_ti
    simp only [Opcode.trusted_instr, Opcode.ofNat, ZMod.val_one,
               i_type_constraints] at this
    exact this.2.2
  -- Convert isU64_b from the index-form to whole-Word form.
  have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
    (SP1Clean.ITypeReader.Assertion.isU64_iff_index_form _).mpr h_isU64_b_idx
  -- Convert the 4 immediate-limb field bounds into the underlying .val < 65536
  -- form expected by Word.isU64_of_cases.
  have h65 : (65536 : ZMod p).val = 65536 := by
    have hp : 2 ^ 17 < p := Fact.out
    rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hb0 : input_adapter_op_c_imm[0].val < 65536 := by
    have : input_adapter_op_c_imm[0].val < (65536 : ZMod p).val := h_c0_lt
    rwa [h65] at this
  have hb1 : input_adapter_op_c_imm[1].val < 65536 := by
    have : input_adapter_op_c_imm[1].val < (65536 : ZMod p).val := h_c1_lt
    rwa [h65] at this
  have hb2 : input_adapter_op_c_imm[2].val < 65536 := by
    have : input_adapter_op_c_imm[2].val < (65536 : ZMod p).val := h_c2_lt
    rwa [h65] at this
  have hb3 : input_adapter_op_c_imm[3].val < 65536 := by
    have : input_adapter_op_c_imm[3].val < (65536 : ZMod p).val := h_c3_lt
    rwa [h65] at this
  have h_isU64_c : Word.isU64 input_adapter_op_c_imm :=
    Word.isU64_of_cases hb0 hb1 hb2 hb3
  have h_allHold : (AddOperation.constraints
        input_adapter_op_b_memory_prev_value
        input_adapter_op_c_imm
        { value := Vector.map (Expression.eval env) input_var_op_a_write_value } 1).allHold :=
    (SP1Clean.AddOp.iff_sp1 _ _ _).mpr h_addop
  -- AddOperation.spec gives `op_a_write_value.toBitVec64 = execute_RTYPE_pure_w b c .ADD`
  -- which reduces (by rfl) to `b.toBitVec64 + c.toBitVec64`.
  have ⟨_, h_bv⟩ := AddOperation.spec h_isU64_b h_isU64_c h_allHold
  rw [show execute_RTYPE_pure_w input_adapter_op_b_memory_prev_value
            input_adapter_op_c_imm rop.ADD =
            input_adapter_op_b_memory_prev_value.toBitVec64 +
              input_adapter_op_c_imm.toBitVec64 from rfl] at h_bv
  -- `Word.toBitVec64 op_c_imm = Word.toBitVec64 #v[op_c_imm[0..3]]` by
  -- whole-Vector vs indexed equivalence. Combined with h_signExt this
  -- converts the 4-limb form to signExtend 64 (12-bit imm).
  have h_op_c_unfold :
      Word.toBitVec64 input_adapter_op_c_imm =
        Word.toBitVec64
          #v[input_adapter_op_c_imm[0], input_adapter_op_c_imm[1],
             input_adapter_op_c_imm[2], input_adapter_op_c_imm[3]] := by
    congr 1
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  -- RV64.addi imm rs1 = BitVec.add rs1 (signExtend 64 imm) = rs1 + signExtend 64 imm.
  simp only [RV64.addi]
  rw [h_bv, h_op_c_unfold, h_signExt]
  rfl

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop, h_cpu, h_itr, h_isreal, h_op_a_0, _h_rv64add⟩ := h_spec
  unfold id at *
  refine ⟨⟨trivial, h_addop⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_itr⟩,
          by linear_combination h_isreal, h_op_a_0⟩

end Assertion

/-- The full Clean `FormalAssertion` for `AddiChip`. Single subcircuit
composition (`AddOp.assertion + CPUState.assertion + ITypeReader.assertion
+ 2 scalar gates`) backing one unified `Spec` whose last conjunct is the
pure BitVec `RV64.add` semantic (auditable at a glance). Per-row Sail
equivalence is derived externally via `sail_correct_of_formalSpec`
(`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) AddiCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addi
