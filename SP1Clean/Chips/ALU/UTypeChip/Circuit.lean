import SP1Clean.Chips.ALU.UTypeChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.JTypeReader
import SP1Clean.Operations.AddOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `UTypeChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract from
`Cols.lean`. Composes three subcircuits — `CPUState.assertion`,
`JTypeReader.Gated.assertion` (which itself bundles `programGated` + one
`RegisterAccess.assertion` for op_a + four `op_a_0 * write_value[i] = 0`
gates), and `AddOp.assertion` gated by `is_real - op_a_0` (so the addition
is only enforced when the chip is active and rd ≠ x0) — plus four inline
scalar gates (is_auipc binary, three `addend[i] - is_auipc * pc[i] = 0`).

The per-row Sail-monadic equivalence to `_root_.UType.spec_lui` /
`spec_auipc` is *not* inside `FormalSpec`; it's derived externally via
`SP1Clean.UTypeChip.SailBridge.sail_correct_of_formalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.UType

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1's `UType.constraints` 1:1 via
three subcircuits — `CPUState.assertion` + `JTypeReader.Gated.assertion`
+ `AddOp.assertion` (gated by `is_real - op_a_0`) — plus four inline
scalar gates (is_auipc binary, three addend gates). The free
`is_real * (is_real - 1) === 0` gate lives inside `JTypeReader.Gated`'s
first conjunct; the four `op_a_0 * add_result[i] === 0` gates and the
program-bus emission are absorbed into `JTypeReader.Gated.Assertion.Spec`. -/
@[reducible]
def main (cols : Var UTypeCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, addend, add_result, is_auipc, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let opcode := is_auipc * 48 + (1 - is_auipc) * 49
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.JTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode, pc, add_result, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.JTypeReader.Gated.Inputs (ZMod p))
  SP1Clean.AddOp.assertion
    (⟨#v[addend[0], addend[1], addend[2], 0], adapter.op_b_imm, add_result,
       is_real - adapter.op_a_0⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  is_auipc * (is_auipc - 1) === 0
  addend[0] - is_auipc * pc[0] === 0
  addend[1] - is_auipc * pc[1] === 0
  addend[2] - is_auipc * pc[2] === 0
  (is_real - 1) * adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) UTypeCols unit where
  name := "SP1Clean.UType"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

/-- Strengthened Assumptions following the JalrChip pattern:
- `is_trusted = is_real` (UserMode TrustMode marker, required by
  `fromMain_toMain` in `Lemmas.lean` for the cols→Main→cols round-trip).
- `is_real = 1` (non-padding row; restricts the FormalAssertion to real
  rows where the AddOp gate `is_real - op_a_0` may fire).
- `Word.isU64 op_b_imm` (operand bound: at the trace level, R/I/J-type
  operands are bounded by the constraint-compiler's column conventions,
  but the bound isn't derivable from `main`'s lookup-derived Specs alone
  without a verbose ZMod-`<`-to-`.val`-`<` conversion; surfacing it here
  keeps the chip's soundness/completeness clean while pushing the bounds
  discharge into the trace-soundness driver). Used by `AddOp.assertion`'s
  Assumptions inside soundness/completeness. -/
def Assumptions (cols : UTypeCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real ∧
  cols.is_real = 1 ∧
  Word.isU64 cols.adapter.op_b_imm

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.UType.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.UType.FormalSpec p

/-- Soundness of `UType.assertion`. Composes the three subcircuit Specs
(`CPUState.Gated`, `JTypeReader.Gated`, `AddOp` with conditional gate
`is_real - op_a_0`) plus 5 inline scalar gates into the unified `FormalSpec`.
The BitVec conjunct (conditional on `is_real = 1 ∧ op_a_0 = 0`) is derived
from `AddOp.assertion.Spec`'s BV64 identity plus the
`Opcode.trusted_instr` sign-extension identity extracted from
`JTypeReader.Gated.Assertion.Spec`'s `ProgramSpec`. Mirrors `JalrChip`'s
canonical recipe (commit `186a456`). -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_trusted, h_is_real, h_isU64_op_b⟩ := h_assumptions
  obtain ⟨h_cpu_sub, h_jtr_sub, h_add_sub, h_isa_bin, h_addend0, h_addend1,
          h_addend2, h_isreal_op_a_0⟩ := h_holds
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Pull h_input apart to expose Expression.eval ↔ input value equalities,
  -- so we can rewrite h_addend{0,1,2} into the canonical `input_addend[i] -
  -- input_is_auipc * input_state_pc[i] = 0` shape.
  obtain ⟨⟨h_e_clk_high, h_e_clk_16_24, h_e_clk_0_16, h_e_pc⟩,
          ⟨h_e_op_a, ⟨h_e_pv, h_e_pl, h_e_dl⟩, h_e_op_a_0, h_e_op_b_imm, h_e_op_c_imm⟩,
          h_e_addend, h_e_add_result, h_e_is_auipc, h_e_is_real,
          h_e_is_trusted⟩ := h_input
  -- Rewrite h_addend{0,1,2} into input_addend / input_state_pc form via
  -- the Vector.map equalities from h_input.
  have h_a0 : input_addend[0] - input_is_auipc * input_state_pc[0] = 0 := by
    have : input_addend[0] = Expression.eval env input_var_addend[0] := by
      rw [← h_e_addend]; simp
    have hp : input_state_pc[0] = Expression.eval env input_var_state_pc[0] := by
      rw [← h_e_pc]; simp
    rw [this, hp]; linear_combination h_addend0
  have h_a1 : input_addend[1] - input_is_auipc * input_state_pc[1] = 0 := by
    have : input_addend[1] = Expression.eval env input_var_addend[1] := by
      rw [← h_e_addend]; simp
    have hp : input_state_pc[1] = Expression.eval env input_var_state_pc[1] := by
      rw [← h_e_pc]; simp
    rw [this, hp]; linear_combination h_addend1
  have h_a2 : input_addend[2] - input_is_auipc * input_state_pc[2] = 0 := by
    have : input_addend[2] = Expression.eval env input_var_addend[2] := by
      rw [← h_e_addend]; simp
    have hp : input_state_pc[2] = Expression.eval env input_var_state_pc[2] := by
      rw [← h_e_pc]; simp
    rw [this, hp]; linear_combination h_addend2
  -- The 5 chip-level scalar gates in canonical sub-form:
  have h_isa_bin' : input_is_auipc * (input_is_auipc - 1) = 0 := by
    linear_combination h_isa_bin
  have h_isreal_op_a_0' : (input_is_real - 1) * input_adapter_op_a_0 = 0 := by
    linear_combination h_isreal_op_a_0
  -- Bridge subcircuit Specs.
  have h_cpu := h_cpu_sub trivial
  have h_jtr := h_jtr_sub trivial
  have h_jtr_copy := h_jtr  -- preserve for the structural conjunct below
  -- Extract op_a_0 binary + pc bounds + Opcode.trusted_instr from h_jtr.
  obtain ⟨_h_gate_jtr, h_prog_disj, _, _, _, _, _⟩ := h_jtr
  have h_ir_ne_zero : input_is_real ≠ 0 := by rw [h_is_real]; exact one_ne_zero
  have h_it_ne_zero : input_adapter_cols_is_trusted ≠ 0 := by
    rw [h_trusted]; exact h_ir_ne_zero
  have h_prog := h_prog_disj.resolve_left h_it_ne_zero
  simp only [SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  obtain ⟨h_ti, _h_op_a_lt, _h_ob, _h_oc,
          h_op_a_0_bin, _h_op_a_0_iff, _h_imm_b, _h_imm_c,
          _h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩ := h_prog
  haveI h65k : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have lt65k : ∀ (x : ZMod p), x < (65536 : ZMod p) → x.val < 65536 :=
    fun x h => by have : x.val < (65536 : ZMod p).val := h; rwa [h65k] at this
  have h_pc_isU64 : Word.isU64
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], (0 : ZMod p)] :=
    Word.isU64_of_cases (lt65k _ h_pc0_lt) (lt65k _ h_pc1_lt)
                        (lt65k _ h_pc2_lt) (by simp [ZMod.val_zero])
  have h_isU64_addend : Word.isU64
      #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)] := by
    rcases mul_eq_zero.mp h_isa_bin' with h0 | h1
    · -- input_is_auipc = 0 → addend = 0.
      have e0 : input_addend[0] = 0 := by
        have := h_a0; rw [h0] at this; linear_combination this
      have e1 : input_addend[1] = 0 := by
        have := h_a1; rw [h0] at this; linear_combination this
      have e2 : input_addend[2] = 0 := by
        have := h_a2; rw [h0] at this; linear_combination this
      rw [show #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)]
            = #v[(0 : ZMod p), 0, 0, 0] from by rw [e0, e1, e2]]
      exact Word.isU64_of_cases (by simp [ZMod.val_zero])
            (by simp [ZMod.val_zero]) (by simp [ZMod.val_zero])
            (by simp [ZMod.val_zero])
    · -- input_is_auipc = 1 → addend = pc.
      have h_iaui_eq : input_is_auipc = 1 := by linear_combination h1
      have e0 : input_addend[0] = input_state_pc[0] := by
        have := h_a0; rw [h_iaui_eq] at this; linear_combination this
      have e1 : input_addend[1] = input_state_pc[1] := by
        have := h_a1; rw [h_iaui_eq] at this; linear_combination this
      have e2 : input_addend[2] = input_state_pc[2] := by
        have := h_a2; rw [h_iaui_eq] at this; linear_combination this
      rw [show #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)]
            = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2],
                 (0 : ZMod p)] from by rw [e0, e1, e2]]
      exact h_pc_isU64
  -- AddOp gate `is_real - op_a_0`: after circuit_proof_start eval, this is
  -- `input_is_real + - input_adapter_op_a_0` (the goal shape).
  have h_gate_bin :
      input_is_real + - input_adapter_op_a_0 = 0 ∨
      input_is_real + - input_adapter_op_a_0 = 1 := by
    rw [h_is_real]
    rcases h_op_a_0_bin with h0 | h1
    · right; rw [h0]; ring
    · left; rw [h1]; ring
  -- Restate h_isU64_addend in the form AddOp expects (with `Expression.eval`
  -- on addend slots, matching h_e_addend's right-hand side).
  have h_isU64_addend_eval : Word.isU64
      #v[Expression.eval env input_var_addend[0],
         Expression.eval env input_var_addend[1],
         Expression.eval env input_var_addend[2], (0 : ZMod p)] := by
    have h0 : Expression.eval env input_var_addend[0] = input_addend[0] := by
      rw [← h_e_addend]; simp
    have h1 : Expression.eval env input_var_addend[1] = input_addend[1] := by
      rw [← h_e_addend]; simp
    have h2 : Expression.eval env input_var_addend[2] = input_addend[2] := by
      rw [← h_e_addend]; simp
    rw [h0, h1, h2]; exact h_isU64_addend
  have h_add_assumptions :
      (input_is_real + - input_adapter_op_a_0 = 0 ∨
       input_is_real + - input_adapter_op_a_0 = 1) ∧
      (input_is_real + - input_adapter_op_a_0 = 1 →
        Word.isU64 #v[Expression.eval env input_var_addend[0],
                      Expression.eval env input_var_addend[1],
                      Expression.eval env input_var_addend[2], (0 : ZMod p)] ∧
        Word.isU64 input_adapter_op_b_imm) :=
    ⟨h_gate_bin, fun _ => ⟨h_isU64_addend_eval, h_isU64_op_b⟩⟩
  have h_add := h_add_sub h_add_assumptions
  -- Assemble FormalSpec's 9 conjuncts.
  refine ⟨h_cpu, ?_, ?_, h_isa_bin', h_a0, h_a1, h_a2, h_isreal_op_a_0', ?_⟩
  · -- AddOp.Assertion.Spec — passthrough from h_add with sub-eq-add-neg bridge.
    intro h_gate
    have h_gate' : input_is_real + - input_adapter_op_a_0 = 1 := by
      have : input_is_real + - input_adapter_op_a_0 =
          input_is_real - input_adapter_op_a_0 := by ring
      rw [this]; exact h_gate
    -- h_add gives AddOp.Spec for the eval form. Bridge result vector via h_e.
    have h_add' := h_add h_gate'
    -- h_add' is over #v[Expression.eval ...] for addend; goal uses input_addend.
    have h_eq_addend : #v[Expression.eval env input_var_addend[0],
                          Expression.eval env input_var_addend[1],
                          Expression.eval env input_var_addend[2], (0 : ZMod p)]
        = #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)] := by
      have h0 : Expression.eval env input_var_addend[0] = input_addend[0] := by
        rw [← h_e_addend]; simp
      have h1 : Expression.eval env input_var_addend[1] = input_addend[1] := by
        rw [← h_e_addend]; simp
      have h2 : Expression.eval env input_var_addend[2] = input_addend[2] := by
        rw [← h_e_addend]; simp
      rw [h0, h1, h2]
    rw [h_eq_addend] at h_add'
    exact h_add'
  · -- JTypeReader.Gated.Assertion.Spec — bridge lowercase `.assertion.Spec`
    -- (from h_jtr_sub) to uppercase `.Assertion.Spec` (from FormalSpec).
    simpa [SP1Clean.JTypeReader.Gated.assertion,
           SP1Clean.JTypeReader.Gated.Assertion.Spec, sub_eq_add_neg] using h_jtr_copy
  · -- BitVec leg: under is_real = 1 ∧ op_a_0 = 0, derive
    -- `Word.isU64 add_result ∧ add_result = if is_auipc = 1 then RV64.auipc imm pc else RV64.lui imm`.
    intro h_isr_eq h_op_a_0_eq
    change input_is_real = 1 at h_isr_eq
    change input_adapter_op_a_0 = 0 at h_op_a_0_eq
    -- Discharge AddOp gate = 1: `input_is_real + - input_adapter_op_a_0 = 1`.
    have h_gate_eq_one : input_is_real + - input_adapter_op_a_0 = 1 := by
      rw [h_isr_eq, h_op_a_0_eq]; ring
    have h_add_out := h_add h_gate_eq_one
    obtain ⟨h_isU64_v, h_bv_add⟩ := h_add_out
    -- Bridge the addend `Expression.eval` form in h_bv_add to input_addend.
    have h_eq_addend_word :
        #v[Expression.eval env input_var_addend[0],
           Expression.eval env input_var_addend[1],
           Expression.eval env input_var_addend[2], (0 : ZMod p)]
        = #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)] := by
      have h0 : Expression.eval env input_var_addend[0] = input_addend[0] := by
        rw [← h_e_addend]; simp
      have h1 : Expression.eval env input_var_addend[1] = input_addend[1] := by
        rw [← h_e_addend]; simp
      have h2 : Expression.eval env input_var_addend[2] = input_addend[2] := by
        rw [← h_e_addend]; simp
      rw [h0, h1, h2]
    rw [h_eq_addend_word] at h_bv_add
    refine ⟨h_isU64_v, ?_⟩
    -- Reduce the opcode form. h_ti : (Opcode.ofNat (is_auipc*48 + (1-is_auipc)*49).val).trusted_instr ...
    -- Case split on is_auipc ∈ {0, 1}.
    rcases mul_eq_zero.mp h_isa_bin' with h_iaui_zero | h_iaui_one_sub
    · -- LUI case: is_auipc = 0. opcode = 49. Opcode.ofNat 49 = .LUI.
      have h_iaui : input_is_auipc = 0 := h_iaui_zero
      have h_opcode_val : (input_is_auipc * 48 + (1 + - input_is_auipc) * 49 : ZMod p).val = 49 := by
        rw [h_iaui]; ring_nf
        have h49_lt : (49 : ℕ) < p := by
          have hp : 2 ^ 17 < p := Fact.out
          have : (49 : ℕ) < 2 ^ 17 := by decide
          omega
        rw [show (49 : ZMod p) = ((49 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt h49_lt]
      rw [h_opcode_val] at h_ti
      simp [Opcode.trusted_instr, show (Opcode.ofNat 49) = Opcode.LUI from rfl] at h_ti
      obtain ⟨h_div, h_se⟩ := h_ti
      -- Bridge `Word.toBitVec64 input_adapter_op_b_imm` ↔ explicit `#v[..]` form.
      have h_op_b_unfold :
          Word.toBitVec64 input_adapter_op_b_imm =
            Word.toBitVec64 #v[input_adapter_op_b_imm[0], input_adapter_op_b_imm[1],
                               input_adapter_op_b_imm[2], input_adapter_op_b_imm[3]] := by
        congr 1
        apply Vector.ext
        intro i hi
        interval_cases i <;> rfl
      -- The standard sign-extension equality for the 20-bit immediate.
      have h_imm : Word.toBitVec64 input_adapter_op_b_imm =
          BitVec.signExtend 64
            ((BitVec.ofNat 20 (input_adapter_op_b_imm[0].val / 4096 +
                               input_adapter_op_b_imm[1].val * 16)) ++ (0#12 : BitVec 12)) := by
        rw [h_op_b_unfold, ← h_se]
        congr 1
        apply BitVec.toNat_inj.mp
        simp [BitVec.toNat_ofNat]
        have h14_div : input_adapter_op_b_imm[0].val / 4096 * 4096 = input_adapter_op_b_imm[0].val := by
          have := Nat.div_add_mod input_adapter_op_b_imm[0].val 4096
          omega
        rw [BitVec.toNat_append]; simp; omega
      -- The LUI branch of the if.
      have h_zero_ne_one : (0 : ZMod p) ≠ 1 := fun h => zero_ne_one h
      simp only [h_iaui, if_neg h_zero_ne_one, RV64.lui]
      -- Addend is zero in LUI case: from h_a{0,1,2} with is_auipc = 0.
      have ea0 : input_addend[0] = 0 := by
        have := h_a0; rw [h_iaui] at this; linear_combination this
      have ea1 : input_addend[1] = 0 := by
        have := h_a1; rw [h_iaui] at this; linear_combination this
      have ea2 : input_addend[2] = 0 := by
        have := h_a2; rw [h_iaui] at this; linear_combination this
      have h_zero_word : Word.toBitVec64 (#v[input_addend[0], input_addend[1],
                                              input_addend[2], (0 : ZMod p)]) = 0#64 := by
        rw [ea0, ea1, ea2]
        simp [Word.toBitVec64, Word.toNat_def, ZMod.val_zero]
      rw [h_bv_add, h_zero_word, BitVec.zero_add]; exact h_imm
    · -- AUIPC case: is_auipc = 1.
      have h_iaui : input_is_auipc = 1 := by linear_combination h_iaui_one_sub
      have h_opcode_val : (input_is_auipc * 48 + (1 + - input_is_auipc) * 49 : ZMod p).val = 48 := by
        rw [h_iaui]; ring_nf
        have h48_lt : (48 : ℕ) < p := by
          have hp : 2 ^ 17 < p := Fact.out
          have : (48 : ℕ) < 2 ^ 17 := by decide
          omega
        rw [show (48 : ZMod p) = ((48 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt h48_lt]
      rw [h_opcode_val] at h_ti
      simp [Opcode.trusted_instr, show (Opcode.ofNat 48) = Opcode.AUIPC from rfl] at h_ti
      obtain ⟨h_div, h_se⟩ := h_ti
      have h_op_b_unfold :
          Word.toBitVec64 input_adapter_op_b_imm =
            Word.toBitVec64 #v[input_adapter_op_b_imm[0], input_adapter_op_b_imm[1],
                               input_adapter_op_b_imm[2], input_adapter_op_b_imm[3]] := by
        congr 1
        apply Vector.ext
        intro i hi
        interval_cases i <;> rfl
      have h_imm : Word.toBitVec64 input_adapter_op_b_imm =
          BitVec.signExtend 64
            ((BitVec.ofNat 20 (input_adapter_op_b_imm[0].val / 4096 +
                               input_adapter_op_b_imm[1].val * 16)) ++ (0#12 : BitVec 12)) := by
        rw [h_op_b_unfold, ← h_se]
        congr 1
        apply BitVec.toNat_inj.mp
        simp [BitVec.toNat_ofNat]
        have h14_div : input_adapter_op_b_imm[0].val / 4096 * 4096 = input_adapter_op_b_imm[0].val := by
          have := Nat.div_add_mod input_adapter_op_b_imm[0].val 4096
          omega
        rw [BitVec.toNat_append]; simp; omega
      -- AUIPC branch.
      simp only [h_iaui, if_true, RV64.auipc]
      -- Addend = pc in AUIPC case.
      have ea0 : input_addend[0] = input_state_pc[0] := by
        have := h_a0; rw [h_iaui] at this; linear_combination this
      have ea1 : input_addend[1] = input_state_pc[1] := by
        have := h_a1; rw [h_iaui] at this; linear_combination this
      have ea2 : input_addend[2] = input_state_pc[2] := by
        have := h_a2; rw [h_iaui] at this; linear_combination this
      have h_addend_eq_pc :
          Word.toBitVec64 (#v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)]) =
          Word.toBitVec64 (#v[input_state_pc[0], input_state_pc[1], input_state_pc[2], (0 : ZMod p)]) := by
        rw [ea0, ea1, ea2]
      rw [h_bv_add, h_addend_eq_pc]; rw [h_imm]; exact BitVec.add_comm _ _

/-- Completeness of `UType.assertion`. The 9 conjuncts of `FormalSpec`
(3 subcircuit Specs + 5 scalar gates + 1 BitVec conjunct) are dispatched
to the matching subcircuit input requirement (`⟨Assumptions, Spec⟩` form)
plus the 5 inline scalar gates. The BitVec conjunct is discarded since
completeness only needs the structural Spec. Mirror `JalrChip/Aggregate.lean`
`Assertion.completeness` (commit `186a456`). -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_trusted, h_is_real, h_isU64_op_b⟩ := h_assumptions
  obtain ⟨h_cpu, h_add_spec, h_jtr, h_isa_bin, h_addend0, h_addend1,
          h_addend2, h_isreal_op_a_0, _h_bv⟩ := h_spec
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Extract op_a_0 binary from h_jtr.ProgramSpec.
  have h_jtr_copy := h_jtr
  obtain ⟨_h_gate_jtr, h_prog_disj, _, _, _, _, _⟩ := h_jtr
  have h_ir_ne_zero : input_is_real ≠ 0 := by rw [h_is_real]; exact one_ne_zero
  have h_it_ne_zero : input_adapter_cols_is_trusted ≠ 0 := by
    rw [h_trusted]; exact h_ir_ne_zero
  have h_prog := h_prog_disj.resolve_left h_it_ne_zero
  simp only [SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  obtain ⟨_h_ti, _h_op_a_lt, _h_ob, _h_oc, h_op_a_0_bin, _h_op_a_0_iff,
          _h_imm_b, _h_imm_c,
          _h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩ := h_prog
  haveI h65k : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have lt65k : ∀ (x : ZMod p), x < (65536 : ZMod p) → x.val < 65536 :=
    fun x h => by have : x.val < (65536 : ZMod p).val := h; rwa [h65k] at this
  -- Bridge the addend gates from `input_addend[i] - input_is_auipc *
  -- input_state_pc[i] = 0` shape to the `Expression.eval` form for AddOp's
  -- Assumptions. This requires the h_input equalities.
  obtain ⟨⟨_h_e_clk_high, _h_e_clk_16_24, _h_e_clk_0_16, h_e_pc⟩, _,
          h_e_addend, _h_e_add_result, _h_e_is_auipc, _h_e_is_real,
          _h_e_is_trusted⟩ := h_input
  have h_pc_isU64 : Word.isU64
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], (0 : ZMod p)] :=
    Word.isU64_of_cases (lt65k _ h_pc0_lt) (lt65k _ h_pc1_lt)
                        (lt65k _ h_pc2_lt) (by simp [ZMod.val_zero])
  have h_isU64_addend : Word.isU64
      #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)] := by
    rcases mul_eq_zero.mp h_isa_bin with h0 | h1
    · have e0 : input_addend[0] = 0 := by
        have := h_addend0; rw [h0] at this; linear_combination this
      have e1 : input_addend[1] = 0 := by
        have := h_addend1; rw [h0] at this; linear_combination this
      have e2 : input_addend[2] = 0 := by
        have := h_addend2; rw [h0] at this; linear_combination this
      rw [show #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)]
            = #v[(0 : ZMod p), 0, 0, 0] from by rw [e0, e1, e2]]
      exact Word.isU64_of_cases (by simp [ZMod.val_zero])
            (by simp [ZMod.val_zero]) (by simp [ZMod.val_zero])
            (by simp [ZMod.val_zero])
    · have h_iaui_eq : input_is_auipc = 1 := by linear_combination h1
      have e0 : input_addend[0] = input_state_pc[0] := by
        have := h_addend0; rw [h_iaui_eq] at this; linear_combination this
      have e1 : input_addend[1] = input_state_pc[1] := by
        have := h_addend1; rw [h_iaui_eq] at this; linear_combination this
      have e2 : input_addend[2] = input_state_pc[2] := by
        have := h_addend2; rw [h_iaui_eq] at this; linear_combination this
      rw [show #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)]
            = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2],
                 (0 : ZMod p)] from by rw [e0, e1, e2]]
      exact h_pc_isU64
  have h_gate_bin :
      input_is_real + - input_adapter_op_a_0 = 0 ∨
      input_is_real + - input_adapter_op_a_0 = 1 := by
    rw [h_is_real]
    rcases h_op_a_0_bin with h0 | h1
    · right; rw [h0]; ring
    · left; rw [h1]; ring
  -- Bridge `input_addend[i]` ↔ `Expression.eval env input_var_addend[i]`.
  have h_isU64_addend_eval : Word.isU64
      #v[Expression.eval env.toEnvironment input_var_addend[0],
         Expression.eval env.toEnvironment input_var_addend[1],
         Expression.eval env.toEnvironment input_var_addend[2], (0 : ZMod p)] := by
    have h0 : Expression.eval env.toEnvironment input_var_addend[0] = input_addend[0] := by
      rw [← h_e_addend]; simp
    have h1 : Expression.eval env.toEnvironment input_var_addend[1] = input_addend[1] := by
      rw [← h_e_addend]; simp
    have h2 : Expression.eval env.toEnvironment input_var_addend[2] = input_addend[2] := by
      rw [← h_e_addend]; simp
    rw [h0, h1, h2]; exact h_isU64_addend
  -- Bridge the scalar gates: h_addend0/1/2 use `.addend[i]` / `.state.pc[i]`
  -- field projections from the cols struct; the goal uses `Expression.eval env
  -- input_var_addend[i]` / `Expression.eval env input_var_state_pc[i]` forms.
  -- Pre-compute the bridging equalities from h_e_addend / h_e_pc.
  have hb_a0 : Expression.eval env.toEnvironment input_var_addend[0] = input_addend[0] := by
    rw [← h_e_addend]; simp
  have hb_a1 : Expression.eval env.toEnvironment input_var_addend[1] = input_addend[1] := by
    rw [← h_e_addend]; simp
  have hb_a2 : Expression.eval env.toEnvironment input_var_addend[2] = input_addend[2] := by
    rw [← h_e_addend]; simp
  have hb_p0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← h_e_pc]; simp
  have hb_p1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← h_e_pc]; simp
  have hb_p2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← h_e_pc]; simp
  -- Rewrite each gate hypothesis from FormalSpec form to circuit-goal form.
  have h_isa_bin_eval : input_is_auipc * (input_is_auipc + -1) = 0 := by
    linear_combination h_isa_bin
  have h_a0_eval : Expression.eval env.toEnvironment input_var_addend[0] +
      -(input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[0]) = 0 := by
    rw [hb_a0, hb_p0]; linear_combination h_addend0
  have h_a1_eval : Expression.eval env.toEnvironment input_var_addend[1] +
      -(input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[1]) = 0 := by
    rw [hb_a1, hb_p1]; linear_combination h_addend1
  have h_a2_eval : Expression.eval env.toEnvironment input_var_addend[2] +
      -(input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[2]) = 0 := by
    rw [hb_a2, hb_p2]; linear_combination h_addend2
  have h_isreal_op_a_0_eval : (input_is_real + -1) * input_adapter_op_a_0 = 0 := by
    linear_combination h_isreal_op_a_0
  refine ⟨⟨trivial, h_cpu⟩, ?_, ?_,
          h_isa_bin_eval, h_a0_eval, h_a1_eval, h_a2_eval, h_isreal_op_a_0_eval⟩
  · -- JTypeReader.Gated.assertion (2nd subcircuit in main): Assumptions + Spec.
    refine ⟨trivial, ?_⟩
    simpa [SP1Clean.JTypeReader.Gated.assertion,
           SP1Clean.JTypeReader.Gated.Assertion.Spec, sub_eq_add_neg] using h_jtr_copy
  · -- AddOp.assertion (3rd subcircuit in main): Assumptions + Spec.
    refine ⟨⟨h_gate_bin, fun _ => ⟨h_isU64_addend_eval, h_isU64_op_b⟩⟩, ?_⟩
    intro h_gate
    have h_gate' : input_is_real - input_adapter_op_a_0 = 1 := by
      rw [show input_is_real - input_adapter_op_a_0 =
            input_is_real + - input_adapter_op_a_0 from by ring]
      exact h_gate
    have h_spec_out := h_add_spec h_gate'
    have h_eq_addend : #v[input_addend[0], input_addend[1], input_addend[2], (0 : ZMod p)]
        = #v[Expression.eval env.toEnvironment input_var_addend[0],
             Expression.eval env.toEnvironment input_var_addend[1],
             Expression.eval env.toEnvironment input_var_addend[2], (0 : ZMod p)] := by
      rw [hb_a0, hb_a1, hb_a2]
    rw [h_eq_addend] at h_spec_out
    exact h_spec_out

end Assertion

/-- The full Clean `FormalAssertion` for `UTypeChip`. Single subcircuit
composition backing one unified `Spec` whose last conjunct is the pure
BitVec `RV64.lui` / `RV64.auipc` semantic (auditable at a glance,
conditional on `is_real = 1 ∧ op_a_0 = 0`). Per-row Sail equivalence is
derived externally via `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) UTypeCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.UType
