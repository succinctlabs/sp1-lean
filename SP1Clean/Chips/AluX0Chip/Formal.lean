import SP1Clean.Chips.AluX0Chip.Defs

/-! # `SP1Clean.AluX0Chip` — contract: `Assumptions` / soundness / completeness / `circuit`

Verifier-side `Assumptions` are trivial (`True`) — soundness derives `is_real` binary and the
reader contract purely from the in-circuit gates. -/

namespace SP1Clean.AluX0Chip

open Circuit
open Extracted (AluX0Cols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The `opcode < 29` LTU byte-table row `⟨4, 1, op, 29⟩` is valid when `op.val < 29` — the chip's dynamic
opcode is a real ALU opcode (`< 29`). Constructs the `ByteRowSpec` (`LTU.constrain 1 op 29`) directly. -/
lemma byteRowSpec_ltu_29 {op : ZMod p} (h : op.val < 29) :
    ByteRowSpec (⟨(4 : ZMod p), 1, op, 29⟩ : ByteRow (ZMod p)) := by
  have hp2 : 1 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h29 : ((29 : ZMod p)).val = 29 := by
    have h29p : (29 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    rw [show (29 : ZMod p) = ((29 : ℕ) : ZMod p) from by norm_cast, ZMod.val_natCast_of_lt h29p]
  haveI : Fact (1 < p) := ⟨hp2⟩
  refine ⟨ByteOpcode.LTU, by norm_cast, ?_⟩
  simp only [ByteOpcode.constrain_LTU]
  refine ⟨⟨?_, ?_, ?_⟩, Or.inr trivial, ?_⟩
  · rw [ZMod.val_one]; norm_num
  · omega
  · rw [h29]; norm_num
  · rw [h29]; exact ⟨fun _ => h, fun _ => trivial⟩

/-- Verifier-side `Assumptions` — trivial. `AluX0` discards its result, so there are no operand
well-formedness obligations; `is_real` binary and the reader contract are derived in soundness from the
in-circuit gates. -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

set_option maxHeartbeats 4000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨_h_cpu, _h_ltu, h_reader, h_gate, h_oa1, h_oa2⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  simp only [← sub_eq_add_neg] at h_oa1 h_oa2
  simp only [isReal, clkLow, opcodeVal]
  -- the per-emitter channel-requirement tail: CPUState / reader (the gated byte pull owes no requirement).
  exact ⟨⟨h_reader h_bin, h_bin, h_oa1, h_oa2⟩,
    Or.inr h_bin, Or.inr h_bin⟩

/-- Honest prover-side row well-formedness: `is_real` binary, the two `op_a_0` forcing gates, the
CPUState clock bounds + the immutable-ALU-reader contract, and the dynamic opcode in ALU range
(`opcode < 29`, the LTU byte pull's witness — the honest prover only emits real ALU opcodes). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  (isReal input = 0 ∨ isReal input = 1) ∧
  isReal input * (input.adapter.op_a_0 - 1) = 0 ∧
  (isReal input - 1) * input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
  Readers.ALUTypeReaderImmutable.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, opcodeVal input⟩ ∧
  (isReal input = 1 → input.opcode.val < 29)

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [isReal, clkLow, opcodeVal] at h_assumptions
  obtain ⟨h_bin, h_oa1, h_oa2, h_cpu, h_reader, h_op_lt⟩ := h_assumptions
  simp only [sub_eq_add_neg] at h_oa1 h_oa2
  refine ⟨⟨h_bin, h_cpu⟩, ?_, ⟨h_bin, h_reader⟩, ?_, ?_, ?_⟩
  · -- the LTU `opcode < 29` byte pull (fires on real rows).
    intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    simp only [byteChannel]
    exact byteRowSpec_ltu_29 (h_op_lt hr1)
  · -- `is_real` binary gate.
    rcases h_bin with h | h <;> rw [h] <;> simp
  · exact h_oa1
  · exact h_oa2

/-- The `AluX0` chip row as a `GeneralFormalCircuit`: validates the ALU-into-`x0` program/register accesses
and advances state (the result discarded); output is the extracted `AluX0Cols`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AluX0Cols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.AluX0Chip
