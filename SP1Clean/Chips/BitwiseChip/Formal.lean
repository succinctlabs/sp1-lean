import SP1Clean.Chips.BitwiseChip.Defs

/-! # `SP1Clean.BitwiseChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge in `Bridge`. This module holds the prover/verifier
`Assumptions`, the semantic flag-gated `Spec`, the soundness/completeness proofs (the AND/OR/XOR
dispatch mirrors `LtChip`'s SLT/SLTU dispatch, organized around the `one_hot3` selector lemma so
each opcode branch is a self-contained local argument), and the bundled `circuit`. -/

namespace SP1Clean.BitwiseChip

open Circuit
open Extracted (BitwiseCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; `is_real`-binary is proven from the in-circuit gate (so it lives in
`Spec`), not assumed. The operands resolve via the adapter projections (`Inputs.op_b_val`/`op_c_val`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness (mirrors `LtChip.ProverAssumptions`, ALU adapter): operand
`isU64`s, the `is_real` binary selector, the `op_a_0 = 0` flag, `imm_c = 0` (AND/OR/XOR are
register-register), the CPUState clock bounds, and the three timestamp `Spec`s (op_c gated by
`is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧ input.adapter.imm_c = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩

/-- Semantic contract (mirrors `LtChip.Spec`, here for the **three-variant** bitwise adapter): the
proven `is_real`-binary fact and the `is_real`/flag-gated meaning — on real rows the result word is the
RV64 `AND` (when `is_and = 1`) / `OR` (when `is_or = 1`) / `XOR` (when `is_xor = 1`) of the operands
(operand order matching the RV64 signature `f rs2_val rs1_val` with `rs1 ↦ op_b_val`). Vacuous on
padding. The `ALUTypeReader`/`CPUState` sub-circuits are still composed (and emit their buses) in `main`;
their cross-row guarantees live at the trace level, so they are not re-exposed in the chip `Spec`. -/
def Spec (input : Inputs (ZMod p)) (cols : BitwiseCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_and = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.and (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_or = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.or (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_xor = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.xor (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

/-- One-hot lemma for the three opcode selectors: given each selector is binary and their sum is binary
(`E1 = is_xor + is_or + is_and` with `E9 = E1·(E1-1) = 0`), whichever selector is `1` forces the other
two to `0`. The sum-bound rules out two-or-three-hot via `2 ≠ 0` / `6 ≠ 0` in `ZMod p` (`p > 2^17`). -/
private lemma one_hot3 {x o a : ZMod p}
    (hx : x = 0 ∨ x = 1) (ho : o = 0 ∨ o = 1) (ha : a = 0 ∨ a = 1)
    (hsum : (x + o + a) * (x + o + a + -1) = 0) :
    (x = 1 → o = 0 ∧ a = 0) ∧ (o = 1 → x = 0 ∧ a = 0) ∧ (a = 1 → x = 0 ∧ o = 0) := by
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]; intro hd
      have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using h
  have h6 : (6 : ZMod p) ≠ 0 := by
    have h : ((6 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]; intro hd
      have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using h
  rcases hx with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases ha with rfl | rfl <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h.symm one_ne_zero
      | (exfalso; apply h2; linear_combination hsum)
      | (exfalso; apply h6; linear_combination hsum)

set_option maxHeartbeats 2000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  haveI hF1 : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_h_cpu, h_bw, _h_adapter, h_gate, h_xor_bin, h_or_bin, h_and_bin, h_sum, _h_opa0⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_xor_bool := bool_of_mul_pred h_xor_bin
  have h_or_bool := bool_of_mul_pred h_or_bin
  have h_and_bool := bool_of_mul_pred h_and_bin
  have hoh := one_hot3 h_xor_bool h_or_bool h_and_bool h_sum
  -- the byte opcode passed to the gadget reduces to a literal once the active flag forces the others to 0
  refine ⟨⟨h_bin, fun _hr => ⟨fun hand => ?_, fun hor => ?_, fun hxor => ?_⟩⟩,
    Or.inr h_bin, Or.inl rfl, Or.inr h_bin⟩
  · -- AND: `is_and = 1` forces `is_xor = is_or = 0`, so `byte_opcode = 0`
    obtain ⟨hx0, ho0⟩ := hoh.2.2 hand
    have hopc : env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0 = 0 := by
      rw [hx0, ho0]; ring
    exact (h_bw ⟨ha, hb, by rw [hopc, ZMod.val_zero]; omega⟩).1 hopc
  · -- OR: `is_or = 1` forces `is_xor = is_and = 0`, so `byte_opcode = 1`
    obtain ⟨hx0, _ha0⟩ := hoh.2.1 hor
    have hopc : env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0 = 1 := by
      rw [hx0, hor]; ring
    exact (h_bw ⟨ha, hb, by rw [hopc, ZMod.val_one]; omega⟩).2.1 hopc
  · -- XOR: `is_xor = 1` forces `is_or = is_and = 0`, so `byte_opcode = 2`
    obtain ⟨ho0, _ha0⟩ := hoh.1 hxor
    have hopc : env.get i₀ * 2 + env.get (i₀ + 1) * 1 + env.get (i₀ + 2) * 0 = 2 := by
      rw [hxor, ho0]; ring
    have h2 : (2 : ZMod p).val < 3 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega : 2 < p)]
      omega
    exact (h_bw ⟨ha, hb, by rw [hopc]; exact h2⟩).2.2 hopc

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, himm, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨h_env_flags, -⟩ := h_env
  have hflag0 : env.get i₀ = 0 := by simpa using h_env_flags 0
  have hflag1 : env.get (i₀ + 1) = 0 := by simpa using h_env_flags 1
  have hflag2 : env.get (i₀ + 2) = 0 := by simpa using h_env_flags 2
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨ha, hb, (by simp only [hflag0, hflag1, zero_mul, mul_zero, add_zero, ZMod.val_zero]; norm_num)⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp,
    by rw [hflag0]; simp,
    by rw [hflag1]; simp,
    by rw [hflag2]; simp,
    by rw [hflag0, hflag1, hflag2]; simp,
    hop_a_0⟩

/-- The Bitwise chip row as a `GeneralFormalCircuit`: flag-gated RV64 `and`/`or`/`xor` semantic contract,
composing the witnessed `BitwiseU16Operation` gadget and the immediate-capable register reader; output is
the extracted `BitwiseCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs BitwiseCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.BitwiseChip
