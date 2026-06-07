import SP1Clean.Chips.BranchChip.Defs
import SP1Clean.Chips.BranchChip.Decision

/-! # `SP1Clean.BranchChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.BranchChip

open Circuit
open Extracted (BranchColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel binary_gate_req_vacuous)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Received-fact row well-formedness: the immediate and the two source-register values are 64-bit
(received facts — register values from the offline-memory writer, the immediate from the program ROM,
never range-checked locally), the program counter is 64-bit, and the **padding convention**
`is_real = 0 → is_branching = 0` (so the fall-through `is_real - is_branching` gate is binary on every
row). `is_real`/flag/`is_branching` binaries are NOT assumed — soundness proves them from the gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
    input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p))

/-- Honest prover-side row well-formedness. The immediate + rs1/rs2 + pc words `isU64`, `is_real` binary,
the CPUState clock bounds + op_a/op_b register-access timestamp bounds, the two targets fitting in 48 bits
(`value[3] = 0`), and the `is_real`-gated next_pc 4-byte alignment + u16 limb ranges. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  let br := hintBranching hint
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (rs1WordInput input) ∧
  Word.isU64 (rs2WordInput input) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  -- the immutable I-type reader's honest sub-`Spec` (op_a_0 read-zeroing + binary, op_a/op_b timestamp
  -- bounds). `opcode`/`is_trusted`/`clk_high`/`pc` are not projected by the `Spec`, so any value works.
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 0⟩ ∧
  (branchTargetWord input)[3] = 0 ∧
  (fallThroughWord input)[3] = 0 ∧
  -- honest opcode flags: each binary, one-hot summing to `is_real`.
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧ (f[2] = 0 ∨ f[2] = 1) ∧
  (f[3] = 0 ∨ f[3] = 1) ∧ (f[4] = 0 ∨ f[4] = 1) ∧ (f[5] = 0 ∨ f[5] = 1) ∧
  (input.is_real = f[0] + f[1] + f[2] + f[3] + f[4] + f[5]) ∧
  -- honest `is_branching`: binary, zero on padding, and (on real rows) the per-opcode branch-taken
  -- decision as a pure function of the source words (mirrors `Spec`'s six-way condition).
  (br = 0 ∨ br = 1) ∧
  (input.is_real = 0 → br = 0) ∧
  (input.is_real = 1 →
    (f[0] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) = Word.toBitVec64 (rs2WordInput input))) ∧
    (f[1] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) ≠ Word.toBitVec64 (rs2WordInput input))) ∧
    (f[2] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[3] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = false)) ∧
    (f[4] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[5] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = false))) ∧
  -- the `is_real`-gated committed `next_pc` byte ranges (4-byte-aligned low limb + two u16 limbs).
  (input.is_real = 1 →
    ((committedNextPc input br)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
    (committedNextPc input br)[1].val < 2 ^ 16 ∧
    (committedNextPc input br)[2].val < 2 ^ 16)

-- The binary-element algebra (`zero_ne_one'`, `val_of_bool`, `one_hot6`) and the six-way decision
-- dispatch (`branch_conditions_of_decision_eq` / `branch_decision_eq_of_conditions`) live in the
-- sibling `Decision` module, so the heavy one-hot case analysis is elaborated once, in a small
-- context, rather than twice under the giant chip goal here.

set_option maxHeartbeats 8000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU⟩ := h_assumptions
  obtain ⟨h_lt, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_realsum, h_sumbin, h_isbr_bin,
    h_isbr, h_pad, h_cpustate, h_add1, h_add1z, h_add2, h_add2z, h_pc0, h_pc1, h_pc2, h_itype,
    h_byte1, h_byte2, h_byte3⟩ := h_holds
  obtain ⟨_h_ir, ⟨_h_ckh, _h_ck1, _h_ck0, hpc⟩, _h_a, ⟨h_amem_pv, _, _⟩, _h_a0, _h_b,
    ⟨h_bmem_pv, _, _⟩, hcimm⟩ := h_input
  -- binary facts for `is_real`, the six flags, and `is_branching`.
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := by
    rw [h_realsum]; exact bool_of_mul_pred h_sumbin
  have hbeq := bool_of_mul_pred h_beq
  have hbne := bool_of_mul_pred h_bne
  have hblt := bool_of_mul_pred h_blt
  have hbge := bool_of_mul_pred h_bge
  have hbltu := bool_of_mul_pred h_bltu
  have hbgeu := bool_of_mul_pred h_bgeu
  have hisbr := bool_of_mul_pred h_isbr_bin
  -- eval-of-input word bridges: rs1 = op_a_memory.prev_value, rs2 = op_b_memory.prev_value, pc.
  -- Proved directly from the whole-vector eval hypotheses (`h_amem_pv`/`h_bmem_pv`/`hpc`) with
  -- `simp only [Vector.getElem_map]` — full `simp` over-triggers, walking the huge `eval` subterms.
  have hrs1eq : (#v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_a_memory_prev_value[0], input_adapter_op_a_memory_prev_value[1],
        input_adapter_op_a_memory_prev_value[2], input_adapter_op_a_memory_prev_value[3]] := by
    rw [← h_amem_pv]; simp only [Vector.getElem_map]
  have hrs2eq : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hrs2U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs2eq ▸ h_rs2U
  have hpceq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have hpcU : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := hpceq ▸ h_pcU
  -- `#v[4,0,0,0]` is a 64-bit word.
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := by
    have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num
  -- one-hot bound on the six flags, and the `is_signed = is_blt + is_bge` binary fact.
  have h_onehot := one_hot6 hbeq hbne hblt hbge hbltu hbgeu h_sumbin
  have h_sig_bin : env.get (i₀ + 2) + env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 2) + env.get (i₀ + 3) = 1 := by
    rcases hblt with hl | hl <;> rcases hbge with hg | hg
    · left; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · exfalso
      have := val_of_bool (h := hbeq); have := val_of_bool (h := hbne)
      have := val_of_bool (h := hbltu); have := val_of_bool (h := hbgeu)
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rw [hl, hg, ZMod.val_one] at h_onehot
      omega
  -- byte-pull padding requirement: vacuous for the binary gate (`toRawGated`, raw values).
  have byte_pad : ∀ x : ZMod p, ¬ -input_is_real = -1 → ¬ -input_is_real = 0 →
      byteChannel.Guarantees (⟨6, x, ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (ZMod p)) env.data :=
    fun x => binary_gate_req_vacuous h_bin _
  refine ⟨⟨?_, h_bin, ⟨hbeq, hbne, hblt, hbge, hbltu, hbgeu, hisbr⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- conjunct 1: ITypeReaderImmutable sub-`Spec` (opcode-independent), from `h_itype` on `is_real` binary.
    exact h_itype h_bin
  · -- conjunct 4: is_branching = 1 → next_pc = pc + op_c_imm.
    intro hr1 hbr1
    -- the branch `AddOperation` Spec: `branch_value = pc + op_c_imm`.
    have hav := (h_add1 ⟨fun _ => ⟨hpcU, h_imm⟩, hisbr⟩ hbr1).2
    rw [hpceq] at hav
    -- the committed `next_pc` limbs collapse to the branch target (mux with is_branching = 1).
    have hn0 : env.get (i₀ + 6 + 1 + 4 + 4) = env.get (i₀ + 6 + 1) := by
      rw [h_pc0, hbr1, hr1]; ring
    have hn1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = env.get (i₀ + 6 + 1 + 1) := by
      rw [h_pc1, hbr1, hr1]; ring
    have hn2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = env.get (i₀ + 6 + 1 + 2) := by
      rw [h_pc2, hbr1, hr1]; ring
    rw [show Word.toBitVec64
          (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + i }))
        = Word.toBitVec64
          (#v[env.get (i₀ + 6 + 1 + 4 + 4), env.get (i₀ + 6 + 1 + 4 + 4 + 1),
            env.get (i₀ + 6 + 1 + 4 + 4 + 2), 0] : Word (ZMod p)) from by
        congr 1; apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i
        · exact hn0.symm
        · exact hn1.symm
        · exact hn2.symm
        · exact h_add1z] at hav
    simp only [nextPcWord, pcWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact hav
  · -- conjunct 5: is_branching = 0 → next_pc = pc + 4.
    intro hr1 hbr0
    have hgate1 : input_is_real + -env.get (i₀ + 6) = 1 := by rw [hr1, hbr0]; ring
    have hav := (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, Or.inr hgate1⟩ hgate1).2
    rw [hpceq] at hav
    have hn0 : env.get (i₀ + 6 + 1 + 4 + 4) = env.get (i₀ + 6 + 1 + 4) := by
      rw [h_pc0, hbr0, hr1]; ring
    have hn1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = env.get (i₀ + 6 + 1 + 4 + 1) := by
      rw [h_pc1, hbr0, hr1]; ring
    have hn2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = env.get (i₀ + 6 + 1 + 4 + 2) := by
      rw [h_pc2, hbr0, hr1]; ring
    rw [show Word.toBitVec64
          (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + 4 + i }))
        = Word.toBitVec64
          (#v[env.get (i₀ + 6 + 1 + 4 + 4), env.get (i₀ + 6 + 1 + 4 + 4 + 1),
            env.get (i₀ + 6 + 1 + 4 + 4 + 2), 0] : Word (ZMod p)) from by
        congr 1; apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i
        · exact hn0.symm
        · exact hn1.symm
        · exact hn2.symm
        · exact h_add2z] at hav
    simp only [nextPcWord, pcWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact hav
  · -- conjunct 6: six-way flag-dispatched branch decision — delegated to `Decision`.
    intro hr1
    -- the signed-compare gadget `Spec` (compare `bit` + the `is_signed = 0` flags-equality), bridged
    -- to the spec's `rs1Word`/`rs2Word`.
    have h_lt_spec := h_lt ⟨hrs1U, hrs2U, h_sig_bin⟩
    simp only [LtOperationSigned.circuit, LtOperationSigned.Spec] at h_lt_spec
    obtain ⟨h_bit, h_eqf, -⟩ := h_lt_spec
    rw [hrs1eq, hrs2eq] at h_bit h_eqf
    simp only [Vector.getElem_map] at h_eqf
    -- the in-circuit decision equation on the real row, and `Σ flags = 1`. `simp only [id_eq]` strips
    -- the `id (ZMod p)` field-type wrapper off the gate so it unifies with the `Decision` lemma's
    -- plain-`ZMod p` equation (the `id` blocks `linear_combination`'s ring synthesis — PROOF_PATTERNS).
    rw [hr1, one_mul] at h_isbr
    simp only [id_eq, LtOperationSigned.circuit] at h_isbr
    have hone : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
        + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [← h_realsum]; exact hr1
    simp only [rs1Word, rs2Word]
    exact branch_conditions_of_decision_eq h_rs1U h_rs2U hbeq hbne hblt hbge hbltu hbgeu hisbr hone
      h_bit h_eqf (by simp only [branchDecision]; linear_combination h_isbr)
  · -- subcircuit + byte-pull obligation tail (in `main` order: LtOp, CPUState, AddOp1, AddOp2,
    -- ITypeReader, three byte pulls).
    refine ⟨Or.inr ⟨hrs1U, hrs2U, h_sig_bin⟩, Or.inr h_bin, Or.inr ⟨fun _ => ⟨hpcU, h_imm⟩, hisbr⟩,
      Or.inr ⟨fun _ => ⟨hpcU, h4U⟩, ?_⟩, Or.inr h_bin, ?_, byte_pad _, byte_pad _⟩
    · -- AddOp2 gate `is_real - is_branching` is binary, via the padding convention `h_pad`.
      rcases h_bin with h0 | h1
      · -- padding: `is_branching = 0`, gate `= 0`.
        have hbr0 : env.get (i₀ + 6) = 0 := by
          have hh : (input_is_real + -1) * env.get (i₀ + 6) = 0 := h_pad
          rw [h0] at hh
          linear_combination -hh
        left; rw [h0, hbr0]; simp
      · -- real row: gate `= 1 - is_branching ∈ {0,1}`.
        rcases hisbr with hb0 | hb1
        · right; rw [h1, hb0]; simp
        · left; rw [h1, hb1]; simp
    · -- first byte pull: the alignment Range check (width 14) — vacuous for the binary gate.
      exact binary_gate_req_vacuous h_bin _

set_option maxHeartbeats 4000000 in
/-- Completeness via **honest `ProverHint` flag witnesses**. `main` witnesses the six opcode flags and
`is_branching` from the prover's `ProverHint` (`hintFlags`/`hintBranching` — the branch opcode is not an
`Inputs` field, so it is threaded through the hint), and `ProverAssumptions` states the honest-prover
contract for them: each flag binary, one-hot summing to `is_real`, `is_branching` binary + zero on
padding, and the six per-opcode branch-taken decisions as pure functions of the source words. The
six-way decision constraint is discharged by mirroring soundness's case analysis in reverse: the
`LtOperationSigned` subcircuit's `Spec` (available via `UsesLocalWitnessesCompleteness`) gives the
compare `bit`/equality-flags, the one-hot bound collapses `decision` to the active opcode's indicator,
and the per-opcode `ProverAssumption` equates it to `is_branching`. Axiom-clean. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU, h_bin, h_cpu, h_it, h_bt3, h_ft3,
    hf0, hf1, hf2, hf3, hf4, hf5, h_realsum, h_brbin, h_brpad, h_dec, h_ranges⟩ := h_assumptions
  obtain ⟨he_flags, he_br, he_bv, he_fv, he_np, he_lt⟩ := h_env
  simp only [branchTargetWord, fallThroughWord] at h_bt3 h_ft3 h_ranges
  -- the witnessed flags/`is_branching` equal the honest hint values.
  have hg0 : env.get i₀ = (hintFlags env.hint)[0] := by simpa using he_flags 0
  have hg1 : env.get (i₀ + 1) = (hintFlags env.hint)[1] := by simpa using he_flags 1
  have hg2 : env.get (i₀ + 2) = (hintFlags env.hint)[2] := by simpa using he_flags 2
  have hg3 : env.get (i₀ + 3) = (hintFlags env.hint)[3] := by simpa using he_flags 3
  have hg4 : env.get (i₀ + 4) = (hintFlags env.hint)[4] := by simpa using he_flags 4
  have hg5 : env.get (i₀ + 5) = (hintFlags env.hint)[5] := by simpa using he_flags 5
  -- per-flag binary facts, in `env.get` form.
  have fb0 : env.get i₀ = 0 ∨ env.get i₀ = 1 := hg0 ▸ hf0
  have fb1 : env.get (i₀ + 1) = 0 ∨ env.get (i₀ + 1) = 1 := hg1 ▸ hf1
  have fb2 : env.get (i₀ + 2) = 0 ∨ env.get (i₀ + 2) = 1 := hg2 ▸ hf2
  have fb3 : env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 3) = 1 := hg3 ▸ hf3
  have fb4 : env.get (i₀ + 4) = 0 ∨ env.get (i₀ + 4) = 1 := hg4 ▸ hf4
  have fb5 : env.get (i₀ + 5) = 0 ∨ env.get (i₀ + 5) = 1 := hg5 ▸ hf5
  have brb : env.get (i₀ + 6) = 0 ∨ env.get (i₀ + 6) = 1 := he_br ▸ h_brbin
  -- the flag sum equals `is_real` (in `env.get` form).
  have hsumreal : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
      + env.get (i₀ + 4) + env.get (i₀ + 5) = input_is_real := by
    rw [hg0, hg1, hg2, hg3, hg4, hg5]; exact h_realsum.symm
  -- eval-of-input word bridges (rs1/rs2/pc), reused from soundness, in `env.toEnvironment` form.
  have hpc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc = input_state_pc :=
    h_input.2.1.2.2.2
  have ep0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ha1eq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by rw [ep0, ep1, ep2]
  have ha1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p)) := ha1eq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := by
    have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num
  have hcimm : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c_imm
      = input_adapter_op_c_imm := h_input.2.2.2.2.2.2.2
  have hcimmeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] : Word (ZMod p))
      = input_adapter_op_c_imm := by
    rw [← hcimm]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  -- rs1/rs2 eval-word bridges + isU64 (soundness lines 173-196, in `env.toEnvironment` form).
  have hrs1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_a_memory_prev_value[0], input_adapter_op_a_memory_prev_value[1],
        input_adapter_op_a_memory_prev_value[2], input_adapter_op_a_memory_prev_value[3]] := by
    rw [← h_input.2.2.2.1.1]; simp only [Vector.getElem_map]
  have hrs2eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [← h_input.2.2.2.2.2.2.1.1]; simp only [Vector.getElem_map]
  have hrs1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hrs2U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs2eq ▸ h_rs2U
  -- one-hot bound + the `is_signed = is_blt + is_bge` binary fact (soundness lines 211-223).
  have hsumbin : (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
      + env.get (i₀ + 4) + env.get (i₀ + 5)) * (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2)
        + env.get (i₀ + 3) + env.get (i₀ + 4) + env.get (i₀ + 5) + -1) = 0 := by
    rw [hsumreal]; rcases h_bin with h | h <;> rw [h] <;> simp
  have h_onehot := one_hot6 fb0 fb1 fb2 fb3 fb4 fb5 hsumbin
  have h_sig_bin : env.get (i₀ + 2) + env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 2) + env.get (i₀ + 3) = 1 := by
    rcases fb2 with hl | hl <;> rcases fb3 with hg | hg
    · left; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · exfalso
      have := val_of_bool (h := fb0); have := val_of_bool (h := fb1)
      have := val_of_bool (h := fb4); have := val_of_bool (h := fb5)
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rw [hl, hg, ZMod.val_one] at h_onehot
      omega
  -- the subcircuit `Assumptions` (conjunct 1), reused to obtain its `Spec` from `he_lt`.
  have h_lt_asm : LtOperationSigned.circuit.Assumptions
      ⟨#v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]],
        #v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]],
        env.get (i₀ + 2) + env.get (i₀ + 3)⟩ :=
    ⟨hrs1U, hrs2U, h_sig_bin⟩
  -- the witnessed add-result vectors are the corresponding `populate`s (JalChip pattern).
  have hbv : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 6 + 1 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] input_adapter_op_c_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_bv ⟨i, hi⟩, hcimmeq]
  have hfv : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 6 + 1 + 4 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] #v[4, 0, 0, 0] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_fv ⟨i, hi⟩]
  -- per-limb add-result values (for the two `value[3] = 0` asserts), bridged to the input words.
  have hbv3 : env.get (i₀ + 6 + 1 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_c_imm)[3] := by
    have := congrArg (·[3]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hfv3 : env.get (i₀ + 6 + 1 + 4 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0])[3] := by
    have := congrArg (·[3]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  -- the additive fall-through gate `is_real - is_branching` is binary on every row.
  have h_gate2 : input_is_real + -env.get (i₀ + 6) = 0 ∨ input_is_real + -env.get (i₀ + 6) = 1 := by
    rcases h_bin with h | h
    · have hbr0 : env.get (i₀ + 6) = 0 := by rw [he_br]; exact h_brpad h
      rw [h, hbr0]; simp
    · rcases brb with hb | hb <;> rw [h, hb] <;> simp
  -- per-limb branch/fall-through values, in `populate` form (the `hbv3`/`hfv3` pattern).
  have hbt0 : env.get (i₀ + 6 + 1) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[0] := by
    have := congrArg (·[0]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hbt1 : env.get (i₀ + 6 + 1 + 1) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[1] := by
    have := congrArg (·[1]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hbt2 : env.get (i₀ + 6 + 1 + 2) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[2] := by
    have := congrArg (·[2]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hft0 : env.get (i₀ + 6 + 1 + 4) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[0] := by
    have := congrArg (·[0]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hft1 : env.get (i₀ + 6 + 1 + 4 + 1) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[1] := by
    have := congrArg (·[1]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hft2 : env.get (i₀ + 6 + 1 + 4 + 2) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[2] := by
    have := congrArg (·[2]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  -- unfold `committedNextPc` in the gated byte-range assumptions into `populate` form.
  simp only [committedNextPc, branchTargetWord, fallThroughWord] at h_ranges
  -- the committed `next_pc` limbs, in `populate` mux form (matches the unfolded `h_ranges`).
  have hnp0 : env.get (i₀ + 6 + 1 + 4 + 4) = hintBranching env.hint * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[0]
      + (input_is_real - hintBranching env.hint) * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[0] := by
    have h := he_np ⟨0, by omega⟩
    simp only [Nat.add_zero, List.getElem_cons_zero] at h
    rw [he_br, hbt0, hft0] at h; exact h
  have hnp1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = hintBranching env.hint * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[1]
      + (input_is_real - hintBranching env.hint) * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[1] := by
    have h := he_np ⟨1, by omega⟩
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [he_br, hbt1, hft1] at h; exact h
  have hnp2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = hintBranching env.hint * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[2]
      + (input_is_real - hintBranching env.hint) * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[2] := by
    have h := he_np ⟨2, by omega⟩
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [he_br, hbt2, hft2] at h; exact h
  refine ⟨h_lt_asm, ?_, ?_, ?_, ?_, ?_, ?_, hsumreal.symm, hsumbin, ?_, ?_, ?_,
    ⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨ha1U, h_imm⟩, brb⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩, ?_⟩, ?_,
    ?_, ?_, ?_, ⟨h_bin, h_it⟩, ?_, ?_, ?_⟩
  · rcases fb0 with h | h <;> rw [h] <;> simp
  · rcases fb1 with h | h <;> rw [h] <;> simp
  · rcases fb2 with h | h <;> rw [h] <;> simp
  · rcases fb3 with h | h <;> rw [h] <;> simp
  · rcases fb4 with h | h <;> rw [h] <;> simp
  · rcases fb5 with h | h <;> rw [h] <;> simp
  · rcases brb with h | h <;> rw [h] <;> simp
  · -- decision: `is_real * (is_branching - decision) = 0` — delegated to `Decision`.
    -- the `===` constraint carrier is the `field` element type `id (ZMod p)`; give `linear_combination`
    -- its commutative-ring instance (defeq to `ZMod p`'s).
    haveI : CommRing (id (ZMod p)) := inferInstanceAs (CommRing (ZMod p))
    rcases h_bin with h | h
    · rw [h]; simp
    · rw [h, one_mul]
      -- the signed-compare gadget `Spec` (from the subcircuit's `ProverSpec` in `h_env`).
      have h_lt_spec := he_lt h_lt_asm
      simp only [LtOperationSigned.circuit, LtOperationSigned.Spec] at h_lt_spec
      obtain ⟨h_bit, h_eqf, h_eqbin⟩ := h_lt_spec
      rw [hrs1eq, hrs2eq] at h_bit h_eqf
      simp only [Vector.getElem_map] at h_eqf h_eqbin
      -- the honest per-opcode decisions, in `env.get` / `rs1WordInput`-unfolded form.
      have hdec := h_dec h
      simp only [rs1WordInput, rs2WordInput] at hdec h_rs1U h_rs2U
      rw [← he_br, ← hg0, ← hg1, ← hg2, ← hg3, ← hg4, ← hg5] at hdec
      obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := hdec
      have hone : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
          + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [hsumreal]; exact h
      have key := branch_decision_eq_of_conditions h_rs1U h_rs2U fb0 fb1 fb2 fb3 fb4 fb5 brb hone
        h_bit h_eqf h_eqbin hd0 hd1 hd2 hd3 hd4 hd5
      simp only [branchDecision] at key
      simp only [LtOperationSigned.circuit]
      linear_combination key
  · -- padding `(is_real - 1) * is_branching = 0`.
    rcases h_bin with h | h
    · have hbr0 : env.get (i₀ + 6) = 0 := by rw [he_br]; exact h_brpad h
      rw [h, hbr0]; simp
    · rw [h]; simp
  · -- AddOp1 (branch target) Spec.
    rw [hbv]; exact AddOperation.spec_populate ha1U h_imm (env.get (i₀ + 6))
  · -- branch_value[3] = 0.
    rw [hbv3]; exact h_bt3
  · -- AddOp2 (fall-through) Spec.
    rw [hfv]; exact AddOperation.spec_populate ha1U h4U (input_is_real + -env.get (i₀ + 6))
  · -- fall_value[3] = 0.
    rw [hfv3]; exact h_ft3
  · -- next_pc[0] selection.
    simpa [sub_eq_add_neg] using he_np 0
  · -- next_pc[1] selection.
    simpa [sub_eq_add_neg] using he_np 1
  · -- next_pc[2] selection.
    simpa [sub_eq_add_neg] using he_np 2
  · -- byte pull 0: next_pc[0] / 4 alignment (width 14).
    intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    simp only [byteChannel, hnp0]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (h_ranges hr1).1

  · -- byte pull 1: next_pc[1] u16 (width 16).
    intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
    simp only [byteChannel, hnp1]
    rw [← c16]
    exact (byteRowSpec_range _ h16p).mpr (h_ranges hr1).2.1
  · -- byte pull 2: next_pc[2] u16 (width 16).
    intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
    simp only [byteChannel, hnp2]
    rw [← c16]
    exact (byteRowSpec_range _ h16p).mpr (h_ranges hr1).2.2

/-- The BRANCH chip row as a `GeneralFormalCircuit`: conditional control flow, composing the signed-compare
gadget, the two witnessed `AddOperation` targets, and the immutable I-type reader; output is the extracted
`BranchColumns`. Both soundness and completeness are proven and axiom-clean (completeness uses honest
`ProverHint` opcode-flag witnesses). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs BranchColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.BranchChip
