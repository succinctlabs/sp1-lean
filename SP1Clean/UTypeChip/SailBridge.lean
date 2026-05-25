import SP1Clean.UTypeChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `UTypeChip`

The chip's `Assertion.FormalSpec` (`Cols.lean`) carries only a pure BitVec
`RV64.lui` / `RV64.auipc` fact (conditional on `is_real = 1 ∧ op_a_0 = 0`);
the monadic Sail equivalence to `_root_.UType.spec_lui` / `spec_auipc` is
*not* in `FormalSpec`. This file provides the on-demand bridge that
downstream trace-Sail proofs invoke to recover the Sail-monadic form.

`sail_correct_of_formalSpec` composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(UType.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.UType.correct_lui` / `correct_auipc` (the Main-level
  Sail-equivalence proofs in `SP1Chips/UType/UTypeChip.lean`).

The dispatch on `is_auipc` happens externally here (matching the
`soundness_utype` aggregator in `SP1Chips/Soundness.lean`): the chip's
binary gate `is_auipc * (is_auipc - 1) = 0` pins `is_auipc ∈ {0, 1}`, then
either branch routes to the matching `correct_*` theorem. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.UType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

open LeanRV64D.Functions BitVec Sail

theorem sail_correct_of_formalSpec
    (cols : UTypeCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_real : cols.is_real = 1)
    (s : SailState)
    (h_init : utypeInitialState_cols cols s) :
    (sp1_utype_cols cols).run s =
      (if cols.is_auipc = 1
       then (_root_.UType.spec_auipc (sp1_op_b_cols cols)
              (.Regidx (sp1_op_a_cols cols))).run s
       else (_root_.UType.spec_lui (sp1_op_b_cols cols)
              (.Regidx (sp1_op_a_cols cols))).run s) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_addop, h_jtr, _h_isr_bin, h_isa_bin,
          h_addend0, h_addend1, h_addend2, _h_op_a_0, _h_bitvec⟩ := h_spec
  -- Round-trip: `fromMain (toMain cols) = cols`, using the UserMode
  -- TrustMode marker from `Assumptions`.
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  -- `(toMain cols)[30] = cols.is_real = 1` reduces by `@[reducible]` toMain.
  have h_isreal' : (toMain cols)[30] = 1 := h_is_real
  -- Reconstruct each structural conjunct shaped against `fromMain (toMain cols)`,
  -- whose @[reducible] projections unfold to `#v[(toMain cols)[k], …]` — the
  -- exact literal-Vector form of `allHold_iff_structural`'s RHS. After
  -- `rw [h_round_trip]`, the goal collapses to the cols-side h_spec form.
  have h_cpu' : SP1Clean.CPUState.cpuStateSpec
      (fromMain (toMain cols)).state.clk_0_16
      (fromMain (toMain cols)).state.clk_16_24 := by
    rw [h_round_trip]; exact h_cpu
  have h_addop' : (_root_.AddOperation.constraints (F := ZMod p)
        #v[(toMain cols)[22], (toMain cols)[23], (toMain cols)[24], 0]
        #v[(toMain cols)[14], (toMain cols)[15], (toMain cols)[16], (toMain cols)[17]]
        { value := #v[(toMain cols)[25], (toMain cols)[26], (toMain cols)[27], (toMain cols)[28]] }
        (1 - (toMain cols)[13])).allHold := by
    -- Step 1: collapse `Nat.cast 1` casts that the Lemmas.lean rewrite chain
    -- inserted, restoring bare `(1 : ZMod p)` form for the gate argument.
    push_cast
    -- Step 2: bridge Word ↔ Vector-literal-of-projections via Vector.ext.
    have e_op_b : (#v[cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
                      cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3]]
                  : Vector (ZMod p) 4)
                 = cols.adapter.op_b_imm := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    have e_addr : (#v[cols.add_result[0], cols.add_result[1],
                       cols.add_result[2], cols.add_result[3]] : Vector (ZMod p) 4)
                 = cols.add_result := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    change (_root_.AddOperation.constraints (F := ZMod p)
        #v[cols.addend[0], cols.addend[1], cols.addend[2], 0]
        #v[cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
           cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3]]
        { value := #v[cols.add_result[0], cols.add_result[1],
                       cols.add_result[2], cols.add_result[3]] }
        (1 - cols.adapter.op_a_0)).allHold
    rw [e_op_b, e_addr,
        show (1 : ZMod p) - cols.adapter.op_a_0
            = cols.is_real - cols.adapter.op_a_0 from by rw [h_is_real]]
    exact h_addop
  have h_jtr' : SP1Clean.JTypeReader.jtypeReaderSpec
      ((fromMain (toMain cols)).state.clk_0_16 +
         (fromMain (toMain cols)).state.clk_16_24 * 65536)
      ((fromMain (toMain cols)).is_auipc * 48 +
         (1 - (fromMain (toMain cols)).is_auipc) * 49)
      (fromMain (toMain cols)).state.pc
      (fromMain (toMain cols)).add_result
      (fromMain (toMain cols)).adapter := by
    rw [h_round_trip]; exact h_jtr
  have h_isa_bin' : (fromMain (toMain cols)).is_auipc *
      ((fromMain (toMain cols)).is_auipc - 1) = 0 := by
    rw [h_round_trip]; exact h_isa_bin
  have h_addend0' : (fromMain (toMain cols)).addend[0] -
      (fromMain (toMain cols)).is_auipc * (fromMain (toMain cols)).state.pc[0] = 0 := by
    rw [h_round_trip]; exact h_addend0
  have h_addend1' : (fromMain (toMain cols)).addend[1] -
      (fromMain (toMain cols)).is_auipc * (fromMain (toMain cols)).state.pc[1] = 0 := by
    rw [h_round_trip]; exact h_addend1
  have h_addend2' : (fromMain (toMain cols)).addend[2] -
      (fromMain (toMain cols)).is_auipc * (fromMain (toMain cols)).state.pc[2] = 0 := by
    rw [h_round_trip]; exact h_addend2
  -- Assemble the structural conjunction matching `allHold_iff_structural`'s
  -- RHS shape and lift to SP1's `.allHold`. The Common.lean iff's
  -- `push_cast; rfl` close inserts `Nat.cast` on the 48 / 1 literals;
  -- `push_cast` here unifies the cast asymmetry on the J-type clause.
  have h_allHold : (_root_.UType.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    refine ⟨h_cpu', h_addop', ?_, h_isa_bin', h_addend0', h_addend1', h_addend2'⟩
    push_cast
    exact h_jtr'
  -- Dispatch on `is_auipc`. The chip's binary gate (in `h_isa_bin`) pins
  -- `is_auipc ∈ {0, 1}`; route to the corresponding `correct_*`.
  by_cases h_au : cols.is_auipc = 1
  · -- AUIPC branch.
    have h_au' : (toMain cols)[29] = 1 := h_au
    simp only [h_au, if_true]
    exact (_root_.UType.correct_auipc (toMain cols) s h_allHold h_isreal' h_au' h_state).symm
  · -- LUI branch: derive `is_auipc = 0` from binary + ne.
    have h_lui : cols.is_auipc = 0 := by
      rcases mul_eq_zero.mp h_isa_bin with h0 | h1
      · exact h0
      · exact absurd (sub_eq_zero.mp h1) h_au
    have h_lui' : (toMain cols)[29] = 0 := h_lui
    rw [h_lui, if_neg (show ¬((0 : ZMod p) = 1) from zero_ne_one)]
    exact (_root_.UType.correct_lui (toMain cols) s h_allHold h_isreal' h_lui' h_state).symm

end SP1Clean.UType
