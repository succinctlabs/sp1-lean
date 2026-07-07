import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Proofs.Chips.SubChip.Bridge

/-! # `SubChip.advance` — the per-Sub-row `try_step` lift (SC Phase 4)

The second chip on the uniform `advance` track, validating that a Tier-A R-type sibling is a **thin
adapter** over the generic `Advance.advance_of_rtype`: the only per-chip inputs are the opcode column
(`SUB`) and the write-value identity `hval` (from `SubChip.Spec`'s gated `RV64.sub` conjunct via the
chip-local `rv64sub_eq_execute_RTYPE_pure`). Everything else — the ∀-state decode, fetch, register reads,
and the `try_step` composition — is reused unchanged from Add. See `AddChip/Advance.lean` for the pattern
and the `inp.adapter = cols.adapter` passthrough note. -/

namespace SP1Clean.SubChip

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **The SUB execute identity.** The RV64 `SUB` semantics (`RV64.sub rs2 rs1 = rs1 - rs2`) equal the pure
R-type execute value (`execute_RTYPE_pure op1 op2 SUB = op1 - op2`); the bridge tying `SubChip.Spec`'s
result to the value `advance_of_rtype` writes. The SUB twin of `rv64add_eq_execute_RTYPE_pure`. -/
theorem rv64sub_eq_execute_RTYPE_pure (a b : BitVec 64) :
    RV64.sub b a = execute_RTYPE_pure a b rop.SUB := by
  simp [RV64.sub, execute_RTYPE_pure]

/-- **`SubChip.advance`.** For a state `s` refining a Sub row `SubChip.kind.view inp cols`, the value
bound, the fetch truth, the chip `Spec`, a real-row selector, the passthrough `inp.adapter = cols.adapter`,
and `op_a ≠ 0`, one real `try_step` produces the row's committed `RowEffect` — closing the per-Sub-row
`TargetObligations.lift`. A ~10-line adapter: opcode `SUB` + `hval` handed to `advance_of_rtype`, the rest
by `rfl`. -/
theorem advance {prog : GuestProgram} {s : SailState}
    (inp : SubChip.Inputs (ZMod p)) (cols : Extracted.SubCols (ZMod p)) (data : ProverData (ZMod p))
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (SubChip.kind.view inp cols))))
    (hvalb : ValueOperandsBound (SubChip.kind.view inp cols) s)
    (hspec : SubChip.Spec inp cols data) (hreal : inp.is_real = 1)
    (hlink : inp.adapter = cols.adapter)
    (hnonX0 : (SubChip.kind.view inp cols).adapter.op_a ≠ 0)
    (hdecrom : decodedInROM prog (programAccess (SubChip.kind.view inp cols)).toRow) :
    ∃ s', SailStep s s' ∧ RowEffect prog (SubChip.kind.view inp cols) s s' := by
  set r := SubChip.kind.view inp cols with hr
  have vrd : r.rdWrite = cols.sub_operation.value := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  obtain ⟨-, hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal
  have hop : r.opcode = ((ropToOpcode rop.SUB).toNat : ZMod p) := by
    simp [hr, SubChip.kind, ropToOpcode, Opcode.toNat]
  have hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) rop.SUB := by
    have hidentity := harith hreal
    simp only [SubChip.Inputs.op_b_val, SubChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopcm, hidentity, rv64sub_eq_execute_RTYPE_pure]
  exact advance_of_rtype rop.SUB hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

end SP1Clean.SubChip
