import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Proofs.Chips.AddiChip.Bridge

/-! # `AddiChip.advance` — the per-Addi-row `try_step` lift (SC Phase 4, I-type)

The first I-type chip on the uniform `advance` track — the I-type analog of `AddChip.advance`. Closes
`TargetObligations.lift` for ADDI rows: given a state refining an Addi row plus the operand-value bound and
the chip `Spec`, one real `try_step` produces the row's committed `RowEffect`. All the plumbing is generic —
the ∀-state decode (`decodesIType`), the fetch, the register read, and the `try_step` composition
(`advance_write_core`) live in `Advance.advance_of_itype`; this is the thin adapter, sourcing the ADDI
opcode and the write-value identity `hval` (`rdWrite = op_b + op_c`, from `AddiChip.Spec`'s gated `RV64.add`
conjunct) — the immediate operand `op_c = op_c_imm` and the round-trip `toBitVec64_bitVecToWord` are handled
inside `advance_of_itype`. Same `inp.adapter = cols.adapter` passthrough note as `AddChip.advance`. -/

namespace SP1Clean.AddiChip

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **`AddiChip.advance`.** For a state `s` refining an Addi row `AddiChip.kind.view inp cols`, the value
bound, the fetch truth, the chip `Spec`, a real-row selector, the passthrough `inp.adapter = cols.adapter`,
and `op_a ≠ 0`, one real `try_step` produces the row's committed `RowEffect` — closing the per-Addi-row
`TargetObligations.lift`. A ~12-line adapter: ADDI opcode + the write identity `hval` handed to
`advance_of_itype`, the rest by `rfl`. -/
theorem advance {prog : GuestProgram} {s : SailState}
    (inp : AddiChip.Inputs (ZMod p)) (cols : Extracted.AddiCols (ZMod p)) (data : ProverData (ZMod p))
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (AddiChip.kind.view inp cols))))
    (hvalb : ValueOperandsBound (AddiChip.kind.view inp cols) s)
    (hspec : AddiChip.Spec inp cols data) (hreal : inp.is_real = 1)
    (hlink : inp.adapter = cols.adapter) (hstatelink : inp.state = cols.state)
    (hnonX0 : (AddiChip.kind.view inp cols).adapter.op_a ≠ 0)
    (hdecrom : decodedInROM prog (programAccess (AddiChip.kind.view inp cols)).toRow) :
    ∃ s', SailStep s s' ∧ RowEffect prog (AddiChip.kind.view inp cols) s s' := by
  set r := AddiChip.kind.view inp cols with hr
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopc : r.adapter.op_c = cols.adapter.op_c_imm := rfl
  obtain ⟨hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal
  rw [hstatelink] at hpc0
  have hop : r.opcode = ((iopToOpcode iop.ADDI).toNat : ZMod p) := by
    simp [hr, AddiChip.kind, iopToOpcode, Opcode.toNat]
  have hval : Word.toBitVec64 r.rdWrite
      = Word.toBitVec64 r.adapter.op_b_memory.prev_value + Word.toBitVec64 r.adapter.op_c := by
    have hidentity := harith hreal
    simp only [AddiChip.Inputs.op_b_val, AddiChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopc, hidentity, RV64.add]
  exact advance_of_itype hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

end SP1Clean.AddiChip
