import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Proofs.Chips.AddChip.Bridge

/-! # `AddChip.advance` — the per-Add-row `try_step` lift (SC Phase 4)

Closes `TargetObligations.lift` for Add rows: given a state refining an Add row (config + ROM + the
committed pc, from `RefinesAt`) and the row's operand-value bounds + the chip `Spec`, one real `try_step`
produces the row's committed `RowEffect`. All the R-type plumbing is now generic — the ∀-state decode
(`decodesRType`), the fetch, the register reads, and the `try_step` composition live in
`Advance.advance_of_rtype`; **this file is the thin per-chip adapter**, sourcing `advance_of_rtype`'s two
op-specific inputs (the opcode column and the write-value identity `hval`) from `AddChip.Spec`, plus the
column-shape facts by `rfl`.

The reader-passthrough well-formedness `inp.adapter = cols.adapter` (the chip commits its input adapter
columns straight into `cols.adapter`; the arithmetic `Spec` names them via `inp`, the view/buses via `cols`)
is an explicit hypothesis here — the eventual `chipRows_advance_sound` dispatcher discharges it from the
trace construction (`cols = main inp`, i.e. `AddChip.main` returns `⟨…, input.adapter, …⟩`). -/

namespace SP1Clean.AddChip

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **`AddChip.advance`.** For a state `s` refining an Add row `AddChip.kind.view inp cols`
(`SailConfigured` + `RomLoaded` + the committed pc), the Memory-bus value bound (`ValueOperandsBound`), the
Program-bus fetch truth (`decodedInROM`), the chip `Spec`, a real-row selector, the reader-passthrough
`inp.adapter = cols.adapter`, and the routing fact `op_a ≠ 0` (Add takes only `rd ≠ x0`), one real
`try_step` takes `s` to the row's committed `RowEffect`. Closes the per-Add-row `TargetObligations.lift`
seam by handing the generic `advance_of_rtype` the ADD opcode fact and the write-value identity (from the
chip `Spec`'s gated `RV64.add` conjunct + `rv64add_eq_execute_RTYPE_pure`, threading the passthrough link). -/
theorem advance {prog : GuestProgram} {s : SailState}
    (inp : AddChip.Inputs (ZMod p)) (cols : Extracted.AddCols (ZMod p)) (data : ProverData (ZMod p))
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (AddChip.kind.view inp cols))))
    (hvalb : ValueOperandsBound (AddChip.kind.view inp cols) s)
    (hspec : AddChip.Spec inp cols data) (hreal : inp.is_real = 1)
    (hlink : inp.adapter = cols.adapter)
    (hnonX0 : (AddChip.kind.view inp cols).adapter.op_a ≠ 0)
    (hdecrom : decodedInROM prog (programAccess (AddChip.kind.view inp cols)).toRow) :
    ∃ s', SailStep s s' ∧ RowEffect prog (AddChip.kind.view inp cols) s s' := by
  set r := AddChip.kind.view inp cols with hr
  -- the view projections (all defeq to the underlying `cols` columns).
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  -- unpack the chip `Spec`: the reader sub-`Spec` (pc-limb bounds) and the gated add identity.
  obtain ⟨-, hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal
  -- the ADD opcode column.
  have hop : r.opcode = ((ropToOpcode rop.ADD).toNat : ZMod p) := by
    simp [hr, AddChip.kind, ropToOpcode, Opcode.toNat]
  -- the write value, from the add identity + the ADD execute identity (via the passthrough link).
  have hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) rop.ADD := by
    have hidentity := harith hreal
    simp only [AddChip.Inputs.op_b_val, AddChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopcm, hidentity, rv64add_eq_execute_RTYPE_pure]
  -- the generic R-type advance: opcode + `hval` are the only per-chip inputs; the rest are `rfl`.
  exact advance_of_rtype rop.ADD hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

end SP1Clean.AddChip
