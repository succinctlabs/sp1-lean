import SP1Clean.Soundness.TargetVm

/-! # `chipRows_advance_sound` — assembling per-chip `advance`s into `TargetObligations.lift`

The Phase-4 dispatcher: it discharges `TargetObligations.lift` (`Soundness/TargetVm.lean`) — *the* open
Sail step-lift seam — **generically**, by routing each walk position to the migrated chip's
`ChipKind.advance` field (`Soundness/ChipRow.lean`, populated per chip in `Chips/<Op>Chip/Bridge.lean`).

It is the `advance`-side analogue of `GatedVm.chipRows_step_sound` (which routes `reaches_sail`): no
`cases`, no per-chip arm — adding/​migrating a chip never touches this lemma. The path→`ChipRow` inversion
(a walk row is one of the trace's real row-views, `path[i] ∈ realRowEdges (rows.map ChipRow.view)`) is done
once here by multiset membership; the chip's `advance` proof then fires.

**What this buys.** The monolithic `lift` seam is decomposed into the per-chip `advance` (done + axiom-clean
for Add/Sub/Addi) plus **three clearly-named residual obligations**, each a standard trace property:

* `h_migrated` — *coverage*: every real row's chip has migrated to `advance` (`isSome`). **Complete
  (SC Phase 4, 25/25):** `ChipRegistry.allChipKinds_migrated` proves every registered `kind.advance.isSome`,
  so for any real row whose `kind ∈ allChipKinds` this discharges — the whole fan-out landed (the last seams,
  MUL/MULHSU + the four width-8 Load/Store/Mul chips, closed via the Move-2 guarded decode).
* `h_decode` — the **Program-bus fetch truth** (`decodedInROM prog (programAccess r.view).toRow`): the
  committed instruction word is the one at the row's pc in the ROM. This is the `ProgTruth` seam (the
  semantic-channels *program flip*), not yet grounded in the soundness conclusion.
* `h_ready` — **trace well-formedness + routing** (`advanceReady`): the reader passthrough `cols = main inp`
  (`inp.adapter = cols.adapter`, and for I-type `inp.state = cols.state`) plus the `op_a ≠ 0` register-write
  routing. Both come from the trace construction (`InstructionTrace`) + the opcode routing table.

So `lift` is no longer a black box: it is `advance` (per chip) ∘ these three residuals, and a
`TargetObligations` over `OperandsBound := Target.ValueOperandsBound` can set
`lift := chipRows_advance_sound rows data h_bin h_spec h_migrated h_decode h_ready`. -/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open SP1Clean SP1Clean.Soundness
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- **Per-chip `advance` dispatch → `lift`.** From each real row's chip `Spec` (`h_spec`), the migration
coverage (`h_migrated`), the Program-bus fetch truth (`h_decode`), and the trace-well-formedness/routing
bundle (`h_ready`), every walk position `i` (before the last) takes one real Sail `try_step` to the row's
committed `RowEffect` — i.e. this is exactly `TargetObligations.lift` for `OperandsBound :=
ValueOperandsBound`. Each position is routed to its chip by inverting `path[i] ∈ realRowEdges (rows.map
ChipRow.view)` (multiset membership) and firing that chip's `ChipKind.advance`; the `RefinesAt` invariant
supplies the config/ROM/pc, and `ValueOperandsBound` the operand values. Generic — no per-chip `cases`. -/
theorem chipRows_advance_sound
    {prog : GuestProgram} {pi : SP1TargetPublicIO (ZMod p)} (rows : List (ChipRow p))
    (data : ProverData (ZMod p))
    (h_bin : ∀ r ∈ rows, r.is_real = 0 ∨ r.is_real = 1)
    (h_spec : ∀ r ∈ rows, r.chipSpec data)
    (h_migrated : ∀ r ∈ rows, r.is_real = 1 → (r.kind.advance).isSome = true)
    (h_decode : ∀ r ∈ rows, r.is_real = 1 →
      decodedInROM prog (programAccess r.view).toRow)
    (h_ready : ∀ r ∈ rows, ∀ s : SailState, r.is_real = 1 →
      r.kind.advanceReady r.inputs r.cols prog s) :
    ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i + 1 < path.length) s,
        RefinesAt prog s0 path i s → ValueOperandsBound (path[i]'(by omega)) s →
        ∃ s', SailStep s s' ∧ RowEffect prog (path[i]'(by omega)) s s' := by
  intro s0 path h0 hw i hi s href hob
  have hi' : i < path.length := by omega
  -- The walk row at `i` is one of the trace's real row-views.
  have hmem : (path[i]'hi') ∈ realRowEdges (rows.map ChipRow.view) :=
    Multiset.mem_of_le hw.2 (Multiset.mem_coe.mpr (List.getElem_mem hi'))
  rw [realRowEdges, Multiset.mem_filter, Multiset.mem_coe, List.mem_map] at hmem
  obtain ⟨⟨r, hr_mem, hr_view⟩, hr_real_ne⟩ := hmem
  -- Recover the chip `r`, real (its `is_real ≠ 0` + binary).
  have hreal : r.is_real = 1 := by
    rcases h_bin r hr_mem with h | h
    · exact absurd (show (stateAccess (path[i]'hi')).is_real = 0 by rw [← hr_view]; exact h) hr_real_ne
    · exact h
  -- Rebase the `RefinesAt` pc read and the operand bound onto `r`'s view.
  have hpc : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (ChipRow.view r))) := by
    rw [hr_view]; exact href.pc hi'
  have hvb : ValueOperandsBound (ChipRow.view r) s := by
    rw [hr_view]; exact hob
  -- Fire the migrated chip's `advance`.
  obtain ⟨pl, -⟩ := Option.isSome_iff_exists.mp (h_migrated r hr_mem hreal)
  obtain ⟨s', hstep, heff⟩ := pl.down r.inputs r.cols data prog s hreal (h_spec r hr_mem)
    href.cfg href.rom hpc hvb (h_decode r hr_mem hreal) (h_ready r hr_mem s hreal)
  have heff' : RowEffect prog (ChipRow.view r) s s' := heff
  exact ⟨s', hstep, hr_view ▸ heff'⟩

end SP1Clean.Soundness.Target
