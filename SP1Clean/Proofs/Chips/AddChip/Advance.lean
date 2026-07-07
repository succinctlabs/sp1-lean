import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Proofs.Chips.AddChip.Bridge

/-! # `AddChip.advance` — the per-Add-row `try_step` lift (SC Phase 4 pilot)

The pilot that closes `TargetObligations.lift` for Add rows: given a state refining an Add row (config +
ROM + the committed pc, from `RefinesAt`) and the row's operand-value bounds + the chip `Spec`, one real
`try_step` produces the row's committed `RowEffect`. The generic composition is `Advance.advance_of_regWrite`
(L11); this file **sources its hypotheses from the bus facts** — the decode from the Program-bus `ProgTruth`
(`decodedInROM`), the register reads from the Memory-bus value bound (`ValueOperandsBound`), the fetch from
`RomLoaded`, and the write value + pc-limb bounds from `AddChip.Spec` — and reads off the `RowEffect`.

Two of the pieces are **R-type-generic** and land here as reusable lemmas for the fan-out:
- `regidx_bv_inj` — `regidxVal` is injective on the register-index range (`< 32 < p`).
- `decodesAdd` — the ∀-configured-state `RTYPE(ADD)` decode from a row's `ProgTruth` membership (the
  fan-out swaps `instrToProgramRow_inv_add` for the op's inversion sibling).

The reader-passthrough well-formedness `inp.adapter = cols.adapter` (the chip commits its input adapter
columns straight into `cols.adapter`; the arithmetic `Spec` names them via `inp`, the view/buses via `cols`)
is an explicit hypothesis here — the eventual `chipRows_advance_sound` dispatcher discharges it from the
trace construction (`cols = main inp`). -/

namespace SP1Clean.AddChip

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **`regidxVal` is injective on the register-index range.** Two register indices with equal committed
`op_a`/`op_b`/`op_c` columns (`(·.toNat : ZMod p)`) are equal — the indices are `< 32 < p`, so `Nat.cast`
does not collide. The pinning fact the ∀-state decode uniqueness rides. -/
theorem regidx_bv_inj {x y : BitVec 5} (h : (x.toNat : ZMod p) = (y.toNat : ZMod p)) : x = y := by
  have hp : (2 : ℕ) ^ 24 < p := Fact.out
  have hxy : x.toNat = y.toNat := by
    have hh := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (by have := x.isLt; omega),
      ZMod.val_natCast_of_lt (by have := y.isLt; omega)] at hh
  exact BitVec.eq_of_toNat_eq hxy

/-- **The ∀-configured-state `RTYPE(ADD)` decode from a row's `ProgTruth` membership.** From
`decodedInROM prog row` on a row whose committed opcode is `ADD`'s and whose `imm_c = 0`, the fetched ROM
word `w` decodes — **in every configured Sail state** — to `RTYPE (rs2, rs1, rd, ADD)` with the register
indices pinned to the row's committed operand columns. A configured witness `s0` instantiates the
`decodedInROM` body; `regidx_bv_inj` pins the (per-state existential) decode to the single instruction the
row's columns determine, lifting it to the uniform ∀-state form `advance_of_regWrite` consumes. The Add
opcode inversion is `instrToProgramRow_inv_add`; the fan-out swaps in the op's sibling. -/
theorem decodesAdd {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROM prog row)
    (hop : row.opcode = ((ropToOpcode rop.ADD).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, rop.ADD)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_add hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_add hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'
    simp only [regidxVal] at h
    exact h.symm)
  subst e2 e1 e0
  rw [hi2] at hrun2
  exact hrun2

/-- **L12 — `AddChip.advance`.** For a state `s` refining an Add row `AddChip.kind.view inp cols`
(`SailConfigured` + `RomLoaded` + the committed pc), the Memory-bus value bound (`ValueOperandsBound`), the
Program-bus fetch truth (`decodedInROM`), the chip `Spec`, a real-row selector, the reader-passthrough
`inp.adapter = cols.adapter`, and the routing fact `op_a ≠ 0` (Add takes only `rd ≠ x0`), one real
`try_step` takes `s` to the row's committed `RowEffect`. This closes the per-Add-row `TargetObligations.lift`
seam by sourcing every hypothesis of `advance_of_regWrite` (L11) from these bus facts. -/
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
  -- the view's projections (all defeq to the underlying `cols` columns).
  have vpc : r.state.pc = cols.state.pc := rfl
  have vopa : r.adapter.op_a = cols.adapter.op_a := rfl
  have vopb : r.adapter.op_b = #v[cols.adapter.op_b, 0, 0, 0] := rfl
  have vopc : r.adapter.op_c = #v[cols.adapter.op_c, 0, 0, 0] := rfl
  have vimmb : r.adapter.imm_b = 0 := rfl
  have vimmc : r.adapter.imm_c = 0 := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  -- unpack the chip `Spec`: the reader sub-`Spec` (pc-limb bounds) and the gated add identity.
  obtain ⟨-, hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal
  -- the row-column bridges (`(programAccess r).toRow.<f>` is defeq the view's adapter column).
  have hop0 : (programAccess r).toRow.opcode = ((ropToOpcode rop.ADD).toNat : ZMod p) := by
    simp [programAccess, ProgramAccess.toRow, hr, AddChip.kind, ropToOpcode, Opcode.toNat]
  have himm0 : (programAccess r).toRow.imm_c = (0 : ZMod p) := vimmc
  -- the ∀-state RTYPE(ADD) decode + the register-index columns, from the Program-bus `ProgTruth`.
  obtain ⟨w, rs2, rs1, rd, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesAdd hdecrom hop0 himm0 hcfg
  -- the fetch key: the row's committed pc reassembles to the fetch address.
  have hpckey : pcBitsOfRow (programAccess r).toRow = rcvPcOf (stateAccess r) := by
    simp [programAccess, ProgramAccess.toRow, pcBitsOfRow, rcvPcOf, stateAccess, pcBitsOfVals, hr,
      AddChip.kind]
  rw [hpckey] at hfetch
  -- the local fetch predicate from `RomLoaded` (L7).
  have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch hpcread
  -- the two register reads, from the value bound at the decoded indices.
  have hidxb : (rs1.toNat : ZMod p) = r.adapter.op_b[0] := by
    have h : r.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] := hopb
    rw [h]; rfl
  have hidxc : (rs2.toNat : ZMod p) = r.adapter.op_c[0] := by
    have h : r.adapter.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopc
    rw [h]; rfl
  have hrs1 : SailState.get_reg? s rs1 = some (Word.toBitVec64 r.adapter.op_b_memory.prev_value) :=
    hvalb.1 rs1 vimmb hidxb
  have hrs2 : SailState.get_reg? s rs2 = some (Word.toBitVec64 r.adapter.op_c_memory.prev_value) :=
    hvalb.2 rs2 vimmc hidxc
  -- `rd ≠ x0`, from the routing fact `op_a ≠ 0`.
  have hrd_ne : rd ≠ 0#5 := by
    intro h0; apply hnonX0
    rw [show r.adapter.op_a = (rd.toNat : ZMod p) from hopa, h0]; simp
  -- the write value, from the add identity + the ADD execute identity (via the passthrough link).
  have hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) rop.ADD := by
    have hidentity := harith hreal
    simp only [AddChip.Inputs.op_b_val, AddChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopcm, hidentity, rv64add_eq_execute_RTYPE_pure]
  -- the straight-line next-pc shape (definitional for Add).
  have hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]] := rfl
  -- assemble `advance_of_regWrite`.
  exact advance_of_regWrite rop.ADD rs2 rs1 rd _ _ (rcvPcOf (stateAccess r))
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
    hcfg hpcread rfl hfetchReady
    (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
    hrs1 hrs2 hrd_ne (show (rd.toNat : ZMod p) = r.adapter.op_a from hopa.symm) hval hstraight hpc0

end SP1Clean.AddChip
