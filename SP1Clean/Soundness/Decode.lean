import SP1Clean.Model.Opcode
import SP1Clean.Model.SailDecode
import SP1Clean.Model.Semantics.Decode
import SP1Clean.FormalModel.Trace.Witness

/-! # Decode-witness substrate: the ∀s → ∃I∀s hoists and the concrete-program shapes

Evidence layer for the Program-channel decode facts (`decodedInROM`, `Model/Semantics/Decode.lean`):

* `decodedInROMg` is the weak ∀s form over the *guarded* projection — what a decode step naturally
  yields; the hoist lemmas (`decodedInROM_rtype_hoist`, `decodedInROM_mul_hoist`) prove the
  strengthened ∃I∀s `decodedInROM` is derivable from it, so strengthening the trusted
  Program-channel guarantee costs no fundamental obligation beyond a mechanical per-family lift.
* `decodedInROM_rtype_operand_lt` recovers the 5-bit source-register bounds from the instruction
  encoding — the decode-intrinsic provenance of `rowAligned_rtype`'s operand-bound hypotheses
  (`Soundness/GroundingAdapter.lean`).
* `addProgram`/`addRow` exhibit the concrete one-instruction shape a per-family decode witness
  proves `decodedInROM` for (the end-to-end ADD witness was retired in the 4.32.2 / Sail-v5
  migration — see `Model/SailDecode.lean`; restoring one witness per instruction family is
  tracked roadmap work).

The frozen Eulerian-walk consumers that used to live here (`DecodeOperandsBound`, `decode_bound`,
the `TargetObligations` wiring) were retired with `Soundness/TargetVm.lean` (2026-08): the live
capstone derives the program-decode truth globally in `supportedCore_orderedRows_programDecoded`
(`Soundness/AIR.lean`) and consumes these hoists through the grounding contracts. -/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩


/-! ## W3-A end-to-end: the concrete-instruction decode witness (proof retired)

A one-instruction guest program (ADD at pc `0x10000`) and the committed Program-bus row it decodes
to. The end-to-end `decodedInROM` proof for this pair (`decodedInROM_addRow`, composing
`SailDecode.decode_ADD_example` — the `ext_decode` reduction — with `instrToProgramRow_rtype`) was
**removed in the 4.32.2 / Sail-v5 migration**; see the retirement notes below and in
`Model/SailDecode.lean`. The data definitions (`addProgram`/`addRow`) are retained but currently
have no in-tree consumers (their sole consumer was the removed proof): they exhibit the
per-concrete-word shape a decode witness proves (`decodedInROM prog addRow`), and a future
per-family example can be rebuilt on them. -/

/-- A one-instruction guest program: `ADD x1, x2, x3` (`0x003100B3`) at pc `0x10000` — the base of the SP1
code window `[2^16, 2^48)`, so it satisfies `rom_in_window`; the word's low two bits are `0b11`
(non-compressed), so it satisfies `rom_full_width`. Doubles as the pilot's end-to-end `advance` witness. -/
def addProgram : GuestProgram where
  rom := [(0x10000#64, 0x003100B3#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; bv_decide

/-- The committed Program-bus row the ADD decodes to — the `instrToProgramRow` projection at pc `0x10000`
(`op_a = rd = x1`, `op_b[0] = rs1 = x2`, `op_c[0] = rs2 = x3`, opcode `ADD`; `pc1 = 1` for `0x10000`). -/
def addRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((ropToOpcode rop.ADD).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-! ## The ∀s → ∃I∀s hoist (C1/Move-2) — evidence the strengthened `decodedInROM` is derivable

`decodedInROM` was strengthened (Move-2) from the weak ∀s∃i form to the ∃I∀s guarded form. These lemmas
prove that strengthening is **sound and derivable**: from `decodedInROMg` (the weak ∀s form over the
*guarded* projection — what a decode step naturally yields) plus the committed `(opcode, imm_c)` columns,
the fixed-instruction ∃I∀s `decodedInROM` follows (the row's columns pin every per-state decode to one
instruction). So strengthening the trusted Program-channel guarantee adds no new *fundamental* obligation
on the eventual grounding engine — only a mechanical per-family lift. Representative families: RTYPE
(unguarded) + MUL (guard-load-bearing, `inv_mul'` without `hpin`); the other 14 are the identical
pattern, ported on demand. -/

/-- The weak ∀s form over the *guarded* projection — what the Program provider certifies pre-hoist. -/
def decodedInROMg (prog : GuestProgram) (row : ProgramRow (ZMod p)) : Prop :=
  ∃ w, prog.fetchWord (pcBitsOfRow row) = some w ∧
    ∀ s, SailConfigured s → ∃ i, (ext_decode w).run s = .ok i s ∧
      instrToProgramRow' (rowPcVec row) i = some row

/-- A configured Sail state exists **unconditionally** (the empty-program initial state) — the side
condition the hoist instantiates to name the witness instruction `i₀`. -/
theorem sailConfigured_nonempty : ∃ s, SailConfigured s := by
  obtain ⟨s0, h⟩ := isInitialState_nonvacuous
  exact ⟨s0, h.configured⟩

/-- The pinning step shared by every `decodedInROM` hoist: a committed scalar operand column
(`op_a`) determines its register, because `regidxVal` is injective on the 5-bit range. -/
private theorem regidx_eq_of_regCol {r r' : regidx} {x : ZMod p}
    (h : x = regidxVal r) (h' : x = regidxVal r') : r' = r := by
  obtain ⟨b⟩ := r
  obtain ⟨b'⟩ := r'
  simp only [regidxVal] at h h'
  exact congrArg regidx.Regidx (regidx_bv_inj (h'.symm.trans h))

/-- The `op_b`/`op_c` twin of `regidx_eq_of_regCol`: those columns commit the register in limb `0`
of a `Word`, so the pinning goes through `v[0]`. -/
private theorem regidx_eq_of_vecCol {r r' : regidx} {v : Vector (ZMod p) 4}
    (h : v = #v[regidxVal r, 0, 0, 0]) (h' : v = #v[regidxVal r', 0, 0, 0]) : r' = r := by
  refine regidx_eq_of_regCol (x := v[0]) ?_ ?_
  · rw [h]; simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  · rw [h']; simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]

/-- **The RTYPE hoist.** Name `i₀` at the unconditional witness state; for arbitrary `s` the row's columns
pin the per-state `i` to `i₀` (both invert to `RTYPE` with `regidx_bv_inj`-equal registers). Keyed on the
committed `(opcode, imm_c)`. -/
theorem decodedInROM_rtype_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : rop)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((ropToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_rtype op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_rtype op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The R-type register-index bound, at a decoded row.**  If a committed Program-bus `row` decodes to
an R-type instruction `op` (opcode `ropToOpcode op`, `imm_c = 0`), then all three operand columns
`op_a`/`op_b[0]`/`op_c[0]` are 5-bit register indices, hence `< 32`.  This is the decode-intrinsic
provenance of `rowAligned_rtype`'s `opa_lt`/`opb_lt`/`opc_lt` hypotheses
(`Soundness/GroundingAdapter.lean`): the source indices are not range-checked in-circuit at all (the
Program bus's `ProgramMsg.RowSpec` guarantee bounds only the write index `op_a`), so the honest source of
the bound is the instruction *encoding* — recovered here by inverting the decode
(`instrToProgramRow_inv_rtype`) and applying `regidxVal_val_lt`, adding no boundary assumption beyond the
`decodedInROM` the capstone already establishes.  (Making it upfront-derivable from `decodedInROM` — never
from the grounding-time chip `Spec` — is what lets the walk's per-row `RowOK` be built before grounding.) -/
theorem decodedInROM_rtype_operand_lt {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : rop)
    (decode : decodedInROM prog row)
    (hop : row.opcode = ((ropToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0) :
    (row.op_a).val < 32 ∧ (row.op_b[0]).val < 32 ∧ (row.op_c[0]).val < 32 := by
  obtain ⟨s, hs⟩ := sailConfigured_nonempty
  obtain ⟨w, i, _hfetch, _hrun, hrow⟩ := decode.decodes s hs
  obtain ⟨rs2, rs1, rd, _hi, ha, hb, hc⟩ := instrToProgramRow_inv_rtype op hrow hop himm
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; exact regidxVal_val_lt rd
  · rw [hb]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
    exact regidxVal_val_lt rs1
  · rw [hc]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
    exact regidxVal_val_lt rs2

/-- **The MUL hoist** — the guard-load-bearing twin: Move-1's canonicity guard is what makes the per-state
`i` pinnable at all (`inv_mul'`, no `hpin`). -/
theorem decodedInROM_mul_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : mul_op)
    (hcanon : mulOpCanonical op = true)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((mulOpToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_mul' op hcanon hrow0 hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_mul' op hcanon hrow hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

-- `decodedInROM_addRow` (the concrete W3-A ADD witness) was removed in the 4.32.2 / Sail-v5
-- migration together with `SailDecode.decode_ADD_example`, which it consumed. See the retirement
-- note in `Model/SailDecode.lean`.

end SP1Clean.Soundness.Target
