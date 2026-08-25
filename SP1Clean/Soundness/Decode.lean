import SP1Clean.Model.Opcode
import SP1Clean.Model.SailDecode
import SP1Clean.Model.Semantics.Decode
import SP1Clean.FormalModel.Trace.Witness

/-! # Decode-witness substrate: the ∀s → ∃I∀s hoists and the concrete-program shapes

Evidence layer for the Program-channel decode facts (`decodedInROM`, `Model/Semantics/Decode.lean`):

* `decodedInROMg` is the weak ∀s form over the *guarded* projection — what a decode step naturally
  yields; the per-family hoist lemmas (`decodedInROM_<family>_hoist`, one per supported
  instruction family) prove the strengthened ∃I∀s `decodedInROM` is derivable from it, so
  strengthening the trusted Program-channel guarantee costs no fundamental obligation beyond a
  mechanical per-family lift.
* `decodedInROM_rtype_operand_lt` recovers the 5-bit source-register bounds from the instruction
  encoding — the decode-intrinsic provenance of `rowAligned_rtype`'s operand-bound hypotheses
  (`Soundness/GroundingAdapter.lean`).
* `addProgram`/`addRow` and the per-family `<fam>Program`/`<fam>Row` shapes exhibit the concrete
  one-instruction programs, and `decodedInROM_<fam>Row` proves the end-to-end `decodedInROM` fact
  for each of the 18 supported families on the `Model/SailDecode.lean` decode witnesses (the
  original ADD witness was retired in the 4.32.2 / Sail-v5 migration and restored 2026-08 with
  the `whnf`-cascade recipe).

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


/-! ## W3-A end-to-end: the concrete-instruction decode witnesses (restored 2026-08)

A one-instruction guest program (ADD at pc `0x10000`) and the committed Program-bus row it decodes
to — the worked template for the per-family end-to-end examples at the end of this file. The
original end-to-end proof (`decodedInROM_addRow`, composing `SailDecode.decode_ADD_example` — the
old arm-by-arm `ext_decode` reduction — with `instrToProgramRow_rtype`) was removed in the 4.32.2 /
Sail-v5 migration; it was **restored 2026-08** on the `whnf`-cascade decode recipe
(`Model/SailDecode.lean`), and the retirement is over: the per-family examples below
(`decodedInROM_<fam>Row`, all 18 supported instruction families) now discharge the concrete
`decodedInROM` shape family by family. `addProgram`/`addRow` are consumed by
`decodedInROM_addRow`. -/

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
on the eventual grounding engine — only a mechanical per-family lift. RTYPE (unguarded) and MUL
(guard-load-bearing, `inv_mul'` without `hpin`) are the two templates; the remaining families follow
below, with immediates/shift-amounts pinned through the committed `Word` columns
(`bv64_eq_of_wordCol` + the per-width injectivity lemmas) rather than `regidx` pinning alone, and
LOAD/STORE riding their guarded (`'`) inversions exactly as MUL does. -/

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

/-- The immediate twin of `regidx_eq_of_regCol`: an `op_b`/`op_c` column committed as the limb
encoding (`bitVecToWord`) of two 64-bit values pins them equal, because `Word.toBitVec64` is a
retraction of `bitVecToWord` (`toBitVec64_bitVecToWord`). The immediate-shaped hoists compose it
with the per-width injectivity of the encoding (`sext12_inj`/`sext13_inj`/`sext21_inj`/
`setWidth64_inj`). -/
private theorem bv64_eq_of_wordCol {v v' : BitVec 64} {w : Word (ZMod p)}
    (h : w = bitVecToWord v) (h' : w = bitVecToWord v') : v' = v := by
  have e := congrArg Word.toBitVec64 (h'.symm.trans h)
  rwa [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e

/-- Zero-extension to 64 bits is injective from any width `≤ 64` — the shift-amount pin for the
`SHIFTIOP`/`SHIFTIWOP` hoists (their `op_c` commits `shamt.setWidth 64`); the `setWidth` twin of
`sext12_inj`. -/
private theorem setWidth64_inj {n : ℕ} (hn : n ≤ 64) {a b : BitVec n}
    (h : a.setWidth 64 = b.setWidth 64) : a = b := by
  have key : ∀ x : BitVec n, (x.setWidth 64).setWidth n = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h64 : i < 64 := by omega
    simp [hi, h64]
  rw [← key a, ← key b, h]

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

/-- **The RTYPEW hoist** — the `execute_RTYPEW` twin of `decodedInROM_rtype_hoist` (same three
`regidx` pins, `instrToProgramRow_inv_rtypew`). -/
theorem decodedInROM_rtypew_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : ropw)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((ropwToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_rtypew op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_rtypew op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The I-type hoist** — the first immediate-shaped instance: `rs1`/`rd` pin via the `regidx`
helpers, the 12-bit immediate via the committed `op_c` word (`bv64_eq_of_wordCol` +
`sext12_inj`). -/
theorem decodedInROM_itype_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : iop)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((iopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_itype op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨imm', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_itype op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : imm' = imm := sext12_inj (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The 64-bit shift-immediate hoist** — the shift amount pins through its zero-extended `op_c`
encoding (`bv64_eq_of_wordCol` + `setWidth64_inj`). -/
theorem decodedInROM_shiftitype_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : sop)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((sopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨shamt, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_shiftitype op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨shamt', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_shiftitype op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : shamt' = shamt := setWidth64_inj (by omega) (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The word shift-immediate hoist** — as above for the 5-bit shift amount. -/
theorem decodedInROM_shiftiwtype_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (op : sopw)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((sopwToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨shamt, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_shiftiwtype op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨shamt', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_shiftiwtype op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : shamt' = shamt := setWidth64_inj (by omega) (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The ADDIW hoist** — the I-type-shaped no-`op` variant, keyed on `(opcode = ADDW,
imm_c = 1)`. -/
theorem decodedInROM_addiw_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((Opcode.ADDW).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_addiw (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨imm', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_addiw (instrToProgramRow'_some hrow) hop himm
  obtain rfl : imm' = imm := sext12_inj (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The U-type hoist** — LUI/AUIPC pin `rd` from `op_a` and the 20-bit immediate from the
shifted-immediate `op_b` encoding, whose injectivity is `sext20shl12_word_inj` directly (no
`bv64_eq_of_wordCol` detour). -/
theorem decodedInROM_utype_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : uop)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((uopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rd, hi0, ha, hb⟩ :=
    instrToProgramRow_inv_utype op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨imm', rd', hi, ha', hb'⟩ :=
    instrToProgramRow_inv_utype op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : imm' = imm := sext20shl12_word_inj imm' imm (hb'.symm.trans hb)
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The JAL hoist** — `rd` from `op_a`, the 21-bit offset from the `op_b` word
(`sext21_inj`); the `op_c = 0` conclusion carries no pinning content. -/
theorem decodedInROM_jal_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((Opcode.JAL).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rd, hi0, ha, hb, -⟩ :=
    instrToProgramRow_inv_jal (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨imm', rd', hi, ha', hb', -⟩ :=
    instrToProgramRow_inv_jal (instrToProgramRow'_some hrow) hop himm
  obtain rfl : imm' = imm := sext21_inj (bv64_eq_of_wordCol hb hb')
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The JALR hoist** — I-type-shaped: `rd`/`rs1` from `op_a`/`op_b`, the 12-bit immediate from
`op_c`. -/
theorem decodedInROM_jalr_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((Opcode.JALR).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_jalr (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨imm', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_jalr (instrToProgramRow'_some hrow) hop himm
  obtain rfl : imm' = imm := sext12_inj (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The BTYPE hoist** — branches pin `rs1` from `op_a` (a SOURCE, not a destination), `rs2` from
`op_b`, and the 13-bit offset from `op_c` (`sext13_inj`). -/
theorem decodedInROM_btype_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : bop)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((bopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rs2, rs1, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_btype op (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨imm', rs2', rs1', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_btype op (instrToProgramRow'_some hrow) hop himm
  obtain rfl : imm' = imm := sext13_inj (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rs1' = rs1 := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The DIV/DIVU hoist** — R-type pinning via `instrToProgramRow_inv_div`, keyed on the
signedness-selected opcode. -/
theorem decodedInROM_div_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROMg prog row)
    (hop : row.opcode = (((if isU then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p))
    (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_div isU (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_div isU (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The REM/REMU hoist.** -/
theorem decodedInROM_rem_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROMg prog row)
    (hop : row.opcode = (((if isU then Opcode.REMU else Opcode.REM)).toNat : ZMod p))
    (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_rem isU (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_rem isU (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The DIVW/DIVUW hoist.** -/
theorem decodedInROM_divw_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROMg prog row)
    (hop : row.opcode = (((if isU then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p))
    (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_divw isU (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_divw isU (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The REMW/REMUW hoist.** -/
theorem decodedInROM_remw_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROMg prog row)
    (hop : row.opcode = (((if isU then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p))
    (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_remw isU (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_remw isU (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The MULW hoist** — the no-`mul_op` multiply, fully fixed by `(opcode = MULW, imm_c = 0)`. -/
theorem decodedInROM_mulw_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((Opcode.MULW).toNat : ZMod p)) (himm : row.imm_c = 0) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨rs2, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_mulw (instrToProgramRow'_some hrow0) hop himm
  obtain ⟨rs2', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_mulw (instrToProgramRow'_some hrow) hop himm
  obtain rfl : rs2' = rs2 := regidx_eq_of_vecCol hc hc'
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The LOAD hoist** — the second guard-load-bearing family: like MUL it rides the *guarded*
inversion (`instrToProgramRow_inv_load'`, no `hpin`), with the width-validity guard `hwidth`
(`by decide` at each concrete width) covering the non-injective width-8 `LD` opcode too. -/
theorem decodedInROM_load_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (width : word_width) (isU : Bool) (hwidth : loadWidthOK width isU = true)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((loadOpcode width isU).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rs1, rd, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_load' width isU hwidth hrow0 hop himm
  obtain ⟨imm', rs1', rd', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_load' width isU hwidth hrow hop himm
  obtain rfl : imm' = imm := sext12_inj (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rd' = rd := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-- **The STORE hoist** — the `instrToProgramRow_inv_store'` twin of the LOAD hoist (`rs2` from
`op_a`, `rs1` from `op_b`, the 12-bit offset from `op_c`; `hwidth` covers the width-8 `SD`
case). -/
theorem decodedInROM_store_hoist {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (width : word_width) (hwidth : storeWidthOK width = true)
    (h : decodedInROMg prog row)
    (hop : row.opcode = ((storeOpcode width).toNat : ZMod p)) (himm : row.imm_c = 1) :
    decodedInROM prog row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨s0, hs0⟩ := sailConfigured_nonempty
  obtain ⟨i0, hrun0, hrow0⟩ := hbody s0 hs0
  refine ⟨w, i0, hfetch, ?_, hrow0⟩
  intro s hs
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  obtain ⟨imm, rs2, rs1, hi0, ha, hb, hc⟩ :=
    instrToProgramRow_inv_store' width hwidth hrow0 hop himm
  obtain ⟨imm', rs2', rs1', hi, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_store' width hwidth hrow hop himm
  obtain rfl : imm' = imm := sext12_inj (bv64_eq_of_wordCol hc hc')
  obtain rfl : rs1' = rs1 := regidx_eq_of_vecCol hb hb'
  obtain rfl : rs2' = rs2 := regidx_eq_of_regCol ha ha'
  rw [hi, ← hi0] at hrun
  exact hrun

/-! ## Per-family end-to-end examples — the concrete `decodedInROM` discharges

One one-instruction guest program + committed Program-bus row + `decodedInROM` proof per supported
instruction family — the 18 decode witnesses of `Model/SailDecode.lean`, each carried to the full
Program-channel fact. Every proof is the same three-step shape: the ROM fetch reduces at the
concrete singleton rom (`pcBitsOfRow_x10000` keys it at `0x10000`), the ∀-configured-state decode
is the per-family `SailDecode.decode_<X>` witness instantiated from the `SailConfigured` bundle
(`init`/`priv`/`mseccfg_disabled`, plus `misa_m` for the six M-extension families), and the
`instrToProgramRow'` projection closes by `rfl` against the transcribed row. These anchors close
the external PR110 report's Finding 3 vacuity hazard family by family: a mis-transcribed
`instrToProgramRow` arm would break its family's `rfl` here. -/

/-- Any committed row with pc limbs `(0, 1, 0)` keys the ROM at `0x10000` — the shared
`pcBitsOfRow` computation of every example row. Not a `rfl`: the pc-limb casts sit under
`ZMod.val` at a symbolic `p`, so the limbs are lifted by `ZMod.val_natCast_of_lt` first. -/
private theorem pcBitsOfRow_x10000 (row : ProgramRow (ZMod p)) (h0 : row.pc0 = 0)
    (h1 : row.pc1 = 1) (h2 : row.pc2 = 0) : pcBitsOfRow row = 0x10000#64 := by
  have hp : (2 : ℕ) ^ 24 < p := Fact.out
  have h0v : ((0 : ZMod p)).val = 0 := by
    rw [← Nat.cast_zero (R := ZMod p), ZMod.val_natCast_of_lt (by omega)]
  have h1v : ((1 : ZMod p)).val = 1 := by
    rw [← Nat.cast_one (R := ZMod p), ZMod.val_natCast_of_lt (by omega)]
  simp only [pcBitsOfRow, pcBitsOfVals, h0, h1, h2, h0v, h1v]
  rfl

/-- End-to-end R-type example: the one-ADD program's committed row is `decodedInROM`. -/
theorem decodedInROM_addRow : decodedInROM addProgram (addRow (p := p)) := by
  refine ⟨0x003100B3#32,
    .RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_ADD s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `ADDI x1, x2, 5` (`0x00510093`) at pc `0x10000` — the I-type example program. -/
def addiProgram : GuestProgram where
  rom := [(0x10000#64, 0x00510093#32)]
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

/-- The committed row `addiProgram` decodes to — the `instrToProgramRow` I-type arm at pc
`#v[0, 1, 0]`. -/
def addiRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((iopToOpcode iop.ADDI).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((5#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end I-type example. -/
theorem decodedInROM_addiRow : decodedInROM addiProgram (addiRow (p := p)) := by
  refine ⟨0x00510093#32,
    .ITYPE (5#12, regidx.Regidx 2#5, regidx.Regidx 1#5, iop.ADDI), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addiRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_ADDI s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `SLLI x1, x2, 3` (`0x00311093`) at pc `0x10000` — the shift-immediate example program. -/
def slliProgram : GuestProgram where
  rom := [(0x10000#64, 0x00311093#32)]
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

/-- The committed row `slliProgram` decodes to — the SHIFTIOP arm (zero-extended shift amount). -/
def slliRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((sopToOpcode sop.SLLI).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((3#6).setWidth 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end shift-immediate example. -/
theorem decodedInROM_slliRow : decodedInROM slliProgram (slliRow (p := p)) := by
  refine ⟨0x00311093#32,
    .SHIFTIOP (3#6, regidx.Regidx 2#5, regidx.Regidx 1#5, sop.SLLI), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (slliRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_SLLI s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `ADDIW x1, x2, 5` (`0x0051009B`) at pc `0x10000` — the W-form I-type example program. -/
def addiwProgram : GuestProgram where
  rom := [(0x10000#64, 0x0051009B#32)]
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

/-- The committed row `addiwProgram` decodes to — the ADDIW arm (opcode ADDW, `imm_c = 1`). -/
def addiwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.ADDW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((5#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end ADDIW example. -/
theorem decodedInROM_addiwRow : decodedInROM addiwProgram (addiwRow (p := p)) := by
  refine ⟨0x0051009B#32, .ADDIW (5#12, regidx.Regidx 2#5, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addiwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_ADDIW s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `ADDW x1, x2, x3` (`0x003100BB`) at pc `0x10000` — the W-form R-type example program. -/
def addwProgram : GuestProgram where
  rom := [(0x10000#64, 0x003100BB#32)]
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

/-- The committed row `addwProgram` decodes to — the RTYPEW arm. -/
def addwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((ropwToOpcode ropw.ADDW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end RTYPEW example. -/
theorem decodedInROM_addwRow : decodedInROM addwProgram (addwRow (p := p)) := by
  refine ⟨0x003100BB#32,
    .RTYPEW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, ropw.ADDW), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_ADDW s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `SLLIW x1, x2, 3` (`0x0031109B`) at pc `0x10000` — the W-form shift-immediate example
program. -/
def slliwProgram : GuestProgram where
  rom := [(0x10000#64, 0x0031109B#32)]
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

/-- The committed row `slliwProgram` decodes to — the SHIFTIWOP arm (5-bit shift amount). -/
def slliwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((sopwToOpcode sopw.SLLIW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((3#5).setWidth 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end word shift-immediate example. -/
theorem decodedInROM_slliwRow : decodedInROM slliwProgram (slliwRow (p := p)) := by
  refine ⟨0x0031109B#32,
    .SHIFTIWOP (3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, sopw.SLLIW), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (slliwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_SLLIW s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `LUI x1, 1` (`0x000010B7`) at pc `0x10000` — the U-type example program. -/
def luiProgram : GuestProgram where
  rom := [(0x10000#64, 0x000010B7#32)]
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

/-- The committed row `luiProgram` decodes to — the UTYPE arm (`op_b = op_c` the shifted
immediate, both immediate flags set). -/
def luiRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((uopToOpcode uop.LUI).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := bitVecToWord (((1#20).signExtend 64) <<< 12),
    imm_b := 1,
    op_c := bitVecToWord (((1#20).signExtend 64) <<< 12),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end U-type example. -/
theorem decodedInROM_luiRow : decodedInROM luiProgram (luiRow (p := p)) := by
  refine ⟨0x000010B7#32, .UTYPE (1#20, regidx.Regidx 1#5, uop.LUI), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (luiRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_LUI s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `JAL x1, 8` (`0x008000EF`) at pc `0x10000` — the J-type example program. -/
def jalProgram : GuestProgram where
  rom := [(0x10000#64, 0x008000EF#32)]
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

/-- The committed row `jalProgram` decodes to — the JAL arm (`op_b` the sign-extended offset,
`op_c = 0`). -/
def jalRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.JAL).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := bitVecToWord ((8#21).signExtend 64),
    imm_b := 1,
    op_c := #v[0, 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end JAL example. -/
theorem decodedInROM_jalRow : decodedInROM jalProgram (jalRow (p := p)) := by
  refine ⟨0x008000EF#32, .JAL (8#21, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (jalRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_JAL s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `JALR x1, x2, 4` (`0x004100E7`) at pc `0x10000` — the JALR example program. -/
def jalrProgram : GuestProgram where
  rom := [(0x10000#64, 0x004100E7#32)]
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

/-- The committed row `jalrProgram` decodes to — the JALR arm (I-type shape). -/
def jalrRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.JALR).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((4#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end JALR example. -/
theorem decodedInROM_jalrRow : decodedInROM jalrProgram (jalrRow (p := p)) := by
  refine ⟨0x004100E7#32, .JALR (4#12, regidx.Regidx 2#5, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (jalrRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_JALR s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `BEQ x1, x2, 8` (`0x00208463`) at pc `0x10000` — the B-type example program. -/
def beqProgram : GuestProgram where
  rom := [(0x10000#64, 0x00208463#32)]
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

/-- The committed row `beqProgram` decodes to — the BTYPE arm (`op_a = rs1`, a source; `op_c` the
sign-extended offset). -/
def beqRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((bopToOpcode bop.BEQ).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((8#13).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end B-type example. -/
theorem decodedInROM_beqRow : decodedInROM beqProgram (beqRow (p := p)) := by
  refine ⟨0x00208463#32,
    .BTYPE (8#13, regidx.Regidx 2#5, regidx.Regidx 1#5, bop.BEQ), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (beqRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_BEQ s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `LW x1, 0(x2)` (`0x00012083`) at pc `0x10000` — the LOAD example program. -/
def lwProgram : GuestProgram where
  rom := [(0x10000#64, 0x00012083#32)]
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

/-- The committed row `lwProgram` decodes to — the LOAD arm at width 4, signed (the
`loadWidthOK`-guarded projection accepts it). -/
def lwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((loadOpcode 4 false).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((0#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end LOAD example (width 4 — the `LW` opcode). -/
theorem decodedInROM_lwRow : decodedInROM lwProgram (lwRow (p := p)) := by
  refine ⟨0x00012083#32,
    .LOAD (0#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 4), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (lwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_LW s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `SW x1, 0(x2)` (`0x00112023`) at pc `0x10000` — the STORE example program. -/
def swProgram : GuestProgram where
  rom := [(0x10000#64, 0x00112023#32)]
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

/-- The committed row `swProgram` decodes to — the STORE arm at width 4 (`op_a = rs2`, the value
source; the `storeWidthOK`-guarded projection accepts it). -/
def swRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((storeOpcode 4).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((0#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end STORE example (width 4 — the `SW` opcode). -/
theorem decodedInROM_swRow : decodedInROM swProgram (swRow (p := p)) := by
  refine ⟨0x00112023#32,
    .STORE (0#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 4), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (swRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_SW s hcfg.init hcfg.priv hcfg.mseccfg_disabled
  · rfl

/-- `MUL x1, x2, x3` (`0x023100B3`) at pc `0x10000` — the M-extension multiply example program. -/
def mulProgram : GuestProgram where
  rom := [(0x10000#64, 0x023100B3#32)]
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

/-- The committed row `mulProgram` decodes to — the MUL arm at the canonical
`(Low, Signed, Signed)` descriptor (the `mulOpCanonical`-guarded projection accepts it). -/
def mulRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((mulOpToOpcode ⟨.Low, .Signed, .Signed⟩).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end MUL example (the M families additionally consume `SailConfigured.misa_m`). -/
theorem decodedInROM_mulRow : decodedInROM mulProgram (mulRow (p := p)) := by
  refine ⟨0x023100B3#32,
    .MUL (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, ⟨.Low, .Signed, .Signed⟩),
    ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (mulRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_MUL s hcfg.init hcfg.priv hcfg.mseccfg_disabled hcfg.misa_m
  · rfl

/-- `MULW x1, x2, x3` (`0x023100BB`) at pc `0x10000` — the MULW example program. -/
def mulwProgram : GuestProgram where
  rom := [(0x10000#64, 0x023100BB#32)]
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

/-- The committed row `mulwProgram` decodes to — the MULW arm. -/
def mulwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.MULW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end MULW example. -/
theorem decodedInROM_mulwRow : decodedInROM mulwProgram (mulwRow (p := p)) := by
  refine ⟨0x023100BB#32,
    .MULW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (mulwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_MULW s hcfg.init hcfg.priv hcfg.mseccfg_disabled hcfg.misa_m
  · rfl

/-- `DIV x1, x2, x3` (`0x023140B3`) at pc `0x10000` — the signed-divide example program. -/
def divProgram : GuestProgram where
  rom := [(0x10000#64, 0x023140B3#32)]
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

/-- The committed row `divProgram` decodes to — the DIV arm at `isU = false` (opcode DIV). -/
def divRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.DIV).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end DIV example. -/
theorem decodedInROM_divRow : decodedInROM divProgram (divRow (p := p)) := by
  refine ⟨0x023140B3#32,
    .DIV (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (divRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_DIV s hcfg.init hcfg.priv hcfg.mseccfg_disabled hcfg.misa_m
  · rfl

/-- `REM x1, x2, x3` (`0x023160B3`) at pc `0x10000` — the signed-remainder example program. -/
def remProgram : GuestProgram where
  rom := [(0x10000#64, 0x023160B3#32)]
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

/-- The committed row `remProgram` decodes to — the REM arm at `isU = false` (opcode REM). -/
def remRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.REM).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end REM example. -/
theorem decodedInROM_remRow : decodedInROM remProgram (remRow (p := p)) := by
  refine ⟨0x023160B3#32,
    .REM (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (remRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_REM s hcfg.init hcfg.priv hcfg.mseccfg_disabled hcfg.misa_m
  · rfl

/-- `DIVW x1, x2, x3` (`0x023140BB`) at pc `0x10000` — the W-form signed-divide example
program. -/
def divwProgram : GuestProgram where
  rom := [(0x10000#64, 0x023140BB#32)]
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

/-- The committed row `divwProgram` decodes to — the DIVW arm at `isU = false` (opcode DIVW). -/
def divwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.DIVW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end DIVW example. -/
theorem decodedInROM_divwRow : decodedInROM divwProgram (divwRow (p := p)) := by
  refine ⟨0x023140BB#32,
    .DIVW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (divwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_DIVW s hcfg.init hcfg.priv hcfg.mseccfg_disabled hcfg.misa_m
  · rfl

/-- `REMW x1, x2, x3` (`0x023160BB`) at pc `0x10000` — the W-form signed-remainder example
program. -/
def remwProgram : GuestProgram where
  rom := [(0x10000#64, 0x023160BB#32)]
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

/-- The committed row `remwProgram` decodes to — the REMW arm at `isU = false` (opcode REMW). -/
def remwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.REMW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end REMW example. -/
theorem decodedInROM_remwRow : decodedInROM remwProgram (remwRow (p := p)) := by
  refine ⟨0x023160BB#32,
    .REMW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (remwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.decode_REMW s hcfg.init hcfg.priv hcfg.mseccfg_disabled hcfg.misa_m
  · rfl

end SP1Clean.Soundness.Target
