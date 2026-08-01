import SP1Clean.Soundness.TargetVm
import SP1Clean.Soundness.ProgramConsistency
import SP1Clean.Soundness.ProgramProviderSpike
import SP1Clean.Model.Opcode
import SP1Clean.Model.SailDecode
import SP1Clean.Model.Semantics.Decode
import SP1Clean.FormalModel.Trace.Witness

/-! # W3 — the decode half of `OperandsBound` (trusted Program path)

The decode component of the target theorem's `OperandsBound` (`Soundness/TargetVm.lean`): each real
row's committed Program-bus operand columns are the **decode of the instruction word at its pc**, built
on the official LeanRV64D decoder (`ext_decode`/`encdec_backwards`) so fetch-decode coherence with
`try_step` holds by construction.

* `instrToProgramRow` projects a decoded LeanRV64D `instruction` to the committed Program-bus column
  shape (`ProgramChip.ProgramRow`), mirroring `Channels.ProgramMsg` / `ProgramConsistency.programAccess`
  (R-type arm first; the other opcode families follow the same convention).
* `DecodeOperandsBound prog` is the concrete decode conjunct of `OperandsBound`.
* `decodedInROM prog` is the "committed program table = decode of the guest ROM" membership predicate —
  the trusted-path instantiation of `ProgramConsistency.inROM` connecting the *encoded* `GuestProgram.rom`
  to the *decoded* committed columns.
* `decode_bound` derives `DecodeOperandsBound` for every real walk row from the (threaded) Program-bus
  consistency `TraceProgramValid rows (decodedInROM prog)` — the decode half of `TargetObligations.bound`.

The full discharge of the threaded consistency from bus balance (a `ProgramProvider (decodedInROM prog)`
via `programConsistent_of_balance`) and the W7 `try_step` decode-stage reduction that *consumes* this
predicate are tracked separately (roadmap W3 discharge / W7). -/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.ProgramChip (ProgramRow)
open SP1Clean.LookupAccessList (isConsistentBalanced aggregateChipRows)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩


/-! ## The decode conjunct of `OperandsBound` and the program-ROM membership -/

/-- **The decode component of `OperandsBound`.** In a configured state, the word fetched at the row's pc
decodes (via the official `ext_decode`) to an instruction whose projection equals the row's committed
Program-bus columns. Built on `ext_decode` so a W7 `try_step` decode-stage reduction sees the same
function. -/
def DecodeOperandsBound (prog : GuestProgram) (r : Trace.RowView (ZMod p)) (s : SailState) : Prop :=
  SailConfigured s → ∀ w, prog.fetchWord (rcvPcOf (stateAccess r)) = some w →
    ∃ i s', (ext_decode w).run s = .ok i s' ∧
      instrToProgramRow r.state.pc i = some (programAccess r).toRow


/-! ## The decode half of `TargetObligations.bound` -/

/-- **The decode half of `TargetObligations.bound`.** Every real walk row satisfies the decode conjunct
of `OperandsBound`, derived from the (threaded) Program-bus consistency that the committed program table
is the decode of the guest ROM (`decodedInROM`). The `WalkOf` trail consists of real rows
(`trail_rows_real`), each a row of the trace, so program consistency hands it its `decodedInROM` fact —
which is exactly `DecodeOperandsBound` at the row's pc. -/
theorem decode_bound (prog : GuestProgram) {pi : SP1PublicIO (ZMod p)}
    {rows : List (ChipRow p)} {path : List (Trace.RowView (ZMod p))}
    (h_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (hw : WalkOf pi rows path) {i : ℕ} (hi : i < path.length) (s : SailState) :
    DecodeOperandsBound prog (path[i]'hi) s := by
  intro hcfg w hfetch
  set r := path[i]'hi
  have hmem : r ∈ realRowEdges (rows.map ChipRow.view) :=
    Multiset.mem_of_le hw.2 (Multiset.mem_coe.mpr (List.getElem_mem hi))
  rw [realRowEdges, Multiset.mem_filter] at hmem
  obtain ⟨hr_coe, h_real⟩ := hmem
  have ha_mem : programAccess r ∈ aggregateProgramAccesses (rows.map ChipRow.view) := by
    simp only [aggregateProgramAccesses]; exact List.mem_map_of_mem (Multiset.mem_coe.mp hr_coe)
  have h_real' : (programAccess r).is_real ≠ 0 := by
    simpa only [programAccess, stateAccess] using h_real
  obtain ⟨w₀, I, hfetch₀, hrun, hrow⟩ := h_link.rom_holds (programAccess r) ha_mem h_real'
  have hpc : pcBitsOfRow (programAccess r).toRow = rcvPcOf (stateAccess r) := by
    simp only [pcBitsOfRow, rcvPcOf, programAccess, ProgramAccess.toRow, stateAccess]
  rw [hpc, hfetch] at hfetch₀
  obtain rfl : w = w₀ := Option.some.inj hfetch₀
  have hpcvec : rowPcVec (programAccess r).toRow = r.state.pc := by
    simp only [rowPcVec, programAccess, ProgramAccess.toRow]
    ext j hj
    interval_cases j <;> simp
  -- ∃I∀s (Move-2): `I` is fixed, `hrun s hcfg` runs the decode at `s`, and the guarded projection
  -- `hrow` yields the unguarded `instrToProgramRow` `DecodeOperandsBound` wants (via `_some`).
  have hrow' : instrToProgramRow (rowPcVec (programAccess r).toRow) I = some (programAccess r).toRow :=
    instrToProgramRow'_some hrow
  rw [hpcvec] at hrow'
  exact ⟨I, s, hrun s hcfg, hrow'⟩

/-! ## The balance-level decode discharge (removing the threaded link) — W3 deliverable B -/

/-- **The decode half of `bound`, from Program-bus balance — no threaded link.** Given a decoded program
ROM (`rom`, each row the decode of the guest ROM, `decodedInROM`) and a balanced Program bus, every real
walk row satisfies `DecodeOperandsBound`. Composes the constructed provider (`programProvider_of_valid` at
`P := decodedInROM prog`) with `programConsistent_of_balance` (which discharges the membership link
`decode_bound` threads as `h_link`). So the residuals are exactly (a) the per-instruction `decodedInROM`
facts — W3 deliverable A, the `ext_decode` reduction shared with W7 — and (b) the lone LogUp/GKR
`isConsistentBalanced` fact, matching how `traceProgramLink_of_validRom_and_balance` discharges the
`ProgramRowSpec` link. -/
theorem decode_bound_of_balance (prog : GuestProgram) {pi : SP1PublicIO (ZMod p)}
    {rows : List (ChipRow p)} {path : List (Trace.RowView (ZMod p))}
    (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h_decoded : ∀ row ∈ rom, decodedInROM prog row)
    (h_bal : isConsistentBalanced
      (aggregateChipRows (rows.map ChipRow.view) programLookups ++ romContributions rom mult))
    (hw : WalkOf pi rows path) {i : ℕ} (hi : i < path.length) (s : SailState) :
    DecodeOperandsBound prog (path[i]'hi) s :=
  decode_bound prog
    (traceProgramValid_of_programLink _ _
      (programConsistent_of_balance _ (romContributions rom mult) (decodedInROM prog)
        (programProvider_of_valid rom mult h_decoded) h_bal))
    hw hi s

/-- **The `TargetObligations.bound`-shaped decode statement, discharged from Program-bus balance.** The
balance-level twin of `decode_targetBound`: the `bound` field for `OperandsBound := DecodeOperandsBound prog`
with the threaded `h_link` replaced by the decoded ROM + balance. Feed this as the `bound` field when
assembling `TargetObligations` at the W3-discharged decode predicate. -/
theorem decode_targetBound_of_balance (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h_decoded : ∀ row ∈ rom, decodedInROM prog row)
    (h_bal : isConsistentBalanced
      (aggregateChipRows (rows.map ChipRow.view) programLookups ++ romContributions rom mult)) :
    ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i < path.length) s, RefinesAt prog s0 path i s →
        DecodeOperandsBound prog (path[i]'hi) s := by
  intro s0 path _h0 hw i hi s _href
  exact decode_bound_of_balance prog rom mult h_decoded h_bal hw hi s

/-! ## Wiring the decode predicate into `TargetObligations` -/

/-- **The `TargetObligations.bound` field, discharged by decode.** Exactly the shape of the `bound`
field of `TargetVm.TargetObligations` instantiated at `OperandsBound := DecodeOperandsBound prog`,
proved from the threaded Program-bus consistency via `decode_bound`. This is the decode seam closed at
the obligation level. -/
theorem decode_targetBound (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (h_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog)) :
    ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i < path.length) s, RefinesAt prog s0 path i s →
        DecodeOperandsBound prog (path[i]'hi) s := by
  intro s0 path _h0 hw i hi s _href
  exact decode_bound prog h_link hw hi s

/-- **`DecodeOperandsBound` is a valid `OperandsBound` for the target theorem.** Assemble a full
`TargetObligations` for `OperandsBound := DecodeOperandsBound prog`: the `bound` field is discharged by
`decode_targetBound` (from the threaded Program-bus consistency), and `lift`/`halt`/`halt_nonempty` are
taken as the remaining named seams (W7 step-lift, W5 ECALL/HALT). Feeding the result into
`Target.sp1_target_execution` yields the machine-level theorem with the *concrete* decode-derived
`OperandsBound`, with exactly the W7/W5 obligations open. -/
def targetObligations_of_decode (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (h_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (h_lift : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i + 1 < path.length) s,
        RefinesAt prog s0 path i s → DecodeOperandsBound prog (path[i]'(by omega)) s →
        ∃ s', SailStep s s' ∧ RowEffect prog (path[i]'(by omega)) s s')
    (h_halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ [])
    (h_halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ (hne : path ≠ []) s,
        RefinesAt prog s0 path (path.length - 1) s →
        DecodeOperandsBound prog (path[path.length - 1]'(by
          have := List.length_pos_of_ne_nil hne; omega)) s →
        SP1Halted prog (exitOf pi.exit_code) s) :
    TargetObligations prog pi rows (DecodeOperandsBound prog) where
  bound := decode_targetBound prog pi rows h_link
  lift := h_lift
  halt_nonempty := h_halt_nonempty
  halt := h_halt

/-! ## W3-A end-to-end: `decodedInROM` for a concrete instruction, via the real Sail decoder

The decode chain closed against the official decoder: a one-instruction guest program (ADD at pc 0),
the committed Program-bus row it decodes to, and a proof that `decodedInROM` holds — composing
`SailDecode.decode_ADD_example` (the `ext_decode` reduction) with `instrToProgramRow_rtype` (the
projection to committed columns). The `SailConfigured s` precondition of `decodedInROM` supplies exactly
the `isInitialized` + machine-mode residue the decode reduction consumes. This is the per-concrete-word
shape `decode_bound_of_balance` consumes (`∀ row ∈ rom, decodedInROM prog row`) — for a fixed program
each row is discharged this way. -/

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

set_option maxRecDepth 10000 in
omit [Fact (2 ^ 24 < p)] in
/-- **W3-A closed for a concrete instruction.** The committed `addRow` is the decode of `addProgram`'s
ROM word at its pc, against the official Sail `ext_decode` — `decodedInROM` holds, axiom-clean modulo the
Sail model's decoder axioms. -/
theorem decodedInROM_addRow : decodedInROM addProgram (addRow (p := p)) := by
  -- ∃I∀s shape (Move-2): the witness instruction is state-independent (a literal under `intro s hcfg`),
  -- so it hoists out of the `∀ s` verbatim; the projection is discharged on the *guarded* wrapper.
  refine ⟨0x003100B3#32,
    .RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD), ?_, ?_, ?_⟩
  · simp only [pcBitsOfRow, addRow, pcBitsOfVals, ZMod.val_zero, ZMod.val_one, addProgram,
      GuestProgram.fetchWord, List.find?_cons, List.find?_nil]
    norm_num
  · exact fun s hcfg => SP1Clean.SailDecode.decode_ADD_example s hcfg.init hcfg.priv
  · rw [instrToProgramRow'_rtype, instrToProgramRow_rtype]; rfl

end SP1Clean.Soundness.Target
