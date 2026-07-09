import SP1Clean.Soundness.TargetVm
import SP1Clean.Soundness.ProgramConsistency
import SP1Clean.Soundness.ProgramProviderSpike
import SP1Clean.Model.Opcode
import SP1Clean.Model.SailDecode
import SP1Clean.Model.Semantics.Decode

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
  obtain ⟨w₀, hfetch₀, hdec⟩ := h_link.rom_holds (programAccess r) ha_mem h_real'
  have hpc : pcBitsOfRow (programAccess r).toRow = rcvPcOf (stateAccess r) := by
    simp only [pcBitsOfRow, rcvPcOf, programAccess, ProgramAccess.toRow, stateAccess]
  rw [hpc, hfetch] at hfetch₀
  obtain rfl : w = w₀ := Option.some.inj hfetch₀
  have hpcvec : rowPcVec (programAccess r).toRow = r.state.pc := by
    simp only [rowPcVec, programAccess, ProgramAccess.toRow]
    ext j hj
    interval_cases j <;> simp
  rw [hpcvec] at hdec
  obtain ⟨i, hr, hrow⟩ := hdec s hcfg
  exact ⟨i, s, hr, hrow⟩

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

set_option maxRecDepth 10000 in
omit [Fact (2 ^ 24 < p)] in
/-- **W3-A closed for a concrete instruction.** The committed `addRow` is the decode of `addProgram`'s
ROM word at its pc, against the official Sail `ext_decode` — `decodedInROM` holds, axiom-clean modulo the
Sail model's decoder axioms. -/
theorem decodedInROM_addRow : decodedInROM addProgram (addRow (p := p)) := by
  refine ⟨0x003100B3#32, ?_, ?_⟩
  · haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    simp only [pcBitsOfRow, addRow, pcBitsOfVals, ZMod.val_zero, ZMod.val_one, addProgram,
      GuestProgram.fetchWord, List.find?_cons, List.find?_nil]
    norm_num
  · intro s hcfg
    refine ⟨.RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD),
      SP1Clean.SailDecode.decode_ADD_example s hcfg.init hcfg.priv, ?_⟩
    rw [instrToProgramRow_rtype]; rfl

end SP1Clean.Soundness.Target
