import SP1Clean.Trace
import SP1Clean.Readers.RTypeReader
import SP1Clean.Model.InteractionBus
import SP1Clean.Chips.ProgramChip
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.InteractionRecovery


/-! # Trace-level Program-bus (instruction-fetch) consistency

The trace-level meaning of the `.program` interaction that `Readers/RTypeReader.lean` + the chip
commit (sibling of `Soundness/StateConsistency.lean` for the State bus). SP1's `RTypeReader::eval`
emits one `send (.program …) is_trusted` per row (`Extracted/RTypeReader.lean:82`) — the
instruction fetch — gated, on the Add chip, by `is_real` (`is_trusted = is_real`).

We project each row to a single signed `LookupAccess` contribution (`Row.programLookups`, `+is_real`)
feeding the multiset bus of `Foundations/InteractionBus.lean`, and to a `ProgramAccess` record. The
program-bus consistency is **membership**: every real row's fetched `(pc, opcode, operands)` tuple lies
in the committed program ROM. That ROM is the off-chip `ProgramChip`'s receive side, not modelled here,
so — exactly as the State bus threads `TraceStateLink` — the membership link is threaded as
`TraceProgramLink`. The per-row projection and the padding-gating lemma `programLookups_padding`
(padding rows contribute 0 to every program-bus key) are proven natively. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open SP1Clean.ProgramChip (ProgramRow programRowKey ProgramProvider inROM_of_provider)

variable {p : ℕ}

/-- Per-row program-bus record: the program counter, opcode (`0` for Add — the field is the program
table's, not the per-row meaning), the three register operands, the `op_a_0` flag, and the `is_real`
gate. -/
structure ProgramAccess (F : Type) where
  pc : Vector F 3
  opcode : F
  op_a : F
  op_b : Word F
  imm_b : F
  op_c : Word F
  op_a_0 : F
  imm_c : F
  is_real : F

/-- Program-access projection for an Add row. `opcode := 0` mirrors `Extracted/AddChip.lean`'s CS2
call shape (`RTypeReader.constraints … 0 …`); the register operands and `op_a_0` are committed adapter
columns. -/
def programAccess (r : Trace.RowView (ZMod p)) : ProgramAccess (ZMod p) :=
  { pc := r.state.pc, opcode := r.opcode,
    op_a := r.adapter.op_a, op_b := r.adapter.op_b, imm_b := r.adapter.imm_b,
    op_c := r.adapter.op_c,
    op_a_0 := r.adapter.op_a_0, imm_c := r.adapter.imm_c, is_real := r.is_real }

/-- Drop the `is_real` gate (not part of the bus key) to get the instruction `ProgramRow` whose
`programRowKey` is the access's Program-bus key — the bridge from a trace access to the receiver model. -/
def ProgramAccess.toRow (pa : ProgramAccess (ZMod p)) : ProgramRow (ZMod p) :=
  { pc0 := pa.pc[0], pc1 := pa.pc[1], pc2 := pa.pc[2], opcode := pa.opcode,
    op_a := pa.op_a, op_b := pa.op_b, imm_b := pa.imm_b, op_c := pa.op_c,
    op_a_0 := pa.op_a_0, imm_c := pa.imm_c }

/-- The single signed Program-bus contribution an Add row emits: a `send` of the 16-tuple instruction
fetch at `+is_real` (matching the `.send (.program …) is_trusted` args at `Extracted/RTypeReader.lean:82`
with `opcode = 0`, `is_trusted = is_real`). On padding rows (`is_real = 0`) the multiplicity vanishes
(`programLookups_padding`). -/
def programLookups (r : Trace.RowView (ZMod p)) : LookupAccessList :=
  let pa := programAccess r
  [ (.Program, "SP1Program",
      [pa.pc[0].val, pa.pc[1].val, pa.pc[2].val, pa.opcode.val, pa.op_a.val,
        pa.op_b[0].val, pa.op_b[1].val, pa.op_b[2].val, pa.op_b[3].val,
        pa.op_c[0].val, pa.op_c[1].val, pa.op_c[2].val, pa.op_c[3].val,
        pa.op_a_0.val, pa.imm_b.val, pa.imm_c.val],
      (pa.is_real.val : ℤ)) ]

/-- Aggregate the trace into its per-row program-access list, in chronological order. -/
def aggregateProgramAccesses (rows : List (Trace.RowView (ZMod p))) : List (ProgramAccess (ZMod p)) :=
  rows.map programAccess

/-- Program-bus consistency: every *real* row's fetched instruction `ProgramRow` lies in the committed
program ROM (`inROM`, the off-chip `ProgramChip`'s membership predicate, `Chips/ProgramChip.lean`). -/
def ProgramConsistent (inROM : ProgramRow (ZMod p) → Prop)
    (accesses : List (ProgramAccess (ZMod p))) : Prop :=
  ∀ a ∈ accesses, a.is_real ≠ 0 → inROM a.toRow

/-- Trace-shape Program-bus invariant: the aggregated accesses are program-consistent. -/
structure TraceProgramValid (rows : List (Trace.RowView (ZMod p)))
    (inROM : ProgramRow (ZMod p) → Prop) : Prop where
  rom_holds : ProgramConsistent inROM (aggregateProgramAccesses rows)

/-- **The crux (threaded).** Instruction-fetch membership in the committed program ROM. Discharged from
the native `ProgramProvider` + a balanced Program bus by `programConsistent_of_balance` below; the only
residual assumption is the LogUp/GKR `isConsistentBalanced`. -/
def TraceProgramLink (rows : List (Trace.RowView (ZMod p)))
    (inROM : ProgramRow (ZMod p) → Prop) : Prop :=
  ProgramConsistent inROM (aggregateProgramAccesses rows)

/-- Discharge of `TraceProgramValid` from the threaded program link (a re-bundling). -/
theorem traceProgramValid_of_programLink (rows : List (Trace.RowView (ZMod p)))
    (inROM : ProgramRow (ZMod p) → Prop) (h_link : TraceProgramLink rows inROM) :
    TraceProgramValid rows inROM :=
  ⟨h_link⟩

/-- **Gating is real.** A padding row (`is_real = 0`) contributes zero to every Program-bus key: its
single signed contribution has multiplicity 0. The emission is `is_real`-gated, matching SP1's
`send … is_trusted` (`is_trusted = is_real` on Add). -/
theorem programLookups_padding [NeZero p] (r : Trace.RowView (ZMod p)) (h : r.is_real = 0) :
    ∀ k, multiplicitySum (programLookups r) k = 0 := by
  have hz : ((programAccess r).is_real.val : ℤ) = 0 := by
    simp only [programAccess, h, ZMod.val_zero, Nat.cast_zero]
  intro k
  simp only [programLookups, multiplicitySum_cons, multiplicitySum_nil, multOf, hz,
    ite_self, add_zero]

/-- **`TraceProgramLink` discharged down to bus balance.** Given a native `ProgramProvider` (SP1's
preprocessed program/decode chip — it carries only validly-decoded ROM rows, `Chips/ProgramChip.lean`)
and a *balanced* Program bus (the LogUp/GKR fact, the lone remaining threaded assumption), every real
row's fetched instruction is an `inROM`-valid row. The argument mirrors `byteAccessValid_of_balance`: a
real send has multiplicity `is_real.val > 0`; on a balanced bus the provider must cancel it
(`provider_touches_pos_send`), so it carries an entry at that key; the provider only carries valid rows,
and the key determines the row, so the fetched row is that valid row. Instantiated with
`ProgramChip.ProgramRowSpec` this hands the register-index bounds / pc bounds / `op_a_0` boolean — the
*received* facts `Channels.ProgramMsg.Spec` defers — to every real instruction fetch. -/
theorem programConsistent_of_balance [NeZero p]
    (rows : List (Trace.RowView (ZMod p))) (prov : LookupAccessList)
    (inROM : ProgramRow (ZMod p) → Prop)
    (h_prov : ProgramProvider inROM prov)
    (h_bal : isConsistentBalanced (aggregateChipRows rows programLookups ++ prov)) :
    TraceProgramLink rows inROM := by
  intro a ha h_real
  simp only [aggregateProgramAccesses, List.mem_map] at ha
  obtain ⟨r, hr, rfl⟩ := ha
  -- the unique Program-bus contribution this row emits
  set send : LookupAccess :=
    (.Program, "SP1Program",
      [(programAccess r).pc[0].val, (programAccess r).pc[1].val, (programAccess r).pc[2].val,
        (programAccess r).opcode.val, (programAccess r).op_a.val,
        (programAccess r).op_b[0].val, (programAccess r).op_b[1].val,
        (programAccess r).op_b[2].val, (programAccess r).op_b[3].val,
        (programAccess r).op_c[0].val, (programAccess r).op_c[1].val,
        (programAccess r).op_c[2].val, (programAccess r).op_c[3].val,
        (programAccess r).op_a_0.val, (programAccess r).imm_b.val, (programAccess r).imm_c.val],
      ((programAccess r).is_real.val : ℤ)) with hsend
  have h_eq : programLookups r = [send] := by rw [hsend]; rfl
  have h_send_mem : send ∈ aggregateChipRows rows programLookups :=
    List.mem_flatMap.mpr ⟨r, hr, by rw [h_eq]; exact List.mem_singleton.mpr rfl⟩
  have hvne : (programAccess r).is_real.val ≠ 0 := fun hv =>
    h_real (ZMod.val_injective p (by rw [ZMod.val_zero]; exact hv))
  have h_pos : 0 < multOf send := by rw [hsend]; simp only [multOf]; omega
  have h_nonneg : ∀ b ∈ aggregateChipRows rows programLookups, 0 ≤ multOf b := by
    intro b hb
    obtain ⟨r', _, hb'⟩ := List.mem_flatMap.mp hb
    simp only [programLookups, List.mem_singleton] at hb'
    subst hb'
    simp only [multOf]; positivity
  obtain ⟨b, hb, hkey⟩ := provider_touches_pos_send _ prov h_nonneg h_bal send h_send_mem h_pos
  have hak : keyOf send = programRowKey (programAccess r).toRow := by
    rw [hsend]; simp only [keyOf, programRowKey, ProgramAccess.toRow]
  exact inROM_of_provider h_prov hb (hkey.trans hak)

/-! ## emitted = projection (Program bus) -/

open Circuit SP1Clean.InteractionRecovery
open SP1Clean.Channels (programChannel ProgramMsg)

/-- **emitted = projection for the Program bus.** The hand-written `programLookups r` equals the
`toAccess`-image of the single Program interaction `Readers/RTypeReader.lean` emits at `offset`: the
three byte-only `RegisterAccessCols` subcircuits and the `op_a_0` Equality gates are filtered out,
leaving the lone program fetch whose `toAccess` matches `programLookups` field-for-field under the
row-realises-circuit hypotheses. So `programLookups` is a derived projection of the real emission
(the Program sibling of `StateConsistency.stateLookups_eq_emitted`). -/
theorem programLookups_eq_emitted [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (r : Trace.RowView (ZMod p)) (env : Environment (ZMod p)) (offset : ℕ)
    (input : Var Readers.RTypeReader.Inputs (ZMod p))
    (h_real : r.is_real = 0 ∨ r.is_real = 1)
    (h_it : Expression.eval env input.is_trusted = r.is_real)
    (h_p0 : Expression.eval env input.pc[0] = r.state.pc[0])
    (h_p1 : Expression.eval env input.pc[1] = r.state.pc[1])
    (h_p2 : Expression.eval env input.pc[2] = r.state.pc[2])
    (h_oc : Expression.eval env input.opcode = r.opcode)
    (h_oa : Expression.eval env input.cols.op_a = r.adapter.op_a)
    (h_ob : Expression.eval env input.cols.op_b = r.adapter.op_b[0])
    (h_ob1 : r.adapter.op_b[1] = 0) (h_ob2 : r.adapter.op_b[2] = 0) (h_ob3 : r.adapter.op_b[3] = 0)
    (h_immb : r.adapter.imm_b = 0)
    (h_oct : Expression.eval env input.cols.op_c = r.adapter.op_c[0])
    (h_oc1 : r.adapter.op_c[1] = 0) (h_oc2 : r.adapter.op_c[2] = 0) (h_oc3 : r.adapter.op_c[3] = 0)
    (h_immc : r.adapter.imm_c = 0)
    (h_oa0 : Expression.eval env input.cols.op_a_0 = r.adapter.op_a_0) :
    programLookups r =
      (((Readers.RTypeReader.main input).operations offset).interactionsWith
          programChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  -- The three `RegisterAccessCols` sub-assertions emit only `byteChannel`, and the five `op_a_0` Equality
  -- gates emit nothing — so their `programChannel` filter is empty (`filter_interactions_formalAssertion_eq_nil`).
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit programChannel.toRaw
      (n := n) inp (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair id id) (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) programChannel.toRaw
      (n := n) inp List.not_mem_nil List.not_mem_nil
  have hp2 : 2 < p := by
    have h := Fact.out (p := 2 ^ 17 < p)
    have h2 : (2 : ℕ) < 2 ^ 17 := by norm_num
    omega
  -- reduce `interactionsWith` to the single program emit (RAC subs + Equality gates + memory emits drop;
  -- the memory emits' `if memoryChannel = programChannel` collapse via the channel distinctness + `if_false`)
  simp only [Readers.RTypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.memoryChannel_eq_programChannel_false, if_false]
  -- `toAccess` the lone emit (the kernel matches the `_root_.emitted` form `circuit_norm` leaves),
  -- then bind to `programLookups` via the realisation hypotheses
  simp only [toAccess_pushIf_program]
  simp [circuit_norm, signedVal_is_real hp2 h_real, programLookups, programAccess,
    h_it, h_p0, h_p1, h_p2, h_oc, h_oa, h_ob, h_ob1, h_ob2, h_ob3, h_immb,
    h_oct, h_oc1, h_oc2, h_oc3, h_immc, h_oa0, ZMod.val_zero]

end SP1Clean.Soundness
