import SP1Clean.Soundness.TypedInteractions
import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.StateCanon
import SP1Clean.Faithful.SyscallInstrsChip
import SP1Clean.Soundness.SyscallRowSemantics

/-! # Typed decoders for system tables

The BumpDecode layer: the StateBump table (stable position 52), MemoryBump table (position 51),
Halt table (position 53), and syscall table (position 54) decoded row-by-row into their chip `Inputs`, with each table's channel
contribution enumerated as the per-row semantic pull/push pairs — the exact analogue, for the
provider-segment system tables, of `DecodedInstructionRow.stateInteractions_eq` for the 25
instruction chips.

The tables carry no `ChipKind.advance` (they are canonicalization rows, not instructions); their
whole trace-level meaning is the message pairs enumerated here, consumed by the canonicalized
State balance (StateBump) and the refresh-eliminated Memory balance (MemoryBump). The rows' full
semantic `Spec`s are extracted by `Table.weakSoundness`: the bump circuits' `Assumptions` are
`True` and their byte-pull guarantees are grounded by `sp1_finishedChannel_guarantees` — the W3
partition re-cut that placed the bump tables on the byte bus's consumer side. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.Channels (stateChannel memoryChannel byteChannel programChannel exitChannel
  syscallChannel publicValuesChannel StateMsg MemoryMsg ProgramMsg ExitMsg)
open Air.Flat
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The MemoryBump table's stable position in the 55-table layout. -/
def memoryBumpIndex : ℕ := instructionTableCount + nonBumpProviderTableCount

/-- The StateBump table's stable position in the 55-table layout. -/
def stateBumpIndex : ℕ := instructionTableCount + stateSilentProviderTableCount

/-- The Halt table's stable position in the 55-table layout. -/
def haltIndex : ℕ := instructionTableCount + stateSilentProviderTableCount + 1

/-- The `SyscallInstrs` table's stable position: last, so every index above is unchanged. -/
def syscallInstrsIndex : ℕ := instructionTableCount + stateSilentProviderTableCount + 2

theorem syscallInstrsIndex_lt_tablesLength (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    syscallInstrsIndex < witness.tables.length := by
  rw [← witness.same_length]
  simp [syscallInstrsIndex, instructionTableCount, stateSilentProviderTableCount,
    sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]

theorem memoryBumpIndex_lt_tablesLength (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    memoryBumpIndex < witness.tables.length := by
  rw [← witness.same_length]
  simp [memoryBumpIndex, instructionTableCount, nonBumpProviderTableCount,
    sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]

theorem stateBumpIndex_lt_tablesLength (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    stateBumpIndex < witness.tables.length := by
  rw [← witness.same_length]
  simp [stateBumpIndex, instructionTableCount, stateSilentProviderTableCount,
    sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]

theorem haltIndex_lt_tablesLength (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    haltIndex < witness.tables.length := by
  rw [← witness.same_length]
  simp [haltIndex, instructionTableCount, stateSilentProviderTableCount,
    sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]

/-- The physical `SyscallInstrs` table selected by the stable ensemble layout. -/
noncomputable def syscallInstrsTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[syscallInstrsIndex]'(syscallInstrsIndex_lt_tablesLength witness)

/-- The physical MemoryBump table selected by the stable ensemble layout. -/
noncomputable def memoryBumpTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[memoryBumpIndex]'(memoryBumpIndex_lt_tablesLength witness)

/-- The physical StateBump table selected by the stable ensemble layout. -/
noncomputable def stateBumpTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[stateBumpIndex]'(stateBumpIndex_lt_tablesLength witness)

/-- The physical Halt table selected by the stable ensemble layout. -/
noncomputable def haltTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[haltIndex]'(haltIndex_lt_tablesLength witness)

/-- The stable MemoryBump position carries the MemoryBump circuit. -/
theorem memoryBumpTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (memoryBumpTable witness).component = { circuit := MemoryBumpChip.circuit } := by
  unfold memoryBumpTable
  have aligned := witness.same_circuits memoryBumpIndex (by
    simp [memoryBumpIndex, instructionTableCount, nonBumpProviderTableCount,
      sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The stable StateBump position carries the StateBump circuit. -/
theorem stateBumpTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (stateBumpTable witness).component = { circuit := StateBumpChip.circuit } := by
  unfold stateBumpTable
  have aligned := witness.same_circuits stateBumpIndex (by
    simp [stateBumpIndex, instructionTableCount, stateSilentProviderTableCount,
      sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The stable Halt position carries the Halt circuit. -/
theorem haltTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (haltTable witness).component = { circuit := HaltChip.circuit } := by
  unfold haltTable
  have aligned := witness.same_circuits haltIndex (by
    simp [haltIndex, instructionTableCount, stateSilentProviderTableCount,
      sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The stable `SyscallInstrs` position carries the syscall circuit. -/
theorem syscallInstrsTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (syscallInstrsTable witness).component = { circuit := SyscallInstrsChip.circuit } := by
  unfold syscallInstrsTable
  have aligned := witness.same_circuits syscallInstrsIndex (by
    simp [syscallInstrsIndex, instructionTableCount, stateSilentProviderTableCount,
      sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The Memory record a MemoryBump row pulls — the old register record (the ZMod-level mirror of
the circuit's `pulledMsg`). -/
def MemoryBumpChip.pulledMessage (r : MemoryBumpChip.Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨r.access.access_timestamp.prev_high, r.access.access_timestamp.prev_low,
    r.addr, 0, 0, r.access.prev_value⟩

/-- The Memory record a MemoryBump row pushes — the same value at the refreshed canonical
timestamp (the ZMod-level mirror of the circuit's `pushedMsg`). -/
def MemoryBumpChip.pushedMessage (r : MemoryBumpChip.Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨r.clk_24_32 + r.clk_32_48 * 256, r.clk_0_16 + r.clk_16_24 * 65536,
    r.addr, 0, 0, r.access.prev_value⟩

/-- The provider tail beyond the state-silent prefix: StateBump, Halt, and the `SyscallInstrs`
table — the three provider-segment components that name the State bus. -/
theorem tables_drop_stateBumpIndex (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.tables.drop stateBumpIndex =
      [stateBumpTable witness, haltTable witness, syscallInstrsTable witness] := by
  have hlen : witness.tables.length = 55 := by
    rw [← witness.same_length]
    simp [sp1Ensemble_tables, sp1Tables_length,
      sp1ProviderTables_length]
  simp only [stateBumpIndex, instructionTableCount, InstructionChipId.count_eq,
    stateSilentProviderTableCount]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  rfl

/-- The provider tail splits into its 27 state-silent tables and the StateBump/Halt/syscall suffix. -/
theorem tables_drop25_split (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.tables.drop instructionTableCount =
      (witness.tables.drop instructionTableCount).take stateSilentProviderTableCount ++
        witness.tables.drop stateBumpIndex := by
  rw [show witness.tables.drop stateBumpIndex =
      (witness.tables.drop instructionTableCount).drop stateSilentProviderTableCount from by
      rw [List.drop_drop]
      rfl, List.take_append_drop]

/-! ## Row decoders

The decoders are spelled `valueFromOffset` — the exact form `Component.Spec { circuit := circuit }` exposes
through `Component.rowInput` — so the two `*_spec` theorems below reach the chip `Spec` by cheap
structural delta/beta.  The `Eval.eval ∘ varFromOffset` spelling would force the unifier through
the `ProvableStruct` evaluator at the theorem head; `stateBumpRow_eq`/`memoryBumpRow_eq` recover
the evaluated form where the interaction-evaluation lemmas need it. -/

/-- A StateBump table row decoded into the chip's semantic `Inputs`. -/
noncomputable def stateBumpRow (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    StateBumpChip.Inputs (ZMod p) :=
  valueFromOffset StateBumpChip.Inputs 0 (Environment.fromArray row data)

/-- A MemoryBump table row decoded into the chip's semantic `Inputs`. -/
noncomputable def memoryBumpRow (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    MemoryBumpChip.Inputs (ZMod p) :=
  valueFromOffset MemoryBumpChip.Inputs 0 (Environment.fromArray row data)

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The decoded StateBump row, in the evaluated-`varFromOffset` form the per-row interaction
evaluations produce. -/
theorem stateBumpRow_eq [Fact p.Prime] (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    stateBumpRow data row =
      Eval.eval (Environment.fromArray row data)
        (varFromOffset StateBumpChip.Inputs 0 : Var StateBumpChip.Inputs (ZMod p)) :=
  (eval_varFromOffset_valueFromOffset _ _ _).symm

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The decoded MemoryBump row, in the evaluated-`varFromOffset` form the per-row interaction
evaluations produce. -/
theorem memoryBumpRow_eq [Fact p.Prime] (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    memoryBumpRow data row =
      Eval.eval (Environment.fromArray row data)
        (varFromOffset MemoryBumpChip.Inputs 0 : Var MemoryBumpChip.Inputs (ZMod p)) :=
  (eval_varFromOffset_valueFromOffset _ _ _).symm

/-! ## Syntactic interaction closed forms and their evaluations

Placed after the two row decoders and before the message-evaluation lemmas: the fully-projected
closed form of a decoded MemoryBump row (`memoryBumpRow_closedForm`, below the component-wise
evaluation lemmas it is assembled from) is what lets a consumer rewrite a `memoryBumpRow`-shaped
goal into `Expression.eval`-of-`varFromOffset` leaves without ever normalising the decoder. -/

omit [Fact (2 ^ 24 < p)] in
/-- The StateBump circuit's exact syntactic State pair: the possibly-non-canonical pull followed by
the canonical push, both gated by the row selector. The six byte pulls filter out. -/
theorem stateBumpMain_stateInteractions [Fact (2 ^ 17 < p)]
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StateBumpChip.main r).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulledIf r.is_real (StateBumpChip.pulledMsg r)).toRaw,
       (stateChannel.pushedIf r.is_real (StateBumpChip.pushedMsg r)).toRaw] := by
  simp [StateBumpChip.main, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- The MemoryBump circuit's exact syntactic Memory pair: the old-record pull followed by the
refreshed push, both gated by the row selector. The six byte pulls filter out. -/
theorem memoryBumpMain_memoryInteractions [Fact (2 ^ 17 < p)]
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryBumpChip.main r).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulledIf r.is_real (MemoryBumpChip.pulledMsg r)).toRaw,
       (memoryChannel.pushedIf r.is_real (MemoryBumpChip.pushedMsg r)).toRaw] := by
  change Operations.interactionsWith _
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [circuit_norm]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the StateBump pulled-message projection. -/
theorem eval_stateBump_pulledMsg [Fact p.Prime] (env : Environment (ZMod p))
    (r : Var StateBumpChip.Inputs (ZMod p)) :
    Eval.eval env (StateBumpChip.pulledMsg r) =
      StateBumpChip.pulledMessage (Eval.eval env r) := by
  simp only [StateBumpChip.pulledMessage, circuit_norm]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the StateBump pushed-message projection. -/
theorem eval_stateBump_pushedMsg [Fact p.Prime] (env : Environment (ZMod p))
    (r : Var StateBumpChip.Inputs (ZMod p)) :
    Eval.eval env (StateBumpChip.pushedMsg r) =
      StateBumpChip.pushedMessage (Eval.eval env r) := by
  simp only [StateBumpChip.pushedMessage, circuit_norm]

/-! The MemoryBump evaluation lemmas cross the nested `MemoryAccessCols` carrier, which a
`circuit_norm`-driven normalization cannot afford (the derived `ProvableStruct` evaluator blows the
`whnf` budget).  Instead, the `Readers.RTypeReader.eval_registerAccessCols` pattern: one folded
component-wise evaluation lemma per struct layer (each closed by a single `rw
[ProvableStruct.eval_eq_eval]; rfl`), then the message lemmas rewrite the layers outside-in and
close by `rfl` with every `Eval.eval` leaf kept opaque. -/

/-- Component-wise evaluation of the innermost five-column timestamp block of the shared
`MemoryAccessCols` carrier. -/
theorem eval_bumpAccessTimestamp {F : Type} [FiniteField F]
    (env : Environment F) (ts : Circuits.Types.MemoryAccessTimestamp (Expression F)) :
    Eval.eval env ts =
      ({ prev_high := Eval.eval env ts.prev_high,
         prev_low := Eval.eval env ts.prev_low,
         compare_low := Eval.eval env ts.compare_low,
         diff_low_limb := Eval.eval env ts.diff_low_limb,
         diff_high_limb := Eval.eval env ts.diff_high_limb } :
        Circuits.Types.MemoryAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the `MemoryAccessCols` carrier. -/
theorem eval_bumpAccessCols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Circuits.Types.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value,
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Circuits.Types.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the MemoryBump input row. -/
theorem eval_bumpInputs {F : Type} [FiniteField F]
    (env : Environment F) (r : MemoryBumpChip.Inputs (Expression F)) :
    Eval.eval env r =
      ({ access := Eval.eval env r.access,
         clk_32_48 := Eval.eval env r.clk_32_48,
         clk_24_32 := Eval.eval env r.clk_24_32,
         clk_16_24 := Eval.eval env r.clk_16_24,
         clk_0_16 := Eval.eval env r.clk_0_16,
         addr := Eval.eval env r.addr,
         is_real := Eval.eval env r.is_real } : MemoryBumpChip.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of a Memory bus message. -/
theorem eval_memoryMsgStruct {F : Type} [FiniteField F]
    (env : Environment F) (m : MemoryMsg (Expression F)) :
    Eval.eval env m =
      ({ clk_high := Eval.eval env m.clk_high,
         clk_low := Eval.eval env m.clk_low,
         addr0 := Eval.eval env m.addr0,
         addr1 := Eval.eval env m.addr1,
         addr2 := Eval.eval env m.addr2,
         value := Eval.eval env m.value } : MemoryMsg F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the MemoryBump pulled-message projection. -/
theorem eval_memoryBump_pulledMsg [Fact p.Prime] (env : Environment (ZMod p))
    (r : Var MemoryBumpChip.Inputs (ZMod p)) :
    Eval.eval env (MemoryBumpChip.pulledMsg r) =
      MemoryBumpChip.pulledMessage (Eval.eval env r) := by
  rw [eval_memoryMsgStruct, eval_bumpInputs, eval_bumpAccessCols, eval_bumpAccessTimestamp]
  -- Every slot is now the same folded `Eval.eval` leaf on both sides except the two constant
  -- `addr1`/`addr2` slots, whose `eval env 0 = 0` needs the `Eval` field instance unfolded.
  with_unfolding_all rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the MemoryBump pushed-message projection. -/
theorem eval_memoryBump_pushedMsg [Fact p.Prime] (env : Environment (ZMod p))
    (r : Var MemoryBumpChip.Inputs (ZMod p)) :
    Eval.eval env (MemoryBumpChip.pushedMsg r) =
      MemoryBumpChip.pushedMessage (Eval.eval env r) := by
  rw [eval_memoryMsgStruct, eval_bumpInputs, eval_bumpAccessCols, eval_bumpAccessTimestamp]
  with_unfolding_all rfl

omit [Fact (2 ^ 24 < p)] in
/-- The decoded MemoryBump row in **fully projected closed form**: every scalar cell spelled as an
`Expression.eval` of the corresponding `varFromOffset` projection, the `prev_value` word as the one
remaining folded `Eval.eval` leaf.

This is the transport a consumer needs to move a `memoryBumpRow`-shaped statement onto the
in-circuit `Expression.eval`-of-`varFromOffset` spelling (and back) *without* ever asking the
unifier to normalise the decoder: `simp only [memoryBumpRow_closedForm]` rewrites the decoded row to
a structure literal and the surrounding projections reduce by iota.  Crossing the same gap by
`exact`/`rfl` instead forces `Eval.eval`'s `fromElements ∘ Vector.map ∘ toElements` through `whnf`
once per occurrence, which is the documented decoded-row landmine
(`docs/agents/proof-patterns.md`, "Compile-time / performance landmines"). -/
theorem memoryBumpRow_closedForm (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    memoryBumpRow data row =
      ({ access :=
          { prev_value := Eval.eval (Environment.fromArray row data)
              (varFromOffset MemoryBumpChip.Inputs 0 :
                Var MemoryBumpChip.Inputs (ZMod p)).access.prev_value,
            access_timestamp :=
            { prev_high := Expression.eval (Environment.fromArray row data)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.prev_high,
              prev_low := Expression.eval (Environment.fromArray row data)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.prev_low,
              compare_low := Expression.eval (Environment.fromArray row data)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.compare_low,
              diff_low_limb := Expression.eval (Environment.fromArray row data)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.diff_low_limb,
              diff_high_limb := Expression.eval (Environment.fromArray row data)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.diff_high_limb } },
         clk_32_48 := Expression.eval (Environment.fromArray row data)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_32_48,
         clk_24_32 := Expression.eval (Environment.fromArray row data)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_24_32,
         clk_16_24 := Expression.eval (Environment.fromArray row data)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_16_24,
         clk_0_16 := Expression.eval (Environment.fromArray row data)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_0_16,
         addr := Expression.eval (Environment.fromArray row data)
           (varFromOffset MemoryBumpChip.Inputs 0).addr,
         is_real := Expression.eval (Environment.fromArray row data)
           (varFromOffset MemoryBumpChip.Inputs 0).is_real } :
        MemoryBumpChip.Inputs (ZMod p)) := by
  rw [memoryBumpRow_eq, eval_bumpInputs, eval_bumpAccessCols, eval_bumpAccessTimestamp]
  simp only [ProvableType.eval_field]

omit [Fact (2 ^ 24 < p)] in
/-- The MemoryBump circuit's **shallow constraint list in closed form**: the four `assertZero`
expressions of `MemoryBumpChip.main`, in source order.  Proved with a single `change` to the
operation-list literal (the `Readers.MemoryAccess` shape used by the chip's own `elaborated`
fields), so a consumer that needs several of the four asserts pays that one unfold instead of one
per membership proof. -/
theorem memoryBumpMain_shallowConstraints
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.shallowConstraints ((MemoryBumpChip.main r).operations offset) =
      [r.is_real * (r.is_real - 1),
       r.is_real * (r.access.access_timestamp.compare_low *
         (r.access.access_timestamp.compare_low - 1)),
       r.is_real * (r.access.access_timestamp.compare_low *
         (r.clk_24_32 + r.clk_32_48 * 256 - r.access.access_timestamp.prev_high)),
       r.is_real *
         ((r.access.access_timestamp.compare_low * (r.clk_0_16 + r.clk_16_24 * 65536)
             + (1 - r.access.access_timestamp.compare_low) * (r.clk_24_32 + r.clk_32_48 * 256)
           - (r.access.access_timestamp.compare_low * r.access.access_timestamp.prev_low
             + (1 - r.access.access_timestamp.compare_low) * r.access.access_timestamp.prev_high)
           - 1)
         - (r.access.access_timestamp.diff_low_limb
             + r.access.access_timestamp.diff_high_limb * 65536))] := by
  change Operations.shallowConstraints
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  rfl

/-! ## Typed per-table enumerations -/

/-- The StateBump table's typed State view: per physical row, the decoded semantic pull/push pair
(the provider-segment analogue of `DecodedInstructionRow.stateInteractions_eq`). -/
theorem stateBumpTable_typedState_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := StateBumpChip.circuit }) :
    typedTableInteractionsWith table data stateChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (stateBumpRow data row).is_real
           (StateBumpChip.pulledMessage (stateBumpRow data row)),
         TypedInteraction.pushedIfValue stateChannel
           (stateBumpRow data row).is_real
           (StateBumpChip.pushedMessage (stateBumpRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((StateBumpChip.main
        (varFromOffset StateBumpChip.Inputs 0 : Var StateBumpChip.Inputs (ZMod p))).operations
          (size StateBumpChip.Inputs)).interactionsWith stateChannel.toRaw) = _
  rw [stateBumpMain_stateInteractions]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw]
  rw [show ((stateChannel (p := p)).pulledIf
        (varFromOffset StateBumpChip.Inputs 0 :
          Var StateBumpChip.Inputs (ZMod p)).is_real
        (StateBumpChip.pulledMsg (varFromOffset StateBumpChip.Inputs 0))).toRaw.eval
        (Environment.fromArray row data) =
      stateChannel.pulledIfValue (stateBumpRow data row).is_real
        (StateBumpChip.pulledMessage (stateBumpRow data row)) from by
    rw [Channel.eval_pulledIf, eval_stateBump_pulledMsg]
    simp only [circuit_norm, stateBumpRow_eq]]
  rw [show ((stateChannel (p := p)).pushedIf
        (varFromOffset StateBumpChip.Inputs 0 :
          Var StateBumpChip.Inputs (ZMod p)).is_real
        (StateBumpChip.pushedMsg (varFromOffset StateBumpChip.Inputs 0))).toRaw.eval
        (Environment.fromArray row data) =
      stateChannel.pushedIfValue (stateBumpRow data row).is_real
        (StateBumpChip.pushedMessage (stateBumpRow data row)) from by
    rw [Channel.eval_pushedIf, eval_stateBump_pushedMsg]
    simp only [circuit_norm, stateBumpRow_eq]]

/-- The legacy assembly specializes the component-local State projection. -/
theorem stateBumpTable_typedState (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (stateBumpTable witness) witness.data stateChannel =
      (stateBumpTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (stateBumpRow witness.data row).is_real
           (StateBumpChip.pulledMessage (stateBumpRow witness.data row)),
         TypedInteraction.pushedIfValue stateChannel
           (stateBumpRow witness.data row).is_real
           (StateBumpChip.pushedMessage (stateBumpRow witness.data row))] :=
  stateBumpTable_typedState_of_component (stateBumpTable witness) witness.data (stateBumpTable_component witness)

/-- The MemoryBump table's typed Memory view: per physical row, the decoded old-record pull and
refreshed push. -/
theorem memoryBumpTable_typedMemory_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := MemoryBumpChip.circuit }) :
    typedTableInteractionsWith table data memoryChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pulledIfValue memoryChannel
           (memoryBumpRow data row).is_real
           (MemoryBumpChip.pulledMessage (memoryBumpRow data row)),
         TypedInteraction.pushedIfValue memoryChannel
           (memoryBumpRow data row).is_real
           (MemoryBumpChip.pushedMessage (memoryBumpRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((MemoryBumpChip.main
        (varFromOffset MemoryBumpChip.Inputs 0 : Var MemoryBumpChip.Inputs (ZMod p))).operations
          (size MemoryBumpChip.Inputs)).interactionsWith memoryChannel.toRaw) = _
  rw [memoryBumpMain_memoryInteractions]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw]
  rw [show ((memoryChannel (p := p)).pulledIf
        (varFromOffset MemoryBumpChip.Inputs 0 :
          Var MemoryBumpChip.Inputs (ZMod p)).is_real
        (MemoryBumpChip.pulledMsg (varFromOffset MemoryBumpChip.Inputs 0))).toRaw.eval
        (Environment.fromArray row data) =
      memoryChannel.pulledIfValue (memoryBumpRow data row).is_real
        (MemoryBumpChip.pulledMessage (memoryBumpRow data row)) from by
    rw [Channel.eval_pulledIf, eval_memoryBump_pulledMsg]
    simp only [circuit_norm, memoryBumpRow_eq]]
  rw [show ((memoryChannel (p := p)).pushedIf
        (varFromOffset MemoryBumpChip.Inputs 0 :
          Var MemoryBumpChip.Inputs (ZMod p)).is_real
        (MemoryBumpChip.pushedMsg (varFromOffset MemoryBumpChip.Inputs 0))).toRaw.eval
        (Environment.fromArray row data) =
      memoryChannel.pushedIfValue (memoryBumpRow data row).is_real
        (MemoryBumpChip.pushedMessage (memoryBumpRow data row)) from by
    rw [Channel.eval_pushedIf, eval_memoryBump_pushedMsg]
    simp only [circuit_norm, memoryBumpRow_eq]]

/-- The legacy assembly specializes the component-local Memory projection. -/
theorem memoryBumpTable_typedMemory (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (memoryBumpTable witness) witness.data memoryChannel =
      (memoryBumpTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue memoryChannel
           (memoryBumpRow witness.data row).is_real
           (MemoryBumpChip.pulledMessage (memoryBumpRow witness.data row)),
         TypedInteraction.pushedIfValue memoryChannel
           (memoryBumpRow witness.data row).is_real
           (MemoryBumpChip.pushedMessage (memoryBumpRow witness.data row))] :=
  memoryBumpTable_typedMemory_of_component (memoryBumpTable witness) witness.data (memoryBumpTable_component witness)

/-! ## Row specs from constraints and grounded byte pulls -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Every interaction routed to the State channel meets the channel's local guarantee: the State
bus's `Guarantees` is literally `fun _ _ => True` (`Model/Channels.lean`), independent of the
interaction's multiplicity or payload.  Stated through an auxiliary channel-generalized fact so the
arity-dependent message vector transports along the channel equality. -/
theorem stateChannel_interaction_guarantees [Fact p.Prime] (env : Environment (ZMod p))
    {i : AbstractInteraction (ZMod p)} (hchannel : i.channel = stateChannel.toRaw) :
    i.Guarantees env := by
  have h : ∀ c : RawChannel (ZMod p), c = stateChannel.toRaw →
      ∀ (m : ZMod p) (v : Vector (ZMod p) c.arity) (d : ProverData (ZMod p)),
        c.Guarantees m v d := by
    rintro _ rfl _ _ _ _
    trivial
  exact fun _ => h _ hchannel _ _ _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The Exit channel's local guarantee is likewise literally `True` — the exit binding is a pure
multiset hand-off (`Model/Channels.lean`). -/
theorem exitChannel_interaction_guarantees [Fact p.Prime] (env : Environment (ZMod p))
    {i : AbstractInteraction (ZMod p)} (hchannel : i.channel = exitChannel.toRaw) :
    i.Guarantees env := by
  have h : ∀ c : RawChannel (ZMod p), c = exitChannel.toRaw →
      ∀ (m : ZMod p) (v : Vector (ZMod p) c.arity) (d : ProverData (ZMod p)),
        c.Guarantees m v d := by
    rintro _ rfl _ _ _ _
    trivial
  exact fun _ => h _ hchannel _ _ _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The syscall bus's local guarantee is `True` as well: with no provider table, D2's carve-out is
derived from *balance* rather than from anything this channel promises. -/
theorem syscallChannel_interaction_guarantees [Fact p.Prime] (env : Environment (ZMod p))
    {i : AbstractInteraction (ZMod p)} (hchannel : i.channel = syscallChannel.toRaw) :
    i.Guarantees env := by
  have h : ∀ c : RawChannel (ZMod p), c = syscallChannel.toRaw →
      ∀ (m : ZMod p) (v : Vector (ZMod p) c.arity) (d : ProverData (ZMod p)),
        c.Guarantees m v d := by
    rintro _ rfl _ _ _ _
    trivial
  exact fun _ => h _ hchannel _ _ _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The public-values bus's local guarantee is `True`; the digest binding lives in the public-values
layer, not in this channel. -/
theorem publicValuesChannel_interaction_guarantees [Fact p.Prime] (env : Environment (ZMod p))
    {i : AbstractInteraction (ZMod p)} (hchannel : i.channel = publicValuesChannel.toRaw) :
    i.Guarantees env := by
  have h : ∀ c : RawChannel (ZMod p), c = publicValuesChannel.toRaw →
      ∀ (m : ZMod p) (v : Vector (ZMod p) c.arity) (d : ProverData (ZMod p)),
        c.Guarantees m v d := by
    rintro _ rfl _ _ _ _
    trivial
  exact fun _ => h _ hchannel _ _ _

/-- Every StateBump row satisfies the chip's semantic `Spec`: `Component.weakSoundness` with the
trivial `Assumptions`, the row's constraints, and the byte/state guarantees — byte grounded by the
finished-channel engine (the bump tables sit on its consumer side), State's guarantee `True`. -/
theorem stateBumpTable_spec_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := StateBumpChip.circuit })
    (tableConstraints : table.Constraints data) (byteGuarantees : table.ChannelGuarantees data byteChannel.toRaw) :
    ∀ row ∈ table.table,
      StateBumpChip.Spec (stateBumpRow data row) := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  intro row rowMem
  have hlist : table.component.circuit.channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw] := by
    rw [component]
    rfl
  have guarantees : table.component.operations.FullGuarantees
      (Environment.fromArray row data) := by
    simp only [Component.guarantees_iff, Component.rowOperations]
    rw [GeneralFormalCircuit.guarantees_iff]
    intro channel channelMem
    show table.component.rowOperations.ChannelGuarantees channel
      (Environment.fromArray row data)
    rw [← Component.channelGuarantees_iff]
    rw [hlist] at channelMem
    rcases List.mem_cons.mp channelMem with rfl | channelMem
    · exact byteGuarantees row rowMem
    · rw [List.mem_singleton.mp channelMem]
      intro i hi hmult
      exact stateChannel_interaction_guarantees _ hmult
  have spec := (table.component.weakSoundness
    (env := Environment.fromArray row data)
    (by rw [component]; trivial) (tableConstraints row rowMem) guarantees).1
  rw [component] at spec
  exact spec

/-- The legacy assembly supplies the local constraints and proved Byte guarantees. -/
theorem stateBumpTable_spec (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ (stateBumpTable witness).table,
      StateBumpChip.Spec (stateBumpRow witness.data row) := by
  have member := List.getElem_mem (stateBumpIndex_lt_tablesLength witness)
  exact stateBumpTable_spec_of_component (stateBumpTable witness) witness.data (stateBumpTable_component witness)
    (constraints _ member) ((sp1_finishedChannel_guarantees witness constraints balanced).2 _ member).1

/-- The MemoryBump table's per-row full guarantee bundle, assembled from the grounded byte pulls
and the supplied Memory pull guarantee.  Split out of `memoryBumpTable_spec` so the guarantee
assembly over the nested-carrier operations and the `weakSoundness` extraction below each keep
their own elaboration budget. -/
private theorem memoryBumpTable_fullGuarantees
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (byteGuarantees : (memoryBumpTable witness).ChannelGuarantees witness.data byteChannel.toRaw)
    (memoryGuarantees : (memoryBumpTable witness).ChannelGuarantees witness.data memoryChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ (memoryBumpTable witness).table) :
    (memoryBumpTable witness).component.operations.FullGuarantees
      (Environment.fromArray row witness.data) := by
  have hlist : (memoryBumpTable witness).component.circuit.channelsWithGuarantees =
      [byteChannel.toRaw, memoryChannel.toRaw] := by
    rw [memoryBumpTable_component]
    rfl
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channelMem
  show (memoryBumpTable witness).component.rowOperations.ChannelGuarantees channel
    (Environment.fromArray row witness.data)
  rw [← Component.channelGuarantees_iff]
  rw [hlist] at channelMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact byteGuarantees row rowMem
  · rw [List.mem_singleton.mp channelMem]
    exact memoryGuarantees row rowMem

/-- The per-row `Spec` extraction through `Component.weakSoundness`, from the table-level facts. -/
private theorem memoryBumpRow_spec_of_facts
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (tableConstraints : (memoryBumpTable witness).Constraints witness.data)
    (byteGuarantees : (memoryBumpTable witness).ChannelGuarantees witness.data byteChannel.toRaw)
    (memoryGuarantees : (memoryBumpTable witness).ChannelGuarantees witness.data memoryChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ (memoryBumpTable witness).table) :
    MemoryBumpChip.Spec (memoryBumpRow witness.data row) := by
  have spec := ((memoryBumpTable witness).component.weakSoundness
    (env := Environment.fromArray row witness.data)
    (by rw [memoryBumpTable_component]; trivial) (tableConstraints row rowMem)
    (memoryBumpTable_fullGuarantees witness byteGuarantees memoryGuarantees rowMem)).1
  rw [memoryBumpTable_component] at spec
  -- Cross from `Component.Spec` to the chip `Spec` in two head-congruent steps (`rowInput` is
  -- definitionally `memoryBumpRow`'s `valueFromOffset` body), so the unifier never descends into
  -- the nested-carrier `Spec` conjuncts.
  show MemoryBumpChip.Spec (Component.rowInput { circuit := MemoryBumpChip.circuit }
    (Environment.fromArray row witness.data))
  exact spec

/-- Every MemoryBump row satisfies the chip's semantic `Spec`. Beside the byte pulls this needs
the row's memory pull guarantee (`isU64 ∧ ClkBound` of the old record), supplied as the explicit
`memoryGuarantees` premise: on the Memory channel the bump table is a genuine consumer, and its
pull grounding is a memory-side balance fact, not a finished-channel one. -/
theorem memoryBumpTable_spec (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (memoryGuarantees : (memoryBumpTable witness).ChannelGuarantees witness.data memoryChannel.toRaw) :
    ∀ row ∈ (memoryBumpTable witness).table,
      MemoryBumpChip.Spec (memoryBumpRow witness.data row) := by
  have tableMem : memoryBumpTable witness ∈ witness.tables :=
    List.getElem_mem (memoryBumpIndex_lt_tablesLength witness)
  have tableConstraints : (memoryBumpTable witness).Constraints witness.data :=
    constraints _ tableMem
  have byteGuarantees := ((sp1_finishedChannel_guarantees witness constraints balanced).2
    _ tableMem).1
  intro row rowMem
  exact memoryBumpRow_spec_of_facts witness tableConstraints byteGuarantees
    memoryGuarantees rowMem

/-! ## Active MemoryBump rows -/

/-- The active rows of the MemoryBump table (mirror of `realStateBumpRows`).  Padding rows stay in
the physical table but denote no refresh edge; the with-bump Memory balance sums exactly this
filtered list. -/
noncomputable def realMemoryBumpRows
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : List (Array (ZMod p)) :=
  (memoryBumpTable witness).table.filter fun row =>
    (memoryBumpRow witness.data row).is_real = 1

/-- Membership in the active MemoryBump rows unpacks to physical-table membership plus the live
selector. -/
theorem mem_realMemoryBumpRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    {row : Array (ZMod p)} (rowMem : row ∈ realMemoryBumpRows witness) :
    row ∈ (memoryBumpTable witness).table ∧
      (memoryBumpRow witness.data row).is_real = 1 := by
  rw [realMemoryBumpRows, List.mem_filter] at rowMem
  simpa only [decide_eq_true_eq] using rowMem

/-! ## Active StateBump rows -/

/-- The active rows of the StateBump table.  Padding rows stay in the physical table but denote no
canonicalization edge; the with-bump State balance sums exactly this filtered list. -/
noncomputable def realStateBumpRows
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : List (Array (ZMod p)) :=
  (stateBumpTable witness).table.filter fun row =>
    (stateBumpRow witness.data row).is_real = 1

/-- Witness constraints and balance discharge selector booleanity for every StateBump row: it is
the first (ungated) conjunct of the row `Spec`. -/
theorem witness_stateBumpRows_selectorBinary
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ (stateBumpTable witness).table,
      (stateBumpRow witness.data row).is_real = 0 ∨
        (stateBumpRow witness.data row).is_real = 1 :=
  fun row rowMem => (stateBumpTable_spec witness constraints balanced row rowMem).1

/-! ## The Halt table decoded (the halt-table wave)

The same decode layer for the Halt table at position 53: the row decoder, the ZMod-level mirrors
of its bus messages, the per-row typed enumeration of all four gated buses plus the Exit hand-off,
the `weakSoundness` `Spec` extraction, and the active-row filter. -/

/-- A Halt table row decoded into the chip's semantic `Inputs`. -/
noncomputable def haltRow (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    HaltChip.Inputs (ZMod p) :=
  valueFromOffset HaltChip.Inputs 0 (Environment.fromArray row data)

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The decoded Halt row, in the evaluated-`varFromOffset` form the per-row interaction
evaluations produce. -/
theorem haltRow_eq [Fact p.Prime] (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    haltRow data row =
      Eval.eval (Environment.fromArray row data)
        (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p)) :=
  (eval_varFromOffset_valueFromOffset _ _ _).symm

/-- A `SyscallInstrs` table row decoded into the chip's semantic `Inputs`. -/
noncomputable def syscallInstrsRow (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    SyscallInstrsChip.Inputs (ZMod p) :=
  valueFromOffset SyscallInstrsChip.Inputs 0 (Environment.fromArray row data)

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The decoded syscall row, in the evaluated-`varFromOffset` form the per-row interaction
evaluations produce. -/
theorem syscallInstrsRow_eq [Fact p.Prime] (data : ProverData (ZMod p)) (row : Array (ZMod p)) :
    syscallInstrsRow data row =
      Eval.eval (Environment.fromArray row data)
        (varFromOffset SyscallInstrsChip.Inputs 0 : Var SyscallInstrsChip.Inputs (ZMod p)) :=
  (eval_varFromOffset_valueFromOffset _ _ _).symm

/-- One syscall register read's pulled prior record. -/
def SyscallInstrsChip.memPulledMessage (r : SyscallInstrsChip.Inputs (ZMod p))
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (idx : ZMod p) : MemoryMsg (ZMod p) :=
  ⟨r.state.clk_high, block.access_timestamp.prev_low, idx, 0, 0, block.prev_value⟩

/-- One syscall register access's read-back record at this row's access clock, carrying `value` —
the prior word for a pure read, the *written* word for `t0`. That `value` parameter is the whole
difference from the halt table's version, which only ever reads. -/
def SyscallInstrsChip.memPushedMessage (r : SyscallInstrsChip.Inputs (ZMod p))
    (idx off : ZMod p) (value : Word (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536 + off, idx, 0, 0, value⟩

/-- The Exit message a real halt-arm syscall row pushes — the reduced `op_b` word. -/
def SyscallInstrsChip.exitMessage (r : SyscallInstrsChip.Inputs (ZMod p)) : ExitMsg (ZMod p) :=
  ⟨r.op_b_memory.prev_value[0] +
    (r.op_b_memory.prev_value[1] +
      (r.op_b_memory.prev_value[2] + r.op_b_memory.prev_value[3] * 65536) * 65536) * 65536⟩

/-- The State message a halt row pulls — the pre-syscall `(clk, pc)`. -/
def HaltChip.statePulledMessage (r : HaltChip.Inputs (ZMod p)) : StateMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536,
    r.state.pc[0], r.state.pc[1], r.state.pc[2]⟩

/-- The State message a halt row pushes — the halted `(clk + 264, haltPc = (1, 0, 0))`. -/
def HaltChip.statePushedMessage (r : HaltChip.Inputs (ZMod p)) : StateMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536 + 264, 1, 0, 0⟩

/-- The Program message a halt row pulls — the committed `ECALL x5, x10, x11` at its pc. -/
def HaltChip.programMessage (r : HaltChip.Inputs (ZMod p)) : ProgramMsg (ZMod p) :=
  ⟨r.state.pc[0], r.state.pc[1], r.state.pc[2], 50, 5, #v[10, 0, 0, 0], #v[11, 0, 0, 0], 0, 0, 0⟩

/-- One halt register read's pulled prior record. -/
def HaltChip.memPulledMessage (r : HaltChip.Inputs (ZMod p))
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (idx : ZMod p) : MemoryMsg (ZMod p) :=
  ⟨r.state.clk_high, block.access_timestamp.prev_low, idx, 0, 0, block.prev_value⟩

/-- One halt register read's read-back record at this row's access clock. -/
def HaltChip.memPushedMessage (r : HaltChip.Inputs (ZMod p))
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (idx off : ZMod p) : MemoryMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536 + off, idx, 0, 0,
    block.prev_value⟩

/-- The Exit message a real halt row pushes — the reduced `x10` word. -/
def HaltChip.exitMessage (r : HaltChip.Inputs (ZMod p)) : ExitMsg (ZMod p) :=
  ⟨r.x10_memory.prev_value[0] +
    (r.x10_memory.prev_value[1] +
      (r.x10_memory.prev_value[2] + r.x10_memory.prev_value[3] * 65536) * 65536) * 65536⟩

omit [Fact (2 ^ 24 < p)] in
/-- Component-wise evaluation of the halt input row (the `AddChip.eval_inputs` pattern: consumers
rewrite this instead of unfolding the derived evaluator through the nested reader blocks). -/
theorem HaltChip.eval_inputs (env : Environment (ZMod p))
    (input : HaltChip.Inputs (Expression (ZMod p))) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, x5_memory := Eval.eval env input.x5_memory,
         x10_memory := Eval.eval env input.x10_memory,
         x11_memory := Eval.eval env input.x11_memory,
         is_real := Eval.eval env input.is_real } : HaltChip.Inputs (ZMod p)) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- The Halt table's typed State view: per physical row, the decoded pre-syscall pull and halted
push. -/
theorem haltTable_typedState_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := HaltChip.circuit }) :
    typedTableInteractionsWith table data stateChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (haltRow data row).is_real
           (HaltChip.statePulledMessage (haltRow data row)),
         TypedInteraction.pushedIfValue stateChannel
           (haltRow data row).is_real
           (HaltChip.statePushedMessage (haltRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((HaltChip.main
        (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p))).operations
          (size HaltChip.Inputs)).interactionsWith stateChannel.toRaw) = _
  rw [HaltChip.interactionsWith_state_eq]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  · rw [Channel.eval_pulledIf]
    simp only [HaltChip.statePulledMessage, circuit_norm, haltRow_eq]
  · rw [Channel.eval_pushedIf]
    simp only [HaltChip.statePushedMessage, circuit_norm, haltRow_eq]

/-- The legacy assembly specializes the component-local State projection. -/
theorem haltTable_typedState (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (haltTable witness) witness.data stateChannel =
      (haltTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (haltRow witness.data row).is_real
           (HaltChip.statePulledMessage (haltRow witness.data row)),
         TypedInteraction.pushedIfValue stateChannel
           (haltRow witness.data row).is_real
           (HaltChip.statePushedMessage (haltRow witness.data row))] :=
  haltTable_typedState_of_component (haltTable witness) witness.data (haltTable_component witness)

/-- The `SyscallInstrs` table's typed State view: per physical row, the pre-syscall pull and the
`(clk + 264, next_pc)` push. This is the table's entry into the State trail — the reason registering
it is not merely "two more buses go silent". -/
theorem syscallInstrsTable_typedState_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit }) :
    typedTableInteractionsWith table data stateChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (syscallInstrsRow data row).is_real
           (SyscallInstrsChip.statePulledMessage
             (syscallInstrsRow data row)),
         TypedInteraction.pushedIfValue stateChannel
           (syscallInstrsRow data row).is_real
           (SyscallInstrsChip.statePushedMessage
             (syscallInstrsRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((SyscallInstrsChip.main
        (varFromOffset SyscallInstrsChip.Inputs 0 : Var SyscallInstrsChip.Inputs (ZMod p))
          ).operations (size SyscallInstrsChip.Inputs)).interactionsWith stateChannel.toRaw) = _
  rw [Faithful.syscallInstrsInteractionsWith_state]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  · rw [Channel.eval_pulledIf]
    simp only [SyscallInstrsChip.statePulledMessage, Readers.CPUState.currentMsg, circuit_norm,
      syscallInstrsRow_eq]
  · rw [Channel.eval_pushedIf]
    simp only [SyscallInstrsChip.statePushedMessage, Readers.CPUState.nextMsg, circuit_norm,
      syscallInstrsRow_eq]

/-- The legacy assembly specializes the component-local State projection. -/
theorem syscallInstrsTable_typedState (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (syscallInstrsTable witness) witness.data stateChannel =
      (syscallInstrsTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.statePulledMessage
             (syscallInstrsRow witness.data row)),
         TypedInteraction.pushedIfValue stateChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.statePushedMessage
             (syscallInstrsRow witness.data row))] :=
  syscallInstrsTable_typedState_of_component (syscallInstrsTable witness) witness.data (syscallInstrsTable_component witness)

/-- One physical HALT row's Program view is its single gated ECALL pull, in any assembly. -/
theorem haltRow_typedProgram_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := HaltChip.circuit }) (row : Array (ZMod p)) :
    typedInteractionValuesWith table.component.operations programChannel (Environment.fromArray row data) =
      [TypedInteraction.pulledIfValue programChannel (haltRow data row).is_real
        (HaltChip.programMessage (haltRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((HaltChip.main
        (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p))).operations
          (size HaltChip.Inputs)).interactionsWith programChannel.toRaw) = _
  rw [HaltChip.interactionsWith_program_eq]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
  rw [Channel.eval_pulledIf]
  simp only [HaltChip.programMessage, HaltChip.programMsg, circuit_norm, haltRow_eq]

/-- The Halt table's typed Program view: per physical row, the gated committed-ECALL fetch pull. -/
theorem haltTable_typedProgram (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (haltTable witness) witness.data programChannel =
      (haltTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue programChannel
           (haltRow witness.data row).is_real
           (HaltChip.programMessage (haltRow witness.data row))] := by
  unfold typedTableInteractionsWith
  exact List.flatMap_congr (fun row _ => haltRow_typedProgram_of_component _ witness.data (haltTable_component witness) row)

/-- One syscall row's typed Program view: the single `is_real`-gated `ECALL` fetch. Split out of
`syscallInstrsTable_typedProgram` so the row's `ProgramMsg.RowSpec` can be read off at one
environment. -/
theorem syscallInstrsRow_typedProgram_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (row : Array (ZMod p)) :
    typedInteractionValuesWith table.component.operations programChannel
        (Environment.fromArray row data) =
      [TypedInteraction.pulledIfValue programChannel
         (syscallInstrsRow data row).is_real
         (SyscallInstrsChip.programMessage
           (syscallInstrsRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((SyscallInstrsChip.main
        (varFromOffset SyscallInstrsChip.Inputs 0 : Var SyscallInstrsChip.Inputs (ZMod p))
          ).operations (size SyscallInstrsChip.Inputs)).interactionsWith programChannel.toRaw) = _
  rw [Faithful.syscallInstrsInteractionsWith_program]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
  -- the anchor states this entry in raw-record form; it is defeq to the `pulledIf` spelling the
  -- evaluation lemma matches on.
  show AbstractInteraction.eval (Environment.fromArray row data)
      ((programChannel.pulledIf (varFromOffset SyscallInstrsChip.Inputs 0).is_real
        (SyscallInstrsChip.programMsg
          (varFromOffset SyscallInstrsChip.Inputs 0))).toRaw) = _
  rw [Channel.eval_pulledIf]
  simp only [SyscallInstrsChip.programMessage, SyscallInstrsChip.programMsg, circuit_norm,
    syscallInstrsRow_eq]

/-- Specialize the physical Program projection to the legacy assembly. -/
theorem syscallInstrsRow_typedProgram (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (row : Array (ZMod p)) :
    typedInteractionValuesWith (syscallInstrsTable witness).component.operations programChannel
        (Environment.fromArray row witness.data) =
      [TypedInteraction.pulledIfValue programChannel
         (syscallInstrsRow witness.data row).is_real
         (SyscallInstrsChip.programMessage
           (syscallInstrsRow witness.data row))] :=
  syscallInstrsRow_typedProgram_of_component _ witness.data (syscallInstrsTable_component witness) row

/-- The `SyscallInstrs` table's typed Program view: per physical row, the gated ECALL fetch pull. -/
theorem syscallInstrsTable_typedProgram (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (syscallInstrsTable witness) witness.data programChannel =
      (syscallInstrsTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue programChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.programMessage
             (syscallInstrsRow witness.data row))] := by
  unfold typedTableInteractionsWith
  exact List.flatMap_congr fun row _ => syscallInstrsRow_typedProgram witness row

/-- The Halt table's typed Memory view: per physical row, the three decoded register
read-prior/read-back pairs (`x5` at `+4`, `x10` at `+3`, `x11` at `+2`). -/
theorem haltTable_typedMemory_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := HaltChip.circuit }) :
    typedTableInteractionsWith table data memoryChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pulledIfValue memoryChannel
           (haltRow data row).is_real
           (HaltChip.memPulledMessage (haltRow data row)
             (haltRow data row).x5_memory 5),
         TypedInteraction.pushedIfValue memoryChannel
           (haltRow data row).is_real
           (HaltChip.memPushedMessage (haltRow data row)
             (haltRow data row).x5_memory 5 4),
         TypedInteraction.pulledIfValue memoryChannel
           (haltRow data row).is_real
           (HaltChip.memPulledMessage (haltRow data row)
             (haltRow data row).x10_memory 10),
         TypedInteraction.pushedIfValue memoryChannel
           (haltRow data row).is_real
           (HaltChip.memPushedMessage (haltRow data row)
             (haltRow data row).x10_memory 10 3),
         TypedInteraction.pulledIfValue memoryChannel
           (haltRow data row).is_real
           (HaltChip.memPulledMessage (haltRow data row)
             (haltRow data row).x11_memory 11),
         TypedInteraction.pushedIfValue memoryChannel
           (haltRow data row).is_real
           (HaltChip.memPushedMessage (haltRow data row)
             (haltRow data row).x11_memory 11 2)] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((HaltChip.main
        (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p))).operations
          (size HaltChip.Inputs)).interactionsWith memoryChannel.toRaw) = _
  rw [HaltChip.interactionsWith_memory_eq]
  simp only [HaltChip.exposedMemoryInteractions, List.map_cons, List.map_nil,
    TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
      List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩ <;>
    first
      | (rw [Channel.eval_pulledIf]
         simp only [HaltChip.memPulledMessage, HaltChip.memPullMsg, circuit_norm, haltRow_eq])
      | (rw [Channel.eval_pushedIf]
         simp only [HaltChip.memPushedMessage, HaltChip.memPushMsg, HaltChip.clkLow,
           circuit_norm, haltRow_eq])

/-- The legacy assembly specializes the component-local Memory projection. -/
theorem haltTable_typedMemory (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (haltTable witness) witness.data memoryChannel =
      (haltTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue memoryChannel
           (haltRow witness.data row).is_real
           (HaltChip.memPulledMessage (haltRow witness.data row)
             (haltRow witness.data row).x5_memory 5),
         TypedInteraction.pushedIfValue memoryChannel
           (haltRow witness.data row).is_real
           (HaltChip.memPushedMessage (haltRow witness.data row)
             (haltRow witness.data row).x5_memory 5 4),
         TypedInteraction.pulledIfValue memoryChannel
           (haltRow witness.data row).is_real
           (HaltChip.memPulledMessage (haltRow witness.data row)
             (haltRow witness.data row).x10_memory 10),
         TypedInteraction.pushedIfValue memoryChannel
           (haltRow witness.data row).is_real
           (HaltChip.memPushedMessage (haltRow witness.data row)
             (haltRow witness.data row).x10_memory 10 3),
         TypedInteraction.pulledIfValue memoryChannel
           (haltRow witness.data row).is_real
           (HaltChip.memPulledMessage (haltRow witness.data row)
             (haltRow witness.data row).x11_memory 11),
         TypedInteraction.pushedIfValue memoryChannel
           (haltRow witness.data row).is_real
           (HaltChip.memPushedMessage (haltRow witness.data row)
             (haltRow witness.data row).x11_memory 11 2)] :=
  haltTable_typedMemory_of_component (haltTable witness) witness.data (haltTable_component witness)

/-- The anchor's Exit entry at the `pushedIf` spelling — same defeq restatement as the Memory
list's below, for the same reason. -/
private theorem syscallInstrsExitInteractions_gated
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (exitChannel (p := p)).toRaw =
      [(exitChannel.pushedIf r.is_halt (SyscallInstrsChip.exitMsg r)).toRaw] :=
  Faithful.syscallInstrsInteractionsWith_exit r offset

/-- The anchor's Memory list, restated at the `pulledIf`/`pushedIf` spelling. The two forms are
definitionally equal — `pulledIf g m` *is* `{ mult := -g, msg := m, assumeGuarantees := true }` — so
this is the same proof term; but the evaluation lemmas match syntactically, and asking `show` to
bridge the gap with metavariables exhausts the recursion budget. -/
private theorem syscallInstrsMemoryInteractions_gated
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (memoryChannel (p := p)).toRaw =
      [(memoryChannel.pulledIf r.is_real
          (SyscallInstrsChip.memPullMsg r r.op_a_memory r.op_a)).toRaw,
       (memoryChannel.pushedIf r.is_real
          (SyscallInstrsChip.memPushMsg r r.op_a 4 r.op_a_value)).toRaw,
       (memoryChannel.pulledIf r.is_real
          (SyscallInstrsChip.memPullMsg r r.op_b_memory r.op_b)).toRaw,
       (memoryChannel.pushedIf r.is_real
          (SyscallInstrsChip.memPushMsg r r.op_b 3 r.op_b_memory.prev_value)).toRaw,
       (memoryChannel.pulledIf r.is_real
          (SyscallInstrsChip.memPullMsg r r.op_c_memory r.op_c)).toRaw,
       (memoryChannel.pushedIf r.is_real
          (SyscallInstrsChip.memPushMsg r r.op_c 2 r.op_c_memory.prev_value)).toRaw] :=
  Faithful.syscallInstrsInteractionsWith_memory r offset

/-- One syscall row's typed Memory view. Split out of `syscallInstrsTable_typedMemory` because the
walk needs it *per row*: the currency antecedent supplies `isU64 ∧ ClkBound` for one row's three
pulls, and `channelGuarantees_of_consumedMessages` turns exactly that into the memory
`ChannelGuarantees` the row's own `weakSoundness` consumes. -/
theorem syscallInstrsRow_typedMemory_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (row : Array (ZMod p)) :
    typedInteractionValuesWith table.component.operations memoryChannel
        (Environment.fromArray row data) =
      [TypedInteraction.pulledIfValue memoryChannel
       (syscallInstrsRow data row).is_real
       (SyscallInstrsChip.memPulledMessage (syscallInstrsRow data row)
         (syscallInstrsRow data row).op_a_memory
         (syscallInstrsRow data row).op_a),
     TypedInteraction.pushedIfValue memoryChannel
       (syscallInstrsRow data row).is_real
       (SyscallInstrsChip.memPushedMessage (syscallInstrsRow data row)
         (syscallInstrsRow data row).op_a 4
         (syscallInstrsRow data row).op_a_value),
     TypedInteraction.pulledIfValue memoryChannel
       (syscallInstrsRow data row).is_real
       (SyscallInstrsChip.memPulledMessage (syscallInstrsRow data row)
         (syscallInstrsRow data row).op_b_memory
         (syscallInstrsRow data row).op_b),
     TypedInteraction.pushedIfValue memoryChannel
       (syscallInstrsRow data row).is_real
       (SyscallInstrsChip.memPushedMessage (syscallInstrsRow data row)
         (syscallInstrsRow data row).op_b 3
         (syscallInstrsRow data row).op_b_memory.prev_value),
     TypedInteraction.pulledIfValue memoryChannel
       (syscallInstrsRow data row).is_real
       (SyscallInstrsChip.memPulledMessage (syscallInstrsRow data row)
         (syscallInstrsRow data row).op_c_memory
         (syscallInstrsRow data row).op_c),
     TypedInteraction.pushedIfValue memoryChannel
       (syscallInstrsRow data row).is_real
       (SyscallInstrsChip.memPushedMessage (syscallInstrsRow data row)
         (syscallInstrsRow data row).op_c 2
         (syscallInstrsRow data row).op_c_memory.prev_value)] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((SyscallInstrsChip.main
        (varFromOffset SyscallInstrsChip.Inputs 0 : Var SyscallInstrsChip.Inputs (ZMod p))
          ).operations (size SyscallInstrsChip.Inputs)).interactionsWith memoryChannel.toRaw) = _
  rw [syscallInstrsMemoryInteractions_gated]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    TypedInteraction.pushedIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
      List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩ <;>
    first
      | (rw [Channel.eval_pulledIf]
         simp only [SyscallInstrsChip.memPulledMessage, SyscallInstrsChip.memPullMsg,
           circuit_norm, syscallInstrsRow_eq])
      | (rw [Channel.eval_pushedIf]
         simp only [SyscallInstrsChip.memPushedMessage, SyscallInstrsChip.memPushMsg,
           SyscallInstrsChip.clkLowVar, circuit_norm, syscallInstrsRow_eq])

/-- The legacy assembly specializes the component-local Memory projection. -/
theorem syscallInstrsRow_typedMemory (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (row : Array (ZMod p)) :
    typedInteractionValuesWith (syscallInstrsTable witness).component.operations memoryChannel
        (Environment.fromArray row witness.data) =
      [TypedInteraction.pulledIfValue memoryChannel
       (syscallInstrsRow witness.data row).is_real
       (SyscallInstrsChip.memPulledMessage (syscallInstrsRow witness.data row)
         (syscallInstrsRow witness.data row).op_a_memory
         (syscallInstrsRow witness.data row).op_a),
     TypedInteraction.pushedIfValue memoryChannel
       (syscallInstrsRow witness.data row).is_real
       (SyscallInstrsChip.memPushedMessage (syscallInstrsRow witness.data row)
         (syscallInstrsRow witness.data row).op_a 4
         (syscallInstrsRow witness.data row).op_a_value),
     TypedInteraction.pulledIfValue memoryChannel
       (syscallInstrsRow witness.data row).is_real
       (SyscallInstrsChip.memPulledMessage (syscallInstrsRow witness.data row)
         (syscallInstrsRow witness.data row).op_b_memory
         (syscallInstrsRow witness.data row).op_b),
     TypedInteraction.pushedIfValue memoryChannel
       (syscallInstrsRow witness.data row).is_real
       (SyscallInstrsChip.memPushedMessage (syscallInstrsRow witness.data row)
         (syscallInstrsRow witness.data row).op_b 3
         (syscallInstrsRow witness.data row).op_b_memory.prev_value),
     TypedInteraction.pulledIfValue memoryChannel
       (syscallInstrsRow witness.data row).is_real
       (SyscallInstrsChip.memPulledMessage (syscallInstrsRow witness.data row)
         (syscallInstrsRow witness.data row).op_c_memory
         (syscallInstrsRow witness.data row).op_c),
     TypedInteraction.pushedIfValue memoryChannel
       (syscallInstrsRow witness.data row).is_real
       (SyscallInstrsChip.memPushedMessage (syscallInstrsRow witness.data row)
         (syscallInstrsRow witness.data row).op_c 2
         (syscallInstrsRow witness.data row).op_c_memory.prev_value)] :=
  syscallInstrsRow_typedMemory_of_component (syscallInstrsTable witness) witness.data (syscallInstrsTable_component witness) row

/-- The `SyscallInstrs` table's typed Memory view: three decoded register read-prior/read-back
pairs (`op_a` at `+4`, `op_b` at `+3`, `op_c` at `+2`). The `op_a` push carries `op_a_value` rather
than the prior word — that is the `t0` write SP1 performs and the halt table models as a read. -/
theorem syscallInstrsTable_typedMemory (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (syscallInstrsTable witness) witness.data memoryChannel =
      (syscallInstrsTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue memoryChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.memPulledMessage (syscallInstrsRow witness.data row)
             (syscallInstrsRow witness.data row).op_a_memory
             (syscallInstrsRow witness.data row).op_a),
         TypedInteraction.pushedIfValue memoryChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.memPushedMessage (syscallInstrsRow witness.data row)
             (syscallInstrsRow witness.data row).op_a 4
             (syscallInstrsRow witness.data row).op_a_value),
         TypedInteraction.pulledIfValue memoryChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.memPulledMessage (syscallInstrsRow witness.data row)
             (syscallInstrsRow witness.data row).op_b_memory
             (syscallInstrsRow witness.data row).op_b),
         TypedInteraction.pushedIfValue memoryChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.memPushedMessage (syscallInstrsRow witness.data row)
             (syscallInstrsRow witness.data row).op_b 3
             (syscallInstrsRow witness.data row).op_b_memory.prev_value),
         TypedInteraction.pulledIfValue memoryChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.memPulledMessage (syscallInstrsRow witness.data row)
             (syscallInstrsRow witness.data row).op_c_memory
             (syscallInstrsRow witness.data row).op_c),
         TypedInteraction.pushedIfValue memoryChannel
           (syscallInstrsRow witness.data row).is_real
           (SyscallInstrsChip.memPushedMessage (syscallInstrsRow witness.data row)
             (syscallInstrsRow witness.data row).op_c 2
             (syscallInstrsRow witness.data row).op_c_memory.prev_value)] := by
  unfold typedTableInteractionsWith
  exact List.flatMap_congr fun row _ => syscallInstrsRow_typedMemory witness row

/-- The `SyscallInstrs` table's typed Exit view: per physical row, a single `is_halt`-gated push.
There is no anti-gated companion — a many-row table cannot balance the verifier that way, which is
exactly why the exit accounting is redesigned when the halt table retires. -/
theorem syscallInstrsTable_typedExit_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := SyscallInstrsChip.circuit }) :
    typedTableInteractionsWith table data exitChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (syscallInstrsRow data row).is_halt
           (SyscallInstrsChip.exitMessage
             (syscallInstrsRow data row))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((SyscallInstrsChip.main
        (varFromOffset SyscallInstrsChip.Inputs 0 : Var SyscallInstrsChip.Inputs (ZMod p))
          ).operations (size SyscallInstrsChip.Inputs)).interactionsWith exitChannel.toRaw) = _
  rw [syscallInstrsExitInteractions_gated]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
  rw [Channel.eval_pushedIf]
  simp only [SyscallInstrsChip.exitMessage, SyscallInstrsChip.exitMsg,
    SyscallInstrsChip.reduceWord, circuit_norm, syscallInstrsRow_eq]

/-- The original ensemble specializes the component-level Exit ledger. -/
theorem syscallInstrsTable_typedExit (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (syscallInstrsTable witness) witness.data exitChannel =
      (syscallInstrsTable witness).table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (syscallInstrsRow witness.data row).is_halt
           (SyscallInstrsChip.exitMessage
             (syscallInstrsRow witness.data row))] :=
  syscallInstrsTable_typedExit_of_component (syscallInstrsTable witness) witness.data (syscallInstrsTable_component witness)

/-- The Halt table's typed Exit view: per physical row, the gated reduced-word push and the
anti-gated zero push — the hand-off pair the verifier's ungated `⟨exit_code⟩` pull balances. -/
theorem haltTable_typedExit_of_component (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = { circuit := HaltChip.circuit }) :
    typedTableInteractionsWith table data exitChannel =
      table.table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (haltRow data row).is_real
           (HaltChip.exitMessage (haltRow data row)),
         TypedInteraction.pushedIfValue exitChannel
           (1 - (haltRow data row).is_real)
           (⟨0⟩ : ExitMsg (ZMod p))] := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromArray row data))
      (((HaltChip.main
        (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p))).operations
          (size HaltChip.Inputs)).interactionsWith exitChannel.toRaw) = _
  rw [HaltChip.interactionsWith_exit_eq]
  simp only [List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_raw]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  · rw [Channel.eval_pushedIf]
    simp only [HaltChip.exitMessage, HaltChip.exitMsg, circuit_norm, haltRow_eq]
  · rw [Channel.eval_pushedIf]
    simp only [HaltChip.exitPaddingMsg, circuit_norm, haltRow_eq]

/-- The original ensemble specializes the component-level Exit ledger. -/
theorem haltTable_typedExit (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (haltTable witness) witness.data exitChannel =
      (haltTable witness).table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (haltRow witness.data row).is_real
           (HaltChip.exitMessage (haltRow witness.data row)),
         TypedInteraction.pushedIfValue exitChannel
           (1 - (haltRow witness.data row).is_real)
           (⟨0⟩ : ExitMsg (ZMod p))] :=
  haltTable_typedExit_of_component (haltTable witness) witness.data (haltTable_component witness)

/-- The Halt table's per-row full guarantee bundle: byte and program grounded by the
finished-channel engine, State and Exit structurally `True`, and the memory read-prior pulls
supplied as the explicit premise (a memory-side balance fact). -/
private theorem haltTable_fullGuarantees
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (byteGuarantees : (haltTable witness).ChannelGuarantees witness.data byteChannel.toRaw)
    (programGuarantees : (haltTable witness).ChannelGuarantees witness.data programChannel.toRaw)
    (memoryGuarantees : (haltTable witness).ChannelGuarantees witness.data memoryChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ (haltTable witness).table) :
    (haltTable witness).component.operations.FullGuarantees
      (Environment.fromArray row witness.data) := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hlist : (haltTable witness).component.circuit.channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
       exitChannel.toRaw] := by
    rw [haltTable_component]
    rfl
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channelMem
  show (haltTable witness).component.rowOperations.ChannelGuarantees channel
    (Environment.fromArray row witness.data)
  rw [← Component.channelGuarantees_iff]
  rw [hlist] at channelMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact byteGuarantees row rowMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · intro i hi hmult
    exact stateChannel_interaction_guarantees _ hmult
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact programGuarantees row rowMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact memoryGuarantees row rowMem
  · rw [List.mem_singleton.mp channelMem]
    intro i hi hmult
    exact exitChannel_interaction_guarantees _ hmult

/-- The per-row `Spec` extraction through `Component.weakSoundness`, from the table-level facts
(the `memoryBumpRow_spec_of_facts` split, for the same elaboration-budget reason). -/
private theorem haltRow_spec_of_facts
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (tableConstraints : (haltTable witness).Constraints witness.data)
    (byteGuarantees : (haltTable witness).ChannelGuarantees witness.data byteChannel.toRaw)
    (programGuarantees : (haltTable witness).ChannelGuarantees witness.data programChannel.toRaw)
    (memoryGuarantees : (haltTable witness).ChannelGuarantees witness.data memoryChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ (haltTable witness).table) :
    HaltChip.Spec (haltRow witness.data row) := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hassump : (haltTable witness).component.CircuitAssumptions
      (Environment.fromArray row witness.data) := by
    rw [haltTable_component]
    rw [show ∀ env, ({ circuit := HaltChip.circuit } : Component (ZMod p)).CircuitAssumptions env = True from
      fun _ => HaltChip.circuit_Assumptions_apply _ _]
    trivial
  have spec := ((haltTable witness).component.weakSoundness
    (env := Environment.fromArray row witness.data)
    hassump (tableConstraints row rowMem)
    (haltTable_fullGuarantees witness byteGuarantees programGuarantees memoryGuarantees rowMem)).1
  rw [haltTable_component,
    show ∀ env, ({ circuit := HaltChip.circuit } : Component (ZMod p)).Spec env =
        HaltChip.Spec (valueFromOffset HaltChip.Inputs 0 env) from
      fun _ => HaltChip.circuit_Spec_apply _ _ _] at spec
  exact spec

/-- Every Halt row satisfies the chip's semantic `Spec`: `Component.weakSoundness` with the
trivial `Assumptions`, the row's constraints, byte/program guarantees from the finished-channel
engine, structural State/Exit guarantees, and the supplied memory pull guarantee. -/
theorem haltTable_spec (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (memoryGuarantees : (haltTable witness).ChannelGuarantees witness.data memoryChannel.toRaw) :
    ∀ row ∈ (haltTable witness).table,
      HaltChip.Spec (haltRow witness.data row) := by
  have tableMem : haltTable witness ∈ witness.tables :=
    List.getElem_mem (haltIndex_lt_tablesLength witness)
  have tableConstraints : (haltTable witness).Constraints witness.data :=
    constraints _ tableMem
  have grounded := (sp1_finishedChannel_guarantees witness constraints balanced).2
    _ tableMem
  intro row rowMem
  exact haltRow_spec_of_facts witness tableConstraints grounded.1 grounded.2
    memoryGuarantees rowMem

/-! ## Active Halt rows -/

/-- The active rows of the Halt table: at most one (the exit hand-off balance forces it), the
halting shard's real ECALL witness row. -/
noncomputable def realHaltRows
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : List (Array (ZMod p)) :=
  (haltTable witness).table.filter fun row =>
    (haltRow witness.data row).is_real = 1

/-- Membership in the active Halt rows unpacks to physical-table membership plus the live
selector. -/
theorem mem_realHaltRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    {row : Array (ZMod p)} (rowMem : row ∈ realHaltRows witness) :
    row ∈ (haltTable witness).table ∧
      (haltRow witness.data row).is_real = 1 := by
  rw [realHaltRows, List.mem_filter] at rowMem
  simpa only [decide_eq_true_eq] using rowMem

/-- The `SyscallInstrs` table's per-row full guarantee bundle. Seven channels rather than the halt
table's five: the two extra buses are the ones only this chip speaks on, and both carry `True`, so
D2's carve-outs stay *derived from balance* rather than promised here. -/
private theorem syscallInstrsTable_fullGuarantees
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (byteGuarantees : table.ChannelGuarantees data byteChannel.toRaw)
    (programGuarantees : table.ChannelGuarantees data programChannel.toRaw)
    {row : Array (ZMod p)}
    (memoryGuarantees : table.component.operations.ChannelGuarantees
      memoryChannel.toRaw (Environment.fromArray row data))
    (rowMem : row ∈ table.table) :
    table.component.operations.FullGuarantees
      (Environment.fromArray row data) := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hlist : table.component.circuit.channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
       exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw] := by
    rw [component]
    rfl
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channelMem
  show table.component.rowOperations.ChannelGuarantees channel
    (Environment.fromArray row data)
  rw [← Component.channelGuarantees_iff]
  rw [hlist] at channelMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact byteGuarantees row rowMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · intro i hi hmult
    exact stateChannel_interaction_guarantees _ hmult
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact programGuarantees row rowMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact memoryGuarantees
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · intro i hi hmult
    exact exitChannel_interaction_guarantees _ hmult
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · intro i hi hmult
    exact syscallChannel_interaction_guarantees _ hmult
  · rw [List.mem_singleton.mp channelMem]
    intro i hi hmult
    exact publicValuesChannel_interaction_guarantees _ hmult

/-- The per-row `Spec` extraction through `Component.weakSoundness`. The Memory guarantee is taken
**at this row's environment** rather than table-wide, because that is the form the walk can supply:
its currency antecedent hands one row's pulls their `isU64 ∧ ClkBound` at a time. -/
theorem syscallInstrsRow_spec_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit })
    (tableConstraints : table.Constraints data)
    (byteGuarantees : table.ChannelGuarantees data byteChannel.toRaw)
    (programGuarantees : table.ChannelGuarantees data programChannel.toRaw)
    {row : Array (ZMod p)}
    (memoryGuarantees : table.component.operations.ChannelGuarantees
      memoryChannel.toRaw (Environment.fromArray row data))
    (rowMem : row ∈ table.table) :
    SyscallInstrsChip.Spec (syscallInstrsRow data row) := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hassump : table.component.CircuitAssumptions
      (Environment.fromArray row data) := by
    rw [component]
    rw [show ∀ env, ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)).CircuitAssumptions env = True from
      fun _ => SyscallInstrsChip.circuit_Assumptions_apply _ _]
    trivial
  have spec := (table.component.weakSoundness
    (env := Environment.fromArray row data)
    hassump (tableConstraints row rowMem)
    (syscallInstrsTable_fullGuarantees table data component byteGuarantees programGuarantees
      memoryGuarantees rowMem)).1
  rw [component,
    show ∀ env, ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)).Spec env =
        SyscallInstrsChip.Spec (valueFromOffset SyscallInstrsChip.Inputs 0 env) from
      fun _ => SyscallInstrsChip.circuit_Spec_apply _ _ _] at spec
  exact spec

/-- The legacy assembly specializes component-local syscall soundness. -/
theorem syscallInstrsRow_spec_of_facts
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (tableConstraints : (syscallInstrsTable witness).Constraints witness.data)
    (byteGuarantees : (syscallInstrsTable witness).ChannelGuarantees witness.data byteChannel.toRaw)
    (programGuarantees : (syscallInstrsTable witness).ChannelGuarantees witness.data programChannel.toRaw)
    {row : Array (ZMod p)}
    (memoryGuarantees : (syscallInstrsTable witness).component.operations.ChannelGuarantees
      memoryChannel.toRaw (Environment.fromArray row witness.data))
    (rowMem : row ∈ (syscallInstrsTable witness).table) :
    SyscallInstrsChip.Spec (syscallInstrsRow witness.data row) :=
  syscallInstrsRow_spec_of_component _ witness.data (syscallInstrsTable_component witness)
    tableConstraints byteGuarantees programGuarantees memoryGuarantees rowMem

/-- **Every `SyscallInstrs` row satisfies the chip's semantic `Spec`.** This is the extractor the
stash was missing: it registered the table and decoded its rows, but nothing carried the row's
meaning out of the ensemble, so every downstream fact about a syscall edge was unreachable. -/
theorem syscallInstrsTable_spec (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (memoryGuarantees : (syscallInstrsTable witness).ChannelGuarantees witness.data memoryChannel.toRaw) :
    ∀ row ∈ (syscallInstrsTable witness).table,
      SyscallInstrsChip.Spec (syscallInstrsRow witness.data row) := by
  have tableMem : syscallInstrsTable witness ∈ witness.tables :=
    List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness)
  have tableConstraints : (syscallInstrsTable witness).Constraints witness.data :=
    constraints _ tableMem
  have grounded := (sp1_finishedChannel_guarantees witness constraints balanced).2
    _ tableMem
  intro row rowMem
  exact syscallInstrsRow_spec_of_facts witness tableConstraints grounded.1 grounded.2
    (memoryGuarantees row rowMem) rowMem

/-- The active rows of the `SyscallInstrs` table. -/
noncomputable def realSyscallInstrsRows
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : List (Array (ZMod p)) :=
  (syscallInstrsTable witness).table.filter fun row =>
    (syscallInstrsRow witness.data row).is_real = 1

/-- Membership in the active syscall rows unpacks to physical-table membership plus the live
selector. -/
theorem mem_realSyscallInstrsRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness) :
    row ∈ (syscallInstrsTable witness).table ∧
      (syscallInstrsRow witness.data row).is_real = 1 := by
  rw [realSyscallInstrsRows, List.mem_filter] at rowMem
  simpa only [decide_eq_true_eq] using rowMem

end SP1Clean.Soundness
