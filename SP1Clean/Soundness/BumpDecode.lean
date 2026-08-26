import SP1Clean.Soundness.TypedInteractions
import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.StateCanon

/-! # Typed decoders for the two bump system tables (W3 D6, external report Finding 2)

The BumpDecode layer: the StateBump table (stable position 52) and MemoryBump table (position 51)
decoded row-by-row into their chip `Inputs`, with each table's channel contribution enumerated as
the per-row semantic pull/push pairs — the exact analogue, for the two provider-segment system
tables, of `DecodedInstructionRow.stateInteractions_eq` for the 25 instruction chips.

The tables carry no `ChipKind.advance` (they are canonicalization rows, not instructions); their
whole trace-level meaning is the message pairs enumerated here, consumed by the canonicalized
State balance (StateBump) and the refresh-eliminated Memory balance (MemoryBump). The rows' full
semantic `Spec`s are extracted by `Table.weakSoundness`: the bump circuits' `Assumptions` are
`True` and their byte-pull guarantees are grounded by `sp1_finishedChannel_guarantees` — the W3
partition re-cut that placed the bump tables on the byte bus's consumer side. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.Channels (stateChannel memoryChannel byteChannel StateMsg MemoryMsg)
open Air.Flat
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The MemoryBump table's stable position in the 53-table layout. -/
def memoryBumpIndex : ℕ := instructionTableCount + nonBumpProviderTableCount

/-- The StateBump table's stable position in the 53-table layout. -/
def stateBumpIndex : ℕ := instructionTableCount + stateSilentProviderTableCount

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

/-- The physical MemoryBump table selected by the stable ensemble layout. -/
noncomputable def memoryBumpTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[memoryBumpIndex]'(memoryBumpIndex_lt_tablesLength witness)

/-- The physical StateBump table selected by the stable ensemble layout. -/
noncomputable def stateBumpTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[stateBumpIndex]'(stateBumpIndex_lt_tablesLength witness)

/-- The stable MemoryBump position carries the MemoryBump circuit. -/
theorem memoryBumpTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (memoryBumpTable witness).component = ⟨MemoryBumpChip.circuit⟩ := by
  unfold memoryBumpTable
  have aligned := witness.same_circuits memoryBumpIndex (by
    simp [memoryBumpIndex, instructionTableCount, nonBumpProviderTableCount,
      sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The stable StateBump position carries the StateBump circuit. -/
theorem stateBumpTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (stateBumpTable witness).component = ⟨StateBumpChip.circuit⟩ := by
  unfold stateBumpTable
  have aligned := witness.same_circuits stateBumpIndex (by
    simp [stateBumpIndex, instructionTableCount, stateSilentProviderTableCount,
      sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The bump tables use the ensemble's shared prover data. -/
theorem memoryBumpTable_data (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (memoryBumpTable witness).data = witness.data :=
  witness.same_data _ (List.getElem_mem (memoryBumpIndex_lt_tablesLength witness))

theorem stateBumpTable_data (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (stateBumpTable witness).data = witness.data :=
  witness.same_data _ (List.getElem_mem (stateBumpIndex_lt_tablesLength witness))

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

/-- The provider tail beyond the state-silent prefix is exactly the StateBump singleton. -/
theorem tables_drop_stateBumpIndex (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.tables.drop stateBumpIndex = [stateBumpTable witness] := by
  have hlen : witness.tables.length = 53 := by
    rw [← witness.same_length]
    simp [sp1Ensemble_tables, sp1Tables_length,
      sp1ProviderTables_length]
  simp only [stateBumpIndex, instructionTableCount, InstructionChipId.count_eq,
    stateSilentProviderTableCount]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  rfl

/-- The provider tail splits into its 27 state-silent tables and the StateBump singleton. -/
theorem tables_drop25_split (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.tables.drop instructionTableCount =
      (witness.tables.drop instructionTableCount).take stateSilentProviderTableCount ++
        witness.tables.drop stateBumpIndex := by
  rw [show witness.tables.drop stateBumpIndex =
      (witness.tables.drop instructionTableCount).drop stateSilentProviderTableCount from by
      rw [List.drop_drop]
      rfl, List.take_append_drop]

/-! ## Row decoders

Both decoders are spelled `valueFromOffset` — the exact form `Component.Spec ⟨circuit⟩` exposes
through `Component.rowInput` — so the two `*_spec` theorems below reach the chip `Spec` by cheap
structural delta/beta.  The `Eval.eval ∘ varFromOffset` spelling would force the unifier through
the `ProvableStruct` evaluator at the theorem head; `stateBumpRow_eq`/`memoryBumpRow_eq` recover
the evaluated form where the interaction-evaluation lemmas need it. -/

/-- A StateBump table row decoded into the chip's semantic `Inputs`. -/
noncomputable def stateBumpRow (t : Table (ZMod p)) (row : Array (ZMod p)) :
    StateBumpChip.Inputs (ZMod p) :=
  valueFromOffset StateBumpChip.Inputs 0 (t.environment row)

/-- A MemoryBump table row decoded into the chip's semantic `Inputs`. -/
noncomputable def memoryBumpRow (t : Table (ZMod p)) (row : Array (ZMod p)) :
    MemoryBumpChip.Inputs (ZMod p) :=
  valueFromOffset MemoryBumpChip.Inputs 0 (t.environment row)

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The decoded StateBump row, in the evaluated-`varFromOffset` form the per-row interaction
evaluations produce. -/
theorem stateBumpRow_eq [Fact p.Prime] (t : Table (ZMod p)) (row : Array (ZMod p)) :
    stateBumpRow t row =
      Eval.eval (t.environment row)
        (varFromOffset StateBumpChip.Inputs 0 : Var StateBumpChip.Inputs (ZMod p)) :=
  (eval_varFromOffset_valueFromOffset _ _ _).symm

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The decoded MemoryBump row, in the evaluated-`varFromOffset` form the per-row interaction
evaluations produce. -/
theorem memoryBumpRow_eq [Fact p.Prime] (t : Table (ZMod p)) (row : Array (ZMod p)) :
    memoryBumpRow t row =
      Eval.eval (t.environment row)
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
    (env : Environment F) (ts : Extracted.MemoryAccessTimestamp (Expression F)) :
    Eval.eval env ts =
      ({ prev_high := Eval.eval env ts.prev_high,
         prev_low := Eval.eval env ts.prev_low,
         compare_low := Eval.eval env ts.compare_low,
         diff_low_limb := Eval.eval env ts.diff_low_limb,
         diff_high_limb := Eval.eval env ts.diff_high_limb } :
        Extracted.MemoryAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the `MemoryAccessCols` carrier. -/
theorem eval_bumpAccessCols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value,
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
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
theorem memoryBumpRow_closedForm (t : Table (ZMod p)) (row : Array (ZMod p)) :
    memoryBumpRow t row =
      ({ access :=
          { prev_value := Eval.eval (t.environment row)
              (varFromOffset MemoryBumpChip.Inputs 0 :
                Var MemoryBumpChip.Inputs (ZMod p)).access.prev_value,
            access_timestamp :=
            { prev_high := Expression.eval (t.environment row)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.prev_high,
              prev_low := Expression.eval (t.environment row)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.prev_low,
              compare_low := Expression.eval (t.environment row)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.compare_low,
              diff_low_limb := Expression.eval (t.environment row)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.diff_low_limb,
              diff_high_limb := Expression.eval (t.environment row)
                (varFromOffset MemoryBumpChip.Inputs 0).access.access_timestamp.diff_high_limb } },
         clk_32_48 := Expression.eval (t.environment row)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_32_48,
         clk_24_32 := Expression.eval (t.environment row)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_24_32,
         clk_16_24 := Expression.eval (t.environment row)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_16_24,
         clk_0_16 := Expression.eval (t.environment row)
           (varFromOffset MemoryBumpChip.Inputs 0).clk_0_16,
         addr := Expression.eval (t.environment row)
           (varFromOffset MemoryBumpChip.Inputs 0).addr,
         is_real := Expression.eval (t.environment row)
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
theorem stateBumpTable_typedState (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (stateBumpTable witness) stateChannel =
      (stateBumpTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue stateChannel
           (stateBumpRow (stateBumpTable witness) row).is_real
           (StateBumpChip.pulledMessage (stateBumpRow (stateBumpTable witness) row)),
         TypedInteraction.pushedIfValue stateChannel
           (stateBumpRow (stateBumpTable witness) row).is_real
           (StateBumpChip.pushedMessage (stateBumpRow (stateBumpTable witness) row))] := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    stateBumpTable_component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval ((stateBumpTable witness).environment row))
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
        ((stateBumpTable witness).environment row) =
      stateChannel.pulledIfValue (stateBumpRow (stateBumpTable witness) row).is_real
        (StateBumpChip.pulledMessage (stateBumpRow (stateBumpTable witness) row)) from by
    rw [Channel.eval_pulledIf, eval_stateBump_pulledMsg]
    simp only [circuit_norm, stateBumpRow_eq]]
  rw [show ((stateChannel (p := p)).pushedIf
        (varFromOffset StateBumpChip.Inputs 0 :
          Var StateBumpChip.Inputs (ZMod p)).is_real
        (StateBumpChip.pushedMsg (varFromOffset StateBumpChip.Inputs 0))).toRaw.eval
        ((stateBumpTable witness).environment row) =
      stateChannel.pushedIfValue (stateBumpRow (stateBumpTable witness) row).is_real
        (StateBumpChip.pushedMessage (stateBumpRow (stateBumpTable witness) row)) from by
    rw [Channel.eval_pushedIf, eval_stateBump_pushedMsg]
    simp only [circuit_norm, stateBumpRow_eq]]

/-- The MemoryBump table's typed Memory view: per physical row, the decoded old-record pull and
refreshed push. -/
theorem memoryBumpTable_typedMemory (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith (memoryBumpTable witness) memoryChannel =
      (memoryBumpTable witness).table.flatMap fun row =>
        [TypedInteraction.pulledIfValue memoryChannel
           (memoryBumpRow (memoryBumpTable witness) row).is_real
           (MemoryBumpChip.pulledMessage (memoryBumpRow (memoryBumpTable witness) row)),
         TypedInteraction.pushedIfValue memoryChannel
           (memoryBumpRow (memoryBumpTable witness) row).is_real
           (MemoryBumpChip.pushedMessage (memoryBumpRow (memoryBumpTable witness) row))] := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  unfold typedTableInteractionsWith
  apply List.flatMap_congr
  intro row rowMem
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map,
    memoryBumpTable_component, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval ((memoryBumpTable witness).environment row))
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
        ((memoryBumpTable witness).environment row) =
      memoryChannel.pulledIfValue (memoryBumpRow (memoryBumpTable witness) row).is_real
        (MemoryBumpChip.pulledMessage (memoryBumpRow (memoryBumpTable witness) row)) from by
    rw [Channel.eval_pulledIf, eval_memoryBump_pulledMsg]
    simp only [circuit_norm, memoryBumpRow_eq]]
  rw [show ((memoryChannel (p := p)).pushedIf
        (varFromOffset MemoryBumpChip.Inputs 0 :
          Var MemoryBumpChip.Inputs (ZMod p)).is_real
        (MemoryBumpChip.pushedMsg (varFromOffset MemoryBumpChip.Inputs 0))).toRaw.eval
        ((memoryBumpTable witness).environment row) =
      memoryChannel.pushedIfValue (memoryBumpRow (memoryBumpTable witness) row).is_real
        (MemoryBumpChip.pushedMessage (memoryBumpRow (memoryBumpTable witness) row)) from by
    rw [Channel.eval_pushedIf, eval_memoryBump_pushedMsg]
    simp only [circuit_norm, memoryBumpRow_eq]]

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

/-- Every StateBump row satisfies the chip's semantic `Spec`: `Component.weakSoundness` with the
trivial `Assumptions`, the row's constraints, and the byte/state guarantees — byte grounded by the
finished-channel engine (the bump tables sit on its consumer side), State's guarantee `True`. -/
theorem stateBumpTable_spec (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ (stateBumpTable witness).table,
      StateBumpChip.Spec (stateBumpRow (stateBumpTable witness) row) := by
  haveI : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have tableMem : stateBumpTable witness ∈ witness.tables :=
    List.getElem_mem (stateBumpIndex_lt_tablesLength witness)
  have tableConstraints : (stateBumpTable witness).Constraints :=
    constraints _ (witness.mem_allTables_of_mem_tables tableMem)
  have byteGuarantees := (sp1_finishedChannel_guarantees witness constraints balanced
    _ (witness.mem_allTables_of_mem_tables tableMem)).1
  intro row rowMem
  have hlist : (stateBumpTable witness).component.circuit.channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw] := by
    rw [stateBumpTable_component]
    rfl
  have guarantees : (stateBumpTable witness).component.operations.FullGuarantees
      ((stateBumpTable witness).environment row) := by
    simp only [Component.guarantees_iff, Component.rowOperations]
    rw [GeneralFormalCircuit.guarantees_iff]
    intro channel channelMem
    show (stateBumpTable witness).component.rowOperations.ChannelGuarantees channel
      ((stateBumpTable witness).environment row)
    rw [← Component.channelGuarantees_iff]
    rw [hlist] at channelMem
    rcases List.mem_cons.mp channelMem with rfl | channelMem
    · exact byteGuarantees row rowMem
    · rw [List.mem_singleton.mp channelMem]
      intro i hi hmult
      exact stateChannel_interaction_guarantees _ hmult
  have spec := ((stateBumpTable witness).component.weakSoundness
    (env := (stateBumpTable witness).environment row)
    (by rw [stateBumpTable_component]; trivial) (tableConstraints row rowMem) guarantees).1
  rw [stateBumpTable_component] at spec
  exact spec

/-- The MemoryBump table's per-row full guarantee bundle, assembled from the grounded byte pulls
and the supplied Memory pull guarantee.  Split out of `memoryBumpTable_spec` so the guarantee
assembly over the nested-carrier operations and the `weakSoundness` extraction below each keep
their own elaboration budget. -/
private theorem memoryBumpTable_fullGuarantees
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (byteGuarantees : (memoryBumpTable witness).ChannelGuarantees byteChannel.toRaw)
    (memoryGuarantees : (memoryBumpTable witness).ChannelGuarantees memoryChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ (memoryBumpTable witness).table) :
    (memoryBumpTable witness).component.operations.FullGuarantees
      ((memoryBumpTable witness).environment row) := by
  have hlist : (memoryBumpTable witness).component.circuit.channelsWithGuarantees =
      [byteChannel.toRaw, memoryChannel.toRaw] := by
    rw [memoryBumpTable_component]
    rfl
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channelMem
  show (memoryBumpTable witness).component.rowOperations.ChannelGuarantees channel
    ((memoryBumpTable witness).environment row)
  rw [← Component.channelGuarantees_iff]
  rw [hlist] at channelMem
  rcases List.mem_cons.mp channelMem with rfl | channelMem
  · exact byteGuarantees row rowMem
  · rw [List.mem_singleton.mp channelMem]
    exact memoryGuarantees row rowMem

/-- The per-row `Spec` extraction through `Component.weakSoundness`, from the table-level facts. -/
private theorem memoryBumpRow_spec_of_facts
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (tableConstraints : (memoryBumpTable witness).Constraints)
    (byteGuarantees : (memoryBumpTable witness).ChannelGuarantees byteChannel.toRaw)
    (memoryGuarantees : (memoryBumpTable witness).ChannelGuarantees memoryChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ (memoryBumpTable witness).table) :
    MemoryBumpChip.Spec (memoryBumpRow (memoryBumpTable witness) row) := by
  have spec := ((memoryBumpTable witness).component.weakSoundness
    (env := (memoryBumpTable witness).environment row)
    (by rw [memoryBumpTable_component]; trivial) (tableConstraints row rowMem)
    (memoryBumpTable_fullGuarantees witness byteGuarantees memoryGuarantees rowMem)).1
  rw [memoryBumpTable_component] at spec
  -- Cross from `Component.Spec` to the chip `Spec` in two head-congruent steps (`rowInput` is
  -- definitionally `memoryBumpRow`'s `valueFromOffset` body), so the unifier never descends into
  -- the nested-carrier `Spec` conjuncts.
  show MemoryBumpChip.Spec (Component.rowInput ⟨MemoryBumpChip.circuit⟩
    ((memoryBumpTable witness).environment row))
  exact spec

/-- Every MemoryBump row satisfies the chip's semantic `Spec`. Beside the byte pulls this needs
the row's memory pull guarantee (`isU64 ∧ ClkBound` of the old record), supplied as the explicit
`memoryGuarantees` premise: on the Memory channel the bump table is a genuine consumer, and its
pull grounding is a memory-side balance fact, not a finished-channel one. -/
theorem memoryBumpTable_spec (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (memoryGuarantees : (memoryBumpTable witness).ChannelGuarantees memoryChannel.toRaw) :
    ∀ row ∈ (memoryBumpTable witness).table,
      MemoryBumpChip.Spec (memoryBumpRow (memoryBumpTable witness) row) := by
  have tableMem : memoryBumpTable witness ∈ witness.tables :=
    List.getElem_mem (memoryBumpIndex_lt_tablesLength witness)
  have tableConstraints : (memoryBumpTable witness).Constraints :=
    constraints _ (witness.mem_allTables_of_mem_tables tableMem)
  have byteGuarantees := (sp1_finishedChannel_guarantees witness constraints balanced
    _ (witness.mem_allTables_of_mem_tables tableMem)).1
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
    (memoryBumpRow (memoryBumpTable witness) row).is_real = 1

/-- Membership in the active MemoryBump rows unpacks to physical-table membership plus the live
selector. -/
theorem mem_realMemoryBumpRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    {row : Array (ZMod p)} (rowMem : row ∈ realMemoryBumpRows witness) :
    row ∈ (memoryBumpTable witness).table ∧
      (memoryBumpRow (memoryBumpTable witness) row).is_real = 1 := by
  rw [realMemoryBumpRows, List.mem_filter] at rowMem
  simpa only [decide_eq_true_eq] using rowMem

/-! ## Active StateBump rows -/

/-- The active rows of the StateBump table.  Padding rows stay in the physical table but denote no
canonicalization edge; the with-bump State balance sums exactly this filtered list. -/
noncomputable def realStateBumpRows
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : List (Array (ZMod p)) :=
  (stateBumpTable witness).table.filter fun row =>
    (stateBumpRow (stateBumpTable witness) row).is_real = 1

/-- Witness constraints and balance discharge selector booleanity for every StateBump row: it is
the first (ungated) conjunct of the row `Spec`. -/
theorem witness_stateBumpRows_selectorBinary
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ (stateBumpTable witness).table,
      (stateBumpRow (stateBumpTable witness) row).is_real = 0 ∨
        (stateBumpRow (stateBumpTable witness) row).is_real = 1 :=
  fun row rowMem => (stateBumpTable_spec witness constraints balanced row rowMem).1

end SP1Clean.Soundness
