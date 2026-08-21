import SP1Clean.Extracted.SystemOracle.MemoryBump
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Proofs.Chips.MemoryBumpChip.Formal

/-! # Chip-level faithfulness anchor — SP1's whole `MemoryBump` system table

The whole-table Rust oracle boundary for the second of the two W3 system tables (external report
Finding 5): the native `MemoryBumpChip` circuit's complete `assertZero` list and complete
interaction multiset are compared against `Extracted/SystemOracle/MemoryBump.lean`, the extracted
`sp1-constraint-compiler` dump of upstream's `MemoryBumpChip::eval`
(`../sp1 crates/core/machine/src/memory/bump.rs`).

## Shape of the anchor

Like `StateBump`, `MemoryBump` is a **flat own-assert table** — no composed subcircuits, no readers,
no operations, `localLength = 0` — so all fifteen cells are inputs and the native physical row *is*
the extracted flat `values` vector. As in `Faithful/StateBumpChip.lean`, the native row type is the
chip's `Inputs` (the row codec is the input-first physical row) and the chip's Clean output is
`unit`, so the anchor is stated as the two `ChipFaithful` clauses over that input-keyed codec rather
than through the `ChipFaithful` structure, whose `ChipRowCodec` is keyed on the circuit's *output*
type map. Both clauses are stated against the real `⟨MemoryBumpChip.circuit⟩` flat component the
ensemble registers; `memoryBumpChip_faithful` bundles them.

The row reuses the shared `Extracted.MemoryAccessCols` carrier, so the first nine cells are the same
`prev_value ++ access_timestamp` block the load/store chips carry.

## The Memory polarity bridge

`MemoryBump` touches the Byte and Memory buses. Byte is aligned (the byte arm of
`Extracted.Interaction.toAccess` already negates, matching Clean's byte *pull* convention), but
**Memory is deliberately flipped**: SP1 `.send`s the read-prior record and `.receive`s the refreshed
one, while the native circuit `memoryChannel.pullIf`s the prior and `pushIf`es the refreshed one.
`nativeAccesses` (`Faithful/ChipOracle.lean`) applies `LookupAccessList.negMult` to the whole Memory
block for exactly this reason, and `signedVal_neg` (`signedVal (-x) = -signedVal x`, valid for every
field element at an odd prime) closes the resulting sign equation — the same LogUp sign symmetry the
load/store anchors use. After that bridge the two projections agree entry for entry, in emission
order.

The extracted dump lists the `is_real` boolean gate **twice** (SP1's `eval_memory_access_read`
fragment re-asserts it); the native circuit asserts it once. `ChipFaithful` compares assertion
systems extensionally, so the duplicate is absorbed by `and_self_left`.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Channels (memoryChannel byteChannel MemoryMsg)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The whole-row column codec -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Four-cell eta for the `Word` carrier, used by the codec round-trips. -/
private theorem memoryBumpWord_eta {F : Type} (w : Word F) : #v[w[0], w[1], w[2], w[3]] = w := by
  ext i hi
  interval_cases i <;> rfl

/-- Whole-row reconfiguration: the native `MemoryBumpChip.Inputs` row in upstream `MemoryBumpCols`
field order (`memory/bump.rs`) — the shared `MemoryAccessCols` carrier flattened as `prev_value`
(four cells) then `access_timestamp` (five cells), then the four refreshed-clock limbs, the register
index, and the row selector. The extraction layer keeps the row as a flat 15-cell vector, so this
map is the audit-visible column order. -/
def memoryBumpReconfigure {F : Type} (r : MemoryBumpChip.Inputs F) : Extracted.MemoryBumpCols F :=
  ⟨#v[r.access.prev_value[0], r.access.prev_value[1], r.access.prev_value[2],
      r.access.prev_value[3],
      r.access.access_timestamp.prev_high, r.access.access_timestamp.prev_low,
      r.access.access_timestamp.compare_low, r.access.access_timestamp.diff_low_limb,
      r.access.access_timestamp.diff_high_limb,
      r.clk_32_48, r.clk_24_32, r.clk_16_24, r.clk_0_16, r.addr, r.is_real]⟩

/-- Inverse whole-row map, used to reconstruct the native proof row from an arbitrary Rust row. -/
def memoryBumpDeconfigure {F : Type} (cols : Extracted.MemoryBumpCols F) :
    MemoryBumpChip.Inputs F :=
  { access :=
      { prev_value := #v[cols.values[0], cols.values[1], cols.values[2], cols.values[3]]
        access_timestamp :=
          { prev_high := cols.values[4]
            prev_low := cols.values[5]
            compare_low := cols.values[6]
            diff_low_limb := cols.values[7]
            diff_high_limb := cols.values[8] } }
    clk_32_48 := cols.values[9]
    clk_24_32 := cols.values[10]
    clk_16_24 := cols.values[11]
    clk_0_16 := cols.values[12]
    addr := cols.values[13]
    is_real := cols.values[14] }

theorem memoryBumpDeconfigure_reconfigure {F : Type} :
    Function.LeftInverse (memoryBumpDeconfigure (F := F)) memoryBumpReconfigure := by
  intro r
  obtain ⟨⟨prev_value, ts⟩, clk_32_48, clk_24_32, clk_16_24, clk_0_16, addr, is_real⟩ := r
  cases ts
  simp [memoryBumpReconfigure, memoryBumpDeconfigure, memoryBumpWord_eta]

theorem memoryBumpReconfigure_deconfigure {F : Type} :
    Function.LeftInverse (memoryBumpReconfigure (F := F)) memoryBumpDeconfigure := by
  intro cols
  obtain ⟨values⟩ := cols
  simp only [memoryBumpDeconfigure, memoryBumpReconfigure, Extracted.MemoryBumpCols.mk.injEq]
  ext i hi
  interval_cases i <;> rfl

/-- SP1 Rust's complete `MemoryBump` oracle, viewed from the native Lean row. The generated
`asserts`/`interactions` ignore both the (width-zero) preprocessed row and the public values, so the
anchor holds for every choice of them; they stay explicit parameters so the oracle is literally the
one `FormalModel`'s exact Core AIR relation evaluates (`Faithful/CoreAIR.lean`, `.memoryBump`
arm). -/
def memoryBumpChipOracle (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160) :
    ChipOracle (ZMod p) MemoryBumpChip.Inputs Extracted.MemoryBumpCols where
  reconfigure := memoryBumpReconfigure
  deconfigure := memoryBumpDeconfigure
  reconfigure_deconfigure := memoryBumpReconfigure_deconfigure
  deconfigure_reconfigure := memoryBumpDeconfigure_reconfigure
  assertZeros cols := Extracted.MemoryBumpCols.asserts cols preprocessed publicValues
  interactions cols := Extracted.MemoryBumpCols.interactions cols preprocessed publicValues

/-! ## The physical row -/

/-- The physical Clean row of a flat table: the typed input followed by an empty witness block. -/
def memoryBumpPhysicalRow {F : Type} (r : MemoryBumpChip.Inputs F) : Array F :=
  inputFirstRow r #v[]

/-- The verifier environment a Rust row induces on the native chip. -/
def memoryBumpEnvironment (cols : Extracted.MemoryBumpCols (ZMod p)) (data : ProverData (ZMod p)) :
    Environment (ZMod p) :=
  Environment.fromArray (memoryBumpPhysicalRow (memoryBumpDeconfigure cols)) data

/-- The flat table's physical width: fifteen input cells and no witness block. -/
theorem memoryBumpChip_size_eq :
    (MemoryBumpChip.circuit (p := p)).size = size MemoryBumpChip.Inputs := by
  rw [GeneralFormalCircuit.size_eq, MemoryBumpChip.circuit_localLength, Nat.add_zero]

/-- The reconstructed row has exactly the flat component's width — 15 cells, no witness block. -/
theorem memoryBumpPhysicalRow_size (cols : Extracted.MemoryBumpCols (ZMod p)) :
    (memoryBumpPhysicalRow (memoryBumpDeconfigure cols)).size =
      (⟨MemoryBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).width := by
  rw [memoryBumpPhysicalRow, inputFirstRow_size, Air.Flat.Component.width, memoryBumpChip_size_eq]
  simp

/-- The reconstructed row decodes back to the native row the codec started from. -/
theorem memoryBumpEnvironment_rowInput (cols : Extracted.MemoryBumpCols (ZMod p))
    (data : ProverData (ZMod p)) :
    (⟨MemoryBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInput
        (memoryBumpEnvironment cols data) = memoryBumpDeconfigure cols :=
  rowInput_inputFirstRow _ _ _ _

omit [Fact (2 ^ 17 < p)] in
/-- The component's row input *variables* evaluate to the decoded native row. -/
theorem memoryBumpEnvironment_eval (cols : Extracted.MemoryBumpCols (ZMod p))
    (data : ProverData (ZMod p)) :
    Eval.eval (memoryBumpEnvironment cols data)
        (varFromOffset MemoryBumpChip.Inputs 0 : Var MemoryBumpChip.Inputs (ZMod p)) =
      memoryBumpDeconfigure cols :=
  eval_inputFirstRow _ _ _

/-- Component-wise evaluation of the innermost timestamp block of the shared `MemoryAccessCols`
carrier. -/
theorem eval_memoryBumpTimestamp {F : Type} [FiniteField F]
    (env : Environment F) (ts : Extracted.MemoryAccessTimestamp (Expression F)) :
    Eval.eval env ts =
      ({ prev_high := Eval.eval env ts.prev_high
         prev_low := Eval.eval env ts.prev_low
         compare_low := Eval.eval env ts.compare_low
         diff_low_limb := Eval.eval env ts.diff_low_limb
         diff_high_limb := Eval.eval env ts.diff_high_limb } :
        Extracted.MemoryAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the shared `MemoryAccessCols` carrier. -/
theorem eval_memoryBumpAccess {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the native MemoryBump row. -/
theorem eval_memoryBumpInputs {F : Type} [FiniteField F]
    (env : Environment F) (r : MemoryBumpChip.Inputs (Expression F)) :
    Eval.eval env r =
      ({ access := Eval.eval env r.access
         clk_32_48 := Eval.eval env r.clk_32_48
         clk_24_32 := Eval.eval env r.clk_24_32
         clk_16_24 := Eval.eval env r.clk_16_24
         clk_0_16 := Eval.eval env r.clk_0_16
         addr := Eval.eval env r.addr
         is_real := Eval.eval env r.is_real } : MemoryBumpChip.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- The fifteen cell-level equations behind a whole-row binding. -/
private theorem memoryBumpFieldEqs (env : Environment (ZMod p))
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (cols : Extracted.MemoryBumpCols (ZMod p))
    (hrow : Eval.eval env r = memoryBumpDeconfigure cols) :
    Expression.eval env r.access.prev_value[0] = cols.values[0] ∧
      Expression.eval env r.access.prev_value[1] = cols.values[1] ∧
      Expression.eval env r.access.prev_value[2] = cols.values[2] ∧
      Expression.eval env r.access.prev_value[3] = cols.values[3] ∧
      Expression.eval env r.access.access_timestamp.prev_high = cols.values[4] ∧
      Expression.eval env r.access.access_timestamp.prev_low = cols.values[5] ∧
      Expression.eval env r.access.access_timestamp.compare_low = cols.values[6] ∧
      Expression.eval env r.access.access_timestamp.diff_low_limb = cols.values[7] ∧
      Expression.eval env r.access.access_timestamp.diff_high_limb = cols.values[8] ∧
      Expression.eval env r.clk_32_48 = cols.values[9] ∧
      Expression.eval env r.clk_24_32 = cols.values[10] ∧
      Expression.eval env r.clk_16_24 = cols.values[11] ∧
      Expression.eval env r.clk_0_16 = cols.values[12] ∧
      Expression.eval env r.addr = cols.values[13] ∧
      Expression.eval env r.is_real = cols.values[14] := by
  rw [eval_memoryBumpInputs] at hrow
  have haccess : Eval.eval env r.access = (memoryBumpDeconfigure cols).access :=
    congrArg MemoryBumpChip.Inputs.access hrow
  rw [eval_memoryBumpAccess] at haccess
  have hword : Eval.eval env r.access.prev_value =
      (memoryBumpDeconfigure cols).access.prev_value :=
    congrArg Extracted.MemoryAccessCols.prev_value haccess
  have hts : Eval.eval env r.access.access_timestamp =
      (memoryBumpDeconfigure cols).access.access_timestamp :=
    congrArg Extracted.MemoryAccessCols.access_timestamp haccess
  rw [eval_memoryBumpTimestamp] at hts
  simp only [ProvableType.eval_field] at hrow hts
  exact ⟨(ProvableType.getElem_eval_fields env r.access.prev_value 0 (by decide)).trans
      (congrArg (fun value => value[0]) hword),
    (ProvableType.getElem_eval_fields env r.access.prev_value 1 (by decide)).trans
      (congrArg (fun value => value[1]) hword),
    (ProvableType.getElem_eval_fields env r.access.prev_value 2 (by decide)).trans
      (congrArg (fun value => value[2]) hword),
    (ProvableType.getElem_eval_fields env r.access.prev_value 3 (by decide)).trans
      (congrArg (fun value => value[3]) hword),
    congrArg Extracted.MemoryAccessTimestamp.prev_high hts,
    congrArg Extracted.MemoryAccessTimestamp.prev_low hts,
    congrArg Extracted.MemoryAccessTimestamp.compare_low hts,
    congrArg Extracted.MemoryAccessTimestamp.diff_low_limb hts,
    congrArg Extracted.MemoryAccessTimestamp.diff_high_limb hts,
    congrArg MemoryBumpChip.Inputs.clk_32_48 hrow,
    congrArg MemoryBumpChip.Inputs.clk_24_32 hrow,
    congrArg MemoryBumpChip.Inputs.clk_16_24 hrow,
    congrArg MemoryBumpChip.Inputs.clk_0_16 hrow,
    congrArg MemoryBumpChip.Inputs.addr hrow,
    congrArg MemoryBumpChip.Inputs.is_real hrow⟩

/-! ## Assertion-system agreement -/

omit [Fact (2 ^ 17 < p)] in
/-- The native chip's complete evaluated `assertZero` list, in source order: the `is_real` gate and
the three `is_real`-gated `eval_memory_access_timestamp` equations. -/
theorem memoryBumpAssertList (env : Environment (ZMod p))
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((MemoryBumpChip.main r).operations offset) =
      [ Expression.eval env (r.is_real * (r.is_real - 1)),
        Expression.eval env
          (r.is_real * (r.access.access_timestamp.compare_low *
            (r.access.access_timestamp.compare_low - 1))),
        Expression.eval env
          (r.is_real * (r.access.access_timestamp.compare_low *
            (r.clk_24_32 + r.clk_32_48 * 256 - r.access.access_timestamp.prev_high))),
        Expression.eval env
          (r.is_real *
            ((r.access.access_timestamp.compare_low * (r.clk_0_16 + r.clk_16_24 * 65536)
                + (1 - r.access.access_timestamp.compare_low) * (r.clk_24_32 + r.clk_32_48 * 256)
              - (r.access.access_timestamp.compare_low * r.access.access_timestamp.prev_low
                + (1 - r.access.access_timestamp.compare_low) *
                  r.access.access_timestamp.prev_high)
              - 1)
            - (r.access.access_timestamp.diff_low_limb
                + r.access.access_timestamp.diff_high_limb * 65536))) ] := by
  change nativeAssertZeros env
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- **Chip-level faithfulness anchor — assertion half.** SP1's generated whole-table `MemoryBump`
assertion list holds exactly when the native circuit's complete `assertZero` list does. The lists
agree entry for entry in source order, except that the extracted dump repeats the `is_real` boolean
gate (SP1's `eval_memory_access_read` fragment re-asserts it) where the native circuit states it
once. -/
theorem memoryBumpChipConstraintsFaithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (env : Environment (ZMod p)) (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.MemoryBumpCols (ZMod p))
    (hrow : Eval.eval env r = memoryBumpDeconfigure cols) :
    List.Forall (· = 0) (Extracted.MemoryBumpCols.asserts cols preprocessed publicValues) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((MemoryBumpChip.main r).operations offset)) := by
  obtain ⟨-, -, -, -, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, h14⟩ :=
    memoryBumpFieldEqs env r cols hrow
  rw [memoryBumpAssertList]
  simp only [Extracted.MemoryBumpCols.asserts, List.Forall, Expression.eval, eval_sub,
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, Nat.cast_one, and_self_left]

/-! ## Interaction agreement -/

omit [Fact (2 ^ 17 < p)] in
/-- The chip's exact Memory pair: the old-record pull, then the refreshed push. -/
theorem memoryBumpInteractionsWith_memory
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryBumpChip.main r).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulledIf r.is_real (MemoryBumpChip.pulledMsg r)).toRaw,
       (memoryChannel.pushedIf r.is_real (MemoryBumpChip.pushedMsg r)).toRaw] := by
  change Operations.interactionsWith _
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- The chip's exact six byte checks: the four refreshed-clock limb checks, the register-index
`LTU` check, and the two timestamp-difference limb checks. -/
theorem memoryBumpInteractionsWith_byte
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryBumpChip.main r).operations offset).interactionsWith byteChannel.toRaw =
      [ (byteChannel.pulledIf r.is_real
          (⟨6, r.clk_0_16, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨6, r.clk_32_48, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨3, 0, r.clk_16_24, r.clk_24_32⟩ : ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨4, 1, r.addr, Expression.const ((32 : ℕ) : ZMod p)⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨6, r.access.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨3, 0, r.access.access_timestamp.diff_high_limb, 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw ] := by
  change Operations.interactionsWith _
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- `MemoryBump` never touches the State bus. -/
theorem memoryBumpInteractionsWith_state
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryBumpChip.main r).operations offset).interactionsWith
      Channels.stateChannel.toRaw = [] := by
  change Operations.interactionsWith _
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- `MemoryBump` never touches the Program bus. -/
theorem memoryBumpInteractionsWith_program
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryBumpChip.main r).operations offset).interactionsWith
      Channels.programChannel.toRaw = [] := by
  change Operations.interactionsWith _
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- Every emitted interaction lands on one of the four known SP1 buses. -/
theorem memoryBumpUnexpectedInteractions
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions ((MemoryBumpChip.main r).operations offset) = [] := by
  change unexpectedInteractions
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [unexpectedInteractions, circuit_norm]

/-- **Chip-level faithfulness anchor — interaction half.** The native circuit's complete emitted
interaction list and SP1's extracted whole-table `MemoryBump` interaction list project to the *same*
`LookupAccess` list — same entries, same signed multiplicities, same order — once the Memory bus's
project-wide polarity flip is bridged by the `negMult` already built into `nativeAccesses` together
with the `signedVal (-x) = -signedVal x` sign symmetry. -/
theorem memoryBumpChipInteractionsFaithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (env : Environment (ZMod p)) (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.MemoryBumpCols (ZMod p))
    (hrow : Eval.eval env r = memoryBumpDeconfigure cols) :
    nativeAccesses env ((MemoryBumpChip.main r).operations offset) =
      (Extracted.MemoryBumpCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess := by
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  obtain ⟨h0, h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    memoryBumpFieldEqs env r cols hrow
  have hMemoryPull :
      ∀ (gate : Expression (ZMod p)) (msg : MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env ((memoryChannel.pulledIf gate msg).toRaw) =
          (InteractionKind.Memory, "SP1Memory",
            [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
             (Expression.eval env msg.addr2).val, (Expression.eval env msg.value[0]).val,
             (Expression.eval env msg.value[1]).val, (Expression.eval env msg.value[2]).val,
             (Expression.eval env msg.value[3]).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_memory env gate msg
  have hMemoryPush :
      ∀ (mult : Expression (ZMod p)) (msg : MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env ((memoryChannel.pushedIf mult msg).toRaw) =
          (InteractionKind.Memory, "SP1Memory",
            [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
             (Expression.eval env msg.addr2).val, (Expression.eval env msg.value[0]).val,
             (Expression.eval env msg.value[1]).val, (Expression.eval env msg.value[2]).val,
             (Expression.eval env msg.value[3]).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_memory env mult msg
  have hBytePull :
      ∀ (gate : Expression (ZMod p)) (msg : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env ((byteChannel.pulledIf gate msg).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env msg.opcode).val, (Expression.eval env msg.a).val,
             (Expression.eval env msg.b).val, (Expression.eval env msg.c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_byte env gate msg
  simp only [nativeAccesses, memoryBumpUnexpectedInteractions, memoryBumpInteractionsWith_state,
    memoryBumpInteractionsWith_byte, memoryBumpInteractionsWith_memory,
    memoryBumpInteractionsWith_program, List.map_nil, List.append_nil, List.nil_append,
    List.map_cons, hMemoryPull, hMemoryPush, hBytePull]
  simp only [MemoryBumpChip.pulledMsg, MemoryBumpChip.pushedMsg,
    Extracted.MemoryBumpCols.interactions, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Extracted.Interaction.toAccess, Extracted.Dir.sign, Expression.eval,
    LookupAccessList.negMult, signedVal_neg hp2, neg_neg,
    h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13, h14,
    Nat.cast_ofNat, neg_one_mul]

/-! ## The constructive whole-chip boundary -/

/-- The bundled circuit's `main` is the chip's `main`. -/
theorem memoryBumpChip_main_eq :
    (MemoryBumpChip.circuit (p := p)).main = MemoryBumpChip.main := rfl

/-- The flat table emits no Clean `Lookup` operations — every SP1 byte check is a channel
interaction, and is therefore compared by the interaction half. -/
theorem memoryBumpChip_lookups_empty :
    (⟨MemoryBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk, memoryBumpChip_main_eq]
  change Operations.lookups
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
      .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p)) = _
  simp [circuit_norm]

/-- **Constructive assertion agreement.** For every Rust row and prover data, the extracted
whole-table assertion list holds exactly when Clean's full constraint predicate holds on the
reconstructed physical row. -/
theorem memoryBumpChipConstraintsConstructive
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (rustCols : Extracted.MemoryBumpCols (ZMod p)) (data : ProverData (ZMod p)) :
    List.Forall (· = 0)
        ((memoryBumpChipOracle preprocessed publicValues).assertZeros rustCols) ↔
      (⟨MemoryBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations.ConstraintsHold
        (memoryBumpEnvironment rustCols data) := by
  refine Iff.trans ?_
    (constraintsHold_iff_nativeAssertZeros (MemoryBumpChip.circuit (p := p))
      (memoryBumpEnvironment rustCols data) memoryBumpChip_lookups_empty).symm
  rw [Air.Flat.Component.rowOperations_mk, memoryBumpChip_main_eq]
  exact memoryBumpChipConstraintsFaithful preprocessed publicValues
    (memoryBumpEnvironment rustCols data)
    (varFromOffset MemoryBumpChip.Inputs 0) (size MemoryBumpChip.Inputs) rustCols
    (memoryBumpEnvironment_eval rustCols data)

/-- **Constructive interaction agreement.** The reconstructed native row's complete emitted
interaction multiset equals the extracted whole-table interaction multiset. -/
theorem memoryBumpChipInteractionsConstructive
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (rustCols : Extracted.MemoryBumpCols (ZMod p)) (data : ProverData (ZMod p)) :
    nativeAccesses (memoryBumpEnvironment rustCols data)
        (⟨MemoryBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations =
      (memoryBumpChipOracle preprocessed publicValues).rustAccesses rustCols := by
  rw [nativeAccesses_component_eq_rowOperations (MemoryBumpChip.circuit (p := p)),
    Air.Flat.Component.rowOperations_mk, memoryBumpChip_main_eq]
  exact memoryBumpChipInteractionsFaithful preprocessed publicValues
    (memoryBumpEnvironment rustCols data)
    (varFromOffset MemoryBumpChip.Inputs 0) (size MemoryBumpChip.Inputs) rustCols
    (memoryBumpEnvironment_eval rustCols data)

/-- **Whole-table faithfulness for `MemoryBump`.** The two `ChipFaithful` clauses, instantiated at
the input-keyed row codec this flat table needs: the extracted whole-table assertion system is
equivalent to the native circuit's complete constraint system on the reconstructed row, and — on
rows those assertions accept — the two complete active interaction multisets agree (modulo the
Memory bus's polarity convention, bridged inside `nativeAccesses`). Both clauses are stated against
`⟨MemoryBumpChip.circuit⟩`, the flat component `sp1Ensemble` registers. -/
theorem memoryBumpChip_faithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160) :
    (∀ (rustCols : Extracted.MemoryBumpCols (ZMod p)) (data : ProverData (ZMod p)),
        List.Forall (· = 0)
            ((memoryBumpChipOracle preprocessed publicValues).assertZeros rustCols) ↔
          (⟨MemoryBumpChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).operations.ConstraintsHold
              (memoryBumpEnvironment rustCols data)) ∧
      ∀ (rustCols : Extracted.MemoryBumpCols (ZMod p)) (data : ProverData (ZMod p)),
        List.Forall (· = 0)
            ((memoryBumpChipOracle preprocessed publicValues).assertZeros rustCols) →
          List.Perm
            (LookupAccessList.active
              (nativeAccesses (memoryBumpEnvironment rustCols data)
                (⟨MemoryBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations))
            (LookupAccessList.active
              ((memoryBumpChipOracle preprocessed publicValues).rustAccesses rustCols)) :=
  ⟨memoryBumpChipConstraintsConstructive preprocessed publicValues,
   fun rustCols data _ =>
     LookupAccessList.active_perm
       (List.Perm.of_eq
         (memoryBumpChipInteractionsConstructive preprocessed publicValues rustCols data))⟩

end SP1Clean.Faithful
