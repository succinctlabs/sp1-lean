import SP1Clean.Extracted.SystemOracle.StateBump
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Proofs.Chips.StateBumpChip.Formal

/-! # Chip-level faithfulness anchor — SP1's whole `StateBump` system table

The whole-table Rust oracle boundary for the first of the two W3 system tables (external report
Finding 5): the native `StateBumpChip` circuit's complete `assertZero` list and complete interaction
multiset are compared against `Extracted/SystemOracle/StateBump.lean`, the extracted
`sp1-constraint-compiler` dump of upstream's `StateBumpChip::eval`
(`../sp1 crates/core/machine/src/adapter/bump.rs`).

## Shape of the anchor

`StateBump` is a **flat own-assert table**: no composed subcircuits, no readers, no operations, and
`localLength = 0`, so all fourteen cells are inputs and the native physical row *is* the extracted
flat `values` vector. Two consequences shape this file relative to the 25 instruction anchors:

* the native row type is the chip's `Inputs` rather than a separate `Columns` block, so
  `stateBumpChipOracle` is a `ChipOracle` over `StateBumpChip.Inputs` and the row codec is the
  input-first physical row `inputFirstRow r #v[]` (`stateBumpPhysicalRow`);
* the chip's Clean output is `unit` (a flat table computes nothing), so the anchor is stated as the
  two `ChipFaithful` clauses over that input-keyed codec rather than through the `ChipFaithful`
  structure itself, whose `ChipRowCodec` is keyed on the circuit's *output* type map. Both clauses
  are stated against the real `⟨StateBumpChip.circuit⟩` flat component the ensemble registers —
  `stateBumpChip_faithful` bundles them.

## Sign convention

`StateBump` touches only the State and Byte buses, and neither is polarity-flipped: the native
`stateChannel.pullIf`/`pushIf` pair projects to the same signed multiplicities as the oracle's
`.receive`/`.send` `.state` pair, and the byte-arm negation in `Extracted.Interaction.toAccess`
already matches Clean's byte *pull* convention. The full interaction comparison is therefore an
equality of `LookupAccess` lists, in emission order, not merely a permutation. (The Memory flip that
the companion `Faithful/MemoryBumpChip.lean` has to bridge does not arise here.)
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Channels (stateChannel byteChannel StateMsg)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The whole-row column codec -/

/-- Whole-row reconfiguration: the native `StateBumpChip.Inputs` row in upstream `StateBumpCols`
field order (`adapter/bump.rs`). The extraction layer keeps the row as a flat 14-cell vector, so
this map is the audit-visible column order. -/
def stateBumpReconfigure {F : Type} (r : StateBumpChip.Inputs F) : Extracted.StateBumpCols F :=
  ⟨#v[r.next_clk_32_48, r.next_clk_24_32, r.next_clk_16_24, r.next_clk_0_16,
      r.clk_high, r.clk_low, r.next_pc0, r.next_pc1, r.next_pc2,
      r.pc0, r.pc1, r.pc2, r.is_clk, r.is_real]⟩

/-- Inverse whole-row map, used to reconstruct the native proof row from an arbitrary Rust row. -/
def stateBumpDeconfigure {F : Type} (cols : Extracted.StateBumpCols F) : StateBumpChip.Inputs F :=
  { next_clk_32_48 := cols.values[0]
    next_clk_24_32 := cols.values[1]
    next_clk_16_24 := cols.values[2]
    next_clk_0_16 := cols.values[3]
    clk_high := cols.values[4]
    clk_low := cols.values[5]
    next_pc0 := cols.values[6]
    next_pc1 := cols.values[7]
    next_pc2 := cols.values[8]
    pc0 := cols.values[9]
    pc1 := cols.values[10]
    pc2 := cols.values[11]
    is_clk := cols.values[12]
    is_real := cols.values[13] }

theorem stateBumpDeconfigure_reconfigure {F : Type} :
    Function.LeftInverse (stateBumpDeconfigure (F := F)) stateBumpReconfigure := by
  intro r
  cases r
  rfl

theorem stateBumpReconfigure_deconfigure {F : Type} :
    Function.LeftInverse (stateBumpReconfigure (F := F)) stateBumpDeconfigure := by
  intro cols
  obtain ⟨values⟩ := cols
  simp only [stateBumpDeconfigure, stateBumpReconfigure, Extracted.StateBumpCols.mk.injEq]
  ext i hi
  interval_cases i <;> rfl

/-- SP1 Rust's complete `StateBump` oracle, viewed from the native Lean row. The generated
`asserts`/`interactions` ignore both the (width-zero) preprocessed row and the public values, so the
anchor holds for every choice of them; they stay explicit parameters so the oracle is literally the
one `FormalModel`'s exact Core AIR relation evaluates (`Faithful/CoreAIR.lean`, `.stateBump` arm). -/
def stateBumpChipOracle (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160) :
    ChipOracle (ZMod p) StateBumpChip.Inputs Extracted.StateBumpCols where
  reconfigure := stateBumpReconfigure
  deconfigure := stateBumpDeconfigure
  reconfigure_deconfigure := stateBumpReconfigure_deconfigure
  deconfigure_reconfigure := stateBumpDeconfigure_reconfigure
  assertZeros cols := Extracted.StateBumpCols.asserts cols preprocessed publicValues
  interactions cols := Extracted.StateBumpCols.interactions cols preprocessed publicValues

/-! ## The physical row -/

/-- The physical Clean row of a flat table: the typed input followed by an empty witness block. -/
def stateBumpPhysicalRow {F : Type} (r : StateBumpChip.Inputs F) : Array F :=
  inputFirstRow r #v[]

/-- The verifier environment a Rust row induces on the native chip. -/
def stateBumpEnvironment (cols : Extracted.StateBumpCols (ZMod p)) (data : ProverData (ZMod p)) :
    Environment (ZMod p) :=
  Environment.fromArray (stateBumpPhysicalRow (stateBumpDeconfigure cols)) data

/-- The flat table's physical width: fourteen input cells and no witness block. -/
theorem stateBumpChip_size_eq :
    (StateBumpChip.circuit (p := p)).size = size StateBumpChip.Inputs := by
  rw [GeneralFormalCircuit.size_eq, StateBumpChip.circuit_localLength, Nat.add_zero]

/-- The reconstructed row has exactly the flat component's width — 14 cells, no witness block. -/
theorem stateBumpPhysicalRow_size (cols : Extracted.StateBumpCols (ZMod p)) :
    (stateBumpPhysicalRow (stateBumpDeconfigure cols)).size =
      (⟨StateBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).width := by
  rw [stateBumpPhysicalRow, inputFirstRow_size, Air.Flat.Component.width, stateBumpChip_size_eq]
  simp

/-- The reconstructed row decodes back to the native row the codec started from. -/
theorem stateBumpEnvironment_rowInput (cols : Extracted.StateBumpCols (ZMod p))
    (data : ProverData (ZMod p)) :
    (⟨StateBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInput
        (stateBumpEnvironment cols data) = stateBumpDeconfigure cols :=
  rowInput_inputFirstRow _ _ _ _

omit [Fact (2 ^ 17 < p)] in
/-- The component's row input *variables* evaluate to the decoded native row. -/
theorem stateBumpEnvironment_eval (cols : Extracted.StateBumpCols (ZMod p))
    (data : ProverData (ZMod p)) :
    Eval.eval (stateBumpEnvironment cols data)
        (varFromOffset StateBumpChip.Inputs 0 : Var StateBumpChip.Inputs (ZMod p)) =
      stateBumpDeconfigure cols :=
  eval_inputFirstRow _ _ _

/-- Component-wise evaluation of the native StateBump row. -/
theorem eval_stateBumpInputs {F : Type} [FiniteField F]
    (env : Environment F) (r : StateBumpChip.Inputs (Expression F)) :
    Eval.eval env r =
      ({ next_clk_32_48 := Eval.eval env r.next_clk_32_48
         next_clk_24_32 := Eval.eval env r.next_clk_24_32
         next_clk_16_24 := Eval.eval env r.next_clk_16_24
         next_clk_0_16 := Eval.eval env r.next_clk_0_16
         clk_high := Eval.eval env r.clk_high
         clk_low := Eval.eval env r.clk_low
         next_pc0 := Eval.eval env r.next_pc0
         next_pc1 := Eval.eval env r.next_pc1
         next_pc2 := Eval.eval env r.next_pc2
         pc0 := Eval.eval env r.pc0
         pc1 := Eval.eval env r.pc1
         pc2 := Eval.eval env r.pc2
         is_clk := Eval.eval env r.is_clk
         is_real := Eval.eval env r.is_real } : StateBumpChip.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- The fourteen cell-level equations behind a whole-row binding. -/
private theorem stateBumpFieldEqs (env : Environment (ZMod p))
    (r : Var StateBumpChip.Inputs (ZMod p)) (cols : Extracted.StateBumpCols (ZMod p))
    (hrow : Eval.eval env r = stateBumpDeconfigure cols) :
    Expression.eval env r.next_clk_32_48 = cols.values[0] ∧
      Expression.eval env r.next_clk_24_32 = cols.values[1] ∧
      Expression.eval env r.next_clk_16_24 = cols.values[2] ∧
      Expression.eval env r.next_clk_0_16 = cols.values[3] ∧
      Expression.eval env r.clk_high = cols.values[4] ∧
      Expression.eval env r.clk_low = cols.values[5] ∧
      Expression.eval env r.next_pc0 = cols.values[6] ∧
      Expression.eval env r.next_pc1 = cols.values[7] ∧
      Expression.eval env r.next_pc2 = cols.values[8] ∧
      Expression.eval env r.pc0 = cols.values[9] ∧
      Expression.eval env r.pc1 = cols.values[10] ∧
      Expression.eval env r.pc2 = cols.values[11] ∧
      Expression.eval env r.is_clk = cols.values[12] ∧
      Expression.eval env r.is_real = cols.values[13] := by
  rw [eval_stateBumpInputs] at hrow
  simp only [ProvableType.eval_field] at hrow
  exact ⟨congrArg StateBumpChip.Inputs.next_clk_32_48 hrow,
    congrArg StateBumpChip.Inputs.next_clk_24_32 hrow,
    congrArg StateBumpChip.Inputs.next_clk_16_24 hrow,
    congrArg StateBumpChip.Inputs.next_clk_0_16 hrow,
    congrArg StateBumpChip.Inputs.clk_high hrow,
    congrArg StateBumpChip.Inputs.clk_low hrow,
    congrArg StateBumpChip.Inputs.next_pc0 hrow,
    congrArg StateBumpChip.Inputs.next_pc1 hrow,
    congrArg StateBumpChip.Inputs.next_pc2 hrow,
    congrArg StateBumpChip.Inputs.pc0 hrow,
    congrArg StateBumpChip.Inputs.pc1 hrow,
    congrArg StateBumpChip.Inputs.pc2 hrow,
    congrArg StateBumpChip.Inputs.is_clk hrow,
    congrArg StateBumpChip.Inputs.is_real hrow⟩

/-! ## Assertion-system agreement -/

omit [Fact (2 ^ 17 < p)] in
/-- The native chip's complete evaluated `assertZero` list, in source order: the `is_real` gate, the
`is_clk` gate, the two `is_real`-gated clock-carry equations, the three binary pc borrows, and the
vanishing top borrow. -/
theorem stateBumpAssertList (env : Environment (ZMod p))
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((StateBumpChip.main r).operations offset) =
      [ Expression.eval env (r.is_real * (r.is_real - 1)),
        Expression.eval env (r.is_clk * (r.is_clk - 1)),
        Expression.eval env
          (r.is_real * (r.next_clk_24_32 + r.next_clk_32_48 * 256 - (r.clk_high + r.is_clk))),
        Expression.eval env
          (r.is_real *
            (r.next_clk_0_16 + r.next_clk_16_24 * 65536 + r.is_clk * 16777216 - r.clk_low)),
        Expression.eval env
          ((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ *
            ((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ - 1)),
        Expression.eval env
          (((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ + r.pc1 - r.next_pc1) * (65536 : ZMod p)⁻¹ *
            ((((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ + r.pc1 - r.next_pc1) *
              (65536 : ZMod p)⁻¹) - 1)),
        Expression.eval env
          (((((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ + r.pc1 - r.next_pc1) *
                (65536 : ZMod p)⁻¹ + r.pc2 - r.next_pc2) * (65536 : ZMod p)⁻¹ *
            (((((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ + r.pc1 - r.next_pc1) *
                (65536 : ZMod p)⁻¹ + r.pc2 - r.next_pc2) * (65536 : ZMod p)⁻¹) - 1))),
        Expression.eval env
          ((((r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹ + r.pc1 - r.next_pc1) *
              (65536 : ZMod p)⁻¹ + r.pc2 - r.next_pc2) * (65536 : ZMod p)⁻¹) ] := by
  change nativeAssertZeros env
    ([.assert _, .interact _, .interact _, .interact _, .interact _, .interact _, .assert _,
      .assert _, .assert _, .assert _, .assert _, .assert _, .assert _, .interact _,
      .interact _, .interact _] : Operations (ZMod p)) = _
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- **Chip-level faithfulness anchor — assertion half.** SP1's generated whole-table `StateBump`
assertion list holds exactly when the native circuit's complete `assertZero` list does. The two
lists agree entry for entry in the same order; the only textual difference is the extracted dump's
`0 + pc0` accumulator seed for the first pc borrow. -/
theorem stateBumpChipConstraintsFaithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (env : Environment (ZMod p)) (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.StateBumpCols (ZMod p))
    (hrow : Eval.eval env r = stateBumpDeconfigure cols) :
    List.Forall (· = 0) (Extracted.StateBumpCols.asserts cols preprocessed publicValues) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((StateBumpChip.main r).operations offset)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    stateBumpFieldEqs env r cols hrow
  rw [stateBumpAssertList]
  simp only [Extracted.StateBumpCols.asserts, List.Forall, Expression.eval, eval_sub,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, Nat.cast_zero, zero_add]

/-! ## Interaction agreement -/

omit [Fact (2 ^ 17 < p)] in
/-- The chip's exact State pair: the possibly-non-canonical pull, then the canonical push. -/
theorem stateBumpInteractionsWith_state
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StateBumpChip.main r).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulledIf r.is_real (StateBumpChip.pulledMsg r)).toRaw,
       (stateChannel.pushedIf r.is_real (StateBumpChip.pushedMsg r)).toRaw] := by
  simp [StateBumpChip.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- The chip's exact six byte range checks: the three pushed-clock limb checks, then the three
pushed-pc limb checks. -/
theorem stateBumpInteractionsWith_byte
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StateBumpChip.main r).operations offset).interactionsWith byteChannel.toRaw =
      [ (byteChannel.pulledIf r.is_real
          (⟨6, (r.next_clk_0_16 - 1) * (8 : ZMod p)⁻¹, Expression.const ((13 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨6, r.next_clk_32_48, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨3, 0, r.next_clk_16_24, r.next_clk_24_32⟩ : ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨6, r.next_pc0, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨6, r.next_pc1, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
        (byteChannel.pulledIf r.is_real
          (⟨6, r.next_pc2, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw ] := by
  simp [StateBumpChip.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- `StateBump` never touches the Memory bus. -/
theorem stateBumpInteractionsWith_memory
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StateBumpChip.main r).operations offset).interactionsWith
      Channels.memoryChannel.toRaw = [] := by
  simp [StateBumpChip.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- `StateBump` never touches the Program bus. -/
theorem stateBumpInteractionsWith_program
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StateBumpChip.main r).operations offset).interactionsWith
      Channels.programChannel.toRaw = [] := by
  simp [StateBumpChip.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- Every emitted interaction lands on one of the four known SP1 buses. -/
theorem stateBumpUnexpectedInteractions
    (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions ((StateBumpChip.main r).operations offset) = [] := by
  simp [unexpectedInteractions, StateBumpChip.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- **Chip-level faithfulness anchor — interaction half.** The native circuit's complete emitted
interaction list and SP1's extracted whole-table `StateBump` interaction list project to the *same*
`LookupAccess` list — same entries, same signed multiplicities, same order. State and Byte are the
two aligned buses (no polarity bridge is needed), and the chip touches no other bus. -/
theorem stateBumpChipInteractionsFaithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (env : Environment (ZMod p)) (r : Var StateBumpChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.StateBumpCols (ZMod p))
    (hrow : Eval.eval env r = stateBumpDeconfigure cols) :
    nativeAccesses env ((StateBumpChip.main r).operations offset) =
      (Extracted.StateBumpCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h13⟩ :=
    stateBumpFieldEqs env r cols hrow
  have hStatePull :
      ∀ (gate : Expression (ZMod p)) (msg : StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env ((stateChannel.pulledIf gate msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_state env gate msg
  have hStatePush :
      ∀ (mult : Expression (ZMod p)) (msg : StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env ((stateChannel.pushedIf mult msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_state env mult msg
  have hBytePull :
      ∀ (gate : Expression (ZMod p)) (msg : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env ((byteChannel.pulledIf gate msg).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env msg.opcode).val, (Expression.eval env msg.a).val,
             (Expression.eval env msg.b).val, (Expression.eval env msg.c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_byte env gate msg
  simp only [nativeAccesses, stateBumpUnexpectedInteractions, stateBumpInteractionsWith_state,
    stateBumpInteractionsWith_byte, stateBumpInteractionsWith_memory,
    stateBumpInteractionsWith_program, List.map_nil, List.append_nil, List.map_cons,
    hStatePull, hStatePush, hBytePull]
  simp only [StateBumpChip.pulledMsg, StateBumpChip.pushedMsg,
    Extracted.StateBumpCols.interactions, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Extracted.Interaction.toAccess, Extracted.Dir.sign, Expression.eval,
    eval_sub, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13,
    Nat.cast_ofNat, neg_one_mul]

/-! ## The constructive whole-chip boundary -/

/-- The bundled circuit's `main` is the chip's `main`. -/
theorem stateBumpChip_main_eq : (StateBumpChip.circuit (p := p)).main = StateBumpChip.main := rfl

/-- The flat table emits no Clean `Lookup` operations — every SP1 byte check is a channel
interaction, and is therefore compared by the interaction half. -/
theorem stateBumpChip_lookups_empty :
    (⟨StateBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk, stateBumpChip_main_eq]
  simp [StateBumpChip.main, circuit_norm]

/-- **Constructive assertion agreement.** For every Rust row and prover data, the extracted
whole-table assertion list holds exactly when Clean's full constraint predicate holds on the
reconstructed physical row. -/
theorem stateBumpChipConstraintsConstructive
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (rustCols : Extracted.StateBumpCols (ZMod p)) (data : ProverData (ZMod p)) :
    List.Forall (· = 0)
        ((stateBumpChipOracle preprocessed publicValues).assertZeros rustCols) ↔
      (⟨StateBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations.ConstraintsHold
        (stateBumpEnvironment rustCols data) := by
  refine Iff.trans ?_
    (constraintsHold_iff_nativeAssertZeros (StateBumpChip.circuit (p := p))
      (stateBumpEnvironment rustCols data) stateBumpChip_lookups_empty).symm
  rw [Air.Flat.Component.rowOperations_mk, stateBumpChip_main_eq]
  exact stateBumpChipConstraintsFaithful preprocessed publicValues
    (stateBumpEnvironment rustCols data)
    (varFromOffset StateBumpChip.Inputs 0) (size StateBumpChip.Inputs) rustCols
    (stateBumpEnvironment_eval rustCols data)

/-- **Constructive interaction agreement.** The reconstructed native row's complete emitted
interaction multiset equals the extracted whole-table interaction multiset. -/
theorem stateBumpChipInteractionsConstructive
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (rustCols : Extracted.StateBumpCols (ZMod p)) (data : ProverData (ZMod p)) :
    nativeAccesses (stateBumpEnvironment rustCols data)
        (⟨StateBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations =
      (stateBumpChipOracle preprocessed publicValues).rustAccesses rustCols := by
  rw [nativeAccesses_component_eq_rowOperations (StateBumpChip.circuit (p := p)),
    Air.Flat.Component.rowOperations_mk, stateBumpChip_main_eq]
  exact stateBumpChipInteractionsFaithful preprocessed publicValues
    (stateBumpEnvironment rustCols data)
    (varFromOffset StateBumpChip.Inputs 0) (size StateBumpChip.Inputs) rustCols
    (stateBumpEnvironment_eval rustCols data)

/-- **Whole-table faithfulness for `StateBump`.** The two `ChipFaithful` clauses, instantiated at
the input-keyed row codec this flat table needs: the extracted whole-table assertion system is
equivalent to the native circuit's complete constraint system on the reconstructed row, and — on
rows those assertions accept — the two complete active interaction multisets agree. Both clauses are
stated against `⟨StateBumpChip.circuit⟩`, the flat component `sp1Ensemble` registers. -/
theorem stateBumpChip_faithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160) :
    (∀ (rustCols : Extracted.StateBumpCols (ZMod p)) (data : ProverData (ZMod p)),
        List.Forall (· = 0)
            ((stateBumpChipOracle preprocessed publicValues).assertZeros rustCols) ↔
          (⟨StateBumpChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).operations.ConstraintsHold
              (stateBumpEnvironment rustCols data)) ∧
      ∀ (rustCols : Extracted.StateBumpCols (ZMod p)) (data : ProverData (ZMod p)),
        List.Forall (· = 0)
            ((stateBumpChipOracle preprocessed publicValues).assertZeros rustCols) →
          List.Perm
            (LookupAccessList.active
              (nativeAccesses (stateBumpEnvironment rustCols data)
                (⟨StateBumpChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).operations))
            (LookupAccessList.active
              ((stateBumpChipOracle preprocessed publicValues).rustAccesses rustCols)) :=
  ⟨stateBumpChipConstraintsConstructive preprocessed publicValues,
   fun rustCols data _ =>
     LookupAccessList.active_perm
       (List.Perm.of_eq
         (stateBumpChipInteractionsConstructive preprocessed publicValues rustCols data))⟩

end SP1Clean.Faithful
