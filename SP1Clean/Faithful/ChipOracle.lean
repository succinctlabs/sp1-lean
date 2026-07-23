import SP1Clean.Extracted.ExtractionDSL
import SP1Clean.Extracted.CPUState
import SP1Clean.Extracted.RTypeReader
import SP1Clean.Faithful.ExtractedInteractionModel
import SP1Clean.Model.InteractionProjection
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import Clean.Circuit.Basic
import Clean.Circuit.Loops
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Air.FlatComponent

/-! # Chip-level Rust oracle boundary

The Rust AIR and a native Lean circuit are intentionally allowed to decompose a chip differently.
In particular, a Lean arithmetic gadget is not required to have a Rust operation-shaped row or an
operation-by-operation constraint list.  The stable boundary is the whole chip row:

* `reconfigure` maps the native Lean row to the extracted Rust chip row;
* `assertZeros` is the Rust chip's complete `assertZero` list;
* `interactions` is the Rust chip's complete interaction list.

`ChipFaithful` then asks for extensional equivalence of the two complete assertion systems and a
permutation of the two complete interaction multisets.  It deliberately says nothing about how either
side factors those lists into readers, operations, or helper gadgets.  In particular, extracted Rust
operation modules may remain as generator-private implementation details without becoming proof
boundaries or public faithfulness claims.
-/

namespace SP1Clean.Faithful

open SP1Clean
open scoped SP1Clean.ConstraintCoe

/-- The extracted Rust view of one native Lean chip row.  This is the only place where the two column
layouts need to know about one another.  The assertion and interaction functions are whole-chip
oracles, even if the generated Rust expression internally contains helper-operation calls. -/
structure ChipOracle (F : Type) [FiniteField F] [CoeHead F ℕ]
    (NativeCols RustCols : TypeMap) where
  reconfigure : NativeCols F → RustCols F
  deconfigure : RustCols F → NativeCols F
  reconfigure_deconfigure : Function.LeftInverse reconfigure deconfigure
  deconfigure_reconfigure : Function.LeftInverse deconfigure reconfigure
  assertZeros : RustCols F → List F
  interactions : RustCols F → List (Extracted.Interaction F)

namespace ChipOracle

variable {F : Type} [FiniteField F] [CoeHead F ℕ]
variable {NativeCols RustCols : TypeMap}

/-- Rust's complete chip assertion list, after reconfiguring a native Lean row. -/
def nativeAssertZeros (oracle : ChipOracle F NativeCols RustCols) (cols : NativeCols F) : List F :=
  oracle.assertZeros (oracle.reconfigure cols)

/-- Rust's complete chip interaction list, after reconfiguring a native Lean row. -/
def nativeInteractions (oracle : ChipOracle F NativeCols RustCols) (cols : NativeCols F) :
    List (Extracted.Interaction F) :=
  oracle.interactions (oracle.reconfigure cols)

@[simp] theorem nativeAssertZeros_deconfigure
    (oracle : ChipOracle F NativeCols RustCols) (cols : RustCols F) :
    oracle.nativeAssertZeros (oracle.deconfigure cols) = oracle.assertZeros cols := by
  rw [nativeAssertZeros, oracle.reconfigure_deconfigure cols]

@[simp] theorem nativeInteractions_deconfigure
    (oracle : ChipOracle F NativeCols RustCols) (cols : RustCols F) :
    oracle.nativeInteractions (oracle.deconfigure cols) = oracle.interactions cols := by
  rw [nativeInteractions, oracle.reconfigure_deconfigure cols]

end ChipOracle

/-- Values of every `assertZero` emitted by a native circuit, recursively including true Clean
subcircuits.  Witness declarations, lookups, and interactions are intentionally excluded. -/
def nativeAssertZeros {F : Type} [FiniteField F]
    (env : Environment F) (ops : Operations F) : List F :=
  ops.constraints.map (Expression.eval env)

/- Direct component-wise evaluation of the canonical generated reader rows. `ProvableStruct.eval`
preserves components by construction, but passing through the generic derived instance is expensive
for deeply nested projections. These normalization lemmas expose that construction once and let chip
proofs reuse the generated row types without reconstructing parallel reader structures. -/

@[circuit_norm] theorem eval_registerAccessTimestamp
    {F : Type} [FiniteField F] (env : Environment F)
    (x : Extracted.RegisterAccessTimestamp (Expression F)) :
    Eval.eval env x =
      ({ prev_low := Eval.eval env x.prev_low
         diff_low_limb := Eval.eval env x.diff_low_limb } :
        Extracted.RegisterAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_registerAccessCols
    {F : Type} [FiniteField F] (env : Environment F)
    (x : Extracted.RegisterAccessCols (Expression F)) :
    Eval.eval env x =
      ({ prev_value := Eval.eval env x.prev_value
         access_timestamp := Eval.eval env x.access_timestamp } :
        Extracted.RegisterAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_rTypeReader
    {F : Type} [FiniteField F] (env : Environment F)
    (x : Extracted.RTypeReader (Expression F)) :
    Eval.eval env x =
      ({ op_a := Eval.eval env x.op_a
         op_a_memory := Eval.eval env x.op_a_memory
         op_a_0 := Eval.eval env x.op_a_0
         op_b := Eval.eval env x.op_b
         op_b_memory := Eval.eval env x.op_b_memory
         op_c := Eval.eval env x.op_c
         op_c_memory := Eval.eval env x.op_c_memory } : Extracted.RTypeReader F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_cpuState
    {F : Type} [FiniteField F] (env : Environment F)
    (x : Extracted.CPUState (Expression F)) :
    Eval.eval env x =
      ({ clk_high := Eval.eval env x.clk_high
         clk_16_24 := Eval.eval env x.clk_16_24
         clk_0_16 := Eval.eval env x.clk_0_16
         pc := Eval.eval env x.pc } : Extracted.CPUState F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/- Clean currently exposes the corresponding interaction-normalization lemmas, but not the constraint
variants. Keep these two tiny flattening facts at the chip-oracle boundary so faithfulness proofs can
descend one true subcircuit at a time without unfolding `Subcircuit` soundness packages. They are good
candidates to upstream to Clean alongside `FormalAssertion.toSubcircuit_interactions`. -/
@[circuit_norm] theorem constraints_toSubcircuit_formalAssertion
    {F : Type} [FiniteField F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input : Var Input F) :
    FlatOperation.constraints (circuit.toSubcircuit n input).ops.toFlat =
      ((circuit.main input).operations n).constraints := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]

@[circuit_norm] theorem constraints_toSubcircuit_formalCircuit
    {F : Type} [FiniteField F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input : Var Input F) :
    FlatOperation.constraints (circuit.toSubcircuit n input).ops.toFlat =
      ((circuit.main input).operations n).constraints := by
  simp only [FormalCircuit.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]

@[circuit_norm] theorem constraints_toSubcircuit_generalFormalCircuit
    {F : Type} [FiniteField F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input : Var Input F) :
    FlatOperation.constraints (circuit.toSubcircuit n input).ops.toFlat =
      ((circuit.main input).operations n).constraints := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.constraints_toFlat]

@[circuit_norm] theorem lookups_toSubcircuit_formalAssertion
    {F : Type} [FiniteField F] {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (n : ℕ) (input : Var Input F) :
    FlatOperation.lookups (circuit.toSubcircuit n input).ops.toFlat =
      ((circuit.main input).operations n).lookups := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.lookups_toFlat]

@[circuit_norm] theorem lookups_toSubcircuit_formalCircuit
    {F : Type} [FiniteField F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (n : ℕ) (input : Var Input F) :
    FlatOperation.lookups (circuit.toSubcircuit n input).ops.toFlat =
      ((circuit.main input).operations n).lookups := by
  simp only [FormalCircuit.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.lookups_toFlat]

@[circuit_norm] theorem lookups_toSubcircuit_generalFormalCircuit
    {F : Type} [FiniteField F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (n : ℕ) (input : Var Input F) :
    FlatOperation.lookups (circuit.toSubcircuit n input).ops.toFlat =
      ((circuit.main input).operations n).lookups := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.lookups_toFlat]

@[circuit_norm] theorem constraints_flatten_operations
    {F : Type} [FiniteField F] (opss : List (Operations F)) :
    Operations.constraints opss.flatten = (opss.map Operations.constraints).flatten := by
  induction opss with
  | nil => rfl
  | cons ops opss ih =>
      simp only [List.flatten_cons, Operations.constraints_append, List.map_cons,
        List.flatten_cons, ih]

@[circuit_norm] theorem lookups_flatten_operations
    {F : Type} [FiniteField F] (opss : List (Operations F)) :
    Operations.lookups opss.flatten = (opss.map Operations.lookups).flatten := by
  induction opss with
  | nil => rfl
  | cons ops opss ih =>
      simp only [List.flatten_cons, Operations.lookups_append, List.map_cons,
        List.flatten_cons, ih]

@[circuit_norm] theorem constraints_forEach
    {F : Type} [FiniteField F] {α : Type} {m : ℕ} [Inhabited α]
    (xs : Vector α m) (body : α → Circuit F Unit) (constant : Circuit.ConstantLength body)
    (offset : ℕ) :
    ((Circuit.forEach xs body constant).operations offset).constraints =
      (List.ofFn fun (i : Fin m) =>
        ((body xs[i]).operations
          (offset + i * (body default).localLength)).constraints).flatten := by
  rw [Circuit.forEach.operations_eq, constraints_flatten_operations, List.map_ofFn]
  rfl

@[circuit_norm] theorem lookups_forEach
    {F : Type} [FiniteField F] {α : Type} {m : ℕ} [Inhabited α]
    (xs : Vector α m) (body : α → Circuit F Unit) (constant : Circuit.ConstantLength body)
    (offset : ℕ) :
    ((Circuit.forEach xs body constant).operations offset).lookups =
      (List.ofFn fun (i : Fin m) =>
        ((body xs[i]).operations
          (offset + i * (body default).localLength)).lookups).flatten := by
  rw [Circuit.forEach.operations_eq, lookups_flatten_operations, List.map_ofFn]
  rfl

/- These are normalization facts for the two canonical generated reader fragments shared by Rust chip
oracles. They are deliberately not reader-level faithfulness claims: consuming proofs use them only to
reassociate a complete chip assertion list before proving one `ChipFaithful` theorem. Keeping the
calculation here avoids cloning the same CPU/register-reader proof in every R-type chip. -/

namespace CanonicalReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem cpuStateAssertions
    (env : Environment (ZMod p)) (input : Var Readers.CPUState.Inputs (ZMod p))
    (offset : ℕ) (cols : Extracted.CPUState (ZMod p)) (nextPc : Vector (ZMod p) 3)
    (clkInc isReal : ZMod p)
    (hr : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.CPUState.asserts cols nextPc clkInc isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((Readers.CPUState.main input).operations offset)) := by
  simp [nativeAssertZeros, Readers.CPUState.main, Extracted.CPUState.asserts,
    circuit_norm]
  rw [hr]

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem equalityAssertions
    (env : Environment (ZMod p)) (x y : Expression (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((Gadgets.Equality.main (M := field) (x, y)).operations offset)) ↔
      Expression.eval env x = Expression.eval env y := by
  simp [nativeAssertZeros, Gadgets.Equality.main, circuit_norm]
  have hx : Expression.eval env (toElements (M := field) x)[0] = Expression.eval env x := rfl
  have hy : Expression.eval env (toElements (M := field) y)[0] = Expression.eval env y := rfl
  rw [hx, hy, sub_eq_zero]

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem registerWriteAssertions
    (env : Environment (ZMod p)) (input : Var Readers.RegisterWrite.Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((Readers.RegisterWrite.main input).operations offset)) ↔ True := by
  simp [nativeAssertZeros, Readers.RegisterWrite.main, circuit_norm]

set_option maxHeartbeats 1000000 in
theorem rTypeAssertions
    (env : Environment (ZMod p)) (input : Var Readers.RTypeReader.Inputs (ZMod p))
    (offset : ℕ) (clkHigh clkLow opcode isReal isTrusted : ZMod p)
    (pc : Vector (ZMod p) 3) (wv : Word (ZMod p)) (cols : Extracted.RTypeReader (ZMod p))
    (hreal : (ProvableStruct.eval env input).is_real = isReal)
    (htrusted : (ProvableStruct.eval env input).is_trusted = isTrusted)
    (hop : Expression.eval env input.cols.op_a_0 = cols.op_a_0)
    (hw0 : Expression.eval env input.wv0 = wv[0])
    (hw1 : Expression.eval env input.wv1 = wv[1])
    (hw2 : Expression.eval env input.wv2 = wv[2])
    (hw3 : Expression.eval env input.wv3 = wv[3])
    (htrust : isTrusted = isReal) :
    (List.Forall (· = 0)
        (Extracted.RTypeReader.asserts
          clkHigh clkLow pc opcode wv cols isReal isTrusted) ∧ cols.op_a_0 = 0) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env ((Readers.RTypeReader.main input).operations offset)) ∧
        cols.op_a_0 = 0) := by
  simp only [nativeAssertZeros, Readers.RTypeReader.main, circuit_norm]
  simp only [Readers.RegisterAccessCols.circuit, circuit_norm]
  simp only [Readers.RegisterAccessCols.main, circuit_norm]
  simp only [Readers.RegisterAccessTimestamp.circuit, circuit_norm]
  simp only [Readers.RegisterAccessTimestamp.main, circuit_norm]
  simp [Extracted.RTypeReader.asserts, Gadgets.Equality.main, circuit_norm]
  have heval (x : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) x)[0] = Expression.eval env x := rfl
  simp_rw [heval]
  simp only [eval_sub, Expression.eval]
  rw [hop, hreal, htrusted, hw0, hw1, hw2, hw3, htrust]
  intro hzero
  rw [hzero]
  simp

end CanonicalReader

open Classical in
/-- Interactions emitted on a channel other than the four SP1 buses. They remain part of the canonical
native access list, so a chip cannot make an accidental channel disappear by proving only four
per-channel comparisons. A well-formed SP1 chip proves this list empty structurally. -/
noncomputable def unexpectedInteractions {p : ℕ} [Fact p.Prime]
    (ops : Operations (ZMod p)) : List (AbstractInteraction (ZMod p)) :=
  ops.interactions.filter fun i =>
    decide (i.channel ≠ Channels.stateChannel.toRaw ∧
      i.channel ≠ Channels.byteChannel.toRaw ∧
      i.channel ≠ Channels.memoryChannel.toRaw ∧
      i.channel ≠ Channels.programChannel.toRaw)

/-- Canonical whole-chip interaction multiset emitted by the native circuit. The four known SP1 buses
are queried directly in State/Byte/Memory/Program order, matching Clean's channel abstraction; any
unexpected-channel tail is retained. Memory and Program are dualized because native channels pull facts
from providers where the current Rust AIR sends the corresponding entries; State and Byte already share
the same orientation. -/
noncomputable def nativeAccesses {p : ℕ} [Fact p.Prime]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p)) : LookupAccessList :=
  let state := (ops.interactionsWith Channels.stateChannel.toRaw).map
    (AbstractInteraction.toAccess env)
  let byte := (ops.interactionsWith Channels.byteChannel.toRaw).map
    (AbstractInteraction.toAccess env)
  let memory := ((ops.interactionsWith Channels.memoryChannel.toRaw).map
    (AbstractInteraction.toAccess env)).map LookupAccessList.negMult
  let program := ((ops.interactionsWith Channels.programChannel.toRaw).map
    (AbstractInteraction.toAccess env)).map LookupAccessList.negMult
  let unexpected := (unexpectedInteractions ops).map (AbstractInteraction.toAccess env)
  state ++ byte ++ memory ++ program ++ unexpected

namespace ChipOracle

variable {p : ℕ} [Fact p.Prime]
variable {NativeCols RustCols : TypeMap}

/-- The Rust whole-chip interaction oracle projected into the same trace-level vocabulary as the
native circuit. -/
def accesses (oracle : ChipOracle (ZMod p) NativeCols RustCols) (cols : NativeCols (ZMod p)) :
    LookupAccessList :=
  (oracle.nativeInteractions cols).map Extracted.Interaction.toAccess

/-- The Rust whole-chip interaction oracle evaluated directly on an adversarial Rust row. -/
def rustAccesses (oracle : ChipOracle (ZMod p) NativeCols RustCols) (cols : RustCols (ZMod p)) :
    LookupAccessList :=
  (oracle.interactions cols).map Extracted.Interaction.toAccess

@[simp] theorem accesses_deconfigure
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) (cols : RustCols (ZMod p)) :
    oracle.accesses (oracle.deconfigure cols) = oracle.rustAccesses cols := by
  simp [accesses, rustAccesses]

end ChipOracle

/-- A concrete Clean physical row reconstructed from a native whole-chip row.  The input and output
equalities make the column ordering explicit: the Rust/native row need not use Clean's input-first
physical layout. -/
structure NativeRowAssignment {F : Type} [FiniteField F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (cols : Output F)
    (data : ProverData F) where
  row : Array F
  input : Input F
  width_eq : row.size = (⟨circuit⟩ : Air.Flat.Component F).width
  rowInput_eq :
    (⟨circuit⟩ : Air.Flat.Component F).rowInput (Environment.fromArray row data) = input
  rowOutput_eq :
    ProvableType.eval (Environment.fromArray row data)
      ((circuit.main (⟨circuit⟩ : Air.Flat.Component F).rowInputVar).output
        (⟨circuit⟩ : Air.Flat.Component F).rowOffset) = cols

namespace NativeRowAssignment

variable {F : Type} [FiniteField F] {Input Output : TypeMap}
variable [ProvableType Input] [ProvableType Output]
variable {circuit : GeneralFormalCircuit F Input Output} {cols : Output F} {data : ProverData F}

/-- The verifier environment represented by a reconstructed physical row. -/
def environment (assignment : NativeRowAssignment circuit cols data) : Environment F :=
  Environment.fromArray assignment.row data

end NativeRowAssignment

/-- Constructive codec from a proof-oriented native row to Clean's input-first physical row. -/
structure ChipRowCodec {F : Type} [FiniteField F] (Input Output : TypeMap)
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) where
  assignment : ∀ cols data, NativeRowAssignment circuit cols data

/-- Canonical input-first physical row used by Clean flat components. -/
def inputFirstRow {F : Type} {Input : TypeMap} [ProvableType Input] {n : ℕ}
    (input : Input F) (locals : Vector F n) : Array F :=
  (toElements input ++ locals).toArray

@[simp] theorem inputFirstRow_size {F : Type} {Input : TypeMap} [ProvableType Input] {n : ℕ}
    (input : Input F) (locals : Vector F n) :
    (inputFirstRow input locals).size = size Input + n := by
  simp [inputFirstRow]

/-- The input variables at offset zero evaluate to the typed prefix of an input-first row. -/
theorem eval_inputFirstRow {F : Type} [FiniteField F]
    {Input : TypeMap} [ProvableType Input] (input : Input F)
    {n : ℕ} (locals : Vector F n) (data : ProverData F) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
      (varFromOffset Input 0 : Input (Expression F)) = input := by
  rw [ProvableType.eval_varFromOffset, ProvableType.fromElements_eq_iff]
  ext i hi
  rw [Vector.getElem_mapRange]
  simp only [Nat.zero_add]
  have hrow : i < (inputFirstRow input locals).size := by
    rw [inputFirstRow_size]
    omega
  rw [Array.getElem?_eq_getElem hrow]
  simp only [Option.getD_some, inputFirstRow]
  change (toElements input ++ locals)[i] = (toElements input)[i]
  rw [Vector.getElem_append_left hi]

/-- The prefix of an input-first physical row decodes to the supplied typed input. -/
theorem rowInput_inputFirstRow {F : Type} [FiniteField F]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (input : Input F)
    {n : ℕ} (locals : Vector F n) (data : ProverData F) :
    (⟨circuit⟩ : Air.Flat.Component F).rowInput
        (Environment.fromArray (inputFirstRow input locals) data) = input := by
  simp only [Air.Flat.Component.rowInput, valueFromOffset]
  rw [ProvableType.fromElements_eq_iff]
  ext i hi
  rw [Vector.getElem_mapRange]
  simp only [Nat.zero_add]
  have hrow : i < (inputFirstRow input locals).size := by
    rw [inputFirstRow_size]
    omega
  rw [Array.getElem?_eq_getElem hrow]
  simp only [Option.getD_some, inputFirstRow]
  change (toElements input ++ locals)[i] = (toElements input)[i]
  rw [Vector.getElem_append_left hi]

/-- Variables immediately after the typed input evaluate to the supplied local-witness suffix. -/
theorem eval_local_inputFirstRow {F : Type} [FiniteField F]
    {Input : TypeMap} [ProvableType Input] (input : Input F)
    {n : ℕ} (locals : Vector F n) (data : ProverData F) (i : ℕ) (hi : i < n) :
    Expression.eval (Environment.fromArray (inputFirstRow input locals) data)
        (var { index := size Input + i }) = locals[i] := by
  simp only [Expression.eval]
  have hrow : size Input + i < (inputFirstRow input locals).size := by
    rw [inputFirstRow_size]
    omega
  rw [Array.getElem?_eq_getElem hrow]
  simp only [Option.getD_some, inputFirstRow]
  change (toElements input ++ locals)[size Input + i] = locals[i]
  rw [Vector.getElem_append_right (by omega) (by omega)]
  congr
  omega

/-- A typed value flattened as a complete row decodes through the matching zero-offset variable map. -/
theorem eval_varFromOffset_typedRow {F : Type} [FiniteField F]
    {M : TypeMap} [ProvableType M] (value : M F) (data : ProverData F) :
    ProvableType.eval (Environment.fromArray (toElements value).toArray data)
      (varFromOffset M 0 : M (Expression F)) = value := by
  rw [← CircuitType.eval_expression, ProvableType.eval_varFromOffset,
    ProvableType.fromElements_eq_iff]
  ext i hi
  rw [Vector.getElem_mapRange]
  simp only [Nat.zero_add]
  have hrow : i < (toElements value).toArray.size := by simpa using hi
  rw [Array.getElem?_eq_getElem hrow]
  simp

/-- Output binding used by chip-faithfulness proofs. It is stated against the canonical `Circuit.output`,
not an `ElaboratedCircuit.output` projection: elaboration proves those equal, while the
faithfulness boundary should not depend on reduction of a selected typeclass instance. It remains
independent of witness generation—any verifier environment assigning the native result to `cols` is
in scope. -/
def BindsChipOutput {F : Type} [FiniteField F] {Input NativeCols : TypeMap}
    [ProvableStruct Input] [ProvableStruct NativeCols]
    (main : Input (Expression F) → Circuit F (NativeCols (Expression F)))
    (env : Environment F) (input : Input (Expression F)) (offset : ℕ)
    (cols : NativeCols F) : Prop :=
  ProvableStruct.eval env ((main input).output offset) = cols

namespace BindsChipOutput

/-- Transport a canonical circuit-output binding to a chosen elaborated output. Keeping the
`ElaboratedCircuit` value explicit avoids relying on typeclass-projection reduction in downstream
proofs; a chip may then normalize its literal output with Clean's struct-evaluation simproc. -/
theorem ofElaborated {F : Type} [FiniteField F] {Input NativeCols : TypeMap}
    [ProvableStruct Input] [ProvableStruct NativeCols]
    {main : Input (Expression F) → Circuit F (NativeCols (Expression F))}
    (elaborated : ElaboratedCircuit F Input NativeCols main)
    {env : Environment F} {input : Input (Expression F)} {offset : ℕ} {cols : NativeCols F}
    (hbind : BindsChipOutput main env input offset cols) :
    ProvableStruct.eval env (elaborated.output input offset) = cols := by
  rw [← elaborated.output_eq]
  exact hbind

end BindsChipOutput

namespace NativeRowAssignment

variable {F : Type} [FiniteField F] {Input Output : TypeMap}
variable [ProvableStruct Input] [ProvableStruct Output]
variable {circuit : GeneralFormalCircuit F Input Output} {cols : Output F} {data : ProverData F}

/-- A reconstructed component row binds the circuit's canonical output to the decoded native row. -/
theorem bindsOutput (assignment : NativeRowAssignment circuit cols data) :
    BindsChipOutput circuit.main assignment.environment
      (⟨circuit⟩ : Air.Flat.Component F).rowInputVar
      (⟨circuit⟩ : Air.Flat.Component F).rowOffset cols := by
  unfold BindsChipOutput environment
  rw [← ProvableStruct.eval_eq_eval]
  rw [CircuitType.eval_expression]
  exact assignment.rowOutput_eq

end NativeRowAssignment

/-- Convert the complete native assertion list into Clean's full constraint predicate when the chip
has no separate `Lookup` operations. SP1 byte/range accesses are channel interactions and therefore
remain covered by the interaction half of `ChipFaithful`. -/
theorem constraintsHold_iff_nativeAssertZeros {F : Type} [FiniteField F]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (env : Environment F)
    (lookupsEmpty : (⟨circuit⟩ : Air.Flat.Component F).operations.lookups = []) :
    (⟨circuit⟩ : Air.Flat.Component F).operations.ConstraintsHold env ↔
      List.Forall (· = 0)
        (nativeAssertZeros env (⟨circuit⟩ : Air.Flat.Component F).rowOperations) := by
  rw [Operations.ConstraintsHold, lookupsEmpty, Air.Flat.Component.constraints_eq]
  simp [nativeAssertZeros, List.forall_iff_forall_mem]

/-- `Component.operations` and `rowOperations` differ only in how the input variables are introduced;
their evaluated whole-chip access multisets are identical. -/
theorem nativeAccesses_component_eq_rowOperations {p : ℕ} [Fact p.Prime]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output) (env : Environment (ZMod p)) :
    nativeAccesses env (⟨circuit⟩ : Air.Flat.Component (ZMod p)).operations =
      nativeAccesses env (⟨circuit⟩ : Air.Flat.Component (ZMod p)).rowOperations := by
  simp only [nativeAccesses, unexpectedInteractions, Operations.interactionsWith,
    Air.Flat.Component.interactions_eq]

/-- Whole-chip faithfulness. Assertion lists need only be extensionally equivalent: the Lean chip may
use different local gadgets or redundant constraints. Interactions are compared as a multiset after
the project-wide bus-orientation convention in `nativeAccesses`. -/
structure ChipFaithful {p : ℕ} [Fact p.Prime]
    (Input NativeCols RustCols : TypeMap) [ProvableStruct Input] [ProvableStruct NativeCols]
    (circuit : GeneralFormalCircuit (ZMod p) Input NativeCols)
    (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) : Prop where
  constraints : ∀ rustCols data,
    let assignment := codec.assignment (oracle.deconfigure rustCols) data
    List.Forall (· = 0) (oracle.assertZeros rustCols) ↔
      (⟨circuit⟩ : Air.Flat.Component (ZMod p)).operations.ConstraintsHold
        assignment.environment
  interactions : ∀ rustCols data,
    let assignment := codec.assignment (oracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨circuit⟩ : Air.Flat.Component (ZMod p)).operations)
      (oracle.rustAccesses rustCols)

end SP1Clean.Faithful
