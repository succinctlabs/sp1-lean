import SP1Clean.Proofs.Chips.LoadByteStaticChip.Complete
import SP1Clean.Proofs.Chips.LoadByteStaticChip.Transport
import SP1Clean.Proofs.Completeness.ProviderInteractions

/-! # Occurrence-preserving LoadByte replacement in an assembled ledger

The compared assemblies reserve one existing U8Range provider row per selected-limb request.
All residual tables, including other U8Range/MSB providers and readers with identical keys,
are retained literally. This is a dedicated-provider assembly transport, not a transformation
of an already aggregated canonical inventory. Removing rows decreases the raw interaction
count; the reverse construction would require its own larger capacity bound.

Generation data and evaluation data are explicit and independent. The constraint transport keeps
one evaluation environment fixed, including for arbitrary residual tables. Applying it to a changed
canonical inventory still requires transporting residual lookups to that inventory; this theorem
does not establish that agreement.
-/

namespace SP1Clean.Soundness.LoadByteStatic

open Air.Flat Circuit
open LoadByteChip (Inputs Columns isReal highByte)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The exact original selected-limb pull, even when its multiplicity is zero. -/
def selectedPull (input : Inputs (ZMod p)) : Interaction (ZMod p) :=
  byteChannel.pulledIfValue (isReal input)
    ⟨3, 0, input.selected_limb_low_byte, highByte input⟩

/-- One existing U8Range provider input for the selected occurrence. Inactive rows use valid
zero bytes, preserving arbitrary inactive consumer values without making provider rows invalid. -/
def selectedProviderInput (input : Inputs (ZMod p)) : ByteChip.U8Range.Inputs (ZMod p) :=
  ⟨isReal input * input.selected_limb_low_byte, isReal input * highByte input, isReal input⟩

/-- The provider's push retains a distinct occurrence even when another provider has the same key. -/
def selectedPush (input : Inputs (ZMod p)) : Interaction (ZMod p) :=
  byteChannel.pushedIfValue (isReal input)
    ⟨3, 0, isReal input * input.selected_limb_low_byte, isReal input * highByte input⟩

/-- The old consumer table uses the existing event/witness infrastructure. -/
def originalTable (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Air.Flat.Table (ZMod p) :=
  Air.Flat.Table.build LoadByteChip.component inputs data hint

/-- The replacement changes only the component, preserving the generated cells. -/
def replacementTable (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Air.Flat.Table (ZMod p) :=
  Air.Flat.Table.build LoadByteStaticChip.component inputs data hint

/-- The old assembly's dedicated provider rows; there is one physical row per input, including
padding. Aggregation is intentionally absent from both sides of this comparison. -/
def selectedProviderTable (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Air.Flat.Table (ZMod p) :=
  Air.Flat.Table.build ByteChip.U8Range.component (inputs.map selectedProviderInput) data hint

/-- The original assembled table list, with arbitrary shared residual tables. -/
def originalAssembly (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (residual : List (Air.Flat.Table (ZMod p))) :
    List (Air.Flat.Table (ZMod p)) :=
  originalTable inputs data hint :: selectedProviderTable inputs data hint :: residual

/-- The replacement leaves every residual table untouched. -/
def replacementAssembly (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (residual : List (Air.Flat.Table (ZMod p))) :
    List (Air.Flat.Table (ZMod p)) := replacementTable inputs data hint :: residual

omit [Fact (2 ^ 24 < p)] in
/-- The named syntactic occurrence evaluates to the exact semantic input pair. -/
theorem selectedRange_eval (input : Var Inputs (ZMod p)) (env : Environment (ZMod p)) :
    (LoadByteStaticChip.selectedRange input).eval env = selectedPull (Eval.eval env input) := by
  rw [LoadByteStaticChip.selectedRange, Channel.eval_pulledIf]
  simp only [selectedPull, isReal, highByte, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- The removed pull/provider pair has zero balance, including zero-multiplicity padding with
unrestricted original low/high values. No key-uniqueness assumption is used. -/
theorem selected_pair_balance (input : Inputs (ZMod p))
    (binary : isReal input = 0 ∨ isReal input = 1) (message : Array (ZMod p)) :
    balanceOf [selectedPull input, selectedPush input] message = 0 := by
  simp only [balanceOf_cons]
  change _ + (_ + 0) = 0
  rcases binary with h | h <;>
    simp only [selectedPull, selectedPush, Channel.pulledIfValue, Channel.pushedIfValue,
      h, zero_mul, one_mul, neg_zero] <;> split_ifs <;> simp

/-- The existing U8Range circuit really emits the dedicated push from its built physical row. -/
theorem providerRow_interactions (input : Inputs (ZMod p)) (data evaluationData : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ByteChip.U8Range.component.operations.interactionValues
      (Environment.fromArray
        (ByteChip.U8Range.component.buildRow (selectedProviderInput input) data hint) evaluationData) =
      [selectedPush input] := by
  trans ByteChip.U8Range.component.operations.interactionValues (Environment.fromArray
    (ByteChip.U8Range.component.buildRow (selectedProviderInput input) data hint) data)
  · exact Operations.interactionValues_congr rfl
  rw [Operations.interactionValues,
    interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
      Ledger.onlyChannel_U8Range, u8Range_interactionsWith_byte]
  unfold ByteChip.U8Range.component
  simp only [List.map_cons, List.map_nil]
  rw [← Channel.pushedIf, Channel.eval_pushedIf]
  have roweval (env : Environment (ZMod p)) (a b : Expression (ZMod p)) :
      eval env (⟨3, 0, a, b⟩ : ByteRow (Expression (ZMod p))) =
        (⟨3, 0, env a, env b⟩ : ByteRow (ZMod p)) := by
    simp only [circuit_norm]
  rw [roweval]
  simp only [ProvableType.eval_field]
  rw [eval_var_buildRow_input_get ({ circuit := ByteChip.U8Range.circuit } : Component (ZMod p))
      (selectedProviderInput input) data hint 0 (by change 0 < 3; omega),
    eval_var_buildRow_input_get ({ circuit := ByteChip.U8Range.circuit } : Component (ZMod p))
      (selectedProviderInput input) data hint 1 (by change 1 < 3; omega),
    eval_var_buildRow_input_get ({ circuit := ByteChip.U8Range.circuit } : Component (ZMod p))
      (selectedProviderInput input) data hint 2 (by change 2 < 3; omega)]
  simp only [selectedProviderInput, toElements, ProvableStruct.structToElements_eq,
    ProvableStruct.toComponents]
  simp only [components, ProvableStruct.componentsToElements]
  rfl

/-- The original physical consumer row is exactly the replacement row plus the named pull,
up to ordering. Every other occurrence (including zero multiplicities) is preserved. -/
theorem consumerRow_interactions_perm (input : Inputs (ZMod p)) (data evaluationData : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (LoadByteChip.component.operations.interactionValues
      (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData)).Perm
      (selectedPull input :: LoadByteStaticChip.component.operations.interactionValues
        (Environment.fromArray (LoadByteStaticChip.component.buildRow input data hint) evaluationData)) := by
  have same := LoadByteStaticChip.buildRow_eq_original input data hint
  change LoadByteStaticChip.component.buildRow input data hint =
    LoadByteChip.component.buildRow input data hint at same
  rw [same]
  simp only [Operations.interactionValues, Component.interactions_eq]
  have h := (LoadByteStaticChip.interactions_perm
    (varFromOffset (F := ZMod p) Inputs 0) (size Inputs)).map
      (AbstractInteraction.eval (Environment.fromArray
        (LoadByteChip.component.buildRow input data hint) evaluationData))
  rw [List.map_cons, selectedRange_eval] at h
  have input_eq : Eval.eval
      (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData)
      (varFromOffset (F := ZMod p) Inputs 0) = input := by
    rw [eval_varFromOffset_valueFromOffset]
    exact Component.rowInput_buildRow LoadByteChip.component input data evaluationData hint
  rw [input_eq] at h
  exact h

/-- The dedicated provider table emits exactly one named push for every input row. -/
theorem providerTable_interactions (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (selectedProviderTable inputs data hint).interactions evaluationData = inputs.map selectedPush := by
  calc
    _ = (inputs.map selectedProviderInput).flatMap
        (fun input : ByteChip.U8Range.Inputs (ZMod p) =>
          ByteChip.U8Range.component.operations.interactionValues (Environment.fromArray
            (ByteChip.U8Range.component.buildRow input data hint) evaluationData)) :=
      Air.Flat.Table.build_interactionValues ByteChip.U8Range.component _ data hint _ evaluationData
    _ = inputs.flatMap (fun input => ByteChip.U8Range.component.operations.interactionValues
        (Environment.fromArray (ByteChip.U8Range.component.buildRow
          (selectedProviderInput input) data hint) evaluationData)) := List.flatMap_map ..
    _ = inputs.map selectedPush := by
      simp only [providerRow_interactions]
      exact List.map_eq_flatMap.symm

/-- Table-wide occurrence preservation, without matching or erasing by key. -/
theorem consumerTable_interactions_perm (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ((originalTable inputs data hint).interactions evaluationData).Perm
      (inputs.map selectedPull ++ (replacementTable inputs data hint).interactions evaluationData) := by
  have original : (originalTable inputs data hint).interactions evaluationData =
      inputs.flatMap (fun input : Inputs (ZMod p) =>
        LoadByteChip.component.operations.interactionValues
          (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData)) :=
    Air.Flat.Table.build_interactionValues LoadByteChip.component inputs data hint _ evaluationData
  have replacement : (replacementTable inputs data hint).interactions evaluationData =
      inputs.flatMap (fun input : Inputs (ZMod p) =>
        LoadByteStaticChip.component.operations.interactionValues (Environment.fromArray
          (LoadByteStaticChip.component.buildRow input data hint) evaluationData)) :=
    Air.Flat.Table.build_interactionValues LoadByteStaticChip.component inputs data hint _ evaluationData
  rw [original, replacement]
  have rowPerm := List.Perm.flatMap_left inputs
    (fun input _ => consumerRow_interactions_perm input data evaluationData hint)
  exact rowPerm.trans (List.map_append_flatMap_perm inputs selectedPull _).symm

/-- Soundness of the actual selected-provider row authenticates both new lookup entries. -/
theorem selectedProvider_bounds (input : Inputs (ZMod p)) (data evaluationData : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (holds : ByteChip.U8Range.component.operations.ConstraintsHold
      (Environment.fromArray
        (ByteChip.U8Range.component.buildRow (selectedProviderInput input) data hint) evaluationData)) :
    (isReal input * input.selected_limb_low_byte).val < 256 ∧
      (isReal input * highByte input).val < 256 := by
  have guarantees : ByteChip.U8Range.component.operations.FullGuarantees
      (Environment.fromArray
        (ByteChip.U8Range.component.buildRow (selectedProviderInput input) data hint) evaluationData) := by
    rw [Operations.FullGuarantees,
      interactions_eq_interactionsWith_of_onlyChannel _ byteChannel.toRaw
        Ledger.onlyChannel_U8Range, u8Range_interactionsWith_byte]
    simp [AbstractInteraction.Guarantees, ChannelInteraction.toRaw, pushedIf]
  have spec := (Component.weakSoundness (by trivial) holds guarantees).1
  change (ByteChip.U8Range.component.rowInput _).b.val < 256 ∧
    (ByteChip.U8Range.component.rowInput _).c.val < 256 at spec
  unfold ByteChip.U8Range.component at spec
  rw [Component.rowInput_buildRow] at spec
  exact spec

/-- The activity gate is derived from the original physical consumer's assertions. -/
theorem consumerRow_binary (input : Inputs (ZMod p)) (data evaluationData : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (holds : LoadByteChip.component.operations.ConstraintsHold
      (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData)) :
    isReal input = 0 ∨ isReal input = 1 := by
  rw [Component.constraintsHold_iff] at holds
  change ((LoadByteChip.main (varFromOffset (F := ZMod p) Inputs 0)).operations
    (size Inputs)).ConstraintsHold _ at holds
  have binary := LoadByteStaticChip.original_isReal_binary _ _ _ holds
  have evalInput : Eval.eval
      (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData)
      (varFromOffset (F := ZMod p) Inputs 0) = input := by
    rw [eval_varFromOffset_valueFromOffset]
    exact Component.rowInput_buildRow LoadByteChip.component input data evaluationData hint
  have gate := congrArg isReal evalInput
  simp only [isReal, circuit_norm] at gate
  simpa only [circuit_norm, gate, isReal] using binary

/-- The replacement preserves raw acceptance of a built consumer when the corresponding actual
provider row is constrained. Arbitrary inputs and inactive out-of-range values are allowed. -/
theorem consumerRow_constraints (input : Inputs (ZMod p)) (data evaluationData : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (consumer : LoadByteChip.component.operations.ConstraintsHold
      (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData))
    (provider : ByteChip.U8Range.component.operations.ConstraintsHold
      (Environment.fromArray
        (ByteChip.U8Range.component.buildRow (selectedProviderInput input) data hint) evaluationData)) :
    LoadByteStaticChip.component.operations.ConstraintsHold
      (Environment.fromArray (LoadByteStaticChip.component.buildRow input data hint) evaluationData) := by
  have same := LoadByteStaticChip.buildRow_eq_original input data hint
  change LoadByteStaticChip.component.buildRow input data hint =
    LoadByteChip.component.buildRow input data hint at same
  rw [same, Component.constraintsHold_iff]
  change ((LoadByteStaticChip.main (varFromOffset (F := ZMod p) Inputs 0)).operations
    (size Inputs)).ConstraintsHold _
  rw [LoadByteStaticChip.constraints_iff]
  refine ⟨(Component.constraintsHold_iff _).mp consumer, ?_⟩
  have bounds := selectedProvider_bounds input data evaluationData hint provider
  have evalInput : Eval.eval
      (Environment.fromArray (LoadByteChip.component.buildRow input data hint) evaluationData)
      (varFromOffset (F := ZMod p) Inputs 0) = input := by
    rw [eval_varFromOffset_valueFromOffset]
    exact Component.rowInput_buildRow LoadByteChip.component input data evaluationData hint
  have low := congrArg (fun i : Inputs (ZMod p) => isReal i * i.selected_limb_low_byte) evalInput
  have high := congrArg (fun i : Inputs (ZMod p) => isReal i * highByte i) evalInput
  simp only [isReal, highByte, circuit_norm] at low high ⊢
  rwa [low, high]

/-- Table constraints at the chosen evaluation data are preserved without semantic or
honest-generator premises. -/
theorem replacementTable_constraints (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (consumer : (originalTable inputs data hint).Constraints evaluationData)
    (provider : (selectedProviderTable inputs data hint).Constraints evaluationData) :
    (replacementTable inputs data hint).Constraints evaluationData := by
  intro row member
  obtain ⟨input, inputMem, rfl⟩ := List.mem_map.mp member
  exact consumerRow_constraints input data evaluationData hint
    (consumer _ (List.mem_map.mpr ⟨input, inputMem, rfl⟩))
    (provider _ (List.mem_map.mpr
      ⟨selectedProviderInput input, List.mem_map.mpr ⟨input, inputMem, rfl⟩, rfl⟩))

/-- The actual all-channel ledger decomposes into exactly the removed occurrences plus the new
ledger. Residual tables, including duplicate keys, are literal common suffixes. -/
theorem assembly_interactions_perm (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (residual : List (Air.Flat.Table (ZMod p))) :
    ((originalAssembly inputs data hint residual).flatMap
      (fun table => table.interactions evaluationData)).Perm
      ((inputs.map selectedPull ++ inputs.map selectedPush) ++
        (replacementAssembly inputs data hint residual).flatMap
          (fun table => table.interactions evaluationData)) := by
  simp only [originalAssembly, replacementAssembly, List.flatMap_cons,
    providerTable_interactions]
  apply ((consumerTable_interactions_perm inputs data evaluationData hint).append_right _).trans
  simp only [List.append_assoc]
  simpa only [List.append_assoc] using
    List.Perm.append_left (inputs.map selectedPull)
      ((List.perm_append_comm (l₁ := (replacementTable inputs data hint).interactions evaluationData)
        (l₂ := inputs.map selectedPush)).append_right
          (residual.flatMap (fun table => table.interactions evaluationData)))

/-- Exactly two physical interaction occurrences disappear per source row, including padding. -/
theorem assembly_raw_count (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (residual : List (Air.Flat.Table (ZMod p))) :
    ((originalAssembly inputs data hint residual).flatMap
      (fun table => table.interactions evaluationData)).length =
      2 * inputs.length +
        ((replacementAssembly inputs data hint residual).flatMap
          (fun table => table.interactions evaluationData)).length := by
  have h := (assembly_interactions_perm inputs data evaluationData hint residual).length_eq
  simp only [List.length_append, List.length_map] at h
  omega

omit [Fact (2 ^ 24 < p)] in
open Classical in
private theorem removed_balance (inputs : List (Inputs (ZMod p)))
    (binary : ∀ input ∈ inputs, isReal input = 0 ∨ isReal input = 1)
    (channel : RawChannel (ZMod p)) (message : Array (ZMod p)) :
    balanceOf ((inputs.map selectedPull ++ inputs.map selectedPush).filter
      (fun i => decide (i.channel = channel))) message = 0 := by
  have perm := (List.map_append_flatMap_perm inputs selectedPull
    (fun input => [selectedPush input])).filter (fun i => decide (i.channel = channel))
  simp only [← List.map_eq_flatMap] at perm
  rw [balanceOf_perm perm]
  clear perm
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
    simp only [List.flatMap_cons, List.filter_append, balanceOf_append]
    rw [ih (fun i hi => binary i (List.mem_cons_of_mem input hi)), add_zero]
    by_cases same : byteChannel.toRaw = channel
    · simpa only [List.filter_cons, selectedPull, selectedPush,
        Channel.pulledIfValue, Channel.pushedIfValue, same, decide_true, List.filter_nil,
        Bool.true_eq, ite_true] using selected_pair_balance input
          (binary input (List.mem_cons_self)) message
    · simp [selectedPull, selectedPush, Channel.pulledIfValue, Channel.pushedIfValue, same,
        balanceOf]

/-- Complete per-channel balance and its raw-count bound transport from old to new. The reverse
construction is deliberately not claimed: it may need a larger admissible interaction budget. -/
theorem assembly_balanced (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (residual : List (Air.Flat.Table (ZMod p)))
    (consumer : (originalTable inputs data hint).Constraints evaluationData)
    (balanced : ∀ channel : RawChannel (ZMod p), BalancedInteractions
      ((originalAssembly inputs data hint residual).flatMap
        (fun t => t.interactionsWith evaluationData channel))) :
    ∀ channel : RawChannel (ZMod p), BalancedInteractions
      ((replacementAssembly inputs data hint residual).flatMap
        (fun t => t.interactionsWith evaluationData channel)) := by
  classical
  have binary : ∀ input ∈ inputs, isReal input = 0 ∨ isReal input = 1 := by
    intro input mem
    exact consumerRow_binary input data evaluationData hint
      (consumer _ (List.mem_map.mpr ⟨input, mem, rfl⟩))
  intro channel
  have perm := (assembly_interactions_perm inputs data evaluationData hint residual).filter
    (fun i => decide (i.channel = channel))
  simp only [List.filter_append, List.filter_flatMap,
    ← Air.Flat.Table.interactionsWith_eq_filter] at perm
  have old := balancedInteractions_of_perm (balanced channel) perm
  refine ⟨?_, ?_⟩
  · have length := old.1
    simp only [List.length_append] at length
    rcases length with length | characteristicZero
    · exact Or.inl (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) length)
    · exact Or.inr characteristicZero
  · intro message
    have eq := old.2 message
    rw [balanceOf_append, ← List.filter_append,
      removed_balance inputs binary channel message, zero_add] at eq
    exact eq

/-- At fixed evaluation data, every old table's raw constraints and every old channel's bounded
balance suffice for the replacement. Canonical-data agreement is a separate obligation. -/
theorem assembly_acceptance (inputs : List (Inputs (ZMod p)))
    (data evaluationData : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (residual : List (Air.Flat.Table (ZMod p)))
    (constraints : ∀ table ∈ originalAssembly inputs data hint residual, table.Constraints evaluationData)
    (balanced : ∀ channel : RawChannel (ZMod p), BalancedInteractions
      ((originalAssembly inputs data hint residual).flatMap
        (fun t => t.interactionsWith evaluationData channel))) :
    (∀ table ∈ replacementAssembly inputs data hint residual, table.Constraints evaluationData) ∧
      (∀ channel : RawChannel (ZMod p), BalancedInteractions
        ((replacementAssembly inputs data hint residual).flatMap
          (fun t => t.interactionsWith evaluationData channel))) := by
  have consumer := constraints _ (List.mem_cons_self)
  have provider := constraints _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨?_, assembly_balanced inputs data evaluationData hint residual consumer balanced⟩
  intro table mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact replacementTable_constraints inputs data evaluationData hint consumer provider
  · exact constraints table (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))

end SP1Clean.Soundness.LoadByteStatic
