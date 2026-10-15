import SP1Clean.Proofs.Chips.LoadByteStaticChip.Witgen
import SP1Clean.Proofs.Chips.LoadByteStaticChip.FixedTable

/-! # Exact constraint and occurrence transport for the LoadByte replacement -/

namespace SP1Clean.LoadByteStaticChip

open Circuit
open LoadByteChip (Inputs Columns)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact (2 ^ 17 < p)] in
private theorem general_lookups {I O : TypeMap} [ProvableType I] [ProvableType O]
    (c : GeneralFormalCircuit (ZMod p) I O) (offset : ℕ) (input : Var I (ZMod p)) :
    FlatOperation.lookups (c.toSubcircuit offset input).ops.toFlat =
      ((c.main input).operations offset).lookups := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.lookups_toFlat]

omit [Fact (2 ^ 17 < p)] in
private theorem assertion_lookups {I : TypeMap} [ProvableType I]
    (c : FormalAssertion (ZMod p) I) (offset : ℕ) (input : Var I (ZMod p)) :
    FlatOperation.lookups (c.toSubcircuit offset input).ops.toFlat =
      ((c.main input).operations offset).lookups := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.lookups_toFlat]

omit [Fact (2 ^ 17 < p)] in
private theorem lookups_asserts (xs : List (Expression (ZMod p))) :
    Operations.lookups (xs.map Operation.assert) = [] := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, Operations.lookups, ih]

omit [Fact (2 ^ 17 < p)] in
private theorem lookups_asserts_ofFn {n : ℕ} (f : Fin n → Expression (ZMod p)) :
    Operations.lookups (List.ofFn (fun i => Operation.assert (f i))) = [] := by
  simpa only [List.map_ofFn, Function.comp_def] using lookups_asserts (List.ofFn f)

omit [Fact (2 ^ 17 < p)] in
private theorem equality_lookups {M : TypeMap} [ProvableType M]
    (input : Var M (ZMod p) × Var M (ZMod p)) (offset : ℕ) :
    ((Gadgets.Equality.main input).operations offset).lookups = [] := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm, lookups_asserts_ofFn]

private theorem perm_insert_three {α : Type} (a b c tail : List α) (x : α) :
    (a ++ (b ++ (c ++ x :: tail))).Perm (x :: (a ++ (b ++ (c ++ tail)))) := by
  simpa only [List.append_assoc] using
    (List.perm_middle (a := x) (l₁ := a ++ b ++ c) (l₂ := tail))

/-- Only this named occurrence is removed; equality of keys does not select occurrences. -/
def selectedRange (input : Var Inputs (ZMod p)) : AbstractInteraction (ZMod p) :=
  (byteChannel.pulledIf (input.is_lb + input.is_lbu)
    (⟨3, 0, input.selected_limb_low_byte,
      (input.selected_limb - input.selected_limb_low_byte) * Expression.const ((256 : ZMod p)⁻¹)⟩ :
      ByteRow (Expression (ZMod p)))).toRaw

/-- Every original arithmetic assertion, in its original order, is preserved. -/
theorem assertions_eq_original (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).constraints =
      ((LoadByteChip.main input).operations offset).constraints := rfl

/-- The old row has no fixed lookups; all its range checks are channel requests. -/
theorem original_lookups (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((LoadByteChip.main input).operations offset).lookups = [] := by
  simp only [LoadByteChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    AddressOperation.circuit, AddressOperation.main, AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main, Readers.ITypeReader.circuit,
    Readers.ITypeReader.main, Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    equality_lookups, general_lookups, assertion_lookups, circuit_norm]

/-- The two lookup occurrences use the upstream table, including zero-valued padding requests. -/
theorem lookups_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups =
      [{ table := Gadgets.ByteTable.toRaw,
         entry := #v[(input.is_lb + input.is_lbu) * input.selected_limb_low_byte] },
       { table := Gadgets.ByteTable.toRaw,
         entry := #v[(input.is_lb + input.is_lbu) *
           ((input.selected_limb - input.selected_limb_low_byte) *
             Expression.const ((256 : ZMod p)⁻¹))] }] := by
  simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
    AddressOperation.circuit, AddressOperation.main, AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main, Readers.ITypeReader.circuit,
    Readers.ITypeReader.main, Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    equality_lookups, general_lookups, assertion_lookups, circuit_norm]
  rfl

private theorem byte_lookup_contains (env : Environment (ZMod p)) (value : Expression (ZMod p)) :
    (Lookup.mk Gadgets.ByteTable.toRaw #v[value]).Contains env ↔ (env value).val < 256 := by
  simp only [Lookup.Contains, Table.toRaw, Vector.map_mk, List.map_toArray,
    List.map_cons, List.map_nil]
  exact fixedByte_contains_iff _ _

/-- Exact raw constraint transport: unchanged assertions plus the two authenticated byte checks. -/
theorem constraints_iff (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    ((main input).operations offset).ConstraintsHold env ↔
      ((LoadByteChip.main input).operations offset).ConstraintsHold env ∧
      (env ((input.is_lb + input.is_lbu) * input.selected_limb_low_byte)).val < 256 ∧
      (env ((input.is_lb + input.is_lbu) *
        ((input.selected_limb - input.selected_limb_low_byte) *
          Expression.const ((256 : ZMod p)⁻¹)))).val < 256 := by
  simp only [Operations.ConstraintsHold, assertions_eq_original, original_lookups, lookups_eq,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    byte_lookup_contains, false_implies, implies_true, and_true]

/-- The alternative preserves all legitimate inactive-row freedom, on arbitrary witness cells. -/
theorem inactive_constraints_iff (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (inactive : env (input.is_lb + input.is_lbu) = 0) :
    ((main input).operations offset).ConstraintsHold env ↔
      ((LoadByteChip.main input).operations offset).ConstraintsHold env := by
  rw [constraints_iff]
  have hz (v : Expression (ZMod p)) : env ((input.is_lb + input.is_lbu) * v) = 0 := by
    change env (input.is_lb + input.is_lbu) * env v = 0
    rw [inactive, zero_mul]
  simp only [hz, ZMod.val_zero]
  simp

/-- The original raw assertions force the activity gate to be binary. -/
theorem original_isReal_binary (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (holds : ((LoadByteChip.main input).operations offset).ConstraintsHold env) :
    env (input.is_lb + input.is_lbu) = 0 ∨ env (input.is_lb + input.is_lbu) = 1 := by
  have h := holds.1 ((input.is_lb + input.is_lbu) * ((input.is_lb + input.is_lbu) - 1))
    (by simp [LoadByteChip.main, circuit_norm])
  simp only [circuit_norm] at h ⊢
  simpa only [sub_eq_zero] using mul_eq_zero.mp h

/-- All old interaction occurrences remain, except the one selected-limb pair. -/
theorem interactions_perm (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (((LoadByteChip.main input).operations offset).interactions).Perm
      (selectedRange input :: ((main input).operations offset).interactions) := by
  simp only [main, LoadByteChip.main, selectedRange,
    Readers.CPUState.circuit, AddressOperation.circuit, Readers.MemoryAccess.circuit,
    Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit, circuit_norm]
  exact perm_insert_three _ _ _ _ _

end SP1Clean.LoadByteStaticChip
