import SP1Clean.FormalModel.Contracts.InitialMemory
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Native.Operations.InitialMemoryLookup.Witness
import ToClean.Air.StaticProvider

/-! # Address-based initial-memory byte reads

The circuit accepts one address word and returns its authenticated byte. Clean's typed witness
IR selects the fixed interval and constructs both comparison rows internally. Completeness needs
only the semantic address bound; callers supply no interval or comparison columns.
-/

namespace SP1Clean.InitialMemoryLookup

open Circuit SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The semantic domain of a byte read. -/
def ProverAssumptions (limit : ℕ) (address : Word (ZMod p)) : Prop :=
  Word.isU64 address ∧ Word.toNat address < limit

/-- Source and target intervals use separate fixed-column membership channels. -/
def membership (memory : ByteMemory) (limit : ℕ) (name : String) :
    StaticTable (ZMod p) MemoryIntervalRow :=
  { memory.fixedTable limit with name := name }

omit [Fact (2 ^ 17 < p)] in
private theorem compare_lower {address lower : Word (ZMod p)}
    {cols : Circuits.Types.LtOperationUnsigned (ZMod p)}
    (spec : LtOperationUnsigned.Spec ⟨address, lower, cols, 1⟩)
    (zero : cols.u16_compare_operation.bit = 0) : Word.toNat lower ≤ Word.toNat address := by
  have equal := (LtOperationUnsigned.result_semantic spec rfl).1
  change cols.u16_compare_operation.bit = if Word.toNat address < Word.toNat lower then 1 else 0 at equal
  rw [zero] at equal
  split at equal
  · exact False.elim (zero_ne_one equal)
  · omega

omit [Fact (2 ^ 17 < p)] in
private theorem compare_upper {address upper : Word (ZMod p)}
    {cols : Circuits.Types.LtOperationUnsigned (ZMod p)}
    (spec : LtOperationUnsigned.Spec ⟨address, upper, cols, 1⟩)
    (one : cols.u16_compare_operation.bit - 1 = 0) : Word.toNat address < Word.toNat upper := by
  have equal := (LtOperationUnsigned.result_semantic spec rfl).1
  change cols.u16_compare_operation.bit = if Word.toNat address < Word.toNat upper then 1 else 0 at equal
  rw [sub_eq_zero.mp one] at equal
  split at equal
  · assumption
  · exact False.elim (one_ne_zero equal)

/-- Select and authenticate a fixed interval, then return its byte. -/
def main (memory : ByteMemory) (limit : ℕ) (address : Var Word (ZMod p))
    (tableName : String := "sp1.native.initial_memory") : Circuit (ZMod p) (Expression (ZMod p)) := do
  let interval ← witness (var := Var MemoryIntervalRow)
    (intervalFE memory limit (address.map Witgen.FExpr.expr))
  (membership memory limit tableName).channel.pull ⟨interval, 1⟩
  assertion WordRangeCheck.circuit address
  let lower ← witness (var := Var Circuits.Types.LtOperationUnsigned)
    (comparisonFE (address.map Witgen.FExpr.expr) (interval.lower.map Witgen.FExpr.expr))
  assertion LtOperationUnsigned.circuit ⟨address, interval.lower, lower, 1⟩
  assertZero lower.u16_compare_operation.bit
  let upper ← witness (var := Var Circuits.Types.LtOperationUnsigned)
    (comparisonFE (address.map Witgen.FExpr.expr) (interval.upper.map Witgen.FExpr.expr))
  assertion LtOperationUnsigned.circuit ⟨address, interval.upper, upper, 1⟩
  assertZero (upper.u16_compare_operation.bit - 1)
  return interval.value

@[local circuit_norm] private theorem range_guarantees :
    (WordRangeCheck.circuit (p := p)).channelsWithGuarantees = [] := rfl

@[local circuit_norm] private theorem range_requirements :
    (WordRangeCheck.circuit (p := p)).channelsWithRequirements = [] := rfl

@[local circuit_norm] private theorem compare_guarantees :
    (LtOperationUnsigned.circuit (p := p)).channelsWithGuarantees =
      [SP1Clean.Channels.byteChannel.toRaw] := rfl

instance elaborated (memory : ByteMemory) (limit : ℕ) (tableName : String) :
    ElaboratedCircuit (ZMod p) Word field (main memory limit (tableName := tableName)) where
  localLength _ := 89
  output _ offset := (varFromOffset MemoryIntervalRow offset : Var MemoryIntervalRow (ZMod p)).value
  channelsWithGuarantees :=
    [(membership memory limit tableName).channel.toRaw, SP1Clean.Channels.byteChannel.toRaw]

/-- Sound and complete byte read with an explicit fixed-table identity. -/
def circuitNamed (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64)
    (tableName : String) : GeneralFormalCircuit (ZMod p) Word field where
  main := main memory limit (tableName := tableName)
  elaborated := elaborated memory limit tableName
  channelsWithRequirements := []
  Spec input output _ := Spec memory limit input output
  ProverAssumptions input _ _ := ProverAssumptions limit input
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      membership, StaticTable.channel]
    obtain ⟨member, addressBound, lowerSpec, lowerZero, upperSpec, upperOne⟩ := h_holds
    have ranges := memory.fixedTable_sound limit limitBound _ member
    have lower := lowerSpec ⟨fun _ => ⟨addressBound, ranges.1⟩, Or.inr rfl⟩
    have upper := upperSpec ⟨fun _ => ⟨addressBound, ranges.2.1⟩, Or.inr rfl⟩
    have inside := And.intro (compare_lower lower lowerZero) (compare_upper upper upperOne)
    exact ⟨addressBound, memory.fixedTable_read limit limitBound _ member _ inside⟩
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      ProverAssumptions, membership, StaticTable.channel]
    have inputEval (i : ℕ) (hi : i < 4) :
        (input_var.map Witgen.FExpr.expr)[i].eval { env := env } = input[i] := by
      simpa only [Vector.getElem_map, Witgen.FExpr.eval] using
        congrArg (fun word : Word (ZMod p) => word[i]) h_input
    obtain ⟨interval, found⟩ := Option.isSome_iff_exists.mp
      ((memory.intervalAt?_isSome_iff limit (Word.toNat input)).mpr h_assumptions.2)
    have selection := memory.intervalAt?_sound limit (Word.toNat input) interval found
    have selected := h_env.1.trans
      (intervalFE_eval { env := env } memory limit limitBound _ input inputEval h_assumptions.1
        interval found)
    have lowerEq := congrArg MemoryIntervalRow.lower selected
    have upperEq := congrArg MemoryIntervalRow.upper selected
    dsimp only at lowerEq upperEq
    have lowerWitness := h_env.2.1.trans
      (comparisonFE_eval { env := env } _ _ input (interval.encode (p := p)).lower inputEval
        (by intro i hi; simpa only [Vector.getElem_map, Witgen.FExpr.eval] using
          congrArg (fun word : Word (ZMod p) => word[i]) lowerEq))
    have upperWitness := h_env.2.2.trans
      (comparisonFE_eval { env := env } _ _ input (interval.encode (p := p)).upper inputEval
        (by intro i hi; simpa only [Vector.getElem_map, Witgen.FExpr.eval] using
          congrArg (fun word : Word (ZMod p) => word[i]) upperEq))
    have lowerBit := congrArg (fun cols : Circuits.Types.LtOperationUnsigned (ZMod p) =>
      cols.u16_compare_operation.bit) lowerWitness
    have upperBit := congrArg (fun cols : Circuits.Types.LtOperationUnsigned (ZMod p) =>
      cols.u16_compare_operation.bit) upperWitness
    dsimp only at lowerBit upperBit
    rw [selected, lowerEq, upperEq, lowerWitness, upperWitness, lowerBit, upperBit]
    have member := (memory.fixedTable_spec limit (interval.encode (p := p))).mpr
      ⟨interval, selection.1, rfl⟩
    have ranges := memory.fixedTable_sound limit limitBound _ member
    have endpoints := memory.intervals_bounds limit interval selection.1
    have encoding := interval.encode_endpoints (p := p) (by omega) (by omega)
    have lowerLe : Word.toNat (interval.encode (p := p)).lower ≤ Word.toNat input := by
      rw [encoding.1]
      exact selection.2.1.1
    have upperLt : Word.toNat input < Word.toNat (interval.encode (p := p)).upper := by
      rw [encoding.2]
      exact selection.2.1.2
    have lowerSpec := LtOperationUnsigned.spec_populate h_assumptions.1 ranges.1
    have upperSpec := LtOperationUnsigned.spec_populate h_assumptions.1 ranges.2.1
    have lowerResult := (LtOperationUnsigned.result_semantic lowerSpec rfl).1
    have upperResult := (LtOperationUnsigned.result_semantic upperSpec rfl).1
    refine ⟨member, h_assumptions.1,
      ⟨⟨fun _ => ⟨h_assumptions.1, ranges.1⟩, Or.inr rfl⟩, lowerSpec⟩, ?_,
      ⟨⟨fun _ => ⟨h_assumptions.1, ranges.2.1⟩, Or.inr rfl⟩, upperSpec⟩, ?_⟩
    · simpa only [if_neg (Nat.not_lt.mpr lowerLe)] using lowerResult
    · rw [upperResult, if_pos upperLt, sub_self]

@[circuit_norm ↓, explicit_circuit_norm] theorem circuitNamed_elaborated (memory : ByteMemory)
    (limit : ℕ) (limitBound : limit < 2 ^ 64) (tableName : String) :
    (circuitNamed (p := p) memory limit limitBound tableName).elaborated =
      elaborated memory limit tableName := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuit_localLength (memory : ByteMemory) (limit : ℕ)
    (bound : limit < 2 ^ 64) (input : Var Word (ZMod p))
    (tableName : String := "sp1.native.initial_memory") :
    (circuitNamed memory limit bound tableName).localLength input = 89 := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuit_guarantees (memory : ByteMemory) (limit : ℕ)
    (bound : limit < 2 ^ 64) (tableName : String := "sp1.native.initial_memory") :
    (circuitNamed (p := p) memory limit bound tableName).channelsWithGuarantees =
      [(membership memory limit tableName).channel.toRaw, SP1Clean.Channels.byteChannel.toRaw] := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuit_requirements (memory : ByteMemory) (limit : ℕ)
    (bound : limit < 2 ^ 64) (tableName : String := "sp1.native.initial_memory") :
    (circuitNamed (p := p) memory limit bound tableName).channelsWithRequirements = [] := rfl

/-- Source-memory specialization of the named byte read. -/
abbrev circuit (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64) :=
  circuitNamed (p := p) memory limit limitBound "sp1.native.initial_memory"

/-- Interval authentication is supplied by the fixed-column membership channel. -/
theorem main_lookups (memory : ByteMemory) (limit : ℕ)
    (input : Var Word (ZMod p)) (name : String) (offset : ℕ) :
    ((main memory limit input name).operations offset).lookups = [] := by
  simp [main, WordRangeCheck.circuit, LtOperationUnsigned.circuit,
    LtOperationUnsigned.main, U16CompareOperation.circuit, U16CompareOperation.main,
    Gadgets.Equality.main, circuit_norm]

/-- Byte reads have no legacy lookups. -/
@[circuit_norm] theorem main_lookupNames (memory : ByteMemory) (limit : ℕ)
    (input : Var Word (ZMod p)) (name : String) (offset : ℕ) :
    ((main memory limit input name).operations offset).lookups.map (·.table.name) = [] := by
  rw [main_lookups]
  rfl

end SP1Clean.InitialMemoryLookup
