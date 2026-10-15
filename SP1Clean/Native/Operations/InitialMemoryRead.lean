import SP1Clean.FormalModel.Contracts.InitialMemoryRead
import SP1Clean.Native.Operations.InitialMemoryLookup
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Math.EvalVec
import ToClean.Circuit.WitnessCombinator

/-! # Address-based initial-memory word reads

The first byte is read directly. Seven witnessed additions locate the remaining bytes, each
authenticated by the bundled byte-read circuit. Callers supply only the base address; the
complete eight-byte footprint is the semantic completeness condition.
-/

namespace SP1Clean.InitialMemoryRead

open Circuit SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private def offset (index : Fin 7) : Word (ZMod p) :=
  bitVecToWord (BitVec.ofNat 64 (index.val + 1))

/-- The semantic domain of a complete word read. -/
def ProverAssumptions (address : Word (ZMod p)) : Prop :=
  Word.isU64 address ∧ Word.toNat address + 8 ≤ 2 ^ 48

/-- Encode a semantic address exactly when its full word lies within native memory. -/
def populate? (address : ℕ) : Option (Word (ZMod p)) :=
  if address + 8 ≤ 2 ^ 48 then some (bitVecToWord (BitVec.ofNat 64 address)) else none

/-- Successful encoding preserves the address and supplies the semantic completeness condition. -/
theorem populate?_sound (address : ℕ) (input : Word (ZMod p))
    (found : populate? address = some input) :
    ProverAssumptions input ∧ Word.toNat input = address := by
  unfold populate? at found
  split at found
  next footprint =>
    cases Option.some.inj found
    have encoded : Word.toNat (bitVecToWord (BitVec.ofNat 64 address) : Word (ZMod p)) = address := by
      rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨⟨isU64_bitVecToWord _, by rw [encoded]; exact footprint⟩, encoded⟩
  next invalid => contradiction

omit [Fact (2 ^ 17 < p)] in
/-- Encoding accepts exactly the semantic eight-byte footprint bound. -/
theorem populate?_isSome_iff (address : ℕ) :
    (populate? (p := p) address).isSome = true ↔ address + 8 ≤ 2 ^ 48 := by
  unfold populate?
  split <;> simp_all

omit [Fact (2 ^ 17 < p)] in
private theorem address_offset {base query : Word (ZMod p)} (index : Fin 8)
    (baseBound : Word.isU64 base) (baseWindow : Word.toNat base < 2 ^ 48)
    (queryBound : Word.isU64 query)
    (equal : Word.toBitVec64 query = Word.toBitVec64 base + BitVec.ofNat 64 index.val) :
    Word.toNat query = Word.toNat base + index.val := by
  have indexBound : index.val < 2 ^ 64 := by have := index.isLt; omega
  rw [← Word.toBitVec64_toNat queryBound, equal, BitVec.toNat_add,
    Word.toBitVec64_toNat baseBound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound,
    Nat.mod_eq_of_lt (by have := index.isLt; omega)]

private theorem read_of_bytes (memory : ByteMemory) (address : Word (ZMod p))
    (bytes : Vector (ZMod p) 8) (queries : Fin 8 → Word (ZMod p))
    (base : queries 0 = address)
    (reads : ∀ index : Fin 8, InitialMemoryLookup.Spec memory (2 ^ 48) (queries index) bytes[index.val])
    (addresses : ∀ index : Fin 8, Word.toBitVec64 (queries index) =
      Word.toBitVec64 address + BitVec.ofNat 64 index.val) :
    Spec memory address (Word.ofBytes bytes) := by
  have first : InitialMemoryLookup.Spec memory (2 ^ 48) address bytes[0] := base ▸ reads 0
  have positions (index : Fin 8) := address_offset index first.1 first.2.1
    (reads index).1 (addresses index)
  have values : bytes =
      (memory.wordBytes (Word.toNat address)).map (fun byte => (byte.toNat : ZMod p)) := by
    ext index bound
    simp only [Vector.getElem_map, ByteMemory.wordBytes, Vector.getElem_ofFn]
    exact ((reads ⟨index, bound⟩).2.2).trans
      (congrArg (fun address => ((memory.read address).toNat : ZMod p)) (positions ⟨index, bound⟩))
  refine ⟨first.1, ?_, ?_, ?_⟩
  · have last : Word.toNat address + 7 < 2 ^ 48 :=
      (positions ⟨7, by decide⟩) ▸ (reads ⟨7, by decide⟩).2.1
    omega
  · rw [values]
    exact Word.ofBytes_isU64 _
  · rw [values, Word.toBitVec64_ofBytes]
    rfl

omit [Fact (2 ^ 17 < p)] in
private theorem eval_word (env : Environment (ZMod p)) (bytes : Vector (Expression (ZMod p)) 8) :
    (Word.ofBytes bytes).map (Expression.eval env) =
      Word.ofBytes (bytes.map (Expression.eval env)) := by
  ext index bound
  interval_cases index <;> simp only [Word.ofBytes, circuit_norm]

/-- Authenticate the eight bytes at the supplied base address and pack their little-endian word. -/
def main (memory : ByteMemory) (address : Var Word (ZMod p))
    (tableName : String := "sp1.native.initial_memory") : Circuit (ZMod p) (Var Word (ZMod p)) := do
  let first ← InitialMemoryLookup.circuitNamed memory (2 ^ 48) (by norm_num) tableName address
  let rest ← Circuit.mapFinRange 7 fun index => do
    let query ← witnessVectorIR 4 (AddOperation.populateIR address (const (offset index)))
    assertion AddOperation.circuit ⟨address, const (offset index), ⟨query⟩, 1⟩
    InitialMemoryLookup.circuitNamed memory (2 ^ 48) (by norm_num) tableName query
  return Word.ofBytes (#v[first] ++ rest)

@[local circuit_norm] private theorem add_guarantees :
    (AddOperation.circuit (p := p)).channelsWithGuarantees =
      List.replicate 4 SP1Clean.Channels.byteChannel.toRaw := rfl

instance elaborated (memory : ByteMemory) (tableName : String) :
    ElaboratedCircuit (ZMod p) Word Word (main memory (tableName := tableName)) := by
  elaborate_circuit

/-- Sound and complete word read with an explicit fixed-table identity. -/
def circuitNamed (memory : ByteMemory) (tableName : String) : GeneralFormalCircuit (ZMod p) Word Word where
  main := main memory (tableName := tableName)
  elaborated := elaborated memory tableName
  Spec input output _ := Spec memory input output
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness := by
    circuit_proof_start [InitialMemoryLookup.circuitNamed, AddOperation.circuit]
    have atOffset (index : Fin 7) :
        (Vector.map Expression.const (offset (p := p) index)).map (Expression.eval env) = offset index := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    simp only [atOffset] at h_holds
    rw [eval_word]
    apply read_of_bytes memory input _
      (Fin.cases input (fun index =>
        (Vector.mapRange 4 fun limb => var ⟨i₀ + 89 + index.val * 93 + limb⟩).map
          (Expression.eval env))) rfl
    · intro index
      induction index using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.val_zero, Vector.getElem_map]
        rw [Vector.getElem_append_left (by decide)]
        exact h_holds.1
      | succ i =>
        simp only [Fin.cases_succ, Fin.val_succ, Vector.getElem_map]
        rw [Vector.getElem_append_right (by omega) (by omega)]
        simpa only [Nat.add_sub_cancel, circuit_norm] using (h_holds.2 i).2
    · intro index
      induction index using Fin.cases with
      | zero => simp
      | succ i =>
        have addition := (h_holds.2 i).1
          ⟨fun _ => ⟨h_holds.1.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩
        simpa only [Fin.cases_succ, Fin.val_succ, offset, toBitVec64_bitVecToWord]
          using (addition rfl).2
  completeness := by
    circuit_proof_start [InitialMemoryLookup.circuitNamed, AddOperation.circuit]
    have atOffset (index : Fin 7) :
        (Vector.map Expression.const (offset (p := p) index)).map (Expression.eval env.toEnvironment) = offset index := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    simp only [atOffset]
    refine ⟨⟨h_assumptions.1, by omega⟩, ?_⟩
    intro index
    have sumEq :
        (Vector.mapRange 4 fun limb => var ⟨i₀ + 89 + index.val * 93 + limb⟩).map
            (Expression.eval env.toEnvironment) = AddOperation.populate input (offset index) := by
      have generated := AddOperation.populateIR_eval env input_var (Vector.map Expression.const (offset index))
        input (offset index)
        ((vec4_eval env.toEnvironment input_var).trans h_input)
        ((vec4_eval env.toEnvironment _).trans (atOffset index))
        h_assumptions.1 (isU64_bitVecToWord _)
      ext limb bound
      simpa only [circuit_norm, generated] using (h_env.2 index).1 ⟨limb, bound⟩
    rw [sumEq]
    have addition := AddOperation.spec_populate (b := offset index) h_assumptions.1
      (isU64_bitVecToWord _) 1
    refine ⟨⟨⟨fun _ => ⟨h_assumptions.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩,
      addition⟩, (addition rfl).1, ?_⟩
    have position := address_offset index.succ h_assumptions.1 (by omega)
      (addition rfl).1 (by
        simpa only [Fin.val_succ, offset, toBitVec64_bitVecToWord] using (addition rfl).2)
    rw [position]
    have := index.isLt
    omega

@[circuit_norm ↓, explicit_circuit_norm] theorem circuitNamed_elaborated (memory : ByteMemory) (tableName : String) :
    (circuitNamed (p := p) memory tableName).elaborated = elaborated memory tableName := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_localLength (memory : ByteMemory) (tableName : String)
    (input : Var Word (ZMod p)) :
    (circuitNamed memory tableName).localLength input = 740 := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_requirements (memory : ByteMemory) (tableName : String) :
    (circuitNamed (p := p) memory tableName).channelsWithRequirements = [] := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_guarantees (memory : ByteMemory) (tableName : String) :
    (circuitNamed (p := p) memory tableName).channelsWithGuarantees =
      [(InitialMemoryLookup.membership memory (2 ^ 48) tableName).channel.toRaw,
        SP1Clean.Channels.byteChannel.toRaw] ++
      (List.replicate 7 (List.replicate 4 SP1Clean.Channels.byteChannel.toRaw ++
        [(InitialMemoryLookup.membership memory (2 ^ 48) tableName).channel.toRaw,
          SP1Clean.Channels.byteChannel.toRaw])).flatten := rfl

/-- Source-memory specialization of the named fixed word read. -/
abbrev circuit (memory : ByteMemory) := circuitNamed (p := p) memory "sp1.native.initial_memory"

/-- Word authentication uses membership channels, with no legacy lookups. -/
@[circuit_norm] theorem main_lookupNames (memory : ByteMemory)
    (input : Var Word (ZMod p)) (name : String) (offset : ℕ) :
    ((main memory input name).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, InitialMemoryLookup.circuitNamed, AddOperation.circuit, AddOperation.main,
    circuit_norm]

end SP1Clean.InitialMemoryRead
