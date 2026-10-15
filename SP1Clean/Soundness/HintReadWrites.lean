import SP1Clean.Soundness.HintReadCoverage
import SP1Clean.Model.Core.HintQueueWordRecords

/-! # Exact physical word writes from authenticated hint coverage

Natural index order and the immutable final-word marker fix the destination address of every
consumer. The last cursor retains its final written address, so its vertex invariant uses a
clipped index. The public inventory states complete address/value agreement without exposing
the internal nonfinal/final split. Word bindings and per-call table balance remain explicit.
-/

namespace SP1Clean.Soundness.HintReadWrites

open Circuit Air.Flat Model.Core Model.Core.HintQueue HintReadCoverage

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def produced (row : Row (p := p)) : ℕ × BitVec 64 :=
  (Address.toNat (rowInput row).address, Word.toBitVec64 (rowInput row).ram.new_value)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem addresses_of_walk {R V : Type*} (edge : R → V × V)
    (index address : V → ℕ) (count base : ℕ) (initial final : V) (path : List R)
    (walk : Walk.IsWalk edge initial final path)
    (steps : ∀ row ∈ path,
      index (edge row).1 < count ∧ index (edge row).2 = index (edge row).1 + 1 ∧
      address (edge row).2 = address (edge row).1 +
        (if index (edge row).1 + 1 = count then 0 else 8))
    (start : address initial = base + min (index initial) (count - 1) * 8) :
    ∀ row ∈ path, address (edge row).1 = base + index (edge row).1 * 8 := by
  induction path generalizing initial with
  | nil => simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have step := steps row (List.mem_cons_self ..)
    have current : address (edge row).1 = base + index (edge row).1 * 8 := by
      have bounded : min (index (edge row).1) (count - 1) = index (edge row).1 := min_eq_left (by omega)
      rw [← source, bounded] at start
      exact start
    have next : address (edge row).2 = base + min (index (edge row).2) (count - 1) * 8 := by
      rw [step.2.2, current, step.2.1]
      split_ifs with last
      · have clipped : min (index (edge row).1 + 1) (count - 1) = index (edge row).1 := by omega
        rw [clipped]
        omega
      · have clipped : min (index (edge row).1 + 1) (count - 1) = index (edge row).1 + 1 := by omega
        rw [clipped]
        omega
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact current
    · exact ih _ tail (fun r h => steps r (List.mem_cons_of_mem _ h)) next other member

omit [Fact (2 ^ 25 < p)] in
private theorem word_facts (last : Bool) (input : HintReadWordChip.Inputs (ZMod p))
    (store : Store) (node : Node) (binding : (input.step last).word.Binds store)
    (read : node? store (Address.toNat input.pointer) = some node) :
    Address.toNat input.index < wordCount node.bytes ∧
      (last = true ↔ Address.toNat input.index + 1 = wordCount node.bytes) ∧
      Word.toBitVec64 input.ram.new_value = wordValue node.bytes (Address.toNat input.index) := by
  have contents := binding.value read
  have marker := binding.isLast_iff read
  have flag : (input.step last).word.isLast = 1 ↔ last = true := by
    cases last <;> simp [HintReadWordChip.Inputs.step]
  exact ⟨contents.1, flag.symm.trans marker, contents.2⟩

omit [Fact (2 ^ 25 < p)] in
private theorem row_steps (last : Bool) (input : HintReadWordChip.Inputs (ZMod p))
    (valid : HintReadStep.Spec last (input.step last)) (store : Store) (node : Node)
    (binding : (input.step last).word.Binds store)
    (read : node? store (Address.toNat input.pointer) = some node) :
    Address.toNat input.index < wordCount node.bytes ∧
      Address.toNat input.nextIndex = Address.toNat input.index + 1 ∧
      Address.toNat input.nextAddress = Address.toNat input.address +
        (if Address.toNat input.index + 1 = wordCount node.bytes then 0 else 8) ∧
      Word.toBitVec64 input.ram.new_value = wordValue node.bytes (Address.toNat input.index) := by
  have words := word_facts last input store node binding read
  refine ⟨words.1, valid.2.2.2.2.1, ?_, words.2.2⟩
  have advance := valid.2.2.2.2.2.2
  change Address.toNat input.nextAddress = Address.toNat input.address + (if last then 0 else 8) at advance
  simpa only [words.2.1] using advance

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem writes_of_walk {R V : Type*} (edge : R → V × V)
    (index address : V → ℕ) (value : R → BitVec 64) (bytes : Bytes)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (indices : path.map (fun row => index (edge row).1) = List.range (wordCount bytes))
    (steps : ∀ row ∈ path,
      index (edge row).1 < wordCount bytes ∧ index (edge row).2 = index (edge row).1 + 1 ∧
      address (edge row).2 = address (edge row).1 +
        (if index (edge row).1 + 1 = wordCount bytes then 0 else 8) ∧
      value row = wordValue bytes (index (edge row).1))
    (zero : index initial = 0) :
    path.map (fun row => (address (edge row).1, value row)) = wordWrites (address initial) bytes ∧
      ∀ row ∈ path, address (edge row).1 = address initial + index (edge row).1 * 8 := by
  have addresses := addresses_of_walk edge index address (wordCount bytes) (address initial)
    initial final path walk (fun row member =>
      ⟨(steps row member).1, (steps row member).2.1, (steps row member).2.2.1⟩) (by simp [zero])
  refine ⟨?_, addresses⟩
  have equal : path.map (fun row => (address (edge row).1, value row)) =
      path.map ((fun i => (address initial + i * 8, wordValue bytes i)) ∘
        (fun row => index (edge row).1)) := by
    apply List.map_congr_left
    intro row member
    exact Prod.ext (addresses row member) (steps row member).2.2.2
  rw [equal, ← List.map_map, indices]
  rfl

/-- Every physical row writes its exact node word at the corresponding consecutive address. -/
theorem ordered_writes (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (initial final : HintReadWordChip.State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : Steps tables data)
    (balanced : BalancedInteractions
      ([HintReadWordChip.stateChannel.pushedValue initial, HintReadWordChip.stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith data HintReadWordChip.stateChannel.toRaw)))
    (store : Store) (node : Node) (read : node? store (Address.toNat initial.pointer) = some node)
    (bindings : ∀ row ∈ TransitionView.readIndexedRows variants tables data, ((rowInput row).step row.1).word.Binds store)
    (zero : Address.toNat initial.index = 0) (count : Address.toNat final.index = wordCount node.bytes) :
    ∃ path : List (Row (p := p)), path.Perm (TransitionView.readIndexedRows variants tables data) ∧
      Walk.IsWalk edge initial final path ∧
      path.map produced = wordWrites (Address.toNat initial.address) node.bytes ∧
      ∀ row ∈ path, context (rowInput row).previous = context initial ∧
        Address.toNat (rowInput row).address =
          Address.toNat initial.address + Address.toNat (rowInput row).index * 8 := by
  obtain ⟨path, perm, walk, length, indices, _, same⟩ := ordered_cover tables data initial final aligned valid balanced
  rw [zero, Nat.zero_add, count] at length
  rw [zero, ← List.range_eq_range', ← length] at indices
  have written := writes_of_walk edge
    (fun state : HintReadWordChip.State (ZMod p) => Address.toNat state.index)
    (fun state => Address.toNat state.address) (fun row => Word.toBitVec64 (rowInput row).ram.new_value)
    node.bytes initial final path walk indices (by
      intro row member
      have pointer := congrArg (fun c => c.2.2) (same row member)
      change (rowInput row).pointer = initial.pointer at pointer
      exact row_steps row.1 (rowInput row) (valid row (perm.mem_iff.mp member))
        store node (bindings row (perm.mem_iff.mp member)) (by rwa [pointer])) zero
  exact ⟨path, perm, walk, written.1, fun row member => ⟨same row member, written.2 row member⟩⟩

end SP1Clean.Soundness.HintReadWrites
