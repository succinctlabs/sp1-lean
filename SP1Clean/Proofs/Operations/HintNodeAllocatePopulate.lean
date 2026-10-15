import SP1Clean.Proofs.Operations.HintNodeAllocate
import SP1Clean.Proofs.Operations.HintQueueCursor

/-! # Fresh node construction and byte-exact persistent extension

The constructor uses the current allocation frontier, never the possibly older head. Checked
allocation appends a real node to the semantic store and preserves all historical nodes. Its
bytes must come from the enclosing authenticated host effect; matching their length alone is
not a byte-authentication theorem.
-/

namespace SP1Clean.HintNodeAllocate

open Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def populate (previous : HostHintQueue.State (ZMod p)) (bytes : Bytes) : Inputs (ZMod p) :=
  ⟨previous, NodeRecord.encode (Address.toNat previous.allocated + 1)
    ⟨bytes, Address.toNat previous.head⟩⟩

/-- Any represented queue admits a checked append when the shared identity capacity permits it. -/
theorem populate_spec (previous : HostHintQueue.State (ZMod p)) (bytes : Bytes)
    (store : Store) (hints : List Bytes) (current : previous.Binds store hints)
    (capacity : store.size + 1 < 2 ^ 48) : Spec (populate previous bytes) := by
  have fits : Address.toNat previous.allocated + 1 < 2 ^ 48 := by rwa [current.2.2.1]
  have descending : Address.toNat previous.head < Address.toNat previous.allocated + 1 :=
    Nat.lt_succ_of_le current.head_le
  refine ⟨current.1, current.2.1, current.head_le, ?_, NodeRecord.encode_valid _ _ fits descending, ?_⟩
  · exact Address.ofNat_toNat current.1
  · exact Address.toNat_ofNat _ fits

omit [Fact (2 ^ 17 < p)] in
/-- A valid allocation cannot select a historical identity, even after the queue has been popped. -/
theorem identity_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (store : Store) (hints : List Bytes) (current : input.previous.Binds store hints) :
    Address.toNat input.node.pointer = store.size + 1 := by
  rw [valid.2.2.2.2.2, current.2.2.1]

omit [Fact (2 ^ 17 < p)] in
theorem fresh_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (store : Store) (hints : List Bytes) (current : input.previous.Binds store hints) :
    node? store (Address.toNat input.node.pointer) = none := by
  rw [identity_of_spec input valid store hints current]
  cases read : node? store (store.size + 1) with
  | none => rfl
  | some node =>
    have bounded := (node?_bound read).2
    omega

omit [Fact (2 ^ 17 < p)] in
/-- Bind the checked metadata to the actual allocated bytes and preserve the entire old store. -/
theorem append_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (store : Store) (hints : List Bytes) (current : input.previous.Binds store hints)
    (bytes : Bytes) (length : Word.toBitVec64 input.node.length = BitVec.ofNat 64 bytes.length) :
    let next := store.push ⟨bytes, Address.toNat input.previous.head⟩
    input.next.Binds next (bytes :: hints) ∧ input.node.Binds next ∧ Extends store next := by
  have pointer := identity_of_spec input valid store hints current
  have nextRead : node? (store.push ⟨bytes, Address.toNat input.previous.head⟩)
      (Address.toNat input.node.pointer) = some ⟨bytes, Address.toNat input.previous.head⟩ := by
    rw [pointer]
    exact node?_fresh _ _
  have extension := extends_push store ⟨bytes, Address.toNat input.previous.head⟩
  have bounds := valid.2.2.2.2.1.1
  refine ⟨⟨bounds, bounds, ?_, ?_⟩, ⟨_, nextRead, ?_, length⟩, extension⟩
  · simpa only [Inputs.next, Array.size_push] using pointer
  · apply Represents.cons nextRead
    · rw [pointer]
      exact Nat.lt_succ_of_le current.2.2.2.bound
    · exact current.2.2.2.extend extension
  · rw [valid.2.2.2.1]

/-- No unproved row contract is needed by the compiler for one actual append. -/
theorem populate_binds (previous : HostHintQueue.State (ZMod p)) (bytes : Bytes)
    (store : Store) (hints : List Bytes) (current : previous.Binds store hints)
    (capacity : store.size + 1 < 2 ^ 48) :
    let input := populate previous bytes
    let next := store.push ⟨bytes, Address.toNat previous.head⟩
    input.next.Binds next (bytes :: hints) ∧ input.node.Binds next ∧ Extends store next := by
  apply append_of_spec _ (populate_spec previous bytes store hints current capacity) store hints current bytes
  exact SP1Clean.Soundness.Target.toBitVec64_bitVecToWord _

end SP1Clean.HintNodeAllocate
