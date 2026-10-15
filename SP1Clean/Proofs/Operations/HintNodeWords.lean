import SP1Clean.Proofs.Operations.HintNodeAllocatePopulate
import SP1Clean.Model.Core.HintQueueWordRecords

/-! # Allocated word contents share the checked fresh node identity

Once the enclosing host effect supplies actual bytes, the existing checked append authenticates
both its metadata and the generated word rows in the same persistent store. The new records
retain the allocation's exact field identity. This is a semantic construction bridge, not an
authorization for arbitrary witness bytes or a replacement for the host's byte-source ledger.
-/

namespace SP1Clean.HintNodeAllocate

open Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem append_contents_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (store : Store) (hints : List Bytes) (current : input.previous.Binds store hints)
    (bytes : Bytes) (length : Word.toBitVec64 input.node.length = BitVec.ofNat 64 bytes.length) :
    let next := store.push ⟨bytes, Address.toNat input.previous.head⟩
    input.next.Binds next (bytes :: hints) ∧ input.node.Binds next ∧
      (∀ record ∈ nodeWordRows (p := p) (Address.toNat input.node.pointer) bytes,
        record.Binds next ∧ record.pointer = input.node.pointer) ∧ Extends store next := by
  obtain ⟨cursor, header, extension⟩ := append_of_spec input valid store hints current bytes length
  refine ⟨cursor, header, ?_, extension⟩
  have pointer := identity_of_spec input valid store hints current
  have bound := Address.toNat_lt valid.2.2.2.2.1.1
  have read : node? (store.push ⟨bytes, Address.toNat input.previous.head⟩)
      (Address.toNat input.node.pointer) = some ⟨bytes, Address.toNat input.previous.head⟩ := by
    rw [pointer]
    exact node?_fresh _ _
  intro record member
  refine ⟨nodeWordRows_binds read bound record member, ?_⟩
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact Address.ofNat_toNat valid.2.2.2.2.1.1

/-- The actual append compiler needs no separately asserted metadata or word-content contract. -/
theorem populate_contents (previous : HostHintQueue.State (ZMod p)) (bytes : Bytes)
    (store : Store) (hints : List Bytes) (current : previous.Binds store hints)
    (capacity : store.size + 1 < 2 ^ 48) :
    let input := populate previous bytes
    let next := store.push ⟨bytes, Address.toNat previous.head⟩
    input.next.Binds next (bytes :: hints) ∧ input.node.Binds next ∧
      (∀ record ∈ nodeWordRows (p := p) (Address.toNat input.node.pointer) bytes,
        record.Binds next ∧ record.pointer = input.node.pointer) ∧ Extends store next := by
  apply append_contents_of_spec _ (populate_spec previous bytes store hints current capacity) store hints current bytes
  exact SP1Clean.Soundness.Target.toBitVec64_bitVecToWord _

end SP1Clean.HintNodeAllocate
