import SP1Clean.Proofs.Operations.HintNodeAllocatePopulate

/-! # Compiling an ordered hint prefix into fresh allocations

WRITE-to-hints adds one node; a hook may add any finite prefix. Both use the same constructor,
allocating from back to front to retain reply order. The proofs derive every local circuit
contract, the exact row count, and full cursor continuity from semantic queue representation and
one capacity bound. Matching these rows to the host call and its bytes remains AIR integration.
-/

namespace SP1Clean.HintNodeAllocate

open Circuit Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def compilePrepend (clock : ℕ) (store : Store) (head : ℕ) : List Bytes → List (Inputs (ZMod p))
  | [] => []
  | bytes :: rest =>
      let next := HintQueue.prepend store head rest
      compilePrepend clock store head rest ++
        [populate (HostHintQueue.State.encode clock next.2 next.1.size) bytes]

/-- Check full before/after cursor continuity, including clocks and the allocation frontier. -/
def replayCursors (initial : HostHintQueue.State (ZMod p)) (rows : List (Inputs (ZMod p))) :
    Option (HostHintQueue.State (ZMod p)) :=
  rows.foldlM (fun state row =>
    if toElements state = toElements row.previous then some row.next else none) initial

omit [Fact (2 ^ 17 < p)] in
theorem compilePrepend_length (clock : ℕ) (store : Store) (head : ℕ) (added : List Bytes) :
    (compilePrepend (p := p) clock store head added).length = added.length := by
  induction added with
  | nil => rfl
  | cons bytes rest ih => simp [compilePrepend, ih]

/-- Successful semantic prepends require no extra row-readiness premise. -/
theorem compilePrepend_spec (clock : ℕ) (store : Store) (head : ℕ)
    (hints added : List Bytes) (current : Represents store head hints)
    (capacity : store.size + added.length < 2 ^ 48) :
    ∀ input ∈ compilePrepend (p := p) clock store head added, Spec input := by
  induction added with
  | nil => simp [compilePrepend]
  | cons bytes rest ih =>
    have count := prepend_size store head rest
    have small : store.size + rest.length < 2 ^ 48 := by
      simp only [List.length_cons] at capacity
      omega
    have represented := prepend_represents current rest
    intro input member
    simp only [compilePrepend, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact ih small input earlier
    · apply populate_spec _ bytes _ (rest ++ hints) (HostHintQueue.State.encode_binds clock represented (by omega))
      simp only [List.length_cons] at capacity
      omega

/-- The computed rows connect the complete input cursor to the semantic prepend's exact output. -/
theorem compilePrepend_replay (clock : ℕ) (store : Store) (head : ℕ) (added : List Bytes)
    (capacity : store.size + added.length < 2 ^ 48) :
    replayCursors (HostHintQueue.State.encode (p := p) clock head store.size)
      (compilePrepend clock store head added) =
        some (HostHintQueue.State.encode clock (HintQueue.prepend store head added).2
          (HintQueue.prepend store head added).1.size) := by
  induction added with
  | nil => rfl
  | cons bytes rest ih =>
    have count := prepend_size store head rest
    have small : store.size + rest.length < 2 ^ 48 := by
      simp only [List.length_cons] at capacity
      omega
    simp only [compilePrepend, replayCursors, List.foldlM_append] at ih ⊢
    rw [ih small]
    simp only [Bind.bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, pure,
      populate, if_true, Inputs.next, HostHintQueue.State.encode, NodeRecord.encode,
      Address.toNat_ofNat _ (show (HintQueue.prepend store head rest).1.size < 2 ^ 48 by omega),
      HintQueue.prepend, Array.size_push]

/-- The endpoint cursor still denotes every byte, in the original hook-reply order. -/
theorem compilePrepend_binds (clock : ℕ) (store : Store) (head : ℕ) (hints added : List Bytes)
    (current : Represents store head hints) (capacity : store.size + added.length < 2 ^ 48) :
    let next := HintQueue.prepend store head added
    (HostHintQueue.State.encode (p := p) clock next.2 next.1.size).Binds next.1 (added ++ hints) := by
  apply HostHintQueue.State.encode_binds clock (prepend_represents current added)
  rwa [prepend_size]

end SP1Clean.HintNodeAllocate
