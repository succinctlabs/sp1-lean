import SP1Clean.Model.Core.HostIO

/-! # Persistent, byte-exact hint queues

Zero denotes the empty queue. Every allocated node stores the complete hint and a smaller tail
pointer; appending nodes preserves all previous pointers. This lets host tables observe a queue
head, prepend guest or hook hints, and pop a consumed hint without copying its unchanged suffix.
No hash or trusted content oracle identifies bytes. Field encodings, resource bounds, and AIR
authentication of the node inventory remain separate from this executable representation.
-/

namespace SP1Clean.Model.Core.HintQueue

structure Node where
  bytes : Bytes
  tail : ℕ
deriving DecidableEq, Repr, Inhabited

abbrev Store := Array Node

/-- Positive pointers index immutable nodes; zero has no node. -/
def node? (store : Store) : ℕ → Option Node
  | 0 => none
  | index + 1 => store[index]?

/-- A queue denotes all bytes in order, with strictly decreasing pointers. -/
inductive Represents (store : Store) : ℕ → List Bytes → Prop
  | nil : Represents store 0 []
  | cons {head tail : ℕ} {bytes : Bytes} {rest : List Bytes}
      (read : node? store head = some ⟨bytes, tail⟩) (descending : tail < head)
      (suffix : Represents store tail rest) : Represents store head (bytes :: rest)

/-- Every old node remains available with exactly the same bytes and tail. -/
def Extends (old new : Store) : Prop :=
  ∀ pointer node, node? old pointer = some node → node? new pointer = some node

/-- The local condition every immutable node must satisfy, including unreachable history. -/
def WellFormed (store : Store) : Prop :=
  ∀ pointer node, node? store pointer = some node → node.tail < pointer

theorem wellFormed_empty : WellFormed #[] := by
  intro pointer node read
  cases pointer <;> simp [node?] at read

theorem Extends.refl (store : Store) : Extends store store := fun _ _ read => read

theorem Extends.trans {first middle last : Store} (left : Extends first middle)
    (right : Extends middle last) : Extends first last :=
  fun pointer node read => right pointer node (left pointer node read)

theorem node?_bound {store : Store} {pointer : ℕ} {node : Node}
    (read : node? store pointer = some node) : 0 < pointer ∧ pointer ≤ store.size := by
  cases pointer with
  | zero => contradiction
  | succ index =>
    have bound := (Array.getElem?_eq_some_iff.mp read).1
    omega

/-- A later store authenticates an earlier read only inside the earlier allocation frontier. -/
theorem Extends.read_of_bound {old new : Store} (extension : Extends old new)
    {pointer : ℕ} {node : Node} (read : node? new pointer = some node)
    (bound : pointer ≤ old.size) : node? old pointer = some node := by
  cases pointer with
  | zero => contradiction
  | succ index =>
    have atIndex : index < old.size := by omega
    have previous : node? old (index + 1) = some old[index] := Array.getElem?_eq_getElem atIndex
    have equal := Option.some.inj ((extension _ _ previous).symm.trans read)
    exact previous.trans (congrArg some equal)

theorem Represents.bound {store : Store} {pointer : ℕ} {hints : List Bytes}
    (represents : Represents store pointer hints) : pointer ≤ store.size := by
  cases represents with
  | nil => omega
  | cons read _ _ => exact (node?_bound read).2

theorem Represents.extend {old new : Store} (extension : Extends old new)
    {pointer : ℕ} {hints : List Bytes} (represents : Represents old pointer hints) :
    Represents new pointer hints := by
  induction represents with
  | nil => exact .nil
  | cons read descending _ ih => exact .cons (extension _ _ read) descending ih

/-- A fresh allocation cannot alter an existing node, even after its queue has been popped. -/
theorem extends_push (store : Store) (node : Node) : Extends store (store.push node) := by
  intro pointer previous read
  cases pointer with
  | zero => contradiction
  | succ index =>
    have bound := (Array.getElem?_eq_some_iff.mp read).1
    simpa only [node?, Array.getElem?_push, if_neg (by omega : index ≠ store.size)] using read

theorem node?_fresh (store : Store) (node : Node) :
    node? (store.push node) (store.size + 1) = some node := Array.getElem?_push_size

theorem wellFormed_push {store : Store} (valid : WellFormed store) (node : Node)
    (tailBound : node.tail ≤ store.size) : WellFormed (store.push node) := by
  intro pointer actual read
  cases pointer with
  | zero => contradiction
  | succ index =>
    simp only [node?, Array.getElem?_push] at read
    split at read
    · next fresh => cases read; omega
    · exact valid (index + 1) actual read

/-- Allocate the added hints from back to front so hook responses retain their original order. -/
def prepend (store : Store) (head : ℕ) : List Bytes → Store × ℕ
  | [] => (store, head)
  | bytes :: rest =>
      let (next, suffix) := prepend store head rest
      (next.push ⟨bytes, suffix⟩, next.size + 1)

theorem prepend_size (store : Store) (head : ℕ) (prepended : List Bytes) :
    (prepend store head prepended).1.size = store.size + prepended.length := by
  induction prepended with
  | nil => simp [prepend]
  | cons bytes rest ih => simp [prepend, ih, Nat.add_assoc]

theorem prepend_extends (store : Store) (head : ℕ) (prepended : List Bytes) :
    Extends store (prepend store head prepended).1 := by
  induction prepended with
  | nil => exact .refl store
  | cons bytes rest ih => exact ih.trans (extends_push _ _)

theorem prepend_head_bound {store : Store} {head : ℕ} (bound : head ≤ store.size)
    (prepended : List Bytes) : (prepend store head prepended).2 ≤ (prepend store head prepended).1.size := by
  cases prepended with
  | nil => exact bound
  | cons bytes rest => simp [prepend]

theorem prepend_wellFormed {store : Store} {head : ℕ} (valid : WellFormed store)
    (bound : head ≤ store.size) (prepended : List Bytes) : WellFormed (prepend store head prepended).1 := by
  induction prepended with
  | nil => exact valid
  | cons bytes rest ih => exact wellFormed_push ih _ (prepend_head_bound bound rest)

/-- The same suffix pointer survives every prepend; no byte content is replaced by a digest. -/
theorem prepend_represents {store : Store} {head : ℕ} {hints : List Bytes}
    (represents : Represents store head hints) (prepended : List Bytes) :
    Represents (prepend store head prepended).1 (prepend store head prepended).2 (prepended ++ hints) := by
  induction prepended with
  | nil => exact represents
  | cons bytes rest ih =>
    simp only [prepend, List.cons_append]
    exact .cons (node?_fresh _ _) (by have := ih.bound; omega) (ih.extend (extends_push _ _))

/-- Every finite boundary queue has a deterministic, complete node inventory. -/
def ofList (hints : List Bytes) : Store × ℕ := prepend #[] 0 hints

theorem ofList_represents (hints : List Bytes) :
    Represents (ofList hints).1 (ofList hints).2 hints := by
  simpa only [ofList, List.append_nil] using prepend_represents (Represents.nil (store := #[])) hints

theorem ofList_size (hints : List Bytes) : (ofList hints).1.size = hints.length := by
  simpa [ofList] using prepend_size #[] 0 hints

theorem ofList_wellFormed (hints : List Bytes) : WellFormed (ofList hints).1 :=
  prepend_wellFormed wellFormed_empty (by decide) hints

/-- A bounded root in a locally well-formed inventory always denotes a finite complete queue. -/
theorem WellFormed.represents {store : Store} (valid : WellFormed store) (head : ℕ)
    (bound : head ≤ store.size) : ∃ hints, Represents store head hints := by
  induction head using Nat.strong_induction_on with
  | h head ih =>
    cases head with
    | zero => exact ⟨[], .nil⟩
    | succ index =>
      have atIndex : index < store.size := by omega
      have read : node? store (index + 1) = some store[index] := Array.getElem?_eq_getElem atIndex
      have descending := valid _ _ read
      obtain ⟨rest, suffix⟩ := ih store[index].tail descending (by omega)
      exact ⟨store[index].bytes :: rest, .cons read descending suffix⟩

/-- Malformed pointers and cycles fail; valid decoding needs no caller-supplied fuel. -/
def decode? (store : Store) (head : ℕ) : Option (List Bytes) :=
  if head = 0 then some [] else do
    let node ← node? store head
    if node.tail < head then
      (node.bytes :: ·) <$> decode? store node.tail
    else none
termination_by head

theorem decode?_of_represents {store : Store} {head : ℕ} {hints : List Bytes}
    (represents : Represents store head hints) : decode? store head = some hints := by
  induction represents with
  | nil => rw [decode?, if_pos rfl]
  | cons read descending _ ih =>
    rw [decode?, if_neg (by have := node?_bound read; omega), read]
    simp only [bind, Option.bind_some, if_pos descending, ih, Functor.map, Option.map_some]

/-- Successful decoding is exactly the byte-level representation relation. -/
theorem decode?_eq_some_iff (store : Store) (head : ℕ) (hints : List Bytes) :
    decode? store head = some hints ↔ Represents store head hints := by
  constructor
  · induction head using Nat.strong_induction_on generalizing hints with
    | h head ih =>
      intro success
      rw [decode?] at success
      split at success
      · next zero =>
        subst head
        cases success
        exact .nil
      · next nonzero =>
        simp only [bind, Option.bind_eq_some_iff] at success
        obtain ⟨node, read, success⟩ := success
        split at success
        · next descending =>
          obtain ⟨rest, decoded, rfl⟩ := Option.map_eq_some_iff.mp success
          exact .cons read descending (ih node.tail descending rest decoded)
        · contradiction
  · exact decode?_of_represents

theorem Represents.unique {store : Store} {head : ℕ} {left right : List Bytes}
    (first : Represents store head left) (second : Represents store head right) : left = right :=
  Option.some.inj ((decode?_of_represents first).symm.trans (decode?_of_represents second))

/-- Observe length without consuming the queue. Empty hints and an empty queue remain distinct. -/
def hintLength? (store : Store) (head : ℕ) : Option (BitVec 64) :=
  if head = 0 then some (BitVec.allOnes 64)
  else (node? store head).map (fun node => BitVec.ofNat 64 node.bytes.length)

theorem hintLength?_of_represents {store : Store} {head : ℕ} {host : HostIO}
    (represents : Represents store head host.hints) :
    hintLength? store head = some host.hintLength := by
  generalize hintsEq : host.hints = hints at represents
  cases represents with
  | nil => simp [hintLength?, HostIO.hintLength, hintsEq]
  | cons read descending _ =>
    rw [hintLength?, if_neg (by have := node?_bound read; omega), read]
    simp [HostIO.hintLength, hintsEq]

/-- Pop returns the complete unpadded hint and its persistent suffix pointer. -/
def pop? (store : Store) (head : ℕ) : Option (Bytes × ℕ) :=
  (node? store head).map (fun node => (node.bytes, node.tail))

theorem pop?_of_represents {store : Store} {head : ℕ} {bytes : Bytes} {rest : List Bytes}
    (represents : Represents store head (bytes :: rest)) :
    ∃ tail, pop? store head = some (bytes, tail) ∧ Represents store tail rest ∧ tail < head := by
  cases represents with
  | cons read descending suffix => exact ⟨_, by simp [pop?, read], suffix, descending⟩

theorem pop?_empty (store : Store) : pop? store 0 = none := rfl

end SP1Clean.Model.Core.HintQueue
