import SP1Clean.Model.Core.HintQueue
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Math.Address
import ToClean.Circuit.StaticTable
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Field records for immutable hint nodes

Node identities and tail pointers use three bounded 16-bit limbs. Lengths use full 64-bit words,
matching HINT_LEN's return convention. A record's local bounds do not authenticate its contents:
`Binds` identifies the actual immutable node. The fixed source table derives that binding from
the complete source hint list, independently of witness data, and fails closed on oversized
node inventories. New allocations require a separate authenticated provider.
-/

namespace SP1Clean.Model.Core.HintQueue

open SP1Clean.Soundness.Target

structure NodeRecord (F : Type) where
  pointer : fields 3 F
  tail : fields 3 F
  length : Word F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas NodeRecord

variable {p : ℕ} [Fact p.Prime]

def NodeRecord.Valid (record : NodeRecord (ZMod p)) : Prop :=
  Address.Bounded record.pointer ∧ Address.Bounded record.tail ∧
    Address.toNat record.tail < Address.toNat record.pointer ∧ Word.isU64 record.length

def NodeRecord.Binds (store : Store) (record : NodeRecord (ZMod p)) : Prop :=
  ∃ node, node? store (Address.toNat record.pointer) = some node ∧
    Address.toNat record.tail = node.tail ∧
    Word.toBitVec64 record.length = BitVec.ofNat 64 node.bytes.length

def NodeRecord.encode (pointer : ℕ) (node : Node) : NodeRecord (ZMod p) :=
  ⟨Address.ofNat pointer, Address.ofNat node.tail, bitVecToWord (BitVec.ofNat 64 node.bytes.length)⟩

variable [Fact (2 ^ 17 < p)]

theorem NodeRecord.encode_valid (pointer : ℕ) (node : Node) (bound : pointer < 2 ^ 48)
    (descending : node.tail < pointer) : (encode (p := p) pointer node).Valid := by
  refine ⟨Address.bounded_ofNat _, Address.bounded_ofNat _, ?_, isU64_bitVecToWord _⟩
  change Address.toNat (Address.ofNat (p := p) node.tail) < Address.toNat (Address.ofNat (p := p) pointer)
  rwa [Address.toNat_ofNat _ (by omega), Address.toNat_ofNat _ bound]

theorem NodeRecord.encode_binds {store : Store} {pointer : ℕ} {node : Node}
    (read : node? store pointer = some node) (bound : pointer < 2 ^ 48)
    (descending : node.tail < pointer) : (encode (p := p) pointer node).Binds store := by
  refine ⟨node, ?_, Address.toNat_ofNat _ (by omega), toBitVec64_bitVecToWord _⟩
  change node? store (Address.toNat (Address.ofNat (p := p) pointer)) = some node
  rwa [Address.toNat_ofNat _ bound]

omit [Fact (2 ^ 17 < p)] in
/-- An authenticated node observation returns that queue head's exact length word. -/
theorem NodeRecord.Binds.hintLength {store : Store} {record : NodeRecord (ZMod p)}
    (binding : record.Binds store) :
    hintLength? store (Address.toNat record.pointer) = some (Word.toBitVec64 record.length) := by
  obtain ⟨node, read, _, length⟩ := binding
  have nonzero := (node?_bound read).1
  rw [hintLength?, if_neg (by omega), read, Option.map_some, length]

omit [Fact (2 ^ 17 < p)] in
/-- Source or earlier allocation metadata remains authenticated after later persistent prepends. -/
theorem NodeRecord.Binds.extend {old new : Store} {record : NodeRecord (ZMod p)}
    (extension : Extends old new) (binding : record.Binds old) : record.Binds new := by
  obtain ⟨node, read, tail, length⟩ := binding
  exact ⟨node, extension _ _ read, tail, length⟩

omit [Fact (2 ^ 17 < p)] in
/-- Authentication restricts to an earlier store when the pointer was already allocated. -/
theorem NodeRecord.Binds.restrict {old new : Store} {record : NodeRecord (ZMod p)}
    (binding : record.Binds new) (extension : Extends old new)
    (bound : Address.toNat record.pointer ≤ old.size) : record.Binds old := by
  obtain ⟨node, read, tail, length⟩ := binding
  exact ⟨node, extension.read_of_bound read bound, tail, length⟩

/-- Initial node identities are local to the shard; an oversized source never wraps into aliases. -/
def sourceRows (hints : List Bytes) : List (NodeRecord (ZMod p)) :=
  if hints.length < 2 ^ 48 then
    List.ofFn (fun index : Fin (ofList hints).1.size =>
      NodeRecord.encode (index.val + 1) (ofList hints).1[index.val])
  else []

@[irreducible] def sourceTable (hints : List Bytes) : StaticTable (ZMod p) NodeRecord :=
  StaticTable.ofRows "sp1.native.hint_source_nodes" (sourceRows hints)

omit [Fact (2 ^ 17 < p)] in
theorem sourceTable_spec (hints : List Bytes) (record : NodeRecord (ZMod p)) :
    (sourceTable hints).Spec record ↔ hints.length < 2 ^ 48 ∧
      ∃ index : Fin (ofList hints).1.size,
        NodeRecord.encode (index.val + 1) (ofList hints).1[index.val] = record := by
  simp [sourceTable, StaticTable.ofRows, sourceRows]

/-- The source lookup proves both local record validity and actual source-node binding. -/
theorem sourceTable_sound (hints : List Bytes) (record : NodeRecord (ZMod p))
    (member : (sourceTable hints).Spec record) : record.Valid ∧ record.Binds (ofList hints).1 := by
  obtain ⟨fits, index, rfl⟩ := (sourceTable_spec hints record).mp member
  have read : node? (ofList hints).1 (index.val + 1) = some (ofList hints).1[index.val] :=
    Array.getElem?_eq_getElem index.isLt
  have descending := ofList_wellFormed hints _ _ read
  have bound : index.val + 1 < 2 ^ 48 := by
    have := index.isLt
    have := ofList_size hints
    omega
  exact ⟨NodeRecord.encode_valid _ _ bound descending, NodeRecord.encode_binds read bound descending⟩

omit [Fact (2 ^ 17 < p)] in
/-- Every source node has its canonical provider row whenever the explicit identity bound holds. -/
theorem sourceTable_complete (hints : List Bytes) (fits : hints.length < 2 ^ 48)
    (index : Fin (ofList hints).1.size) :
    (sourceTable (p := p) hints).Spec (NodeRecord.encode (index.val + 1) (ofList hints).1[index.val]) :=
  (sourceTable_spec hints _).mpr ⟨fits, index, rfl⟩

end SP1Clean.Model.Core.HintQueue
