import SP1Clean.Soundness.HostHintQueueBoundary
import ToClean.Air.TableSlot

/-! # Registered positions of native host component blocks

The source-backed registration has one ordered component list. Bank references name their
actual receiver or terminal component and remain valid when resource blocks are appended.
The installed reference accounts for the protected CPU prefix and its HALT replacement once;
consumers read original tables through `TableSlot`, without maintaining their own offsets.
-/

namespace SP1Clean.Soundness.HostTableRegistry

open Circuit Air.Flat Model.Core HostHintReadLocal HostHintReadHandoff HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance registryLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Existing receiver and source-resource blocks, in their physical registration order. -/
def auxiliary (hints : List Bytes) : List (Component (ZMod p)) :=
  (receiver :: HostCallReceivers.available).map (·.component) ++
    (wordResources ++ sourceResources hints)

/-- The installed physical suffix has exactly the registered host components, in order. -/
theorem auxiliary_components {image : ProgramImage} {source : ExecutionSnapshot}
    {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal
      HostCallReceivers.available (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))) :
    (witness.tables.drop 62).map (·.component) = auxiliary source.host.io.hints := by
  have components := HostLocalCore.auxiliaryTables_components (HostHintQueueBoundary.projected witness)
  change ((HostHintQueueBoundary.projected witness).tables.drop 62).map (·.component) =
    auxiliary source.host.io.hints at components
  rw [HostHintQueueBoundary.projected_drop witness 62 (by decide)] at components
  exact components

/-- Number of source-backed host components before any further resource extension. -/
theorem auxiliary_length (hints : List Bytes) : (auxiliary (p := p) hints).length = 27 := rfl

/-- Physical bank position inside the host block, including its administrative terminal. -/
def bankPosition (deferred : Bool) : Index → ℕ
  | some slot => (if deferred then 11 else 3) + slot.val
  | none => if deferred then 26 else 25

/-- Every bank position lies in the registered source-backed block. -/
theorem bankPosition_lt (deferred : Bool) (index : Index) : bankPosition deferred index < 27 := by
  cases index with
  | none => cases deferred <;> decide
  | some slot => have := slot.isLt; cases deferred <;> simp only [bankPosition, Bool.false_eq_true,
      if_false, if_true] <;> omega

/-- Typed receiver and terminal references, independent of the enclosing CPU prefix. -/
def bankSlot (hints : List Bytes) (deferred : Bool) (index : Index) :
    TableSlot (auxiliary (p := p) hints) (view deferred index).component where
  index := ⟨bankPosition deferred index, by rw [auxiliary_length]; exact bankPosition_lt deferred index⟩
  component_eq := by
    cases index with
    | none => cases deferred <;> rfl
    | some slot => cases deferred <;> fin_cases slot <;> rfl

/-- Appended resources cannot move or reinterpret any existing bank table. -/
def extendedBankSlot (hints : List Bytes) (extra : List (Component (ZMod p)))
    (deferred : Bool) (index : Index) :
    TableSlot (auxiliary hints ++ extra) (view deferred index).component :=
  (bankSlot hints deferred index).appendLeft extra

/-- Typed bank registration in the actual boundary-installed local ensemble. -/
def installedBankSlot (image : ProgramImage) (source : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (channels : List (RawChannel (ZMod p))) (deferred : Bool) (index : Index) :
    TableSlot (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)).tables (view deferred index).component :=
  ((bankSlot source.host.io.hints deferred index).appendRight
    ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer)).setOther 57
    HaltPaddingChip.component (by
      change 57 ≠ ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer).length +
        bankPosition deferred index
      rw [List.length_set, ProtectedLocalCore.tables_length]
      omega)

/-- The installed position is the original host-block position plus its CPU prefix. -/
theorem installedBankSlot_index (image : ProgramImage) (source : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (channels : List (RawChannel (ZMod p))) (deferred : Bool) (index : Index) :
    (installedBankSlot image source final bankFinal channels deferred index).index.val =
      62 + bankPosition deferred index := by
  change ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer).length +
    bankPosition deferred index = _
  rw [List.length_set, ProtectedLocalCore.tables_length]

end SP1Clean.Soundness.HostTableRegistry
