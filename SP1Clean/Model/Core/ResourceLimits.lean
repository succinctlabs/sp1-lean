import SP1Clean.Model.Core.NativeLayout

/-! # Numeric limits for the bounded native facade

All values are inclusive ceilings. Semantic usage and physical accounting are separate consumers
of this data. In particular, individual count ceilings do not establish that their combined
physical expansion fits: the capacity proof must include providers, refreshes and boundaries.
There is no predicate-valued field and no compiler or witness in this interface.
-/

namespace SP1Clean.Model.Core

/-- Independent inclusive semantic and physical ceilings for one native shard. -/
structure ResourceLimits where
  /-- Number of real ordinary and host events. -/
  events : ℕ
  /-- Elapsed interaction-clock ticks. -/
  ticks : ℕ
  /-- Total requested host read bytes, counting overlapping logical requests separately. -/
  readBytes : ℕ
  /-- Total emitted host write bytes, including hint padding. -/
  writeBytes : ℕ
  /-- Total freshly allocated hints, independently of subsequent consumption. -/
  allocatedHints : ℕ
  /-- Peak number of hints in the live queue. -/
  liveHints : ℕ
  /-- Peak total byte length of the live queue. -/
  liveHintBytes : ℕ
  /-- Number of accumulated external hook and proof requests. -/
  requests : ℕ
  /-- Total accumulated public, standard-output and standard-error bytes. -/
  outputBytes : ℕ
  /-- Canonical represented boundary payload, independent of sparse update history. -/
  boundaryBytes : ℕ
  /-- Physical height of each table, including administrative and padding rows. -/
  tableRows : ℕ
  /-- Occurrences in each complete registered-channel ledger, independently of multiplicities. -/
  channelOccurrences : ℕ
deriving DecidableEq, Repr, Inhabited

namespace ResourceLimits

/-- Native tick and field-count ceilings. Fixed pointer/length widths and combined physical
capacity require separate proofs; arbitrary characteristics need not fit fixed bit widths. -/
def native (characteristic : ℕ) : ResourceLimits where
  events := NativeLayout.maxShardTicks / 8
  ticks := NativeLayout.maxShardTicks
  readBytes := characteristic - 1
  writeBytes := characteristic - 1
  allocatedHints := characteristic - 1
  liveHints := characteristic - 1
  liveHintBytes := characteristic - 1
  requests := characteristic - 1
  outputBytes := characteristic - 1
  boundaryBytes := characteristic - 1
  tableRows := characteristic - 1
  channelOccurrences := characteristic - 1

/-- Independent ceilings may be tightened without choosing another machine or memory model. -/
def LE (small large : ResourceLimits) : Prop :=
  small.events ≤ large.events ∧ small.ticks ≤ large.ticks ∧
  small.readBytes ≤ large.readBytes ∧ small.writeBytes ≤ large.writeBytes ∧
  small.allocatedHints ≤ large.allocatedHints ∧ small.liveHints ≤ large.liveHints ∧
  small.liveHintBytes ≤ large.liveHintBytes ∧ small.requests ≤ large.requests ∧
  small.outputBytes ≤ large.outputBytes ∧ small.boundaryBytes ≤ large.boundaryBytes ∧
  small.tableRows ≤ large.tableRows ∧ small.channelOccurrences ≤ large.channelOccurrences

theorem LE.refl (limits : ResourceLimits) : limits.LE limits := by
  simp [LE]

theorem LE.trans {first middle last : ResourceLimits}
    (left : first.LE middle) (right : middle.LE last) : first.LE last := by
  unfold LE at *
  omega

end ResourceLimits
end SP1Clean.Model.Core
