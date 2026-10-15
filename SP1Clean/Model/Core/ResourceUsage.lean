import SP1Clean.Model.Core.ResourceLimits
import SP1Clean.Model.Core.HostFootprint
import SP1Clean.Model.Core.HintQueueEvent

/-! # Semantic resource arithmetic

The first five quantities accumulate work. The others record peak live occupancy. Combining
segments adds work and takes maxima; it does not reset the host's incoming queue or output.
Physical table heights and occurrence counts are measured separately from semantic usage.
-/

namespace SP1Clean.Model.Core

/-- Semantic quantities bounded by the numeric native policy. -/
inductive ResourceKind where
  | events | ticks | readBytes | writeBytes | allocatedHints
  | liveHints | liveHintBytes | requests | outputBytes | boundaryBytes
deriving DecidableEq, Repr

/-- Additive work, as opposed to maximum live occupancy. -/
def ResourceKind.cumulative : ResourceKind → Bool
  | .events | .ticks | .readBytes | .writeBytes | .allocatedHints => true
  | _ => false

/-- A named semantic projection of the data-only limit record. -/
def ResourceLimits.ceiling (limits : ResourceLimits) : ResourceKind → ℕ
  | .events => limits.events
  | .ticks => limits.ticks
  | .readBytes => limits.readBytes
  | .writeBytes => limits.writeBytes
  | .allocatedHints => limits.allocatedHints
  | .liveHints => limits.liveHints
  | .liveHintBytes => limits.liveHintBytes
  | .requests => limits.requests
  | .outputBytes => limits.outputBytes
  | .boundaryBytes => limits.boundaryBytes

/-- Semantic work and peak occupancy, with no execution or circuit witness stored in the carrier. -/
abbrev ResourceUsage := ResourceKind → ℕ

namespace ResourceUsage

/-- The empty resource inventory. -/
def zero : ResourceUsage := fun _ => 0

/-- Composition adds work and preserves the largest actual live occupancy. -/
def combine (first second : ResourceUsage) : ResourceUsage :=
  fun kind => if kind.cumulative then first kind + second kind else max (first kind) (second kind)

/-- Every named semantic quantity obeys its declared inclusive ceiling. -/
def Fits (usage : ResourceUsage) (limits : ResourceLimits) : Prop :=
  ∀ kind, usage kind ≤ limits.ceiling kind

/-- Executable comparison of all semantic quantities, with no compiler or witness input. -/
def checkFits (usage : ResourceUsage) (limits : ResourceLimits) : Bool :=
  [.events, .ticks, .readBytes, .writeBytes, .allocatedHints,
    .liveHints, .liveHintBytes, .requests, .outputBytes, .boundaryBytes].all
      (fun kind => decide (usage kind ≤ limits.ceiling kind))

/-- The finite comparison checks exactly the semantic predicate. -/
theorem checkFits_iff (usage : ResourceUsage) (limits : ResourceLimits) :
    usage.checkFits limits = true ↔ usage.Fits limits := by
  simp only [checkFits, List.all_cons, List.all_nil, Bool.and_eq_true,
    decide_eq_true_eq, and_true]
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, i, j⟩ kind
    cases kind <;> assumption
  · intro fits
    exact ⟨fits _, fits _, fits _, fits _, fits _, fits _, fits _, fits _, fits _, fits _⟩

theorem zero_fits (limits : ResourceLimits) : zero.Fits limits := fun _ => Nat.zero_le _

@[simp] theorem zero_combine (usage : ResourceUsage) : zero.combine usage = usage := by
  funext kind
  simp [combine, zero]

@[simp] theorem combine_zero (usage : ResourceUsage) : usage.combine zero = usage := by
  funext kind
  simp [combine, zero]

theorem combine_assoc (first second third : ResourceUsage) :
    (first.combine second).combine third = first.combine (second.combine third) := by
  funext kind
  simp only [combine]
  split <;> simp [Nat.add_assoc, max_assoc]

theorem le_combine_left (first second : ResourceUsage) (kind : ResourceKind) :
    first kind ≤ first.combine second kind := by
  simp only [combine]
  split <;> omega

theorem le_combine_right (first second : ResourceUsage) (kind : ResourceKind) :
    second kind ≤ first.combine second kind := by
  simp only [combine]
  split <;> omega

theorem Fits.left {first second : ResourceUsage} {limits : ResourceLimits}
    (fits : (first.combine second).Fits limits) : first.Fits limits :=
  fun kind => (le_combine_left first second kind).trans (fits kind)

theorem Fits.right {first second : ResourceUsage} {limits : ResourceLimits}
    (fits : (first.combine second).Fits limits) : second.Fits limits :=
  fun kind => (le_combine_right first second kind).trans (fits kind)

theorem Fits.mono {usage : ResourceUsage} {small large : ResourceLimits}
    (fits : usage.Fits small) (larger : small.LE large) : usage.Fits large := by
  intro kind
  apply (fits kind).trans
  cases kind <;> simp only [ResourceLimits.ceiling] <;> unfold ResourceLimits.LE at larger <;> omega

end ResourceUsage

/-- Fresh nodes created by an actual host queue observation; reads and length queries allocate none. -/
def HintQueue.Event.allocations : HintQueue.Event → ℕ
  | .prepend hints => hints.length
  | .read _ | .length _ => 0

/-- Requested bytes from the existing footprint, including each logical VERIFY buffer. -/
def HostExecution.readByteCount (execution : HostExecution) (context : HostReadContext) : ℕ :=
  ((execution.readSpans? context).getD []).map MemorySpan.length |>.sum

/-- Bytes actually emitted by the host interpreter, including mandatory hint padding. -/
def HostExecution.writeByteCount (execution : HostExecution) : ℕ :=
  (execution.writeSpans.map MemorySpan.length).sum

/-- Host work from a successful concrete execution, without counting final occupancy as allocation. -/
def HostState.executionResources (host : HostState) (context : HostReadContext)
    (execution : HostExecution) : ResourceUsage
  | .readBytes => execution.readByteCount context
  | .writeBytes => execution.writeByteCount
  | .allocatedHints => (host.hintEvent execution).allocations
  | _ => 0

/-- A produced read footprint eliminates the total observer's fallback. -/
theorem HostExecution.readByteCount_eq {execution : HostExecution} {context : HostReadContext}
    {reads : List MemorySpan} (spans : execution.readSpans? context = some reads) :
    execution.readByteCount context = (reads.map MemorySpan.length).sum := by
  simp only [readByteCount, spans, Option.getD_some]

/-- Overlap changes the physical cell cover, never the two logical 32-byte observations. -/
theorem HostExecution.readByteCount_verify {execution : HostExecution} (context : HostReadContext)
    (kind : execution.kind = .verifyProof) : execution.readByteCount context = 64 := by
  simp [readByteCount, readSpans?, kind]

/-- WRITE's demand follows the observed x12 value, not either pointer argument. -/
theorem HostExecution.readByteCount_write {execution : HostExecution} {context : HostReadContext}
    {length : BitVec 64} (kind : execution.kind = .write)
    (observed : context.register 12#5 = some length) :
    execution.readByteCount context = length.toNat := by
  simp [readByteCount, readSpans?, kind, observed]

/-- The resource observer counts the complete emitted byte list. -/
theorem HostExecution.writeByteCount_eq {execution : HostExecution} {write : HostMemoryWrite}
    (emitted : execution.effect.write = some write) : execution.writeByteCount = write.bytes.length := by
  simp [writeByteCount, writeSpans, emitted]

end SP1Clean.Model.Core
