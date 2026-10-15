import SP1Clean.Model.Core.Boot
import SP1Clean.Model.Semantics.MicroTime

/-! # Native memory-boundary records

The initial provider's public contract fixes the value at the actual decoded Memory-bus location
to the native boot state. Address canonicality and zero time are conclusions of the provider,
not assumptions supplied by a trace consumer. Final records share the canonical address contract;
their last-access meaning and both inventories' uniqueness are global balance arguments.
-/

namespace SP1Clean.MemoryBoundary

open SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime]

/-- The field encoding of a Memory record's address as a full word. -/
def address {R : Type} [Zero R] (message : MemoryMsg R) : Word R :=
  #v[message.addr0, message.addr1, message.addr2, 0]

/-- The encoded key is range checked and equals the decoded location's canonical address. -/
def CanonicalKey (message : MemoryMsg (ZMod p)) : Prop :=
  Word.isU64 (address message) ∧
    Word.toNat (address message) = (MemoryMsg.locOf message).busAddress

/-- Shared address contract for initial and final boundary records. -/
def CanonicalSpec (message : MemoryMsg (ZMod p)) : Prop :=
  (MemoryMsg.locOf message).CanonicalAddress ∧ CanonicalKey message

/-- An authentic initial record at a canonical register or aligned RAM location. -/
def InitialSpec (image : ProgramImage) (message : MemoryMsg (ZMod p)) : Prop :=
  MemoryMsg.isU64 message ∧ MemoryMsg.ClkBound message ∧
    MemoryMsg.timeNat message = 0 ∧ (MemoryMsg.locOf message).CanonicalAddress ∧
      locContent image.initialSailState (MemoryMsg.locOf message) =
        some (Word.toBitVec64 message.value) ∧ CanonicalKey message

/-- Authentication also preserves the caller's semantic query address. This clause lets a
composed row constructor choose its ordered key before executing the provider's witnesses. -/
def InitialAtSpec (image : ProgramImage) (query : ℕ) (message : MemoryMsg (ZMod p)) : Prop :=
  InitialSpec image message ∧ Word.toNat (address message) = query

theorem InitialSpec.canonical {image : ProgramImage} {message : MemoryMsg (ZMod p)}
    (valid : InitialSpec image message) : CanonicalSpec message :=
  ⟨valid.2.2.2.1, valid.2.2.2.2.2⟩

private theorem aligned_cell (address : ℕ) (bound : address < 2 ^ 48)
    (aligned : address % 8 = 0) :
    (BitVec.ofNat 61 (address / 8)).toNat * 8 = address := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address / 8 < 2 ^ 61)]
  omega

/-- An aligned guest RAM key denotes its exact canonical Sail memory cell. -/
theorem ram_location_of_key (record : MemoryMsg (ZMod p)) (address : ℕ)
    (lower : 2 ^ 16 ≤ address) (upper : address < 2 ^ 48) (alignment : address % 8 = 0)
    (key : record.addr0.val + record.addr1.val * 2 ^ 16 + record.addr2.val * 2 ^ 32 = address) :
    (MemoryMsg.locOf record).CanonicalAddress ∧
      Word.toNat (SP1Clean.MemoryBoundary.address record) = (MemoryMsg.locOf record).busAddress ∧
      ∀ state, locContent state (MemoryMsg.locOf record) =
        ramWord64? state (BitVec.ofNat 64 address) := by
  have notRegister : ¬ (record.addr0.val < 32 ∧ record.addr1 = 0 ∧ record.addr2 = 0) := by
    rintro ⟨small, one, two⟩
    simp only [one, two, ZMod.val_zero, zero_mul, add_zero] at key
    omega
  let cell : RamCell := BitVec.ofNat 61 (address / 8)
  have aligned : cell.toNat * 8 = address := aligned_cell address upper alignment
  have decoded : MemoryMsg.locOf record = MemLoc.ram cell := by
    simp only [MemoryMsg.locOf, if_neg notRegister, key, cell]
  have base : cell.baseAddr = BitVec.ofNat 64 address :=
    congrArg (BitVec.ofNat 64) aligned
  refine ⟨?_, ?_, ?_⟩
  · rw [decoded]
    change 32 ≤ cell.toNat * 8 ∧ cell.toNat * 8 < 2 ^ 48
    rw [aligned]
    exact ⟨by omega, upper⟩
  · rw [decoded]
    change Word.toNat (SP1Clean.MemoryBoundary.address record) = cell.toNat * 8
    simpa only [SP1Clean.MemoryBoundary.address, Word.toNat, circuit_norm, ZMod.val_zero,
      zero_mul, add_zero, aligned] using key
  · intro state
    rw [decoded]
    change ramWord64? state cell.baseAddr = _
    rw [base]

/-- The local finalizer establishes only its canonical location. Values and timestamps are
grounded from the global Memory ledger after both inventories' locations are known. -/
def FinalSpec (message : MemoryMsg (ZMod p)) : Prop :=
  CanonicalSpec message

def FinalAtSpec (query : ℕ) (message : MemoryMsg (ZMod p)) : Prop :=
  FinalSpec message ∧ Word.toNat (address message) = query

end SP1Clean.MemoryBoundary
