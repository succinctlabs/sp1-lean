import SP1Clean.Model.Core.AddressRange

/-! # The native SP1 range instance

These bounds match the pinned SP1 platform and current native encodings. The Sail snapshot
contains bytes below the guest window too; guest access permission and memory-map presence are
different notions. Changing this instance requires new Sail/encoding agreement, not only new data.
-/

namespace SP1Clean.Model.Core.NativeLayout

/-- Pinned SP1 guest RAM/ROM window, also used by the configured Sail PMA. -/
abbrev guestMemory : AddressRange := ⟨2 ^ 16, 2 ^ 48⟩

/-- Exact byte-key domain of the complete Sail snapshot realization. -/
abbrev sailMemory : AddressRange := ⟨0, 2 ^ 48⟩

/-- Two 24-bit clock limbs. Individual accesses must also fit their local limb window. -/
abbrev clocks : AddressRange := ⟨0, 2 ^ 48⟩

/-- MAX_SHARD_SIZE from the released executor's opts.rs, measured in clock ticks.
This constant does not assert that an existing native ensemble enforces the limit. -/
abbrev maxShardTicks : ℕ := 2 ^ 24

theorem guestMemory_valid : guestMemory.Valid := by decide
theorem sailMemory_valid : sailMemory.Valid := by decide
theorem clocks_valid : clocks.Valid := by decide

end SP1Clean.Model.Core.NativeLayout
