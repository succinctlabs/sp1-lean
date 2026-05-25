import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # TrustMode scaffolding (mirror of Rust `trait TrustMode`)

Upstream Rust SP1 parametrizes every chip's `Cols` struct over
`M: TrustMode` and stores mode-dependent columns in
`adapter_cols: M::AdapterCols<T>`
(`sp1/crates/core/machine/src/lib.rs:47-150`).

This file is the Lean mirror: an inductive `TrustMode` with constructors
`UserMode` and `SupervisorMode`, the user-mode adapter payload
`UserModeReaderCols` (just `is_trusted : T`, matching Rust line 80), an
`EmptyCols T` for SupervisorMode (Rust line 61), and the
`AdapterCols : TrustMode → Type → Type` selector that plays the role of
Rust's associated type `M::AdapterCols<T>`.

The repo currently only verifies `UserMode`; `SupervisorMode` is
scaffolded so future trusted-mode chips slot in without re-shaping every
Cols. The other four `TrustMode` associated types in Rust
(`SyscallInstrCols`, `SliceProtCols`, `AluX0SelectorCols`,
`TrapCodeCols`) are not modeled here — they're only used by chips not
currently in SP1Clean. -/

namespace SP1Clean

/-- Names match the Rust trait implementors:
- `UserMode` (Rust `lib.rs:143`) — untrusted user programs; per-row
  `is_trusted` flag distinguishes trusted bootloader rows from
  untrusted user-program rows.
- `SupervisorMode` (Rust `lib.rs:69`) — always-trusted; no extra columns. -/
inductive TrustMode where
  | UserMode
  | SupervisorMode
deriving DecidableEq, Repr

/-- Mirrors Rust `UserModeReaderCols<T>`
(`sp1/crates/core/machine/src/lib.rs:78-82`). The single column controls
whether the reader emits its trusted-program lookup at this row. -/
@[ext]
structure UserModeReaderCols (T : Type) where
  is_trusted : T
deriving ProvableStruct

/-- Mirrors Rust `EmptyCols<T>` (`sp1/crates/core/machine/src/lib.rs:56-61`).
Used by `SupervisorMode` for all five `M::*Cols<T>` associated types.
No `deriving ProvableStruct` here — the deriving handler requires at
least one field. SupervisorMode chips don't currently exist in
SP1Clean; when they do, a manual `ProvableStruct EmptyCols` instance
will be needed. -/
structure EmptyCols (T : Type) where

/-- The `M::AdapterCols<T>` associated type. `abbrev` so that
`deriving ProvableStruct` on chip Cols can flatten through this when `M`
is instantiated to a concrete constructor. -/
abbrev AdapterCols : TrustMode → Type → Type
  | .UserMode,       T => UserModeReaderCols T
  | .SupervisorMode, T => EmptyCols T

end SP1Clean
