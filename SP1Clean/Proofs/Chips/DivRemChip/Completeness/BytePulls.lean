import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds

/-! # `DivRemChip` — the simple byte-range pulls (factored for dedup + parallel compilation)

The chip's tail emits 26 single-cell `byteChannel` range lookups (`pabsc`/`pabsr`/`pq`/`pr`/`pctq`/
`pe2r1`/`pe2q1`): each is a gated lookup `opcode = 6` (Range) on one witnessed cell. `completeness`
discharges each by rewriting the cell to its populate value and `convert byteRow_range16 … using 2`.
That `convert` is a deep defeq; factoring it into one parametric lemma collapses 26 of them into a
single proof (and moves it off the heavy `completeness` budget). -/

namespace SP1Clean.DivRemChip.BytePulls

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- A gated single-cell byte Range lookup: the cell `env.get idx` equals a populate value `v` with
`v.val < 2^16`, so the (`gate`-conditioned) `byteChannel` guarantee holds. The `gate` is irrelevant
(the lookup is unconditional once the row is committed), so it is left abstract. -/
lemma bytePullSimple {gate : Prop} {env : ProverEnvironment (ZMod p)} {idx : ℕ} {v : ZMod p}
    (hpin : env.get idx = v) (hb : v.val < 2 ^ 16) :
    gate → byteChannel.Guarantees
      ({ opcode := 6, a := env.get idx, b := 16, c := 0 } : ByteRow (ZMod p)) env.data :=
  fun _ => by rw [hpin]; convert byteRow_range16 hb using 2

end SP1Clean.DivRemChip.BytePulls
