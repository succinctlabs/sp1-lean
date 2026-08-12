import Clean.Circuit.Basic
import Clean.Circuit.Explicit

/-! # `witnessVectorIR` — the vector witness combinator used by every chip row

Clean offers two vector-shaped witness entry points, and neither is quite what a chip row wants:

* `Circuit.witnessVector m out` has exactly the right *shape* — it emits `.witness m …`, so the
  cell count appears literally in the operation list — but its payload is a bare `VExpr`, with no
  room for the shared `letU` steps a carry chain needs;
* `witnessIR (fields m) ir` accepts a full `WitgenIR`, but emits `.witness (size (fields m)) …`.
  `size (fields m)` is *definitionally* `m` yet not *syntactically* `m`, so it survives into the
  offset arithmetic of every later operation. Structural proofs that compute a subcircuit's offset
  by `simp only` (the chip faithfulness anchors, `Soundness/TypedMemorySelectors.lean`, the
  `exposedChannels_eq` obligations) then stall on `offset + size (fields 2) + size (fields 1)`
  instead of `offset + 3`.

`witnessVectorIR` is the combination: a full `WitgenIR` payload in the literal-`m` shape. That makes
the witgen cutover a payload swap for the structural layer — `.witness m (.native f)` becomes
`.witness m (.ir …)`, and every offset computation downstream is unchanged.

## Upstream

Destined for `Clean/Circuit/Basic.lean`, beside `Circuit.witnessVector`, of which this is the
`WitgenIR`-taking generalisation. It carries no witness semantics of its own — `witnessVector m out`
is exactly `witnessVectorIR m (.ir [] out)` — so the merge is additive. Declared here in the
namespace it would occupy upstream, so acceptance is a deletion plus dropping the import. -/

namespace Circuit

variable {F : Type} [FiniteField F]

/-- Witness a vector of `m` field elements from a witness-IR program, keeping the cell count literal
in the emitted operation (see the module docstring). -/
@[circuit_norm]
def witnessVectorIR (m : ℕ) (ir : Witgen.WitgenIR F m) : Circuit F (Vector (Expression F) m) :=
  fun offset => (varFromOffset (fields m) offset, [.witness m ir])

/-- Explicit operations/length/output, so `elaborate_circuit` and the structural simp sets see this
combinator exactly as they saw `witnessVectorNative` — with the cell count literal. Mirrors Clean's
own instance for `witnessVector`. -/
instance {k : ℕ} : ExplicitCircuits (F := F) (witnessVectorIR k) where
  output _ n := varFromOffset (fields k) n
  localLength _ _ := k
  operations ir n := [.witness k ir]
  channelsWithGuarantees _ _ := []

attribute [explicit_circuit_no_unfold] witnessVectorIR

end Circuit

-- Mirrors Clean's own `export Circuit (witnessVar witnessField witnessVector …)`, so call sites
-- write `witnessVectorIR` unqualified exactly as they write `witnessVector`.
export Circuit (witnessVectorIR)
