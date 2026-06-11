import Clean.Circuit.Basic

/-! # Circuit-as-trace-generator: derive a chip's trace rows from its own circuit definition.

In Clean, witness generation is part of the circuit *language*: a chip's `main` interleaves
constraints with `.witness m (fun env => …)` operations, so the same program elaborates to both the
constraint system and the witness generator. This file makes that operational ("compiler-style"
trace generation): given a chip's `main` and one row's concrete input column values, we

1. run the circuit's own witness closures in emission order via `FlatOperation.dynamicWitnesses`
   (through `Circuit.proverEnvironment`), threading the environment so later closures read earlier
   witnesses — indices `< inputs.length` read the inputs, indices `≥ inputs.length` read accumulated
   local witnesses;
2. evaluate `main`'s *output struct* (the chip's extracted cols assembled from input vars and
   witness vars) under the resulting environment — the output layout **is** the row layout.

So a full trace row is *derived* from the circuit definition; nothing about column order, witness
formulas, or wiring is restated. `generateTrace` then assembles a whole matrix: derived rows for the
real events plus all-zero padding rows, exactly mirroring SP1's `generate_trace` (which zero-fills
padding). The conformance anchors (`TraceGenTests/<Chip>TraceWitness.lean`) check the derived matrix
against whole traces dumped from SP1's **real** `generate_trace`.

Everything here is computable and axiom-clean; `native_decide` appears only in the anchor files.

Reasoning hook (not used yet): for circuits satisfying `Circuit.ComputableWitnesses`, the witness
segment of the environment built here agrees with `Operations.localWitnesses` at the fixpoint
environment (`Circuit.proverEnvironment_usesLocalWitnesses` in `Clean.Circuit.Theorems`) — the
bridge from this conformance layer to the chips' completeness theorems, if we later upgrade the
sampled conformance into an all-inputs statement. -/

namespace SP1Clean.TraceGenTests

variable {F : Type} [Field F]

/-- Derive one trace row from a circuit: run `main`'s own witness closures on the given input
column values (env-threaded, via `Circuit.proverEnvironment`), then evaluate `main`'s output struct
under the final environment. The circuit is the row generator; `inputs` is the flattened
(`toElements`-ordered) input column list and **must** have length `size Input` — the input
variables `0 … size Input - 1` read it positionally, and local witnesses are allocated after it. -/
def circuitTraceRow (Input : TypeMap) [ProvableType Input] {Output : TypeMap} [ProvableType Output]
    (main : Var Input F → Circuit F (Var Output F)) (inputs : List F)
    (hint : ProverHint F := ProverHint.empty F) : List F :=
  let circ := main (varFromOffset Input 0)
  let env := circ.proverEnvironment hint inputs
  let out : Output (Expression F) := circ.output inputs.length
  (toElements out).toList.map (Expression.eval env.toEnvironment)

/-- Assemble a whole trace matrix from a per-event row generator: derived rows for the real events,
then all-zero rows up to `height` — mirroring SP1's `generate_trace`, which zero-fills padding. -/
def generateTrace {α : Type} (rowGen : α → List F) (events : List α) (height width : ℕ) :
    List (List F) :=
  events.map rowGen ++ List.replicate (height - events.length) (List.replicate width 0)

/-- Project a row onto the kept `[lo, hi)` column ranges. The masked anchors (chips whose variant
flags are witnessed as constant zeros, so the flag columns cannot conform) compare
`keepCols`-projected matrices; the keep list doubles as the per-chip column-mapping artifact. -/
def keepCols {α : Type} (keep : List (ℕ × ℕ)) (row : List α) : List α :=
  keep.flatMap fun (lo, hi) => (row.drop lo).take (hi - lo)

end SP1Clean.TraceGenTests
