import SP1Clean.Extracted.ExtractionDSL
import SP1Clean.Foundations.InteractionProjection
import SP1Clean.Foundations.ByteTable

/-! # Syntactic projection of the EXTRACTED interaction ADT to `LookupAccess`

The extracted-side counterpart of `AbstractInteraction.toAccess` (`Foundations/InteractionProjection.lean`).
The extracted `Interaction (ZMod p)` (the SP1-oracle bus vocabulary, `Extracted/ExtractionDSL.lean`)
projected to the **same** `LookupAccess` tuple `(kind, table, argvals, signedmult)` that the Clean
circuit's emitted interactions project to. Equality of the two `.map toAccess` lists is the *syntactic*
faithfulness bridge: it compares the channel, the message arg **values**, and the **signed
multiplicity/direction** — not byte semantics (unlike `Interaction.toProp`, which collapses every
non-byte interaction to `True` and reasons about `op.constrain`/`< 65536`).

## Sign convention (the one modeling gap the syntactic comparison surfaces)

Clean models the byte lookup as a **pull** — `byteChannel.pullIf is_real` → `pullIf`, with
multiplicity `-is_real` on `byteChannel.toRaw` (`Operations/AddOperation/Extracted.lean`). SP1's
`send_byte` is the dual **source** endpoint (`Extracted/AddOperation.lean`: `⟨.send, .byte 6 v 16 0,
is_real⟩`). Same physical lookup, opposite source/sink convention — so the `.byte` arm records the
**sink** sign `signedVal (-mult)`, matching Clean's pull, while the message tuple `[op.idx, a, b, c]`
already matches field-for-field. The dynamic buses (State/Memory/Program) use the natural `Dir.sign`
(`pushIf` send `+mult`, receive `-mult`) — byte is the sole *pull* bus
(`Foundations/Channels.lean` `byteChannel` docstring), hence its hardcoded `-mult`. -/

namespace SP1Clean.Extracted

open SP1Clean

variable {p : ℕ}

/-- The signed multiplicity of an extracted interaction by direction: `.send → +mult`,
`.receive → -mult` (sends positive, receives negative, matching the LogUp bus `InteractionBus.lean`). -/
def Dir.sign (d : Dir) (mult : ZMod p) : ZMod p :=
  match d with
  | .send => mult
  | .receive => -mult

/-- Project one extracted interaction to its `LookupAccess` — the val-image `(kind, table, argvals,
signedmult)`, the extracted-side mirror of `AbstractInteraction.toAccess`. The `.byte` arm uses the
sink sign `signedVal (-mult)` (Clean's pull convention); the dynamic buses use `Dir.sign`. -/
def Interaction.toAccess (intr : Interaction (ZMod p)) : LookupAccess :=
  match intr.payload with
  | .byte op a b c =>
      (InteractionKind.Byte, "SP1Byte", [op.idx, a.val, b.val, c.val], signedVal (-intr.mult))
  | .state a b c d e =>
      (InteractionKind.State, "SP1State",
        [a.val, b.val, c.val, d.val, e.val], signedVal (intr.dir.sign intr.mult))
  | .memory a b c d e f g h i =>
      (InteractionKind.Memory, "SP1Memory",
        [a.val, b.val, c.val, d.val, e.val, f.val, g.val, h.val, i.val],
        signedVal (intr.dir.sign intr.mult))
  | .program a b c op d e f g h i j k l m n o =>
      (InteractionKind.Program, "SP1Program",
        [a.val, b.val, c.val, op, d.val, e.val, f.val, g.val, h.val,
         i.val, j.val, k.val, l.val, m.val, n.val, o.val],
        signedVal (intr.dir.sign intr.mult))

/-- The `.byte` arm of `Interaction.toAccess` as a `rfl`-`simp` lemma (independent of the `Dir`, which
the byte arm ignores — it records the sink sign `-mult`). Drives the syntactic faithfulness proofs. -/
@[simp] lemma Interaction.toAccess_byte (op : ByteOpcode) (a b c mult : ZMod p) (d : Dir) :
    (⟨d, .byte op a b c, mult⟩ : Interaction (ZMod p)).toAccess
      = (InteractionKind.Byte, "SP1Byte", [op.idx, a.val, b.val, c.val], signedVal (-mult)) :=
  rfl

end SP1Clean.Extracted
