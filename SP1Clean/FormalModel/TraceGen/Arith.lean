import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Native.Operations.AddOperation.Populate

/-! # Trace generation — the `AddOperation` witness at built words

The second module split out of `Readers.lean` for a layering reason, and the same one
`Memory.lean` records: `Readers.lean` proves the reader-family contracts while importing nothing
below `FormalModel/`, and this file needs `Native/Operations/AddOperation/Populate.lean` — the
witness generator the two **jump** chips run over their operands. Keeping it here confines that
import to one module.

The content is one theorem and its two convenience forms. `AddOperation.populate` is SP1's
limb-wise 64-bit addition, and the builder of `Inputs.lean` commits every 64-bit quantity as
`wordOfNat`; so the witness a jump chip generates for `pc + imm` or `rs1 + imm` is *itself* a built
word, of the plain-`ℕ` sum:

```
populate (wordOfNat a) (wordOfNat b) = wordOfNat ((a + b) % 2 ^ 64)
```

That one identity is what turns each jump chip's three target obligations — the two
`value[3] = 0` gates and the `Range(value[0] / 4, 14)` alignment pull — into the plain-`ℕ`
statements `JTypeEvent.JalTargets` / `ITypeEvent.JalrTargets` make about the executor, via the
`wordOfNat_three_eq_zero` / `wordOfNat_div_four_val_lt` lemmas of `Readers.lean`.

The proof does not re-derive the carry chain: it goes through the gadget's own
`AddOperation.spec_populate` (the result is a u64 whose `toBitVec64` is the `BitVec` sum) and back
down through `Word.toNat`, which is injective on u64 words (`word_eq_of_toNat_eq`). -/

namespace SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Four-cell eta for the `Word` carrier: the word a chip rebuilds limb-by-limb out of a reader
block *is* the block's word. (The jump chips spell their `AddOperation` operands this way.) -/
lemma word_eta (w : Word (ZMod p)) : (#v[w[0], w[1], w[2], w[3]] : Word (ZMod p)) = w := by
  refine Vector.ext (fun i hi => ?_)
  interval_cases i <;> rfl

omit [Fact (2 ^ 24 < p)] in
/-- **`Word.toNat` is injective on u64 words.** Each limb is a `< 2 ^ 16` residue, so the base-2^16
sum determines them, and `ZMod.val` is injective. -/
lemma word_eq_of_toNat_eq {w v : Word (ZMod p)} (hw : Word.isU64 w) (hv : Word.isU64 v)
    (h : Word.toNat w = Word.toNat v) : w = v := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hw
  obtain ⟨g0, g1, g2, g3⟩ := Word.lt_cases_of_isU64 hv
  rw [Word.toNat_def, Word.toNat_def] at h
  have hinj : ∀ x y : ZMod p, x.val = y.val → x = y := fun x y hxy => ZMod.val_injective _ hxy
  refine Vector.ext (fun i hi => ?_)
  interval_cases i
  · exact hinj _ _ (by omega)
  · exact hinj _ _ (by omega)
  · exact hinj _ _ (by omega)
  · exact hinj _ _ (by omega)

/-- **The `AddOperation` witness at two built words is the built word of the sum.** SP1's limb-wise
64-bit addition, run on the committed forms of two naturals, commits the natural sum truncated to
64 bits — so a jump chip's witnessed target word is `wordOfNat` of the executor's own wrapping
sum. -/
theorem populate_wordOfNat (a b : ℕ) :
    AddOperation.populate (wordOfNat (p := p) a) (wordOfNat (p := p) b)
      = wordOfNat ((a + b) % 2 ^ 64) := by
  obtain ⟨hU, hbv⟩ := AddOperation.spec_populate (wordOfNat_isU64 (p := p) a)
    (wordOfNat_isU64 (p := p) b) 1 rfl
  simp only at hU hbv
  refine word_eq_of_toNat_eq hU (wordOfNat_isU64 _) ?_
  have h := congrArg BitVec.toNat hbv
  rw [BitVec.toNat_add, Word.toBitVec64_toNat hU,
    Word.toBitVec64_toNat (wordOfNat_isU64 (p := p) a),
    Word.toBitVec64_toNat (wordOfNat_isU64 (p := p) b), wordOfNat_toNat, wordOfNat_toNat] at h
  rw [h, wordOfNat_toNat, Nat.mod_mod, ← Nat.add_mod]

/-- The literal `4` addend the two jump chips add to the program counter is the built word of `4`
(SP1's `op_a_operation` computes the link address `pc + 4`). -/
lemma wordOfNat_four : (#v[4, 0, 0, 0] : Word (ZMod p)) = wordOfNat 4 := by
  have hp : 2 ^ 24 < p := Fact.out
  refine Vector.ext (fun i hi => ?_)
  interval_cases i
  · rw [wordOfNat_zero]; norm_num
  · rw [wordOfNat_one]; norm_num
  · rw [wordOfNat_two]; norm_num
  · rw [wordOfNat_three]; norm_num

/-- The jump chips' `pc + imm` witness: the program-counter operand is the three committed `pc`
limbs padded with a zero high limb, which `cpuStateCols_pcWord_eq` identifies with `wordOfNat pc`.
Serves both `Jal`'s jump target (`imm = op_b`) and both chips' link address (`imm = 4`). -/
theorem populate_pcWord {clk pc : ℕ} (h : pc < 2 ^ 48) (m : ℕ) :
    AddOperation.populate
        (#v[(cpuStateCols (p := p) clk pc).pc[0], (cpuStateCols (p := p) clk pc).pc[1],
          (cpuStateCols (p := p) clk pc).pc[2], 0] : Word (ZMod p)) (wordOfNat m)
      = wordOfNat ((pc + m) % 2 ^ 64) := by
  rw [cpuStateCols_pcWord_eq h, populate_wordOfNat]

end SP1Clean.TraceGen
