import SP1Clean.Model.Core.MemoryTable
import SP1Clean.Circuits.Gadgets.LtUnsigned

/-! # Exportable witnesses for address-based memory reads

The fixed interval selector and unsigned-comparison columns use Clean's field-sorted witness
expressions. Four-limb comparisons retain the exclusive endpoint `2^48` and avoid truncating a
field value to a machine integer. Evaluation is related to the existing semantic interval search.
-/

namespace SP1Clean.InitialMemoryLookup

open Circuit Witgen Model.Core Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The eight unsigned-comparison cells, using the existing field-sorted limb scan. -/
def comparisonFE (left right : Word (FExpr (ZMod p))) :
    Circuits.Types.LtOperationUnsigned (FExpr (ZMod p)) :=
  ⟨⟨LtOperationUnsigned.compareBitF left right⟩,
    Vector.ofFn (LtOperationUnsigned.flagsF left right),
    LtOperationUnsigned.notEqInvF left right,
    Vector.ofFn (LtOperationUnsigned.comparisonLimbsF left right)⟩

omit [Fact (2 ^ 17 < p)] in
/-- Comparison witnesses evaluate to the native population function. -/
theorem comparisonFE_eval (ctx : Ctx (ZMod p)) (left right : Word (FExpr (ZMod p)))
    (a b : Word (ZMod p))
    (ha : ∀ (i : ℕ) (_ : i < 4), left[i].eval ctx = a[i])
    (hb : ∀ (i : ℕ) (_ : i < 4), right[i].eval ctx = b[i]) :
    Witgen.eval ctx (comparisonFE left right) = LtOperationUnsigned.populate a b := by
  have scan := LtOperationUnsigned.scanF_eval ctx left right a b ha hb
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [comparisonFE, circuit_norm, ProvableStruct.toComponents,
    ProvableStruct.fromComponents, Witgen.eval_fields', Vector.map_ofFn]
  unfold LtOperationUnsigned.populate
  congr 1
  · exact congrArg Circuits.Types.U16CompareOperation.mk scan.2.2.2
  · ext i hi
    simpa only [Vector.getElem_ofFn, Function.comp_apply] using scan.2.1 ⟨i, hi⟩
  · exact scan.2.2.1
  · ext i hi
    simpa only [Vector.getElem_ofFn, Function.comp_apply] using scan.1 ⟨i, hi⟩

/-- Unsigned word comparison as a condition in the existing witness IR. -/
private def lessThanFE (left right : Word (FExpr (ZMod p))) : BExpr (ZMod p) :=
  .flt (LtOperationUnsigned.comparisonLimbsF left right 0)
    (LtOperationUnsigned.comparisonLimbsF left right 1)

private theorem lessThanFE_eval (ctx : Ctx (ZMod p))
    (left right : Word (FExpr (ZMod p))) (a b : Word (ZMod p))
    (ha : ∀ (i : ℕ) (_ : i < 4), left[i].eval ctx = a[i])
    (hb : ∀ (i : ℕ) (_ : i < 4), right[i].eval ctx = b[i])
    (aBound : Word.isU64 a) (bBound : Word.isU64 b) :
    (lessThanFE left right).eval ctx = decide (Word.toNat a < Word.toNat b) := by
  have scan := (LtOperationUnsigned.scanF_eval ctx left right a b ha hb).2.2.2
  have semantic := (LtOperationUnsigned.result_semantic
    (LtOperationUnsigned.spec_populate aBound bBound) rfl).1
  have bit := scan.trans semantic
  change (if (lessThanFE left right).eval ctx then (1 : ZMod p) else 0) =
    (if Word.toNat a < Word.toNat b then 1 else 0) at bit
  cases condition : (lessThanFE left right).eval ctx <;>
    by_cases order : Word.toNat a < Word.toNat b <;> simp_all

/-- Containment compares full four-limb words against the two fixed endpoints. -/
private def containsFE (address : Word (FExpr (ZMod p))) (interval : MemoryInterval) :
    BExpr (ZMod p) :=
  let row := interval.encode (p := p)
  .and (.not (lessThanFE address (row.lower.map FExpr.const)))
    (lessThanFE address (row.upper.map FExpr.const))

private theorem containsFE_eval (ctx : Ctx (ZMod p)) (address : Word (FExpr (ZMod p)))
    (value : Word (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = value[i])
    (bounded : Word.isU64 value) (interval : MemoryInterval)
    (lower : interval.lower < 2 ^ 64) (upper : interval.upper < 2 ^ 64) :
    (containsFE address interval).eval ctx = decide (interval.Contains (Word.toNat value)) := by
  have low := lessThanFE_eval ctx address ((interval.encode (p := p)).lower.map FExpr.const)
    value (interval.encode (p := p)).lower evaluates
    (by intro i hi; simp only [Vector.getElem_map, FExpr.eval])
    bounded (isU64_bitVecToWord _)
  have high := lessThanFE_eval ctx address ((interval.encode (p := p)).upper.map FExpr.const)
    value (interval.encode (p := p)).upper evaluates
    (by intro i hi; simp only [Vector.getElem_map, FExpr.eval])
    bounded (isU64_bitVecToWord _)
  have endpoints := interval.encode_endpoints (p := p) lower upper
  change (!(lessThanFE address _).eval ctx && (lessThanFE address _).eval ctx) = _
  rw [low, high, endpoints.1, endpoints.2]
  by_cases lowBound : interval.lower ≤ Word.toNat value <;>
    by_cases highBound : Word.toNat value < interval.upper <;>
      simp_all [MemoryInterval.Contains]
  exact decide_eq_false_iff_not.mpr (by omega)

/-- Select one fixed-row field, defaulting to zero outside every interval. -/
private def selectFE (address : Word (FExpr (ZMod p)))
    (field : MemoryInterval → ZMod p) : List MemoryInterval → FExpr (ZMod p)
  | [] => 0
  | interval :: rest => .ite (containsFE address interval) (.const (field interval))
      (selectFE address field rest)

private theorem selectFE_eval (ctx : Ctx (ZMod p)) (address : Word (FExpr (ZMod p)))
    (value : Word (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = value[i])
    (bounded : Word.isU64 value) (field : MemoryInterval → ZMod p)
    (rows : List MemoryInterval)
    (bounds : ∀ interval ∈ rows, interval.lower < 2 ^ 64 ∧ interval.upper < 2 ^ 64) :
    (selectFE address field rows).eval ctx =
      ((rows.find? fun interval => decide (interval.Contains (Word.toNat value))).map field).getD 0 := by
  induction rows with
  | nil => rfl
  | cons interval rest ih =>
      have endpoints := bounds interval (List.mem_cons_self ..)
      have condition := containsFE_eval ctx address value evaluates bounded interval
        endpoints.1 endpoints.2
      have tail := ih (fun row member => bounds row (List.mem_cons_of_mem _ member))
      by_cases inside : interval.Contains (Word.toNat value)
      · simp [selectFE, FExpr.eval, condition, inside]
      · simp [selectFE, FExpr.eval, condition, inside, tail]

/-- The selected interval, encoded directly as typed Clean witness expressions. -/
def intervalFE (memory : ByteMemory) (limit : ℕ) (address : Word (FExpr (ZMod p))) :
    MemoryIntervalRow (FExpr (ZMod p)) :=
  ⟨Vector.ofFn fun i => selectFE address (fun interval => (interval.encode (p := p)).lower[i])
      (memory.intervals limit),
    Vector.ofFn fun i => selectFE address (fun interval => (interval.encode (p := p)).upper[i])
      (memory.intervals limit),
    selectFE address (fun interval => (interval.encode (p := p)).value) (memory.intervals limit)⟩

/-- Typed witness evaluation selects exactly the semantic interval row. -/
theorem intervalFE_eval (ctx : Ctx (ZMod p)) (memory : ByteMemory) (limit : ℕ)
    (limitBound : limit < 2 ^ 64) (address : Word (FExpr (ZMod p))) (value : Word (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = value[i])
    (bounded : Word.isU64 value) (interval : MemoryInterval)
    (found : memory.intervalAt? limit (Word.toNat value) = some interval) :
    Witgen.eval ctx (intervalFE memory limit address) = interval.encode := by
  have bounds (row : MemoryInterval) (member : row ∈ memory.intervals limit) :
      row.lower < 2 ^ 64 ∧ row.upper < 2 ^ 64 := by
    have endpoints := memory.intervals_bounds limit row member
    exact ⟨lt_of_le_of_lt (endpoints.1.trans endpoints.2) limitBound,
      lt_of_le_of_lt endpoints.2 limitBound⟩
  have fieldEval (field : MemoryInterval → ZMod p) :
      (selectFE address field (memory.intervals limit)).eval ctx = field interval := by
    rw [selectFE_eval ctx address value evaluates bounded field _ bounds]
    change ((memory.intervalAt? limit (Word.toNat value)).map field).getD 0 = _
    rw [found]
    rfl
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [intervalFE, circuit_norm, ProvableStruct.toComponents,
    ProvableStruct.fromComponents, Witgen.eval_fields', Vector.map_ofFn]
  congr 1
  · ext i hi
    simpa only [Vector.getElem_ofFn, Function.comp_apply, MemoryInterval.encode] using
      fieldEval (fun row => (row.encode (p := p)).lower[i])
  · ext i hi
    simpa only [Vector.getElem_ofFn, Function.comp_apply, MemoryInterval.encode] using
      fieldEval (fun row => (row.encode (p := p)).upper[i])
  · exact fieldEval (fun row => (row.encode (p := p)).value)

omit [Fact (2 ^ 17 < p)] in
/-- Comparison cells depend only on the evaluated operands, not other prover state. -/
theorem comparisonFE_congr (ctx ctx' : Ctx (ZMod p))
    (left right left' right' : Word (FExpr (ZMod p)))
    (ha : ∀ (i : ℕ) (_ : i < 4), left[i].eval ctx = left'[i].eval ctx')
    (hb : ∀ (i : ℕ) (_ : i < 4), right[i].eval ctx = right'[i].eval ctx') :
    Witgen.eval ctx (comparisonFE left right) = Witgen.eval ctx' (comparisonFE left' right') := by
  rw [comparisonFE_eval ctx left right (left.map (FExpr.eval ctx)) (right.map (FExpr.eval ctx))
    (by intro i hi; simp only [Vector.getElem_map])
    (by intro i hi; simp only [Vector.getElem_map])]
  symm
  apply comparisonFE_eval
  · intro i hi
    simpa only [Vector.getElem_map] using (ha i hi).symm
  · intro i hi
    simpa only [Vector.getElem_map] using (hb i hi).symm

omit [Fact (2 ^ 17 < p)] in
private theorem lessThanFE_congr (ctx ctx' : Ctx (ZMod p))
    (left right left' right' : Word (FExpr (ZMod p)))
    (ha : ∀ (i : ℕ) (_ : i < 4), left[i].eval ctx = left'[i].eval ctx')
    (hb : ∀ (i : ℕ) (_ : i < 4), right[i].eval ctx = right'[i].eval ctx') :
    (lessThanFE left right).eval ctx = (lessThanFE left' right').eval ctx' := by
  have scan := (LtOperationUnsigned.scanF_congr ctx ctx' left right ha hb).1
  simp only [lessThanFE, BExpr.eval, scan 0, scan 1]

omit [Fact (2 ^ 17 < p)] in
private theorem containsFE_congr (ctx ctx' : Ctx (ZMod p))
    (address address' : Word (FExpr (ZMod p)))
    (same : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = address'[i].eval ctx')
    (interval : MemoryInterval) :
    (containsFE address interval).eval ctx = (containsFE address' interval).eval ctx' := by
  have constant (word : Word (ZMod p)) (i : ℕ) (hi : i < 4) :
      (word.map FExpr.const)[i].eval ctx = (word.map FExpr.const)[i].eval ctx' := by
    simp only [Vector.getElem_map, FExpr.eval]
  have low := lessThanFE_congr ctx ctx' address _ address' _ same
    (constant (interval.encode (p := p)).lower)
  have high := lessThanFE_congr ctx ctx' address _ address' _ same
    (constant (interval.encode (p := p)).upper)
  change (!(lessThanFE address _).eval ctx && (lessThanFE address _).eval ctx) = _
  rw [low, high]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem selectFE_congr (ctx ctx' : Ctx (ZMod p))
    (address address' : Word (FExpr (ZMod p)))
    (same : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = address'[i].eval ctx')
    (field : MemoryInterval → ZMod p) (rows : List MemoryInterval) :
    (selectFE address field rows).eval ctx = (selectFE address' field rows).eval ctx' := by
  induction rows with
  | nil => rfl
  | cons interval rest ih =>
      simp only [selectFE, FExpr.eval, containsFE_congr ctx ctx' address address' same interval, ih]

omit [Fact (2 ^ 17 < p)] in
/-- Interval witnesses read only the supplied address, including under changes to prover data. -/
theorem intervalFE_congr (ctx ctx' : Ctx (ZMod p)) (memory : ByteMemory) (limit : ℕ)
    (address address' : Word (FExpr (ZMod p)))
    (same : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = address'[i].eval ctx') :
    Witgen.eval ctx (intervalFE memory limit address) =
      Witgen.eval ctx' (intervalFE memory limit address') := by
  simp only [intervalFE, Witgen.StructEval.eval_eq_eval, circuit_norm, ProvableStruct.toComponents,
    ProvableStruct.fromComponents, Witgen.eval_fields', Vector.map_ofFn]
  refine ⟨?_, ?_, ?_⟩
  · ext i hi
    simp only [Vector.getElem_ofFn, Function.comp_apply]
    exact selectFE_congr ctx ctx' address address' same _ _
  · ext i hi
    simp only [Vector.getElem_ofFn, Function.comp_apply]
    exact selectFE_congr ctx ctx' address address' same _ _
  · exact selectFE_congr ctx ctx' address address' same _ _

end SP1Clean.InitialMemoryLookup
