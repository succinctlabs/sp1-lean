# U16 Composition Proof Guide for SP1-Lean

This guide helps future Claude Code instances complete U16 composition proofs in the SP1-Lean framework.

## Overview

U16 composition proofs verify that all field elements used in SP1 chip constraints respect 16-bit bounds (< 65536) when `is_real` is true. These proofs are crucial for ensuring the soundness of the zero-knowledge virtual machine implementation.

## Key Concepts

### 1. U16CompProp Definition
```lean
def SP1ConstraintList.U16CompProp (xs : SP1ConstraintList) : Prop :=
  List.Forall SP1Constraint.toU16CompProp xs
```

The `toU16CompProp` function extracts bounds requirements from constraints:
- For memory receive operations: proves limbs and addresses are < 65536
- For program send operations: proves PC components are bounded appropriately

### 2. Proof Structure Pattern

Most U16 composition proofs follow this structure:

```lean
def u16_composition : (constraints Main).U16CompProp := by
  -- 1. Expand definitions
  simp [SP1Constraint.toU16CompProp, constraints, List.Forall, 
        AddOperation.constraints, CPUState.constraints, ITypeReader.constraints]
  
  -- 2. Decompose constraints hypothesis
  simp [constraints] at cstrs
  obtain ⟨op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
  
  -- 3. Prove each conjunct
  refine ⟨?_, ?_, ?_⟩
```

## Step-by-Step Approach

### Step 1: Initial Setup
Always start with:
```lean
simp [SP1Constraint.toU16CompProp, constraints, List.Forall, ...]
```
This expands the goal into explicit bounds requirements.

### Step 2: Understand the Goal
Use the `lean_goal` tool to see the expanded goal. It typically has the form:
```
(¬Main[is_real_idx] = 0 → bounds₁) ∧ 
(¬Main[is_real_idx] = 0 → bounds₂) ∧ ...
```

### Step 3: Decompose Constraints
```lean
simp [constraints] at cstrs
obtain ⟨component1_cstrs, component2_cstrs, ...⟩ := cstrs
```

### Step 4: Prove Each Component
For each conjunct in the goal:
1. Introduce the `is_real` hypothesis: `intro h_is_real`
2. Expand relevant constraints: `simp [ComponentName.constraints, SP1Constraint.toProp, h_is_real, ...] at component_cstrs`
3. Extract facts using `extract_from_and`
4. Apply appropriate proof tactics

## Special Case: Handling Multiple Operation Types

### Bitwise Operations Pattern
Some chips (like Bitwise) support multiple operations selected by selector bits. The proof requires:

1. **Prove the selector constraint**:
```lean
-- First establish that the sum of selectors equals 1
have h_sum_eq_one : Main[48] + Main[49] + Main[50] = 1 := by
  cases what_is_this with
  | inl h => 
    -- Case when sum = 0 means no operation selected
    -- This leads to Main[31] = 0 and simplified constraints
    simp [h] at *
    -- The goal becomes trivial when no operation is selected
  | inr h => exact h
```

2. **Case analysis on exactly one selector**:
```lean
-- Prove exactly one selector is 1
have h_exactly_one : (Main[48] = 1 ∧ Main[49] = 0 ∧ Main[50] = 0) ∨ 
                     (Main[48] = 0 ∧ Main[49] = 1 ∧ Main[50] = 0) ∨ 
                     (Main[48] = 0 ∧ Main[49] = 0 ∧ Main[50] = 1) := by
  cases h_is_xor_is_bool <;> rename_i h48
  <;> cases h_is_or_is_bool <;> rename_i h49
  <;> cases h_is_and_is_bool <;> rename_i h50
  <;> simp [h48, h49, h50] at h_sum_eq_one
  <;> aesop
```

3. **Unified proof for all cases**:
```lean
-- Use rcases with same name for all branches
rcases h_exactly_one with h_everything | (h_everything | h_everything)

all_goals {
  obtain ⟨h_48, h_49, h_50⟩ := h_everything
  simp [h_48, h_49, h_50, ByteOpcode.ofNat, ...] at constraints
  -- Rest of proof is identical for all cases
}
```

## Common Proof Patterns

### Pattern 1: PC Bounds (Program Counter)
```lean
· intro h_is_real
  simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  refine ⟨?_, by extract_from_and reader_cstrs, by extract_from_and reader_cstrs⟩
  -- Prove PC + 4 ≤ 65536
  have h_pc_nat_mul4 : Main[pc_idx].val % 4 = 0 := by
    have h_pc_mul4 : Main[pc_idx] % 4 = 0 := by extract_from_and reader_cstrs
    have : (Main[pc_idx] % 4).val = Main[pc_idx].val % 4 := Fin.mod_val Main[pc_idx] 4
    rw [h_pc_mul4] at this
    simp at this
    exact this.symm
  have h_pc_nat_bound : Main[pc_idx].val < 65536 := by extract_from_and reader_cstrs
  have h_no_overflow : Main[pc_idx].val + 4 < BB := by
    calc Main[pc_idx].val + 4 < 65536 + 4 := by omega
    _ = 65540 := by norm_num
    _ < BB := by norm_num
  rw [Fin.le_iff_val_le_val]
  rw [Fin.val_add_eq_of_add_lt h_no_overflow]
  omega
```

### Pattern 2: Output Bounds
```lean
· intro h_is_real
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ...] at add_op_cstrs
  refine ⟨⟨by aesop, by aesop, by aesop, by aesop⟩, ?_⟩
  -- For register bounds
  simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, ...] at reader_cstrs
  calc 
    Main[reg_idx] < 32 := by extract_from_and reader_cstrs
    _             < 65536 := by trivial
```

### Pattern 3: Word Bounds (4-element vectors)
```lean
· intro h_is_real
  simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, ...] at reader_cstrs
  have h_is_u64 : Word.isU64 #v[Main[a], Main[b], Main[c], Main[d]] := by
    simp_all only
  -- Use Word.lt_cases_of_isU64 to extract individual bounds
  exact Word.lt_cases_of_isU64 h_is_u64
```

**Important**: Always use the `#v[...]` notation for Word vectors, and apply `Word.lt_cases_of_isU64` to convert from `Word.isU64` to individual element bounds.

## Key Tactics and Lemmas

### Essential Tactics
- `simp`: Simplifies definitions and unfolds constraints
- `extract_from_and`: Custom tactic to extract facts from nested conjunctions
- `aesop`: Automated proof search for simple goals
- `omega`: Linear arithmetic solver
- `calc`: Structured inequality proofs
- `trivial`: Solves simple goals like `32 < 65536`

### Important Lemmas
- `Fin.mod_val`: Relates Fin modulo to Nat modulo
- `Fin.le_iff_val_le_val`: Converts Fin inequalities to Nat
- `Fin.val_add_eq_of_add_lt`: Addition in Fin when no overflow
- `Word.isU64`: Proves all components of a word are < 65536
- `Word.lt_cases_of_isU64`: Converts `Word.isU64` to individual element bounds

## Debugging Tips

1. **Use lean_goal frequently**: Check the goal after each `simp` to understand what needs to be proven
2. **Check diagnostic messages**: Use `lean_diagnostic_messages` to catch type errors early
3. **Examine constraint structure**: Use `Read` tool to understand the constraint definitions
4. **Follow existing examples**: Look at completed proofs (e.g., Add/U16Composition.lean) as templates
5. **Set maxHeartbeats**: Use `set_option maxHeartbeats 400000` for complex proofs

## Common Pitfalls

1. **Wrong index assumptions**: Main vector indices vary between chips - always check the constraints file
2. **Missing imports**: Ensure all necessary tactics and definitions are imported
3. **Incomplete simplification**: Some definitions need explicit unfolding with `simp`
4. **Arithmetic overflow**: Always prove no overflow before using Fin arithmetic lemmas
5. **Forgetting the is_real = 0 case**: Some proofs split on whether the operation is real or padding
6. **Incorrect selector handling**: For multi-operation chips, must prove exactly one selector is active
7. **Not using `simp_all only`**: Sometimes `simp_all` with explicit `only` is needed instead of listing hypotheses
8. **Using let-bound variables for is_real**: Avoid `let is_real := ...` as it makes `simp` harder to work with
9. **Using `extract_from_and` when `simp_all only` works**: Prefer `simp_all only` for performance and reliability

## Example Chips and Their Patterns

- **Add/Sub chips**: Use RTypeReader, have 33 Main elements, straightforward single operation
- **Addi chip**: Uses ITypeReader, has 30 Main elements, includes immediate values
- **Bitwise chip**: 
  - Has 52 Main elements
  - Supports XOR/OR/AND operations via selectors Main[48], Main[49], Main[50]
  - Requires proving sum of selectors = 1
  - Uses `all_goals` tactic for unified proof across all operations
  - Handles both real operations and padding (is_real = 0 case)
- **Branch chip**:
  - Has 45 Main elements
  - Supports 6 branch operations (BEQ, BNE, BLT, BGE, BLTU, BGEU) via selectors Main[28] through Main[33]
  - Uses ITypeReaderImmutable with complex match expression on opcode
  - Sum of selectors represents is_real
  - PC bounds are at the end of chip_cstrs
- **Jalr chip**: More complex PC manipulation, requires careful overflow checking

## Advanced Techniques

### Handling is_real = 0 Case
When the operation is not real (padding), constraints simplify significantly:
```lean
cases this  -- where this : sum = 0 ∨ sum = 1
· rename_i h_not_real 
  simp [h_not_real] at *
  -- Many constraints become True or have ¬True conditions
  -- The proof often becomes trivial
```

**Important**: Don't use `let is_real := Main[a] + Main[b] + ...`. Instead, work directly with the sum to avoid issues with `simp` not unfolding the definition.

### Word Bounds with Conditional Logic
For operations with conditional immediate values:
```lean
· intro h_imm_c
  simp [h_imm_c] at alu_cstrs
  clear * - h_imm_c alu_cstrs
  refine ⟨?_, by simp_all only⟩
  have h_op_c_is_u64 : Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] := by simp_all only
  exact Word.lt_cases_of_isU64 h_op_c_is_u64
```

### Simplification Strategy
Use multiple rounds of simplification:
1. First `simp` to expand `toU16CompProp`
2. Second `simp` on `cstrs` to prepare for decomposition
3. After obtaining components, `simp` each with `SP1Constraint.toProp`
4. Use operation-specific simplifications (e.g., `ByteOpcode.ofNat`)

## Workflow Summary

1. Read the constraints file to understand the chip structure
2. Start with `simp` to expand all definitions until no more `*.constraints` remain
3. Check if the chip has multiple operations (look for selector constraints)
4. Handle the `sum = 0` case first if there are selectors (where sum is the selector sum)
5. For multi-operation chips, prove selector constraints first
6. Use `lean_goal` to see the proof obligations
7. Decompose the constraints hypothesis with `obtain`
8. Prove each conjunct using the appropriate pattern
9. Prefer `simp_all only` over `extract_from_and` when possible
10. For complex constraints with match expressions, may need manual decomposition
11. Increase `maxHeartbeats` if timeouts occur (e.g., to 800000)

## Specific Patterns for Common Goals

### Proving Word Bounds (op_a, op_b)
When the goal asks for bounds on a 4-element word (e.g., `Main[7], Main[8], Main[9], Main[10]`):
```lean
refine ⟨?_, ?_⟩
· have h_op_a_is_u64 : Word.isU64 #v[Main[7], Main[8], Main[9], Main[10]] := by simp_all only
  exact Word.lt_cases_of_isU64 h_op_a_is_u64
```

### Proving Register Bounds
When the goal asks for register bounds (typically < 32 which implies < 65536):
```lean
· calc Main[6] < 32 := by simp_all only
       _ < 65536 := by trivial
```

### Structured Proof for Multiple Bounds
When proving multiple bounds together:
```lean
refine ⟨?_, ?_⟩  -- Split the conjunction
· -- First part (word bounds)
  have h_word_is_u64 : Word.isU64 #v[Main[a], Main[b], Main[c], Main[d]] := by simp_all only
  exact Word.lt_cases_of_isU64 h_word_is_u64
· -- Second part (register or other bounds)
  -- Use calc, simp_all only, or direct extraction
```