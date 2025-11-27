# Lean 4 Induction Curriculum

A complete, progressive curriculum designed to teach proof patterns needed for the Metamath/Lean formalization project.

**Status**: 6 lessons + 3 pattern analysis documents

---

## Quick Links

- **Start here**: [Curriculum Overview](#curriculum-overview)
- **Pattern diagnosis**: [STUCK_PROOF_PATTERNS.md](STUCK_PROOF_PATTERNS.md) - Maps stuck proofs to lessons
- **Error isolation**: [PATTERN_VIOLATIONS.md](PATTERN_VIOLATIONS.md) - Specific syntax/logical errors
- **Theory**: [PROOF_PATTERNS.md](../.claude/PROOF_PATTERNS.md) - General proof strategies

---

## Curriculum Overview

### Progression Path

```
Lesson 1: Basic List Induction
    ↓
Lesson 2: Fold Induction (Generalized Accumulator)
    ↓
Lesson 3: Monadic Folds (foldlM with Option)
    ↓ (splits into parallel topics)
    ├→ Lesson 4: List Splitting (Array/List conversion)
    ├→ Lesson 5: Function Pattern Mismatch (Lambda equivalence)
    └→ Lesson 6: FoldlM Case Analysis (Success/Failure cases)
```

### Lessons

#### **Lesson 1: Basic List Induction** (01_BasicListInduction.lean)
- **Goal**: Learn foundational list induction pattern
- **Key Pattern**: `induction xs with | nil => | cons x xs ih =>`
- **Theorems**: `length_append`, `length_map`, `map_append`
- **Status**: ✅ Working
- **Complexity**: Easy (~10 min)

#### **Lesson 2: Fold Induction** (02_FoldInduction.lean)
- **Goal**: Prove properties of `List.foldl` using induction
- **Key Pattern**: `induction xs generalizing init with` (CRITICAL!)
- **Theorems**: `length_via_fold`, `append_via_fold`, `foldl_push_creates_list`, `map_then_fold`
- **Status**: ✅ Working
- **Complexity**: Medium (~30 min)
- **Why Important**: The "generalizing accumulator" is the KEY to all fold proofs in this project

#### **Lesson 3: Monadic Folds** (03_MonadicFolds.lean)
- **Goal**: Learn `List.foldlM` with monad (Option/Except)
- **Key Pattern**: Induction on fold with monadic bind
- **Theorems**: `option_fold_preserves_sum` ⭐, `except_fold_success`, + 4 more
- **Status**: ✅ Working (6 theorems + executable examples)
- **Complexity**: Medium (~45 min)
- **Important Notes**: Ultra-simple examples that build from trivial to general

#### **Lesson 4: List Splitting** (04_ListSplitting.lean) ⭐
- **Goal**: Convert array size/index properties to list pattern matching
- **Key Pattern**: `0 < xs.length → ∃ head tail, xs = head :: tail`
- **Theorems**: `list_nonempty_split`, `head_after_split`, `head_stable_in_fold`, `array_nonempty_split`
- **Status**: ✅ Working
- **Complexity**: Medium (~40 min)
- **Maps to Stuck Proof**: Line 328 (`subst_preserves_head_of_const0`)

#### **Lesson 5: Function Pattern Mismatch** (05_FunctionPatternMismatch.lean)
- **Goal**: Handle when lambdas use different syntactic patterns
- **Key Pattern**: Normalize via `simp`, `Function.ext`, or `rfl`
- **Theorems**: `pair_versions_equal`, `check_pair_versions_equal`, `simulated_all_true_with_tuples`
- **Status**: ✅ Working
- **Complexity**: Medium (~30 min)
- **Maps to Stuck Proof**: Line 861 (`toSubstTyped_of_allM_true`)

#### **Lesson 6: FoldlM Case Analysis** (06_FoldWithCaseAnalysis.lean) ⭐⭐
- **Goal**: Prove properties of foldlM when step function CAN fail
- **Key Pattern**: Two-level induction with case analysis on success/failure
- **Theorems**: `fold_output_matches_spec`, `fold_spec_correspondence`, `fold_spec_correspondence_correct`
- **Status**: ✅ Working
- **Complexity**: Hard (~60-90 min)
- **Maps to Stuck Proof**: Line 370 (`subst_ok_flatMap_tail`)
- **Critical Insight**: Generalizing accumulator + case analysis together

---

## Using the Curriculum

### For Learning

1. **Start with Lesson 1-3** if you're new to Lean 4 induction proofs
2. **Read the documentation** in each file before attempting theorems
3. **Study the working theorems** to understand the pattern
4. **Complete the EXERCISE sections** (commented with `sorry`)
5. **Run `lake build`** to verify your work compiles

### For Solving Stuck Proofs

1. **Identify which proof is stuck**: See [STUCK_PROOF_PATTERNS.md](STUCK_PROOF_PATTERNS.md)
2. **Find the corresponding lesson**: Table maps line numbers to lessons
3. **Study the key pattern** in that lesson
4. **Apply to your stuck proof**, using exact pattern structure
5. **Verify with `lake build`**

### Example: Fixing Line 328

```
1. Line 328 is stuck (subst_preserves_head_of_const0)
2. Maps to Lesson 4 (List Splitting)
3. Study: list_nonempty_split, head_after_split
4. Apply pattern: Convert f.size > 0 to ∃ head tail, f.toList = head :: tail
5. Case on cons to discharge nil impossibility
6. Continue with list induction on tail
```

---

## Pattern Analysis Documents

### STUCK_PROOF_PATTERNS.md
**Detailed mapping of stuck proofs to curriculum lessons**

- Maps each stuck proof (lines 328, 370, 401) to specific lessons
- Shows proof sketch using curriculum patterns
- Identifies helper lemmas needed
- Provides completion priority and strategy

**Use when**: You need to know which lesson applies to your stuck proof

### PATTERN_VIOLATIONS.md
**Specific syntax/logic errors isolated in simple cases**

- Pattern Violation 1: Array/List index mismatch
- Pattern Violation 2: Fold case analysis missing
- Pattern Violation 3: Accumulator not generalized
- Pattern Violation 4: Function pattern mismatch
- Pattern Violation 5: Case analysis coverage

**Use when**: You get stuck with a specific error and want to see the minimal example

---

## Key Insights

### The Golden Rule: Generalize Accumulators
When inducting on folds, ALWAYS use:
```lean
induction xs generalizing acc with
```
Without `generalizing`, induction hypothesis won't apply to modified accumulators.

### The Two-Level Pattern
When fold step can fail, use:
```lean
have helper : ∀ acc, ... := by
  intro acc
  induction xs generalizing acc with
    | cons ... => cases h_step : f acc x with ...
```

### Array/List Duality
- Arrays use `![n]` indexing with `.size` property
- Lists use `[n]!` indexing with `.length` property
- Convert between them before pattern matching:
  - `0 < a.size` → split `a.toList` into `head :: tail`
  - Now you can induct on the list

### Case Analysis is Your Friend
In monadic folds with potential failure:
```lean
cases h_step : f acc x with
| error _ => -- Leads to .error, contradicts .ok assumption
| ok acc' => -- Leads to .ok, continue with IH
```

---

## File Structure

```
Lean Curriculum/
├── 01_BasicListInduction.lean      [3 theorems, ~40 lines]
├── 02_FoldInduction.lean            [4 theorems, ~70 lines]
├── 03_MonadicFolds.lean             [2 theorems, ~75 lines]
├── 04_ListSplitting.lean            [5 theorems, ~150 lines]
├── 05_FunctionPatternMismatch.lean  [6 theorems, ~150 lines]
├── 06_FoldWithCaseAnalysis.lean     [6 theorems, ~200 lines]
├── README.md                        (this file)
├── STUCK_PROOF_PATTERNS.md          [Detailed mapping & analysis]
├── PATTERN_VIOLATIONS.md            [Error isolation & diagnosis]
└── lakefile.toml                    [Build config]
```

---

## Related Files in Project

- **Main proofs**: `/Metamath/KernelClean.lean` (stuck proofs at lines 328, 370, 401)
- **Helper lemmas**: `/Metamath/ArrayListExt.lean`, `/Metamath/KernelExtras.lean`
- **Proof strategy reference**: `/.claude/PROOF_PATTERNS.md`
- **Axiom tracking**: `/.claude/AXIOM_POLICY.md`
- **Stuck proof analysis**: `STUCK_PROOFS_ANALYSIS.md`

---

## Estimated Time to Complete

- **Lessons 1-3** (foundation): 60-90 min
- **Lesson 4** (list splitting): 40 min
- **Lesson 5** (pattern mismatch): 30 min
- **Lesson 6** (case analysis): 60-90 min

**Total**: 3-4 hours for full curriculum

**Critical path only** (for fixing stuck proofs):
- Lesson 2 (generalized induction): 30 min
- Lesson 4 (list splitting): 40 min
- Lesson 6 (case analysis): 60-90 min

**Total**: 2-2.5 hours

---

## Exercises

Each lesson contains EXERCISE sections (marked with `sorry`) to practice:

1. After Lesson 2: `exercise_length_via_fold_arbitrary`
2. After Lesson 4: `exercise_head_preservation`
3. After Lesson 6: `concat_fold_spec`

These are **simplified versions** of the stuck proofs, allowing you to test understanding
before tackling the full proofs.

---

## Getting Help

**For specific errors**: Check [PATTERN_VIOLATIONS.md](PATTERN_VIOLATIONS.md)
**For stuck proofs**: Check [STUCK_PROOF_PATTERNS.md](STUCK_PROOF_PATTERNS.md)
**For general patterns**: Check `/.claude/PROOF_PATTERNS.md`

---

## Version Info

- **Created**: 2025-11-09
- **Lean 4 Version**: Latest (supports Except, Option monads)
- **Target Project**: Metamath formal verification in Lean 4
- **Curriculum Status**: Complete with 6 lessons + analysis docs
