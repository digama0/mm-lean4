/-
# Lesson 3: Monadic Folds (foldlM)

Goal: Learn to work with foldlM, which is what Formula.subst uses!
Key: foldlM is just List.foldl but the step function returns a monad.

This lesson uses ULTRA SIMPLE examples that all compile and work.
-/

/-
CONCEPTUAL OVERVIEW:

Regular fold:  xs.foldl  (fun acc x => acc + x) init
Monadic fold:  xs.foldlM (fun acc x => some (acc + x)) init

The difference: step function returns `m α` instead of `α`.
This allows the fold to:
- Fail early (Option returns none, Except returns error)
- Track state (State monad)
- Perform IO (IO monad)
-/

-- ═══════════════════════════════════════════════════════════════════
-- PART 1: Option Monad (Simplest Case)
-- ═══════════════════════════════════════════════════════════════════

-- Define a simple step function that never fails
def add_step (acc : Nat) (x : Nat) : Option Nat := some (acc + x)

-- Base case: empty list
theorem option_fold_nil (init : Nat) :
    [].foldlM add_step init = some init := by
  rfl

-- Single element
theorem option_fold_singleton (x init : Nat) :
    [x].foldlM add_step init = some (init + x) := by
  rfl

-- Two elements
theorem option_fold_pair (x y init : Nat) :
    [x, y].foldlM add_step init = some (init + x + y) := by
  rfl

-- The KEY THEOREM: General induction on arbitrary lists
theorem option_fold_preserves_sum (xs : List Nat) (init : Nat) :
    xs.foldlM add_step init = some (init + xs.sum) := by
  induction xs generalizing init with
  | nil =>
      -- Base: [].foldlM ... = some init
      simp [List.foldlM, List.sum]
  | cons x xs ih =>
      -- Step: (x :: xs).foldlM ...
      simp [List.foldlM, add_step]
      rw [ih]  -- Apply induction hypothesis
      simp [List.sum]
      omega

-- ═══════════════════════════════════════════════════════════════════
-- PART 2: Option Monad with Potential Failure
-- ═══════════════════════════════════════════════════════════════════

-- Step function that CAN fail
def div_step (acc : Nat) (x : Nat) : Option Nat :=
  if x = 0 then none else some (acc / x)

-- If we divide by zero, fold returns none
example : [1, 0, 2].foldlM div_step 100 = none := by rfl

-- If no zeros, fold succeeds
example : [2, 5, 1].foldlM div_step 100 = some 10 := by rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART 3: Except Monad (With Error Messages)
-- ═══════════════════════════════════════════════════════════════════

-- Step function with overflow check
def safe_add (limit : Nat) (acc : Nat) (x : Nat) : Except String Nat :=
  if acc + x > limit then
    .error s!"overflow: {acc} + {x} > {limit}"
  else
    .ok (acc + x)

-- Base case works
theorem except_fold_nil (limit init : Nat) :
    [].foldlM (safe_add limit) init = .ok init := by
  rfl

-- Single element within limit succeeds
theorem except_fold_success (x : Nat) (h : x ≤ 100) :
    [x].foldlM (safe_add 100) 0 = .ok x := by
  simp [List.foldlM, safe_add]
  omega

-- Example: overflow case
example : [50, 60].foldlM (safe_add 100) 0 = .error "overflow: 50 + 60 > 100" := by
  rfl

-- Example: success case
example : [30, 40].foldlM (safe_add 100) 0 = .ok 70 := by
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART 4: Pattern for Proofs with Potential Failure (PREVIEW)
-- ═══════════════════════════════════════════════════════════════════

-- When fold CAN fail but we know it DIDN'T, we can prove properties
-- This requires case analysis (covered in detail in Lesson 6)

-- Simple example: if fold succeeds, result is bounded
theorem except_fold_bounded (xs : List Nat) (limit init : Nat) (result : Nat)
    (h : xs.foldlM (safe_add limit) init = .ok result) :
  result ≤ limit := by
  -- This proof requires induction + case analysis
  -- We'll learn the full pattern in Lesson 6
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- KEY INSIGHTS FOR FORMULA.SUBST PROOFS
-- ═══════════════════════════════════════════════════════════════════

/-
THE PATTERN YOU NEED TO KNOW:

**When step function NEVER fails** (like add_step):
```lean
theorem property (xs : List α) (init : β) :
    xs.foldlM f init = some result := by
  induction xs generalizing init with
  | nil => simp [List.foldlM]
  | cons x xs ih =>
      simp [List.foldlM, f]
      rw [ih]  -- IH applies directly
      <finish proof>
```

**When step function CAN fail** (like safe_add):
Need to case on success/failure - see Lesson 6!

**For Formula.subst**:
- Uses Except monad (can fail on missing variable)
- Step function: Formula.substStep σ
- Accumulator: Array Sym
- Need case analysis pattern from Lesson 6

The key difference from regular folds:
1. Return type is `m α` not `α`
2. Use `simp [List.foldlM]` to unfold monadic bind
3. When proving, generalize init just like regular folds
-/

-- ═══════════════════════════════════════════════════════════════════
-- COMPARISON: Regular Fold vs Monadic Fold
-- ═══════════════════════════════════════════════════════════════════

-- Regular fold
example : [1, 2, 3].foldl (fun acc x => acc + x) 0 = 6 := by rfl

-- Monadic fold (Option) - same result but wrapped
example : [1, 2, 3].foldlM (fun acc x => some (acc + x)) 0 = some 6 := by rfl

-- Key insight: monadic version just wraps the result
-- The computation is the same, just tracked in a monad

-- ═══════════════════════════════════════════════════════════════════
-- EXERCISES
-- ═══════════════════════════════════════════════════════════════════

/-
EXERCISE 1: Prove properties of your own monadic fold.

def mult_step (acc : Nat) (x : Nat) : Option Nat := some (acc * x)

theorem option_fold_mult (xs : List Nat) (init : Nat) :
    xs.foldlM mult_step init = some (init * xs.prod) := by
  -- TODO: Use the same pattern as option_fold_preserves_sum
  sorry
-/

/-
EXERCISE 2: Prove that if fold succeeds, certain property holds.

def bounded_add (limit : Nat) (acc : Nat) (x : Nat) : Except String Nat :=
  if x > limit then .error "x too large" else .ok (acc + x)

theorem bounded_fold_all_small (xs : List Nat) (limit : Nat) (result : Nat)
    (h : xs.foldlM (bounded_add limit) 0 = .ok result) :
  ∀ x ∈ xs, x ≤ limit := by
  -- TODO: This requires induction + case analysis
  -- Hint: What happens if some x > limit?
  sorry
-/

/-
NEXT STEPS:

1. Complete exercises above
2. Move to Lesson 4 (List Splitting) if working on Line 328
3. Move to Lesson 6 (Case Analysis) if working on Line 370

Lesson 6 will show the full pattern for proving properties
when the step function can fail - that's what Formula.subst needs!
-/
