/-
# Lesson 8: Dependent Match with Split Tactic

Goal: Learn to prove theorems about functions that use dependent pattern matching
with `match h : expr with` where the equality proof `h` is used in branches.

Key: When you need to prove something about a definition that uses dependent match,
use `unfold`, `show` to handle lets, then `split` to case on the match branches.

This lesson solves the pattern from Line 861 (toSubstTyped_of_allM_true)!
-/

/-
CONCEPTUAL OVERVIEW:

Dependent pattern matching with `match h : expr with` creates an equality proof
that's available in each branch. Example:

```lean
def foo (xs : List Nat) : Option Nat :=
  match h : xs with
  | [] => none
  | x :: _ => some x  -- h : xs = x :: _ is available here
```

When proving theorems about such functions, you can't directly rewrite the match
expression. Instead, use the `split` tactic to case on each branch.

CHALLENGE: If the match is inside a `let` binding, `split` can't see it.
SOLUTION: Use `show` to expose the structure, `simp only []` to inline lets.
-/

-- ═══════════════════════════════════════════════════════════════════
-- PART 1: Simple Match Without Let
-- ═══════════════════════════════════════════════════════════════════

-- Simple function with match
def headOpt (xs : List α) : Option α :=
  match h : xs with
  | [] => none
  | x :: _ => some x

-- Proving something about it: use split
example (xs : List α) (h : xs ≠ []) : ∃ x, headOpt xs = some x := by
  unfold headOpt
  split
  · -- Case: xs = []
    contradiction
  · -- Case: xs = x :: tail
    exact ⟨_, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART 2: Match With Let Binding (THE TRICKY CASE)
-- ═══════════════════════════════════════════════════════════════════

-- Function with let before match (like toSubstTyped)
def headOptWithLet (xs : List α) : Option α :=
  let ys := xs
  match h : ys with
  | [] => none
  | x :: _ => some x

-- ❌ WRONG: split fails because it can't see through let
example (xs : List α) (h : xs ≠ []) : ∃ x, headOptWithLet xs = some x := by
  unfold headOptWithLet
  -- split  -- ERROR: Could not split an `if` or `match` expression
  sorry

-- ✅ RIGHT: Use show + simp only [] to inline let first
example (xs : List α) (h : xs ≠ []) : ∃ x, headOptWithLet xs = some x := by
  unfold headOptWithLet
  -- Expose the structure with show
  show ∃ x, (let ys := xs; match h : ys with | [] => none | x :: _ => some x) = some x
  -- Inline the let binding
  simp only []
  -- Now split works!
  split
  · contradiction
  · exact ⟨_, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART 3: Pattern with Different Lambda Forms (Line 861 Pattern)
-- ═══════════════════════════════════════════════════════════════════

-- Simulating the allM pattern from Line 861
def checkPairs (pairs : List (Nat × String)) : Bool :=
  pairs.all (fun (n, s) => n > 0 && s.length > 0)

def processIfValid (pairs : List (Nat × String)) : Option (List Nat) :=
  let xs := pairs
  match h : xs.all (fun x => x.fst > 0 && x.snd.length > 0) with
  | true => some (xs.map (·.fst))
  | false => none

-- KEY INSIGHT: fun (n, s) => and fun x => x.fst, x.snd are definitionally equal
-- Prove they're equal via function extensionality
theorem processIfValid_of_checkPairs_true (pairs : List (Nat × String))
    (hCheck : checkPairs pairs = true) :
    ∃ ns, processIfValid pairs = some ns := by
  -- Step 1: Convert hCheck to the form processIfValid uses
  have h_eq : pairs.all (fun x => x.fst > 0 && x.snd.length > 0) = true := by
    -- Prove the predicates are equal
    have : (fun x : Nat × String => x.fst > 0 && x.snd.length > 0) =
           (fun x => match x with | (n, s) => n > 0 && s.length > 0) := by
      funext ⟨n, s⟩
      rfl
    unfold checkPairs at hCheck
    rw [← this]
    exact hCheck
  -- Step 2: Unfold and handle let
  unfold processIfValid
  show ∃ ns, (let xs := pairs; _) = some ns
  simp only []
  -- Step 3: Split on the match
  split
  · -- Case: all returns true
    exact ⟨_, rfl⟩
  · -- Case: all returns false
    -- But h_eq says it's true, contradiction
    simp_all

-- ═══════════════════════════════════════════════════════════════════
-- PART 4: THE COMPLETE PATTERN (From Line 861)
-- ═══════════════════════════════════════════════════════════════════

/-
Here's the exact pattern that solved Line 861:

```lean
theorem toSubstTyped_of_allM_true
    (fr : Spec.Frame) (σ_impl : Std.HashMap String Verify.Formula)
    (hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true) :
  ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped fr σ_impl = some σ_typed := by
  -- STEP 1: Convert lambda pattern to match definition's form
  have h_eq : (Bridge.floats fr).allM (fun x => checkFloat σ_impl x.fst x.snd) = some true := by
    have : (fun x : Spec.Constant × Spec.Variable => checkFloat σ_impl x.fst x.snd) =
           (fun x => match x with | (c, v) => checkFloat σ_impl c v) := by
      funext ⟨c, v⟩; rfl
    rw [← this]; exact hAll
  -- STEP 2: Unfold definition
  unfold toSubstTyped
  -- STEP 3: Handle let binding
  show ∃ σ_typed, (let xs := Bridge.floats fr; _) = some σ_typed
  simp only []
  -- STEP 4: Split on match
  split
  · -- some true branch: witness exists
    exact ⟨_, rfl⟩
  · -- other branches: contradiction with h_eq
    simp_all
```

KEY TECHNIQUES:
1. **funext** - Prove lambda patterns are equal
2. **show** - Expose structure of goal before splitting
3. **simp only []** - Inline let bindings
4. **split** - Case on match branches
5. **simp_all** - Discharge contradictory branches using hypotheses
-/

-- ═══════════════════════════════════════════════════════════════════
-- PART 5: Comparison with Other Approaches
-- ═══════════════════════════════════════════════════════════════════

-- ❌ DOESN'T WORK: Direct rewrite of match discriminant
example (xs : List α) (h : xs.length > 0) : ∃ x, headOptWithLet xs = some x := by
  have h_ne : xs ≠ [] := by
    intro h_eq
    simp [h_eq] at h
  unfold headOptWithLet
  -- rw [h_ne]  -- ERROR: Can't rewrite inside match
  sorry

-- ❌ DOESN'T WORK: Split without handling let first
example (xs : List α) (h : xs ≠ []) : ∃ x, headOptWithLet xs = some x := by
  unfold headOptWithLet
  -- split  -- ERROR: Could not split (let is in the way)
  sorry

-- ✅ WORKS: The full pattern
example (xs : List α) (h : xs ≠ []) : ∃ x, headOptWithLet xs = some x := by
  unfold headOptWithLet
  show ∃ x, (let ys := xs; _) = some x
  simp only []
  split
  · contradiction
  · exact ⟨_, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- SUMMARY: When to Use This Pattern
-- ═══════════════════════════════════════════════════════════════════

/-
USE THIS PATTERN WHEN:

1. **Definition has dependent match**
   - Uses `match h : expr with`
   - The proof `h` is used in branches (dependent type)

2. **Match is inside let binding**
   - `let x := ...; match h : ... with`
   - Direct `split` fails

3. **Lambda pattern mismatch**
   - Hypothesis uses `fun (a, b) => ...`
   - Definition uses `fun x => ... x.fst x.snd`
   - Prove equal via `funext`

RECIPE:
1. Convert lambda patterns (if needed) using `funext`
2. `unfold` the definition
3. `show` to expose let structure
4. `simp only []` to inline lets
5. `split` to case on match
6. `simp_all` for contradictions in impossible branches

COMMON ERRORS:
- "Could not split" → Need to inline let first with `simp only []`
- "Did not find occurrence" → Lambda pattern mismatch, use `funext`
- Goal still has match → Need `show` to restructure goal first

SEE ALSO:
- Lesson 5 (Function Pattern Mismatch) - for the funext technique
- Lesson 7 (AllM Witness Extraction) - for the allM context
-/

-- ═══════════════════════════════════════════════════════════════════
-- EXERCISES
-- ═══════════════════════════════════════════════════════════════════

/-
EXERCISE 1: Complete this simpler version

def lastOpt (xs : List α) : Option α :=
  let ys := xs
  match h : ys with
  | [] => none
  | [x] => some x
  | _ :: tail => lastOpt tail

theorem lastOpt_of_nonempty (xs : List α) (h : xs ≠ []) :
    ∃ x, lastOpt xs = some x ∨ lastOpt xs = none := by
  -- TODO: Use the pattern from this lesson
  sorry
-/

/-
EXERCISE 2: Handle Option.map case

def safeHead (xs : List Nat) : Option Nat :=
  let ys := xs
  match h : ys.headD? with
  | some n => if n > 0 then some n else none
  | none => none

theorem safeHead_some_iff (xs : List Nat) :
    (∃ n, safeHead xs = some n) ↔ (∃ n ∈ xs.head?, n > 0) := by
  -- TODO: Use split pattern
  sorry
-/

/-
NEXT STEPS:

This pattern is crucial for proving theorems about bridge functions
that validate properties using dependent matches.

For more complex cases with multiple nested matches, you may need
to split multiple times or use induction combined with split.
-/
