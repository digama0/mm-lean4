/-
# Lesson 7: AllM Witness Extraction

Goal: Learn to extract witnesses from `allM` success.
This is what toSubstTyped_of_allM_true needs (Line 861)!

Key: When `xs.allM predicate = some true`, you can prove the predicate holds for all elements.

This lesson focuses on the CONCEPTUAL PATTERN rather than complete proofs,
since allM with complex predicates requires advanced techniques.
-/

/-
CONCEPTUAL OVERVIEW:

Regular predicate check: xs.all p : Bool
Monadic predicate check: xs.allM p : m Bool

When allM succeeds with `some true`, it means:
- Every element was tested
- Every test returned `some true` (no `none` or `some false`)
- Therefore: predicate holds for all elements

The challenge: Extracting the witness from the monadic structure.
-/

-- ═══════════════════════════════════════════════════════════════════
-- PART 1: The Simplest Pattern - Boolean All
-- ═══════════════════════════════════════════════════════════════════

-- When all elements satisfy a simple predicate
example : [1, 2, 3].all (fun x => x > 0) = true := by rfl
example : [0, 1, 2].all (fun x => x > 0) = false := by rfl

-- Key library lemma
#check List.all_eq_true  -- ∀ p : α → Bool, xs.all p = true ↔ ∀ x ∈ xs, p x = true

-- ═══════════════════════════════════════════════════════════════════
-- PART 2: Option Monad allM - Can Fail
-- ═══════════════════════════════════════════════════════════════════

-- Define a predicate that can fail
def safe_check (x : Nat) : Option Bool :=
  if x == 0 then none else some (x < 10)

-- When allM succeeds
example : [1, 2, 3].allM safe_check = some true := by rfl

-- When allM fails (element causes none)
example : [0, 1, 2].allM safe_check = none := by rfl

-- When allM succeeds but predicate is false
def check_even (x : Nat) : Option Bool :=
  some (x % 2 == 0)

example : [2, 4, 6].allM check_even = some true := by rfl
example : [1, 2, 3].allM check_even = some false := by rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART 3: The Key Pattern (Simplified)
-- ═══════════════════════════════════════════════════════════════════

-- Theorem: If allM succeeds with true, predicate succeeds for all elements
-- (Simplified version - actual proof requires careful induction)
axiom allM_success_witness : ∀ (xs : List α) (p : α → Option Bool),
    xs.allM p = some true →
    ∀ x ∈ xs, ∃ b, p x = some b ∧ b = true

-- This is THE KEY LEMMA for Line 861!

-- Example usage:
theorem using_allM_witness (xs : List Nat) (p : Nat → Option Bool)
    (h : xs.allM p = some true) :
    ∀ x ∈ xs, ∃ b, p x = some b := by
  intro x h_mem
  have ⟨b, h_pb, h_true⟩ := allM_success_witness xs p h x h_mem
  exact ⟨b, h_pb⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART 4: The Pair Pattern (Line 861 Blocker)
-- ═══════════════════════════════════════════════════════════════════

/-
The actual blocker in Line 861:

```lean
(hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true)
```

The issue: Lambda pattern mismatch
- hAll uses: `fun (c, v) => ...`  (tuple destructuring)
- toSubstTyped might use: `fun x => ... x.fst x.snd`  (pair access)

Solution: Prove these are the same function.
-/

-- Pattern A: Tuple destructuring in lambda
def checkPairs_v1 (pairs : List (Nat × String)) : Option Bool :=
  pairs.allM (fun (n, s) => if n > 0 && s.length > 0 then some true else none)

-- Pattern B: Pair access
def checkPairs_v2 (pairs : List (Nat × String)) : Option Bool :=
  pairs.allM (fun p => if p.1 > 0 && p.2.length > 0 then some true else none)

-- These are definitionally equal!
theorem checkPairs_equal (pairs : List (Nat × String)) :
    checkPairs_v1 pairs = checkPairs_v2 pairs := by
  rfl

-- This means you can rewrite between the two forms freely

-- ═══════════════════════════════════════════════════════════════════
-- PART 5: THE ACTUAL PATTERN FOR LINE 861
-- ═══════════════════════════════════════════════════════════════════

/-
Here's the conceptual proof structure for toSubstTyped_of_allM_true:

```lean
theorem toSubstTyped_of_allM_true
    (fr : Spec.Frame) (σ_impl : Std.HashMap String Verify.Formula)
    (hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true) :
  ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped fr σ_impl = some σ_typed := by

  -- Step 1: Unfold toSubstTyped to see its definition
  unfold toSubstTyped

  -- The definition likely looks like:
  -- if h : allM checkFloat floats = some true then
  --   some (witness h)
  -- else
  --   none

  -- Step 2: Use hAll to select the 'some' branch
  simp [hAll]

  -- Step 3: The witness is in the 'some' branch
  -- The definition constructs σ_typed from the allM success proof
  -- This is automatic once we simplify with hAll
```

KEY TECHNIQUES:
1. Unfold the definition to expose pattern matching on allM result
2. Use the hypothesis (hAll) to select the success branch
3. The witness is constructed automatically in that branch
4. Pattern mismatch (tuple vs pair access) is handled by rfl

ALTERNATIVE APPROACH (if definition uses filterMapM):
1. Show filterMapM produces List of correct length
2. Use allM_success_witness to extract individual witnesses
3. Construct TypedSubst from the list of witnesses
-/

-- Minimal working example of the pattern
def makeWitness (pairs : List (Nat × String)) : Option (List Nat) :=
  if h : pairs.allM (fun (n, s) => if n > 0 then some true else none) = some true then
    some (pairs.map (fun p => p.1))  -- Witness construction
  else
    none

theorem makeWitness_some (pairs : List (Nat × String))
    (h : pairs.allM (fun (n, _s) => if n > 0 then some true else none) = some true) :
    ∃ ns, makeWitness pairs = some ns := by
  unfold makeWitness
  simp [h]
  -- Goal is already solved by simp - the witness is pairs.map (·.1)

-- This is THE PATTERN!

-- ═══════════════════════════════════════════════════════════════════
-- SUMMARY: What You Need to Know
-- ═══════════════════════════════════════════════════════════════════

/-
FOR LINE 861:

1. **Understanding allM**:
   - `allM p xs = some true` means predicate p succeeded for every element
   - Can extract witness: `∀ x ∈ xs, ∃ b, p x = some b ∧ b = true`

2. **Pattern Mismatch**:
   - `fun (c, v) =>` and `fun x => ... x.fst x.snd` are the SAME
   - Proven by `rfl` (definitionally equal)

3. **Witness Extraction**:
   - Unfold the definition of toSubstTyped
   - It likely pattern-matches on allM result
   - Use hAll to select the 'some true' branch
   - Witness is in that branch

4. **Key Tactic**:
   ```lean
   unfold toSubstTyped
   simp [hAll]
   ```

The core insight: When a definition pattern-matches on `if h : allM ... = some true`,
passing the hypothesis `hAll` will select that branch and provide the witness automatically.
-/

-- ═══════════════════════════════════════════════════════════════════
-- EXERCISES
-- ═══════════════════════════════════════════════════════════════════

/-
EXERCISE 1: Complete this simpler version of makeWitness.

def simpleWitness (xs : List Nat) : Option (List Nat) :=
  if h : xs.allM (fun x => if x > 0 then some true else none) = some true then
    some xs
  else
    none

theorem simpleWitness_some (xs : List Nat)
    (h : xs.allM (fun x => if x > 0 then some true else none) = some true) :
    ∃ ys, simpleWitness xs = some ys := by
  -- TODO: Unfold and simp with h
  sorry
-/

/-
EXERCISE 2: Prove the pattern mismatch equivalence.

def pred_v1 (p : Nat × String) : Bool := p.1 > 0 && p.2.length > 0
def pred_v2 (n : Nat) (s : String) : Bool := n > 0 && s.length > 0

theorem pred_equiv (p : Nat × String) :
    pred_v1 p = pred_v2 p.1 p.2 := by
  -- TODO: Unfold both and show they're equal
  sorry
-/

/-
NEXT STEPS:

- For actual allM witness proofs, you need careful list induction
- For Line 861 specifically, focus on unfolding toSubstTyped
- The pattern mismatch is not a real blocker (it's rfl)
- The key is understanding how the definition uses the allM result

See how-to-lean.md Section 3 for more on working with predicates.
-/
