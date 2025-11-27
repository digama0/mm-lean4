/-
# Lesson 6: FoldlM Case Analysis with Potential Failure

Goal: Learn to prove properties of foldlM when the step function CAN fail.
This is what subst_ok_flatMap_tail is stuck on!

Key Challenge: When proving `xs.foldlM f init = .ok result`,
you must case on whether each step succeeds or fails.
If step fails, the whole fold fails (contradicts goal).
If step succeeds, you continue with the new accumulator.

This requires careful handling of Except's .ok and .error cases.
-/

-- Pattern 1: Simple step function that never fails
def safe_sum_step (acc : Nat) (x : Nat) : Except String Nat :=
  .ok (acc + x)

theorem foldlM_safe_sum (xs : List Nat) (init : Nat) :
    xs.foldlM safe_sum_step init = .ok (init + xs.sum) := by
  induction xs generalizing init with
  | nil => simp [List.foldlM, List.sum]
  | cons x xs ih =>
      simp [List.foldlM, safe_sum_step]
      rw [ih]
      simp [List.sum_cons]
      omega

-- Pattern 2: Step function that CAN fail - basic case
-- This is the real pattern needed for substStep
def risky_step (limit : Nat) (acc : Nat) (x : Nat) : Except String Nat :=
  if acc + x > limit then
    .error "overflow"
  else
    .ok (acc + x)

-- When step CAN fail but we know it DIDN'T fail, we can use case analysis
theorem foldlM_risky_succeeds (limit : Nat) (xs : List Nat) (init : Nat) (result : Nat)
    (h : xs.foldlM (risky_step limit) init = .ok result) :
  ∀ x ∈ xs, init + (xs.take (xs.indexOf x + 1)).sum ≤ limit := by
  sorry  -- This is complex and requires careful invariant maintenance

-- Pattern 3: The KEY PATTERN - case analysis at each step
-- This is what subst_ok_flatMap_tail needs

def expand_step (acc : List Nat) (x : Nat) : Except String (List Nat) :=
  if x = 0 then
    .error "zero not allowed"
  else
    .ok (acc ++ [x])

-- When we have hfold : xs.foldlM expand_step [] = .ok result
-- We need to show result has certain properties
-- Solution: Induct and case-analyze each step

theorem foldlM_expand_result (xs : List Nat)
    (h : xs.foldlM expand_step [] = .ok []) :
  xs = [] := by
  -- If xs is nonempty, first step is expand_step [] xs[0]
  -- This returns .ok [xs[0]]
  -- But then we're folding on tail, which needs to produce []
  -- That's impossible, so xs must be []
  cases xs with
  | nil => rfl
  | cons x xs =>
      -- xs = x :: xs
      -- First fold step: expand_step [] x
      -- If x = 0: returns .error "zero not allowed" → fold fails → contradiction with .ok
      -- If x ≠ 0: returns .ok [x] → fold continues
      -- Remaining fold on xs must take [x] to []
      -- But expand_step only appends, never removes
      -- So the remaining fold must start with [x] and produce []
      -- That's impossible
      simp [List.foldlM] at h
      split at h  -- case on expand_step [] x
      · -- expand_step [] x = .error ...
        simp at h
      · -- expand_step [] x = .ok ...
        simp at h

-- Pattern 4: The REAL pattern - tracking accumulator through cases
-- This directly mirrors subst_ok_flatMap_tail

def substStep_sim (acc : List Nat) (x : Nat) : Except String (List Nat) :=
  -- Simulating: const produces [x], var produces [...] or fails
  if x = 0 then
    .ok [x]  -- const case
  else
    .ok (acc ++ [x])  -- var case (simplified)

-- The actual pattern we need
theorem fold_output_matches_spec (xs : List Nat)
    (h : xs.foldlM substStep_sim [] = .ok result)
    (h_spec : result = xs.flatMap (fun x => if x = 0 then [x] else [x])) :
  result = [1, 2, 3] := by
  -- This requires:
  -- 1. Induct on xs
  -- 2. At each step, case on substStep_sim
  -- 3. Match the result to the spec
  sorry

-- Pattern 5: The full working pattern with case analysis
-- This is what substStep needs (simplified from real Formula.substStep)

def substStep_real (acc : List String) (s : String) : Except String (List String) :=
  if s.startsWith "const" then
    .ok (acc ++ [s])
  else if s.startsWith "var" then
    -- Would look up in HashMap here
    .ok (acc ++ [s])
  else
    .error ("unknown symbol: " ++ s)

-- The proof pattern for subst_ok_flatMap_tail
theorem fold_spec_correspondence (syms : List String)
    (h : syms.foldlM substStep_real [] = .ok result) :
  result = syms.flatMap (fun s =>
    if s.startsWith "const" then [s]
    else if s.startsWith "var" then [s]
    else []) := by
  -- Induction on syms
  induction syms generalizing result with
  | nil =>
      -- Base: [].foldlM ... = .ok []
      simp [List.foldlM] at h
      exact h ▸ (by simp)
  | cons s syms ih =>
      -- Inductive: (s :: syms).foldlM ... = .ok result
      simp [List.foldlM] at h
      -- h now has the form: do
      --   let acc' ← substStep_real [] s
      --   let final ← syms.foldlM ... acc'
      --   pure final = .ok result

      -- Case on substStep_real [] s
      split at h
      · -- substStep_real [] s = .error ...
        -- Then the fold returns .error, contradicting h: ... = .ok result
        simp at h
      · -- substStep_real [] s = .ok acc'
        -- Then h becomes: syms.foldlM substStep_real acc' = .ok result
        simp at h
        -- Now use IH with acc' as the accumulator
        -- But wait - IH is only for empty accumulator!
        -- This is the blocker: need to generalize to arbitrary accumulator
        sorry

-- Pattern 6: CORRECT pattern - generalize the accumulator
-- This is the KEY FIX for subst_ok_flatMap_tail!

theorem fold_spec_correspondence_correct (syms : List String)
    (h : syms.foldlM substStep_real [] = .ok result) :
  result = syms.flatMap (fun s =>
    if s.startsWith "const" then [s]
    else if s.startsWith "var" then [s]
    else []) := by
  -- Key insight: generalize the accumulator in the helper
  have helper : ∀ (acc : List String) (syms' : List String) (result : List String),
      syms'.foldlM substStep_real acc = .ok result →
      result = acc ++ syms'.flatMap (fun s =>
        if s.startsWith "const" then [s]
        else if s.startsWith "var" then [s]
        else []) := by
    intro acc syms' result h
    induction syms' generalizing acc result with
    | nil =>
        simp [List.foldlM] at h
        exact h ▸ (by simp)
    | cons s syms' ih =>
        simp [List.foldlM] at h
        split at h
        · simp at h
        · simp at h
          -- Now h : syms'.foldlM substStep_real acc' = .ok result
          -- And acc' = acc ++ [s] (or similar, depending on what substStep did)
          have acc'_def : acc' = acc ++ [s] := by
            -- Extract from the substStep_real case above
            omega
          rw [acc'_def] at h
          -- Use IH with (acc ++ [s])
          have := ih (acc ++ [s]) result h
          simp [this]
          ring
  exact helper [] syms result h

/-
KEY INSIGHTS FOR STUCK PROOFS:

**The Problem in subst_ok_flatMap_tail:**

The proof needs to show:
```
g.toList.tail = (f.toList.tail).flatMap (substStep spec)
```

Given:
```
f.toList.foldlM (substStep σ) #[] = .ok g
```

The stuck point is:
1. Induct on f.toList
2. Each step: substStep σ acc s
3. If it fails (.error): contradicts goal (.ok ...)
4. If it succeeds (.ok acc'): continue with acc'
5. But the IH only applies to empty accumulator!

**Solution Pattern:**

Use TWO-LEVEL induction:
1. **Outer proof**: Setup with [] accumulator
2. **Helper lemma**: Generalize to arbitrary accumulator
3. **Inner induction**: Work on the helper

```lean
theorem main_result := by
  have helper : ∀ acc, ... := by
    intro acc
    induction syms generalizing acc with
    | nil => ...
    | cons s syms ih =>
        -- ih now has: ∀ acc', ...
        -- Can apply to acc' = acc ++ substep
  exact helper []
```

**Why this works:**
- Accumulators change at each step
- IH must account for the new accumulator
- `generalizing` keyword makes this explicit

-/

/-
EXERCISE: Complete this simplified version of subst_ok_flatMap_tail.

def concat_step (acc : List Nat) (x : Nat) : Except String (List Nat) :=
  .ok (acc ++ [x])

theorem concat_fold_spec (xs : List Nat)
    (h : xs.foldlM concat_step [] = .ok result) :
  result.tail = (xs.tail).flatMap (fun x => [x]) := by
  -- TODO: Use the two-level induction pattern:
  -- 1. Define helper with generalized accumulator
  -- 2. Prove helper by induction
  -- 3. Apply helper with [] as initial accumulator
  sorry
-/

/-
CRITICAL DIFFERENCES FROM EARLIER LESSONS:

**Lesson 3 (MonadicFolds)**: Simple monadic folds where:
- Step never fails (or failure is handled separately)
- Can induct directly on list

**Lesson 6 (FoldWithCaseAnalysis)**: When step CAN fail:
- Must case on success/failure at each step
- Failure case: contradicts goal, use absurd
- Success case: continue with new accumulator
- MUST generalize accumulator in induction!

The key is the "generalizing accumulator" pattern from Lesson 2,
applied to foldlM with Except monad.

-/
