# Pattern Violations - Isolating the Exact Errors

This document identifies the **specific syntactic/conceptual errors** in each stuck proof
and shows how to isolate them in simple cases via curriculum lessons.

---

## Pattern Violation 1: Array/List Index Mismatch

**Stuck Proof**: Line 328 (`subst_preserves_head_of_const0`)

**The Problem:**
```lean
(hf : 0 < f.size)           -- Array size property
(hhead : ∃ c, f[0]! = Verify.Sym.const c)  -- Array access

-- But fold operates on lists!
subst σ f = f.toList.foldlM (substStep σ) #[]
-- f.toList : List Sym
-- Need: ∃ head tail, f.toList = head :: tail
```

**Symptom:**
Trying to use array properties directly on the list representation inside the fold.
Arrays and lists have different structure; you can't directly pattern-match array.

**Isolated in Lesson 4:**
```lean
theorem list_nonempty_split (xs : List α) (h : 0 < xs.length) :
    ∃ head tail, xs = head :: tail

theorem array_nonempty_split {α : Type u} (a : Array α) (h : 0 < a.size) :
    ∃ head tail, a = #[head] ++ tail
```

**Solution:**
1. Convert array property to list property: `0 < a.size` → `0 < a.toList.length`
2. Use list splitting to get structural pattern: `∃ head tail, a.toList = head :: tail`
3. Now you can induct on the list structure

---

## Pattern Violation 2: Fold Case Analysis Missing

**Stuck Proof**: Line 370 (`subst_ok_flatMap_tail`)

**The Problem:**
```lean
(hsub : f.subst σ = .ok g)  -- Fold succeeded!

-- Try to induct directly:
induction f.toList generalizing acc with
| nil => ...
| cons s syms ih =>
    -- h: f.toList.foldlM (substStep σ) acc = .ok result
    -- What is substStep σ acc s?
    -- Could be .ok acc' or .error _ !
    -- If .error, the whole fold fails, contradicting hsub
```

**Symptom:**
Induction succeeds structurally, but you never case on whether each step succeeds.
You're implicitly assuming success, which leaves the proof incomplete.

**Isolated in Lesson 6:**
```lean
-- BAD: Direct induction (missing cases)
theorem fold_naïve (xs : List Nat) (h : xs.foldlM risky_step [] = .ok result) :
    ... := by
  induction xs with
  | cons x xs ih =>
      simp [List.foldlM] at h
      -- Stuck here! What if risky_step fails?

-- GOOD: Case analysis at each step
theorem fold_correct (xs : List Nat) (h : xs.foldlM risky_step [] = .ok result) :
    ... := by
  induction xs with
  | cons x xs ih =>
      simp [List.foldlM] at h
      cases h_step : risky_step [] x with
      | error _ => simp [h_step] at h  -- Contradiction!
      | ok acc' => simp [h_step] at h   -- Continue with acc'
```

**Solution:**
1. Use `cases h_step : f acc x with | error _ => | ok acc' =>`
2. In error case: show contradiction with `.ok` fold result
3. In ok case: use induction hypothesis with new accumulator

---

## Pattern Violation 3: Accumulator Not Generalized

**Stuck Proof**: Line 370 (deeper issue in fold induction)

**The Problem:**
```lean
induction f.toList with
| cons s syms ih =>
    -- ih : syms.foldlM f acc = .ok result'
    -- But what is acc here?
    -- It should be (f acc s), not the original!
    -- Yet ih is only proven for one specific accumulator
```

**Symptom:**
Induction hypothesis doesn't apply because it's specialized to a specific accumulator,
but each fold step creates a new accumulator.

**Isolated in Lesson 2:**
```lean
-- BAD: No generalization
theorem fold_bad (xs : List Nat) :
    xs.foldl (fun a x => a + x) 0 = xs.sum := by
  induction xs with
  | cons x xs ih =>
      -- ih : xs.foldl (fun a x => a + x) 0 = xs.sum
      -- But actual fold is: xs.foldl (fun a x => a + x) (0 + head)
      -- These are different accumulators!
      sorry

-- GOOD: Generalize the accumulator
theorem fold_good (xs : List Nat) (acc : Nat) :
    xs.foldl (fun a x => a + x) acc = acc + xs.sum := by
  induction xs generalizing acc with  -- KEY: generalizing!
  | cons x xs ih =>
      -- ih : ∀ acc', xs.foldl (fun a x => a + x) acc' = acc' + xs.sum
      -- Now applies to any accumulator!
      rw [ih]
```

**Solution:**
1. Identify what value the accumulator should have in the inductive case
2. Add it as a parameter: `induction xs generalizing new_acc`
3. Now induction hypothesis applies to all accumulator values

---

## Pattern Violation 4: Function Pattern Mismatch

**Stuck Proof**: Line 861 (`toSubstTyped_of_allM_true`)

**The Problem:**
```lean
(hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true)
-- Proof uses tuple destructuring: fun (c, v) => ...

-- But toSubstTyped might use:
items.allM (fun x => checkFloat σ_impl x.fst x.snd)
-- Different lambda pattern!
```

**Symptom:**
Two functions are extensionally equal but syntactically different.
Lean's pattern matching is strict, so you can't use one proof for the other.

**Isolated in Lesson 5:**
```lean
-- These are syntactically different but extensionally equal
def f1 (p : Nat × String) : Bool := let (a, b) := p; a > 0 && b.length > 0
def f2 (p : Nat × String) : Bool := let a := p.fst; let b := p.snd; a > 0 && b.length > 0

-- f1 = f2 by rfl (definitionally equal)

-- But in allM:
[pairs].allM (fun (c, v) => body)  -- Pattern 1
[pairs].allM (fun x => body_on_x)  -- Pattern 2

-- Appear different to Lean
```

**Solution:**
1. Unfold/expand both sides to normal form
2. Use `simp only [...]` to reduce patterns
3. Use `Function.ext` if needed to prove pointwise equality
4. Often just `rfl` after unfolding works

---

## Pattern Violation 5: Case Analysis Coverage

**General Issue**: Not all success/failure branches handled

**Symptom:**
```lean
-- Fold produces .ok result
(h : xs.foldlM f init = .ok result)

-- But what if during fold execution:
-- Step 1: f init x1 fails (.error)
-- Then the fold fails immediately!
-- So h : ... = .ok result contradicts this

-- Solution: MUST case on each step and show:
-- Either it succeeds (.ok) and we continue
-- Or it fails (.error) and we contradict h
```

**Isolated in Lesson 6:**
```lean
def risky_step (acc : Nat) (x : Nat) : Except String Nat :=
  if acc + x > limit then .error "overflow" else .ok (acc + x)

-- When you have: h : xs.foldlM risky_step 0 = .ok result
-- You MUST case on each step:
-- Can it fail? If so, contradicts h
-- Will it succeed? Apply IH to the new accumulator

cases h_step : risky_step acc x with
| error _ =>
    -- This path leads to .error, contradicts h : ... = .ok
    simp [h_step] at h  -- Gets contradiction
| ok acc' =>
    -- This path continues with acc'
    simp [h_step] at h
    -- h : xs.foldlM risky_step acc' = .ok result
    -- Apply IH with acc'
```

---

## Summary Table: Pattern Violations

| Pattern | Symptom | Lesson | Fix |
|---------|---------|--------|-----|
| Array/List mismatch | Using array pattern on list inside fold | L4 | Convert properties, split, match structurally |
| Missing case analysis | Ignoring that fold step can fail | L6 | Case on .ok/.error, discharge error case |
| Accumulator not generalized | IH doesn't apply to new accumulator | L2 | Add `generalizing acc` to induction |
| Function pattern mismatch | Two lambdas syntactically different | L5 | Unfold/simp to normal form |
| Incomplete coverage | Only success path considered | L6 | Case analysis on all branches |

---

## How to Use This Document

1. **If stuck on a proof**: Look up the pattern violation above
2. **Find the curriculum lesson**: Check which lesson isolates it (L2-L6)
3. **Study the working example**: In the lesson, see the pattern that works
4. **Apply to your proof**: Use the exact same structure in your stuck proof
5. **Verify**: `lake build` should pass

---

## Testing Your Understanding

For each pattern, the curriculum has:
- **Working theorems**: Study these to see the pattern
- **EXERCISE comments**: Try implementing with hints
- **Detailed explanations**: Why the pattern matters

To test comprehension:
1. Read the curriculum lesson
2. Complete the exercise in comments (uses `sorry`)
3. Try applying to actual stuck proof
4. Compare with this document for feedback

---

## Cheat Sheet: The 6 Critical Patterns

### Lesson 1: Basic List Induction
```lean
induction xs with | nil => | cons x xs ih =>
```

### Lesson 2: Fold with Generalized Accumulator
```lean
induction xs generalizing acc with | cons x xs ih =>
-- ih : xs.foldl f (f acc x) = ...
```

### Lesson 3: Monadic Folds (no failure)
```lean
induction xs generalizing init with
| cons x xs ih => simp [List.foldlM, step]; rw [ih]
```

### Lesson 4: List Splitting
```lean
obtain ⟨head, tail, h_split⟩ := list_nonempty_split xs (by omega)
-- Now xs = head :: tail
```

### Lesson 5: Function Pattern Normalization
```lean
simp only [...]  -- or Function.ext or rfl
```

### Lesson 6: FoldlM Case Analysis
```lean
cases h_step : f acc x with
| error _ => simp [h_step] at h_fold  -- Contradiction
| ok acc' => simp [h_step] at h_fold; -- Continue with acc'
             have := ih acc' h_fold   -- IH with new acc
```

---

## Blocking Dependencies

```
Line 401 (parser invariant)
    ↓ (unblocks)
Line 328 (head preservation + list splitting)
    ↓ (prerequisite for)
Line 370 (tail/flatMap + case analysis)
    ↓ (depends on bridge layer, not yet attempted)
Lines 861, 987, 1100
```

All three critical proofs follow the pattern ladder:
1. **List splitting** (Lesson 4)
2. **Generalized fold induction** (Lesson 2)
3. **Monadic case analysis** (Lesson 6)
