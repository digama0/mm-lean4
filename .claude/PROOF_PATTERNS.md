# Lean 4 Proof Patterns for This Codebase

This file contains **working, tested** proof patterns for common tasks in this project.

## List.foldlM Induction Pattern

### The Challenge
Proving properties about `List.foldlM` requires handling:
1. The monadic structure (Except in our case)
2. The accumulator threading through the fold
3. Case analysis on list structure (nil/cons)

### Working Pattern (from Lean 4 source)

```lean
-- Basic expansion of foldlM for 3 elements
example [Monad m] (f : α → β → m α) :
    [a, b, c].foldlM f x₀ = (do
      let x₁ ← f x₀ a
      let x₂ ← f x₁ b
      let x₃ ← f x₂ c
      pure x₃) := by rfl
```

### Key Tactics

1. **`induction xs with`** - Standard list induction
   ```lean
   induction xs with
   | nil => <prove base case>
   | cons x xs ih => <prove inductive case using ih>
   ```

2. **`simp [List.foldlM]`** - Unfolds foldlM definition

3. **For Except monad:**
   ```lean
   -- After unfolding, you get: match (f acc x) with | .ok acc' => ...
   cases hstep : f acc x with
   | error e => <impossible case if fold succeeded>
   | ok acc' => <continue with acc'>
   ```

## TODO for subst_ok_flatMap_tail

The proof needs to show:
```
g.toList.tail = (f.toList.tail).flatMap (...)
```

After `rw [subst_eq_foldlM]`, we have:
```
hsub : f.toList.foldlM (substStep σ) #[] = .ok g
```

**Proof strategy:**
1. Split `f.toList = head :: tail` (since size > 0)
2. Unfold first step: `substStep σ #[] head = .ok acc₀`
3. Show remaining fold on `tail` produces exactly `flatMap tail`
4. Use induction on `tail` to match fold steps to flatMap

**Helper needed:** Lemma relating `Array.toList` of accumulated result to `flatMap`

## TODO for subst_preserves_head_of_const0

Similar pattern but proving head preservation instead of tail correspondence.

**Key insight:** Use `generalize` to abstract the accumulator, then induct on tail.

## Blocked: Helper Lemma Syntax Issue

Lines 292-303 in KernelClean.lean have commented-out helper lemmas that cause parse errors.
The issue is likely namespace/end mismatch or missing context.

**For Opus:** Check namespace balance around line 290-310 before uncommenting.
