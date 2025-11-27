/-
# Lesson 4: List Splitting in Inductions

Goal: Learn the critical pattern of splitting non-empty lists into (head :: tail) form.
This is what subst_preserves_head_of_const0 is stuck on!

Key Challenge: When you have `h : 0 < xs.length` or similar,
you need to convert this to explicit `∃ head tail, xs = head :: tail`.
-/

-- Pattern 1: Simple existence splitting
theorem list_nonempty_split (xs : List α) (h : 0 < xs.length) :
    ∃ head tail, xs = head :: tail := by
  cases xs with
  | nil => simp at h
  | cons head tail => exact ⟨head, tail, rfl⟩

-- Pattern 2: Head access after splitting
theorem head_after_split (xs : List α) (h : 0 < xs.length) :
    ∃ (hne : xs.length > 0) (head : α) (tail : List α),
    xs = head :: tail ∧ xs[0]'(by omega) = head := by
  cases xs with
  | nil => simp at h
  | cons head tail =>
      use Nat.zero_lt_succ _
      use head, tail
      simp

-- Pattern 3: Preserving a property of the head through operations
-- This directly mirrors subst_preserves_head_of_const0
theorem head_preserved_through_append (xs : List α) (h : ∃ x, xs[0]! = x) :
    ∃ ys, ∃ y zs, xs = y :: zs ∧ (y :: (ys ++ zs))[0]! = xs[0]! := by
  -- Step 1: Split xs
  cases xs with
  | nil =>
      -- If xs = [], then xs[0]! crashes, but we got h: ∃ x, xs[0]! = x
      -- This is a contradiction; can discharge by showing h is false
      simp at h
  | cons head tail =>
      -- Now xs = head :: tail, and xs[0]! = head
      use [999]  -- arbitrary list to append
      use head, tail
      simp

-- Pattern 4: The full pattern: split + property + operations
theorem head_stable_in_fold (xs : List α) (h : 0 < xs.length) (hprop : ∃ c, xs[0]! = c) :
    ∃ acc ys,
    -- After fold operations that append to accumulator:
    (acc ++ xs)[0]! = xs[0]! := by
  -- Step 1: Extract the property from h
  obtain ⟨c, hc⟩ := hprop

  -- Step 2: Split xs into head :: tail
  cases xs with
  | nil =>
      -- Contradiction: 0 < [].length is false
      simp at h
  | cons head tail =>
      -- Now xs = head :: tail
      -- So xs[0]! = head
      -- And hc : head = c (from unifying xs[0]! = c with the cons case)
      use []
      use []
      simp

-- Pattern 5: The critical "size > 0 implies non-empty" lemma
-- This is needed for subst_preserves_head_of_const0
theorem array_nonempty_split {α : Type u} (a : Array α) (h : 0 < a.size) :
    ∃ head tail, a = #[head] ++ tail := by
  -- Array is trickier: need to use Array.get with the proof
  cases a with
  | empty =>
      -- If empty, then size = 0, contradiction with h
      simp at h
  | mk data =>
      -- Array has data : List α where a.size = data.length
      simp at h
      cases data with
      | nil => simp at h
      | cons head tail =>
          use head
          use Array.mk tail
          simp

/-
KEY INSIGHTS FOR STUCK PROOFS:

**The Problem in subst_preserves_head_of_const0:**

The proof needs to show:
- f.size > 0  (given from hf)
- ∃ c, f[0]! = c  (given from hhead)
- Need to prove: g[0]'h_g = f[0]'h_f

The stuck point is converting between:
1. f.size > 0 (numeric size)
2. ∃ head tail, f.toList = head :: tail (structural pattern)
3. f[0]! = head (array access)

**Solution Pattern:**

```lean
-- 1. Convert array to list
have h_to_list := f.toList_of_toArray -- or similar
-- 2. Use size > 0 to get non-empty list
obtain ⟨head, tail, h_split⟩ := list_nonempty_split f.toList hf
-- 3. Now work with head :: tail structure
-- 4. Use list induction on tail
```

**Why it's tricky:**
- Array and List have different indexing (![n] vs [n]![])
- Converting between array.size and list.length requires lemmas
- Pattern matching on arrays doesn't work like lists
- Case analysis sometimes needs `by simp at h` to discharge nil cases

-/

/-
EXERCISE: Try to complete this partial proof using the patterns above.

theorem exercise_head_preservation (xs : List α) (hne : 0 < xs.length) (h_prop : ∃ v, xs[0]! = v) :
    ∃ acc : List α,
    (acc ++ xs)[0]! = xs[0]! := by
  -- TODO: Use list_nonempty_split and head_after_split patterns
  sorry
-/
