/-
# Lesson 1: Basic List Induction

Goal: Learn the basic pattern of list induction in Lean 4.
-/

-- Simple example: length of append
theorem length_append (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil =>
      -- Base case: [] ++ ys
      simp
  | cons x xs ih =>
      -- Inductive case: (x :: xs) ++ ys
      -- ih : (xs ++ ys).length = xs.length + ys.length
      simp [ih]
      omega

-- Practice: map preserves length
theorem length_map (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

-- Next level: relating two operations
theorem map_append (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-
Key Pattern:
1. `induction xs with` starts the proof
2. `| nil =>` handles empty list
3. `| cons x xs ih =>` handles non-empty, where `ih` is the inductive hypothesis
4. `simp` often handles simple cases automatically
5. Use `ih` to apply the inductive hypothesis
-/
