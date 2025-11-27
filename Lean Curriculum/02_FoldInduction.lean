/-
# Lesson 2: Induction on Folds

Goal: Learn how to prove properties about List.foldl and List.foldr.
This is critical for our substitution proofs!
-/

-- Pattern 1: Length via fold (with generalized accumulator)
theorem length_via_fold (xs : List α) (acc : Nat) :
    xs.foldl (fun a _ => a + 1) acc = acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      omega

theorem length_via_fold' (xs : List α) :
    xs.foldl (fun acc _ => acc + 1) 0 = xs.length := by
  simpa using length_via_fold xs 0

-- Pattern 2: Append via fold
theorem append_via_fold (xs ys : List α) :
    xs.foldl (fun acc x => acc ++ [x]) ys = ys ++ xs := by
  induction xs generalizing ys with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.append_assoc]

-- Pattern 3: Fold that builds a list (our critical pattern)
theorem foldl_push_creates_list (xs : List α) (init : List α) :
    xs.foldl (fun acc x => acc ++ [x]) init = init ++ xs := by
  induction xs generalizing init with
  | nil =>
      simp [List.foldl]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      -- After ih: init ++ [x] ++ xs = init ++ (x :: xs)
      simp [List.append_assoc]

-- Pattern 4: Mapping then folding
theorem map_then_fold (f : α → β) (g : γ → β → γ) (xs : List α) (init : γ) :
    (xs.map f).foldl g init = xs.foldl (fun acc x => g acc (f x)) init := by
  induction xs generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih _

-- CRITICAL FOR OUR PROOFS: The accumulator must be generalized!
-- Without `generalizing init`, the induction gets stuck.
theorem foldl_with_single_element (f : α → β → α) (x : β) (init : α) :
    [x].foldl f init = f init x := by
  simp [List.foldl]

/-
CRITICAL INSIGHTS FOR SUBSTITUTION PROOFS:
1. ALWAYS use `generalizing accumulator` when proving fold properties
2. The induction automatically unfolds List.foldl_cons
3. The IH gives you: tail.foldl f acc' = <something>
4. You must relate this to the full list result

For List.foldlM (monadic folds), same pattern applies:
- Unfold the foldlM definition
- Case on the monadic step result
- Use IH on remaining elements
-/
